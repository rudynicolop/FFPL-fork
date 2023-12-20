From ffpl.lib Require Import prelude.
From ffpl.type_systems.systemf_state Require Import lang notation bigstep tactics types_fo logrel.
From Equations Require Import Equations.

(** Here, we take the approach of encoding [assert],
  instead of adding it as a primitive to the language.
  This saves us from adding it to all of the existing proofs.
  But clearly it has the same reduction behavior.
 *)

Definition assert (e : expr) : expr :=
  if: e then #LitUnit else (#0 #0).

Definition Or (e1 e2 : expr) : expr :=
  if: e1 then #true else e2.
Definition And (e1 e2 : expr) : expr :=
  if: e1 then e2 else #false.
Notation "e1 '||' e2" := (Or e1 e2) : expr_scope.
Notation "e1 '&&' e2" := (And e1 e2) : expr_scope.

(** Proving safety of MutBit *)

Definition MUTBIT : type :=
  (Unit -> Unit) * (Unit -> Bool).

Definition MyMutBit : expr :=
  let: new #0 in
  ((lam: let: ^1 <- #1 - (! ^1) in #()),
   (lam: #0 < (! ^1))).

Lemma MyMutBit_typed Delta Gamma :
  TY Delta; Gamma |- MyMutBit : MUTBIT.
Proof.
  eapply (type_app (Ref FOInt)); last by repeat econstructor.
  econstructor; last by repeat econstructor.
  econstructor.
  - eapply (type_lam Unit); last by repeat econstructor.
    eapply type_app; first by repeat econstructor.
    eapply (type_store FOInt); first by repeat econstructor.
    repeat econstructor.
    eapply (type_load FOInt); by repeat econstructor.
  - eapply (type_lam Unit); last by repeat econstructor.
    repeat econstructor.
    eapply (type_load FOInt); by repeat econstructor.
Qed.

Definition MyMutBit_unsafe : expr :=
  let: new #0 in
  ((lam: let: assert ((!^1 = #0) || (!^1 = #1)) in
         let: ^2 <- #1 - (! ^2) in #()),
   (lam: let: assert ((!^1 = #0) || (!^1 = #1)) in
            #0 < !^2)).

Lemma MyMutBit_unsafe_sem_typed :
  TY 0; [] |= MyMutBit_unsafe : MUTBIT.
Proof.
  intros delta W0 gamma Hctx.
  simp type_interp. intros h1 W1 Hwext1 Hwsat1.
  set l := fresh (dom h1).
  set INV := (fun sigma : heap => sigma = {[l:=#0]} \/ sigma = {[l:=#1]}).
  set W2 := (W1 ++ [INV]).
  assert (HINV: W2 !! (length W1) = Some INV).
  { rewrite lookup_app_r; last done.
    rewrite (_: length W1 - length W1 = 0); last by lia. done. }
  eexists _, (<[l:=_]> h1), W2. split_and!.
  3:{ change (MyMutBit_unsafe.[gamma]) with MyMutBit_unsafe.
      rewrite /MyMutBit_unsafe. repeat econstructor. }
  1:{ apply prefix_app_r. done. }
  1:{ rewrite insert_union_singleton_l. eapply wsat_new; first done.
      - left. done.
      - apply map_disjoint_singleton_r_2, not_elem_of_dom. apply is_fresh. }
  asimpl. rewrite -/l.
  (* Now the reference is created, show soundness of the two fields. *)
  unfold MUTBIT. simp type_interp. eexists _, _.
  split_and!; first done.
  - (* flip *) simp type_interp. eexists. split; first done.
    intros v W3 Hwext3 Hv. asimpl.
    simp type_interp. intros h4 W4 Hwext4 Hwsat4. clear Hwsat1.
    edestruct (wsat_lookup_wext Hwsat4 HINV) as (h' & Hsub & Hinv).
    { by etrans. }
    assert (exists n:Z, h4 !! l = Some #n /\ (n = 0 \/ n = 1)%Z) as (n & Hl & Hn).
    { destruct Hinv; subst; eexists; (split; first (eapply lookup_weaken, Hsub; rewrite lookup_singleton //)); eauto. }
    eexists #(), _, _. split_and!.
    3:{ destruct Hn; subst.
        - bs_steps_det. eapply bs_if_true; bs_steps_det.
          eapply bs_if_true; bs_steps_det. 
        - bs_steps_det. eapply bs_if_true; bs_steps_det.
          eapply bs_if_false; bs_steps_det. }
    2:{ eapply (wsat_update_wext Hwsat4 HINV).
        { by etrans. }
        intros h [-> | ->]; (split; [rewrite lookup_insert_eq; eauto | ]).
        all: rewrite insert_insert; destruct Hn; subst n INV; simpl; eauto. }
    1:{ done. }
    simp type_interp. done.
  - (* get *) simp type_interp. eexists. split; first done.
    intros v W3 Hwext3 Hv. asimpl.
    simp type_interp. intros h4 W4 Hwext4 Hwsat4. clear Hwsat1.
    edestruct (wsat_lookup_wext Hwsat4 HINV) as (h' & Hsub & Hinv).
    { by etrans. }
    assert (exists (n:Z) (b:bool), h4 !! l = Some #n /\ ((n = 0 /\ b = false) \/ (n = 1 /\ b = true))%Z) as (n & b & Hl & Hnb).
    { destruct Hinv; subst; eexists _, _; (split; first (eapply lookup_weaken, Hsub; rewrite lookup_singleton //)); eauto. }
    eexists #b, _, _. split_and!.
    3:{ destruct Hnb as [[]|[]]; subst.
        - bs_steps_det. eapply bs_if_true; bs_steps_det.
          eapply bs_if_true; bs_steps_det. 
        - bs_steps_det. eapply bs_if_true; bs_steps_det.
          eapply bs_if_false; bs_steps_det. }
    2:{ done. }
    1:{ done. }
    simp type_interp. eauto.
Qed.

(** It follows that any term [e] that is syntactically well-typed (which can be
checked automatically!) and uses some free variable of type [MUTBIT], will run
safely when that variable is replaced by our unsafe code. *)
Lemma MyMutBit_unsafe_user_safe (e : expr) A :
  TY 0; [MUTBIT] |- e : A ->
  forall h, safe h e.[MyMutBit_unsafe/].
Proof.
  intros He. eapply sem_type_safety. eapply sem_type_subst_one.
  - eapply MyMutBit_unsafe_sem_typed.
  - eapply sem_soundness. done.
Qed.
