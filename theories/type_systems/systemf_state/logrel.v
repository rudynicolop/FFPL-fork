From stdpp Require Import gmap base relations.
From ffpl.lib Require Import prelude.
From ffpl.lib Require Export facts.
From ffpl.type_systems.systemf_state Require Import lang notation types_fo bigstep.
From Equations Require Export Equations.


(** * Logical relation for SystemF + mutable state *)

(** As we have seen with Landin's Knot, System F with mutable state is not a
terminating language. Instead, we will prove termination (and semantic type
soundness) of the fragment of that langauge that only puts first-order types on
the heap: integers, booleans, units, and products of such types. We have defined
the type system for that in [types_fo.v]; this file defines the logical relation.
*)

Implicit Types
  (Delta : nat)
  (Gamma : typing_context)
  (v : val)
  (alpha : var)
  (e : expr)
  (A : type)
  (a : fotype).

(** ** Worlds *)
(** We represent heap invariants as predicates on heaps,
  and worlds as lists of such invariants.
 *)
Definition heap_inv := heap -> Prop.
Definition world := list heap_inv.
Implicit Types (W : world) (INV : heap_inv).
(** [W'] extends [W] if [W] is a prefix of [W'] *)
Definition wext W W' := prefix W W'.
#[export] Instance wext_preorder : PreOrder wext.
Proof. apply _. Qed.

(** World satisfaction is defined by recursion.
  We use map difference `difference` that computes the difference of two maps
  based on the domain. This means the recursive call uses the "remaining"
  heap that is left after removing the part of the heap described by the current INV.
 *)
Fixpoint wsat W h :=
  match W with
  | INV :: W' =>
    exists h0, INV h0 /\ h0 `subseteq` h /\ wsat W' (h `difference` h0)
  | [] => True
  end.

(** The invariant for "location has type a" *)
Definition loc_type_inv l a : heap_inv :=
  fun h => exists v, h = {[ l := v ]} /\ TY 0; [] |- (of_val v) : a.

(** ** Semantic types *)
(** Semantic types are no longer just predicates over values.
They also need access to the world, and they need to be monotone in the world. *)

Record sem_type := mk_ST {
  sem_type_car :> world -> val -> Prop;
  sem_type_mono : forall W1 W2 v, sem_type_car W1 v -> wext W1 W2 -> sem_type_car W2 v;
}.

(** Defining [sem_type] is a bit annoying: you have to define a predicate and
then prove that it is world-monotone. [pose_sem_type P as N] makes this easier;
it defines a semantic type at name [N] with the value predicate [P]. *)
Tactic Notation "pose_sem_type" uconstr(P) "as" ident(N) :=
  (* slightly complicated formulation to make the proof terms opaque and
  prevent them from polluting the context *)
  let mono := fresh "__mono" in
  unshelve refine ((fun mono => let N := (mk_ST P mono) in _) _);
    first (simpl in mono); cycle 1.

(** ** Definition of the logrel *)

(** The logical relation is defined mutually recursively on expressions and values.
To encode this in Coq, we define a type that is "expression or value", and then
define the relation on that. The [inj_val] and [inj_expr] constructors
are used to convert values/expressions into that shared type. *)
Inductive val_or_expr : Type :=
| inj_val : val -> val_or_expr
| inj_expr : expr -> val_or_expr.

(** As before, we need to define a measure to prove that our recursive definitions are well-formed. *)
Equations type_size (A : type) : nat :=
  type_size Int := 1;
  type_size Bool := 1;
  type_size Unit := 1;
  type_size (A -> B) := type_size A + type_size B + 1;
  type_size (^alpha) := 1;
  type_size (forall: A) := type_size A + 2;
  type_size (exists: A) := type_size A + 2;
  type_size (A * B) := type_size A + type_size B + 1;
  type_size (Ref a) := 2
.

Equations type_interp_measure (ve : val_or_expr) (A : type) : nat :=
  type_interp_measure (inj_expr e) A := 1 + type_size A;
  type_interp_measure (inj_val v) A := type_size A.

(** Now that our types contain free variables, we need to parameterize the type interpretation
function by an interpretation for the free variables. *)
Definition tyvar_interp := var -> sem_type.

Implicit Types
  (delta : tyvar_interp)
  (tau : sem_type)
.

(** The logical relation *)
Equations type_interp (ve : val_or_expr) (A : type) (delta : tyvar_interp) (W : world) : Prop by wf (type_interp_measure ve A) := {
  type_interp (inj_val v) Int delta W =>
    exists z : Z, v = #z ;
  type_interp (inj_val v) Bool delta W =>
    exists b : bool, v = #b ;
  type_interp (inj_val v) Unit delta W =>
    v = #LitUnit ;
  type_interp (inj_val v) (A * B) delta W =>
    exists v1 v2 : val, v = (v1, v2)%V /\
      type_interp (inj_val v1) A delta W /\ type_interp (inj_val v2) B delta W;
  type_interp (inj_val v) (A -> B) delta W =>
    exists e, v = LamV e /\
      (* have to quantify over future world to ensure world-monotonicity *)
      forall v' W', wext W W' ->
        type_interp (inj_val v') A delta W' ->
        type_interp (inj_expr (e.[of_val v'/])) B delta W';
  (** Type variable case *)
  type_interp (inj_val v) (^alpha) delta W =>
    (delta alpha) W v;
  (** forall case *)
  type_interp (inj_val v) (forall: A) delta W =>
    exists e, v = TLamV e /\
      forall tau : sem_type, type_interp (inj_expr e) A (tau .: delta) W;
  (** exists case *)
  type_interp (inj_val v) (exists: A) delta W =>
    exists v', v = PackV v' /\
      exists tau : sem_type, type_interp (inj_val v') A (tau .: delta) W;
  (** reference case *)
  type_interp (inj_val v) (Ref a) delta W =>
      exists (l : loc) i, v = LitV $ LitLoc l /\ W !! i = Some (loc_type_inv l a);

  (** expression relation *)
  type_interp (inj_expr e) A delta W =>
    (* have to quantify over future world to ensure world-monotonicity *)
    forall h' W', wext W W' -> wsat W' h' ->
    exists v h'' W'', wext W' W'' /\ wsat W'' h'' /\
      big_step (h', e) (h'', v) /\ type_interp (inj_val v) A delta W''
}.
Next Obligation. repeat simp type_interp_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp type_interp_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp type_interp_measure; simp type_size; lia. Qed.
Next Obligation.
  simp type_interp_measure. simp type_size.
  destruct A; repeat simp type_interp_measure; repeat simp type_size; lia.
Qed.
Next Obligation. repeat simp type_interp_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp type_interp_measure; simp type_size; lia. Qed.

(** Value relation and expression relation *)
Notation sem_val_rel A delta W v := (type_interp (inj_val v) A delta W).
Notation sem_expr_rel A delta W e := (type_interp (inj_expr e) A delta W).

(** ** Semantic typing of contexts *)

(** We use maps to [expr] rather than [val] to obtain a stronger result:
open terms can have arbitrary semantically well-tpyed *expressions*
in place of their free variables. *)
Implicit Types (gamma : var -> expr).

Definition sem_ctx_rel Gamma delta W gamma :=
  forall x A, Gamma !! x = Some A -> sem_expr_rel A delta W (gamma x).

(** ** The semantic typing judgment *)
(** Now that [Delta] does not actually matter!
THis is because we use a total function for [delta], so *all* type variables have to map to *some*
semantic type. Only the type variables in [Delta] actually matter. *)
Definition sem_typed Delta Gamma e A :=
  forall delta W gamma, sem_ctx_rel Gamma delta W gamma -> sem_expr_rel A delta W e.[gamma].
Notation "'TY' Delta ;  Gamma |= e : A" := (sem_typed Delta Gamma e A) (at level 74, e, A at next level).

(** ** Basic properties of these definitions. *)

(** The relations are monotone wrt the world. *)
Lemma type_interp_mono ve A delta W1 W2 :
  type_interp ve A delta W1 -> wext W1 W2 -> type_interp ve A delta W2.
Proof.
  (* Sadly [Equations] does not generate a suitable induction principle,
  so we have to do induction over the measure "by hand". *)
  remember (ve, A) as x.
  revert ve A delta W1 W2 Heqx.
  induction (lt_wf_0_projected (B := val_or_expr*type)
     (fun '(ve, A) => type_interp_measure ve A) x) as [x _ IH].
  intros ve A delta W1 W2 -> Hinterp Hwext.
  destruct ve as [v|e]; last first.
  { (* expression case *)
    simp type_interp. intros h' W' Hwext' Hwsat'.
    simp type_interp in Hinterp.
    destruct (Hinterp h' W') as (v & h'' & W'' & Hgood); [|done|].
    { by trans W2. }
    exists v, h'', W''. eauto. }
  (* value case. need to case on the type. *)
  destruct A as [x | | | | A | A | A B | A B | a ]; simp type_interp; simp type_interp in Hinterp.
  - (* var *) by eapply sem_type_mono.
  - (* universal *)
    destruct Hinterp as (e & -> & Hinterp).
    eexists. split; first done.
    intros tau. specialize (Hinterp tau).
    eapply (IH (inj_expr _, _)); [|done..].
    repeat simp type_interp_measure; simp type_size; lia.
  - (* existential *)
    destruct Hinterp as (v' & -> & tau & Hinterp).
    eexists. split; first done. exists tau.
    eapply (IH (inj_val _, _)); [|done..].
    repeat simp type_interp_measure; simp type_size; lia.
  - (* function *)
    destruct Hinterp as (e & -> & Hinterp).
    eexists. split; first done.
    intros v' W' Hwext' Hinterp'. eapply Hinterp; last done.
    by trans W2.
  - (* product *)
    destruct Hinterp as (v1 & v2 & -> & Hinterp1 & Hinterp2).
    eexists _, _. split; first done. split.
    + eapply (IH (inj_val _, _)); [|done..].
      repeat simp type_interp_measure; simp type_size; lia.
    + eapply (IH (inj_val _, _)); [|done..].
      repeat simp type_interp_measure; simp type_size; lia.
  - (* reference *)
    destruct Hinterp as (l & i & -> & Hinv).
    eexists _, i. split; first done.
    eapply prefix_lookup in Hwext; done.
Qed.

(** Mapping syntactic type to semantic type *)
Definition syn_type_sem (A : type) delta : sem_type.
Proof.
  pose_sem_type (fun W v => sem_val_rel A delta W v) as tau.
  { intros. by eapply type_interp_mono. }
  exact tau.
Defined.

(** Value inclusion lemma *)
Lemma val_inclusion A delta W v :
  sem_val_rel A delta W v -> sem_expr_rel A delta W (of_val v).
Proof.
  intros Hv. simp type_interp. intros h' W' Hext' Hsat'.
  exists v, h', W'. split; first done. split; first done.
  split; last by eapply type_interp_mono. apply big_step_val.
Qed.

(** Context typing properties *)
Lemma sem_ctx_rel_nil delta W gamma : sem_ctx_rel [] delta W gamma.
Proof.
  intros x A. rewrite lookup_nil. done.
Qed.

Lemma sem_ctx_rel_cons Gamma delta W gamma v A :
  sem_val_rel A delta W v ->
  sem_ctx_rel Gamma delta W gamma ->
  sem_ctx_rel (A :: Gamma) delta W (of_val v .: gamma).
Proof.
  intros Hv Hgamma [|x] B; simpl.
  - intros [= <-]. eapply val_inclusion. done.
  - eapply Hgamma.
Qed.

Lemma sem_ctx_rel_mono Gamma delta W1 W2 gamma :
  sem_ctx_rel Gamma delta W1 gamma -> wext W1 W2 -> sem_ctx_rel Gamma delta W2 gamma.
Proof.
  intros Hgamma Hext. intros x A Hx. eapply type_interp_mono; last done.
  eapply Hgamma. done.
Qed.

(** The compatibility lemmas involving type variables require some technical but
boring helper lemmas. We encourage you to skip over the proofs of these lemmas. *)
Section boring_lemmas.
  (** When [delta] and [delta'] are pointwise equivalent, then they also make no
  difference for semantic interpration of values. *)
  (** "Boring Lemma 1" for the value relation. *)
  Lemma sem_val_rel_ext B delta delta' v :
    (forall n v W, delta n W v <-> delta' n W v) ->
    forall W, sem_val_rel B delta W v <-> sem_val_rel B delta' W v.
  Proof.
    induction B in delta, delta', v |-*; simpl; intros Hiff W; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv.
      eapply forall_proper; intros tau.
      simp type_interp.
      eapply forall_proper; intros h'.
      eapply forall_proper; intros W'.
      eapply forall_proper; intros Hext.
      eapply forall_proper; intros Hsat.
      f_equiv; intros w.
      f_equiv; intros h''.
      f_equiv; intros W''.
      f_equiv. f_equiv. f_equiv. apply IHB.
      intros [|m] ?; simpl; eauto.
    - f_equiv; intros w. f_equiv. f_equiv. intros tau.
      eapply IHB. intros [|m] ?; simpl; eauto.
    - f_equiv. intros ?. f_equiv.
      eapply forall_proper; intros w.
      eapply forall_proper; intros W'.
      eapply if_iff; first by eauto.
      eapply if_iff; first by eauto.
      simp type_interp.
      eapply forall_proper; intros h'.
      eapply forall_proper; intros W''.
      eapply forall_proper; intros Hext.
      eapply forall_proper; intros Hsat.
      f_equiv. intros ?. f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. f_equiv. eauto.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; eauto.
  Qed.

  (** Renaming in [B] is like renaming in [delta].
  (Usually we'd use [delta] as the name for the renaming, but in this file [delta]
  is already used for the type variable interpretation, so we use [sigma]. *)
  Lemma sem_val_rel_move_ren B delta (sigma : var -> var) W v :
     sem_val_rel B.[ren sigma] delta W v <-> sem_val_rel B (fun n => delta (sigma n)) W v.
  Proof.
    induction B in sigma, delta, W, v |-*; simpl; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv.
      eapply forall_proper; intros tau.
      simp type_interp.
      eapply forall_proper; intros h'.
      eapply forall_proper; intros W'.
      eapply forall_proper; intros Hext.
      eapply forall_proper; intros Hset.
      f_equiv; intros w.
      f_equiv; intros h''.
      f_equiv; intros W''.
      do 3 f_equiv.
      asimpl. rewrite IHB.
      eapply sem_val_rel_ext; intros [|n] u; asimpl; done.
    - f_equiv; intros w. f_equiv. f_equiv. intros tau.
      asimpl. rewrite IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      +  simp type_interp. done.
      + simpl. rewrite /up. simpl. done.
    - f_equiv. intros ?. f_equiv.
      eapply forall_proper; intros x.
      eapply forall_proper; intros W'.
      eapply if_iff; first done.
      eapply if_iff; first done.
      simp type_interp.
      eapply forall_proper; intros h'.
      eapply forall_proper; intros W''.
      eapply forall_proper; intros Hext.
      eapply forall_proper; intros Hsat.
      f_equiv. intros ?. f_equiv. intros ?. f_equiv. intros ?.
      do 3 f_equiv. done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; done.
  Qed.

  (** Similarly, apply a substitution in [B] is like applying it in [delta],
  using [syn_type_sem] to interpret the substitution itself. *)
  Lemma sem_val_rel_move_subst B delta sigma W v :
    sem_val_rel (B.[sigma]) delta W v <-> sem_val_rel B (fun n => syn_type_sem (sigma n) delta) W v.
  Proof.
    induction B in sigma, delta, W, v |-*; simpl; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv.
      eapply forall_proper; intros tau.
      simp type_interp.
      eapply forall_proper; intros h'.
      eapply forall_proper; intros W'.
      eapply forall_proper; intros Hext.
      eapply forall_proper; intros Hset.
      f_equiv; intros w.
      f_equiv; intros h''.
      f_equiv; intros W''.
      do 3 f_equiv. rewrite IHB.
      eapply sem_val_rel_ext; intros [|n] u W'''.
      + simp type_interp. done.
      + simpl. rewrite /syn_type_sem. simpl.
        asimpl. rewrite sem_val_rel_move_ren.
        simpl. done.
    - f_equiv; intros w. f_equiv. f_equiv. intros tau.
      rewrite IHB.
      eapply sem_val_rel_ext; intros [|n] u W'.
      +  simp type_interp. done.
      + simpl. rewrite /syn_type_sem. simpl.
        asimpl. rewrite sem_val_rel_move_ren.
        simpl. done.
    - f_equiv. intros ?. f_equiv.
      eapply forall_proper; intros x.
      eapply forall_proper; intros W'.
      eapply if_iff; first done.
      eapply if_iff; first done.
      simp type_interp.
      eapply forall_proper; intros h'.
      eapply forall_proper; intros W''.
      eapply forall_proper; intros Hext.
      eapply forall_proper; intros Hsat.
      f_equiv. intros ?. f_equiv. intros ?. f_equiv. intros ?.
      do 3 f_equiv. done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; done.
  Qed.

  (** The previous lemma specialize to substituting a single variable. *)
  (** "Boring Lemma 2" for the value relation. *)
  Lemma sem_val_rel_move_single_subst A B delta W v :
    sem_val_rel (B.[A/]) delta W v <-> sem_val_rel B (syn_type_sem A delta .: delta) W v.
  Proof.
    rewrite sem_val_rel_move_subst. eapply sem_val_rel_ext.
    intros [| n] w W'; simpl; done.
  Qed.

  (** Semantic typing is preserved when we bump up the free type variables,
  and add an arbitrary type interpretation [tau] for the new index 0.
  We need this in both directions. *)
  Lemma sem_val_rel_up A delta W v tau :
    sem_val_rel A delta W v <->
    sem_val_rel A.[ren (+1)] (tau .: delta) W v.
  Proof.
    rewrite sem_val_rel_move_subst; simpl.
    eapply sem_val_rel_ext. done.
  Qed.
  Lemma sem_expr_rel_up A delta W e tau :
    sem_expr_rel A delta W e <->
    sem_expr_rel A.[ren (+1)] (tau .: delta) W e.
  Proof.
    simp type_interp. setoid_rewrite <-sem_val_rel_up. done.
  Qed.

  (** Semantic typing of contexts is preserved when we bump up the free type
  variables *everywhere* and add an arbitrary [tau] for the new index 0. *)
  Lemma sem_ctx_rel_upctx Gamma delta W gamma tau :
    sem_ctx_rel Gamma delta W gamma ->
    sem_ctx_rel (upctx Gamma) (tau .: delta) W gamma.
  Proof.
    intros Hctx x A. rewrite /upctx list_lookup_fmap.
    destruct (Gamma !! x) as [B|] eqn:EQ; rewrite EQ; last done.
    asimpl. intros [= <-].
    rewrite -sem_expr_rel_up. eapply Hctx. done.
  Qed.
End boring_lemmas.

(** First-order types are simple: syntactic and semantic typing are equivalent. *)
Lemma syn_fo_typed_val a delta W v :
  TY 0; [] |- of_val v : a <-> sem_val_rel a delta W v.
Proof.
  induction a as [ | | | a1 IH1 a2 IH2 ] in v |-*.
  - split.
    + intros [z Heq]%canonical_values_int; last eauto.
      destruct v; try done. destruct l; try done.
      simp type_interp. eauto.
    + simp type_interp. intros (z & ->). constructor.
  - split.
    + intros (b & Heq)%canonical_values_bool; last eauto.
      destruct v; try done. destruct l; try done.
      simp type_interp. eauto.
    + simp type_interp. intros (b & ->). constructor.
  - split.
    + intros Heq%canonical_values_unit; last eauto.
      destruct v; try done. destruct l; try done.
    + simp type_interp. intros ->. econstructor.
  - split.
    + simpl. inversion 1; destruct v; simplify_eq/=; eauto.
      simp type_interp. exists v1, v2. split; first done. split.
      * eapply IH1. done.
      * eapply IH2. done.
    + simpl. simp type_interp. intros (v1 & v2 & -> & Hv1%IH1 & Hv2%IH2). econstructor; done.
Qed.

(** Lemmas about world satisfaction *)

Lemma wsat_new W h1 h2 INV :
  wsat W h1 ->
  INV h2 ->
  map_disjoint h1 h2 ->
  wsat (W ++ [INV]) (h2 `union` h1).
Proof.
  intros Hwsat Hinv Hdisj.
  induction W as [|INV' W IH] in h1, Hwsat, Hdisj |- *; simpl.
  - exists h2. split; first done. split; last done.
    apply map_union_subseteq_l.
  - destruct Hwsat as (h0 & Hinv' & Hh0 & Hwsat).
    specialize (IH _ Hwsat). feed specialize IH.
    { eapply map_disjoint_weaken_l; first done.
      eapply map_subseteq_difference_l. done. }
    exists h0. split; first done. split.
    + etrans; first eassumption.
      eapply map_union_subseteq_r. done.
    + replace ((h2 ∪ h1) `difference` h0) with (h2 ∪ h1 `difference` h0); first done.
      rewrite map_difference_union' //. f_equal.
      apply map_disjoint_difference.
      eapply map_disjoint_weaken_r; done.
Qed.

Lemma wsat_alloc h l v a W :
  wsat W h ->
  h !! l = None ->
  TY 0; [] |- of_val v : a ->
  wsat (W ++ [loc_type_inv l a]) (<[l:=v]> h).
Proof.
  intros. rewrite insert_union_singleton_l. eapply wsat_new.
  - done.
  - eexists. split; done.
  - apply map_disjoint_singleton_r_2. done.
Qed.

Lemma wsat_lookup {W h i INV} :
  wsat W h ->
  W !! i = Some INV ->
  exists h0, h0 `subseteq` h /\ INV h0.
Proof.
  induction W as [ | INV' W IH] in i, h |-*; first done.
  simpl. intros (h0 & HINV' & Hincl & Hsat).
  destruct i as [ | i]; simpl.
  - intros [= ->]. eauto.
  - intros Hlook. destruct (IH _ _ Hsat Hlook) as (h1 & ? & ?).
    exists h1; split; last done. etrans; eauto.
    by apply map_subseteq_difference_l.
Qed.

Lemma wsat_lookup_wext {W1 W2 h i INV} :
  wsat W2 h ->
  W1 !! i = Some INV ->
  wext W1 W2 ->
  exists h0, h0 `subseteq` h /\ INV h0.
Proof.
  intros Hwsat Hlookup Hwext.
  eapply prefix_lookup in Hwext; last done.
  eapply wsat_lookup; done.
Qed.

Lemma wsat_load {W h i l a} :
  wsat W h ->
  W !! i = Some (loc_type_inv l a) ->
  exists v, h !! l = Some v /\ TY 0; [] |- of_val v : a.
Proof.
  intros Hsat Hinv.
  destruct (wsat_lookup Hsat Hinv) as (h0 & Hsub & v & -> & Hv).
  exists v. split; last done.
  eapply lookup_weaken; last done.
  rewrite lookup_singleton. done.
Qed.

Lemma wsat_mono h h' W :
  wsat W h ->
  h `subseteq` h' ->
  wsat W h'.
Proof.
  induction W as [ | INV W' IH] in h, h' |-*; first done.
  simpl. intros (h0 & Hinv & Hincl' & Hsat) Hincl.
  exists h0; split; first done. split; first by etrans.
  eapply IH; first done.
  by apply map_difference_mono.
Qed.

(** Assuming that we have found a heap invariant [P] talking about [l] and that
is invariant wrt the concrete value, we can update [l]. *)
Lemma wsat_update W h i (l : loc) (v : val) INV :
  wsat W h ->
  W !! i = Some INV ->
  (forall h, INV h -> is_Some (h !! l) /\ INV (<[l:=v]> h)) ->
  wsat W (<[l:=v]> h).
Proof.
  induction W as [ | INV' W IH] in i, h |-*; first done.
  destruct i as [ | i].
  - intros (h0 & HINV & Hincl & Hsat).
    intros [= ->] Hupd. eexists. split_and!; [eapply Hupd, HINV | | ].
    + by apply insert_mono.
    + apply Hupd in HINV as [[v0 Hs] _]. eapply wsat_mono; first apply Hsat.
      rewrite (difference_insert _ _ _ _ _ v0). rewrite insert_id; done.
  - intros Hsat Hlook Hupd.
    destruct Hsat as (h0 & HINV & Hincl & Hsat). simpl in *.
    specialize (wsat_lookup Hsat Hlook) as (h1 & Hincl' & [Hs ?]%Hupd).
    specialize (IH _ _ Hsat Hlook Hupd).
    assert (h0 !! l = None) as H0l.
    { eapply lookup_weaken_is_Some in Hincl'; last done.
      apply lookup_difference_is_Some in Hincl'. apply Hincl'.
    }
    exists h0. split_and!; [  done | | ].
    + etrans; first by eapply (insert_subseteq _ l v).
      by apply insert_mono.
    + assert (<[l:=v]> h `difference` h0 = <[l:=v]> (h `difference` h0)) as ->; last done.
      symmetry. apply insert_difference'. done.
Qed.

Lemma wsat_update_wext {W1 W2 h i l v INV} :
  wsat W2 h ->
  W1 !! i = Some INV ->
  wext W1 W2 ->
  (forall h, INV h -> is_Some (h !! l) /\ INV (<[l:=v]> h)) ->
  wsat W2 (<[l:=v]> h).
Proof.
  intros Hwsat Hlookup Hwext.
  eapply prefix_lookup in Hwext; last done.
  eapply wsat_update; done.
Qed.

Lemma wsat_store h l v a W i :
  wsat W h ->
  W !! i = Some (loc_type_inv l a) ->
  TY 0; [] |- of_val v : a ->
  wsat W (<[l:=v]> h).
Proof.
  intros Hsat Hinv Hty. eapply wsat_update; [done..|].
  intros h0 (w & -> & Hw). split.
  - eexists. rewrite lookup_singleton. done.
  - exists v. rewrite insert_insert. split; done.
Qed.

Lemma wsat_empty h :
  wsat [] h.
Proof.
  simpl. done.
Qed.

(** ** Compatibility lemmas *)

Lemma compat_int Delta Gamma z : TY Delta; Gamma |= (Lit $ LitInt z) : Int.
Proof.
  intros delta W gamma _. apply val_inclusion with (v := #z).
  simp type_interp. eauto.
Qed.

Lemma compat_bool Delta Gamma b : TY Delta; Gamma |= (Lit $ LitBool b) : Bool.
Proof.
  intros delta W gamma _. apply val_inclusion with (v := #b).
  simp type_interp. eauto.
Qed.

Lemma compat_unit Delta Gamma : TY Delta; Gamma |= (Lit $ LitUnit) : Unit.
Proof.
  intros delta W gamma _. apply val_inclusion with (v := #LitUnit).
  simp type_interp. done.
Qed.

Lemma compat_var Delta Gamma x A :
  Gamma !! x = Some A ->
  TY Delta; Gamma |= (Var x) : A.
Proof.
  intros Hx delta W gamma Hctx; simpl. eapply Hctx. done.
Qed.

Lemma compat_int_binop Delta Gamma op e1 e2 :
  bin_op_typed op Int Int Int ->
  TY Delta; Gamma |= e1 : Int ->
  TY Delta; Gamma |= e2 : Int ->
  TY Delta; Gamma |= (BinOp op e1 e2) : Int.
Proof.
  intros Hop He1 He2 delta W gamma Hctx. simpl.
  simp type_interp. intros h' W' Hext' Hsat'.
  specialize (He1 _ _ _ Hctx). specialize (He2 _ _ _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct (He2 h' W') as (v2 & h'' & W'' & Hwext'' & Hsat'' & Hb2 & Hv2); [done..|].
  destruct (He1 h'' W'') as (v1 & h''' & W''' & Hwext''' & Hsat''' & Hb1 & Hv1); [|done|].
  { by trans W'. }
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst op.
  + exists #(z1 + z2)%Z, h''', W'''. split.
    { by trans W''. }
    split; first done. split.
    - econstructor; done.
    - exists (z1 + z2)%Z. done.
  + exists #(z1 - z2)%Z, h''', W'''. split.
    { by trans W''. }
    split; first done. split.
    - econstructor; done.
    - exists (z1 - z2)%Z. done.
  + exists #(z1 * z2)%Z, h''', W'''. split.
    { by trans W''. }
    split; first done. split.
    - econstructor; done.
    - exists (z1 * z2)%Z. done.
Qed.

Lemma compat_int_bool_binop Delta Gamma op e1 e2 :
  bin_op_typed op Int Int Bool ->
  TY Delta; Gamma |= e1 : Int ->
  TY Delta; Gamma |= e2 : Int ->
  TY Delta; Gamma |= (BinOp op e1 e2) : Bool.
Proof.
  intros Hop He1 He2 delta W gamma Hctx. simpl.
  simp type_interp. intros h' W' Hext' Hsat'.
  specialize (He1 _ _ _ Hctx). specialize (He2 _ _ _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct (He2 h' W') as (v2 & h'' & W'' & Hwext'' & Hsat'' & Hb2 & Hv2); [done..|].
  destruct (He1 h'' W'') as (v1 & h''' & W''' & Hwext''' & Hsat''' & Hb1 & Hv1); [|done|].
  { by trans W'. }
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst op.
  + exists #(bool_decide (z1 < z2))%Z, h''', W'''. split.
    { by trans W''. }
    split; first done. split.
    - econstructor; done.
    - by eexists _.
  + exists #(bool_decide (z1 <= z2))%Z, h''', W'''. split.
    { by trans W''. }
    split; first done. split.
    - econstructor; done.
    - by eexists _.
  + exists #(bool_decide (z1 = z2))%Z, h''', W'''. split.
    { by trans W''. }
    split; first done. split.
    - econstructor; done.
    - eexists _. done.
Qed.

Lemma compat_binop Delta Gamma op A B C e1 e2 :
  bin_op_typed op A B C ->
  TY Delta; Gamma |= e1 : A ->
  TY Delta; Gamma |= e2 : B ->
  TY Delta; Gamma |= (BinOp op e1 e2) : C.
Proof.
  inversion 1; subst.
  1-3: by apply compat_int_binop.
  1-3: by apply compat_int_bool_binop.
Qed.

Lemma compat_if n Gamma e0 e1 e2 A :
  TY n; Gamma |= e0 : Bool ->
  TY n; Gamma |= e1 : A ->
  TY n; Gamma |= e2 : A ->
  TY n; Gamma |= (if: e0 then e1 else e2) : A.
Proof.
  intros He0 He1 He2 delta W gamma Hctx. simpl.
  simp type_interp. intros h' W' Hext' Hsat'.
  specialize (He0 _ _ _ Hctx). simp type_interp in He0.
  specialize (He1 _ _ _ Hctx). simp type_interp in He1.
  specialize (He2 _ _ _ Hctx). simp type_interp in He2.

  destruct (He0 h' W') as (v0 & h'' & W'' & Hwext'' & Hsat'' & Hb0 & Hv0); [done..|].
  simp type_interp in Hv0. destruct Hv0 as (b & ->).
  destruct b.
  - destruct (He1 h'' W'') as (v1 & h''' & W''' & Hwext''' & Hsat''' & Hb1 & Hv1); [|done|].
    { by trans W'. }
    exists v1, h''', W'''. split.
    { by trans W''. }
    split; first done.
    split; first by repeat econstructor. done.
  - destruct (He2 h'' W'') as (v2 & h''' & W''' & Hwext''' & Hsat''' & Hb2 & Hv2); [|done|].
    { by trans W'. }
    exists v2, h''', W'''. split.
    { by trans W''. }
    split; first done.
    split; first by repeat econstructor. done.
Qed.

Lemma compat_app Delta Gamma e1 e2 A B :
  TY Delta; Gamma |= e1 : (A -> B) ->
  TY Delta; Gamma |= e2 : A ->
  TY Delta; Gamma |= (e1 e2) : B.
Proof.
  intros Hfun Harg delta W gamma Hctx; simpl.
  simp type_interp. intros h' W' Hext' Hsat'.

  specialize (Harg _ _ _ Hctx). simp type_interp in Harg.
  destruct (Harg h' W') as (v2 & h'' & W'' & Hwext'' & Hsat'' & Hbs2 & Hv2); [done..|].
  specialize (Hfun _ _ _ Hctx). simp type_interp in Hfun.
  destruct (Hfun h'' W'') as (v1 & h''' & W''' & Hwext''' & Hsat''' & Hbs1 & Hv1); [|done|].
  { by trans W'. }
  simp type_interp in Hv1. destruct Hv1 as (e & -> & Hv1).

  specialize (Hv1 v2 W''').
  eapply type_interp_mono in Hv2.
  1: apply Hv1 in Hv2.
  2-3: done.
  simp type_interp in Hv2.
  destruct (Hv2 h''' W''') as (v & h'''' & W'''' & Hwext'''' & Hsat'''' & Hbsv & Hv); [done..|].

  exists v, h'''', W''''. split.
  { trans W''; first done. by trans W'''. }
  split; first done.
  split; last done.
  eauto.
Qed.

Lemma compat_lam Delta Gamma e A B :
  TY Delta; (A :: Gamma) |= e : B ->
  TY Delta; Gamma |= (Lam e) : (A -> B).
Proof.
  intros Hbody delta W gamma Hctxt. simpl.
  apply val_inclusion with (v := (lam: _)%V).
  simp type_interp.
  eexists _. split; first done.

  intros v W' Hext' Hv.
  asimpl. eapply (Hbody _ _ (of_val v .: gamma)).
  eapply sem_ctx_rel_cons; first done.
  eapply sem_ctx_rel_mono; done.
Qed.

Lemma compat_pair Delta Gamma e1 e2 A B :
  TY Delta; Gamma |= e1 : A ->
  TY Delta; Gamma |= e2 : B ->
  TY Delta; Gamma |= (e1, e2) : A * B.
Proof.
  intros He1 He2 delta W gamma Hctx. simpl.
  simp type_interp. intros h' W' Hext' Hsat'.
  specialize (He2 _ _ _ Hctx). simp type_interp in He2.
  destruct (He2 h' W') as (v2 & h'' & W'' & Hwext'' & Hsat'' & Hb2 & Hv2); [done..|].
  specialize (He1 _ _ _ Hctx). simp type_interp in He1.
  destruct (He1 h'' W'') as (v1 & h''' & W''' & Hwext''' & Hsat''' & Hb1 & Hv1); [|done|].
  { by trans W'. }
  exists (v1, v2)%V, h''', W'''. split.
  { by trans W''. }
  split; first done. split; first by eauto.
  simp type_interp. exists v1, v2. split; first done.
  split; first done. by eapply type_interp_mono.
Qed.

Lemma compat_fst Delta Gamma e A B :
  TY Delta; Gamma |= e : A * B ->
  TY Delta; Gamma |= Fst e : A.
Proof.
  intros He delta W gamma Hctx. simpl.
  simp type_interp. intros h' W' Hext' Hsat'.
  specialize (He _ _ _ Hctx). simp type_interp in He.
  destruct (He h' W') as (v & h'' & W'' & Hwext'' & Hsat'' & Hb & Hv); [done..|].
  simp type_interp in Hv. destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).
  exists v1, h'', W''. eauto.
Qed.

Lemma compat_snd Delta Gamma e A B :
  TY Delta; Gamma |= e : A * B ->
  TY Delta; Gamma |= Snd e : B.
Proof.
  intros He delta W gamma Hctx. simpl.
  simp type_interp. intros h' W' Hext' Hsat'.
  specialize (He _ _ _ Hctx). simp type_interp in He.
  destruct (He h' W') as (v & h'' & W'' & Hwext'' & Hsat'' & Hb & Hv); [done..|].
  simp type_interp in Hv. destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).
  exists v2, h'', W''. eauto.
Qed.

Lemma compat_tapp Delta Gamma e A B :
  TY Delta; Gamma |= e : (forall: B) ->
  TY Delta; Gamma |= (e <>) : (B.[A/]).
Proof.
  intros He delta W gamma Hctx. simpl.
  simp type_interp. intros h' W' Hext' Hsat'.

  specialize (He _ _ _ Hctx). simp type_interp in He.
  destruct (He h' W') as (v & h'' & W'' & Hwext'' & Hsat'' & Hb & Hv); [done..|].
  simp type_interp in Hv.
  destruct Hv as (e1 & -> & He1).

  (* [set] is used to introduce a short-hand. It is basically a local definition. *)
  set tau := syn_type_sem A delta.
  specialize (He1 tau).
  simp type_interp in He1.
  destruct (He1 h'' W'') as (v & h''' & W''' & Hwext''' & Hsat''' & Hb2 & Hv); [done..|].
  exists v, h''', W'''. split.
  { by trans W''. }
  split; first done. split. { econstructor; done. }
  apply sem_val_rel_move_single_subst. done.
Qed.

Lemma compat_tlam Delta Gamma e A :
  TY S Delta; (upctx Gamma) |= e : A ->
  TY Delta; Gamma |= (Lam: e) : (forall: A).
Proof.
  intros He delta W gamma Hctx. simpl.
  apply val_inclusion with (v := (Lam: _)%V).
  simp type_interp.
  eexists _. split_and!; first done.
  intros tau. eapply He.
  by eapply sem_ctx_rel_upctx.
Qed.

Lemma compat_pack Delta Gamma e n A B :
  TY n; Gamma |= e : A.[B/] ->
  TY n; Gamma |= (pack e) : (exists: A).
Proof.
  intros He delta W gamma Hctx. simpl.
  simp type_interp. intros h' W' Hext' Hsat'.

  specialize (He _ _ _ Hctx). simp type_interp in He.
  destruct (He h' W') as (v & h'' & W'' & Hwext'' & Hsat'' & Hb & Hv); [done..|].
  exists (PackV v), h'', W''. split; first done. split; first done.
  split; first by eauto.

  simp type_interp. exists v. split; first done.
  exists (syn_type_sem B delta).
  apply sem_val_rel_move_single_subst. done.
Qed.

Lemma compat_unpack n Gamma A B e e' :
  TY n; Gamma |= e : (exists: A) ->
  TY S n; A :: (upctx Gamma) |= e' : B.[ren (+1)] ->
  TY n; Gamma |= (unpack e in e') : B.
Proof.
  intros He He' delta W gamma Hctx. simpl.
  simp type_interp. intros h' W' Hext' Hsat'.

  specialize (He _ _ _ Hctx). simp type_interp in He.
  destruct (He h' W') as (v & h'' & W'' & Hwext'' & Hsat'' & Hb & Hv); [done..|].
  simp type_interp in Hv. destruct Hv as (v' & -> & tau & Hv').

  specialize (He' (tau .: delta) W'' (of_val v' .: gamma)).
  feed specialize He'.
  { eapply sem_ctx_rel_cons; first done. apply sem_ctx_rel_upctx.
    eapply sem_ctx_rel_mono; first done. by trans W'. }

  simp type_interp in He'.
  destruct (He' h'' W'') as (v & h''' & W''' & Hwext''' & Hsat''' & Hb' & Hv); [done..|].
  exists v, h''', W'''. split.
  { by trans W''. }
  split; first done. split.
  { econstructor; first done. asimpl. done. }
  by eapply sem_val_rel_up.
Qed.

Lemma compat_new Delta Gamma e a :
  TY Delta; Gamma |= e : a ->
  TY Delta; Gamma |= new e : (Ref a).
Proof.
  intros He delta W gamma Hctx. simpl.
  simp type_interp. intros h' W' Hext' Hsat'.

  specialize (He _ _ _ Hctx). simp type_interp in He.
  destruct (He h' W') as (v & h'' & W'' & Hwext'' & Hsat'' & Hb & Hv); [done..|].
  simp type_interp in Hv.

  eexists _, _, (W'' ++ [loc_type_inv _ a]). split_and!.
  { by apply prefix_app_r. }
  2:{ econstructor; done. }
  { eapply wsat_alloc; [done| |].
    - apply not_elem_of_dom, is_fresh.
    - rewrite syn_fo_typed_val. done. }

  simp type_interp. eexists _, (length W''). split; first done.
  rewrite lookup_app_r; last done.
  replace (length W'' - length W'') with 0 by lia.
  done.
Qed.

Lemma compat_load Delta Gamma e a :
  TY Delta; Gamma |= e : Ref a ->
  TY Delta; Gamma |= !e : a.
Proof.
  intros He delta W gamma Hctx. simpl.
  simp type_interp. intros h' W' Hext' Hsat'.

  specialize (He _ _ _ Hctx). simp type_interp in He.
  destruct (He h' W') as (v & h'' & W'' & Hwext'' & Hsat'' & Hb & Hv); [done..|].
  simp type_interp in Hv. destruct Hv as (l & i & -> & Hinv).

  eapply wsat_load in Hinv as (v & Hh & Hv); last done.
  exists v, h'', W''. split; first done. split; first done. split.
  - econstructor; done.
  - eapply syn_fo_typed_val. done.
Qed.

Lemma compat_store Delta Gamma e1 e2 a :
  TY Delta; Gamma |= e1 : Ref a ->
  TY Delta; Gamma |= e2 : a ->
  TY Delta; Gamma |= (e1 <- e2) : a.
Proof.
  intros He1 He2 delta W gamma Hctx. simpl.
  simp type_interp. intros h' W' Hext' Hsat'.

  specialize (He2 _ _ _ Hctx). simp type_interp in He2.
  destruct (He2 h' W') as (w & h'' & W'' & Hwext'' & Hsat'' & Hb2 & Hv2); [done..|].
  specialize (He1 _ _ _ Hctx). simp type_interp in He1.
  destruct (He1 h'' W'') as (v & h''' & W''' & Hwext''' & Hsat''' & Hb1 & Hv1); [|done|].
  { by trans W'. }
  simp type_interp in Hv1. destruct Hv1 as (l & i & -> & Hinv).

  edestruct (wsat_load Hsat''' Hinv) as (v & Hh & _).
  eexists w, _, W'''. split_and!.
  { by trans W''. }
  2:{ econstructor; done. }
  { eapply wsat_store; [done..|]. eapply syn_fo_typed_val. done. }
  by eapply type_interp_mono.
Qed.

(** Semantic soundness theorem *)

Theorem sem_soundness Delta Gamma e A :
  TY Delta; Gamma |- e : A ->
  TY Delta; Gamma |= e : A.
Proof.
  induction 1.
  - by eapply compat_var.
  - by eapply compat_lam.
  - by eapply compat_app.
  - by eapply compat_tlam.
  - by eapply compat_tapp.
  - by eapply compat_pack.
  - by eapply compat_unpack.
  - by eapply compat_int.
  - by eapply compat_bool.
  - by eapply compat_unit.
  - by eapply compat_if.
  - by eapply compat_binop.
  - by eapply compat_pair.
  - by eapply compat_fst.
  - by eapply compat_snd.
  - by eapply compat_load.
  - by eapply compat_store.
  - by eapply compat_new.
Qed.

(* Some dummy type interpretation. *)
Definition delta_emp : tyvar_interp.
Proof.
  intros _.
  pose_sem_type (fun W v => False) as tau.
  { intros. done. }
  exact tau.
Defined.

Corollary sem_soundness_closed e A W :
  TY 0; [] |- e : A ->
  sem_expr_rel A delta_emp W e.
Proof.
  intros Hsem%sem_soundness.
  specialize (Hsem delta_emp W ids).
  asimpl in Hsem. apply Hsem. eapply sem_ctx_rel_nil.
Qed.

Corollary termination h e A :
  (TY 0; [] |- e : A)%ty ->
  exists h' v, big_step (h, e) (h', v).
Proof.
  intros Hsem%(sem_soundness_closed _ _ []).
  simp type_interp in Hsem.
  edestruct Hsem as (v & h' & _ & _ & _ & Hbs & _); first done.
  { apply wsat_empty. }
  eauto.
Qed.

(** Semantic typing admits subtitution principles similar to syntactic typing. *)
Lemma sem_type_subst_one Delta Gamma e1 B e A :
  TY Delta; Gamma |= e1 : B ->
  TY Delta; B :: Gamma |= e : A ->
  TY Delta; Gamma |= e.[e1/] : A.
Proof.
  intros He1 He delta W gamma Hctx. asimpl. eapply He.
  intros x B'. destruct x as [|x].
  - simpl. intros [= <-]. eapply He1. done.
  - simpl. eapply Hctx.
Qed.

Lemma sem_type_safety e A :
  TY 0; [] |= e : A ->
  forall h, safe h e.
Proof.
  intros Hsem h.
  specialize (Hsem delta_emp [] ids).
  simp type_interp in Hsem.
  edestruct Hsem as (v & h' & _ & _ & _ & Hevals & _).
  { eapply sem_ctx_rel_nil. }
  { reflexivity. }
  { eapply wsat_empty. }
  eapply big_step_safe.
  asimpl in Hevals. exact Hevals.
Qed.

Corollary type_safety e A :
  TY 0; [] |- e : A ->
  forall h, safe h e.
Proof.
  intros Htyped. eapply sem_type_safety. eapply sem_soundness. done.
Qed.
