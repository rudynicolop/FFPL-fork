From stdpp Require Import base relations tactics.
From ffpl.lib Require Import prelude sets maps.
From ffpl.type_systems.stlc Require Import lang types closed notation.

Lemma big_step_deterministic (e : expr) (v w : val) :
  big_step e v -> big_step e w -> v = w.
(* REMOVE *) Proof.
  induction 1 in w |- *; inversion 1; try eauto; simplify_eq.
  - (* or just: naive_solver. *)
    apply IHbig_step1 in H4.
    apply IHbig_step2 in H6.
    congruence.
  - (* or just: naive_solver. *)
    apply IHbig_step1 in H5.
    apply IHbig_step2 in H6.
    simplify_eq.
    by apply IHbig_step3 in H8.
Qed.

Lemma fill_contextual_step_rtc K e1 e2 :
  rtc contextual_step e1 e2 -> rtc contextual_step (fill K e1) (fill K e2).
(* REMOVE *) Proof.
  induction 1.
  - done.
  - eapply rtc_l.
    * by apply fill_contextual_step.
    * done.
Qed.

Lemma base_step_step e1 e2 :
  base_step e1 e2 -> step e1 e2.
(* REMOVE *) Proof.
  destruct 1; subst.
  - eauto.
  - by econstructor.
Qed.

Lemma fill_step K e1 e2 :
  step e1 e2 -> step (fill K e1) (fill K e2).
(* REMOVE *) Proof.
  induction K as [|Ki K IH] in e1, e2 |- *; first done.
  destruct Ki; simpl; eauto.
Qed.

Lemma contextual_step_step e1 e2 :
  contextual_step e1 e2 -> step e1 e2.
(* REMOVE *) Proof.
  destruct 1 as [K h1 h2 -> -> Hstep].
  eapply fill_step, base_step_step, Hstep.
Qed.

(** Here, you are asked to do the remaining case of progress, which we skipped
over in class. See types.v for solution. *)
Theorem type_progress e A :
  empty |- e : A -> progressive e.
Proof.
  remember empty as Gamma. induction 1 as [??? Hx| | | Gamma e1 e2 A B Hty IH1 _ IH2 | Gamma e1 e2 Hty1 IH1 Hty2 IH2].
  - subst.
    (** The lemma [lookup_empty] shows that [empty !! x = None], which in this
    case suffices to complete the proof by contradiction. *)
    rewrite lookup_empty in Hx. done.
  - left. done.
  - left. done.
  - destruct (IH2 HeqGamma) as [H2|H2]; [destruct (IH1 HeqGamma) as [H1|H1]|].
    + eapply canonical_values_arr in Hty as (x & e & ->); last done.
      right. eexists.
      eapply base_contextual_step, BetaS; eauto.
    + right. eapply is_val_spec in H2 as [v Heq].
      replace e2 with (of_val v); last by eapply of_to_val.
      destruct H1 as [e1' Hstep].
      eexists. eapply (fill_contextual_step [AppLCtx v]). done.
    + right. destruct H2 as [e2' H2].
      eexists. eapply (fill_contextual_step [AppRCtx e1]). done.
  -
Admitted.

(** Corollary 15 *)
Corollary type_safety e1 e2 A:
  empty |- e1 : A ->
  rtc contextual_step e1 e2 ->
  progressive e2.
(* REMOVE *) Proof.
  induction 2; eauto using type_progress, type_preservation.
Qed.
