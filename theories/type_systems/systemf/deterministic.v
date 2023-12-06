From stdpp Require Import gmap base relations.
From ffpl.lib Require Import prelude.
From ffpl.type_systems.systemf Require Import lang notation.
From Equations Require Import Equations.

(** Proof that our small-step semantics are deterministic. *)

Lemma base_step_det e e1 e2 :
  base_step e e1 -> base_step e e2 -> e1 = e2.
Proof.
  inversion 1; inversion 1; subst; congruence.
Qed.

(** We need this very technical lemma with tons of cases. None of the cases is
very interesting. We use some Coq tactic programming to handle them all
automatically. *)

Lemma base_redex_unique K1 e1 e1' K2 e2 e2' :
  fill K1 e1 = fill K2 e2 ->
  base_step e1 e1' ->
  base_step e2 e2' ->
  K1 = K2 /\ e1 = e2.
Proof.
  induction K1 in K2, e2, e2' |- *; simpl.
  all: destruct K2; intros; simplify_eq/=.
  all: repeat match goal with
      | H : ?e' = fill ?K ?e |- _ =>
          (* maybe [e'] is a value *)
          let Hval := fresh "Hval" in
          assert (is_val e') as Hval by (by eauto);
          rewrite H in Hval;
          clear H (* avoid loops *)
      | H : fill ?K ?e = of_val _ |- _ =>
          symmetry in H (* make it hit the case above *)
      | H : is_val (fill _ _) |- _ =>
          apply fill_is_val_inv in H
      | H : to_val (fill _ _) = Some _ |- _ =>
          apply is_val_to_val in H
      | H1 : is_val ?e, H2 : base_step ?e _ |- _ =>
          apply base_step_no_val in H2; done
      | H : fill _ ?e1 = fill _ ?e2, H1 : base_step ?e1 _, H2 : base_step ?e2 _ |- _ =>
          destruct (IHK1 _ _ _ H H1 H2); simplify_eq/=; by eauto
      | H : base_step _ _ |- _ =>
          inversion H;
          simplify_eq/=;
          [clear H] (* also asserts that there is exactly one goal *)
      | H : base_step _ _ |- _ =>
          inversion H;
          simplify_eq/=;
          done (* sometimes this closes all goals *)
      | H : base_step _ _ |- _ =>
          inversion H;
          simplify_eq/=;
          [clear H|clear H] (* for if, we need to allow 2 goals *)
      end.
Qed.

Lemma contextual_step_det {e e1 e2} :
  contextual_step e e1 -> contextual_step e e2 -> e1 = e2.
Proof.
  inversion 1; inversion 1; subst.
  edestruct base_redex_unique; [done|done|done|subst].
  f_equal. eapply base_step_det; done.
Qed.

(** It follows that if [e] can step to two different terms, then
really one is just a more reduced form of the other. *)
Lemma contextual_steps_det {e e1 e2} :
  rtc contextual_step e e1 ->
  rtc contextual_step e e2 ->
  (rtc contextual_step e1 e2 \/ rtc contextual_step e2 e1).
Proof.
  induction 1 as [e|e e1 e1' Hstep1 Hsteps1 IH] in e2 |- *.
  { eauto. }
  destruct 1 as [e|e e2 e2' Hstep2 Hsteps2].
  { right. econstructor; done. }
  pose proof (contextual_step_det Hstep1 Hstep2) as ->.
  eapply IH. done.
Qed.
