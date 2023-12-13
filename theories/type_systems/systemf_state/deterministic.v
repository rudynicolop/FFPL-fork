From stdpp Require Import gmap base relations.
From ffpl.lib Require Import prelude.
From ffpl.type_systems.systemf_state Require Import lang notation.
From Equations Require Import Equations.

(** Proof that our small-step semantics are deterministic. *)

Lemma base_step_det h e h1 e1 h2 e2 :
  base_step (h, e) (h1, e1) -> base_step (h, e) (h2, e2) -> h1 = h2 /\ e1 = e2.
Proof.
  inversion 1; inversion 1; subst; split; congruence.
Qed.

(** We need this very technical lemma with tons of cases. None of the cases is
very interesting. We use some Coq tactic programming to handle them all
automatically. *)

Lemma base_redex_unique K1 h e1 h1' e1' K2 e2 h2' e2' :
  fill K1 e1 = fill K2 e2 ->
  base_step (h, e1) (h1', e1') ->
  base_step (h, e2) (h2', e2') ->
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
      | H1 : is_val ?e, H2 : base_step (_, ?e) _ |- _ =>
          apply base_step_no_val in H2; done
      | H : fill _ ?e1 = fill _ ?e2, H1 : base_step (_, ?e1) _, H2 : base_step (_, ?e2) _ |- _ =>
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

Lemma contextual_step_det {h e h1 e1 h2 e2} :
  contextual_step (h, e) (h1, e1) -> contextual_step (h, e) (h2, e2) -> h1 = h2 /\ e1 = e2.
Proof.
  inversion 1; inversion 1; subst.
  edestruct base_redex_unique; [done|done|done|subst]. split.
  - eapply base_step_det; done.
  - f_equal. eapply base_step_det; done.
Qed.

(** It follows that if [e] can step to two different terms, then
really one is just a more reduced form of the other. *)
Lemma contextual_steps_det {h e h1 e1 h2 e2} :
  rtc contextual_step (h, e) (h1, e1) ->
  rtc contextual_step (h, e) (h2, e2) ->
  (rtc contextual_step (h1, e1) (h2, e2) \/ rtc contextual_step (h2, e2) (h1, e1)).
Proof.
  remember (h, e) as cfg.
  remember (h1, e1) as cfg1.
  remember (h2, e2) as cfg2.
  induction 1 as [cfg|cfg cfg1' cfg1 Hstep1 Hsteps1 IH] in h, e, Heqcfg, h1, h2, Heqcfg1, h2, e2, cfg2, Heqcfg2 |- *.
  { simplify_eq/=. eauto. }
  destruct 1 as [cfg|cfg cfg2' cfg2 Hstep2 Hsteps2].
  { simplify_eq/=. right. econstructor; done. }
  destruct cfg1' as [h1' e1'].
  destruct cfg2' as [h2' e2'].
  simplify_eq/=.
  pose proof (contextual_step_det Hstep1 Hstep2) as [-> ->].
  eapply IH; done.
Qed.
