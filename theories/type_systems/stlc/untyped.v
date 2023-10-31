From stdpp Require Import base relations tactics.
From ffpl.lib Require Import prelude.
From ffpl.type_systems.stlc Require Import lang closed notation.

(** The following two lemmas will be helpful in the sequel.
  They just lift multiple reduction steps (via [rtc]) to application.
 *)
Lemma steps_app_r (e1 e2 e2' : expr) :
  rtc step e2 e2' ->
  rtc step (e1 e2) (e1 e2').
Proof.
  induction 1 as [ e | e e' e'' Hstep Hsteps IH].
  - (** [reflexivity] works not only on [=], but on reflexive relations in general. *)
    reflexivity.
  - eapply (rtc_l _ _ (e1 e')).
    { by eapply StepAppR. }
    done.
Qed.

Lemma steps_app_l (e1 e1' e2 : expr) :
  is_val e2 ->
  rtc step e1 e1' ->
  rtc step (e1 e2) (e1' e2).
Proof.
  intros Hv.
  induction 1 as [ e | e e' e'' Hstep Hsteps IH].
  - reflexivity.
  - eapply (rtc_l _ _ (e' e2)).
    { by eapply StepAppL. }
    done.
Qed.


(** * Untyped Lambda Calculus *)

(** We do not re-define the language to remove primitive addition -- instead, we just
  restrict our usage in this file to variables, application, and lambdas.
*)


Definition omega : val := lam: "x", "x" "x".
Definition Omega : expr := omega omega.


(** Omega reduces to itself! *)
Lemma Omega_step : step Omega Omega.
Proof.
  apply StepBeta. done.
Qed.

(** ** Scott encodings *)

(** Since the Scott-encoded terms can become rather large, we also use this
opportunity to introduce some of the automation facilities of Coq that help
dealing with larger terms. *)

Definition zero : val := lam: "z" "s", "z".

Fixpoint enc_nat (n : nat) : val :=
  match n with
  | O => zero
  | S n => lam: "z" "s", "s" (enc_nat n)
  end.

Compute (enc_nat 1).

(** [Succ] can be seen as a constructor in the language: it takes a
representation of [n] and returns a representation of [S n]. *)
Definition Succ : val := lam: "n" "z" "s", "s" "n".

(** This computes as we would expect. *)
Example three : step (Succ (enc_nat 2)) (enc_nat 3).
Proof. apply StepBeta. apply is_val_of_val. Qed.

(** When doing these proofs in Coq we realize that we care about whether a term
is "closed". A term is said to be closed if all variables it mentions are bound
inside the term. This is useful since closed terms do not change under
substitution (lemma [subst_closed_nil]).  *)
Lemma enc_nat_closed n :
  closed empty (enc_nat n).
Proof.
  induction n as [ | n IH].
  - done.
  - simpl. by apply closed_weaken_nil.
Qed.

Lemma enc_S_red n (z s : val) :
  rtc step (enc_nat (S n) z s) (s (enc_nat n)).
Proof.
  simpl. eapply rtc_l.
  { (** The [econstructor] tactic is like [eapply] for inductive predicates:
    here the predicate is [step], so [econstructor] will try to [eapply]
    each of [step]'s constructors. In this case [StepBeta] will succeed. *)
    econstructor.
    { apply is_val_of_val. }
    econstructor.
    apply is_val_of_val.
  }
  simpl. eapply rtc_l.
  { econstructor. apply is_val_of_val. }
  simpl. rewrite (subst_closed_nil (enc_nat n)); last apply enc_nat_closed.
  rewrite subst_closed_nil; last apply enc_nat_closed.
  reflexivity.
Restart.
  (** This can be automated better! We can use the hints that [lang.v] added to [eauto]. *)
  simpl. eapply rtc_l.
  { eauto. }
  simpl. eapply rtc_l.
  { eauto. }
  (** The interesting part of the proof we still have to do ourselves. *)
  simpl. rewrite (subst_closed_nil (enc_nat n)); last apply enc_nat_closed.
  rewrite subst_closed_nil; last apply enc_nat_closed.
  reflexivity.
Qed.

Lemma enc_0_red (z s : val) :
  is_closed empty z ->
  rtc step (enc_nat 0 z s) z.
Proof.
  intros Hcl. simpl.
  eapply rtc_l.
  { eauto. }
  simpl. eapply rtc_l.
  { eauto. }
  rewrite subst_closed_nil; done.
Qed.

Lemma Succ_red n : step (Succ (enc_nat n)) (enc_nat (S n)).
Proof. econstructor; eauto. Qed.

Lemma Succ_red_n n : rtc step (Nat.iter n Succ zero) (enc_nat n).
Proof.
  induction n as [ | n IH].
  - reflexivity.
  - simpl. eapply rtc_transitive.
    { eapply steps_app_r. apply IH. }
    eapply rtc_l.
    { apply Succ_red. }
    reflexivity.
Qed.

(** ** Recursion *)
Definition Fix' : val := lam: "f'" "F", "F" (lam: "x", "f'" "f'" "F" "x").
Definition Fix (F : val) : val := lam: "x", Fix' Fix' F "x".
Arguments Fix : simpl never.

(** Example usage: multiplication by 2 *)
Definition mul2_step : val := lam: "rec", lam: "n", "n" zero (lam: "n'", Succ  (Succ ("rec" "n'"))).
Definition mul2 := Fix mul2_step.

Example mul2_2 : rtc step (mul2 (enc_nat 2)) (enc_nat 4).
Proof.
  (** Reducing a term of this size one step at a time gets really tedious.
  We could try to add more hints to [eauto] to make that work, but [eauto]
  is pretty bad at unfolding definitions like [mul2] or [Fix]. So instead
  we directly use tactics like [econstructor] that are more expensive
  but also better at looking through definitions. [by eauto] takes
  care of side-conditions like the [is_value] that comes up.
  We [repeat] because after applying a rule such as [StepAppR],
  we need to use another constructor to reduce a term below the application.

  We do not expect you to be able to come up with tactics like this,
  but we will provide them when they are useful and explain
  what they do. *)
  Ltac solve_step := repeat (econstructor; try by eauto).
  (** To reduce the term by one step, we apply [rtc_l] and
  solve the [step] goal that this will open. *)
  Ltac one_step := eapply rtc_l; first (by solve_step); simpl.
  (** Now we can repeat that until the term is as reduced as it gets. *)
  repeat one_step. done.
Qed.

(** We prove that [fix] satisfies the recursive unfolding. *)
Lemma Fix_step (s r : val) :
  is_closed empty s ->
  rtc step (Fix s r) (s ((Fix s))%E r).
Proof.
  intros Hclosed.
  eapply rtc_l.
  { econstructor. eauto. }
  eapply rtc_l.
  { simpl. econstructor; first by eauto.
    econstructor. { rewrite subst_closed_nil; eauto. }
    econstructor. done.
  }
  simpl. rewrite subst_closed_nil; last done.
  eapply rtc_l.
  { econstructor; first by eauto.
    econstructor. eauto.
  }
  simpl. reflexivity.
Restart.
  (** Having to step through these computations is getting a bit tiring,
  let's use our tactics from before! *)
  intros Hclosed.
  one_step.
  (** Here, [one_step] doesn't work. The issue is the [is_val (subst "x" r s)]
  subgoal which we handled via [subst_closed_nil] above. *)
Abort.

(** Let's define a lemma that helps with those goals, and teach [eauto]
about it. Then [solve_step] will pick it up thanks to its use of [by eauto]
for side-conditions. *)
Lemma is_val_subst n x e :
  is_val e -> closed empty e -> is_val (subst n x e).
Proof. intros. rewrite subst_closed_nil; eauto. Qed.
#[local] Hint Resolve is_val_subst : core.

Lemma Fix_step (s r : val) :
  is_closed empty s ->
  rtc step (Fix s r) (s ((Fix s))%E r).
Proof.
  intros Hclosed.
  do 2 one_step.
  rewrite subst_closed_nil; last done.
  by one_step.
Qed.

(** Now we can prove that [mul2] behaves the way we want. *)
Lemma mul2_step_0 : rtc step (mul2 zero) zero.
Proof. repeat one_step. done. Qed.

Lemma mul2_step_S n : rtc step (mul2 (enc_nat (S n))) (Succ (Succ (mul2 (enc_nat n)))).
Proof.
  (** The [etrans] tactic works on transitive relations. It applies transitivity
  and introduces an evar for the new term "in the middle". Here is is equivaleny
  to (and shorter than) [eapply rtc_transitive]. *)
  etrans.
  { eapply Fix_step.
    (* We need to tell Coq to efficiently compute this term,
    or else it might take forever. *)
    vm_compute. done. }
  (* beta-reduce [mul2_step]'s 2 arguments. *)
  do 2 one_step.
  (* Sadly now it becomes hard to see what we are doing, since all definitions
  are unfolded. But we know what this is so we can [change] to a readbale goal. *)
  change (rtc step ((enc_nat (S n)) zero (lam: "n'", Succ (Succ (mul2 "n'")))) (Succ (Succ (mul2 (enc_nat n)))))%E.
  (* After 2 beta-reductions we have reduced away the case distinction *)
  simpl. do 2 one_step.
  (* This involves [subst] into the closed value [enc_nat], let's get rid of that. *)
  rewrite (subst_closed_nil (enc_nat _)); last apply enc_nat_closed.
  rewrite subst_closed_nil; last apply enc_nat_closed.
  (* Now we can make the goal nice again. *)
  change (rtc step ((lam: "n'", Succ (Succ (mul2 "n'"))) (enc_nat n)) (Succ (Succ (mul2 (enc_nat n)))))%E.
  (* And we are just a single beta-reduction away from being done! *)
  one_step. done.
Qed.

Lemma mul2_correct n : rtc step (mul2 (enc_nat n)) (enc_nat (2 * n)).
Proof.
  induction n as [|n' IH].
  - apply mul2_step_0.
  - etrans.
    { apply mul2_step_S. }
    (* Reduce the [mul2 (enc_nat n')] under the two [Succ]. *)
    etrans.
    { eapply steps_app_r, steps_app_r. done. }
    (* Reduce the [Succ]. *)
    eapply rtc_l.
    { eapply StepAppR, Succ_red. }
    eapply rtc_l.
    { eapply Succ_red. }
    (* lia helps us to shape the goal. *)
    replace (2 * S n')%nat with (S (S (2 * n'))) by lia.
    done.
Qed.
