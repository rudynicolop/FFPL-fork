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
  - reflexivity.
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

Definition zero : val := lam: "o" "s", "o".

Definition succ (n : val) : val := lam: "o" "s", "s" n.

Fixpoint enc_nat (n : nat) : val :=
  match n with
  | O => zero
  | S n => succ (enc_nat n)
  end.

(** When doing these proofs in Coq we realize that we care about whether a term
is "closed". A term is said to be closed if all variables it mentions are bound
inside the term. This is useful since closed terms do not change under
substitution (lemma [subst_closed_nil]).  *)
Lemma enc_nat_closed n :
  closed [] (enc_nat n).
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
  (** This can be automated better! All those sequences of [econstructor]
  and [apply is_val_val] can be handled by [eauto] if we just tell it which
  lemmas to apply. *)
#[local] Hint Constructors step : core.
#[local] Hint Resolve is_val_of_val : core.
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
  is_closed [] z ->
  rtc step (enc_nat 0 z s) z.
Proof.
  intros Hcl. simpl.
  eapply rtc_l.
  { eauto. }
  simpl. eapply rtc_l.
  { eauto. }
  rewrite subst_closed_nil; done.
Qed.

(** [Succ] can be seen as a constructor in the language: it takes a
representation of [n] and returns a representation of [S n]. *)
Definition Succ : val := lam: "n" "o" "s", "s" "n".

Lemma Succ_red n : step (Succ (enc_nat n)) (enc_nat (S n)).
Proof. econstructor; auto. Qed.

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
  care of side-conditions like the [is_value] that comes up. *)
  Ltac solve_step := repeat (simpl; econstructor; try by eauto).
  (** When to reduce the term by one step, we apply [rtc_l] and
  solve the [step] goal that this will open. *)
  Ltac one_step := eapply rtc_l; first (by solve_step); simpl.
  (** Now we can repeat that until the term is as reduced as it gets. *)
  repeat one_step. done.
Qed.

(** We prove that it satisfies the recursive unfolding. *)
Lemma Fix_step (s r : val) :
  is_closed [] s ->
  rtc step (Fix s r) (s ((Fix s))%E r).
Proof.
  intros Hclosed.
  eapply rtc_l.
  { econstructor. auto. }
  eapply rtc_l.
  { simpl. econstructor; first by auto.
    econstructor. { rewrite subst_closed_nil; auto. }
    econstructor. done.
  }
  simpl. rewrite subst_closed_nil; last done.
  eapply rtc_l.
  { econstructor; first by auto.
    econstructor. auto.
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
  is_val e -> closed [] e -> is_val (subst n x e).
Proof. intros. rewrite subst_closed_nil; auto. Qed.
#[local] Hint Resolve is_val_subst : core.

Lemma Fix_step (s r : val) :
  is_closed [] s ->
  rtc step (Fix s r) (s ((Fix s))%E r).
Proof.
  intros Hclosed.
  do 2 one_step.
  rewrite subst_closed_nil; last done.
  by one_step.
Qed.

(** Example usage: addition on Scott-encoded numbers *)
Definition add_step : val := lam: "rec", lam: "n" "m", "n" "m" (lam: "n'", Succ ("rec" "n'" "m")).
Definition add := Fix add_step.

(** We are now going to prove it correct:
 [add (enc_nat n) (enc_nat m))] steps to [(enc_nat (n + m))]

 First, we prove that it satisfies the expected defining equations for Peano addition.
 *)

Lemma add_step_0 m : rtc step (add (enc_nat 0) (enc_nat m)) (enc_nat m).
Proof.
  (* use the unfolding equation of the fixpoint combinator *)
  etrans.
  { eapply steps_app_l; first by auto.
    eapply Fix_step. done.
  }
  (* subst it into the [add_step] function *)
  one_step.
  (* Sadly now it becomes hard to see what we are doing, since all definitions
  are unfolded. Let us introduce some abbreviations to make the term slightly
  more readable. *)
  set FixE' := (lam: "f'" "F", "F" (lam: "x", "f'" "f'" "F" "x"))%E.
  (* Note that [FixE'] is not the same as [Fix']! The former is an expression,
  the latter is a value. That's why we cannot directly use [Fix']. *)
  set add_stepE := (lam: "rec", lam: "n" "m", "n" "m" (lam: "n'", Succ ("rec" "n'" "m")))%E.
  set addE := (lam: "x", Fix' Fix' add_stepE "x")%E.
  (* subst in the zero *)
  one_step.
  rewrite -/FixE' -/add_stepE -/addE.
  (* subst in the m *)
  one_step.
  rewrite -/FixE' -/add_stepE -/addE.
  (* do a step *)
  etrans.
  { apply (enc_0_red (enc_nat m) (lam: "n'", Succ (Fix add_step "n'" (enc_nat m)))).
    apply enc_nat_closed.
  }
  reflexivity.
Qed.

Lemma add_step_S n m : rtc step (add (enc_nat (S n)) (enc_nat m)) (Succ (add (enc_nat n) (enc_nat m))).
Proof.
  (* use the unfolding equation of the fixpoint combinator *)
  etrans.
  { eapply steps_app_l; first by auto.
    eapply Fix_step. done.
  }
  (* subst it into the [add_step] function *)
  one_step.
  (* subst in the zero *)
  one_step.
  (* subst in the m *)
  one_step.
  (* do a step *)
  etrans.
  { rewrite subst_closed_nil; last apply enc_nat_closed.
    apply (enc_S_red n (enc_nat m) (lam: "n'", Succ (Fix add_step "n'" (enc_nat m)))).
  }

  one_step.
  rewrite subst_closed_nil; last apply enc_nat_closed.
  reflexivity.
Qed.

Lemma add_correct n m : rtc step (add (enc_nat n) (enc_nat m)) (enc_nat (n + m)).
Proof.
  induction n as [ | n IH].
  - apply add_step_0.
  - etrans. { apply add_step_S. }
    etrans. { apply steps_app_r. apply IH. }
    eapply rtc_l. { apply Succ_red. }
    reflexivity.
Qed.
