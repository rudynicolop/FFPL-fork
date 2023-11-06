From stdpp Require Export strings.
From ffpl.lib Require Import prelude.
Global Open Scope Z.

(** * Simply Typed Lambda Calculus *)

(** ** Expressions and values. *)
Inductive expr :=
  (* Base lambda calculus *)
  | Var (x : string)
  | Lam (x : string) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | LitInt (n: Z)
  | Plus (e1 e2 : expr).

Inductive val :=
  | LitIntV (n: Z)
  | LamV (x : string) (e : expr).

(** *** Substitution: replace [x] by [es] in [e]. *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | LitInt n => LitInt n
  (* The function [decide] can be used to decide propositions.
    It can only be applied to propositions for which, by type class inference,
    it can be determined that the proposition is decidable. *)
  | Var y => if decide (x = y) then es else Var y
  | Lam y e =>
      Lam y $ if decide (x = y) then e else subst x es e
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | Plus e1 e2 => Plus (subst x es e1) (subst x es e2)
  end.

(** ** §1.1: Operational Semantics *)

(** *** Small-Step Structural Semantics *)
Definition is_val (e : expr) : Prop :=
  match e with
  | LitInt n => True
  | Lam x e => True
  | _ => False
  end.

(* We use right-to-left evaluation order,
   which means in a binary term (e.g., e1 + e2),
   the left side can only be reduced once the right
   side is fully evaluated (i.e., is a value). *)
Inductive step : expr -> expr -> Prop :=
  | StepBeta x e e'  :
    is_val e' ->
    step (App (Lam x e) e') (subst x e' e)
  | StepAppL e1 e1' e2 :
    is_val e2 ->
    step e1 e1' ->
    step (App e1 e2) (App e1' e2)
  | StepAppR e1 e2 e2' :
    step e2 e2' ->
    step (App e1 e2) (App e1 e2')
  | StepPlus (n1 n2 n3 : Z) :
    n1 + n2 = n3 ->
    step (Plus (LitInt n1) (LitInt n2)) (LitInt n3)
  | StepPlusL e1 e1' e2 :
    is_val e2 ->
    step e1 e1' ->
    step (Plus e1 e2) (Plus e1' e2)
  | StepPlusR e1 e2 e2' :
    step e2 e2' ->
    step (Plus e1 e2) (Plus e1 e2').

Module examples.
Example step_1_plus_1 : step (Plus (LitInt 1) (LitInt 1)) (LitInt 2).
Proof. apply StepPlus. lia. Qed.

Definition plus1 := Lam "x" (Plus (Var "x") (LitInt 1)).
Example step_call_plus_1 : step (App plus1 (LitInt 1)) (Plus (LitInt 1) (LitInt 1)).
Proof. apply StepBeta. done. Qed.
Definition steps := rtc step.
Example steps_call_plus_1 : steps (App plus1 (LitInt 1)) (LitInt 2).
Proof.
  eapply rtc_l.
  - apply step_call_plus_1.
  - apply rtc_once, step_1_plus_1.
Qed.
Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.
Notation "e1 + e2" := (Plus e1 e2) : expr_scope.
Check (LitInt 1 + LitInt 1)%E.
Coercion LitInt : Z >-> expr.

Example step_1_plus_1' : step (1 + 1)%E 2.
Proof. apply StepPlus. lia. Qed.
Notation "'lam:' x , e" := (Lam x e%E)
  (at level 200, x at level 1, e at level 200).
Print plus1.
Coercion Var : string >-> expr.
Print plus1.
Definition plus1' := lam: "x", "x" + 1.
Example step_call_plus_1' : step (App plus1 1) (1 + 1).
Proof. apply StepBeta. done. Qed.
Coercion App : expr >-> Funclass.
Check step (plus1 1) (1 + 1).

End examples.

(** *** Big-Step Semantics *)

(* Injections into expr *)
Definition of_val (v : val) : expr :=
  match v with
  | LitIntV n => LitInt n
  | LamV x e => Lam x e
  end.

(* try to make an expr into a val *)
Definition to_val (e : expr) : option val :=
  match e with
  | LitInt n => Some (LitIntV n)
  | Lam x e => Some (LamV x e)
  | _ => None
  end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  destruct v; simpl; reflexivity.
Qed.

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof.
  destruct e; simpl; try congruence.
  all: injection 1 as <-; simpl; reflexivity.
Qed.

Lemma is_val_spec e : is_val e <-> exists v, to_val e = Some v.
Proof.
  destruct e; simpl.
  (* With [all:], we can apply a tactic to all open subgoals. *)
  all: split; [intros H|intros [v H]]; try done.
  (* [done] can solve almost all of these goals, but it cannot show these two
  existential quantifiers. We could prove them individually by hand now, but
  then we have to manually state the witness that proves the existential.
  Instead we can have Coq infer the witness by using evars (existential
  variables) that we have already seen before with [eapply]: The [eexists]
  tactic turns the quantified variable into an evar. *)
  all: eexists.
  (* Now both of these goals can be proven by reflexivity, which implicitly
  makes Coq choose the right witness for the existentials. *)
  all: done.
Qed.

Lemma is_val_of_val v : is_val (of_val v).
Proof.
  apply is_val_spec. rewrite to_of_val. by eexists.
Qed.

Inductive big_step : expr -> val -> Prop :=
  | BsLitInt (n : Z) :
      big_step (LitInt n) (LitIntV n)
  | BsLam (x : string) (e : expr) :
      big_step (Lam x e) (LamV x e)
  | BsPlus e1 e2 (z1 z2 : Z) :
      big_step e1 (LitIntV z1) ->
      big_step e2 (LitIntV z2) ->
      big_step (Plus e1 e2) (LitIntV (z1 + z2))%Z
  | BisApp e1 e2 x e v2 v :
      big_step e1 (LamV x e) ->
      big_step e2 v2 ->
      big_step (subst x (of_val v2) e) v ->
      big_step (App e1 e2) v
.
Lemma big_step_vals (v : val) : big_step (of_val v) v.
Proof.
  induction v.
  - apply BsLitInt.
  - apply BsLam.
Restart.
  induction v; constructor.
Qed.

Lemma big_step_inv_vals (v w : val) : big_step (of_val v) w -> v = w.
Proof.
  destruct v; inversion 1; congruence.
Qed.

Lemma big_step_deterministic (e : expr) (v w : val) :
  big_step e v -> big_step e w -> v = w.
Proof. (* FILL IN HERE *) Admitted.

Lemma rtc_step_app_l e1 e1' e2:
  rtc step e1 e1' -> is_val e2 -> rtc step (App e1 e2) (App e1' e2).
Proof.
  induction 1 as [|e1 e1' e1'' Hstep Hsteps IH].
  { intros. apply rtc_refl. }
  intros He. eapply rtc_l.
  - econstructor; eassumption.
  - eapply IH. assumption.
Qed.
#[export] Hint Constructors rtc step : core.
Lemma rtc_step_app_r e1 e2 e2':
  rtc step e2 e2' -> rtc step (App e1 e2) (App e1 e2').
Proof.
  induction 1; eauto.
Qed.

Lemma rtc_step_plus_l e1 e1' e2:
  rtc step e1 e1' -> is_val e2 -> rtc step (Plus e1 e2) (Plus e1' e2).
Proof.
  induction 1; eauto.
Qed.

Lemma rtc_step_plus_r e1 e2 e2':
  rtc step e2 e2' -> rtc step (Plus e1 e2) (Plus e1 e2').
Proof.
  induction 1; eauto.
Qed.
#[export] Hint Resolve is_val_of_val : core.

Lemma big_step_step e v :
  big_step e v -> rtc step e (of_val v).
Proof. (* DONE IN CLASS *) Admitted.

(** *** Contextual Semantics *)
Inductive base_step : expr -> expr -> Prop :=
  | BetaS x e1 e2 e' :
     is_val e2 ->
     e' = subst x e2 e1 ->
     base_step (App (Lam x e1) e2) e'
  | PlusS e1 e2 (n1 n2 n3 : Z):
     e1 = (LitInt n1) ->
     e2 = (LitInt n2) ->
     (n1 + n2)%Z = n3 ->
     base_step (Plus e1 e2) (LitInt n3).
Module ectx_on_paper.
Inductive ectx :=
  | HoleCtx
  | AppLCtx (K : ectx) (v2 : val)
  | AppRCtx (e1 : expr) (K : ectx)
  | PlusLCtx (K : ectx) (v2 : val)
  | PlusRCtx (e1 : expr) (K : ectx).

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | AppLCtx K v2 => App (fill K e) (of_val v2)
  | AppRCtx e1 K => App e1 (fill K e)
  | PlusLCtx K v2 => Plus (fill K e) (of_val v2)
  | PlusRCtx e1 K => Plus e1 (fill K e)
  end.
End ectx_on_paper.
Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | PlusLCtx (v2 : val)
  | PlusRCtx (e1 : expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | PlusLCtx v2 => Plus e (of_val v2)
  | PlusRCtx e1 => Plus e1 e
  end.

Definition ectx := list ectx_item.
Definition fill (K : ectx) (e : expr) : expr := foldl (λ e Ki, fill_item Ki e) e K.

Module ectx_on_paper_comparison.

Definition ectx1_on_paper := ectx_on_paper.AppLCtx ectx_on_paper.HoleCtx (LitIntV 1).
Compute (ectx_on_paper.fill ectx1_on_paper examples.plus1).
Definition ectx1 := [AppLCtx (LitIntV 1)].
Compute (fill ectx1 examples.plus1).

Example compare1 :
  ectx_on_paper.fill ectx1_on_paper examples.plus1 = fill ectx1 examples.plus1.
Proof. reflexivity. Qed.

Definition ectx2_on_paper :=
  ectx_on_paper.PlusRCtx (LitInt 40) (ectx_on_paper.AppLCtx ectx_on_paper.HoleCtx (LitIntV 1)).
Compute (ectx_on_paper.fill ectx2_on_paper examples.plus1).
Definition ectx2 := [AppLCtx (LitIntV 1); PlusRCtx (LitInt 40)].
Compute (fill ectx2 examples.plus1).

Example compare2 :
  ectx_on_paper.fill ectx2_on_paper examples.plus1 = fill ectx2 examples.plus1.
Proof. reflexivity. Qed.

End ectx_on_paper_comparison.

Inductive contextual_step (e1 : expr) (e2 : expr) : Prop :=
  EctxStep K e1' e2' :
    e1 = fill K e1' ->
    e2 = fill K e2' ->
    base_step e1' e2' ->
    contextual_step e1 e2.

(* Basic lemmas about the contextual semantics *)
Definition comp_ectx (Ko Ki : ectx) := Ki ++ Ko.
Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. symmetry. apply foldl_app. Qed.

(* If you are curious why we chose [foldl] over [foldr], it is
because that makes the following lemma true by [reflexivity],
without any rewriting: *)
Example the_reason_for_foldl (Ki : ectx_item) (K : ectx) e :
  fill K (fill [Ki] e) = fill (comp_ectx K [Ki]) e.
Proof. reflexivity. Qed.
(* If we had used [foldr], this would need a rewrite with [foldr_app].
For engineering proofs and tactics on top of this, having "the right"
definitional equalities can be very useful, and that's why we prefer
[foldl] for [fill]. *)

Definition empty_ectx : ectx := [].
Lemma fill_empty e : fill empty_ectx e = e.
Proof. done. Qed.

Lemma base_contextual_step e1 e2 :
  base_step e1 e2 -> contextual_step e1 e2.
Proof. apply EctxStep with empty_ectx; by rewrite ?fill_empty. Qed.

(* This is the "context lifting" lemma (Lemma 1 in the lecture notes).  *)
Lemma fill_contextual_step K e1 e2 :
  contextual_step e1 e2 -> contextual_step (fill K e1) (fill K e2).
Proof. (* DONE IN CLASS *) Admitted.

Lemma fill_contextual_step_rtc K e1 e2 :
  rtc contextual_step e1 e2 -> rtc contextual_step (fill K e1) (fill K e2).
Proof. (* FILL IN HERE *) Admitted.

Lemma base_step_step e1 e2 :
  base_step e1 e2 -> step e1 e2.
Proof. (* FILL IN HERE *) Admitted.

Lemma fill_step K e1 e2 :
  step e1 e2 -> step (fill K e1) (fill K e2).
Proof. (* FILL IN HERE *) Admitted.

Lemma contextual_step_step e1 e2 :
  contextual_step e1 e2 -> step e1 e2.
Proof. (* FILL IN HERE *) Admitted.

(* We have added the constructors of [step] as [eauto] hints,
let's also do that for the other operational semantics. *)
#[export] Hint Constructors big_step : core.
#[export] Hint Constructors base_step : core.
#[export] Hint Constructors contextual_step : core.
