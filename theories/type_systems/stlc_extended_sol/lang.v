From stdpp Require Export strings.
From ffpl.lib Require Import prelude.

(** [Z] is Coq's version of the integers.
    All the standard operations, like [+], are defined on it.
    For this file and everything that imports this file, we want
    the notation for [+] but also literals like [42] to be interpreted
    as integers, nor natural numbers:
*)
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
  | Plus (e1 e2 : expr)
  | Pair (e1 e2 : expr)
  | Proj1 (e : expr)
  | Proj2 (e : expr).

Inductive val :=
  | LitIntV (n: Z)
  | LamV (x : string) (e : expr)
  | PairV (x : val) (y : val).

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
  | Pair e1 e2 => Pair (subst x es e1) (subst x es e2)
  | Proj1 e => Proj1 (subst x es e)
  | Proj2 e => Proj2 (subst x es e)
  end.

(** ** §1.1: Operational Semantics *)

(** *** Small-Step Structural Semantics *)

(** A predicate which holds true whenever an
expression is a value. *)
Fixpoint is_val (e : expr) : Prop :=
  match e with
  | LitInt n => True
  | Lam x e => True
  | Pair x y => is_val x /\ is_val y
  | _ => False
  end.

(** Writing down terms like that is way too painful, so we define some notation.
We would like to use [+] for [Plus], but have to be careful not to mix that up with [nat.plus]!
To this end we define a separate *notation scope* that will contain our expression notations. *)
Declare Scope expr_scope.
(** We declare the scope to be abbreviated with %E (we'll see an example of what
that means below). *)
Delimit Scope expr_scope with E.
(** And we declare that things of type [expr] should automatically be parsed
in this scope. *)
Bind Scope expr_scope with expr.

(** *** Big-Step Semantics *)

(** To formalize big-step semantics, we have to define not just a predicate [is_val]
but an actual *type* of values, [val]. We also define functions to convert between
expressions and values and show their basic properties. *)

(* Injections into expr *)
Fixpoint of_val (v : val) : expr :=
  match v with
  | LitIntV n => LitInt n
  | LamV x e => Lam x e
  | PairV x y => Pair (of_val x) (of_val y)
  end.

(* try to make an expr into a val *)
Fixpoint to_val (e : expr) : option val :=
  match e with
  | LitInt n => Some (LitIntV n)
  | Lam x e => Some (LamV x e)
  | Pair x y =>
      match (to_val x, to_val y) with
      | (Some x, Some y) => Some (PairV x y)
      | _ => None
      end
  | _ => None
  end.

Lemma to_of_val v : to_val (of_val v) = Some v.
(* REMOVE *) Proof.
  induction v; simpl; eauto. rewrite IHv1 IHv2 //.
Qed.

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
(* REMOVE *) Proof.
  induction e in v |- *; simpl; try congruence.
  - injection 1 as <-; simpl; reflexivity.
  - injection 1 as <-; simpl; reflexivity.
  - destruct (to_val e1), (to_val e2); intros Heq; try discriminate.
    injection Heq as <-. simpl. rewrite IHe1 // IHe2 //.
Qed.

Lemma is_val_spec e : is_val e <-> exists v, to_val e = Some v.
(* REMOVE *) Proof.
  induction e; simpl.
  all: split; [intros H|intros [v H]]; try done; eauto.
  - destruct H as [He1 He2].
    rewrite IHe1 in He1.
    rewrite IHe2 in He2.
    destruct He1 as (v1 & ->).
    destruct He2 as (v2 & ->).
    eauto.
  - rewrite IHe1 IHe2. destruct (to_val e1), (to_val e2); eauto.
Qed.

Lemma is_val_rewrite e :
  is_val e -> exists v, e = of_val v.
Proof.
  intros [v Hv]%is_val_spec. exists v.
  apply of_to_val in Hv. done.
Qed.

Lemma is_val_of_val v : is_val (of_val v).
Proof.
  apply is_val_spec. rewrite to_of_val. by eexists.
Qed.

(** *** Contextual Semantics *)
(** Base reduction *)
Inductive base_step : expr -> expr -> Prop :=
  | BetaS x e1 e2 e' :
     is_val e2 ->
     e' = subst x e2 e1 ->
     base_step (App (Lam x e1) e2) e'
  | PlusS e1 e2 (n1 n2 n3 : Z):
     e1 = (LitInt n1) ->
     e2 = (LitInt n2) ->
     (n1 + n2)%Z = n3 ->
     base_step (Plus e1 e2) (LitInt n3)
  | Proj1S e1 e2 :
     is_val e1 ->
     is_val e2 ->
     base_step (Proj1 (Pair e1 e2)) e1
  | Proj2S e1 e2 :
     is_val e1 ->
     is_val e2 ->
     base_step (Proj2 (Pair e1 e2)) e2.
#[export] Hint Constructors base_step : core.

Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | PlusLCtx (v2 : val)
  | PlusRCtx (e1 : expr)
  | PairLCtx (v2 : val)
  | PairRCtx (e1 : expr)
  | Proj1Ctx
  | Proj2Ctx.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | PlusLCtx v2 => Plus e (of_val v2)
  | PlusRCtx e1 => Plus e1 e
  | PairLCtx v2 => Pair e (of_val v2)
  | PairRCtx e1 => Pair e1 e
  | Proj1Ctx => Proj1 e
  | Proj2Ctx => Proj2 e
  end.

Definition ectx := list ectx_item.
Definition fill (K : ectx) (e : expr) : expr := foldl (λ e Ki, fill_item Ki e) e K.

Inductive contextual_step (e1 : expr) (e2 : expr) : Prop :=
  EctxStep K e1' e2' :
    e1 = fill K e1' ->
    e2 = fill K e2' ->
    base_step e1' e2' ->
    contextual_step e1 e2.
#[export] Hint Constructors contextual_step : core.

(* Basic lemmas about the contextual semantics *)

(** Composition of contexts.
This is where using a list starts paying off.
Remember that the innermost items [Ki] go first. *)
Definition comp_ectx (Ko Ki : ectx) := Ki ++ Ko.
(** This is Lemma 2 in the lecture notes. Since we used lists to define [ectx],
we can use use standard list lemmas instead of doing our own induction. *)
Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. symmetry. apply foldl_app. Qed.

Definition empty_ectx : ectx := [].
Lemma fill_empty e : fill empty_ectx e = e.
Proof. done. Qed.

Lemma base_contextual_step e1 e2 :
  base_step e1 e2 -> contextual_step e1 e2.
Proof. apply EctxStep with empty_ectx; by rewrite ?fill_empty. Qed.

(* This is the "context lifting" lemma (Lemma 1 in the lecture notes).  *)
Lemma fill_contextual_step K e1 e2 :
  contextual_step e1 e2 -> contextual_step (fill K e1) (fill K e2).
(* CLASS *) Proof.
  destruct 1 as [K' e1' e2' -> ->].
  rewrite !fill_comp. by econstructor.
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
