From Autosubst Require Export Autosubst.
From ffpl.lib Require Import prelude.

(** [Z] is Coq's version of the integers.
    All the standard operations, like [+], are defined on it.
    For this file and everything that imports this file, we want
    the notation for [+] but also literals like [42] to be interpreted
    as integers, nor natural numbers:
*)
Global Open Scope Z.

(** Make [eauto] able to prove [rtc] goals *)
#[export] Hint Constructors rtc : core.

(** * Simply Typed Lambda Calculus *)

(** ** Expressions / Terms. *)
(** We use De Bruijn indices with the help of the Autosubst library. *)
Inductive expr :=
  (* Base lambda calculus *)
  (** [var] is the type of variables of Autosubst -- it unfolds to [nat] *)
  | Var (x : var)
  (** The [{bind 1 of type}] tells Autosubst to put a De Bruijn binder here *)
  | Lam (e : {bind 1 of expr})
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | LitInt (n: Z)
  | Plus (e1 e2 : expr).

(** Autosubst instances.
  This lets Autosubst do its magic and derive all the substitution functions, etc.
 *)
#[export] Instance Ids_expr : Ids expr. derive. Defined.
#[export] Instance Rename_expr : Rename expr. derive. Defined.
#[export] Instance Subst_expr : Subst expr. derive. Defined.
#[export] Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

(** Values *)

Inductive val :=
  | LitIntV (n: Z)
  | LamV (e : {bind 1 of expr}).

(* Injections into expr *)
Definition of_val (v : val) : expr :=
  match v with
  | LitIntV n => LitInt n
  | LamV e => Lam e
  end.

(* Try to make an expr into a val *)
Definition to_val (e : expr) : option val :=
  match e with
  | LitInt n => Some (LitIntV n)
  | Lam e => Some (LamV e)
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

(** We can recover the [is_val] that we have used in the base language
from these definitions. This is basically making [is_val_spec]
the definition of [is_val] rather than a theorem. *)
Definition is_val e := exists v, e = of_val v.

(* We teach [eauto] some useful facts about [is_val]. *)
Lemma is_val_of_val e v : e = of_val v -> is_val e.
Proof.
  intros ->. by eexists.
Qed.
Lemma is_val_to_val e v : to_val e = Some v -> is_val e.
Proof.
  intros ?%of_to_val. by eexists.
Qed.

#[export] Hint Resolve is_val_of_val is_val_to_val : core.

(** *** Contextual Semantics *)

(** Base reduction *)
Inductive base_step : expr -> expr -> Prop :=
  | BetaS e1 e2 e' :
     is_val e2 ->
     e' = e1.[e2/] ->
     base_step (App (Lam e1) e2) e'
  | PlusS e1 e2 (n1 n2 n3 : Z):
     e1 = (LitInt n1) ->
     e2 = (LitInt n2) ->
     (n1 + n2)%Z = n3 ->
     base_step (Plus e1 e2) (LitInt n3).
#[export] Hint Constructors base_step : core.

(** * Evaluation contexts *)

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

(** * Contextual step relation *)

Inductive contextual_step (e1 : expr) (e2 : expr) : Prop :=
  EctxStep K e1' e2' :
    e1 = fill K e1' ->
    e2 = fill K e2' ->
    base_step e1' e2' ->
    contextual_step e1 e2.
#[export] Hint Constructors contextual_step : core.

(** Basic lemmas about the contextual semantics *)

Lemma base_contextual_step e1 e2 :
  base_step e1 e2 -> contextual_step e1 e2.
Proof. apply EctxStep with empty_ectx; by rewrite ?fill_empty. Qed.

(* This is the "context lifting" lemma (Lemma 1 in the lecture notes).  *)
Lemma fill_contextual_step K e1 e2 :
  contextual_step e1 e2 -> contextual_step (fill K e1) (fill K e2).
Proof.
  destruct 1 as [K' e1' e2' -> ->].
  rewrite !fill_comp. by econstructor.
Qed.

Lemma fill_contextual_step_rtc K e1 e2 :
  rtc contextual_step e1 e2 -> rtc contextual_step (fill K e1) (fill K e2).
Proof.
  induction 1; eauto using fill_contextual_step.
Qed.
