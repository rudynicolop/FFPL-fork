From stdpp Require Import gmap base relations tactics.
From ffpl.lib Require Import prelude.
From ffpl.type_systems.stlc Require Import lang notation types.

(** Complete the missing definitions and fill in all the missing proofs. *)

(** Exercise 1: Structural Operational Semantics implies Contextual Operational Semantics *)

(* Hint: is [is_val_rewrite] lemma is quite useful when you have an assumption
of the form [is_val e]. *)
Lemma step_contextual_step e1 e2 : step e1 e2 -> contextual_step e1 e2.
Proof. (* FILL IN HERE (15 LOC proof) *) Admitted.

(** Exercise 2: Structural Operational Semantics implies Big-Step Semantics *)

(** Hint 1: [eauto] will be really useful for this exercise! Remember that we told it to
apply the constructors of [big_step] automatically. *)
(** Hint 2: Remember that on paper, we provided two helper lemmas before proving the
final theorem. *)


Lemma steps_big_step e (v : val) :
  rtc step e (of_val v) -> big_step e v.
Proof. (* FILL IN HERE (19 LOC helpers and 1 LOC proof) *) Admitted.

(** Exercise 3: Unique typing for source terms. *)

(** First, define source terms and source term typing. *)
Inductive src_expr := (* FILL IN HERE *).

Reserved Notation "Gamma '|-S' e : A" (at level 74, e, A at next level).
Inductive src_typed : typing_context -> src_expr -> type -> Prop := (* FILL IN HERE *).
#[export] Hint Constructors src_typed : core.
Notation "Gamma '|-S' e : A" := (src_typed Gamma e A%ty).

(** Then show that source term typing is unique. *)

Lemma src_typing_unique Gamma E A B :
  (Gamma |-S E : A)%ty -> (Gamma |-S E : B)%ty -> A = B.
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.

(** As a bonus exericse, show that typing of runtime terms is *not* unique. *)
Lemma runtime_typing_not_unique :
  exists Gamma e A B, Gamma |- e : A /\ Gamma |- e : B /\ A != B.
Proof. (* FILL IN HERE (6 LOC proof) *) Admitted.

(** Exercise 4: Type erasure *)

(** Define the erasure function *)
Fixpoint erase (E : src_expr) : expr. (* FILL IN HERE *) Admitted.

(** Prove that it preserves typing. *)
Lemma type_erasure_correctness E A :
  (empty |-S E : A)%ty -> (empty |- erase E : A)%ty.
Proof. (* FILL IN HERE (2 LOC proof) *) Admitted.

(** Exercise 5: Type inference *)

(** To compute whether a term is well-typed, we will have to
test twot ypes for equality. So we define a function that checks that. *)
Fixpoint type_eq A B : bool :=
  match A, B with
  | Int, Int => true
  | Fun A B, Fun A' B' => type_eq A A' && type_eq B B'
  | _, _ => false
  end.

(** Prove the correctness of this function.
Hint: The lemma [andb_true_iff] will be useful. *)
Lemma type_eq_iff A B : type_eq A B = true <-> A = B.
Proof. (* FILL IN HERE (5 LOC proof) *) Admitted.

(** Now define the type inference function. *)
Fixpoint infer_type (Gamma : gmap string type) (E : src_expr) : option type. (* FILL IN HERE *) Admitted.

(** And prove its correctness. *)
Lemma infer_type_typing Gamma E A :
  infer_type Gamma E = Some A -> (Gamma |-S E : A)%ty.
Proof. (* FILL IN HERE (17 LOC proof) *) Admitted.

(** As a nice corollary, we can chain all our results together to show that:
if [infer_type] can compute the type of a term, then the erasure of that
term is safe. *)
Definition safe (e : expr) :=
 forall e', rtc contextual_step e e' -> progressive e'.

Corollary infer_safe E A :
  infer_type empty E = Some A -> safe (erase E).
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.
