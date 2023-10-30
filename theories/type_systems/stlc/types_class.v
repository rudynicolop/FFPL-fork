From stdpp Require Import base relations tactics.
From ffpl.lib Require Import prelude sets maps.
From ffpl.type_systems.stlc Require Import lang closed notation.

(** ** Syntactic typing *)

Inductive type : Set :=
  | Int
  | Fun (A B : type).
Definition typing_context := gmap string type.
Implicit Types
  (Gamma : typing_context)
  (v : val)
  (e : expr)
  (A : type)
  (x : string).
Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Infix "->" := Fun : FType_scope.

Reserved Notation "Gamma |- e : A" (at level 74, e, A at next level).
Inductive syn_typed : typing_context -> expr -> type -> Prop :=
  | typed_var Gamma x A :
      (* lookup the variable in the context *)
      Gamma !! x = Some A ->
      Gamma |- (Var x) : A
  | typed_lam Gamma x e A B :
      (* add a new type assignment to the context *)
     (<[ x := A ]> Gamma) |- e : B ->
      Gamma |- (Lam x e) : (A -> B)
  | typed_int Gamma z :
      Gamma |- (LitInt z) : Int
  | typed_app Gamma e1 e2 A B :
      Gamma |- e1 : (A -> B) ->
      Gamma |- e2 : A ->
      Gamma |- e1 e2 : B
  | typed_add Gamma e1 e2 :
      Gamma |- e1 : Int ->
      Gamma |- e2 : Int ->
      Gamma |- e1 + e2 : Int
where "Gamma |- e : A" := (syn_typed Gamma e%E A%ty) : FType_scope.
#[export] Hint Constructors syn_typed : core.
Local Open Scope FType_scope.
Notation "Gamma |- e : A" := (syn_typed Gamma e%E A%ty).
Goal empty |- (lam: "x", 1 + "x")%E : (Int -> Int).
Proof. eauto. Qed.
Lemma var_inversion Gamma (x : string) A :
  Gamma |- x : A -> Gamma !! x = Some A.
Proof. inversion 1; subst; auto. Qed.

Lemma lam_inversion Gamma (x : string) e C :
  (Gamma |- (lam: x, e) : C) ->
  exists A B, C = (A -> B)%ty /\ <[x:=A]> Gamma |- e : B.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma lit_int_inversion Gamma (n : Z) A : (Gamma |- n : A) -> A = Int.
Proof. inversion 1; subst; auto. Qed.

Lemma app_inversion Gamma e1 e2 B :
  (Gamma |- e1 e2 : B) ->
  exists A,  Gamma |- e1 : (A -> B) /\ Gamma |- e2 : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma plus_inversion Gamma e1 e2 B :
  (Gamma |- e1 + e2 : B) ->
  B = Int /\ Gamma |- e1 : Int /\ Gamma |- e2 : Int.
Proof. inversion 1; subst; eauto. Qed.

(** * Progress *)
Lemma canonical_values_arr Gamma e A B :
  Gamma |- e : (A -> B) ->
  is_val e ->
  exists x e', e = (lam: x, e')%E.
Proof. (* DONE IN CLASS *) Admitted.

Lemma canonical_values_int Gamma e :
  Gamma |- e : Int ->
  is_val e ->
  exists n: Z, e = n.
Proof. (* DONE IN CLASS *) Admitted.
Definition progressive (e : expr) :=
  is_val e \/ exists e', contextual_step e e'.
Theorem type_progress e A :
  empty |- e : A -> progressive e.
Proof. (* DONE IN CLASS *) Admitted.

(** * Preservation *)

Lemma type_weakening Gamma Delta e A :
  Gamma |- e : A ->
  Gamma `subseteq` Delta ->
  Delta |- e : A.
Proof. (* DONE IN CLASS *) Admitted.
Lemma type_substitution e e' Gamma x A B :
  empty |- e' : A ->
  <[x := A]> Gamma |- e : B ->
  Gamma |- subst x e' e : B.
Proof. (* DONE IN CLASS *) Admitted.
Lemma type_preservation_base_step e e' A :
  empty |- e : A ->
  base_step e e' ->
  empty |- e' : A.
Proof. (* DONE IN CLASS *) Admitted.
Definition ectx_item_typing (Ki : ectx_item) (A B : type) :=
  forall e, empty |- e : A -> empty |- (fill_item Ki e) : B.

Lemma fill_item_typing_decompose Ki e A :
  empty |- fill_item Ki e : A ->
  exists B, empty |- e : B /\ ectx_item_typing Ki B A.
Proof. (* DONE IN CLASS *) Admitted.

Definition ectx_typing (K : ectx) (A B : type) :=
  forall e, empty |- e : A -> empty |- (fill K e) : B.
Lemma fill_typing_decompose K e A :
  empty |- fill K e : A ->
  exists B, empty |- e : B /\ ectx_typing K B A.
Proof. (* DONE IN CLASS *) Admitted.
Lemma fill_typing_compose K e A B :
  empty |- e : B ->
  ectx_typing K B A ->
  empty |- fill K e : A.
Proof. (* DONE IN CLASS *) Admitted.
Theorem type_preservation e e' A :
  empty |- e : A ->
  contextual_step e e' ->
  empty |- e' : A.
Proof. (* DONE IN CLASS *) Admitted.
Corollary type_safety e1 e2 A:
  empty |- e1 : A ->
  rtc contextual_step e1 e2 ->
  progressive e2.
Proof. (* FILL IN HERE *) Admitted.
