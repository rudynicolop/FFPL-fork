From stdpp Require Import gmap base relations.
From ffpl.lib Require Import prelude.
From ffpl.lib Require Export facts.
From ffpl.type_systems.systemf_state Require Import lang notation.

(** System F with first-order mutable state *)

(** As we have seen with Landin's Knot, System F with mutable state is not a
terminating language. For the purpose of our semantic safety proof, we hence
define a sublanguage that only allows first-order types on the heap: integers,
booleans, units, and products of such types. *)

(** First-order types *)
Inductive fotype : Type :=
  | FOInt
  | FOBool
  | FOUnit
  | FOProd (A B : fotype).

(** System F types. The only difference to the full type system is that
[Ref] is restricted to first-order types. *)

Inductive type : Type :=
  (** [var] is the type of variables of Autosubst -- it unfolds to [nat] *)
  | TVar : var -> type
  | Int
  | Bool
  | Unit
  (** The [{bind 1 of type}] tells Autosubst to put a De Bruijn binder here *)
  | TForall : {bind 1 of type} -> type
  | TExists : {bind 1 of type} -> type
  | Fun (A B : type)
  | Prod (A B : type)
  | Ref (a : fotype)
.

(** Autosubst instances.
  This lets Autosubst do its magic and derive all the substitution functions, etc.
 *)
#[export] Instance Ids_type : Ids type. derive. Defined.
#[export] Instance Rename_type : Rename type. derive. Defined.
#[export] Instance Subst_type : Subst type. derive. Defined.
#[export] Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Fixpoint of_fotype (a : fotype) : type :=
  match a with
  | FOInt => Int
  | FOBool => Bool
  | FOUnit => Unit
  | FOProd a b => Prod (of_fotype a) (of_fotype b)
  end.
Coercion of_fotype : fotype >-> type.

Notation typing_context := (list type).
Definition typevar_context := nat.

Implicit Types
  (Delta : typevar_context)
  (Gamma : typing_context)
  (A B : type)
  (a : fotype)
  (v : val)
  (e : expr).

Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Notation "^ x" := (TVar x) : FType_scope.
Infix "->" := Fun : FType_scope.
Notation "(->)" := Fun (only parsing) : FType_scope.
Notation "forall: tau" :=
  (TForall tau%ty)
  (at level 100, tau at level 200) : FType_scope.
Notation "exists: tau" :=
  (TExists tau%ty)
  (at level 100, tau at level 200) : FType_scope.
Infix "*" := Prod : FType_scope.
Notation "(\*)" := Prod (only parsing) : FType_scope.

(** Shift all the indices in the context by one,
   used when a new type variable is introduced. *)
(* [<$>] is notation for the [fmap] operation that maps the substitution over the whole map. *)
(* [ren] is Autosubst's renaming operation -- it renames all type variables according to the given function,
  in this case [S] to shift the variables up by 1. *)
Definition upctx Gamma := subst (ren S) <$> Gamma.

(** [type_wf Delta A] states that a type [A] has only free variables in [Delta].
 (in other words, all variables occurring free are strictly bounded by [Delta]). *)
Inductive type_wf : typevar_context -> type -> Prop :=
  | type_wf_TVar alpha Delta :
      alpha < Delta ->
      type_wf Delta (TVar alpha)
  | type_wf_Int Delta : type_wf Delta Int
  | type_wf_Bool Delta : type_wf Delta Bool
  | type_wf_Unit Delta : type_wf Delta Unit
  | type_wf_TForall Delta A :
      type_wf (S Delta) A ->
      type_wf Delta (TForall A)
  | type_wf_TExists Delta A :
      type_wf (S Delta) A ->
      type_wf Delta (TExists A)
  | type_wf_Fun Delta A B :
      type_wf Delta A ->
      type_wf Delta B ->
      type_wf Delta (Fun A B)
  | type_wf_Prod Delta A B :
      type_wf Delta A ->
      type_wf Delta B ->
      type_wf Delta (Prod A B)
  | type_wf_ref n a :
      (* First-order types cannot contain type variables so this is always
      well-formed. *)
      type_wf n (Ref a)
.
#[export] Hint Constructors type_wf : core.

Inductive bin_op_typed : bin_op -> type -> type -> type -> Prop :=
  | plus_op_typed : bin_op_typed PlusOp Int Int Int
  | minus_op_typed : bin_op_typed MinusOp Int Int Int
  | mul_op_typed : bin_op_typed MultOp Int Int Int
  | lt_op_typed : bin_op_typed LtOp Int Int Bool
  | le_op_typed : bin_op_typed LeOp Int Int Bool
  | eq_op_typed : bin_op_typed EqOp Int Int Bool.
#[export] Hint Constructors bin_op_typed : core.

(** The fundamental theorem only holds for programs without location literals,
so we define a type system without heap typing. *)
Reserved Notation "'TY' Delta ; Gamma |- e : A" (at level 74, e, A at next level).
Inductive syn_typed : typevar_context -> typing_context -> expr -> type -> Prop :=
  | type_var Delta Gamma x A :
      Gamma !! x = Some A ->
      TY Delta; Gamma |- (Var x) : A
  | type_lam {Delta Gamma e} A B :
      TY Delta ; (A :: Gamma) |- e : B ->
      type_wf Delta A ->
      TY Delta; Gamma |- (Lam e) : (A -> B)
  | type_app {Delta Gamma e1 e2} A B :
      TY Delta; Gamma |- e1 : (A -> B) ->
      TY Delta; Gamma |- e2 : A ->
      TY Delta; Gamma |- (e1 e2)%E : B
  | type_tlam Delta Gamma e A :
      (* we need to shift the context up as we descend under a binder *)
      TY (S Delta); (upctx Gamma) |- e : A ->
      TY Delta; Gamma |- (Lam: e) : (forall: A)
  | type_tapp Delta Gamma A B e :
      TY Delta; Gamma |- e : (forall: A) ->
      type_wf Delta B ->
      (* A.[B/] is the notation for Autosubst's substitution operation that
        replaces variable 0 by [B] *)
      TY Delta; Gamma |- (e <>) : (A.[B/])
  | type_pack Delta Gamma A B e :
      type_wf Delta B ->
      TY Delta; Gamma |- e : (A.[B/]) ->
      TY Delta; Gamma |- (pack e) : (exists: A)
  | type_unpack Delta Gamma A B e e' :
      type_wf Delta B -> (* we should not leak the existential! *)
      TY Delta; Gamma |- e : (exists: A) ->
      (* As we descend under a type variable binder for the typing of [e'],
          we need to shift the indices in [Gamma] and [B] up by one.
        On the other hand, [A] is already defined under this binder, so we need not shift it.
      *)
      TY (S Delta); (A :: (upctx Gamma)) |- e' : (B.[ren (+1)]) ->
      TY Delta; Gamma |- (unpack e in e') : B
  | type_int Delta Gamma z :
      TY Delta; Gamma |- (Lit $ LitInt z) : Int
  | type_bool Delta Gamma b :
      TY Delta; Gamma |- (Lit $ LitBool b) : Bool
  | type_unit Delta Gamma :
      TY Delta; Gamma |- (Lit $ LitUnit) : Unit
  | type_if Delta Gamma e0 e1 e2 A :
      TY Delta; Gamma |- e0 : Bool ->
      TY Delta; Gamma |- e1 : A ->
      TY Delta; Gamma |- e2 : A ->
      TY Delta; Gamma |- If e0 e1 e2 : A
  | type_binop Delta Gamma e1 e2 op A B C :
      bin_op_typed op A B C ->
      TY Delta; Gamma |- e1 : A ->
      TY Delta; Gamma |- e2 : B ->
      TY Delta; Gamma |- BinOp op e1 e2 : C
  | type_pair Delta Gamma e1 e2 A B :
      TY Delta; Gamma |- e1 : A ->
      TY Delta; Gamma |- e2 : B ->
      TY Delta; Gamma |- (e1, e2) : A * B
  | type_fst Delta Gamma e A B :
      TY Delta; Gamma |- e : A * B ->
      TY Delta; Gamma |- Fst e : A
  | type_snd Delta Gamma e A B :
      TY Delta; Gamma |- e : A * B ->
      TY Delta; Gamma |- Snd e : B
  | type_load {Delta Gamma e} a :
      TY Delta; Gamma |- e : (Ref a) ->
      TY Delta; Gamma |- !e : a
  | type_store {Delta Gamma e1 e2} a :
      TY Delta; Gamma |- e1 : (Ref a) ->
      TY Delta; Gamma |- e2 : a ->
      TY Delta; Gamma |- (e1 <- e2) : a
  | type_new {Delta Gamma e} a :
      TY Delta; Gamma |- e : a ->
      TY Delta; Gamma |- (new e) : Ref a
where "'TY' Delta ; Gamma |- e : A" := (syn_typed Delta Gamma e%E A%ty).
#[export] Hint Constructors syn_typed : core.


(** A bit of theory about first-order types *)
Lemma type_wf_fotype a : type_wf 0 a.
Proof. induction a; simpl; eauto. Qed.

Lemma canonical_values_int n Gamma e:
  TY n; Gamma |- e : Int ->
  is_val e ->
  exists n : Z, e = (#n)%E.
Proof. inversion 1; simplify_eq/=; by eauto. Qed.

Lemma canonical_values_bool n Gamma e:
  TY n; Gamma |- e : Bool ->
  is_val e ->
  exists b : bool, e = (#b)%E.
Proof. inversion 1; simplify_eq/=; by eauto. Qed.

Lemma canonical_values_unit n Gamma e:
  TY n; Gamma |- e : Unit ->
  is_val e ->
  e = (#LitUnit)%E.
Proof. inversion 1; simplify_eq/=; by eauto. Qed.

Lemma canonical_values_prod n Gamma e A B :
  TY n; Gamma |- e : A * B ->
  is_val e ->
  exists e1 e2, e = (e1, e2)%E /\ is_val e1 /\ is_val e2.
Proof. inversion 1; simplify_eq/=; by eauto 10. Qed.
