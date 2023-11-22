From stdpp Require Import base relations.
From ffpl.lib Require Import prelude.
From ffpl.lib Require Import maps.
From ffpl.type_systems.systemf Require Import lang notation.
From Autosubst Require Export Autosubst.

(** ** Syntactic typing *)
(** We use De Bruijn indices with the help of the Autosubst library. *)
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
  | Sum (A B : type).

(** Autosubst instances.
  This lets Autosubst do its magic and derive all the substitution functions, etc.
 *)
#[export] Instance Ids_type : Ids type. derive. Defined.
#[export] Instance Rename_type : Rename type. derive. Defined.
#[export] Instance Subst_type : Subst type. derive. Defined.
#[export] Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Notation typing_context := (list type).
Implicit Types
  (Delta : nat)
  (Gamma : typing_context)
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
Infix "+" := Sum : FType_scope.
Notation "(+)" := Sum (only parsing) : FType_scope.

(** Shift all the indices in the context by one,
   used when a new type variable is introduced. *)
(* [<$>] is notation for the [fmap] operation that maps the substitution over the whole map. *)
(* [ren] is Autosubst's renaming operation -- it renames all type variables according to the given function,
  in this case [S] to shift the variables up by 1. *)
Definition upctx Gamma := subst (ren S) <$> Gamma.

(** [type_wf Delta A] states that a type [A] has only free variables in [Delta].
 (in other words, all variables occurring free are strictly bounded by [Delta]). *)
Inductive type_wf : nat -> type -> Prop :=
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
  | type_wf_Sum Delta A B :
      type_wf Delta A ->
      type_wf Delta B ->
      type_wf Delta (Sum A B)
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

Inductive un_op_typed : un_op -> type -> type -> Prop :=
  | neg_op_typed : un_op_typed NegOp Bool Bool
  | minus_un_op_typed : un_op_typed MinusUnOp Int Int.

Reserved Notation "'TY' Delta ; Gamma |- e : A" (at level 74, e, A at next level).
Inductive syn_typed : nat -> typing_context -> expr -> type -> Prop :=
  | type_var Delta Gamma x A :
      Gamma !! x = Some A ->
      TY Delta; Gamma |- (Var x) : A
  | type_lam Delta Gamma e A B :
      TY Delta ; (A :: Gamma) |- e : B ->
      type_wf Delta A ->
      TY Delta; Gamma |- (Lam e) : (A -> B)
  | type_app Delta Gamma e1 e2 A B :
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
      type_wf (S Delta) A ->
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
  | type_int Delta Gamma z : TY Delta; Gamma |- (Lit $ LitInt z) : Int
  | type_bool Delta Gamma b : TY Delta; Gamma |- (Lit $ LitBool b) : Bool
  | type_unit Delta Gamma : TY Delta; Gamma |- (Lit $ LitUnit) : Unit
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
  | type_unop Delta Gamma e op A B :
      un_op_typed op A B ->
      TY Delta; Gamma |- e : A ->
      TY Delta; Gamma |- UnOp op e : B
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
  | type_injl Delta Gamma e A B :
      type_wf Delta B ->
      TY Delta; Gamma |- e : A ->
      TY Delta; Gamma |- InjL e : A + B
  | type_injr Delta Gamma e A B :
      type_wf Delta A ->
      TY Delta; Gamma |- e : B ->
      TY Delta; Gamma |- InjR e : A + B
  | type_case Delta Gamma e e1 e2 A B C :
      TY Delta; Gamma |- e : B + C ->
      TY Delta; Gamma |- e1 : (B -> A) ->
      TY Delta; Gamma |- e2 : (C -> A) ->
      TY Delta; Gamma |- Case e e1 e2 : A
where "'TY' Delta ; Gamma |- e : A" := (syn_typed Delta Gamma e%E A%ty).
#[export] Hint Constructors syn_typed : core.

(* derived typing rule for match *)
Lemma type_match Delta Gamma e e1 e2 A B C :
  type_wf Delta B ->
  type_wf Delta C ->
  TY Delta; Gamma |- e : B + C ->
  TY Delta; B:: Gamma |- e1 : A ->
  TY Delta; C:: Gamma |- e2 : A ->
  TY Delta; Gamma |- match: e with InjL => e1 | InjR => e2 end : A.
Proof. eauto. Qed.

(** ** Examples *)

Goal TY 0; [] |- (lam: #1 + ^0)%E : (Int -> Int).
Proof. eauto. Qed.
(** [forall: #0 -> #0] corresponds to [forall alpha. alpha -> alpha] with named binders. *)
Goal TY 0; [] |- (Lam: lam: ^0)%E : (forall: ^0 -> ^0).
Proof. repeat econstructor. Qed.
Goal TY 0; [] |- (pack ((lam: ^0), #42)) : exists: (^0 -> ^0) * ^0.
Proof.
  apply (type_pack _ _ _ Int).
  - eauto.
  - repeat econstructor.
  - asimpl. eauto.
Qed.
Goal TY 0; [] |- (unpack (pack ((lam: ^0), #42)) in (lam: #1337) ((Fst ^0) (Snd ^0))) : Int.
Proof.
  (* if we want to typecheck stuff with existentials, we need a bit more explicit proofs.
    Letting eauto try to instantiate the evars becomes too expensive. *)
  apply (type_unpack _ _ ((^0 -> ^0) * ^0)%ty).
  - done.
  - apply (type_pack _ _ _ Int); asimpl; eauto.
    repeat econstructor.
  - eapply (type_app _ _ _ _ (^0)%ty); eauto 10.
Qed.

(** fails: we are not allowed to leak the existential *)
Goal TY 0; [] |- (unpack (pack ((lam: ^0), #42)) in (Fst ^0) (Snd ^0)) : ^0.
Proof.
  apply (type_unpack _ _ ((^0 -> ^0) * ^0)%ty).
Abort.

(** ** Typing inversion lemmas *)

Lemma var_inversion Gamma Delta (x : var) A :
  TY Delta; Gamma |- ^x : A -> Gamma !! x = Some A.
Proof. inversion 1; subst; auto. Qed.

Lemma lam_inversion Delta Gamma e C :
  TY Delta; Gamma |- (lam: e) : C ->
  exists A B, C = (A -> B)%ty /\ type_wf Delta A /\ TY Delta; A :: Gamma |- e : B.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma app_inversion Delta Gamma e1 e2 B :
  TY Delta; Gamma |- e1 e2 : B ->
  exists A, TY Delta; Gamma |- e1 : (A -> B) /\ TY Delta; Gamma |- e2 : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma if_inversion Delta Gamma e0 e1 e2 B :
  TY Delta; Gamma |- If e0 e1 e2 : B ->
  TY Delta; Gamma |- e0 : Bool /\ TY Delta; Gamma |- e1 : B /\ TY Delta; Gamma |- e2 : B.
Proof. inversion 1; subst; eauto. Qed.

Lemma binop_inversion Delta Gamma op e1 e2 B :
  TY Delta; Gamma |- BinOp op e1 e2 : B ->
  exists A1 A2, bin_op_typed op A1 A2 B /\ TY Delta; Gamma |- e1 : A1 /\ TY Delta; Gamma |- e2 : A2.
Proof. inversion 1; subst; eauto. Qed.

Lemma unop_inversion Delta Gamma op e B :
  TY Delta; Gamma |- UnOp op e : B ->
  exists A, un_op_typed op A B /\ TY Delta; Gamma |- e : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma type_app_inversion Delta Gamma e B :
  TY Delta; Gamma |- e <> : B ->
  exists A C, B = A.[C/] /\ type_wf Delta C /\ TY Delta; Gamma |- e : (forall: A).
Proof. inversion 1; subst; eauto. Qed.

Lemma type_lam_inversion Delta Gamma e B :
  TY Delta; Gamma |- (Lam: e) : B ->
  exists A, B = (forall: A)%ty /\ TY (S Delta); upctx Gamma |- e : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma type_pack_inversion Delta Gamma e B :
  TY Delta; Gamma |- (pack e) : B ->
  exists A C, B = (exists: A)%ty /\ TY Delta; Gamma |- e : (A.[C/])%ty /\ type_wf Delta C /\ type_wf (S Delta) A.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma type_unpack_inversion Delta Gamma e e' B :
  TY Delta; Gamma |- (unpack e in e') : B ->
  exists A, type_wf Delta B /\ TY Delta; Gamma |- e : (exists: A) /\ TY S Delta; A :: (upctx Gamma) |- e' : (B.[ren (+1)]).
Proof. inversion 1; subst; eauto 10. Qed.

Lemma pair_inversion Delta Gamma e1 e2 C :
  TY Delta; Gamma |- (e1, e2) : C ->
  exists A B, C = (A * B)%ty /\ TY Delta; Gamma |- e1 : A /\ TY Delta; Gamma |- e2 : B.
Proof. inversion 1; subst; eauto. Qed.

Lemma fst_inversion Delta Gamma e A :
  TY Delta; Gamma |- Fst e : A ->
  exists B, TY Delta; Gamma |- e : A * B.
Proof. inversion 1; subst; eauto. Qed.

Lemma snd_inversion Delta Gamma e B :
  TY Delta; Gamma |- Snd e : B ->
  exists A, TY Delta; Gamma |- e : A * B.
Proof. inversion 1; subst; eauto. Qed.

Lemma injl_inversion Delta Gamma e C :
  TY Delta; Gamma |- InjL e : C ->
  exists A B, C = (A + B)%ty /\ TY Delta; Gamma |- e : A /\ type_wf Delta B.
Proof. inversion 1; subst; eauto. Qed.

Lemma injr_inversion Delta Gamma e C :
  TY Delta; Gamma |- InjR e : C ->
  exists A B, C = (A + B)%ty /\ TY Delta; Gamma |- e : B /\ type_wf Delta A.
Proof. inversion 1; subst; eauto. Qed.

Lemma case_inversion Delta Gamma e e1 e2 A :
  TY Delta; Gamma |- Case e e1 e2 : A ->
  exists B C, TY Delta; Gamma |- e : B + C /\ TY Delta; Gamma |- e1 : (B -> A) /\ TY Delta; Gamma |- e2 : (C -> A).
Proof. inversion 1; subst; eauto. Qed.

(** ** Progress *)

(** Canonical forms lemmas *)
Lemma canonical_values_arr Delta Gamma e A B :
  TY Delta; Gamma |- e : (A -> B) ->
  is_val e ->
  exists e', e = (lam: e')%E.
Proof.
  inversion 1; simplify_eq; by eauto.
Qed.

Lemma canonical_values_forall Delta Gamma e A :
  TY Delta; Gamma |- e : (forall: A)%ty ->
  is_val e ->
  exists e', e = (Lam: e')%E.
Proof.
  inversion 1; simplify_eq; by eauto.
Qed.

Lemma canonical_values_exists Delta Gamma e A :
  TY Delta; Gamma |- e : (exists: A) ->
  is_val e ->
  exists e', e = (pack e')%E.
Proof.
  inversion 1; simplify_eq; by eauto.
Qed.

Lemma canonical_values_int Delta Gamma e :
  TY Delta; Gamma |- e : Int ->
  is_val e ->
  exists n: Z, e = (#n)%E.
Proof.
  inversion 1; simplify_eq; by eauto.
Qed.

Lemma canonical_values_bool Delta Gamma e :
  TY Delta; Gamma |- e : Bool ->
  is_val e ->
  exists b: bool, e = (#b)%E.
Proof.
  inversion 1; simplify_eq; by eauto.
Qed.

Lemma canonical_values_unit Delta Gamma e :
  TY Delta; Gamma |- e : Unit ->
  is_val e ->
  e = (#LitUnit)%E.
Proof.
  inversion 1; simplify_eq; by eauto.
Qed.

Lemma canonical_values_prod Delta Gamma e A B :
  TY Delta; Gamma |- e : A * B ->
  is_val e ->
  exists e1 e2, e = (e1, e2)%E /\ is_val e1 /\ is_val e2.
Proof.
  inversion 1; simplify_eq; by eauto 10.
Qed.

Lemma canonical_values_sum Delta Gamma e A B :
  TY Delta; Gamma |- e : A + B ->
  is_val e ->
  (exists e', e = InjL e' /\ is_val e') \/ (exists e', e = InjR e' /\ is_val e').
Proof.
  inversion 1; simplify_eq; by eauto.
Qed.

Definition progressive (e : expr) :=
  is_val e \/ exists e', contextual_step e e'.

Lemma type_progress e A:
  TY 0; [] |- e : A -> progressive e.
Proof.
  remember [] as Gamma. remember 0 as n.
  induction 1 as [| | Delta Gamma e1 e2 A B Hty IH1 _ IH2 | | Delta Gamma A B e Hty IH | Delta Gamma A B e Hwf Hwf' Hty IH
    | Delta Gamma A B e e' Hwf Hty1 IH1 Hty2 IH2 | | | | Delta Gamma e0 e1 e2 A Hty1 IH1 Hty2 IH2 Hty3 IH3
    | Delta Gamma e1 e2 op A B C Hop Hty1 IH1 Hty2 IH2 | Delta Gamma e op A B Hop Hty IH | Delta Gamma e1 e2 A B Hty1 IH1 Hty2 IH2
    | Delta Gamma e A B Hty IH | Delta Gamma e A B Hty IH | Delta Gamma e A B Hwf Hty IH | Delta Gamma e A B Hwf Hty IH
    | Delta Gamma e e1 e2 A B C Htye IHe Htye1 IHe1 Htye2 IHe2 ].
  - (* variable *) subst. by exfalso.
  - (* lambda *) left. done.
  - (* app *)
    destruct (IH2 HeqGamma Heqn) as [H2|H2]; [destruct (IH1 HeqGamma Heqn) as [H1|H1]|].
    + eapply canonical_values_arr in Hty as (e & ->); last done.
      right. eexists.
      eapply base_contextual_step, BetaS; eauto.
    + right. destruct H1 as [e1' Hstep]. eauto.
    + right. destruct H2 as [e2' H2]. eauto.
  - (* big lambda *) (* FILL IN HERE (1 LOC proof) *) admit.
  - (* type app *)
    (* You will need the following lemmas: canonical_values_forall,
    base_contextual_step, contextual_step_tapp. *)
    (* FILL IN HERE (4 LOC proof) *) admit.
  - (* pack *)
    (* You will need the lemma contextual_step_pack. *)
    (* FILL IN HERE (3 LOC proof) *) admit.
  - (* unpack *)
    (* You will need the following lemmas: canonical_values_exists,
    base_contextual_step, contextual_step_unpack. *)
    (* FILL IN HERE (5 LOC proof) *) admit.
  - (* int *) left. done.
  - (* bool *) left. done.
  - (* unit *) left. done.
  - (* if *)
    destruct (IH1 HeqGamma Heqn) as [H1 | H1].
    + eapply canonical_values_bool in Hty1 as (b & ->); last done.
      right. destruct b; eexists; eapply base_contextual_step; constructor.
    + right. destruct H1 as [e0' Hstep].
      eexists. eauto.
  - (* binop *)
    assert (A = Int /\ B = Int) as [-> ->].
    { inversion Hop; subst A B C; done. }
    destruct (IH2 HeqGamma Heqn) as [H2|H2]; [destruct (IH1 HeqGamma Heqn) as [H1|H1]|].
    + right. eapply canonical_values_int in Hty1 as [n1 ->]; last done.
      eapply canonical_values_int in Hty2 as [n2 ->]; last done.
      inversion Hop; subst; simpl.
      all: eexists; eapply base_contextual_step; eapply BinOpS; eauto.
    + right. destruct H1 as [e1' Hstep]. eauto.
    + right. destruct H2 as [e2' H2]. eauto.
  - (* unop *)
    inversion Hop; subst A B op.
    + right. destruct (IH HeqGamma Heqn) as [H2 | H2].
      * eapply canonical_values_bool in Hty as [b ->]; last done.
        eexists; eapply base_contextual_step; eapply UnOpS; eauto.
      * destruct H2 as [e' H2]. eauto.
    + right. destruct (IH HeqGamma Heqn) as [H2 | H2].
      * eapply canonical_values_int in Hty as [z ->]; last done.
        eexists; eapply base_contextual_step; eapply UnOpS; eauto.
      * destruct H2 as [e' H2]. eauto.
  - (* pair *)
    destruct (IH2 HeqGamma Heqn) as [H2|H2]; [destruct (IH1 HeqGamma Heqn) as [H1|H1]|].
    + left. done.
    + right. destruct H1 as [e1' Hstep]. eauto.
    + right. destruct H2 as [e2' H2]. eauto.
  - (* fst *)
    destruct (IH HeqGamma Heqn) as [H | H].
    + eapply canonical_values_prod in Hty as (e1 & e2 & -> & ? & ?); last done.
      right. eexists. eapply base_contextual_step. econstructor; done.
    + right. destruct H as [e' H]. eauto.
  - (* snd *)
    destruct (IH HeqGamma Heqn) as [H | H].
    + eapply canonical_values_prod in Hty as (e1 & e2 & -> & ? & ?); last done.
      right. eexists. eapply base_contextual_step. econstructor; done.
    + right. destruct H as [e' H]. eauto.
  - (* injl *)
    destruct (IH HeqGamma Heqn) as [H | H].
    + left. done.
    + right. destruct H as [e' H]. eauto.
  - (* injr *)
    destruct (IH HeqGamma Heqn) as [H | H].
    + left. done.
    + right. destruct H as [e' H]. eauto.
  - (* case *)
    right. destruct (IHe HeqGamma Heqn) as [H1|H1].
    + eapply canonical_values_sum in Htye as [(e' & -> & ?) | (e' & -> & ?)]; last done.
      * eexists. eapply base_contextual_step. eauto.
      * eexists. eapply base_contextual_step. eauto.
    + destruct H1 as [e' H1]. eauto.
Admitted.

(** ** Renamings and substitutions on types *)

(** Well-formed type renamings from [Delta1] to [Delta2].
(Or, equivalently: [Delta1] is included in [Delta2] via renaming [delta]. *)
Definition wf_tren Delta1 Delta2 (delta : var -> var) :=
  forall alpha, alpha < Delta1 -> delta alpha < Delta2.

(** Renaming well-formedness is preserved when we increase both typing contexts
by one and shift the renaming up. *)
Lemma wf_tren_up delta Delta1 Delta2 :
  wf_tren Delta1 Delta2 delta -> wf_tren (S Delta1) (S Delta2) (upren delta).
Proof.
  intros Hdelta [|k]; simpl; first by lia.
  specialize (Hdelta k). lia.
Qed.

(** Type context [n] is included in [S n] with the successor renaming. **)
Lemma wf_tren_S Delta :
  wf_tren Delta (S Delta) S.
Proof.
  intros k. lia.
Qed.

(** Type well-formedness is preserved under renaming. *)
Lemma type_wf_rename Delta1 Delta2 A delta :
  wf_tren Delta1 Delta2 delta ->
  type_wf Delta1 A ->
  type_wf Delta2 (A.[ren delta]).
Proof.
  intros Hdelta. induction 1 in Delta2, Hdelta, delta |-*; asimpl; eauto.
  - econstructor. eapply IHtype_wf, wf_tren_up. done.
  - econstructor. eapply IHtype_wf, wf_tren_up. done.
Qed.

(** Well-formed type substitutions: [sigma] maps the types from context [Delta1]
into types that are avlid in [Delta2]. *)
Definition wf_tsubst Delta1 Delta2 sigma :=
  forall alpha, alpha < Delta1 -> type_wf Delta2 (sigma alpha).

(** On renamings, [wf_tren] and [wf_tsubst] are equivalent.
(We don't actually need this lemma for the type safety proof, but it demonstrates
that [wf_tsubst] is a generalization of [wf_tren].) *)
Lemma wf_tsubst_tren Delta1 Delta2 (delta : var -> var) :
  wf_tren Delta1 Delta2 delta <-> wf_tsubst Delta1 Delta2 (ren delta).
Proof.
  split.
  - intros Hdelta k. specialize (Hdelta k). simpl. eauto with lia.
  - intros Hdelta k Hk. specialize (Hdelta k Hk). by inversion Hdelta.
Qed.

Lemma wf_tsubst_up sigma Delta1 Delta2 :
  wf_tsubst Delta1 Delta2 sigma -> wf_tsubst (S Delta1) (S Delta2) (up sigma).
Proof.
  intros Hdelta [|k]; asimpl.
  - eauto with lia.
  - specialize (Hdelta k). intros.
    eapply type_wf_rename; last by eauto with lia.
    eapply wf_tren_S.
Qed.

Lemma wf_tsubst_single Delta A :
  type_wf Delta A ->
  wf_tsubst (S Delta) Delta (A .: ids).
Proof.
  intros Hwf [|k] Hk; simpl.
  - done.
  - econstructor. lia.
Qed.

(** Applying a well-formed substitution preserves well-formedness. *)
Lemma type_wf_substitution Delta1 Delta2 A sigma :
  wf_tsubst Delta1 Delta2 sigma ->
  type_wf Delta1 A ->
  type_wf Delta2 A.[sigma].
Proof.
  intros Hsigma. induction 1 in Delta2, Hsigma, sigma |-*; simpl; eauto.
  + econstructor; eapply IHtype_wf. eapply wf_tsubst_up. done.
  + econstructor; eapply IHtype_wf. eapply wf_tsubst_up. done.
Qed.

(** Shifting of contexts and applying a substitution in a context commutes. *)
Lemma up_subst sigma Gamma :
  upctx (subst sigma <$> Gamma) = subst (up sigma) <$> upctx Gamma.
Proof.
  rewrite /upctx. apply list_eq. intros x. rewrite !list_lookup_fmap.
  destruct (Gamma !! x) as [B|]; last done. by asimpl.
Qed.

(** Applying such a well-formed type substitution to a typing judgment (both the
context and the result type) preserves typing. *)
Lemma type_tsubstitution Delta1 Delta2 Gamma e A sigma :
  wf_tsubst Delta1 Delta2 sigma ->
  TY Delta1; Gamma |- e : A ->
  TY Delta2; (subst sigma) <$> Gamma |- e : A.[sigma].
Proof.
  intros Hsigma.
  induction 1 as [ Delta Gamma x A Heq| | | Delta Gamma e A Hty IH | |n Gamma A B e Hwf Hwf' Hty IH
    | Delta Gamma A B e e' Hwf Hty1 IH1 Hty2 IH2 | | | | |? ? ? ? ? ? ? ? Hop | ? ? ? ? ? ? Hop | | | | | | ]
    in Hsigma, sigma, Delta2 |-*; simpl.
  - (* var *) econstructor. rewrite list_lookup_fmap Heq //=.
  - (* lam *) econstructor; last by eapply type_wf_substitution.
    rewrite -fmap_cons. eauto.
  - (* app *) eauto.
  - (* tlam *) econstructor. rewrite up_subst.
    eapply IH. eapply wf_tsubst_up. done.
  - (* tapp *) replace (A.[B/].[sigma]) with (A.[up sigma].[B.[sigma]/]) by by asimpl.
    eauto using type_wf_substitution.
  - (* pack *)
    eapply (type_pack _ _ _ (subst sigma B)).
    + eapply type_wf_substitution; done.
    + eapply type_wf_substitution; last done.
      eapply wf_tsubst_up. done.
    + replace (A.[up sigma].[B.[sigma]/]) with (A.[B/].[sigma]) by by asimpl.
      eauto using type_wf_substitution.
  - (* unpack *)
    eapply (type_unpack _ _ A.[up sigma]).
    + eapply type_wf_substitution; done.
    + replace (exists: A.[up sigma])%ty with ((exists: A).[sigma])%ty by by asimpl.
      eapply IH1. done.
    + rewrite up_subst. rewrite -fmap_cons.
      replace (B.[sigma].[ren (+1)]) with (B.[ren(+1)].[up sigma]) by by asimpl.
      eapply IH2. eapply wf_tsubst_up. done.
  - (* int *) eauto.
  - (* bool *) eauto.
  - (* unit *) eauto.
  - (* if *) eauto.
  - (* binop *) inversion Hop; subst; eauto.
  - (* unop *) inversion Hop; subst; eauto.
  - (* pair *) eauto.
  - (* fst *) eauto.
  - (* snd *) eauto.
  - (* inl *) eauto 10 using type_wf_substitution.
  - (* inr *) eauto 10 using type_wf_substitution.
  - (* case *) eauto.
Qed.

(** We can derive the on-paper version by specializing to single substitution.

We also make the lemma easier to apply by introducing [Gamma'] which must
be equal to [Gamma] with the substitution applied everywhere.
This means we can [eapply] the lemma and then prove the equality, rather than
having to get things into the right shape for [eapply] to even work.
The same goes for [A'] *)
Lemma type_tsubstitution_single Delta Gamma Gamma' e A A' B :
  type_wf Delta B ->
  TY (S Delta); Gamma |- e : A ->
  Gamma' = (fun A' => A'.[B/]) <$> Gamma ->
  A' = A.[B/] ->
  TY Delta; Gamma' |- e : A'.
Proof.
  intros HB He -> ->. eapply type_tsubstitution; last done.
  eapply wf_tsubst_single. done.
Qed.

(** ** Renamings and substitutions on terms *)

(** Type-preserving renamings ("context inclusion") *)
Definition typed_ren (Gamma1 Gamma2 : typing_context) (delta : var -> var) :=
  forall x B, Gamma1 !! x = Some B -> Gamma2 !! (delta x) = Some B.

(** As before, [typed_ren] is preserved if we add the same type at index 0 in
both contexts. *)
Lemma typed_ren_up delta Gamma1 Gamma2 A :
  typed_ren Gamma1 Gamma2 delta -> typed_ren (A :: Gamma1) (A :: Gamma2) (upren delta).
Proof.
  intros Hsigma [|x] C; simpl; first done. eauto.
Qed.

(** [Gamma] is included in [A :: Gamma] with the successor renaming. *)
Lemma typed_ren_S A Gamma :
  typed_ren Gamma (A :: Gamma) S.
Proof.
  intros x C. eauto.
Qed.

(** We also get a new preservation lemma for renaming the contexts themselves using [upctx]. *)
Lemma typed_ren_upctx delta Gamma1 Gamma2 :
  typed_ren Gamma1 Gamma2 delta -> typed_ren (upctx Gamma1) (upctx Gamma2) delta.
Proof.
  intros Hsigma x C. rewrite !list_lookup_fmap.
  intros (C' & ? & ->)%fmap_Some. eapply fmap_Some. eauto.
Qed.

(** Then we get to weakening, or the "renaming" lemma. *)
Lemma type_renaming delta Delta Gamma1 Gamma2 e A :
  typed_ren Gamma1 Gamma2 delta ->
  TY Delta; Gamma1 |- e : A ->
  TY Delta; Gamma2 |- e.[ren delta] : A.
Proof.
  intros Hsigma. induction 1 in Gamma2, delta, Hsigma.
  (* That's a lot of cases. Fortunately, most of them are trivial since they
  don't do anything with binders. *)
  all: asimpl; eauto.
  (* The remaining 3 cases have to be done by hand. *)
  - (* lam *) constructor; last done.
    eapply IHsyn_typed, typed_ren_up. done.
  - (* tlam *) econstructor. eapply IHsyn_typed.
    eapply typed_ren_upctx. done.
  - (* unpack *) econstructor.
    + done.
    + eapply IHsyn_typed1. done.
    + eapply IHsyn_typed2. eapply typed_ren_up, typed_ren_upctx. done.
Qed.

(** Type-preserving substitution *)
Definition typed_subst Delta Gamma1 Gamma2 (sigma : var -> expr) :=
  forall x B, Gamma1 !! x = Some B -> TY Delta; Gamma2 |- sigma x : B.

(** On renamings, [typed_ren] and [typed_subst] are equivalent.
(We don't actually need this lemma for the type safety proof, but it demonstrates
that [typed_subst] is a generalization of [typed_ren].) *)
Lemma typed_subst_ren Delta (Gamma1 Gamma2 : typing_context) (delta : var -> var) :
  typed_ren Gamma1 Gamma2 delta <-> typed_subst Delta Gamma1 Gamma2 (ren delta).
Proof.
  split.
  - intros Hdelta x B Hx. specialize (Hdelta _ _ Hx). by constructor.
  - intros Hdelta x B Hx. specialize (Hdelta _ _ Hx). by inversion Hdelta.
Qed.

(** As always, we can extend the context with a new type if we also shift the
substitution. *)
Lemma typed_subst_up Delta sigma Gamma1 Gamma2 A :
  typed_subst Delta Gamma1 Gamma2 sigma -> typed_subst Delta (A :: Gamma1) (A :: Gamma2) (up sigma).
Proof.
  intros Hsigma [|x] C; simpl; intros.
  - simplify_eq. constructor. done.
  - asimpl. eapply type_renaming; last by eauto. eapply typed_ren_S.
Qed.

(** We can remove a single type from the context if the substitution puts in a
well-typed term. *)
Lemma typed_subst_single Delta Gamma A e :
  TY Delta; Gamma |- e : A ->
  typed_subst Delta (A :: Gamma) Gamma (e .: ids).
Proof.
  intros He [|x] C; simpl; intros Hx.
  - simplify_eq. done.
  - eauto.
Qed.

(** And [typed_subst] is preserved when we shift up the typing context by 1. *)
Lemma typed_subst_upctx Delta sigma Gamma1 Gamma2 :
  typed_subst Delta Gamma1 Gamma2 sigma -> typed_subst (S Delta) (upctx Gamma1) (upctx Gamma2) sigma.
Proof.
  intros Hsigma x C. rewrite !list_lookup_fmap.
  intros (C' & ? & ->)%fmap_Some. eapply type_tsubstitution; last by eauto.
  eapply wf_tsubst_tren, wf_tren_S.
Qed.

(** Finally, the main substitution lemma *)
Lemma type_substitution sigma Delta e Gamma1 Gamma2 A :
  typed_subst Delta Gamma1 Gamma2 sigma ->
  TY Delta; Gamma1 |- e : A ->
  TY Delta; Gamma2 |- e.[sigma] : A.
Proof.
  intros Hsigma. induction e in Delta, Gamma1, Gamma2, A, sigma, Hsigma |- *.
  - (* literals *) asimpl. inversion 1; subst; auto.
  - intros Hp % var_inversion.
    specialize (Hsigma _ _ Hp). asimpl. done.
  - intros (C & D & -> & Hwf & Hty)%lam_inversion. asimpl.
    econstructor; last done. eapply IHe; last done. by eapply typed_subst_up.
  - intros (C & Hty1 & Hty2) % app_inversion. asimpl. eauto.
  - intros (? & Hop & H1) % unop_inversion. asimpl.
    destruct op; inversion Hop; subst; eauto.
  - intros (? & ? & Hop & H1 & H2) % binop_inversion. asimpl.
    destruct op; inversion Hop; subst; eauto.
  - intros (H1 & H2 & H3)%if_inversion. asimpl. eauto.
  - intros (C & D & -> & Hwf & Hty) % type_app_inversion. asimpl. eauto.
  - intros (C & -> & Hty)%type_lam_inversion. asimpl. econstructor.
    eapply IHe; last done. eapply typed_subst_upctx. done.
  - (* pack *) intros (C & D & -> & Hty & Hwf1 & Hwf2)%type_pack_inversion.
    econstructor; [done..|]. eapply IHe; done.
  - intros (C & Hwf & Hty1 & Hty2)%type_unpack_inversion. asimpl.
    econstructor; first done.
    + eapply IHe; done.
    + eapply IHe0; last done.
      eapply typed_subst_up, typed_subst_upctx. done.
  - intros (? & ? & -> & ? & ?) % pair_inversion. asimpl. eauto.
  - intros (? & ?)%fst_inversion. asimpl. eauto.
  - intros (? & ?)%snd_inversion. asimpl. eauto.
  - intros (? & ? & -> & ? & ?)%injl_inversion. asimpl. eauto.
  - intros (? & ? & -> & ? & ?)%injr_inversion. asimpl. eauto.
  - intros (? & ? & ? & ? & ?)%case_inversion. asimpl. eauto.
Qed.

(** We can derive the on-paper version by specializing to single substitution. *)
Lemma type_substitution_single e e' Delta Gamma A B :
  TY Delta; Gamma |- e' : B ->
  TY Delta; B :: Gamma |- e : A ->
  TY Delta; Gamma |- e.[e'/] : A.
Proof.
  intros. eapply type_substitution; last done.
  eapply typed_subst_single. done.
Qed.

(** ** Preservation *)

(** Base step preservation **)
Lemma type_preservation_base_step e e' A :
  TY 0; [] |- e : A ->
  base_step e e' ->
  TY 0; [] |- e' : A.
Proof.
  intros Hty Hstep. destruct Hstep as [ | | | op e v v' Heq Heval | op e1 v1 e2 v2 v3 Heq1 Heq2 Heval | | | | | | ]; subst.
  - (* beta *) eapply app_inversion in Hty as (B & H1 & H2).
    eapply lam_inversion in H1 as (C & D & Heq & Hwf & Hty).
    simplify_eq.
    eapply type_substitution_single; done.
  - (* tbeta *)
    (* You will need the inversion lemmas type_app_inversion and type_lam_inversion, as well as
    type_tsubstitution_single. *)
    (* FILL IN HERE (5 LOC proof) *) admit.
  - (* unpack *)
    (* You will need the inversion lemmas type_unpack_inversion and
    type_pack_inversion, as well as type_substitution_single and
    type_tsubstitution_single. You will also need the [asimpl] tactic from
    Autosubst. *)
    (* FILL IN HERE (7 LOC proof) *) admit.
  - (* unop *)
    eapply unop_inversion in Hty as (A1 & Hop & Hty).
    assert ((A1 = Int /\ A = Int) \/ (A1 = Bool /\ A = Bool)) as [(-> & ->) | (-> & ->)].
    { inversion Hop; subst; eauto. }
    + eapply canonical_values_int in Hty as [n ->]; last by eauto.
      simpl in Heq. injection Heq as <-.
      inversion Hop; subst; simpl in *; injection Heval as <-; constructor.
    + eapply canonical_values_bool in Hty as [b ->]; last by eauto.
      simpl in Heq. injection Heq as <-.
      inversion Hop; subst; simpl in *; injection Heval as <-; constructor.
  - (* binop *)
    eapply binop_inversion in Hty as (A1 & A2 & Hop & Hty1 & Hty2).
    assert (A1 = Int /\ A2 = Int /\ (A = Int \/ A = Bool)) as (-> & -> & HC).
    { inversion Hop; subst; eauto. }
    eapply canonical_values_int in Hty1 as [n ->]; last by eauto.
    eapply canonical_values_int in Hty2 as [m ->]; last by eauto.
    simpl in Heq1, Heq2. simplify_eq.
    simpl in Heval.
    inversion Hop; subst; simpl in *; simplify_eq; constructor.
  - (* if true *) by eapply if_inversion in Hty as (H1 & H2 & H3).
  - (* if false *) by eapply if_inversion in Hty as (H1 & H2 & H3).
  - (* fst *) by eapply fst_inversion in Hty as (B & (? & ? & [= <- <-] & ? & ?)%pair_inversion).
  - (* snd *) by eapply snd_inversion in Hty as (B & (? & ? & [= <- <-] & ? & ?)%pair_inversion).
  - (* casel *) eapply case_inversion in Hty as (B & C & (? & ? & [= <- <-] & Hty & ?)%injl_inversion & ? & ?).
    eauto.
  - (* caser *) eapply case_inversion in Hty as (B & C & (? & ? & [= <- <-] & Hty & ?)%injr_inversion & ? & ?).
    eauto.
Admitted.

(** Evaluation context typing *)
Definition ectx_typing (K: ectx) (A B: type) :=
  forall e, TY 0; [] |- e : A -> TY 0; [] |- (fill K e) : B.

Lemma fill_typing_decompose K e A :
  TY 0; [] |- fill K e : A ->
  exists B, TY 0; [] |- e : B /\ ectx_typing K B A.
Proof.
  unfold ectx_typing; induction K in A |-*; simpl; inversion 1; subst; eauto.
  all: edestruct IHK as (? & ? & ?); eauto.
Qed.

Lemma fill_typing_compose K e A B :
  TY 0; [] |- e : B ->
  ectx_typing K B A ->
  TY 0; [] |- fill K e : A.
Proof.
  intros H1 H2; by eapply H2.
Qed.

(** Presevration lemma *)
Lemma type_preservation e e' A :
  TY 0; [] |- e : A ->
  contextual_step e e' ->
  TY 0; [] |- e' : A.
Proof.
  intros Hty Hstep. destruct Hstep as [K e1 e2 -> -> Hstep].
  eapply fill_typing_decompose in Hty as [B [H1 H2]].
  eapply fill_typing_compose; last done.
  by eapply type_preservation_base_step.
Qed.

(** Top-level type safety theorem. *)

Theorem type_safety e1 e2 A :
  TY 0; [] |- e1 : A ->
  rtc contextual_step e1 e2 ->
  progressive e2.
Proof.
  induction 2; eauto using type_progress, type_preservation.
Qed.
