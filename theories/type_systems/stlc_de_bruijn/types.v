From stdpp Require Import base relations tactics.
From ffpl.lib Require Import prelude sets maps.
From ffpl.type_systems.stlc_de_bruijn Require Import lang notation.

(** ** Syntactic typing *)
(** In the Coq formalization, we exclusively define runtime typing (Curry-style). *)

Inductive type : Set :=
  | Int
  | Fun (A B : type).

(** Now that variables are using De Bruijn indices, typing contexts are just lists of types.
On paper we write "Gamma, A" to extend a context, but lists in Coq are indexed
from the left so this will correspond to [A :: Gamma]. *)
Notation typing_context := (list type).

Implicit Types
  (Gamma : typing_context)
  (v : val)
  (e : expr)
  (A : type).

(** We define notation for types in a new scope with delimiter [ty].
  See below for an example. *)
Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Infix "->" := Fun : FType_scope.

(** Typing rules *)
(** We need to reserve the notation beforehand to already use it when defining the
   typing rules. *)
Reserved Notation "Gamma |- e : A" (at level 74, e, A at next level).
Inductive syn_typed : typing_context -> expr -> type -> Prop :=
  | type_var Gamma x A :
      (* lookup the variable in the context *)
      Gamma !! x = Some A ->
      Gamma |- (Var x) : A
  | type_lam Gamma e A B :
      (* add a new type assignment to the context *)
      (A :: Gamma) |- e : B ->
      Gamma |- (Lam e) : (A -> B)
  | type_int Gamma z :
      Gamma |- (LitInt z) : Int
  | type_app Gamma e1 e2 A B :
      Gamma |- e1 : (A -> B) ->
      Gamma |- e2 : A ->
      Gamma |- e1 e2 : B
  | type_add Gamma e1 e2 :
      Gamma |- e1 : Int ->
      Gamma |- e2 : Int ->
      Gamma |- e1 + e2 : Int
where "Gamma |- e : A" := (syn_typed Gamma e%E A%ty) : FType_scope.
(** Add constructors to [eauto]'s hint database. *)
#[export] Hint Constructors syn_typed : core.
Local Open Scope FType_scope.
(** Also export the notation (it would otherwise remain local to this file). *)
Notation "Gamma |- e : A" := (syn_typed Gamma e%E A%ty).

(** some small examples *)
Goal [] |- (lam: 1 + ^0)%E : (Int -> Int).
Proof. eauto. Qed.
Goal [Int] |- (lam: ^1 + ^0)%E : (Int -> Int).
Proof. eauto. Qed.
Goal [Int; Int -> Int] |- (^1 ^0)%E : Int.
Proof. eauto. Qed.

(** We derive some inversion lemmas -- this is cleaner than directly
using the [inversion] tactic everywhere.*)
Lemma var_inversion Gamma (x : var) A :
  Gamma |- Var x : A -> Gamma !! x = Some A.
Proof. inversion 1; subst; auto. Qed.

Lemma lam_inversion Gamma e C :
  (Gamma |- (lam: e) : C) ->
  exists A B, C = (A -> B)%ty /\ A :: Gamma |- e : B.
Proof. inversion 1; subst; eauto. Qed.

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

(** Canonical forms lemmas *)
Lemma canonical_values_arr Gamma e A B :
  Gamma |- e : (A -> B) ->
  is_val e ->
  exists e', e = (lam: e')%E.
Proof.
  inversion 1; simplify_eq; by eauto.
Qed.

Lemma canonical_values_int Gamma e :
  Gamma |- e : Int ->
  is_val e ->
  exists n: Z, e = n.
Proof.
  inversion 1; simplify_eq; by eauto.
Qed.

Definition reducible (e : expr) :=
  exists e', contextual_step e e'.

Definition progressive (e : expr) :=
  is_val e \/ reducible e.

Theorem type_progress e A :
  [] |- e : A -> progressive e.
(* CLASS *) Proof.
  remember [] as Gamma. induction 1 as [??? Hx| | | Gamma e1 e2 A B Hty IH1 _ IH2 | Gamma e1 e2 Hty1 IH1 Hty2 IH2].
  - subst. rewrite lookup_nil in Hx. done.
  - left. by eauto.
  - left. by eauto.
  - destruct (IH2 HeqGamma) as [H2|H2]; [destruct (IH1 HeqGamma) as [H1|H1]|].
    + eapply canonical_values_arr in Hty as (e & ->); last done.
      right. eexists.
      eapply base_contextual_step, BetaS; eauto.
    + right. apply is_val_make_val in H2 as [v ->].
      destruct H1 as [e1' Hstep].
      eexists. eapply (fill_contextual_step [AppLCtx v]). done.
    + right. destruct H2 as [e2' H2].
      eexists. eapply (fill_contextual_step [AppRCtx e1]). done.
  - destruct (IH2 HeqGamma) as [H2|H2]; first destruct (IH1 HeqGamma) as [H1|H1].
    + right. eapply canonical_values_int in Hty1 as [n1 ->]; last done.
      eapply canonical_values_int in Hty2 as [n2 ->]; last done.
      eexists. eapply base_contextual_step. eapply PlusS; eauto.
    + right. apply is_val_make_val in H2 as [v ->].
      destruct H1 as [e1' Hstep].
      eexists. eapply (fill_contextual_step [PlusLCtx v]). done.
    + right. destruct H2 as [e2' H2].
      eexists. eapply (fill_contextual_step [PlusRCtx e1]). done.
Qed.

(** * Preservation *)

(** Helper lemmas for base preservation *)

(** The weakening and substitution lemmas change significantly with De Bruijn
indices. First we have to generalize our idea of "weakening" to renamings that
preserve typing from one context to another. Basically, [delta] tells us "how"
[Gamma1] is included in [Gamma2] by showing, for each type in [Gamma1], where we
can find the same type in [Gamma2]. *)
Definition typed_ren (Gamma1 Gamma2 : typing_context) (delta : var -> var) :=
  forall x B, Gamma1 !! x = Some B -> Gamma2 !! (delta x) = Some B.

(** [typed_ren] is preserved when both context get identically extended with
a new type at position 0, and [delta] is shifted up by 1. *)
Lemma typed_ren_up delta Gamma1 Gamma2 A :
  typed_ren Gamma1 Gamma2 delta ->
  typed_ren (A :: Gamma1) (A :: Gamma2) (upren delta).
Proof.
  intros Hdelta [|x] C; simpl; eauto.
Qed.

(** [Gamma] is included in [A :: Gamma] with the successor renaming. *)
Lemma typed_ren_S A Gamma :
  typed_ren Gamma (A :: Gamma) S.
Proof.
  intros y B'. asimpl. eauto.
Qed.

(** Lemma 26 *)
Lemma type_renaming e Gamma1 Gamma2 (delta : var -> var) A :
  typed_ren Gamma1 Gamma2 delta ->
  Gamma1 |- e : A ->
  Gamma2 |- e.[ren delta] : A.
Proof.
  intros Hdelta. induction 1 in Gamma2, delta, Hdelta.
  (* The [asimpl] tactic understands the properties of substituions and uses them
  to simplify the goal. *)
  all: asimpl.
  - constructor. eapply Hdelta. done.
  - constructor. eapply IHsyn_typed. eapply typed_ren_up. done.
  - eauto.
  - eauto.
  - eauto.
Qed.

(** For the substitution lemma, we introduce the idea of a type-preserving
substitution. Note that this is very similar to [typed_ren], but instead of
[Gamma2 !! (delta x) = Some B] (which only makes sense when [delta x] is a
variable) we know have [Gamma2 |- sigma x : B] (which makes sense even when
[sigma x] is an arbitrary term). *)
Definition typed_subst (Gamma1 Gamma2 : typing_context) (sigma : var -> expr) :=
  forall x B, Gamma1 !! x = Some B -> Gamma2 |- sigma x : B.

(** On renamings, [typed_ren] and [typed_subst] are equivalent.
(We don't actually need this lemma for the type safety proof, but it demonstrates
that [typed_subst] is a generalization of [typed_ren].) *)
Lemma typed_subst_ren (Gamma1 Gamma2 : typing_context) (delta : var -> var) :
  typed_ren Gamma1 Gamma2 delta <-> typed_subst Gamma1 Gamma2 (ren delta).
Proof.
  split.
  - intros Hdelta x B Hx. specialize (Hdelta _ _ Hx). by constructor.
  - intros Hdelta x B Hx. specialize (Hdelta _ _ Hx). by inversion Hdelta.
Qed.

(** [typed_subst] is preserved when both context get identically extended with
a new type at position 0, and [sigma] is shifted up by 1. *)
Lemma typed_subst_up sigma Gamma1 Gamma2 A :
  typed_subst Gamma1 Gamma2 sigma ->
  typed_subst (A :: Gamma1) (A :: Gamma2) (up sigma).
Proof.
  intros Hsigma [|x] B; asimpl.
  + intros [= ->]. eauto.
  + intros Hx. specialize (Hsigma _ _ Hx).
    eapply type_renaming; last done. eapply typed_ren_S.
Qed.

(** The (parallel) substitution [e .: ids] corresponds to the single-variable
substitution [term.[e/]]: it replaces variable 0 with [e] and shifts everything
down by one. This lemma shows the type of that substitution: it removes a type
[A] from the context. *)
Lemma typed_subst_single Gamma A e :
  Gamma |- e : A ->
  typed_subst (A :: Gamma) Gamma (e .: ids).
Proof.
  intros He [|x] C; simpl; intros Hx.
  - simplify_eq. done.
  - eauto.
Qed.

(** Lemma 27 *)
Lemma type_substitution e Gamma1 Gamma2 sigma A :
  typed_subst Gamma1 Gamma2 sigma ->
  Gamma1 |- e : A ->
  Gamma2 |- e.[sigma] : A.
Proof.
  intros Hsigma. induction e in Gamma1, Gamma2, A, sigma, Hsigma |- *.
  - intros Hp%var_inversion. asimpl. eapply Hsigma. done.
  - intros (C & D & -> & Hty)%lam_inversion. asimpl.
    econstructor. eapply IHe; last done. by eapply typed_subst_up.
  - intros (C & Hty1 & Hty2)%app_inversion. asimpl. eauto.
  - intros ->%lit_int_inversion. asimpl. eauto.
  - intros (-> & Hty1 & Hty2)%plus_inversion. asimpl. eauto.
Qed.

(** Lemma 28: We can derive a substitution lemma for single-variable substitution.
Note how this is significantly stronger than the version we proved for string-based
substitution! [e'] can now use the variables in [Gamma], which the previous
lemma did not allow. This is because previously we needed [e'] to be a closed
term to avoid the problems with capturing substitution, but now with De Bruijn
indices we have a proper capture-avoiding substitution. *)
Lemma type_substitution_single e e' Gamma A B :
  Gamma |- e' : B ->
  B :: Gamma |- e : A ->
  Gamma |- e.[e'/] : A.
Proof.
  intros. eapply type_substitution; last done.
  eapply typed_subst_single. done.
Qed.

(** Base preservation *)
Lemma type_preservation_base_step e e' A :
  [] |- e : A ->
  base_step e e' ->
  [] |- e' : A.
Proof.
  intros Hty Hstep. destruct Hstep as [| e1 e2 n1 n2 n3 Heq1 Heq2 Heval]; subst.
  - eapply app_inversion in Hty as (B & Hty1 & Hty2).
    eapply lam_inversion in Hty1 as (B' & A' & Heq1 & Hty).
    simplify_eq. eapply type_substitution_single; done.
  - eapply plus_inversion in Hty as (-> & Hty1 & Hty2).
    econstructor.
Qed.

(** Contextual typing for evaluation context items and evaluation contexts  *)
Definition ectx_item_typing (Ki : ectx_item) (A B : type) :=
  forall e, [] |- e : A -> [] |- (fill_item Ki e) : B.

Lemma fill_item_typing_decompose Ki e A :
  [] |- fill_item Ki e : A ->
  exists B, [] |- e : B /\ ectx_item_typing Ki B A.
(* CLASS *) Proof.
  unfold ectx_item_typing; destruct Ki; simpl; inversion 1; subst; eauto.
Qed.

Definition ectx_typing (K : ectx) (A B : type) :=
  forall e, [] |- e : A -> [] |- (fill K e) : B.

Lemma fill_typing_decompose K e A :
  [] |- fill K e : A ->
  exists B, [] |- e : B /\ ectx_typing K B A.
(* CLASS *) Proof.
  unfold ectx_typing. induction K as [|k K] in e |- *; simpl; eauto.
  intros [B [Hit Hty]]%IHK.
  eapply fill_item_typing_decompose in Hit as [B' [? ?]]; eauto.
Qed.

Lemma fill_typing_compose K e A B :
  [] |- e : B ->
  ectx_typing K B A ->
  [] |- fill K e : A.
(* CLASS *) Proof.
  intros H1 H2; by eapply H2.
Qed.

(** Preservation *)
Theorem type_preservation e e' A :
  [] |- e : A ->
  contextual_step e e' ->
  [] |- e' : A.
(* CLASS *) Proof.
  intros Hty Hstep. destruct Hstep as [K e1 e2 -> -> Hstep].
  eapply fill_typing_decompose in Hty as [B [H1 H2]].
  eapply fill_typing_compose; last done.
  by eapply type_preservation_base_step.
Qed.

(** And finally: Type Safety *)
Corollary type_safety e1 e2 A :
  [] |- e1 : A ->
  rtc contextual_step e1 e2 ->
  progressive e2.
(* REMOVE *) Proof.
  induction 2; eauto using type_progress, type_preservation.
Qed.
