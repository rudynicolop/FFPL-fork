From stdpp Require Import base relations tactics.
From ffpl.lib Require Import prelude sets maps.
From ffpl.type_systems.stlc Require Import lang notation.

(** ** Syntactic typing *)
(** In the Coq formalization, we exclusively define runtime typing (Curry-style). *)
(** It will be an exercise to consider Church-style typing. *)

Inductive type : Set :=
  | Int
  | Fun (A B : type).

(** In the lecture, we defined contexts 'Gamma' inductively.
However, in the end we are just using them as an association map that maps
variable names to types, so we use a type of finite partial maps in Coq: [gmap K
V]. Its key operations are:
- lookup: With [m : gmap K V] and [k : K], the term [m !! k] of type [option V]
  is a lookup of [k] in [m] that returns [Some v] if [k] maps to [v] and [None]
  if [k] does not currently map to anything.
- insert: With [m : gmap K V], [k : K], and [v : V], the term [ <[ k := v ]> m ]
  is the map where [k] maps to [v] and everything else maps the same way it does
  in [m]. This can be used to insert a new key into a map and to overwrite an
  already existing key.
In our case, variable names are strings, so the type of contexts is defined as
follows: *)
Notation typing_context := (gmap string type).

(** This command tells Coq that when a variable is named [Gamma] or [Gamma'] or
[Gamma1] or something like that, then it should implicitly have type
[typing_context], and similar for the other names and types. This avoids type
annotations in the rest of the file. *)
Implicit Types
  (Gamma : typing_context)
  (v : val)
  (e : expr)
  (A : type)
  (x : string).

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
  | type_lam Gamma x e A B :
      (* add a new type assignment to the context *)
     (<[ x := A ]> Gamma) |- e : B ->
      Gamma |- (Lam x e) : (A -> B)
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

(** a small example *)
Goal empty |- (lam: "x", 1 + "x")%E : (Int -> Int).
Proof. eauto. Qed.

(** We derive some inversion lemmas -- this is cleaner than directly
using the [inversion] tactic everywhere.*)
Lemma var_inversion Gamma (x : string) A :
  Gamma |- x : A -> Gamma !! x = Some A.
Proof. inversion 1; subst; auto. Qed.

Lemma lam_inversion Gamma (x : string) e C :
  (Gamma |- (lam: x, e) : C) ->
  exists A B, C = (A -> B)%ty /\ <[x:=A]> Gamma |- e : B.
(** [eauto] has a "fuel" parameter that tells it how long it shoud keep
going before giving up on a goal. Here we need to increase the fuel to 10
to enable it to solve all goals. *)
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

(** Canonical forms lemmas (Lemma 7) *)
Lemma canonical_values_arr Gamma e A B :
  Gamma |- e : (A -> B) ->
  is_val e ->
  exists x e', e = (lam: x, e')%E.
(* CLASS *) Proof.
  inversion 1; simpl; by eauto.
Qed.

Lemma canonical_values_int Gamma e :
  Gamma |- e : Int ->
  is_val e ->
  exists n: Z, e = n.
(* CLASS *) Proof.
  inversion 1; simpl; by eauto.
Qed.

(** Definition 6 *)
Definition progressive (e : expr) :=
  is_val e \/ exists e', contextual_step e e'.

(** Theorem 8 *)
Theorem type_progress e A :
  empty |- e : A -> progressive e.
(* CLASS *) Proof.
  remember empty as Gamma. induction 1 as [??? Hx| | | Gamma e1 e2 A B Hty IH1 _ IH2 | Gamma e1 e2 Hty1 IH1 Hty2 IH2].
  - subst.
    (** The lemma [lookup_empty] shows that [empty !! x = None], which in this
    case suffices to complete the proof by contradiction. *)
    rewrite lookup_empty in Hx. done.
  - left. done.
  - left. done.
  - destruct (IH2 HeqGamma) as [H2|H2]; [destruct (IH1 HeqGamma) as [H1|H1]|].
    + eapply canonical_values_arr in Hty as (x & e & ->); last done.
      right. eexists.
      eapply base_contextual_step, BetaS; eauto.
    + right. eapply is_val_rewrite in H2 as [v ->].
      destruct H1 as [e1' Hstep].
      eexists. eapply (fill_contextual_step [AppLCtx v]). done.
    + right. destruct H2 as [e2' H2].
      eexists. eapply (fill_contextual_step [AppRCtx e1]). done.
  - destruct (IH2 HeqGamma) as [H2|H2]; first destruct (IH1 HeqGamma) as [H1|H1].
    + right. eapply canonical_values_int in Hty1 as [n1 ->]; last done.
      eapply canonical_values_int in Hty2 as [n2 ->]; last done.
      eexists. eapply base_contextual_step. eapply PlusS; eauto.
    + right. eapply is_val_rewrite in H2 as [v ->].
      destruct H1 as [e1' Hstep].
      eexists. eapply (fill_contextual_step [PlusLCtx v]). done.
    + right. destruct H2 as [e2' H2].
      eexists. eapply (fill_contextual_step [PlusRCtx e1]). done.
Qed.

(** * Preservation *)

(** Helper lemmas for base preservation *)

(** We are using various lemmas about maps here, such as [lookup_weaken]
and [insert_mono]. Use [About] to learn about their statements. *)

(** Lemma 9 *)
Lemma type_weakening Gamma1 Gamma2 e A :
  Gamma1 |- e : A ->
  Gamma1 `subseteq` Gamma2 ->
  Gamma2 |- e : A.
(* CLASS *) Proof.
  induction 1 in Gamma2; intros Hsub.
  - eauto using lookup_weaken.
  - eauto using insert_mono.
  - eauto.
  - eauto.
  - eauto.
Qed.

(** Lemma 10 *)
Lemma type_substitution e e' Gamma x A B :
  empty |- e' : A ->
  <[x := A]> Gamma |- e : B ->
  Gamma |- subst x e' e : B.
(* CLASS *) Proof.
  intros He'. revert B Gamma; induction e as [y | y | | |]; intros B Gamma; simpl.
  - intros Hp%var_inversion.
    (** We could say [destruct (decide (x = y))] here to make progress in the proof,
    but [destruct] is smart and we can give it a partial term that it will then
    find in the goal to figure out what we want to do case distinction on. *)
    destruct (decide _); subst; eauto.
    + Search (<[?x:=_]> _ !! ?x = Some _).
      rewrite lookup_insert_eq in Hp. simplify_eq.
      eapply type_weakening; first done. apply map_empty_subseteq.
    + rewrite lookup_insert_ne in Hp; last done. auto.
  - intros (C & D & -> & Hty)%lam_inversion.
    econstructor. destruct (decide _) as [|Heq]; simplify_eq.
    + by rewrite insert_insert in Hty.
    + rewrite insert_commute // in Hty. by eapply IHe.
  - intros (C & Hty1 & Hty2)%app_inversion. eauto.
  - intros ->%lit_int_inversion. eauto.
  - intros (-> & Hty1 & Hty2)%plus_inversion. eauto.
Qed.

(** Base preservation (Lemma 11) *)
Lemma type_preservation_base_step e e' A :
  empty |- e : A ->
  base_step e e' ->
  empty |- e' : A.
(* CLASS *) Proof.
  intros Hty Hstep. destruct Hstep as [| e1 e2 n1 n2 n3 Heq1 Heq2 Heval]; subst.
  - eapply app_inversion in Hty as (B & Hty1 & Hty2).
    eapply lam_inversion in Hty1 as (B' & A' & Heq1 & Hty).
    simplify_eq. eapply type_substitution; eauto.
  - eapply plus_inversion in Hty as (-> & Hty1 & Hty2).
    econstructor.
Qed.

(** Contextual typing for evaluation context items and evaluation contexts  *)
Definition ectx_item_typing (Ki : ectx_item) (A B : type) :=
  forall e, empty |- e : A -> empty |- (fill_item Ki e) : B.

Lemma fill_item_typing_decompose Ki e A :
  empty |- fill_item Ki e : A ->
  exists B, empty |- e : B /\ ectx_item_typing Ki B A.
(* CLASS *) Proof.
  unfold ectx_item_typing; destruct Ki; simpl; inversion 1; subst; eauto.
Qed.

Definition ectx_typing (K : ectx) (A B : type) :=
  forall e, empty |- e : A -> empty |- (fill K e) : B.

(** Lemma 12 *)
Lemma fill_typing_decompose K e A :
  empty |- fill K e : A ->
  exists B, empty |- e : B /\ ectx_typing K B A.
(* CLASS *) Proof.
  (** The [in e |- *] here performs automatic generalization over [e]. *)
  (** Contrary to the proof in the notes, we don't need to generalize [A] here,
  because prepending a context item to a context list corresponds to
  precomposing with the context item. *)
  unfold ectx_typing. induction K as [|k K] in e |- *; simpl; eauto.
  intros [B [Hit Hty]]%IHK.
  eapply fill_item_typing_decompose in Hit as [B' [? ?]]; eauto.
Qed.

(** Lemma 13 *)
Lemma fill_typing_compose K e A B :
  empty |- e : B ->
  ectx_typing K B A ->
  empty |- fill K e : A.
(* CLASS *) Proof.
  intros H1 H2; by eapply H2.
Qed.

(** Preservation (Theorem 14) *)
Theorem type_preservation e e' A :
  empty |- e : A ->
  contextual_step e e' ->
  empty |- e' : A.
(* CLASS *) Proof.
  intros Hty Hstep. destruct Hstep as [K e1 e2 -> -> Hstep].
  eapply fill_typing_decompose in Hty as [B [H1 H2]].
  eapply fill_typing_compose; last done.
  by eapply type_preservation_base_step.
Qed.

(** Corollary 15 *)

Definition safe e :=
  forall e', rtc contextual_step e e' -> progressive e'.

Corollary type_safety e A:
  empty |- e : A ->
  safe e.
(* REMOVE *) Proof.
  induction 2; eauto using type_progress, type_preservation.
Qed.
