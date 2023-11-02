From stdpp Require Import base relations.
From ffpl.lib Require Import prelude sets maps.
From ffpl.type_systems.stlc Require Import lang notation types parallel_subst.
From Equations Require Import Equations.

(** The next command makes Coq guess the type of a variable based on its name.
*)
Implicit Types
  (Gamma : typing_context)
  (v : val)
  (e : expr)
  (A : type).


(** ** Definition of the logical relation. *)

(** The logical relation is defined mutually recursively on expressions and values.
To encode this in Coq, we define a type that is "expression or value", and then
define the relation on that. The [inj_val] and [inj_expr] constructors
are used to convert values/expressions into that shared type. *)
Inductive val_or_expr : Type :=
| inj_val : val -> val_or_expr
| inj_expr : expr -> val_or_expr.

(**
  In Coq, we need to make argument why the logical relation is well-defined precise:
  This holds true in particular for the mutual recursion between the value relation and the expression relation
   (note that the value relation is defined in terms of the expression relation, and vice versa).
  We therefore define a termination measure [mut_measure] that makes sure that for each recursive call, we either
   - decrease the size of the type
   - or switch from the expression case to the value case.

  We use the Equations package to define the logical relation, as it's tedious to make the termination
   argument work with Coq's built-in support for recursive functions---but under the hood, Equations also
   just encodes it as a Coq Fixpoint.
 *)

(* The [type_size] function just structurally descends, essentially taking the size of the "type tree". *)
Equations type_size (t : type) : nat :=
  type_size Int := 1;
  type_size (Fun A B) := type_size A + type_size B + 1.

(* The definition of the expression relation uses the value relation -- therefore, it needs to be larger, and we add [1]. *)
Equations mut_measure (ve : val_or_expr) (t : type) : nat :=
  mut_measure (inj_expr e) t := 1 + type_size t;
  mut_measure (inj_val v) t := type_size t.


(** The main definition of the logical relation.

  The [by wf ..] part tells Equations to use [mut_measure] for the well-formedness argument.
  It turns out that we get nicer simplification behavior for the expression case
  by putting the [val + expr] argument first.
 *)
Equations type_interp (ve : val_or_expr) (t : type) : Prop by wf (mut_measure ve t) := {
  type_interp (inj_val v) Int =>
    exists z : Z, v = z ;
  type_interp (inj_val v) (A -> B) =>
    (* [closed X v] in Coq corresponds to [fv(v) `subeteq` X] on paper. *)
    exists x e, v = @LamV x e /\ closed empty v /\
      forall v',
        type_interp (inj_val v') A ->
        type_interp (inj_expr (subst x v' e)) B;

  type_interp (inj_expr e) t =>
    exists v, big_step e v /\ type_interp (inj_val v) t
}.
Next Obligation.
  (** [simp] is a tactic provided by [Equations]. It rewrites with the defining equations of the definition.
    [simpl]/[cbn] will NOT unfold definitions made with Equations.
   *)
  repeat simp mut_measure; simp type_size; lia.
Qed.
Next Obligation.
  simp mut_measure. simp type_size.
  destruct A; repeat simp mut_measure; repeat simp type_size; lia.
Qed.

(** We derive the expression/value relation.
Note that these are [Notation], not [Definition]: we are not introducing new
terms here that have to be unfolded, we are merly introducing a notational short-hand.
This means tactics like [simp] can still "see" the underlying [type_interp],
which makes proof a lot more pleasant. *)
Notation sem_val_rel t v := (type_interp (inj_val v) t).
Notation sem_expr_rel t e := (type_interp (inj_expr e) t).

(** *** Semantic typing of contexts *)
(** Substitutions map to expressions -- this is so that we can more easily reuse notions like closedness *)
Implicit Types
  (gamma : gmap string expr).

Inductive sem_ctx_rel : typing_context -> (gmap string expr) -> Prop :=
  | sem_ctx_rel_empty : sem_ctx_rel empty empty
  | sem_ctx_rel_insert Gamma gamma v x A :
    sem_val_rel A v ->
    sem_ctx_rel Gamma gamma ->
    sem_ctx_rel (<[x := A]> Gamma) (<[x := of_val v]> gamma).


(** The semantic typing judgment *)
Definition sem_typed Gamma e A :=
  closed (dom Gamma) e /\
  forall gamma, sem_ctx_rel Gamma gamma -> sem_expr_rel A (subst_map gamma e).
Notation "Gamma |= e : A" := (sem_typed Gamma e A) (at level 74, e, A at next level).

(** We start by proving a couple of helper lemmas that will be useful later. *)

Lemma val_rel_closed v A:
  sem_val_rel A v -> closed empty v.
Proof.
  induction A; simp type_interp.
  - intros [z ->]. done.
  - intros (x & e & -> & Hcl & _). done.
Qed.

Lemma ctx_rel_closed Gamma gamma :
  sem_ctx_rel Gamma gamma -> subst_closed empty gamma.
Proof.
  induction 1; rewrite /subst_closed.
  - intros x e. rewrite lookup_empty. done.
  - intros y e. rewrite lookup_insert_Some.
    intros [[-> <-]|[Hne Hlook]].
    + eapply val_rel_closed. done.
    + eapply IHsem_ctx_rel; last done.
Qed.

(** This is basically the inversion lemma for [sem_ctx_rel]:
if a variable exists in Gamma, then we can find a suitable value in gamma. *)
Lemma ctx_rel_lookup Gamma gamma x A :
  sem_ctx_rel Gamma gamma ->
  Gamma !! x = Some A ->
  exists v, gamma !! x = Some (of_val v) /\ sem_val_rel A v.
Proof.
  induction 1 as [|Gamma gamma v y B Hval Hctx IH].
  - rewrite lookup_empty. done.
  - rewrite lookup_insert_Some. intros [[-> ->]|[Hne Hlook]].
    + exists v. split; first by rewrite lookup_insert_eq.
      eauto.
    + eapply IH in Hlook as (w & Hlook & Hval_w).
      eexists. split; first by rewrite lookup_insert_ne.
      eauto.
Qed.

Lemma ctx_rel_dom Gamma gamma :
  sem_ctx_rel Gamma gamma -> dom Gamma = dom gamma.
Proof.
  induction 1; first by rewrite !dom_empty.
  rewrite !dom_insert. congruence.
Qed.

(** Lemma 17: Value Inclusion *)
Lemma val_inclusion A v :
  sem_val_rel A v -> sem_expr_rel A (of_val v).
Proof.
  intros Hv. simp type_interp. exists v.
  split; last done. apply big_step_vals.
Qed.

(** *** Compatibility lemmas *)

(** Lemma 19 *)
Lemma compat_int Gamma z : Gamma |= (LitInt z) : Int.
Proof.
  split; first done.
  intros gamma _. simpl. apply (val_inclusion _ z).
  simp type_interp. eauto.
Qed.

(** Lemma 20 *)
Lemma compat_var Gamma x A :
  Gamma !! x = Some A ->
  Gamma |= (Var x) : A.
Proof.
  intros Hx. split.
  { simpl. apply bool_decide_pack. apply elem_of_dom. eauto. }
  intros gamma Hctx; simpl.
  eapply ctx_rel_lookup in Hx as (v & Hlookup & Hv); last done.
  rewrite Hlookup. apply val_inclusion. done.
Qed.

(** Lemma 21 *)
Lemma compat_app Gamma e1 e2 A B :
  Gamma |= e1 : (A -> B) ->
  Gamma |= e2 : A ->
  Gamma |= (e1 e2) : B.
Proof.
  intros [Hfuncl Hfun] [Hargcl Harg]. split.
  { simpl. eauto. }
  intros gamma Hctx; simpl.
  specialize (Hfun _ Hctx). simp type_interp in Hfun. destruct Hfun as (v1 & Hbs1 & Hv1).
  simp type_interp in Hv1. destruct Hv1 as (x & e & -> & _ & Hv1).
  specialize (Harg _ Hctx). simp type_interp in Harg.
  destruct Harg as (v2 & Hbs2 & Hv2).

  apply Hv1 in Hv2.
  simp type_interp in Hv2. destruct Hv2 as (v & Hbsv & Hv).

  simp type_interp.
  exists v.
  split; last done.
  eauto.
Qed.

(* Compatibility for [lam] unfortunately needs a very technical helper lemma. *)
Lemma lam_closed Gamma gamma x A e :
  closed (dom (<[x:=A]> Gamma)) e ->
  sem_ctx_rel Gamma gamma ->
  closed ∅ (lam: x, subst_map (delete x gamma) e)%V.
Proof.
  intros Hcl Hctxt. simpl. eapply closed_subst_map.
  - eapply closed_weaken; first done.
    rewrite dom_delete dom_insert (ctx_rel_dom Gamma gamma) //.
    (* The [set_solver] tactic is great for solving goals involving set
    inclusion and union. However, when set difference is involved, it can't
    always solve the goal -- we need to help it by doing a case distinction on
    whether the element we are considering is [x] or not. *)
    intros y. destruct (decide (x = y)); set_solver.
  - eapply subst_closed_weaken, ctx_rel_closed; last done.
    + set_solver.
    + apply map_delete_subseteq.
Qed.

(** Lemma 22 *)
Lemma compat_lam Gamma x e A B :
  (<[ x := A ]> Gamma) |= e : B ->
  Gamma |= (Lam x e) : (A -> B).
Proof.
  intros [Hcl Hbody]. split.
  { simpl. eapply closed_weaken; first done. set_solver. }
  intros gamma Hctxt. simpl.
  apply (val_inclusion _ ((lam: x, subst_map (delete x gamma) e))%V).
  simp type_interp.
  eexists _, _. split; first done.
  split.
  { by eapply lam_closed. }

  intros v Hv.
  specialize (Hbody (<[ x := of_val v]> gamma)).
  rewrite subst_subst_map; last by eapply ctx_rel_closed.
  apply Hbody.
  constructor; try done.
Qed.

(** Omitted in the lecture notes *)
Lemma compat_add Gamma e1 e2 :
  Gamma |= e1 : Int ->
  Gamma |= e2 : Int ->
  Gamma |= (e1 + e2) : Int.
Proof.
  intros [Hcl1 He1] [Hcl2 He2]. split.
  { simpl. eauto. }
  intros gamma Hctx. simpl.
  simp type_interp.
  specialize (He1 _ Hctx). specialize (He2 _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  exists (z1 + z2)%Z. split.
  - constructor; done.
  - exists (z1 + z2)%Z. done.
Qed.

(** Theorem 23 *)
Theorem sem_soundness Gamma e A :
  (Gamma |- e : A)%ty ->
  Gamma |= e : A.
Proof.
  induction 1.
  - by apply compat_var.
  - by apply compat_lam.
  - by apply compat_int.
  - by eapply compat_app.
  - by apply compat_add.
Qed.

(** Corollary 24 *)
Corollary termination e A :
  (empty |- e : A)%ty ->
  exists v, big_step e v.
Proof.
  intros [_ Hsem]%sem_soundness.
  specialize (Hsem empty).
  simp type_interp in Hsem.
  rewrite subst_map_empty in Hsem.
  destruct Hsem as (v & Hbs & _); last by eauto.
  constructor.
Qed.
