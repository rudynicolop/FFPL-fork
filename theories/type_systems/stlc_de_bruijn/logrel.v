From stdpp Require Import base relations.
From ffpl.lib Require Import prelude sets maps.
From ffpl.type_systems.stlc_de_bruijn Require Import lang notation bigstep types.
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
Equations type_size (A : type) : nat :=
  type_size Int := 1;
  type_size (Fun A B) := type_size A + type_size B + 1.

(* The definition of the expression relation uses the value relation -- therefore, it needs to be larger, and we add [1]. *)
Equations mut_measure (ve : val_or_expr) (A : type) : nat :=
  mut_measure (inj_expr e) A := 1 + type_size A;
  mut_measure (inj_val v) A := type_size A.


(** The main definition of the logical relation.

  The [by wf ..] part tells Equations to use [mut_measure] for the well-formedness argument.
  It turns out that we get nicer simplification behavior for the expression case
  by putting the [val + expr] argument first.
 *)
Equations type_interp (ve : val_or_expr) (A : type) : Prop by wf (mut_measure ve A) := {
  type_interp (inj_val v) Int =>
    exists z : Z, v = z ;
  type_interp (inj_val v) (A -> B) =>
    exists e, v = LamV e /\
      forall v',
        type_interp (inj_val v') A ->
        type_interp (inj_expr e.[of_val v'/]) B;

  type_interp (inj_expr e) A =>
    exists v, big_step e v /\ type_interp (inj_val v) A
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
Notation sem_val_rel A v := (type_interp (inj_val v) A).
Notation sem_expr_rel A e := (type_interp (inj_expr e) A).

(** *** Semantic typing of contexts *)

(** As before, we use maps to [expr] rather than [val] to represent "value
substitutions", this time because they can be directly used as substitutions with
Autosubst. *)
Implicit Types (gamma : var -> expr).

Definition sem_ctx_rel Gamma gamma :=
  forall x A, Gamma !! x = Some A -> exists v, gamma x = of_val v /\ sem_val_rel A v.

(** The semantic typing judgment *)
Definition sem_typed Gamma e A :=
  forall gamma, sem_ctx_rel Gamma gamma -> sem_expr_rel A e.[gamma].
Notation "Gamma |= e : A" := (sem_typed Gamma e A) (at level 74, e, A at next level).

(** We start by proving a couple of helper lemmas that will be useful later. *)

Lemma sem_ctx_rel_nil gamma : sem_ctx_rel [] gamma.
Proof.
  intros x A. rewrite lookup_nil. done.
Qed.

Lemma sem_ctx_rel_cons Gamma gamma v A :
  sem_val_rel A v ->
  sem_ctx_rel Gamma gamma ->
  sem_ctx_rel (A :: Gamma) (of_val v .: gamma).
Proof.
  intros Hv Hgamma [|x] B; simpl.
  - intros [= <-]. eauto.
  - eapply Hgamma.
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
  intros gamma _. simpl. apply (val_inclusion _ z).
  simp type_interp. eauto.
Qed.

(** Lemma 20 *)
Lemma compat_var Gamma x A :
  Gamma !! x = Some A ->
  Gamma |= (Var x) : A.
Proof.
  intros Hx gamma Hctx; simpl.
  specialize (Hctx _ _ Hx) as (v & Hlookup & Hv).
  rewrite Hlookup. apply val_inclusion. done.
Qed.

(** Lemma 21 *)
Lemma compat_add Gamma e1 e2 :
  Gamma |= e1 : Int ->
  Gamma |= e2 : Int ->
  Gamma |= (e1 + e2) : Int.
Proof.
  intros He1 He2 gamma Hctx. simpl.
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

(** Lemma 22 *)
Lemma compat_app Gamma e1 e2 A B :
  Gamma |= e1 : (A -> B) ->
  Gamma |= e2 : A ->
  Gamma |= (e1 e2) : B.
Proof.
  intros Hfun Harg gamma Hctx; simpl.
  specialize (Hfun _ Hctx). simp type_interp in Hfun. destruct Hfun as (v1 & Hbs1 & Hv1).
  simp type_interp in Hv1. destruct Hv1 as (e & -> & Hv1).
  specialize (Harg _ Hctx). simp type_interp in Harg.
  destruct Harg as (v2 & Hbs2 & Hv2).

  apply Hv1 in Hv2.
  simp type_interp in Hv2. destruct Hv2 as (v & Hbsv & Hv).

  simp type_interp.
  exists v.
  split; last done.
  eauto.
Qed.

(** Lemma 23 *)
Lemma compat_lam Gamma e A B :
  (A :: Gamma) |= e : B ->
  Gamma |= (Lam e) : (A -> B).
Proof.
  intros Hbody gamma Hctxt. asimpl.
  apply (val_inclusion _ (lam: _)%V).
  simp type_interp.
  eexists _. split; first done.

  intros v Hv.
  asimpl. apply (Hbody (of_val v .: gamma)).
  eapply sem_ctx_rel_cons; done.
Qed.

(** Theorem 24 *)
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

(** Corollary 25 *)
Corollary termination e A :
  ([] |- e : A)%ty ->
  exists v, big_step e v.
Proof.
  intros Hsem%sem_soundness.
  specialize (Hsem ids).
  simp type_interp in Hsem.
  destruct Hsem as (v & Hbs & _).
  { eapply sem_ctx_rel_nil. }
  asimpl in Hbs. eauto.
Qed.
