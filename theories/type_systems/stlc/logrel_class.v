From stdpp Require Import base relations.
From ffpl.lib Require Import prelude sets maps.
From ffpl.type_systems.stlc Require Import lang notation types parallel_subst.
From Equations Require Import Equations.

Implicit Types
  (Gamma : typing_context)
  (v : val)
  (e : expr)
  (A : type).


(** ** Definition of the logical relation. *)

Inductive val_or_expr : Type :=
| inj_val : val -> val_or_expr
| inj_expr : expr -> val_or_expr.

(** Convince Coq that our logical relation is well-defined. *)
Equations type_size (t : type) : nat :=
  type_size Int := 1;
  type_size (Fun A B) := type_size A + type_size B + 1.
Equations mut_measure (ve : val_or_expr) (t : type) : nat :=
  mut_measure (inj_expr e) t := 1 + type_size t;
  mut_measure (inj_val v) t := type_size t.

Equations type_interp (ve : val_or_expr) (t : type) : Prop by wf (mut_measure ve t) := {
  type_interp (inj_val v) Int =>
    exists z : Z, v = z ;
  type_interp (inj_val v) (A -> B) =>
    exists x e, v = LamV x e /\ closed empty (of_val v) /\
      forall v',
        type_interp (inj_val v') A ->
        type_interp (inj_expr (subst x (of_val v') e)) B;

  type_interp (inj_expr e) t =>
    exists v, big_step e v /\ type_interp (inj_val v) t
}.
Next Obligation.
  simp mut_measure. simp type_size. lia.
Qed.
Next Obligation.
  simp mut_measure. simp type_size.
  destruct A; simp mut_measure; simp type_size; lia.
Qed.

(** We derive the expression/value relation. *)
Notation sem_val_rel t v := (type_interp (inj_val v) t).
Notation sem_expr_rel t e := (type_interp (inj_expr e) t).

(** *** Semantic typing of contexts *)
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
  sem_val_rel A v -> closed empty (of_val v).
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
Proof. (* FILL IN HERE *) Admitted.

(** *** Compatibility lemmas *)

(** Lemma 19 *)
Lemma compat_int Gamma z : Gamma |= (LitInt z) : Int.
Proof. (* DONE IN CLASS *) Admitted.

(** Lemma 20 *)
Lemma compat_var Gamma x A :
  Gamma !! x = Some A ->
  Gamma |= (Var x) : A.
Proof. (* DONE IN CLASS *) Admitted.

(** Lemma 21 *)
Lemma compat_app Gamma e1 e2 A B :
  Gamma |= e1 : (A -> B) ->
  Gamma |= e2 : A ->
  Gamma |= (e1 e2) : B.
Proof. (* DONE IN CLASS *) Admitted.

(* Compatibility for [lam] unfortunately needs a very technical helper lemma. *)
Lemma lam_closed Gamma gamma x A e :
  closed (dom (<[x:=A]> Gamma)) e ->
  sem_ctx_rel Gamma gamma ->
  closed empty (lam: x, subst_map (delete x gamma) e)%E.
Proof.
  intros Hcl Hctxt. simpl. eapply closed_subst_map.
  - eapply closed_weaken; first done.
    rewrite dom_delete dom_insert (ctx_rel_dom Gamma gamma) //.
    intros y. destruct (decide (x = y)); set_solver.
  - eapply subst_closed_weaken, ctx_rel_closed; last done.
    + set_solver.
    + apply map_delete_subseteq.
Qed.

(** Lemma 22 *)
Lemma compat_lam Gamma x e A B :
  (<[ x := A ]> Gamma) |= e : B ->
  Gamma |= (Lam x e) : (A -> B).
Proof. (* DONE IN CLASS *) Admitted.

(** Omitted in the lecture notes *)
Lemma compat_add Gamma e1 e2 :
  Gamma |= e1 : Int ->
  Gamma |= e2 : Int ->
  Gamma |= (e1 + e2) : Int.
Proof. (* FILL IN HERE *) Admitted.

(** Theorem 23 *)
Theorem sem_soundness Gamma e A :
  (Gamma |- e : A)%ty ->
  Gamma |= e : A.
Proof. (* FILL IN HERE *) Admitted.

(** Corollary 24 *)
Corollary termination e A :
  (empty |- e : A)%ty ->
  exists v, big_step e v.
Proof. (* DONE IN CLASS *) Admitted.

(* In-class exercise:
- [type_safety] in types_class2.v
  (bonus exercise: complete [type_substitution])
- [val_inclusion], [compat_add] and [sem_soundness] above. *)
