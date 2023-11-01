From stdpp Require Import prelude.
From ffpl.lib Require Import prelude.
From ffpl.lib Require Export maps.
From ffpl.type_systems.stlc_extended_sol Require Import lang notation closed.

(** * Parallel substitution *)

(** This is the parallel substitution operation. We represent a substitution map
as a finite map [xs]. We use maps of [expr] to be able to reuse [closed]. *)
Fixpoint subst_map (xs : gmap string expr) (e : expr) : expr :=
  match e with
  | LitInt n => LitInt n
  | Var y => match xs !! y with Some es => es | _ =>  Var y end
  | App e1 e2 => App (subst_map xs e1) (subst_map xs e2)
  | Lam x e => Lam x (subst_map (delete x xs) e)
  | Plus e1 e2 => Plus (subst_map xs e1) (subst_map xs e2)
  | Pair e1 e2 => Pair (subst_map xs e1) (subst_map xs e2)
  | Proj1 e => Proj1 (subst_map xs e)
  | Proj2 e => Proj2 (subst_map xs e)
  end.

(** We lift the notion of closedness [closed] to substitution maps. *)
Definition subst_closed (X : gset string) (map : gmap string expr) :=
  forall x e, map !! x = Some e -> closed X e.

(** Some lemmas about these definitions. We don't expect you to be able to do
these proofs; we will provide all the results you need. *)

Lemma subst_map_empty e :
  subst_map empty e = e.
Proof.
  induction e; simpl; f_equal; [|by eauto..].
  by rewrite !delete_empty.
Qed.

Lemma subst_closed_weaken X Y map1 map2 :
  Y `subseteq` X -> map1 `subseteq` map2 -> subst_closed Y map2 -> subst_closed X map1.
Proof.
  intros Hsub1 Hsub2 Hclosed2 x e Hl.
  eapply closed_weaken. 1:eapply Hclosed2, map_subseteq_spec; done. done.
Qed.

(** Lemma about the interaction with "normal" substitution. *)
Lemma subst_subst_map x es gamma e :
  subst_closed empty gamma ->
  subst x es (subst_map (delete x gamma) e) =
  subst_map (<[x:=es]> gamma) e.
Proof.
  revert gamma es x; induction e; intros gamma v0 xx Hclosed; simpl;
  try (f_equal; eauto).
  - destruct (decide (xx=x)) as [->|Hne].
    + rewrite lookup_delete_eq // lookup_insert_eq //. simpl.
      rewrite decide_True //.
    + rewrite lookup_delete_ne // lookup_insert_ne //.
      destruct (_ !! x) as [rr|] eqn:Helem.
      * apply Hclosed in Helem.
        by apply subst_closed_nil.
      * simpl. rewrite decide_False //.
  - case_decide.
    + simplify_eq. rewrite delete_idemp delete_insert_delete. done.
    + rewrite delete_insert_ne //. rewrite delete_commute. apply IHe.
      eapply subst_closed_weaken; [done| |done].
      apply map_delete_subseteq.
Qed.

(** Lemma about when the result of [subst_map] is closed:
for [subst_map gamma e] to be closed under X, we need [gamma] itself to be
closed under [X], and [e] to be closed under [X] plus everything defined in
[gamma]. In other words, [subst_map gamma] removes [dom gamma] from the set of
free variables of [e], if [gamma] is itself sufficiently closed. *)
Lemma closed_subst_map X gamma e:
  closed (X `union` dom gamma) e ->
  subst_closed X gamma ->
  closed X (subst_map gamma e).
Proof.
  induction e in X, gamma |-*; simpl.
  - intros Hel%bool_decide_unpack Hcl.
    destruct (gamma !! x) eqn:EQ.
    + by eapply Hcl.
    + simpl. apply bool_decide_pack.
      apply not_elem_of_dom in EQ. set_solver.
  - intros Hcl Hcl'.
    eapply IHe.
    2:{ eapply subst_closed_weaken; last done. 1:set_solver.
        apply map_delete_subseteq. }
    eapply closed_weaken; first done.
    rewrite dom_delete.
    intros y. destruct (decide (x = y)); set_solver.
  - rewrite !andb_True. intros [H1 H2] Hcl. split; eauto.
  - auto.
  - rewrite !andb_True. intros [H1 H2] Hcl. split; eauto.
  - rewrite !andb_True. intros [H1 H2] Hcl. split; eauto.
  - eauto.
  - eauto.
Qed.
