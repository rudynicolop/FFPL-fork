From ffpl.lib Require Import prelude.
From ffpl.type_systems.stlc Require Export lang.

(** Open and closed expressions.
[is_closed X e] evaluates to [true] iff all free variables in [e]
are contained in [X]. *)
Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x `elem` X)
  | Lam x e => is_closed (x :: X) e
  | LitInt _ => true
  | App e1 e2
  | Plus e1 e2 => is_closed X e1 && is_closed X e2
  end.

(** [closed X e] is the propositional version of [is_closed X e]:
[closed X e] has type [Prop], not [bool]. *)
Notation closed X e := (Is_true (is_closed X e)).

(** Defining it like this means we can do proofs "by computation". *)
Example lit_is_closed z : closed [] (LitInt z).
Proof. simpl. done. Qed.

(** We show some key properties of [closed].
We don't expect you to be able to do these proofs ([Is_true] can be
somewhat tricky to work with); we will provide all the results you need. *)
Lemma closed_weaken X Y e : closed X e -> subseteq X Y -> closed Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma closed_weaken_nil X e : closed [] e -> closed X e.
Proof. intros. by apply closed_weaken with [], list_subseteq_nil. Qed.

Lemma closed_subst X Y e x es :
  closed Y es -> closed (x :: X) e -> closed (X ++ Y) (subst x es e).
Proof.
  (** [induction ... in X |- *] is a short-hand for generalizing X in the
  induction hypothesis. *)
  induction e as [y|y e IH|e1 e2|n|e1 e2] in X |- *; simpl; intros Hc1 Hc2; eauto.
  - eapply bool_decide_unpack, elem_of_cons in Hc2 as [->|Hc2].
    + destruct decide; try congruence. eapply closed_weaken; eauto with set_solver.
    + destruct decide.
      * eapply closed_weaken; eauto with set_solver.
      * simpl. eapply bool_decide_pack. set_solver.
  - destruct decide as [Heq|].
    + eapply closed_weaken; eauto. set_solver.
    + rewrite app_comm_cons. eapply IH; eauto.
      eapply closed_weaken; eauto. set_solver.
  - eapply andb_True. eapply andb_True in Hc2 as [H1 H2].
    split; eauto.
  - eapply andb_True. eapply andb_True in Hc2 as [H1 H2].
    split; eauto.
Qed.

Lemma closed_subst_nil X e x es :
  closed [] es -> closed (x :: X) e -> closed X (subst x es e).
Proof.
  intros Hc1 Hc2. eapply closed_subst in Hc1; eauto.
  revert Hc1. rewrite right_id //.
Qed.

Lemma closed_do_subst' X e x es :
  closed [] es -> closed (x :: X) e -> closed X (subst x es e).
Proof. destruct x; eauto using closed_subst_nil. Qed.

Lemma subst_closed X e x es : closed X e -> ~(x `elem` X) -> subst x es e = e.
Proof.
  induction e in X |- *; simpl; rewrite ?bool_decide_spec ?andb_True; intros ??;
    repeat case_decide; simplify_eq; simpl; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_closed_nil e x es : closed [] e -> subst x es e = e.
Proof. intros. apply subst_closed with []; set_solver. Qed.
