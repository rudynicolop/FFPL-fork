From ffpl.lib Require Import prelude sets.
From ffpl.type_systems.stlc_extended Require Export lang.

(** Open and closed expressions.
In the lecture notes we formalize the "set of free variables" of a term.
For Coq it turns out to be sufficient, and easier, to instead define a predicate
that says whether a set [X] contains all free variables:
[is_closed X e] evaluates to [true] iff all free variables in [e] are contained in [X].
We define this as a functon that returns a [bool], i.e. this actually computes an
answer that is either [true] or [false]. *)
Fixpoint is_closed (X : gset string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x `elem` X)
  | Lam x e => is_closed ({[x]} `union` X) e
  | LitInt _ => true
  | App e1 e2
  | Plus e1 e2 => is_closed X e1 && is_closed X e2
  | Pair e1 e2 => is_closed X e1 && is_closed X e2
  | Proj1 e => is_closed X e
  | Proj2 e => is_closed X e
  end.

(** We can compute with this definition. *)
Compute (is_closed empty (LitInt 0)).
Compute (is_closed empty (Var "x")).
Compute (is_closed {["x"]} (Var "x")).

(** [closed X e] is the propositional version of [is_closed X e]:
[closed X e] has type [Prop], not [bool]. *)
Notation closed X e := (Is_true (is_closed X e)).

(** Defining it like this means we can do proofs "by computation". *)
Example lit_is_closed z : closed empty (LitInt z).
Proof. simpl. done. Qed.

(** We show some key properties of [closed].
We don't expect you to be able to do these proofs ([Is_true] can be
somewhat tricky to work with); we will provide all the results you need. *)
Lemma closed_weaken X Y e : closed X e -> subseteq X Y -> closed Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma closed_weaken_nil X e : closed empty e -> closed X e.
Proof. intros. by apply closed_weaken with empty, empty_subseteq. Qed.

Lemma subst_closed X e x es : closed X e -> ~(x `elem` X) -> subst x es e = e.
Proof.
  induction e in X |- *; simpl; rewrite ?bool_decide_spec ?andb_True; intros ??;
    repeat case_decide; simplify_eq; simpl; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_closed_nil e x es : closed empty e -> subst x es e = e.
Proof. intros. apply subst_closed with empty; done || set_solver. Qed.
