From stdpp Require Export sets countable gmap.
From ffpl.lib Require Export prelude.

(** * Finite sets *)
(** This file provides lemmas on finite sets [gset].
  The stdpp library provides a definitions and lemmas on finite sets [gset], but states lemmas axiomatically in terms of the [FinSet] typeclass, which may make them hard to read for novice users of stdpp.
  We therefore instantiate the most important lemmas specifically for [gset] to make the statements easier to comprehend.

  The most important operations are:
   - the empty set empty defines a set with no elements
   - the singleton set {[ x ]} defines a singleton set
   - the union operation X `union` Y represents the union of two sets
   - the intersection operation X `intersection` Y represents the union of two sets
   - the difference operation X `difference` Y represents the difference (Note: this is NOT a backslash. Pay attention to use the right unicode symbol.)
   - the subset predicate X `subseteq` Y states that X is a subset of Y
   - the element predicate x `elem` X states that x is an element of X
   - the elements operation elements X gives a duplicate-free list of elements of X

  stdpp's sets satisfy extensional Leibniz equality -- that is, two sets X and Y are equal (X = Y) iff they contain the same elements.
 *)

Section sets.
  Context {K} {A : Type} `{Countable K}.

  Definition gset := gset.
  #[global]
  Arguments gset _ {_ _}.

  Implicit Types (X Y : gset K).

  Lemma elem_of_singleton x y : x `elem` ({[ y ]} : gset K) <-> x = y.
  Proof. apply elem_of_singleton. Qed.
  Lemma elem_of_union X Y x : x `elem` (X `union` Y) <-> x `elem` X \/ x `elem` Y.
  Proof. apply elem_of_union. Qed.
  Lemma elem_of_intersection X Y x : x `elem` (X `intersection` Y) <-> x `elem` X /\ x `elem` Y.
  Proof. apply elem_of_intersection. Qed.
  Lemma elem_of_difference X Y x : x `elem` (X `difference` Y) <-> x `elem` X /\ ~(x `elem` Y).
  Proof. apply elem_of_difference. Qed.

  Lemma elem_of_elements X x : x `elem` elements X <-> x `elem` X.
  Proof. apply elem_of_elements. Qed.
  Lemma elements_empty : elements (empty : gset K) = [].
  Proof. apply elements_empty. Qed.
  Lemma elements_empty_iff X : elements X = [] <-> X = empty.
  Proof. rewrite elements_empty_iff. by rewrite leibniz_equiv_iff. Qed.

  Lemma set_equiv X Y : X = Y <-> forall x, x `elem` X <-> x `elem` Y.
  Proof. set_solver. Qed.
  Lemma set_equiv_subseteq X Y : X = Y <-> X `subseteq` Y /\ Y `subseteq` X.
  Proof. set_solver. Qed.

  (** Subset relation *)
  Lemma subseteq_union X Y : X `subseteq` Y <-> X `union` Y = Y.
  Proof. set_solver. Qed.
  Lemma subseteq_union_1 X Y : X `subseteq` Y -> X `union` Y = Y.
  Proof. by rewrite subseteq_union. Qed.
  Lemma subseteq_union_2 X Y : X `union` Y = Y -> X `subseteq` Y.
  Proof. by rewrite subseteq_union. Qed.

  Lemma union_subseteq_l X Y : X `subseteq` X `union` Y.
  Proof. set_solver. Qed.
  Lemma union_subseteq_l' X X' Y : X `subseteq` X' -> X `subseteq` (X' `union` Y).
  Proof. set_solver. Qed.
  Lemma union_subseteq_r X Y : Y `subseteq` X `union` Y.
  Proof. set_solver. Qed.
  Lemma union_subseteq_r' X Y Y' : Y `subseteq` Y' -> Y `subseteq` (X `union` Y').
  Proof. set_solver. Qed.
  Lemma union_least X Y Z : X `subseteq` Z -> Y `subseteq` Z -> (X `union` Y) `subseteq` Z.
  Proof. set_solver. Qed.

  Lemma elem_of_subseteq X Y : X `subseteq` Y <-> forall x, x `elem` X -> x `elem` Y.
  Proof. done. Qed.
  Lemma elem_of_weaken x X Y : x `elem` X -> X `subseteq` Y -> x `elem` Y.
  Proof. set_solver. Qed.

  Lemma not_elem_of_weaken x X Y : ~(x `elem` Y) -> X `subseteq` Y -> ~(x `elem` X).
  Proof. set_solver. Qed.

  (** Union *)
  Lemma union_subseteq X Y Z : X `union` Y `subseteq` Z <-> X `subseteq` Z /\ Y `subseteq` Z.
  Proof. set_solver. Qed.
  Lemma not_elem_of_union x X Y : ~(x `elem` (X `union` Y)) <-> ~(x `elem` X) /\ ~(x `elem` Y).
  Proof. set_solver. Qed.
  Lemma elem_of_union_l x X Y : x `elem` X -> x `elem` X `union` Y.
  Proof. set_solver. Qed.
  Lemma elem_of_union_r x X Y : x `elem` Y -> x `elem` X `union` Y.
  Proof. set_solver. Qed.
  Lemma union_mono_l X Y1 Y2 : Y1 `subseteq` Y2 -> (X `union` Y1) `subseteq` (X `union` Y2).
  Proof. set_solver. Qed.
  Lemma union_mono_r X1 X2 Y : X1 `subseteq` X2 -> (X1 `union` Y) `subseteq` (X2 `union` Y).
  Proof. set_solver. Qed.
  Lemma union_mono X1 X2 Y1 Y2 : X1 `subseteq` X2 -> Y1 `subseteq` Y2 -> (X1 `union` Y1) `subseteq` (X2 `union` Y2).
  Proof. set_solver. Qed.

  Lemma empty_union X Y : X `union` Y = empty <-> X = empty /\ Y = empty.
  Proof. set_solver. Qed.

  (** Empty *)
  Lemma empty_subseteq X : empty `subseteq` X.
  Proof. set_solver. Qed.
  Lemma elem_of_equiv_empty X : X = empty <-> forall x, ~(x `elem` X).
  Proof. set_solver. Qed.
  Lemma elem_of_empty x : x `elem` (empty : gset K) <-> False.
  Proof. set_solver. Qed.
  Lemma equiv_empty X : X `subseteq` empty -> X = empty.
  Proof. set_solver. Qed.
  Lemma union_positive_l X Y : X `union` Y = empty -> X = empty.
  Proof. set_solver. Qed.
  Lemma union_positive_l_alt X Y : X != empty -> X `union` Y != empty.
  Proof. set_solver. Qed.
  Lemma non_empty_inhabited x X : x `elem` X -> X != empty.
  Proof. set_solver. Qed.

  (** Singleton *)
  Lemma elem_of_singleton_1 x y : x `elem` ({[y]} : gset K) -> x = y.
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma elem_of_singleton_2 x y : x = y -> x `elem` ({[y]} : gset K).
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma elem_of_subseteq_singleton x X : x `elem` X <-> {[ x ]} `subseteq` X.
  Proof. set_solver. Qed.
  Lemma non_empty_singleton x : ({[ x ]} : gset K) != empty.
  Proof. set_solver. Qed.
  Lemma not_elem_of_singleton x y : ~(x `elem` ({[ y ]} : gset K)) <-> x != y.
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma not_elem_of_singleton_1 x y : ~(x `elem` ({[ y ]} : gset K)) -> x != y.
  Proof. apply not_elem_of_singleton. Qed.
  Lemma not_elem_of_singleton_2 x y : x != y -> ~(x `elem` ({[ y ]} : gset K)).
  Proof. apply not_elem_of_singleton. Qed.

  Lemma singleton_subseteq_l x X : {[ x ]} `subseteq` X <-> x `elem` X.
  Proof. set_solver. Qed.
  Lemma singleton_subseteq x y : ({[ x ]} : gset K) `subseteq` {[ y ]} <-> x = y.
  Proof. set_solver. Qed.

End sets.
