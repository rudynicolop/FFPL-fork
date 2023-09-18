From stdpp Require Import binders gmap.
From ffpl.lib Require Export prelude.

(** Useful lemmas not found in std++ or the Coq Stdlib. *)
Lemma if_iff P Q R S:
  (P <-> Q) ->
  (R <-> S) ->
  ((P -> R) <-> (Q -> S)).
Proof.
  naive_solver.
Qed.

Lemma if_iff' P R S :
  (P -> R <-> S) -> (P -> R) <-> (P -> S).
Proof. tauto. Qed.
Lemma and_iff' (P R S : Prop) :
  (P -> R <-> S) -> (P /\ R) <-> (P /\ S).
Proof. tauto. Qed.
Lemma and_iff (P Q R S : Prop) :
  (P <-> Q) -> ((P \/ Q) -> R <-> S) -> (P /\ R) <-> (Q /\ S).
Proof. tauto. Qed.

Lemma list_subseteq_cons {X} (A B : list X) x : A `subseteq` B -> x :: A `subseteq` x :: B.
Proof. intros Hincl. intros y. rewrite !elem_of_cons. naive_solver. Qed.
Lemma list_subseteq_cons_binder A B x : A `subseteq` B -> x :b: A `subseteq` x :b: B.
Proof. destruct x; [done|]. apply list_subseteq_cons. Qed.
Lemma list_subseteq_cons_l {X} (A B : list X) x : A `subseteq` x :: B -> x :: A `subseteq` x :: B.
Proof. 
  intros Hincl. intros y. rewrite elem_of_cons. intros [-> | ?]. 
  - left.
  - apply Hincl. naive_solver. 
Qed.

Lemma list_subseteq_cons_elem {X} (A B : list X) x :
  x `elem` B -> A `subseteq` B -> (x :: A) `subseteq` B.
Proof.
  intros Hel Hincl.
  intros a [-> | ?]%elem_of_cons; [done|].
  by apply Hincl.
Qed.

Lemma elements_subseteq `{EqDecision A} `{Countable A} (X Y : gset A):
  X `subseteq` Y -> elements X `subseteq` elements Y.
Proof.
  rewrite elem_of_subseteq.
  intros Ha a. rewrite !elem_of_elements.
  apply Ha.
Qed.
Lemma list_subseteq_cons_r {X} (A B : list X) x :
  A `subseteq` B -> A `subseteq` (x :: B).
Proof.
  intros Hincl. trans B; [done|].
  intros b Hel. apply elem_of_cons; by right.
Qed.
