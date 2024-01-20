(** * Lecture 1: Introduction to Coq (part 1) *)
From ffpl.lib Require Import prelude.

(** ######################################################################### *)
(** * Introduction *)
(** ######################################################################### *)

(** ######################################################################### *)
(** * Definition of the natural numbers *)
(** ######################################################################### *)

Module nat_defs.

  Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.

  Fixpoint plus (n1 n2 : nat) : nat :=
    match n1 with
    | O => n2
    | S n1' => S (plus n1' n2)
    end.

  Fail Fixpoint foo (n : nat) := S (foo n).
  Fail Fixpoint bar (n : nat) := S (bar (S n)).

  Fixpoint mult (n1 n2 : nat) : nat :=
    match n1 with
    | O => O
    | S n1' => plus n2 (mult n1' n2)
    end.

  Definition pred (n : nat) : nat :=
    match n with
    | S n => n
    | O => O
    end.

  Compute (plus (S (S O)) (S (S (S (S O))))).
  Compute (mult (S (S O)) (S (S (S (S O))))).
  Compute ((fun x => plus x (mult x (S (S x)))) (S (S O))).

  Check plus.
  Check (plus (S (S O))).
  Check (fun x => plus x (mult x (S (S x)))).

  Infix "+" := plus.
  Infix "*" := mult.

  Check (fun x => x + x * S (S x)).
End nat_defs.

Compute (2 + 4).
Compute (2 + S (S (S (S O)))).
Compute (2 * 4).
Compute ((fun x => x + (x * (S (S x)))) 2).

(** ######################################################################### *)
(** * Proofs about the natural numbers *)
(** ######################################################################### *)

Lemma plus_0_l n :
  0 + n = n.
Proof. reflexivity. Qed.

Lemma O_or_S n :
  n = 0 \/ n = S (pred n).
Proof. (* DONE IN CLASS *) Admitted.

Lemma plus_O_O n m :
  n = 0 -> m = 0 -> n + m = 0.
Proof. (* DONE IN CLASS *) Admitted.

Lemma S_ne_O n :
  S n <> 0.
Proof. (* DONE IN CLASS *) Admitted.

Lemma S_pred n : n <> 0 -> n = S (pred n).
Proof. (* DONE IN CLASS *) Admitted.

Lemma plus_0_inv n m :
  n + m = 0 -> n = 0 /\ m = 0.
Proof. (* DONE IN CLASS *) Admitted.

Lemma plus_0_iff n m :
  n + m = 0 <-> n = 0 /\ m = 0.
Proof. (* DONE IN CLASS *) Admitted.

Lemma plus_ne_0_iff n m :
  n + m <> 0 <-> n <> 0 \/ m <> 0.
Proof. (* DONE IN CLASS *) Admitted.

Lemma plus_0_r n :
  n + 0 = n.
Proof. (* DONE IN CLASS *) Admitted.

Lemma plus_S_r n1 n2 :
  n1 + S n2 = S (n1 + n2).
Proof. (* DONE IN CLASS *) Admitted.

Lemma plus_assoc n1 n2 n3 :
  n1 + (n2 + n3) = (n1 + n2) + n3.
Proof. (* DONE IN CLASS *) Admitted.

Lemma plus_comm n1 n2 :
  n1 + n2 = n2 + n1.
Proof. (* DONE IN CLASS *) Admitted.

Lemma plus_rearrange n m p q :
  (n + m) + p + q = (m + n) + (p + q).
Proof. (* DONE IN CLASS *) Admitted.

Lemma plus_inj_l n1 n2 n3 :
  n1 + n2 = n1 + n3 -> n2 = n3.
Proof. (* DONE IN CLASS *) Admitted.

Lemma double_inj n m :
  n + n = m + m -> n = m.
Proof. (* DONE IN CLASS *) Admitted.

(** ######################################################################### *)
(** * Exercises about natural numbers *)
(** ######################################################################### *)

Lemma mult_0_inv n m :
  n * m = 0 -> n = 0 \/ m = 0.
Proof. (* FILL IN HERE *) Admitted.

Lemma mult_0_l n :
  0 * n = 0.
Proof. (* FILL IN HERE *) Admitted.

Lemma mult_0_r n :
  n * 0 = 0.
Proof. (* FILL IN HERE *) Admitted.

Lemma plus_swap n1 n2 n3 :
  n1 + (n2 + n3) = n2 + (n1 + n3).
Proof. (* FILL IN HERE *) Admitted.

Lemma mult_S_r n1 n2 :
  n1 * S n2 = n1 + n1 * n2.
Proof. (* FILL IN HERE *) Admitted.

Lemma mult_comm n1 n2 :
  n1 * n2 = n2 * n1.
Proof. (* FILL IN HERE *) Admitted.

Lemma plus_mult_distr_l n1 n2 n3 :
  (n1 + n2) * n3 = n1 * n3 + n2 * n3.
Proof. (* FILL IN HERE *) Admitted.

Lemma mult_assoc n1 n2 n3 :
  n1 * (n2 * n3) = (n1 * n2) * n3.
Proof. (* FILL IN HERE *) Admitted.

Lemma plus_inj_r n1 n2 n3 :
  n1 + n3 = n2 + n3 -> n1 = n2.
Proof. (* FILL IN HERE *) Admitted.

Lemma mult_plus_same_inj n m p :
  n * (n + p) = m * (m + p) -> m = n.
Proof. (* FILL IN HERE *) Admitted.

Lemma square_inj n m :
  n * n = m * m -> m = n.
Proof. (* FILL IN HERE *) Admitted.

(** ######################################################################### *)
(** * Definition of the Booleans *)
(** ######################################################################### *)

Module bool_defs.
  Inductive bool :=
    | true : bool
    | false : bool.

  Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

  Definition andb (b1 b2 : bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.

  Definition orb (b1 b2 : bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.

  Definition xorb (b1 b2 : bool) :  bool :=
    match b1, b2 with
    | true, false => true
    | false, true => true
    | _, _ => false
    end.

  Infix "&&" := andb.
  Infix "||" := orb.
End bool_defs.

(** ######################################################################### *)
(** * Theorems and proofs about the Booleans *)
(** ######################################################################### *)

Lemma andb_true_l b : true && b = b.
Proof. (* DONE IN CLASS *) Admitted.

Lemma andb_true_r b : b && true = b.
Proof. (* DONE IN CLASS *) Admitted.

Lemma andb_comm b1 b2 : b1 && b2 = b2 && b1.
Proof. (* DONE IN CLASS *) Admitted.

Lemma xorb_inj_l b1 b2 b3 : xorb b1 b2 = xorb b1 b3 -> b2 = b3.
Proof. (* DONE IN CLASS *) Admitted.

Lemma negb_andb b1 b2 :
  negb (b1 && b2) = negb b1 || negb b2.
Proof. (* DONE IN CLASS *) Admitted.

Lemma orb_andb_distr b1 b2 b3 :
  b1 && (b2 || b3) = (b1 && b2) || (b1 && b3).
Proof. (* DONE IN CLASS *) Admitted.

Lemma andb_assoc b1 b2 b3 : b1 && (b2 && b3) = (b1 && b2) && b3.
Proof. (* DONE IN CLASS *) Admitted.

(** ########################################################################## *)
(** * Exercises about the Booleans *)
(** ########################################################################## *)

Lemma xorb_false_l b :
  xorb false b = b.
Proof. (* FILL IN HERE *) Admitted.

Lemma xorb_false_inv b1 b2 : xorb b1 b2 = false -> b1 = b2.
Proof. (* FILL IN HERE *) Admitted.

Lemma xorb_negb_l b1 b2 :
  xorb (negb b1) b2 = negb (xorb b1 b2).
Proof. (* FILL IN HERE *) Admitted.

Lemma negb_involutive b :
  negb (negb b) = b.
Proof. (* FILL IN HERE *) Admitted.

Lemma negb_inv b1 b2 :
  negb b1 = negb b2 <-> b1 = b2.
Proof. (* FILL IN HERE *) Admitted.

Fixpoint oddb (n : nat) : bool :=
  match n with
  | O => false
  | S n' => negb (oddb n')
  end.

Definition evenb (n : nat) : bool :=
  negb (oddb n).

Lemma oddb_mult_2 n :
  oddb (n * 2) = false.
Proof. (* FILL IN HERE *) Admitted.

Lemma oddb_plus n m :
  oddb (n + m) = xorb (oddb n) (oddb m).
Proof. (* FILL IN HERE *) Admitted.
Definition f (b1 b2 : bool) : bool.
  (* FILL IN DEFINITION HERE (not a proof script) *) Admitted.

Lemma evenb_plus n m :
  evenb (n + m) = f (evenb n) (evenb m).
Proof. (* FILL IN HERE *) Admitted.

Lemma mul_oddb n m :
  oddb (n * m) = oddb n && oddb m.
Proof. (* FILL IN HERE *) Admitted.
Lemma evenb_mul n m :
  evenb (n * m) = evenb n || evenb m.
Proof. (* FILL IN HERE *) Admitted.

(** ########################################################################## *)
(** * Final exercise *)
(** ########################################################################## *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n => factorial n * S n
  end.

Fixpoint factorial_tailrec_go (n acc : nat) : nat :=
  match n with
  | O => acc
  | S n => factorial_tailrec_go n (acc * S n)
  end.

Definition factorial_tailrec (n : nat) : nat :=
  factorial_tailrec_go n 1.

Lemma factorial_tailrec_correct n :
  factorial_tailrec n = factorial n.
Proof. (* FILL IN HERE *) Admitted.
