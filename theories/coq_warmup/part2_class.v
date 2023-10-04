(** * Lecture 2: Introduction to Coq (part 2) *)
From ffpl.lib Require Import prelude.

(** ######################################################################### *)
(** * Introduction *)
(** ######################################################################### *)

(** ######################################################################### *)
(** * Coq tactics and searching for lemmas *)
(** ######################################################################### *)

(** ** Searching for lemmas *)

Search (nat -> nat -> Prop).

Print Nat.lt.
Print lt.

Search lt.

Search "pos" lt.
Search lt plus.
Search "<" "+".
Search (_ + _ < _ + _).
Search (?n + _ < ?n + _).

(** ** The [lia] tactic *)

Lemma lia_example_1 n m :
  n < 8 + 5*m ->
  m <= 3 - 4*n ->
  m < 4 /\ n < 8.
Proof. (* DONE IN CLASS *) Admitted.

Lemma lia_example_2 (f : nat -> bool) i j :
  (forall n m, f (n + m) = f n && f m) ->
  f ((i + j) * 10) = f (i + (2 * j)) && f (j * 8 + i * 9).
Proof. (* DONE IN CLASS *) Admitted.

(** ** The [subst], [congruence], and [simplify_eq] tactics *)

Lemma subst_example_1 (f : nat -> nat) a b :
  a = b ->
  f a = 1 ->
  f b = 0 ->
  0 = 1.
Proof. (* DONE IN CLASS *) Admitted.
Lemma subst_example_2 (f : nat -> nat) a b :
  a = 1 ->
  b = 2 ->
  a + 2 = b + 1.
Proof. (* DONE IN CLASS *) Admitted.

Lemma congruence_example_1 a b c :
  (S a, S a) = (S b, S c) -> b = c.
Proof. (* DONE IN CLASS *) Admitted.

Lemma congruence_example_2 (f : nat -> nat) a b :
  a = b ->
  f a = 1 ->
  f b = 0 ->
  0 = 1.
Proof. (* DONE IN CLASS *) Admitted.

Lemma simplify_eq_example_1 a b c :
  (S a, S a) = (S b, S c) ->
  b + c = 2 * b.
Proof. (* DONE IN CLASS *) Admitted.

(** ** The [done] tactic *)

Lemma plus_0_l n :
  0 + n = n.
Proof. (* DONE IN CLASS *) Admitted.

Lemma S_ne_O n :
  S n != 0.
Proof. (* DONE IN CLASS *) Admitted.

Lemma S_pred n : n != 0 -> n = S (pred n).
Proof. (* DONE IN CLASS *) Admitted.

Lemma xorb_false_inv b1 b2 :
  xorb b1 b2 = false -> b1 = b2.
Proof. (* DONE IN CLASS *) Admitted.

Lemma plus_0_inv n m :
  n + m = 0 -> n = 0 /\ m = 0.
Proof. (* DONE IN CLASS *) Admitted.

Lemma done_example_1 n :
  n = 1 -> 1 = n.
Proof. (* DONE IN CLASS *) Admitted.

Lemma done_example_2 (n m : nat) :
  n = m -> n != m -> 1 = 2.
Proof. (* DONE IN CLASS *) Admitted.

Lemma done_example_3 n :
  n != n -> n = 10.
Proof. (* DONE IN CLASS *) Admitted.

Lemma done_example_4 n :
  n != 1 -> 1 != n.
Proof. (* DONE IN CLASS *) Admitted.

(** ** [simpl] and [done] during [rewrite] *)

Lemma plus_0_r n :
  n + 0 = n.
Proof. (* DONE IN CLASS *) Admitted.

(** ** Destruct with equations *)

Lemma destruct_eqn_example (f : bool -> bool) :
  exists b, f b = b \/ f (f b) = b.
Proof. (* DONE IN CLASS *) Admitted.

(** ** [apply] in hypotheses *)

Lemma plus_mono_l n1 n2 k :
  n1 + k <= n2 + k -> n1 <= n2.
Proof. (* DONE IN CLASS *) Admitted.

(** ######################################################################### *)
(** * Exercises about Coq tactics and searching for lemmas *)
(** ######################################################################### *)

Lemma tactics_exercise_1 (m n : nat) :
  m <= n -> m > 10 -> n < 8 -> False.
Proof. (* FILL IN HERE *) Admitted.

Lemma tactics_exercise_2 (n : nat) :
  4 <= n -> 2 <= Nat.sqrt n.
Proof. (* FILL IN HERE *) Admitted.

Lemma tactics_exercise_3 (P : nat -> Prop) (n : nat) :
  (forall m, P (2*m + 1)) ->
  P (n + 1 + n).
Proof. (* FILL IN HERE *) Admitted.

Lemma tactics_exercise_4 (f : bool -> bool) :
  f true != f false ->
  (forall b, f b = b) \/ (forall b, f b != b).
Proof. (* FILL IN HERE *) Admitted.

(** ######################################################################### *)
(** * Compact proof scripts *)
(** ######################################################################### *)

(** ** Tacticals / tactic combinators *)

Lemma plus_S_r n m :
  n + S m = S (n + m).
Proof. (* DONE IN CLASS *) Admitted.

Definition f (n : nat) : nat :=
  match n with
  | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2
  | n => n
  end.

Lemma f_twice n :
  f (f n) = n.
Proof. (* DONE IN CLASS *) Admitted.

(** ** Introduction patterns *)

Lemma intro_pattern_example_1 (P1 P2 P3 : Prop) :
  P1 /\ (P2 \/ P3) ->
  (P1 /\ P2) \/ (P1 /\ P3).
Proof. (* DONE IN CLASS *) Admitted.

Lemma intro_pattern_example_2 (P1 P2 P3 : nat -> Prop) :
  (exists x y, P1 x /\ P2 x /\ P3 y) ->
  (exists x, P1 x /\ P2 x) /\ (exists y, P3 y).
Proof. (* DONE IN CLASS *) Admitted.

Lemma intro_pattern_example_3 (P : Prop) :
  P \/ False ->
  P.
Proof. (* DONE IN CLASS *) Admitted.

Lemma intro_pattern_example_4 (P Q : nat -> Prop) :
  (exists nm : nat * nat, P (fst nm) /\ Q (snd nm)) ->
  exists n m : nat, P n /\ Q m.
Proof. (* DONE IN CLASS *) Admitted.

Lemma intro_pattern_example_5 (P : nat -> Prop) n :
  (exists m, n = S m /\ P m) ->
  0 < n /\ P (pred n).
Proof. (* DONE IN CLASS *) Admitted.

Lemma intro_pattern_example_6 (P : nat -> Prop) n :
  (exists m, S n = S m /\ P m) ->
  P n.
Proof. (* DONE IN CLASS *) Admitted.

Lemma intro_pattern_example_7 n1 n2 k :
  n1 + k <= n2 + k -> n1 <= n2.
Proof. (* DONE IN CLASS *) Admitted.

(** ** Evars ("existential variables") *)

Lemma evar_demo_1 (P Q : nat -> Prop) (m n : nat) :
  (forall n m, P m -> Q n) ->
  P (m * 1024 + n * 256 + 64) -> Q (m * 64 + n * 256 + 1024).
Proof. (* DONE IN CLASS *) Admitted.

Lemma le_mult_2 m : m <= 2*m.
Proof. lia. Qed.
Lemma evar_demo_2 m :
  Nat.sqrt m <= 2 * Nat.sqrt (2 * m).
Proof. (* DONE IN CLASS *) Admitted.

(** ######################################################################### *)
(** * Exercises about compact proof scripts *)
(** ######################################################################### *)

Lemma compact_exercise_1 (f : bool -> bool) (b : bool) :
  f (f (f b)) = f b.
Proof. (* FILL IN HERE *) Admitted.

Lemma compact_exercise_2 n :
  (exists m, (m < 2 /\ S n = S m) \/ (m < 3 /\ n < m)) ->
  n < 2.
Proof. (* FILL IN HERE *) Admitted.

(** Do this exercise twice: once with evars, and once with [%lemma] patterns. *)
Lemma compact_exercise_3 (P : nat -> Prop) n :
  (forall m1 m2, P (m1 + m2) -> P m1) ->
  P (n + 3 + n + 8) -> P n.
Proof. (* FILL IN HERE *) Admitted.

Lemma compact_exercise_4 n1 n2 n3 :
  n1 + n2 = n1 + n3 -> n2 = n3.
Proof. (* FILL IN HERE *) Admitted.

Lemma compact_exercise_5 (f : bool -> bool) :
  f true != f false ->
  (forall b, f b = b) \/ (forall b, f b != b).
Proof. (* FILL IN HERE *) Admitted.

(** ######################################################################### *)
(** * Inductive relations *)
(** ######################################################################### *)

Inductive even : nat -> Prop :=
| Even0 : even 0
| Even2 : forall n, even n -> even (2 + n).

Lemma even_4 : even 4.
Proof. (* DONE IN CLASS *) Admitted.

Lemma even_mul2 n :
  even n -> exists k, n = 2*k.
Proof. (* DONE IN CLASS *) Admitted.

Lemma not_even_1 : ~even 1.
Proof. (* DONE IN CLASS *) Admitted.

Lemma mul2_even k n :
  n = 2*k -> even n.
Proof. (* DONE IN CLASS *) Admitted.
