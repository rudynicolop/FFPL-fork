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
(** * Exercises about searching for lemmas *)
(** ######################################################################### *)

Lemma search_exercise_1 (n : nat) :
  4 <= n -> 2 <= Nat.sqrt n.
Proof. (* FILL IN HERE *) Admitted.

Lemma search_exercise_2 a :
  0 < a ->
  1 + Nat.log2 a <= a.
Proof. (* FILL IN HERE *) Admitted.

(** ######################################################################### *)
(** * Exercises about Coq tactics  *)
(** ######################################################################### *)

Lemma tactics_exercise_1 (m n : nat) :
  m <= n -> m > 10 -> n < 8 -> False.
Proof. (* FILL IN HERE *) Admitted.

Lemma tactics_exercise_2 (P : nat -> Prop) (n : nat) :
  (forall m, P (2*m + 1)) ->
  P (n + 1 + n).
Proof. (* FILL IN HERE *) Admitted.

Lemma tactics_exercise_3 (f : bool -> bool) :
  f true != f false ->
  (forall b, f b = b) \/ (forall b, f b != b).
Proof. (* FILL IN HERE *) Admitted.

Lemma eq_exercise_1 a b c d :
  S a = S b ->
  b != c + c ->
  S c = S d ->
  b != d * 2.
Proof. (* FILL IN HERE *) Admitted.

Lemma eq_exercise_2 (f : nat -> nat) a :
  f (f a) = f a ->
  f (f (f a)) = f a.
Proof. (* FILL IN HERE *) Admitted.

Fixpoint power_2 (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => 2 * power_2 n'
  end.

Lemma power_2_pos n :
  0 < power_2 n.
Proof. (* FILL IN HERE *) Admitted.
Lemma log2_power_2_inv n :
  log2 (power_2 n) = n.
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

Lemma intro_pattern_example_7 a b c :
  (S a, S a) = (S b, S c) ->
  b + c = 2 * b.
Proof. (* DONE IN CLASS *) Admitted.

Lemma intro_pattern_example_8 n1 n2 k :
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

(* Do this proof twice: once with evars, and once with [%lemma] patterns. *)
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

(* Hint: Evars will be useful in the following exercise. *)

Lemma compact_exercise_6 {T} (P Q : T -> Prop) (R : Prop) :
  (forall x y, P x -> Q y -> R) ->
  (exists x, P x) -> (exists y, Q y) -> R.
Proof. (* FILL IN HERE *) Admitted.

(** ######################################################################### *)
(** * Inductive predicates *)
(** ######################################################################### *)
Inductive even : nat -> Prop :=
| Even0 : even 0
| Even2 : forall n', even n' -> even (2 + n').
Check Even0.
Check Even2.
Lemma even_4 : even 4.
Proof. (* DONE IN CLASS *) Admitted.
Lemma even_n n : even n -> n = 0 \/ (exists n', n = S (S n')).
Proof.
  intros [|n' Heven'].
  - left. done.
  - right. exists n'. done.
Qed.

Lemma even_mul2 n :
  even n -> exists k, n = 2*k.
Proof. (* DONE IN CLASS *) Admitted.

Lemma not_even_1 : ~even 1.
Proof. (* DONE IN CLASS *) Admitted.

(** ######################################################################### *)
(** * Exercises about inductive predicates *)
(** ######################################################################### *)

Lemma mul2_even k n :
  n = 2*k -> even n.
Proof. (* FILL IN HERE *) Admitted.

(* A number is odd if it is ... *)
Inductive odd : nat -> Prop :=
(* ... 1 or ... *)
| Odd1 : odd 1
(* ... 2 + an odd number. *)
| Odd2 : forall n, odd n -> odd (2 + n).

Lemma even_plus_odd n m :
  even n -> odd m -> odd (n + m).
Proof. (* FILL IN HERE *) Admitted.

Lemma never_both_even_odd n :
  even n -> ~ odd n.
Proof. (* FILL IN HERE *) Admitted.

(* Hint: To prove this lemma, you may find it useful to formulate certain
helper lemmas along the way. *)
Lemma even_or_odd n :
  even n \/ odd n.
Proof. (* FILL IN HERE *) Admitted.

(** ######################################################################### *)
(** * The list and option data types *)
(** ######################################################################### *)

Module list_defs.
  Inductive list (A : Type) :=
    | nil : list A
    | cons : A -> list A -> list A.

  About nil.
  About cons.

  Check cons nat 10 (cons nat 11 (nil nat)).

  Arguments nil {_}.
  Arguments cons {_}.

  Check cons 10 (cons 11 nil).

  Check nil. (* [nil : list ?A] *)
  Check (@nil nat). (* [nil : list nat] *)

  Infix "::" := cons.
  Notation "[]" := nil.
  Notation "[ x ]" := (cons x nil).
  Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).

  Check [10; 11].

  Fixpoint length {A} (xs : list A) : nat :=
    match xs with
    | [] => 0
    | x :: xs => S (length xs)
    end.

  Compute length [10; 11].

  Fixpoint app {A} (xs1 xs2 : list A) : list A :=
    match xs1 with
    | [] => xs2
    | x :: xs1 => x :: app xs1 xs2
    end.

  Infix "++" := app.

  Compute [10; 11] ++ [20; 21].

  Fixpoint rev {A} (xs : list A) : list A :=
    match xs with
    | [] => []
    | x :: xs => rev xs ++ [x]
    end.

  Compute rev [10; 11; 20; 21].

  Fixpoint concat {A} (xss : list (list A)) : list A :=
    match xss with
    | [] => []
    | xs :: xss => xs ++ concat xss
    end.

  Compute concat [[10; 11]; [20; 21]; [30; 31]].

  Fixpoint In {A} (x' : A) (xs : list A) : Prop :=
    match xs with
    | [] => False
    | x :: xs => x = x' \/ In x' xs
    end.

  Inductive option (A : Type) :=
    | None : option A
    | Some : A -> option A.
  Arguments None {_}.
  Arguments Some {_}.

  Fixpoint nth_error {A} (xs : list A) (i : nat) : option A :=
    match i, xs with
    | 0, [] => None
    | 0, x :: xs => Some x
    | S i, [] => None
    | S i, x :: xs => nth_error xs i
    end.
End list_defs.

Lemma app_nil_r {A} (xs : list A) :
  xs ++ [] = xs.
Proof. (* DONE IN CLASS *) Admitted.

Lemma in_nth_error {A} (xs : list A) x :
  In x xs <-> exists i, nth_error xs i = Some x.
Proof. (* DONE IN CLASS *) Admitted.

(** ######################################################################### *)
(** * Exercises about the list and option data types *)
(** ######################################################################### *)

Lemma app_assoc {A} (xs ys zs : list A) :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof. (* FILL IN HERE *) Admitted.

Lemma in_app_iff {A} (xs1 xs2 : list A) x :
  In x (xs1 ++ xs2) <-> In x xs1 \/ In x xs2.
Proof. (* FILL IN HERE *) Admitted.

Lemma length_app {A} (xs1 xs2 : list A) :
  length (xs1 ++ xs2) = length xs1 + length xs2.
Proof. (* FILL IN HERE *) Admitted.

Lemma rev_rev {A} (xs : list A) :
  rev (rev xs) = xs.
Proof. (* FILL IN HERE *) Admitted.

Lemma in_rev_iff {A} (xs : list A) x :
  In x (rev xs) <-> In x xs.
Proof. (* FILL IN HERE *) Admitted.

Lemma in_concat_iff {A} (xss : list (list A)) x :
  In x (concat xss) <-> exists xs, In x xs /\ In xs xss.
Proof. (* FILL IN HERE *) Admitted.

Lemma nth_error_Some_iff {A} (l : list A) n x :
  nth_error l n = Some x <->
  exists l1 l2, l = l1 ++ x :: l2 /\ length l1 = n.
Proof. (* FILL IN HERE *) Admitted.
