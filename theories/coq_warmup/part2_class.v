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

Print lt.
Print Nat.lt.

Search lt.

Search "pos" lt.
Search lt plus.
Search "<" "+".
Search (_ + _ < _ + _).
Search (?n + _ < ?n + _).

(** ** The [tauto] tactic *)

Lemma tauto_example_1 (P1 P2 P3 : Prop) :
  P1 /\ (P2 \/ P3) ->
  (P1 /\ P2) \/ (P1 /\ P3).
Proof. (* DONE IN CLASS *) Admitted.

Lemma tauto_example_2 (x y z1 z2 : nat) :
  x = y /\ (y = z1 \/ y = z2) ->
  (x = y /\ y = z1) \/ (x = y /\ y = z2).
Proof. (* DONE IN CLASS *) Admitted.

Lemma tauto_example_3 (P1 P2 Q R : Prop) :
  (P1 -> Q \/ False) ->
  P1 \/ P2 \/ Q ->
  ~(P2 /\ Q) ->
  ~P2 <-> Q.
Proof. (* DONE IN CLASS *) Admitted.

(** ** The [lia] tactic *)

Lemma lia_example_1 n m :
  n < 8 + 5*m ->
  m <= 3 - 4*n ->
  m < 4 /\ n < 8.
Proof. (* DONE IN CLASS *) Admitted.

Lemma lia_example_2 n m x y i :
  S m < S n ->
  x < S m ->
  (i < n -> x <> y) ->
  2*i + x < 2*n + x ->
  ~ x < y ->
  y + i < m + n.
Proof. (* DONE IN CLASS *) Admitted.

Lemma lia_example_3 (f : nat -> bool) i j :
  (forall n m, f (n + m) = f n && f m) ->
  f ((i + j) * 10) = f (i + (2 * j)) && f (j * 8 + i * 9).
Proof. (* DONE IN CLASS *) Admitted.

(** ** The [congruence] and [simplify_eq] tactics *)

Lemma congruence_example_1 a b c :
  (S a, S a) = (S b, S c) -> b = c.
Proof. (* DONE IN CLASS *) Admitted.

Lemma congruence_example_2 (f : nat -> nat) a  :
  f (f (f (f (f (f (f (f a))))))) = a ->
  f (f (f (f (f a)))) = a ->
  f a = a.
Proof. (* DONE IN CLASS *) Admitted.

(* The [congruence] tactic also solves inconsistent goals, and can thus be used
as a more powerful version of [discriminate]. *)

Lemma congruence_example_3 (f g : nat -> nat) a  :
  f (f (f (f (f (f (f (f a))))))) = a ->
  f (f (f (f (f a)))) = a ->
  f a <> a ->
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

Lemma xorb_false_inv b1 b2 :
  xorb b1 b2 = false -> b1 = b2.
Proof. (* DONE IN CLASS *) Admitted.

Lemma mult_0_r n :
  n * 0 = 0.
Proof. (* DONE IN CLASS *) Admitted.

Lemma plus_0_inv n m :
  n + m = 0 -> n = 0 /\ m = 0.
Proof. (* DONE IN CLASS *) Admitted.

Lemma done_example_1 n :
  n = 1 -> 1 = n.
Proof. (* DONE IN CLASS *) Admitted.

Lemma done_example_2 (n m : nat) :
  n = m -> n <> m -> 1 = 2.
Proof. (* DONE IN CLASS *) Admitted.

Lemma done_example_3 n :
  n <> n -> n = 10.
Proof. (* DONE IN CLASS *) Admitted.

Lemma done_example_4 n :
  n <> 1 -> 1 <> n.
Proof. (* DONE IN CLASS *) Admitted.

(** ** Destruct with equations *)

Lemma destruct_eqn_example (f : bool -> bool) :
  exists b, f b = b \/ f (f b) = b.
Proof. (* DONE IN CLASS *) Admitted.

(** ** Tacticals / tactic combinators *)

Lemma plus_0_r n :
  n + 0 = n.
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
  (exists nm, P (fst nm) /\ Q (snd nm)) ->
  exists n m, P n /\ Q m.
Proof. (* DONE IN CLASS *) Admitted.

Lemma intro_pattern_example_5 (P : nat -> Prop) n :
  (exists m, n = S m /\ P m) ->
  0 < n /\ P (pred n).
Proof. (* DONE IN CLASS *) Admitted.

Lemma intro_pattern_example_6 (P : nat -> Prop) n :
  (exists m, S n = S m /\ P m) ->
  P n.
Proof. (* DONE IN CLASS *) Admitted.

Lemma intro_pattern_example_7 n :
  (exists m, (m < 2 /\ S n = S m) \/ (m < 3 /\ n < m)) ->
  n < 2.
Proof. (* DONE IN CLASS *) Admitted.

(** ######################################################################### *)
(** * Exercises about Coq tactics and searching for lemmas *)
(** ######################################################################### *)

Lemma tactics_exercise_1 (f : bool -> bool) (b : bool) :
  f (f (f b)) = f b.
Proof. (* FILL IN HERE *) Admitted.

Lemma tactics_exercise_2 n :
  (exists m, n = m /\ m < 2) \/ (exists p, p < 3 /\ n < p) ->
  Nat.sqrt n <= 3.
Proof. (* FILL IN HERE *) Admitted.

Lemma tactics_exercise_3 (P Q R : nat -> Prop) :
  (exists n, (Q n <-> R n) /\ exists m, n = S m /\ P m /\ Q n) ->
  (exists i, R i /\ P (pred i)).
Proof. (* FILL IN HERE *) Admitted.

Lemma tactics_exercise_4 a b c d :
  c <> 0 ->
  (b * c + a + d * c) mod c = a mod c.
Proof. (* FILL IN HERE *) Admitted.

(** ######################################################################### *)
(** * Prop versus bool *)
(** ######################################################################### *)

Fixpoint oddb (n : nat) : bool :=
  match n with
  | O => false
  | S n' => negb (oddb n')
  end.

Definition evenb (n : nat) : bool :=
  negb (oddb n).

Compute (evenb 234).
Compute (oddb 234).

Definition even (n : nat) : Prop := exists m, n = m * 2.
Definition odd (n : nat) : Prop := exists m, n = S (m * 2).

Compute (even 234).

Lemma even_234 : even 234.
Proof. (* DONE IN CLASS *) Admitted.

Lemma oddb_plus n m :
  oddb (n + m) = xorb (oddb n) (oddb m).
Proof. (* DONE IN CLASS *) Admitted.

Lemma oddb_mult n m :
  oddb (n * m) = oddb n && oddb m.
Proof. (* DONE IN CLASS *) Admitted.

Lemma oddb_pow n m :
  oddb (n ^ m) = (m =? 0) || oddb n.
Proof. (* DONE IN CLASS *) Admitted.

Lemma example_oddb :
  oddb (11 + 233 * 24 ^ (12 + 54 ^ (34 ^ 88))) = true.
Proof. (* DONE IN CLASS *) Admitted.

Lemma oddb_mult_2 n :
  oddb (n * 2) = false.
Proof. (* DONE IN CLASS *) Admitted.

Lemma oddb_odd_2 n :
  odd n -> oddb n = true.
Proof. (* DONE IN CLASS *) Admitted.

Lemma oddb_odd_1 n :
  oddb n = true -> odd n.
Proof. (* DONE IN CLASS *) Admitted.

Lemma oddb_odd n :
  oddb n = true <-> odd n.
Proof. (* DONE IN CLASS *) Admitted.

Search "<" "<?".

(** ######################################################################### *)
(** * Exercises about Prop versus bool *)
(** ######################################################################### *)

Lemma even_or_odd n :
  even n \/ odd n.
Proof. (* FILL IN HERE *) Admitted.

Lemma not_even_and_odd n :
  ~ (even n /\ odd n).
Proof. (* FILL IN HERE *) Admitted.

Lemma odd_em n :
  odd n \/ ~odd n.
Proof. (* FILL IN HERE *) Admitted.

Lemma evenb_even n :
  evenb n = true <-> even n.
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

Lemma app_assoc {A} (xs ys zs : list A) :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof. (* DONE IN CLASS *) Admitted.

Lemma in_nth_error {A} (xs : list A) x :
  In x xs <-> exists i, nth_error xs i = Some x.
Proof. (* DONE IN CLASS *) Admitted.

(** ######################################################################### *)
(** * Exercises about the list and option data types *)
(** ######################################################################### *)

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
