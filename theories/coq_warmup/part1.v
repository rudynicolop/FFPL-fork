(** * Lecture 1: Introduction to Coq (part 1) *)
From ffpl.lib Require Import prelude.

(** REMINDER:

          #####################################################
          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
          #####################################################

*)


(** ######################################################################### *)
(** * Introduction *)
(** ######################################################################### *)

(** In this lecture we show how Coq can be used as:

- A typed functional programming language (similar to OCaml or Haskell, but with
  the requirement that all functions are pure and terminating).
- A language to write mathematical statements and proofs.

IMPORTANT: In order to do the exercises in this file, make sure that you have
set up the shortcuts of your IDE (CoqIDE, Proofgeneral in Emacs, or VSCode)
properly so that you can execute commands one by one. Navigating via the menu
buttons using your mouse is inconvenient and takes lots of time. *)


(** ######################################################################### *)
(** * Definition of the natural numbers *)
(** ######################################################################### *)

(** To ensure the trustworthiness of Coq, the designers of the system tried to
keep the theory of Coq as small as possible. The standard data types (Booleans,
numbers, pairs, etc.) that we know and love from other programming languages are
not built-in primitives, but are defined in in terms of unified constructs.
Specifically, in Coq, these data types (and many more) can be defined by means
of "inductive types" (similar to algebraic data types in Haskell or OCaml).

Note: All of the inductive types that we define in this lecture are part of the
Coq standard library. To avoid confusion between the standard library and our
copies, we put our copies in a [Module] (for example, [Module nat_defs] below).
That way, after we close the module, we can use the definitions and notations
from the Coq standard library. *)

Module nat_defs.
  (** A very commonly used data type is the natural numbers 0, 1, 2, 3, ...
  One can define the natural numbers [nat] in Coq as the Peano numerals: *)

  Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.

  (** The type [nat] has two constructors: [O] represents the natural number 0,
  and [S n] represents the natural number [n + 1]. Using this data type, we can
  construct every natural number:

    0 := O
    1 := S O
    2 := S (S O)
    3 := S (S (S O))
    4 := S (S (S (S O)))

  And so on.

  An important feature of inductive types in Coq is that we can define functions
  by structural recursion. For example: *)

  Fixpoint plus (n1 n2 : nat) : nat :=
    match n1 with
    | O => n2
    | S n1' => S (plus n1' n2)
    end.

  (** The above function implements addition of Peano natural numbers, simply by
  merging together the [S] constructors. *)

  (** It is important to note that the function is structurally recursive on the
  argument [n1], i.e., the size of the argument [n1] reduces in each recursive
  call. To obtain logical soundness, all functions in Coq should be total (i.e.,
  terminating), which is enforced by structural recursion. The following
  non-terminating functions are _not_ structurally recursive, and are thus
  rejected by Coq: *)

  Fail Fixpoint foo (n : nat) := S (foo n).
  Fail Fixpoint bar (n : nat) := S (bar (S n)).

  (** Both of these attempts result in the error:

    Recursive call to foo has principal argument equal to "n" instead of
    a sub-term of "n".

  Indeed, these functions would not terminate, try to simplify [foo 0] (on
  paper), for instance.

  Unfortunately, Coq's restriction to structurally recursive functions also
  rules out "good" terminating functions. You can try to come up with an example
  yourself. Note that this situation is inevitable---it is undecidable to
  determine whether a function is terminating (by the halting problem), so any
  restriction to terminating functions that can be automatically enforced will
  be an over-approximation (i.e., is incomplete). *)

  (** In similar style as we have defined addition, we define multiplication.
  This function is structurally recursive in its first argument [n1] so Coq
  accepts it. *)

  Fixpoint mult (n1 n2 : nat) : nat :=
    match n1 with
    | O => O
    | S n1' => plus n2 (mult n1' n2)
    end.

  (** The predecessor function [pred n] decrements the number [n] by one. Since
  all functions in Coq have to be total, we let it return [O] in case the
  argument [n] is [O]. Since the predecessor function is not recursive, we use
  the command [Definition] instead of [Fixpoint]. *)

  Definition pred (n : nat) : nat :=
    match n with
    | S n => n
    | O => O
    end.

  (** Now that we have defined various functions on the natural numbers, we can
  perform some computations. For that, you do not need to compile this Coq file,
  but you can simply use Coq's [Compute] command. For example: *)

  Compute (plus (S (S O)) (S (S (S (S O))))).
  (** Gives [S (S (S (S (S (S O)))))] *)
  Compute (mult (S (S O)) (S (S (S (S O))))).
  (** Gives [S (S (S (S (S (S (S (S O)))))))] *)
  Compute ((fun x => plus x (mult x (S (S x)))) (S (S O))).
  (** Gives [S (S (S (S (S (S (S (S (S (S O)))))))))] *)

  (** Similarly, we can use Coq's [Check] command to type-check terms: *)

  Check plus.
  (** Gives [nat -> nat -> nat] *)
  Check (plus (S (S O))).
  (** Gives [nat -> nat] *)
  Check (fun x => plus x (mult x (S (S x)))).
  (** Gives [nat -> nat] *)

  (** To obtain expressions that are easier to read, we instruct Coq to use the
  conventional notations for parsing and pretty printing: *)

  Infix "+" := plus.
  Infix "*" := mult.

  Check (fun x => x + x * S (S x)).
  (** Gives [nat -> nat] *)
End nat_defs.

(** Now that we have seen how we can define the natural numbers and some
functions on them, let us close the module [nat_defs]. This hides the content,
and allows us to use the natural numbers from Coq's standard library. For these
we have the usual notations for literals: 0, 1, 2, and so on. *)

Compute (2 + 4).
(** Gives [6] *)
Compute (2 + S (S (S (S O)))).
(** Gives [6] *)
Compute (2 * 4).
(** Gives [8] *)
Compute ((fun x => x + (x * (S (S x)))) 2).
(** Gives [10] *)


(** ######################################################################### *)
(** * Proofs about the natural numbers *)
(** ######################################################################### *)

(** Now that we have defined some operations on natural numbers, let us prove
some properties about them. A lemma and proof are stated as follows in Coq:

  Lemma lemma_name vars :
    lemma statement.
  Proof.
    tactic1.
    tactic2.
    ...
  Qed.

This declares a lemma called [lemma_name] that says that [lemma statement]
holds for all values of variables [vars]. The proof is composed of tactics, which
correspond to the inference rules of logic. To develop or view a proof in Coq,
you should use your IDE to step over each tactic one-by-one. This will show the
intermediate proof state between each step.

Note: A lemma can equivalently be written as:

  Lemma lemma_name :
    forall vars, lemma statement.

In this course we favor the version where the top-most universally quantified
variables are put in front of the colon. This makes lemma statements more
concise and avoids us from having to introduce the variables explicitly in the
proof. *)

(** Let us start with a simple example *)

Lemma plus_0_l n :
  0 + n = n.
Proof.
  simpl. (** Simplify the goal, following the definition of [plus]. Since [plus]
  is defined by pattern matching on the first argument, [0 + n] is simplified
  into [n]. *)
  reflexivity. (** Both sides of the equality are equal, so we conclude the proof. *)
Qed.

(** The above property was trivial to prove, it followed immediately by
definition of the function [plus]. Proofs using [simpl] are called
"proof by computation". Let us now consider an example that involves the
familiar logical connectives and tactics corresponding to the familiar rules for
introduction and elimination. *)

Lemma O_or_S n :
  n = 0 \/ n = S (pred n).
Proof.
  destruct n as [|n']. (** Make a case distinction: The variable [n] is of type
  [nat], so it is either [O] or [S n'] for some [n']. The syntax [ as [|n'] ]
  is used to name the argument of the constructor [S]. This results in two goals,
  which should be structured using bullets [-], [+], or [*]. *)
  - (** Case [n = 0] *)
    left. (** Introduce the disjunction by picking the left disjunct. *)
    reflexivity.
  - (** Case [n = S n'] *)
    right. (** Introduce the disjunction by picking the right disjunct. *)
    simpl. (** [pred (S n')] simplifies to [n']. *)
    reflexivity.
Qed.

Lemma plus_O_O n m :
  n = 0 -> m = 0 -> n + m = 0.
Proof.
  (** The goal is an implication, and we can introduce an hypothesis with the
  [intros] tactic. If our goal is [P1 -> P2], the tactic [intros H] adds
  [H : P1] to the context and turns the goal into [P2]: *)
  intros Hn.
  (** We introduce the second hypothesis in the same way: *)
  intros Hm.

  (** IMPORTANT: Coq also allow you to use write [intros] without arguments. It
  then automatically selects names for the hypotheses (like [H] and [H0]). We
  strongly recommend to always give explicit names, otherwise proofs become very
  hard to read, modify, and debug. *)

  (** Now that we have introduced these hypotheses, we use the [rewrite H]
  tactic, which substitutes an equality [H : x = y] in the goal. We do that for
  both hypotheses: *)
  rewrite Hn.
  rewrite Hm.
  (** We finish the proof using [simpl] and [reflexivity] as before: *)
  simpl.
  reflexivity.
Restart. (** Let us try to make the proof a little shorter. *)
  intros Hn Hm. (** We can introduce both hypotheses in one go. *)
  rewrite Hn Hm. (** We can do both rewrites in one go. *)
  reflexivity. (** [reflexivity] automatically performs [simpl]. *)
Qed.

Lemma S_ne_O n :
  S n <> 0.
Proof.
  (** This lemma involves inequality, which is defined as the negation of
  equality. Hence, the statement is actually syntactic sugar for [~(S n = 0)].
  To proceed, let us look up the definition of negation in Coq: *)
  Print "~".
  (** We see that [~ A] is defined as [not : A -> False]. *)

  (** We ask Coq to unfold the definition of [~] in our goal.
  This is done with the [rewrite] tactic by adding a [/] in front of the
  name we want to unfold: *)
  rewrite /not.

  (** Since our goal is an implication, we use [intros]: *)
  intros Hn.

  (** It is impossible for [S ...] to be equal to [0], we can thus derive
  anything, including [False], which is never provable. The [discriminate] tactic
  looks for an impossible equality and solves any goal by contradiction. *)
  discriminate.
Restart. (** Let us try to make the proof a little shorter. *)
  discriminate. (** [discriminate] automatically unfolds [~] and performs
  [intros]. *)
Qed.

Lemma plus_0_inv n m :
  n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros Hnm. (** Introduce the implication *)
  destruct n as [|n'].
  - (** Case [n = 0] *)
    simpl in Hnm. (** Simplify the hypothesis [Hnm], transforming it from
    [0 + m = 0] into [m = 0]. *)
    split. (** Use conjunction introduction. This will create two goals for
    both conjuncts. *)
    + reflexivity. (** Both sides are equal, so we complete this goal. *)
    + assumption. (** The goal follows from the assumption [Hnm]. *)
  - (** Case [n = S n'] *)
    simpl in Hnm. (** Simplify the hypothesis [Hnm], transforming it from
    [S n' + m = 0] into [S (n' + m) = 0]. *)
    discriminate. (** It is impossible for [S ...] to be equal to [0], we can
    thus derive anything. The [discriminate] tactic looks for an impossible
    equality and solves any goal. *)
Qed.


(** ######################################################################### *)
(** * Exercises about natural numbers *)
(** ######################################################################### *)

(** Prove the lemmas below. For each of the lemmas carefully take into account:

- Can you derive it from results you have proven already?
- If not, do you have to perform induction? If so, on which variable?

You are _not_ allowed to use the Coq standard library or Coq tactics that we
have not discussed for these proofs. You are allowed to use: [intros],
[left], [right], [destruct], [assumption], [reflexivity], [simpl],
[rewrite], and [discriminate]. *)

(** IMPORTANT: You can "cheat" by finishing proofs with the [Admitted] command
instead of [Qed]. We do this for exercises, and the idea is that you finish the
proofs and get rid of all occurrences of [Admitted]. *)

Lemma mult_0_inv n m :
  n * m = 0 -> n = 0 \/ m = 0.
Proof. (* FILL IN HERE *) Admitted.

Lemma mult_0_l n :
  0 * n = 0.
Proof. (* FILL IN HERE *) Admitted.


(** ######################################################################### *)
(** * Definition of the Booleans *)
(** ######################################################################### *)

(** In Coq, the Booleans are defined as an inductive type. In the module
[bool_defs] below we give the definition of the [bool] type and show some of
the familiar operators on Booleans. All of these definitions are also in Coq's
standard library. *)

Module bool_defs.
  Inductive bool :=
    | true : bool
    | false : bool.

  (** Let us define the logical operators: *)

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

  (** Using the [Infix] command we define the familiar notation for the
  Boolean operations that we have just defined. *)

  Infix "&&" := andb.
  Infix "||" := orb.
End bool_defs.


(** ######################################################################### *)
(** * Exercises about the Booleans *)
(** ######################################################################### *)

Lemma andb_true_l b : true && b = b.
Proof. (* FILL IN HERE *) Admitted.

Lemma andb_true_r b : b && true = b.
Proof. (* FILL IN HERE *) Admitted.

Lemma andb_comm b1 b2 : b1 && b2 = b2 && b1.
Proof. (* FILL IN HERE *) Admitted.

Lemma xorb_inj_l b1 b2 b3 : xorb b1 b2 = xorb b1 b3 -> b2 = b3.
Proof. (* FILL IN HERE *) Admitted.

Lemma negb_andb b1 b2 :
  negb (b1 && b2) = negb b1 || negb b2.
Proof. (* FILL IN HERE *) Admitted.
