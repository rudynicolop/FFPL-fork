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

Lemma S_pred n : n <> 0 -> n = S (pred n).
Proof.
  intros Hn.
  (** By the lemma [O_or_S] above we know [n = 0 \/ n = S (pred n)]. The first
  disjunct leads to a contradiction, and the second is exactly what we want to
  prove. The [destruct] tactic is also used for disjunction elimination, i.e.,
  if we have [H : P1 \/ P2], the tactic [destruct H as [H1|H2]] will give
  two goals with [H1 : P1] and [H2 : P2], respectively. For [H : P1 \/ P2] we
  can also use lemmas we have already proved, e.g., [O_or_S n]: *)
  destruct (O_or_S n) as [H0|HS].
  - rewrite /not in Hn. (** Remember that inequality [x <> y] is [x = y -> False] *)
    exfalso. (** We have reached a point in the proof where we can show a
    contradiction. Since [False] implies everything, we can use the [exfalso]
    tactic to tell Coq that instead of the current goal, we wish to prove
    [False] instead. This is often not necessary (the proof script below
    would work even without using [exfalso], but it is useful to communicate
    to later readers of your proof (in particular, your future self) that
    we have reached a contradiction. *)
    destruct Hn. (** Our hypothesis is [n = 0 -> False]. By False elimination
    (aka ex falso, aka principle of explosion) we can derive anything from
    [False]. So, provided we can prove [n = 0], we are done. The [destruct]
    tactic is also used for False elimination. In this case it will create a
    goal for the premise [n = 0]. *)
    assumption. (** When the goal exactly matches one of the assumptions,
    the [assumption] tactic will complete the proof. *)
  - assumption.
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

(** The following is a stronger version of the above lemma, instead of
implication [->] we use bi-implication [<->] (aka "iff" or "if and only if"). *)

Lemma plus_0_iff n m :
  n + m = 0 <-> n = 0 /\ m = 0.
Proof.
  (** To figure out how to prove a [<->], we can ask Coq to show us its
  definition *)
  Print "<->".
  (** We see that [A <-> B] is defined as [iff: (A -> B) /\ (B -> A)]. *)

  (** We ask Coq to unfold the definition of [<->] in our goal. *)
  rewrite /iff.

  (** Since we are faced with proving a conjunction, we can proceed with the
  [split] tactic for conjunction introduction that we already used in the
  previous lemma. *)
  split.
  - (** Since the left-to-right direction is our previous lemma, we can use it.
    For that, we use Coq's [apply] tactic. *)
    apply plus_0_inv.
  - intros Hnm.
    destruct Hnm as [Hn Hm]. (** The [destruct] tactic is also used for
    conjunction elimination, i.e., if we have [H : P1 /\ P2], the tactic
    [destruct H as [H1 H2]] will give [H1 : P1] and [H2 : P2]. *)
    rewrite Hn Hm.
    simpl.
    reflexivity.
Qed.

(** Let us practice a bit more with inequality and bi-implication. *)

Lemma plus_ne_0_iff n m :
  n + m <> 0 <-> n <> 0 \/ m <> 0.
Proof.
  split. (** [split] will automatically unfold. *)
  - intros Hnm. destruct n as [|n].
    + simpl in Hnm. right. assumption.
    + left. intros Hn. discriminate.
  - intros Hnm Hnm0. destruct (plus_0_inv n m) as [Hn0 Hm0].
    (* Instead of bullets, we can also use curly braces for subgoals.
    This avoids proofs that look like very unbalanced trees. *)
    { assumption. }
    destruct Hnm as [Hn|Hm].
    + destruct Hn. assumption.
    + destruct Hm. assumption.
Qed.

(** In the above proofs we used the bullets [-], [+], and [*] to structure the
proof. If you need deeper levels of nesting, you can also use [--], [++], [**],
[---], [+++], [***], etc. You can also use brackets [{ }], which are often
preferred if the proof of the first goal is very small. *)

(** The following lemma is similar to [plus_0_l : 0 + n = n], but with 0 for
the second instead of the first argument. *)

Lemma plus_0_r n :
  n + 0 = n.
Proof.
  simpl. (** Does not do anything. Since [plus] is defined by pattern matching
  on the first argument, [n + 0] is not simplified. *)

  (** We could try to proceed by case distinction on [n]. *)
  destruct n as [|n'].
  - simpl. reflexivity. (** So far so good. *)
  - simpl. (** Now we end up with [S (n + 0) = S n], which did not make the
    situation better. This goal is more complicated than the goal we started
    with! *)

Restart. (** Let us try again *)

  (** Perform proof by induction: using the tactic [ induction n as [|n' IH] ]
  we perform induction on a natural number [n]. It will produce two subgoals,
  one for the base case, and one for the inductive case. The induction
  hypothesis will be called [IH]. *)
  induction n as [|n' IH].
  - (** Base case *)
    simpl. reflexivity.
  - (** Inductive case *)
    (** Now we have the same goal as before, but with the additional hypothesis:

      IH : n' + 0 = n'

    That is to say, we know that the property holds for the smaller natural
    number [n']. This gives us enough information to finish the proof. *)
    simpl.
    rewrite IH. (** Replace the LHS of [IH : n' + 0 = n'] with the RHS. *)
    reflexivity.
Qed.

(** Let us practice more with proof by induction *)

Lemma plus_S_r n1 n2 :
  n1 + S n2 = S (n1 + n2).
Proof.
  induction n1 as [|n1 IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.

Restart.

  (** Instead of [rewrite], we will now demonstrate another tactic: [f_equal],
  which makes use of the fact that [p = q] implies [S p = S q]. *)

  induction n1 as [|n1 IH].
  - simpl. reflexivity.
  - simpl.
    f_equal.
    assumption.
Qed.

(** For the following lemma, think carefully on which argument we should do
induction. Why do we use [n1] and not another argument? *)

Lemma plus_assoc n1 n2 n3 :
  n1 + (n2 + n3) = (n1 + n2) + n3.
Proof.
  (** For this proof it is worth enabling "View - Display parentheses".
  Otherwise it can be hard to see what we are even proving.
  If you are not using CoqIDE, [Set Printing Parentheses] should
  have the same effect. *)
  induction n1 as [|n1 IH].
  - simpl. reflexivity.
  - simpl. f_equal. assumption.
Qed.

(** In the next proof, we see that we can reuse lemmas that we have proved before.
This is important, as otherwise proofs quickly become unmanageable. *)

Lemma plus_comm n1 n2 :
  n1 + n2 = n2 + n1.
Proof.
  induction n1 as [|n1 IH].
  - simpl.
    rewrite plus_0_r. (** The goal [n2 = n2 + 0] is an instance of the lemma
    [plus_0_r] that we proved before. *)
    reflexivity.
  - simpl.
    rewrite plus_S_r. (** In this case, we make use of the lemma [plus_S_r] that
    we just proved. *)
    rewrite IH. reflexivity.
Qed.

(** Now that we have seen some proofs by induction, the [induction] tactic may
appear attractive to prove *any* lemma about natural numbers. However,
defaulting to induction is a bad idea! As the lemma below shows, reuse of
lemmas, instead of blindly performing induction, is very important. The lemma
below can be proven using the properties we have proved so far: associativity
and commutativity of addition.

Note: To convince yourself that proof by induction is not always the right
approach, you could try to prove the lemma by induction. You will see that it
gets very difficult (you even might get stuck). *)

Lemma plus_rearrange n m p q :
  (n + m) + p + q = (m + n) + (p + q).
Proof.
  (** The situation here becomes a bit tricky: if we would just write
  [rewrite plus_comm] it will trigger the rewrite at an arbitrary position in
  the goal. This happens because [plus_comm] is universally quantified.
  Use [About] to show the lemma statement: *)
  About plus_comm.
  (** In CoqIDE, you can move your cursor over the lemma name and
  hit Ctrl-Shift-A, and it will run the [About] command. Other IDEs
  will have similar feature, and they are worth learning!
  As proof developments get bigger, a significant fraction of time
  is spent finding the right lemmas and understanding their exact
  statement.

  This prints:

    plus_comm n1 n2 : n1 + n2 = n2 + n1

  It fits any occurrence of [plus] in the goal. To work around that, we tell
  [rewrite] where exactly it should apply the lemma, by giving a pattern
  in square brackets. *)
  rewrite [n + _]plus_comm.

  (** Now we just need to rewrite one more time with associativity. *)
  rewrite plus_assoc.
  reflexivity.
Qed.

(** In the following lemma, we demonstrate Coq's [injection] tactic, which
simplifies a hypothesis using injectivity of constructors. *)

Lemma plus_inj_l n1 n2 n3 :
  n1 + n2 = n1 + n3 -> n2 = n3.
Proof.
  intros H. induction n1 as [|n1 IH].
  - simpl in H.
    assumption.
  - simpl in H.
    apply IH.
    injection H as H. (** The [injection] tactic applies the fact that
    constructors of inductive data types are injective. For the case of natural
    numbers that means:

      S p = S q -> p = q

    *)
    assumption.
Qed.

(** Until now, all lemmas that we proved by induction started the proof
immediately using the [induction] tactic. Let us take a look at a lemma where
this approach does not work, and see how it can be fixed. The fix is an instance
of what is often called "generalizing the induction hypothesis". *)

Lemma double_inj n m :
  n + n = m + m -> n = m.
Proof.
  intros Hnm. induction n as [|n IH].
  - (** The base case is either, [m] is either 0 and then we are done, or it is
    a [S] and then we have a contradiction. *)
    simpl in Hnm. destruct m as [|m].
    + reflexivity.
    + discriminate.
  - (** In the inductive case we again perform a case analysis on [m]. *)
    destruct m as [|m].
    + discriminate.
    + f_equal.
      (** At this point we are stuck. We want to prove [n = m], but the
      conclusion of our induction hypothesis is [n = S m]. In other words, the
      [n] and [m] have ran out of sync in the induction hypothesis. *)
    (** If you go back to the beginning of this inductive case (before the
    [destruct], and have a look at our context, you will see that we were already
    doomed there: our assumption [Hnm] says [2 + 2n = 2m], and the [IH] requires
    [2n = 2m]. So our induction hpoythesis requires something unprovable, making
    it useless. *)

Restart. (** Let us try again *)
  (** The problem is that the induction hypothesis talks about a specific [m],
  namely the one that we have fixed at the start of the proof. We can solve this
  problem by generalizing our goal before performing induction. For that we use
  the [revert] tactic, which turns the goal into

    forall m, n + n = m + m -> n = m

  As a result, in the inductive case, we now have to prove
  [forall m, S n + S n = m + m -> S n = m] under the assumption of the induction
  hypothesis [forall m, n + n = m + m -> n = m]. Importantly, the new induction
  hypothesis allows us to pick any [m]. *)

  revert m.
  induction n as [|n IH].
  - (** The base case is as before, the only difference is that we need to
    introduce [m] and [Hnm]. *)
    intros m Hnm. simpl in Hnm. destruct m as [|m].
    + reflexivity.
    + discriminate.
  - intros m Hnm. simpl in Hnm. destruct m as [|m].
    + discriminate.
    + f_equal.
      (** At this point, our induction hypothesis does fit! *)
      apply IH.
      (** Allowing us to finish the proof in the way we are used to. *)
      simpl in Hnm.
      rewrite plus_S_r in Hnm.
      rewrite plus_S_r in Hnm.
      injection Hnm as Hnm.
      assumption.
Qed.


(** ######################################################################### *)
(** * Exercises about natural numbers *)
(** ######################################################################### *)

(** Prove the lemmas below. For each of the lemmas carefully take into account:

- Can you derive it from results you have proven already?
- If not, do you have to perform induction? If so, on which variable?

You are _not_ allowed to use the Coq standard library or Coq tactics that we
have not discussed for these proofs. You are allowed to use: [intros], [revert],
[split], [left], [right], [destruct], [induction], [assumption], [reflexivity],
[simpl], [rewrite], [discriminate], [injection], [exfalso], [f_equal], and [apply]. *)

(** IMPORTANT: You can "cheat" by finishing proofs with the [Admitted] command
instead of [Qed]. We do this for exercises, and the idea is that you finish the
proofs and get rid of all occurrences of [Admitted].

To give you some rough estimate of the proof complexity, we show how many lines
of code the sample solution has. However, note that the sample solution puts
multiple tactics on the same line and are generally very compact. Don't worry
if your proof is longer. But if your proof is 5x longer, consider asking for
a shorter proof in the exercise group or check the sample solution. *)

Lemma mult_0_inv n m :
  n * m = 0 -> n = 0 \/ m = 0.
Proof. (* FILL IN HERE (5 LOC proof) *) Admitted.

Lemma mult_0_l n :
  0 * n = 0.
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

Lemma mult_0_r n :
  n * 0 = 0.
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.

Lemma plus_swap n1 n2 n3 :
  n1 + (n2 + n3) = n2 + (n1 + n3).
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

Lemma mult_S_r n1 n2 :
  n1 * S n2 = n1 + n1 * n2.
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.

Lemma mult_comm n1 n2 :
  n1 * n2 = n2 * n1.
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.

Lemma plus_mult_distr_l n1 n2 n3 :
  (n1 + n2) * n3 = n1 * n3 + n2 * n3.
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.

Lemma mult_assoc n1 n2 n3 :
  n1 * (n2 * n3) = (n1 * n2) * n3.
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.

(** When proving this lemma, it will help to apply [plus_inj_l].
However, note that this lemma is stated as follows:

  forall n1 n2 n3 : nat, n1 + n2 = n1 + n3 -> n2 = n3

When applying it, the variable [n1] is entirely unconstrained!
[apply plus_inj_l] will hence not work. You have to explicitly
tell Coq the desired value for [n1], which you can do by treating
the lemma as a function that takes [n1] as the first argument:
[apply (plus_inj_l <value>)]. *)

Lemma plus_inj_r n1 n2 n3 :
  n1 + n3 = n2 + n3 -> n1 = n2.
Proof. (* FILL IN HERE (4 LOC proof) *) Admitted.

(** The following lemma is challenging. You need to generalize the induction
hypothesis (that is, use [revert]), and use a combination of previously proven
lemmas with both [apply] and [rewrite]. When performing a [rewrite], it is often
necessary to use [rewrite [pattern]lemma] as we have demonstrated in the
proof of [plus_rearrange] above. You can use [rewrite !lemma] to rewrite with
the same lemma as often as possible. You will also have to apply lemmas
with explicitly given arguments, as in [apply (lemma arg1 ...)].

IMPORTANT: If you get stuck, it is best to finish the other exercises below
first. *)

Lemma mult_plus_same_inj n m p :
  n * (n + p) = m * (m + p) -> m = n.
Proof. (* FILL IN HERE (12 LOC proof) *) Admitted.

Lemma square_inj n m :
  n * n = m * m -> m = n.
Proof. (* FILL IN HERE (2 LOC proof) *) Admitted.


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
(** * Theorems and proofs about the Booleans *)
(** ######################################################################### *)

Lemma andb_true_l b : true && b = b.
Proof.
  simpl. (** Simplify the goal, following the definition of [andb]. Since [andb]
  is defined by pattern matching on the first argument, [true && b] is
  simplified into [b]. *)
  reflexivity. (** Both sides are equal. *)
Qed.

Lemma andb_true_r b : b && true = b.
Proof.
  simpl. (** Similar to [n + 0], this does not simplify anything because [andb]
  is defined by pattern matching on the first argument. *)

  (** Hence we proceed using the [destruct] tactic to make a case distinction
  between [b = true] and [b = false]. *)
  destruct b.
  - (** Case [b = true] *)
    simpl.
    reflexivity.
  - (** Case [b = false] *)
    simpl.
    reflexivity.
Qed.

Lemma andb_comm b1 b2 : b1 && b2 = b2 && b1.
Proof.
  destruct b1.
  - destruct b2.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
  - destruct b2.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Restart.
  (** The above proof is lengthy and contains a lot of repetition. We will now
  carry out the proof in a shorter and more concise manner.

  First observe that tactics are separated by a period. The period executes the
  tactic, and produces a number of subgoals (or zero, for example when using
  [reflexivity] or [assumption]), which are then shown in your IDE. Apart from
  periods, tactics in Coq can also be composed using the semicolon operator:

    tac1; tac2.

  The semantics of [tac1; tac2] is different than [tac1. tac2]: it will apply
  [tac2] to all subgoals generated by [tac1] (not just the first), and it does
  not explicitly show goals for the intermediate in your IDE. Let us see the
  semicolon operator in action: *)

  destruct b1; destruct b2; simpl; reflexivity.
Restart.
  (** Multiple [destruct]s can be turned into one *)
  destruct b1, b2; simpl; reflexivity.
Restart.
  (** [reflexivity] automatically performs [simpl], so this can be omitted.
  WARNING: Omitting [simpl] might make debugging/replaying your proof more
  difficult, thus do so with care. *)
  destruct b1, b2; reflexivity.
Qed.

Lemma xorb_inj_l b1 b2 b3 : xorb b1 b2 = xorb b1 b3 -> b2 = b3.
Proof.
  intros H.
  (** Since [xor] is defined by pattern matching on both arguments, we proceed
  by case distinction on all Boolean variables. *)
  destruct b1, b2, b3; simpl in H.
  (** This gives [2^3 = 8] subgoals, but as we can see, these can be classified
  into two kinds:

  - Trivial goals: [true = true] and [false = false].
  - Contradictory goals, where we have either the hypothesis [false = true] or
    [true = false].

  Of course, we could prove each of these goals individually, but that gets
  lengthy. So, instead we will make use of the following tactic operator:

    tac1 || tac2

  This operator will try to run the tactic [tac1] and in case it fails, it will
  run [tac2] instead. *)

Restart. (* Let us start over *)
  intros H.
  destruct b1, b2, b3; simpl in H; discriminate || reflexivity.
Qed.

Lemma negb_andb b1 b2 :
  negb (b1 && b2) = negb b1 || negb b2.
Proof.
  destruct b1; simpl; reflexivity.
Qed.

Lemma orb_andb_distr b1 b2 b3 :
  b1 && (b2 || b3) = (b1 && b2) || (b1 && b3).
Proof.
  destruct b1; simpl; reflexivity.
Qed.

Lemma andb_assoc b1 b2 b3 : b1 && (b2 && b3) = (b1 && b2) && b3.
Proof.
  destruct b1; simpl; reflexivity.
  (** Question: Why do we not need to perform a case analysis on [b2] or [b3]? *)
Qed.


(** ########################################################################## *)
(** * Exercises about the Booleans *)
(** ########################################################################## *)

(** Remember to use the operators [;] and [||] to shorten your proofs. *)

Lemma xorb_false_l b :
  xorb false b = b.
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

Lemma xorb_false_inv b1 b2 : xorb b1 b2 = false -> b1 = b2.
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

Lemma xorb_negb_l b1 b2 :
  xorb (negb b1) b2 = negb (xorb b1 b2).
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

Lemma negb_involutive b :
  negb (negb b) = b.
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

Lemma negb_inv b1 b2 :
  negb b1 = negb b2 <-> b1 = b2.
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.

(** We define the functions [oddb : nat -> bool] and [evenb : nat -> bool] to
test whether a number is odd or even: *)

Fixpoint oddb (n : nat) : bool :=
  match n with
  | O => false
  | S n' => negb (oddb n')
  end.

Definition evenb (n : nat) : bool :=
  negb (oddb n).

Lemma oddb_mult_2 n :
  oddb (n * 2) = false.
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.

(** Prove the following lemma by induction (decide yourself on which variable).
For both the base and the inductive case, you need to [rewrite] with some of the
lemmas about [xorb] that we have proved above. *)

Lemma oddb_plus n m :
  oddb (n + m) = xorb (oddb n) (oddb m).
Proof. (* FILL IN HERE (4 LOC proof) *) Admitted.

(** Fix the definition [f] to make the next lemma true *)
Definition f (b1 b2 : bool) : bool. (* FILL IN HERE *) Admitted.

(** To prove this lemma, you want to start by unfolding the definition of [f]
and [evenb]. You should [rewrite] using the lemma [plus_oddb] and some lemmas
about the logical operators. *)

Lemma evenb_plus n m :
  evenb (n + m) = f (evenb n) (evenb m).
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

(** Prove the following lemma using induction. For the inductive case, you need
to write a helping lemma that involves [&&], [xorb], and [negb]. *)

Lemma mul_oddb n m :
  oddb (n * m) = oddb n && oddb m.
Proof. (* FILL IN HERE (4 LOC helpers and 4 LOC proof) *) Admitted.

(** Prove this lemma without induction. Use the preceding lemma [mul_oddb]
instead. Note that you can use [rewrite -lemma] to rewrite right-to-left
instead of the usual left-to-right. *)
Lemma evenb_mul n m :
  evenb (n * m) = evenb n || evenb m.
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.


(** ########################################################################## *)
(** * Final exercise *)
(** ########################################################################## *)

(** Below we define two versions of the factorial function:

- [factorial] is the usual definition that we know from textbooks. This
  definition is not tail recursive, so will cause stack-overflows for large
  numbers.
- [factorial_tailrec] is tail recursive, and thus more efficient because it can
  be compiled into a simple loop. It uses a helper [factorial_tailrec_go] that
  involves an accumulator.

The goal of this exercise is to prove that both functions give the same results.
That is:

  factorial_tailrec n = factorial n

for any natural number [n]. *)

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

(** To prove the lemma [factorial_tailrec_correct] you need to first state and
prove a helping lemma that involves [factorial_tailrec_go]. *)

Lemma factorial_tailrec_correct n :
  factorial_tailrec n = factorial n.
Proof. (* FILL IN HERE (11 LOC helpers and 2 LOC proof) *) Admitted.
