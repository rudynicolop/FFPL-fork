(** * Lecture 2: Introduction to Coq (part 2) *)
From ffpl.lib Require Import prelude.

(** REMINDER:

          #####################################################
          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
          #####################################################

*)


(** ######################################################################### *)
(** * Introduction *)
(** ######################################################################### *)

(** In this lecture we will cover the following topics:

- We discuss a number of Coq features to automatically find proofs, to look for
  lemmas from the standard library, and to write proofs in a more compact
  manner.
- We learn about inductively defined predicates.
- We take a look at the polymorphic list and option data types and the familiar
  functions on those. *)


(** ######################################################################### *)
(** * Coq tactics and searching for lemmas *)
(** ######################################################################### *)

(** ** Searching for lemmas *)

(** In large proofs it is essential to avoid reinventing the wheel. You should
use the Coq standard library when possible (unless we explicitly ask you not to
in certain exercises or on the exam). You can search for definitions and lemmas
in Coq's libraries using the [Search] command. For example, let us assume
we are interested in inequality of natural numbers, then the [Search] command
below will display all binary relations on natural numbers. *)

Search (nat -> nat -> Prop).

(** In this list we see [lt : nat -> nat -> Prop], which considering the name
is likely the relation that we are looking for. (Note that [Nat.lt] and [lt]
are aliases.) You can use the [Print] command to verify it is indeed the right
definition. *)

Print Nat.lt.
Print lt.

(** Using the [Search] command below we can subsequently obtain all lemmas about
[lt] (in the output, we also see that [lt] is pretty printed as [<], which is
another indication that we have found the right relation). *)

Search lt.

(** The above list is very long, and finding the right lemma is not always easy.
We can limit our search as follows. *)

Search "pos" lt.          (** All lemmas about [lt] with "pos" in the name. *)
Search lt plus.           (** All lemmas about [lt] and [plus]. *)
Search "<" "+".           (** The same, but using notations instead of names. *)
Search (_ + _ < _ + _).   (** Search by pattern. *)
Search (?n + _ < ?n + _). (** More refined search by pattern. *)

(** ** The [lia] tactic *)

(** Perhaps the most useful tactic for reasoning about natural numbers is [lia].
It automatically solves goals that involve linear arithmetic (in)equalities.
It is complete for propositional goals involving [<], [<=], [=], [+], [-], [S],
[0], and [*] where one argument is a constant. For goals involving arbitrary
multiplication [lia] is not complete, but is often still able to find a
proof. *)

Lemma lia_example_1 n m :
  n < 8 + 5*m ->
  m <= 3 - 4*n ->
  m < 4 /\ n < 8.
Proof.
  lia.
Qed.

(** The following [example] cannot be solved by [lia]: It involves an unknown
function [f] and the premise involves a quantifier. Yet, [lia] can be of help
in a manual proof. *)

Lemma lia_example_2 (f : nat -> bool) i j :
  (forall n m, f (n + m) = f n && f m) ->
  f ((i + j) * 10) = f (i + (2 * j)) && f (j * 8 + i * 9).
Proof.
  intros Hf.
  (** We would like to rewrite with [Hf], but its left-hand side does not
  match our goal. We use [replace ... with ... by lia] to turn our goal into the
  right shape to use [Hf]. *)
  replace ((i + j) * 10) with ((i + (2 * j)) + (j * 8 + i * 9)) by lia.

  (** Now we can use [Hf] to complete our proof. *)
  rewrite Hf.
  reflexivity.
Qed.

(** The above pattern occurs often: The lemma that you want to [apply] or
[rewrite] nearly matches the goal, but not entirely. Using [replace] you can
turn your goal into the right shape.

Note that you can use [replace t1 with t2 by tac] with any tactic [tac], not
just [lia]. You can also leave out [by tac], which results in an explicit goal
with the equality [t1 = t2] that you have to prove yourself.
(That goal becomes the *second* subgoal, so you will usually want
to use [2:{] to discharge the side-condition before continuing with the
rest of the proof.) *)


(** ** The [subst], [congruence], and [simplify_eq] tactics *)

(** The [subst x] tactic looks for an equality of the form [x = term] or [term = x],
and entirely removes [x] by replacing all of its occurrences with [term]. *)

Lemma subst_example_1 (f : nat -> nat) a b :
  a = b ->
  f a = 1 ->
  f b = 0 ->
  0 = 1.
Proof.
  intros Hab Hfa Hfb. subst a.
  rewrite -Hfa -Hfb. reflexivity.
Qed.

(** [subst] without an argument will replace all variables that have a suitable
equality. *)
Lemma subst_example_2 (f : nat -> nat) a b :
  a = 1 ->
  b = 2 ->
  a + 2 = b + 1.
Proof.
  intros Ha Hb. subst. reflexivity.
Qed.

(** The [congruence] tactic implements a solver for equalities that can be
proved without knowing anything about the symbols involved, except that
constructors are injective. *)

Lemma congruence_example_1 a b c :
  (S a, S a) = (S b, S c) -> b = c.
Proof.
  congruence.
Qed.

(** The [congruence] tactic also solves inconsistent goals, and can thus be used
as a more powerful version of [discriminate]. *)

Lemma congruence_example_2 (f : nat -> nat) a b :
  a = b ->
  f a = 1 ->
  f b = 0 ->
  0 = 1.
Proof.
  congruence.
Qed.

(** The [simplify_eq] tactic repeatedly applies [subst], [injection]
and [discriminate]. Its effect is somewhat similar to [congruence],
but where [congruence] fails if it cannot completely solve the goal,
[simplify_eq] returns a goal. *)

Lemma simplify_eq_example_1 a b c :
  (S a, S a) = (S b, S c) ->
  b + c = 2 * b.
Proof.
  intros H.
  simplify_eq.
  lia. (** The [lia] tactic does not work on the initial goal, since it involves
  pairs, i.e., it is not in the domain of linear integer arithmetic.
  [simplify_eq] moved the goal into [lia]'s domain. *)
Qed.

(** ** The [done] tactic *)

(** As you might have noticed in the exercises of week 1, Coq proofs often end
with [reflexivity], [assumption] or [discriminate]. Instead of having to pick
such a tactic yourself for each leaf of your proof, the [done] tactic will do
so automatically. Roughly, [done] introduces all universal quantifiers,
implications and conjunctions, and then solves the goal with [reflexivity],
[assumption], or [discriminate]. Additionally, it uses symmetry of equality,
and solves simple inconsistent goals (e.g., with contradicting hypotheses [P]
and [~P], or [x != x]).

You can use the syntax [by tac] for [tac; done] as a shorthand. *)

(** Let us see some examples from previous week. *)

Lemma plus_0_l n :
  0 + n = n.
Proof. done. Qed.

(** We have been using the symbol [<>] for ineqality so far, but
we will need that symbol for a different piece of syntax later.
So we will switch to [!=] for inequality. *)

Lemma S_ne_O n :
  S n != 0.
Proof. done. Qed.

Lemma S_pred n : n != 0 -> n = S (pred n).
Proof. by destruct n. Qed.

(** The tactics [done] and [by tac] are useful when chaining tactics with [;].
Often many subgoals are solved in a similar but slightly different manner (e.g.,
one goal by [discriminate] and another by [reflexivity]). *)

Lemma xorb_false_inv b1 b2 :
  xorb b1 b2 = false -> b1 = b2.
Proof. by destruct b1, b2. Qed.

Lemma plus_0_inv n m :
  n + m = 0 -> n = 0 /\ m = 0.
Proof. by destruct n. Qed.

(** Finally we give some examples where [done] uses symmetry of equality or
derives contradictions. *)

Lemma done_example_1 n :
  n = 1 -> 1 = n.
Proof. done. Qed.

Lemma done_example_2 (n m : nat) :
  n = m -> n != m -> 1 = 2.
Proof. done. Qed.

Lemma done_example_3 n :
  n != n -> n = 10.
Proof. done. Qed.

Lemma done_example_4 n :
  n != 1 -> 1 != n.
Proof. done. Qed.

(** ** [simpl] and [done] during [rewrite] *)

(** Often we need to combine [rewrite] with [simpl] and [done].
Coq provides special syntax for conveniently doing that:
[/=] means [simpl], and [//] means [done]. *)
Lemma plus_0_r n :
  n + 0 = n.
Proof.
  induction n as [|n' IH].
  { done. }
  rewrite /= IH //.
  (* This tactic is short for: [simpl; rewrite IH; done.] *)
Qed.

(** ** Destruct with equations *)

(** In week 1 we have used the [destruct] tactic to perform case analysis on
natural numbers and Booleans. Typically, we use [destruct t as ...] where [t]
is a variable. The [destruct] tactic can also be used on compound terms [t],
e.g., [f n] for a function [f]. The general form is [destruct t as ... eqn:H],
where [t] can be any term. This tactic also adds the corresponding equation
[H : t = ...] to each subgoal.

For instance, when doing [destruct t as [|n] eqn:H] where [t] is some term of
type natural number, we will have one subgoal with [H : t = 0], and one subgoal
with [H : t = S n]. *)

Lemma destruct_eqn_example (f : bool -> bool) :
  exists b, f b = b \/ f (f b) = b.
Proof.
  (** We use [destruct (f true) eqn:H] to determine whether
  [Htrue : f true = true] or [Htrue : f true = false]. *)
  destruct (f true) eqn:Htrue.
  - (** Case [f true = true] *)
    exists true. by left.
  - (** Case [f true = false] *)
    (** Now we do the same for [f false]. *)
    destruct (f false) eqn:Hfalse.
    + (** Case [f false = true] *)
      exists false. right. congruence.
    + (** Case [f false = false] *)
      exists false. left. congruence.
Qed.

(** ** [apply] in hypotheses *)

(** The [apply] tactic can be used not only on the goal,
but also on assumptions. This lets us do "forward" reasoning. *)
Lemma plus_mono_l n1 n2 k :
  n1 + k <= n2 + k -> n1 <= n2.
Proof.
  intros Hn12. apply Nat.add_le_mono_r in Hn12. done.
Qed.

(** ######################################################################### *)
(** * Exercises about searching for lemmas *)
(** ######################################################################### *)

(** Search for suitable lemmas to prove these exercises. *)

Lemma search_exercise_1 (n : nat) :
  4 <= n -> 2 <= Nat.sqrt n.
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.

Lemma search_exercise_2 a :
  0 < a ->
  1 + Nat.log2 a <= a.
Proof. (* FILL IN HERE (6 LOC proof) *) Admitted.

(** ######################################################################### *)
(** * Exercises about Coq tactics  *)
(** ######################################################################### *)

(** Prove these lemmas using the techniques you have learned today. *)

Lemma tactics_exercise_1 (m n : nat) :
  m <= n -> m > 10 -> n < 8 -> False.
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

Lemma tactics_exercise_2 (P : nat -> Prop) (n : nat) :
  (forall m, P (2*m + 1)) ->
  P (n + 1 + n).
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

Lemma tactics_exercise_3 (f : bool -> bool) :
  f true != f false ->
  (forall b, f b = b) \/ (forall b, f b != b).
Proof. (* FILL IN HERE (8 LOC proof) *) Admitted.

Lemma eq_exercise_1 a b c d :
  S a = S b ->
  b != c + c ->
  S c = S d ->
  b != d * 2.
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

Lemma eq_exercise_2 (f : nat -> nat) a :
  f (f a) = f a ->
  f (f (f a)) = f a.
Proof. (* FILL IN HERE (7 LOC proof) *) Admitted.

Fixpoint power_2 (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => 2 * power_2 n'
  end.

Lemma power_2_pos n :
  0 < power_2 n.
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.

(** For this exercise you will also need to find a suitable lemma about [log2]. *)
Lemma log2_power_2_inv n :
  log2 (power_2 n) = n.
Proof. (* FILL IN HERE (5 LOC proof) *) Admitted.

(** ######################################################################### *)
(** * Compact proof scripts *)
(** ######################################################################### *)

(** ** Tacticals / tactic combinators *)

(** Coq supports various tactic combinators (aka "tacticals"). Below we provide
a list of the most common ones (the first two were already covered in week 1):

- [by tac]:               Syntactic suger for [tac; done]
- [try tac]:              Execute [tac] but do nothing if it fails
- [repeat tac]:           Repeatedly execute [tac]
- [do n tac]:             Execute [tac] [n] times
- [tac1 || tac2]:         First execute [tac1], and use [tac2] if [tac1] fails
- [tac1; tac2]:           Execute [tac2] on all subgoals of [tac1]
- [tac1; first tac2]:     Execute [tac2] on the first subgoal of [tac1]
- [tac1; last tac2]:      Execute [tac2] on the last subgoal of [tac1]
- [tac1; [tac2|tac3]]:    Execute [tac2] on the 1st subgoal and [tac3] on the 2nd
- [tac1; [tac2|..|tac3]]: Execute [tac2] on the 1st subgoal and [tac3] on the last

More examples:

- [tac1; [..|tac2|tac3|tac4]]
- [tac1; [tac2|..|tac3|tac4]]
- [tac1; [tac2|tac3|tac4|..]]

See the cheatsheet for more details about these combinators. We will give some
examples and use these combinators throughout this lecture. *)

Lemma plus_S_r n m :
  n + S m = S (n + m).
Proof.
  (** The [ first ] combinator is often used when one subgoal can be solved
  immediately, for example, the base case of a proof by induction. *)
  induction n as [|n' IH]; first done.
  by rewrite /= IH.
Qed.

Definition f (n : nat) : nat :=
  match n with
  | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2
  | n => n
  end.

Lemma f_twice n :
  f (f n) = n.
Proof.
  repeat (done || destruct n as [|n]).
  (** Why does [repeat (destruct n as [|n] || done)] loop? *)
Qed.

(** ** Introduction patterns *)

(** A considerable part of a Coq proof involves bookkeeping to introduce and
eliminate logical connectives, perform case analysis on data types, etc. To
reduce the amount of code that is needed to perform such bookkeeping, Coq has
so called "introduction patterns", which make it possible to unpack multiple
levels of logical connectives in one go. Introduction patterns [pat] can be used
as arguments of many Coq, including but not limited to [intros] and [destruct],
and can be nested. The most important introduction patterns are:

- [ [x H] ]     eliminate [exists x, P]
- [ [H1 H2] ]   eliminate [P /\ Q]
- [ [H1|H2] ]   eliminate [P \/ Q]
- [ [] ]        eliminate [False]
- [ [x y] ]     eliminate a pair [A * B]
- [ [|n] ]      eliminate a natural number
- [ [|] ]       eliminate a Boolean
- [ [->] ]      eliminate [x = y] by substituting [x] with [y]
- [ [<-] ]      eliminate [x = y] by substituting [y] with [x]
- [ [= H1 H2] ] turn [C x1 y1 = C x2 y2] into [x1 = x2] and [y1 = y2] for
                a constructor [C] (works for any arity)
- [ [=] ]       derive a contradiction from [C x1 y2 = C' x2 y2] if [C] and
                [C'] are different constructors (works for any arity)
- [ (x & y & z & ...) ] a shorthand for [ [x [y [z ...]] ]
- [ ...%lemma ] applies the [lemma] to the assumption

Let us take a look at some basic examples. More realistic examples will appear
throughout the lecture. *)

Lemma intro_pattern_example_1 (P1 P2 P3 : Prop) :
  P1 /\ (P2 \/ P3) ->
  (P1 /\ P2) \/ (P1 /\ P3).
Proof.
  intros H.
  (* Without introduction pattens, the proof is quite verbose. We need multiple
  [destruct]s and we need to name auxiliary hypotheses. *)
  destruct H as [H1 Haux].
  destruct Haux as [H2|H3].
Restart.
  intros H.
  (** With introduction patterns we eliminate the [/\] and [\/] in one go. *)
  destruct H as [H1 [H2|H3]].
Restart.
  intros [H1 [H2|H3]]. (** We can also do that as part of [intros]. *)
Abort.

Lemma intro_pattern_example_2 (P1 P2 P3 : nat -> Prop) :
  (exists x y, P1 x /\ P2 x /\ P3 y) ->
  (exists x, P1 x /\ P2 x) /\ (exists y, P3 y).
Proof.
  intros [x [y [H1 [H2 H3]]]]. (** Introduce [->], eliminate [exists] and [/\]. *)
Restart.
  intros (x & y & H1 & H2 & H3). (** The [(x & y & z & ...)] syntax is useful
  to "flatten" the introduction pattern when eliminating many nested [exists]
  and [/\] connectives. *)
Abort.

Lemma intro_pattern_example_3 (P : Prop) :
  P \/ False ->
  P.
Proof.
  intros [H|[]]. (** Perform [False] elimination in the second disjunct. *)
Abort.

Lemma intro_pattern_example_4 (P Q : nat -> Prop) :
  (exists nm : nat * nat, P (fst nm) /\ Q (snd nm)) ->
  exists n m : nat, P n /\ Q m.
Proof.
  intros ([n m] & HP & HQ). (** You can also eliminate data types, e.g., pairs. *)
Abort.

Lemma intro_pattern_example_5 (P : nat -> Prop) n :
  (exists m, n = S m /\ P m) ->
  0 < n /\ P (pred n).
Proof.
  intros (m & -> & HP). (** ... and substitute equalities immediately. *)
Abort.

Lemma intro_pattern_example_6 (P : nat -> Prop) n :
  (exists m, S n = S m /\ P m) ->
  P n.
Proof.
  intros (m & [= Hn] & HP). (** ... and perform [injection]. *)
Abort.

Lemma intro_pattern_example_7 a b c :
  (S a, S a) = (S b, S c) ->
  b + c = 2 * b.
Proof.
  (** We've seen this proof with [simplify_eq] above, here's
  a compact proof with intro patterns. *)
  intros [= <- <-]. lia.
Qed.

Lemma intro_pattern_example_8 n1 n2 k :
  n1 + k <= n2 + k -> n1 <= n2.
Proof.
  intros Hn12%Nat.add_le_mono_r. done. (** We can also apply lemmas (equivalent to [apply ... in]). *)
Qed.

(** ** Evars ("existential variables") *)

(** When applying a lemma, so far all parameters of the lemma had to
be explicitly provided by us. *)
Lemma evar_demo_1 (P Q : nat -> Prop) (m n : nat) :
  (forall n m, P m -> Q n) ->
  P (m * 1024 + n * 256 + 64) -> Q (m * 64 + n * 256 + 1024).
Proof.
  (** That can be quite cumbersome, as in this example. *)
  intros HPQ Hf. apply (HPQ (m * 64 + n * 256 + 1024) (m * 1024 + n * 256 + 64)).
Restart.
  (** We can use [_] to omit values that can be infered from the goal,
  but even that only gets us so far. *)
  intros HPQ Hf. apply (HPQ _ (m * 1024 + n * 256 + 64)).
Restart.
  (** The tactic [eapply] lets us go a lot further:
  instead of having us pick the value for [m] now, we can now defer that choice
  by introducing an *existential variable* [?m]. This is a variable that we can use now
  whose value we only have to precisely fix later. *)
  intros HPQ Hf. eapply HPQ. done.
Qed.

(** Existential variables are particularly convenient when making use of
transitivity: we can avoid stating the element in the middle. *)
Lemma le_mult_2 m : m <= 2*m.
Proof. lia. Qed.
Lemma evar_demo_2 m :
  Nat.sqrt m <= 2 * Nat.sqrt (2 * m).
Proof.
  apply (Nat.le_trans _ (Nat.sqrt (2 * m))).
  - apply Nat.sqrt_le_mono. apply le_mult_2.
  - apply le_mult_2.
Restart.
  eapply Nat.le_trans.
  - apply Nat.sqrt_le_mono, le_mult_2.
  - apply le_mult_2.
Qed.

(** ######################################################################### *)
(** * Exercises about compact proof scripts *)
(** ######################################################################### *)

(** Prove these lemmas as compactly as you can, making use of the
tactics and patterns you learned above.
Some of these are lemmas you have already seen before, but now
we can write the proofs more concisely. *)

Lemma compact_exercise_1 (f : bool -> bool) (b : bool) :
  f (f (f b)) = f b.
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

Lemma compact_exercise_2 n :
  (exists m, (m < 2 /\ S n = S m) \/ (m < 3 /\ n < m)) ->
  n < 2.
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

(* Do this proof twice: once with evars, and once with [%lemma] patterns. *)
Lemma compact_exercise_3 (P : nat -> Prop) n :
  (forall m1 m2, P (m1 + m2) -> P m1) ->
  P (n + 3 + n + 8) -> P n.
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.

Lemma compact_exercise_4 n1 n2 n3 :
  n1 + n2 = n1 + n3 -> n2 = n3.
Proof. (* FILL IN HERE (2 LOC proof) *) Admitted.

Lemma compact_exercise_5 (f : bool -> bool) :
  f true != f false ->
  (forall b, f b = b) \/ (forall b, f b != b).
Proof. (* FILL IN HERE (2 LOC proof) *) Admitted.

(* Hint: Evars will be useful in the following exercise. *)

Lemma compact_exercise_6 {T} (P Q : T -> Prop) (R : Prop) :
  (forall x y, P x -> Q y -> R) ->
  (exists x, P x) -> (exists y, Q y) -> R.
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

(** ######################################################################### *)
(** * Inductive predicates *)
(** ######################################################################### *)

(** We can not only define datatypes (such as [bool] and [nat])
inductively, we can also define *predicates* (and more generally, relations) inductively.
For instance, here is a definition of "even numbers": *)
Inductive even : nat -> Prop :=
| Even0 : even 0
| Even2 : forall n', even n' -> even (2 + n').

(** This creates constructors with the declared types. *)
Check Even0.
Check Even2.

(** Proving [even] is straight-forward, using the constructors. *)
Lemma even_4 : even 4.
Proof.
  apply Even2. apply Even2. apply Even0.
Qed.

(** As an inductive predicate, [even] can be subject to case distinction.
Ever proof of [even n] is either [Even0] of [Even2 n' H] for some [n']
and some [H] proving [even n'].
We can use [destruct] to perform this case distinction in a proof. *)
Lemma even_n n : even n -> n = 0 \/ (exists n', n = S (S n')).
Proof.
  intros [|n' Heven'].
  (** Note that doing case distinction on [even n] "magically" replaces [n]
  by something else in the proof! This is because if [even n] was constructed with
  [Even0], then [n] *must* be [0], and similar for [Even2]. *)
  - left. done.
  - right. exists n'. done.
Qed.

(** The interesting point about inductive predicates as that we can do induction on them.
This exploits that every proof of [even n] is constructed with a finite number of
[Even0] and [Even2]. You can think of this as a tree, where the [Even0] are the leaves
and [Even2] are the inner nodes. (For [even], these inner nodes only ever have a single
child, but we will later encounter inductive predicates where these nodes can have
multiple children.) We are now effectively doing induction over the height of
that tree.

The general induction principle looks as follows:
to show [forall n, even n -> P n], it suffices to show
- [case Even0] P 0
- [case Even2] forall n', even n' -> P n' -> P (2+n')

Coq automatically computes this induction principle from our definition of [even].
Note that in the inductive case, we add *two* to [n'], in contrast to the usual
induction where every step increments by one. This is because we are doing induction
over the [even] proof, not over the [n]. For every layer in the tree that was contructed
to prove [even n], [n] increments by 2, and hence we also get an increment by 2 in the
induction principle. We also learn that [n'] is even in the "step", because
every [Even2] can only have been constructed with an even [n'].
*)

Lemma even_mul2 n :
  even n -> exists k, n = 2*k.
Proof.
  intros Heven. induction Heven as [|n' Heven IH].
  - (** The goal changed, [n] became [0]. *)
    exists 0. lia.
  - (** The goal changed, [n] became [S (S n')].
    We also got some new assumptions: [Heven] and [IH]. *)
    destruct IH as [k EQ]. exists (S k). lia.
Qed.

Lemma not_even_1 : ~even 1.
Proof.
  (** Destructing inductive predicates can sometimes surprisingly not be
  very useful. For instance: *)
  intros Heven. destruct Heven.
  - (** This goal is unprovable! We have no assumption, and have to prove [False].
    What happened? We destructed a proof of [even 1], and as before this will
    replace all occurrences of [1] by [0]. However, there is no [1] anywhere
    else in our proof state, so this changes nothing, and now we are stuck.
    Let's try again. *)
Restart.
  (** The solution is to make sure that we only destruct [even t] when the term [t]
  is a variable. That variable can then be replaced by [0] (or [S (S n')]) to
  give us the information we need. When [t] is not yet a variable, we can use
  [remember t as n] to introduce a new variable [n], together with a proof of [n = t]. *)
  intros Heven. remember 1 as n. destruct Heven.
  - (** Now there is an [n] that can be replaced by [0]:
    [n = 1] becomes [0 = 1]. The proof is finished by [discriminate]. *)
    discriminate.
  - (** Similarly, [n = 1] became [S (S n') = 1], which is a contradiction
    and again we can finish the proof with [discriminate]. *)
    discriminate.
Restart.
  (** The [inversion] tactic performs [remember] and [discriminate] automatically. *)
  intros Heven. inversion Heven.
Qed.

(** ######################################################################### *)
(** * Exercises about inductive predicates *)
(** ######################################################################### *)

(** Hint: The [apply] tactics accepts a [with] clause to allow you to manually
specify instantiations of universal quantifiers. For example, [apply H with (x := v)]
applies to the goal the lemma or hypothesis [H] with [x] instantiated to be [v].
This is a useful alternative to [eapply] when there is not enough information
later in the proof for Coq to determine the value for the evar. *)

(** Here you will need strong induction:
[induction n as [n IH] using lt_wf_ind.].
Remember that you might also have to strengthen the induction hypothesis. *)
Lemma mul2_even k n :
  n = 2*k -> even n.
Proof. (* FILL IN HERE (12 LOC proof) *) Admitted.

(* A number is odd if it is ... *)
Inductive odd : nat -> Prop :=
(* ... 1 or ... *)
| Odd1 : odd 1
(* ... 2 + an odd number. *)
| Odd2 : forall n, odd n -> odd (2 + n).

Lemma even_plus_odd n m :
  even n -> odd m -> odd (n + m).
Proof. (* FILL IN HERE (3 LOC proof) *) Admitted.

Lemma never_both_even_odd n :
  even n -> ~ odd n.
Proof. (* FILL IN HERE (6 LOC proof) *) Admitted.

(* Hint: To prove this lemma, you may find it useful to formulate certain
helper lemmas along the way. *)
Lemma even_or_odd n :
  even n \/ odd n.
Proof. (* FILL IN HERE (15 LOC helpers and 5 LOC proof) *) Admitted.

(** ######################################################################### *)
(** * The list and option data types *)
(** ######################################################################### *)

(** In part 1 we have defined the natural numbers and Booleans as inductive
types in Coq. Now we take a look at the list and option types. An important
difference between natural numbers/Booleans and list/option is that list/option
are polymorphic, i.e., list/option are parametric in the type of elements.

In the module [list_defs] below we give the definition of the [list] and
[option] type and show how the definitions of a number of familiar functions.
All of these definitions are also in Coq's standard library. *)

Module list_defs.
  (** With the [A : Type] syntax we tell Coq that the [list] type is parametric
  in the type [A] of elements. *)
  Inductive list (A : Type) :=
    | nil : list A
    | cons : A -> list A -> list A.

  (** Polymorphism is handled differently in Coq compared to functional
  languages like OCaml and Haskell. The constructors [nil] and [cons] have 1
  and 3 arguments, respectively---i.e., one more argument than you might expect.
  The additional argument is the type [A] of elements. *)

  About nil.  (** [nil : forall A : Type, list A] *)
  About cons. (** [cons : forall A : Type, A -> list A -> list A] *)

  Check cons nat 10 (cons nat 11 (nil nat)).

  (** In most cases Coq can infer the type argument [A] by type checking. For
  example, in the above list, [A] can be derived from the fact that [10] and
  [11] have type [nat]. We instruct Coq to automatically infer type arguments
  using the following commands (in Coq terminology, we say that we make the
  arguments between braces "implicit"): *)

  Arguments nil {_}.
  Arguments cons {_}.

  Check cons 10 (cons 11 nil).

  (** Side note: You can make _any_ argument implicit, including value arguments.
  For example, you can write [Arguments cons {_ _}] to also make the head of
  the list implicit. This is unlikely what you want, since we cannot expect Coq
  to invent values out of thin air. *)

  (** In some cases, we want to explicitly pass an implicit (type) argument.
  We can do so by prefixing a constructor or function name with an [@]. *)

  Check nil. (* [nil : list ?A] *)
  Check (@nil nat). (* [nil : list nat] *)

  (** We define the familiar notations for lists. *)

  Infix "::" := cons.
  Notation "[]" := nil.
  Notation "[ x ]" := (cons x nil).
  Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).

  Check [10; 11].

  (** Now let us define some functions on lists. *)

  (** To define polymorphic functions, we need to add an implicit (i.e.,
  automatically inferred) type argument with syntax [{A}]. *)

  Fixpoint length {A} (xs : list A) : nat :=
    match xs with
    | [] => 0
    | x :: xs => S (length xs)
    end.

  Compute length [10; 11]. (** Gives [2]. *)

  Fixpoint app {A} (xs1 xs2 : list A) : list A :=
    match xs1 with
    | [] => xs2
    | x :: xs1 => x :: app xs1 xs2
    end.

  Infix "++" := app.

  Compute [10; 11] ++ [20; 21]. (** Gives [ [10; 11; 20; 21] ]. *)

  Fixpoint rev {A} (xs : list A) : list A :=
    match xs with
    | [] => []
    | x :: xs => rev xs ++ [x]
    end.

  Compute rev [10; 11; 20; 21]. (** Gives [ [21; 20; 11; 10] ]. *)

  (** The function [concat] takes a list of lists and appends all lists to
  each other. *)

  Fixpoint concat {A} (xss : list (list A)) : list A :=
    match xss with
    | [] => []
    | xs :: xss => xs ++ concat xss
    end.

  Compute concat [[10; 11]; [20; 21]; [30; 31]].
    (** Gives [ [10; 11; 20; 21; 30; 31] ]. *)

  (** Aside from functions that produce data (like another list or a value),
  Coq allows us to define functions that produce propositions. For example, the
  function [In x' xs] defines the proposition that specifies whether an element
  [x'] is in list [xs]. *)

  Fixpoint In {A} (x' : A) (xs : list A) : Prop :=
    match xs with
    | [] => False
    | x :: xs => x = x' \/ In x' xs
    end.

  (** The option data type, which is often used to define partial functions, is
  defined in a similar fashion as the list data type. *)

  Inductive option (A : Type) :=
    | None : option A
    | Some : A -> option A.
  Arguments None {_}.
  Arguments Some {_}.

  (** We use the option type to define the function [nth_error xs i]. This
  function looks up the [i]th element of the list. If the index [i] is out of
  bounds, it returns [None]. *)

  Fixpoint nth_error {A} (xs : list A) (i : nat) : option A :=
    match i, xs with
    | 0, [] => None
    | 0, x :: xs => Some x
    | S i, [] => None
    | S i, x :: xs => nth_error xs i
    end.
End list_defs.

(** Now let us take a look at some proofs about lists. All the tactics that we
have seen (e.g., [simpl], [destruct], [induction], [injection], [discriminate],
[f_equal]) generalize to lists in the obvious way. *)

Lemma app_nil_r {A} (xs : list A) :
  xs ++ [] = xs.
Proof.
  induction xs as [|x xs' IH].
  - (** Base case, [xs = []]. *)
    simpl. reflexivity.
  - (** Inductive case, [xs = x :: xs']. *)
    simpl. rewrite IH.
Restart.
  (** Let us put the material from the beginning of the lecture to practice to
  shorten the proof. Note that we omit the [as] argument of [induction] since
  we do not need to refer to variables ourselves. *)
  induction xs; simpl; congruence.
Qed.

(** The following lemma states that an element [x] is in a list [xs] if there
exists a corresponding index [i] at which we can find [x]. *)

Lemma in_nth_error {A} (xs : list A) x :
  In x xs <-> exists i, nth_error xs i = Some x.
Proof.
  (** Instead of proving both directions of the [<->] individually, let us prove
  both at the same time using a single induction. *)
  induction xs as [|x' xs' IH]; simpl.
  - (** Base case *)
    (** One direction is an immediate contradiction, we use [done]. *)
    split; first done.
    (** Since [nth_error] is defined by pattern matching on both arguments, we
    need to perform a case analysis on the index to obtain a contradiction. We
    can do that concisely by nesting introduction patterns. *)
    intros [[|i] [=]].
  - (** Inductive case *)
    split.
    + intros [->|Hin].
      * by exists 0.
      * (** Note that we can also use [apply] on hypotheses. Additionally, we
        can use [as pat] to immediately perform some operations on the result. *)
        apply IH in Hin as [i Hin].
        by exists (S i).
    +  (* [simplify_eq/=] combines [simplify_eq] with [simpl],
       similar to how [/=] in [rewrite] also means [simpl]. *)
       intros [[|i] Hnth]; simplify_eq/=.
      * by left.
      * right. apply IH. by exists i.
Qed.

(** ######################################################################### *)
(** * Exercises about the list and option data types *)
(** ######################################################################### *)


Lemma app_assoc {A} (xs ys zs : list A) :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

Lemma in_app_iff {A} (xs1 xs2 : list A) x :
  In x (xs1 ++ xs2) <-> In x xs1 \/ In x xs2.
Proof. (* FILL IN HERE (7 LOC proof) *) Admitted.

Lemma length_app {A} (xs1 xs2 : list A) :
  length (xs1 ++ xs2) = length xs1 + length xs2.
Proof. (* FILL IN HERE (1 LOC proof) *) Admitted.

(** To prove the following lemma, you should declare and prove a helper lemma. *)

Lemma rev_rev {A} (xs : list A) :
  rev (rev xs) = xs.
Proof. (* FILL IN HERE (16 LOC helpers and 4 LOC proof) *) Admitted.

(** Hint: Remember that [apply] and [apply ... in] work with bi-implications.
Furthermore, it might come in handy that [rewrite] also supports rewriting with
bi-implication [<->] in addition to equality [=]. *)

Lemma in_rev_iff {A} (xs : list A) x :
  In x (rev xs) <-> In x xs.
Proof. (* FILL IN HERE (4 LOC proof) *) Admitted.

Lemma in_concat_iff {A} (xss : list (list A)) x :
  In x (concat xss) <-> exists xs, In x xs /\ In xs xss.
Proof. (* FILL IN HERE (9 LOC proof) *) Admitted.

Lemma nth_error_Some_iff {A} (l : list A) n x :
  nth_error l n = Some x <->
  exists l1 l2, l = l1 ++ x :: l2 /\ length l1 = n.
Proof. (* FILL IN HERE (6 LOC proof) *) Admitted.
