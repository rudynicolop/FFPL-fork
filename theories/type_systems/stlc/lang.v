From stdpp Require Export strings.
From ffpl.lib Require Import prelude.

(** [Z] is Coq's version of the integers.
    All the standard operations, like [+], are defined on it.
    For this file and everything that imports this file, we want
    the notation for [+] but also literals like [42] to be interpreted
    as integers, nor natural numbers:
*)
Global Open Scope Z.

(** * Simply Typed Lambda Calculus *)

(** ** Expressions / Terms. *)
Inductive expr :=
  (* Base lambda calculus *)
  | Var (x : string)
  | Lam (x : string) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | LitInt (n: Z)
  | Plus (e1 e2 : expr).

(** *** Substitution: replace [x] by [es] in [e]. *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | LitInt n => LitInt n
  (* The function [decide] can be used to decide propositions.
    It can only be applied to propositions for which, by type class inference,
    it can be determined that the proposition is decidable. *)
  | Var y => if decide (x = y) then es else Var y
  | Lam y e =>
      Lam y $ if decide (x = y) then e else subst x es e
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | Plus e1 e2 => Plus (subst x es e1) (subst x es e2)
  end.

(** A predicate which holds true whenever an
expression is a value. *)
Definition is_val (e : expr) : Prop :=
  match e with
  | LitInt n => True
  | Lam x e => True
  | _ => False
  end.

(** ** §1.1: Operational Semantics *)

(** *** Small-Step Structural Semantics *)

(* We use right-to-left evaluation order,
   which means in a binary term (e.g., e1 + e2),
   the left side can only be reduced once the right
   side is fully evaluated (i.e., is a value). *)
Inductive step : expr -> expr -> Prop :=
  | StepBeta x e e'  :
    is_val e' ->
    step (App (Lam x e) e') (subst x e' e)
  | StepAppL e1 e1' e2 :
    is_val e2 ->
    step e1 e1' ->
    step (App e1 e2) (App e1' e2)
  | StepAppR e1 e2 e2' :
    step e2 e2' ->
    step (App e1 e2) (App e1 e2')
  | StepPlus (n1 n2 n3 : Z) :
    n1 + n2 = n3 ->
    step (Plus (LitInt n1) (LitInt n2)) (LitInt n3)
  | StepPlusL e1 e1' e2 :
    is_val e2 ->
    step e1 e1' ->
    step (Plus e1 e2) (Plus e1' e2)
  | StepPlusR e1 e2 e2' :
    step e2 e2' ->
    step (Plus e1 e2) (Plus e1 e2').

Module examples.

(** Now we can experiment with our semantics a bit. *)
Example step_1_plus_1 : step (Plus (LitInt 1) (LitInt 1)) (LitInt 2).
Proof. apply StepPlus. lia. Qed.

Definition plus1 := Lam "x" (Plus (Var "x") (LitInt 1)).
Example step_call_plus_1 : step (App plus1 (LitInt 1)) (Plus (LitInt 1) (LitInt 1)).
Proof. apply StepBeta. done. Qed.

(** [step] is just a single reduction step; often we want to talk
about an arbitrary sequence of steps: the "reflexive transitive closure"
of steps, short [rtc]. *)
Definition steps := rtc step.
Example steps_call_plus_1 : steps (App plus1 (LitInt 1)) (LitInt 2).
Proof.
  (** The lemma [rtc_l] lets us take one step and then arbitrary many steps
  after that. [rtc_once] indicates this is the last step we want to take. *)
  eapply rtc_l.
  - apply step_call_plus_1.
  - apply rtc_once, step_1_plus_1.
Qed.

(** Writing down terms like that is way too painful, so we define some notation.
We would like to use [+] for [Plus], but have to be careful not to mix that up with [nat.plus]!
To this end we define a separate *notation scope* that will contain our expression notations. *)
Declare Scope expr_scope.
(** We declare the scope to be abbreviated with %E (we'll see an example of what
that means below). *)
Delimit Scope expr_scope with E.
(** And we declare that things of type [expr] should automatically be parsed
in this scope. *)
Bind Scope expr_scope with expr.

(** Now we can add our notation. *)
Notation "e1 + e2" := (Plus e1 e2) : expr_scope.

(** So we can write... *)
Check (LitInt 1 + LitInt 1)%E.
(** But this is still cumbersome. To get rid of the [LitInt], we declare a *coercion*: *)
Coercion LitInt : Z >-> expr.
(** This means that whenever Coq finds a term of type Z and expects a term of type [expr],
it will insert a call to [LitInt]. It also means [LitInt] will no longer be printed.
This can be quite confusing when you are working on a term and forgot that there are
hidden [LitInt] around! Coercions should be used sparingly. But here it's worth it. *)

Example step_1_plus_1' : step (1 + 1)%E 2.
Proof. apply StepPlus. lia. Qed.

(** Of course we also want notation for lambda terms.
This is a new notation that Coq doesn't already know about so we can choose the "levels",
which defines the relative precedence of keywords and operators. Choosing the right levels
is an art in itself; here we use values that experience shows work well. *)
Notation "'lam:' x , e" := (Lam x e%E)
  (at level 200, x at level 1, e at level 200).

(** This already looks much better. *)
Print plus1.
(** But the [Var] is still ugly. Let's make [Var] a coercion, too, so
we don't have to read or write it, matching what we do on paper. *)
Coercion Var : string >-> expr.
Print plus1.

(** Now we can write the example as... *)
Definition plus1' := lam: "x", "x" + 1.
Example step_call_plus_1' : step (App plus1 1) (1 + 1).
Proof. apply StepBeta. done. Qed.

(** As the very last step to match the notation on paper,
we get rid of the [App] by marking it as a "Funclass" coercion.
This means whenever Coq sees an [expr] and expected a function,
it will apply the coercion. *)
Coercion App : expr >-> Funclass.
Check step (plus1 1) (1 + 1).
(** Why does this work? [plus1] is an [expr], and when we write [plus1 1], Coq
sees that it needs [plus1] to be a function that it can apply [1] to. It applies
the coercion, so the candidate term is now [(App plus1) 1], which is the same as
[App plus1 1]. We are not quite done yet since [1] is a [Z] where we need an
[expr], so we apply the [LitInt] coercion and end up with [App plus1 (LitInt 1)],
which is the final term. *)

(** Ending the module here also removes our notations; they are later re-added in [notation.v]. *)
End examples.

(** *** Big-Step Semantics *)

(** To formalize big-step semantics, we have to define not just a predicate
[is_val] but an actual Coq *type* of values, [val]. We also define functions to
convert between expressions and values and show their basic properties, and
their relationship with [is_val]. *)

Inductive val :=
  | LitIntV (n: Z)
  | LamV (x : string) (e : expr).

(* Injections into expr *)
Definition of_val (v : val) : expr :=
  match v with
  | LitIntV n => LitInt n
  | LamV x e => Lam x e
  end.

(* Try to make an expr into a val *)
Definition to_val (e : expr) : option val :=
  match e with
  | LitInt n => Some (LitIntV n)
  | Lam x e => Some (LamV x e)
  | _ => None
  end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  destruct v; simpl; reflexivity.
Qed.

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof.
  destruct e; simpl; try congruence.
  all: injection 1 as <-; simpl; reflexivity.
Qed.

(** We can rewrite terms that are values into the form [of_val v]. *)
Lemma is_val_make_val e : is_val e -> exists v, e = of_val v.
Proof.
  intros He.
  (* [cut] is "it suffices to show". *)
  cut (exists v, to_val e = Some v).
  { intros [v ?]. exists v. symmetry. apply of_to_val. done. }
  (* Handle the rest. Many cases are simple contradictions. *)
  destruct e; simpl; try contradiction.
  (* We could prove the remaining goals individually by hand now, but then we
  have to manually state the witness that proves the existential. Instead we can
  have Coq infer the witness by using evars (existential variables) that we have
  already seen before with [eapply]: The [eexists] tactic turns the quantified
  variable into an evar. *)
  all: eexists; done.
Qed.

(** In fact, [is_val] is fully characterized by these new operations. *)
Lemma is_val_spec e : is_val e <-> exists v, e = of_val v.
Proof.
  split; first by apply is_val_make_val.
  intros [v ->]. destruct v; done.
Qed.

(** Now we are finally ready to define the actual big-step evaluation relation. *)

Inductive big_step : expr -> val -> Prop :=
  | BsLitInt (n : Z) :
      big_step (LitInt n) (LitIntV n)
  | BsLam (x : string) (e : expr) :
      big_step (Lam x e) (LamV x e)
  | BsPlus e1 e2 (z1 z2 : Z) :
      big_step e1 (LitIntV z1) ->
      big_step e2 (LitIntV z2) ->
      big_step (Plus e1 e2) (LitIntV (z1 + z2))%Z
  | BisApp e1 e2 x e v2 v :
      big_step e1 (LamV x e) ->
      big_step e2 v2 ->
      big_step (subst x (of_val v2) e) v ->
      big_step (App e1 e2) v
.

(** We can show that values behave the way they should. *)
Lemma big_step_vals (v : val) : big_step (of_val v) v.
Proof.
  induction v.
  - apply BsLitInt.
  - apply BsLam.
Restart.
  (** We can make this proof shorter with the [constructor] tactic, which
  works when the goal is an inductive type or predicate and tries to apply
  all its constructors. *)
  induction v; constructor.
Qed.

Lemma big_step_inv_vals (v w : val) : big_step (of_val v) w -> v = w.
Proof.
  (** [inversion 1] means "do inversion on the first assumption in the goal",
  i.e., it is the same as [intros H; inversion H]. *)
  destruct v; inversion 1; congruence.
Qed.

(** Big-step semantics implies small-step semantics.
    This needs some helper lemmas. *)

Lemma rtc_step_app_l e1 e1' e2:
  rtc step e1 e1' -> is_val e2 -> rtc step (App e1 e2) (App e1' e2).
Proof.
  (** [induction] also supports numeric arguments to do induction
  in something that is still in the goal. *)
  induction 1 as [|e1 e1' e1'' Hstep Hsteps IH].
  { intros. apply rtc_refl. }
  intros He. eapply rtc_l.
  - econstructor; eassumption.
  - eapply IH. assumption.
Qed.

(** We could now write that proof script a few more times for the other lemmas,
but this is getting tedious. Let's make Coq help us. Basically all we needed to
prove the lemma was
- an initial induction
- applying a bunch of other lemmas
- making use of assumptions.

This is exactly the kind of proof that [eauto] can automate. [eauto] works with
a database of lemmas it knows to apply. So let's add the lemmas we need.
[Hint Constructor] adds all constructors of an inductive type or predicate as
lemmas. [core] here is the name of the hint database; [eauto] uses the [core]
database by default. #[export] means that whoever imports this file
will also import the hints. *)
#[export] Hint Constructors rtc step : core.

(** Now the proof proceeds almost fully automatically!
[eauto] always takes into account lemmas in the local context, which is how it is able
to automatically apply the induction hypothesis. *)
Lemma rtc_step_app_r e1 e2 e2':
  rtc step e2 e2' -> rtc step (App e1 e2) (App e1 e2').
Proof.
  induction 1; eauto.
Qed.

Lemma rtc_step_plus_l e1 e1' e2:
  rtc step e1 e1' -> is_val e2 -> rtc step (Plus e1 e2) (Plus e1' e2).
Proof.
  induction 1; eauto.
Qed.

Lemma rtc_step_plus_r e1 e2 e2':
  rtc step e2 e2' -> rtc step (Plus e1 e2) (Plus e1 e2').
Proof.
  induction 1; eauto.
Qed.

(** For this proof we tell [eauto] about another lemma that we will need:
showing that [of_val v] is always a value. *)
Lemma is_val_of_val v : is_val (of_val v).
Proof.
  apply is_val_spec. eexists. done.
Qed.
(* [Hint Resolve] adds an individual lemma to the hint database. *)
#[export] Hint Resolve is_val_of_val : core.

Lemma big_step_step e v :
  big_step e v -> rtc step e (of_val v).
(* CLASS *) Proof.
  induction 1 as [ | | e1 e2 v1 v2 H1 IH1 H2 IH2 | e1 e2 x e v2 v H1 IH1 H2 IH2 H3 IH3].
  - constructor.
  - constructor.
  - etransitivity. { eapply rtc_step_plus_r; eauto. }
    etransitivity. { eapply rtc_step_plus_l; eauto. }
    eapply rtc_l. { apply StepPlus; done. } done.
  - etransitivity. { eapply rtc_step_app_r; eauto. }
    etransitivity. { eapply rtc_step_app_l; eauto. }
    eapply rtc_l. { simpl. econstructor. eauto. }
    done.
Qed.

(** The opposite direction will be an exercise. *)

(** *** Contextual Semantics *)

(** * Base reduction *)
Inductive base_step : expr -> expr -> Prop :=
  | BetaS x e1 e2 e' :
     is_val e2 ->
     e' = subst x e2 e1 ->
     base_step (App (Lam x e1) e2) e'
  | PlusS e1 e2 (n1 n2 n3 : Z):
     e1 = (LitInt n1) ->
     e2 = (LitInt n2) ->
     (n1 + n2)%Z = n3 ->
     base_step (Plus e1 e2) (LitInt n3).

(** * Evaluation contexts *)

(** On paper, we defined evaluation contexts roughly like this. *)
Module ectx_on_paper.
Inductive ectx :=
  | HoleCtx
  | AppLCtx (K : ectx) (v2 : val)
  | AppRCtx (e1 : expr) (K : ectx)
  | PlusLCtx (K : ectx) (v2 : val)
  | PlusRCtx (e1 : expr) (K : ectx).

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | AppLCtx K v2 => App (fill K e) (of_val v2)
  | AppRCtx e1 K => App e1 (fill K e)
  | PlusLCtx K v2 => Plus (fill K e) (of_val v2)
  | PlusRCtx e1 K => Plus e1 (fill K e)
  end.
End ectx_on_paper.

(** However, it turns out that for a Coq formalization, it helps a lot to follow a slightly different approach.
We observe that [ectx] has exactly one constructor without any arguments ([HoleCtx]), and all other
constructors have exactly one [ectx] recursive argument. In other words, this is a list!
Instead of re-defining a list type as part of our [ectx] definition, we define a type of
evaluation context *items* and then let [ectx := list ectx_item]. *)
Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | PlusLCtx (v2 : val)
  | PlusRCtx (e1 : expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | PlusLCtx v2 => Plus e (of_val v2)
  | PlusRCtx e1 => Plus e1 e
  end.

Definition ectx := list ectx_item.
Definition fill (K : ectx) (e : expr) : expr := foldl (λ e Ki, fill_item Ki e) e K.

Module ectx_on_paper_comparison.
(** This version of [ectx] behaves exactly as we would expect from the on-paper
definition. *)

Definition ectx1_on_paper := ectx_on_paper.AppLCtx ectx_on_paper.HoleCtx (LitIntV 1).
Compute (ectx_on_paper.fill ectx1_on_paper examples.plus1).
Definition ectx1 := [AppLCtx (LitIntV 1)].
Compute (fill ectx1 examples.plus1).

Example compare1 :
  ectx_on_paper.fill ectx1_on_paper examples.plus1 = fill ectx1 examples.plus1.
Proof. reflexivity. Qed.

(** The one surprising point is that for list-based contexts, we choose to write
them "backwards", with the innermost context item first. This is caused by us
using [foldl] in the definition of [fill], which processes the first list
element first. *)

Definition ectx2_on_paper :=
  ectx_on_paper.PlusRCtx (LitInt 40) (ectx_on_paper.AppLCtx ectx_on_paper.HoleCtx (LitIntV 1)).
Compute (ectx_on_paper.fill ectx2_on_paper examples.plus1).
Definition ectx2 := [AppLCtx (LitIntV 1); PlusRCtx (LitInt 40)].
Compute (fill ectx2 examples.plus1).

Example compare2 :
  ectx_on_paper.fill ectx2_on_paper examples.plus1 = fill ectx2 examples.plus1.
Proof. reflexivity. Qed.

End ectx_on_paper_comparison.

(** Composition of contexts.
This is where using a list starts paying off.
Remember that the innermost items [Ki] go first. *)
Definition comp_ectx (Ko Ki : ectx) := Ki ++ Ko.
(** This is Lemma 2 in the lecture notes. Since we used lists to define [ectx],
we can use use standard list lemmas instead of doing our own induction. *)
Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. symmetry. apply foldl_app. Qed.

(* If you are curious why we chose [foldl] over [foldr], it is
because that makes the following lemma true by [reflexivity],
without any rewriting: *)
Example the_reason_for_foldl (Ki : ectx_item) (K : ectx) e :
  fill K (fill [Ki] e) = fill (comp_ectx K [Ki]) e.
Proof. reflexivity. Qed.
(* If we had used [foldr], this would need a rewrite with [foldr_app].
For engineering proofs and tactics on top of this, having "the right"
definitional equalities can be very useful, and that's why we prefer
[foldl] for [fill]. *)

Definition empty_ectx : ectx := [].
Lemma fill_empty e : fill empty_ectx e = e.
Proof. done. Qed.

(** * Contextual step relation *)

Inductive contextual_step (e1 : expr) (e2 : expr) : Prop :=
  EctxStep K e1' e2' :
    e1 = fill K e1' ->
    e2 = fill K e2' ->
    base_step e1' e2' ->
    contextual_step e1 e2.

(** Basic lemmas about the contextual semantics *)

Lemma base_contextual_step e1 e2 :
  base_step e1 e2 -> contextual_step e1 e2.
Proof. apply EctxStep with empty_ectx; by rewrite ?fill_empty. Qed.

(* This is the "context lifting" lemma (Lemma 1 in the lecture notes).  *)
Lemma fill_contextual_step K e1 e2 :
  contextual_step e1 e2 -> contextual_step (fill K e1) (fill K e2).
(* CLASS *) Proof.
  destruct 1 as [K' e1' e2' -> ->].
  rewrite !fill_comp. by econstructor.
Qed.

Lemma fill_contextual_step_rtc K e1 e2 :
  rtc contextual_step e1 e2 -> rtc contextual_step (fill K e1) (fill K e2).
(* REMOVE *) Proof.
  induction 1.
  - done.
  - eapply rtc_l.
    * by apply fill_contextual_step.
    * done.
Qed.

(** Contextual semantics implies structural semantics *)
Lemma base_step_step e1 e2 :
  base_step e1 e2 -> step e1 e2.
(* REMOVE *) Proof.
  destruct 1; subst.
  - eauto.
  - by econstructor.
Qed.

Lemma fill_step K e1 e2 :
  step e1 e2 -> step (fill K e1) (fill K e2).
(* REMOVE *) Proof.
  induction K as [|Ki K IH] in e1, e2 |- *; first done.
  destruct Ki; simpl; eauto.
Qed.

Lemma contextual_step_step e1 e2 :
  contextual_step e1 e2 -> step e1 e2.
(* REMOVE *) Proof.
  destruct 1 as [K h1 h2 -> -> Hstep].
  eapply fill_step, base_step_step, Hstep.
Qed.

(* We have added the constructors of [step] as [eauto] hints,
let's also do that for the other operational semantics. *)
#[export] Hint Constructors big_step : core.
#[export] Hint Constructors base_step : core.
#[export] Hint Constructors contextual_step : core.
