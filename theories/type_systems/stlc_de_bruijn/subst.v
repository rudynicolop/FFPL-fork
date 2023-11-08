From ffpl.lib Require Import prelude.
From ffpl.type_systems.stlc_de_bruijn Require Import lang notation.

(* Autosubst magically defined a substitution function for us.
Let's explore it with some examples. *)
Definition e1 : expr := ^0 + 1. (* x + 1 *)
Compute e1.[LitInt 2/].

Definition e2 : expr := lam: e1. (* lam: x, x + 1 *)
Compute e2.[LitInt 2/].

(* Things get intersting when we substitute under binders.
Substituting closed terms works pretty directly. *)
Definition e3 : expr := lam: ^1. (* lam: x, y. *)
Compute e3.[LitInt 2/].
Compute e3.[e2/].

(* But when we substitute an open term... *)
Compute e3.[e1/].
(* ... the free variables need to be updated since they are now
below more binders! The "^0" in [e1] changes to "^1" since it must
now "skip over" the "lam:" in [e3]. *)

(* When there are multiple free variables in a term, substituting one "shifts" the others down. *)
Compute (^0 + ^1)%E.[LitInt 4/].
(* Now that ^0 is gone, the former ^1 is the "first" variable. *)

(* With de-Bruijn indices, we typically use "parallel substitution" as the primitive building block.
We previously encountered parallel substitution when defining the logical relation.
A parallel substitution [sigma] has type [var -> expr], and the operation [e.[sigma]]
applies [sigma] everywhere in [e]. This is like our previous [subst_map], except that
it is a *total* function: all variables must be mapped to some term.
Variables that we want to leave unchanged can just map to themselves.

To define substitution of the "first" variable (^0) with some term [e], we construct
a suitable parallel substitution: *)
Definition subst_from_single e : var -> expr := fun n =>
  match n with
  | O => e
  (* Everything else gets decremented by one since the first variable is gone! *)
  | S n => Var n
  end.
(* We can show that this is equivalent to what autosubst does. *)
Lemma subst_from_single_correct e1 e2 :
  e1.[subst_from_single e2] = e1.[e2/].
Proof. reflexivity. Qed.

(* Parallel substitution is defined by the following equations. *)
Lemma subst_plus sigma (e1 e2 : expr) :
  (e1 + e2)%E.[sigma] = (e1.[sigma] + e2.[sigma])%E.
Proof. reflexivity. Qed.
Lemma subst_int sigma (n : Z) :
  (LitInt n).[sigma] = LitInt n.
Proof. reflexivity. Qed.
Lemma subst_app sigma (e1 e2 : expr) :
  (e1 e2).[sigma] = e1.[sigma] e2.[sigma].
Proof. reflexivity. Qed.
Lemma subst_var sigma (x : var) :
  (Var x).[sigma] = sigma x.
Proof. reflexivity. Qed.
(* So far this is just structural recursion over the term,
looking up variables when we reach them. Things get interesting
when we have to traverse below a binder: we need to "shift"
the substitution by one. Inside this lambda, [0] needs to remain unchanged
(since it refers to the binder we just went through), and everything else
needs to account for the fact that it is now under one more lambda. *)
Definition subst_up (sigma : var -> expr) : var -> expr := fun n =>
  match n with
  | O => Var O
  | S n => (sigma n).[fun m => Var (S m)]
  end.
Lemma subst_lam sigma e :
  (Lam e).[sigma] = Lam (e.[subst_up sigma]).
Proof.
  (* This time we need to unfold some autosubst internals to show that
  this is really the same thing. *)
  asimpl. f_equal. f_equal. f_ext. intros [|x]; simpl.
  - reflexivity.
  - asimpl. reflexivity.
Qed.

(* There is just one problem with this definition: it is recursive! In
[subst_up], we used substitution, but we are currently trying to *define*
substitution. Resolving this recursion involves introducing a notion of
"renamings" of type [var -> var] and first defining how to substitute renamings
before we can define how to apply full substitutions. [subst_up] can be defined
using just renamins, and renamings can be defined without [subst_up] (they need
a [ren_up], but that one can be defined directly without needing any kind of
substitution). It's all a bit cumbersome, but lucky enough, we don't have to
worry about this -- Autosubst does all that work for us.

The upshot is that the definition given above *is* well-formed, it just takes a
bit of work to convince Coq of that fact. Conveniently, we don't have to do that
work. *)
