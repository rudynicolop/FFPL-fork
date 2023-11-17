From stdpp Require Import base gmap strings pretty.
From ffpl.type_systems.stlc_de_bruijn Require Import lang.
From ffpl.type_systems.stlc Require Import lang notation.

(* Use natural numbers (not integers) by default in this file. *)
Local Open Scope nat.

(* We imported two [expr] types now (from [stlc.lang] and
[stlc_de_bruijn.lang]), and the notation scope [E] currently refers to the
expressions with named variables. Set up notation again for expressions with De
Bruijn variables using scope name [EdB] to disambiguate, so that we can use
notation to write both types of expressions. *)
Declare Scope expr_scope_dB.
Delimit Scope expr_scope_dB with EdB.
Bind Scope expr_scope_dB with stlc_de_bruijn.lang.expr.
Coercion stlc_de_bruijn.lang.LitInt : Z >-> stlc_de_bruijn.lang.expr.
Coercion stlc_de_bruijn.lang.App : stlc_de_bruijn.lang.expr >-> Funclass.
Number Notation Z Z.of_num_int Z.to_num_int : expr_scope_dB.
Notation "'^' n" := (stlc_de_bruijn.lang.Var n%nat)
  (at level 8, format "'^' n") : expr_scope_dB.
Notation "e1 + e2" := (stlc_de_bruijn.lang.Plus e1%EdB e2%EdB) : expr_scope_dB.
Notation "'lam_dB:' e" := (stlc_de_bruijn.lang.Lam e%EdB)
  (at level 200, e at level 200,
   format "'[' 'lam_dB:'  e ']'") : expr_scope_dB.

(* Helper function for [named_to_debruijn]. Converts a closed term with named
binders to a closed term with De Bruijn indexing. The map [m] is needed to keep track of
binders "above" us: which binders refer to which name. [None] should be
returned when the provided term [e] refers to variables that are not in [m]
(unbound/free variables). *)
(* HINT: Use [m !! x] to look up a key in a map, and [<[x := 0]> m] to insert a
new key (or change an existing key). To increment every value of a map, use [S
<$> m]. To explain, the meaning of [<$>] is [fmap], so [S <$> m] means "apply
[S] (incrementation) to every value in the map [m]". *)
Fixpoint named_to_debruijn' (m: gmap string nat) (e : stlc.lang.expr) : option stlc_de_bruijn.lang.expr :=
  None.

Definition named_to_debruijn e := named_to_debruijn' empty e.

(* Some examples to demonstrate that it works *)
Example named_to_debruijn_ex1 :
  named_to_debruijn (lam: "x", "x")%E = Some (lam_dB: ^0)%EdB.
Proof. Admitted.
Example named_to_debruijn_ex2 :
  named_to_debruijn (lam: "x", lam: "y", "x" + "y" + "x")%E = Some (lam_dB: (lam_dB: ^1 + ^0 + ^1))%EdB.
Proof. Admitted.
Example named_to_debruijn_ex3 :
  named_to_debruijn (lam: "x", (lam: "y", "x") 0 + "x")%E = Some (lam_dB: (lam_dB: ^1) 0 + ^0)%EdB.
Proof. Admitted.
Example named_to_debruijn_ex4 :
  named_to_debruijn (lam: "x", (lam: "x", "x"))%E = Some (lam_dB: (lam_dB: ^0))%EdB.
Proof. Admitted.

(* Helper function for [debruijn_to_named]. [depth] tracks the number of
lambdas that are "above" us. [None] should be returned when [e] refers to De
Bruijn indices that are greater than or equal to [depth] (unbound variables). *)
(* HINT: The function [pretty] can be used to convert [nat] to [string] in its
decimal representation. *)
Fixpoint debruijn_to_named' (depth : nat) (e : stlc_de_bruijn.lang.expr) : option stlc.lang.expr :=
  None.

(* Converts a closed term with De Bruijn indexing to a closed term with named binders. *)
Definition debruijn_to_named (e : stlc_de_bruijn.lang.expr) : option stlc.lang.expr :=
  debruijn_to_named' 0 e.

(* More examples. Here [<$>] is the "map" operation that applies a function
below [option]. In other words, if [f : A -> B], then [f <$> x] works on
[x : option A] and returns [option B]. *)
Compute debruijn_to_named <$> named_to_debruijn (lam: "x", lam: "y", "x" + "y" + "x")%E.
Compute debruijn_to_named <$> named_to_debruijn (lam: "x", (lam: "y", "x") 0 + "x")%E.
Compute debruijn_to_named <$> named_to_debruijn (lam: "x", (lam: "x", "x") 0 + "x")%E.
