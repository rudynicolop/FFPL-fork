From ffpl.lib Require Import prelude.
From ffpl.type_systems.stlc_de_bruijn Require Export lang.

(* We declare two notation scopes, one for values and one for expressions.
   Afterwards, we add notations to them, which then do not interfere with
   any existing Coq notations. *)
Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.
Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

(* Values can be embedded into expressions with of_val
   and integers into expressions with LitInt. The following
   coercions allow us to omit the embeddings. With them
   (e1 v2 n3) desugars to (e3 (of_val v2) (LitInt n1)). *)
Coercion of_val : val >-> expr.
Coercion LitInt : Z >-> expr.
Coercion LitIntV : Z >-> val.
Coercion App : expr >-> Funclass.

(* In the expr and val scopes, we want numbers to be interpreted as integers. *)
Number Notation Z Z.of_num_int Z.to_num_int : expr_scope.
Number Notation Z Z.of_num_int Z.to_num_int : val_scope.

(* Notation for de-Bruijn indices *)
Notation "'^' n" := (Var n%nat)
  (at level 8, format "'^' n") : expr_scope.

(* Notation for particular expression.s *)
Notation "e1 + e2" := (Plus e1%E e2%E) : expr_scope.

Notation "'lam:' e" := (Lam e%E)
  (at level 200, e at level 200,
   format "'[' 'lam:'  e ']'") : expr_scope.

Notation "'lam:' e" := (LamV e%E)
  (at level 200, e at level 200,
   format "'[' 'lam:'  e ']'") : val_scope.
