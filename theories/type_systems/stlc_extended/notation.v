From ffpl.lib Require Import prelude.
From ffpl.type_systems.stlc_extended Require Export lang.

(* We declare two notation scopes, one for values and one for expressions.
   Afterwards, we add notations to them, which then do not interfere with
   any existing Coq notations. *)
Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.
Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

(* Automatically embed integers into expressions *)
Coercion LitInt : Z >-> expr.
Coercion LitIntV : Z >-> val.
(* Automatically turn strings into variables. *)
Coercion Var : string >-> expr.
(* Make [e1 e2] be short for [App e1 e2]. *)
Coercion App : expr >-> Funclass.

(* In the expr and val scopes, we want numbers to be interpreted as integers. *)
Number Notation Z Z.of_num_int Z.to_num_int : expr_scope.
Number Notation Z Z.of_num_int Z.to_num_int : val_scope.

(* Notation for particular expression.s *)
Notation "e1 + e2" := (Plus e1%E e2%E) : expr_scope.

(* The breaking point '/  ' makes sure that the body of the lam: is indented
by two spaces in case the whole lam: does not fit on a single line. *)
Notation "'lam:' x , e" := (Lam x e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'lam:'  x ,  '/  ' e ']'") : expr_scope.
Notation "'lam:' x y .. z , e" := (Lam x (Lam y .. (Lam z e%E) ..))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'lam:'  x  y  ..  z ,  '/  ' e ']'") : expr_scope.

Notation "'lam:' x , e" := (LamV x e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'lam:'  x ,  '/  ' e ']'") : val_scope.
Notation "'lam:' x y .. z , e" := (LamV x (Lam y .. (Lam z e%E) .. ))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'lam:'  x  y  ..  z ,  '/  ' e ']'") : val_scope.
