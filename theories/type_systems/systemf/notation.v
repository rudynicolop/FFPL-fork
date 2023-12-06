From ffpl.type_systems.systemf Require Export lang.

(* Automatically embed integers and booleans into literals *)
Coercion LitInt : Z >-> base_lit.
Coercion LitBool : bool >-> base_lit.
(* Make [e1 e2] be short for [App e1 e2]. *)
Coercion App : expr >-> Funclass.

(* Notation for de-Bruijn indices *)
Notation "'^' n" := (Var n%nat)
  (at level 8, format "'^' n") : expr_scope.

(** In the expr and val scopes, we want numbers to be interpreted as integers. *)
Number Notation Z Z.of_num_int Z.to_num_int : expr_scope.
Number Notation Z Z.of_num_int Z.to_num_int : val_scope.

(** Define some derived forms. *)
Notation Let e1 e2 := (App (Lam e2) e1) (only parsing).

(* No scope for the value literal notation, does not conflict and scope is often
not inferred properly. *)
Notation "# l" := (LitV l%Z%V%stdpp) (at level 8, format "# l").
Notation "# l" := (Lit l%Z%E%stdpp) (at level 8, format "# l") : expr_scope.

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (PairV .. (PairV e1 e2) .. en) : val_scope.

Notation "()" := LitUnit : val_scope.
Notation "()" := LitUnit : expr_scope.

Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E) : expr_scope.
Notation "e1 * e2" := (BinOp MultOp e1%E e2%E) : expr_scope.
Notation "e1 <= e2" := (BinOp LeOp e1%E e2%E) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E) : expr_scope.

(*Notation "~ e" := (UnOp NegOp e%E) (at level 75, right associativity) : expr_scope.*)

Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.

Notation "'lam:' e" := (Lam e%E)
  (at level 200, e at level 200,
   format "'[' 'lam:'  e ']'") : expr_scope.

Notation "'lam:' e" := (LamV e%E)
  (at level 200, e at level 200,
   format "'[' 'lam:'  e ']'") : val_scope.

Notation "'let:' e1 'in' e2" := (Let e1%E e2%E)
  (at level 200, e1, e2 at level 200,
   format "'[' 'let:'  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Notation "'Lam:' e" := (TLam e%E)
  (at level 200, e at level 200,
    format "'[' 'Lam:'  e ']'") : expr_scope.
Notation "'Lam:' e" := (TLamV e%E)
  (at level 200, e at level 200,
    format "'[' 'Lam:'  e ']'") : val_scope.

(* the [e] always needs to be paranthesized, due to the level
   (chosen to make this cooperate with the [App] coercion) *)
Notation "e '<>'" := (TApp e%E)
  (at level 10) : expr_scope.
(*Check ((Lam:, #4) <>)%E.*)
(*Check (((lam: "x", "x") #5) <>)%E.*)

Notation "'pack' e" := (Pack e%E)
  (at level 200, e at level 200) : expr_scope.
Notation "'pack' v" := (PackV v%V)
  (at level 200, v at level 200) : val_scope.
Notation "'unpack'  e1  'in'  e2" := (Unpack e1%E e2%E)
  (at level 200, e1, e2 at level 200) : expr_scope.
