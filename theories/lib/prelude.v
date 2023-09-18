(** This file provides support for using std++ in combination with the ssreflect
tactics. It patches up some global options of ssreflect. *)
From Coq.ssr Require Export ssreflect.
From stdpp Require Export prelude.

(** Restore Coq's normal "if" scope, ssr redefines it. *)
Global Open Scope general_if_scope.

(** See Coq issue #5706 *)
Export Set SsrOldRewriteGoalsOrder.

(** Overwrite ssr's [done] tactic with ours *)
Ltac done := stdpp.tactics.done.

(** We also want the options stdpp has. *)
From stdpp Require Export options.

(** Configure the default [Section] behavior. *)
Export Set Default Proof Using "Type*".

(** ASCII notation for std++ operations *)
Notation "x '!=' y" := (~(x = y)) (at level 70, only parsing) : stdpp_scope.
Notation "m >>= f" := (mbind f m) (at level 60, right associativity) : stdpp_scope.

Infix "`elem`" := elem_of (at level 70, only parsing) : stdpp_scope.
Infix "`union`" := union (at level 50, left associativity, only parsing) : stdpp_scope.
Infix "`intersection`" := intersection (at level 40, only parsing) : stdpp_scope.
Infix "`difference`" := difference (at level 40, left associativity) : stdpp_scope.
Infix "`subseteq`" := subseteq (at level 70, only parsing) : stdpp_scope.

(** Backporting of some lemmas and tactics that were added to std++ more recently. *)
Lemma union_Some {A} (mx my : option A) z :
  mx `union` my = Some z <-> mx = Some z \/ (mx = None /\ my = Some z).
Proof. destruct mx, my; naive_solver. Qed.
Lemma union_Some_l {A} x (my : option A) :
  Some x `union` my = Some x.
Proof. destruct my; done. Qed.
Lemma union_Some_r {A} (mx : option A) y :
  mx `union` Some y = Some (default y mx).
Proof. destruct mx; done. Qed.
Lemma union_None {A} (mx my : option A) :
  mx `union` my = None <-> mx = None /\ my = None.
Proof. destruct mx, my; naive_solver. Qed.
Lemma union_is_Some {A} (mx my : option A) :
  is_Some (mx `union` my) <-> is_Some mx \/ is_Some my.
Proof. destruct mx, my; naive_solver. Qed.

Global Instance option_union_left_id {A} : LeftId (=@{option A}) None union.
Proof. by intros [?|]. Qed.
Global Instance option_union_right_id {A} : RightId (=@{option A}) None union.
Proof. by intros [?|]. Qed.

Ltac tc_solve := solve [once (typeclasses eauto)].
