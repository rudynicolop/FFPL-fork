From stdpp Require Import gmap base relations.
From ffpl.lib Require Import prelude.
From ffpl.lib Require Export debruijn.
From ffpl.type_systems.systemf Require Import lang notation types bigstep logrel tactics.
From Equations Require Import Equations.

(** * Existential types and invariants *)
Implicit Types
  (Delta : nat)
  (Gamma : typing_context)
  (v : val)
  (alpha : var)
  (e : expr)
  (A : type).

(** Here, we take the approach of encoding [assert],
  instead of adding it as a primitive to the language.
  This saves us from adding it to all of the existing proofs.
  But clearly it has the same reduction behavior.
 *)

Definition assert (e : expr) : expr :=
  if: e then #LitUnit else (#0 #0).
Lemma assert_true : rtc contextual_step (assert #true) (#())%E.
Proof.
  econstructor.
  { eapply base_contextual_step. constructor. }
  constructor.
Qed.
Lemma assert_false : rtc contextual_step (assert #false) (#0 #0)%E.
Proof.
  econstructor. { eapply base_contextual_step. econstructor. }
  constructor.
Qed.

Definition Or (e1 e2 : expr) : expr :=
  if: e1 then #true else e2.
Definition And (e1 e2 : expr) : expr :=
  if: e1 then e2 else #false.
Notation "e1 '||' e2" := (Or e1 e2) : expr_scope.
Notation "e1 '&&' e2" := (And e1 e2) : expr_scope.

(** *** BIT *)
(* exists alpha, { bit : alpha, flip : alpha -> alpha, get : alpha -> bool } *)
Definition BIT : type := exists: (^0 * (^0 -> ^0)) * (^0 -> Bool).

Definition MyBit_safe : val :=
  pack (#0,              (* bit *)
        lam: #1 - ^0,    (* flip *)
        lam: #0 < ^0).   (* get *)

Lemma MyBit_typed n Gamma :
  TY n; Gamma |- of_val MyBit_safe : BIT.
Proof. eapply (type_pack _ _ _ Int); repeat econstructor. Qed.

Definition MyBit_unsafe : val :=
  pack (#0,                                                     (* bit *)
        lam: let: assert ((^0 = #0) || (^0 = #1)) in #1 - ^1,   (* flip *)
        lam: let: assert ((^0 = #0) || (^0 = #1)) in #0 < ^1).  (* get *)

Lemma MyBit_unsafe_sem_typed delta :
  sem_val_rel BIT delta MyBit_unsafe.
Proof.
  unfold BIT. simp type_interp.
  eexists. split; first done.
  set tau : sem_type := (fun x => x = #0 \/ x = #1).
  exists tau.
  simp type_interp. eexists _, _. split; first done. split.
  1: simp type_interp; eexists _, _; split; first done; split.
  - (* bit *) simp type_interp. simpl. by left.
  - (* flip *) simp type_interp. eexists _. split; first done.
    intros v'. simp type_interp; simpl.
    (* Note: this part of the proof is a bit different from the paper version, as we directly do a case split. *)
    intros [-> | ->].
    + exists #1. split.
      * bs_steps_det. eapply bs_if_true; bs_steps_det. eapply bs_if_true; bs_steps_det.
      * simp type_interp. simpl. by right.
    + exists #0. split.
      * bs_steps_det. eapply bs_if_true; bs_steps_det. eapply bs_if_false; bs_steps_det.
      * simp type_interp. simpl. by left.
  - (* get *) simp type_interp. eexists _. split; first done.
    intros v'. simp type_interp; simpl. intros [-> | ->].
    + exists #false. split.
      * bs_steps_det. eapply bs_if_true; bs_steps_det. eapply bs_if_true; bs_steps_det.
      * simp type_interp. simpl. eauto.
    + exists #true. split.
      * bs_steps_det. eapply bs_if_true; bs_steps_det. eapply bs_if_false; bs_steps_det.
      * simp type_interp. simpl. eauto.
Qed.

(** It follows that any term [e] that is syntactically well-typed (which can be
checked automatically!) and uses some free variable of type [BIT], will run
safely when that variable is replaced by our unsafe code. *)
Lemma MyBit_unsafe_user_safe (e : expr) A :
  TY 0; [BIT] |- e : A ->
  safe (e.[of_val MyBit_unsafe/]).
Proof.
  intros He. eapply sem_expr_rel_safe, sem_type_subst.
  - eapply (MyBit_unsafe_sem_typed delta_emp).
  - eapply sem_soundness. done.
Qed.
