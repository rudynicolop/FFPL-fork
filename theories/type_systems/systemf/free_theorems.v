From stdpp Require Import gmap base relations.
From ffpl.lib Require Import prelude.
From ffpl.lib Require Export debruijn.
From ffpl.type_systems.systemf Require Import lang notation types bigstep logrel.
From Equations Require Import Equations.

(** * Free Theorems *)
Implicit Types
  (Delta : nat)
  (Gamma : typing_context)
  (v : val)
  (alpha : var)
  (e : expr)
  (A : type).

Definition void_type : type := forall: ^0.

(** Free theorem for the void type. *)
Lemma not_every_type_inhabited : ~ exists e, TY 0; [] |- e : void_type.
Proof.
  intros (e & Hty%sem_soundness_closed).
  simp type_interp in Hty.
  destruct Hty as (v & Hb & Hv).
  rewrite /void_type in Hv. simp type_interp in Hv. destruct Hv as (e' & -> & Ha).
  (* [set] is used to introduce a short-hand. It is basically a local definition. *)
  set tau : sem_type := fun _ => False.
  specialize (Ha tau).
  simp type_interp in Ha. destruct Ha as (v' & He' & Hv').
  simp type_interp in Hv'. asimpl in Hv'.
  exact Hv'.
Qed.

Definition unit_type : type := forall: ^0 -> ^0.

(** Free theorem for the unit type. *)
Lemma all_identity e :
  TY 0; [] |- e : unit_type ->
  forall v, big_step (e <> (of_val v)) v.
Proof.
  intros Hty%sem_soundness_closed v0.
  simp type_interp in Hty.
  destruct Hty as (v & Hb & Hv).

  rewrite /unit_type in Hv. simp type_interp in Hv. destruct Hv as (e' & -> & Hv).
  set tau : sem_type := fun v' => v' = v0.
  specialize (Hv tau).
  simp type_interp in Hv.

  destruct Hv as (v & He & Hv).
  simp type_interp in Hv.
  destruct Hv as (e'' & -> & Hv).
  specialize (Hv v0).
  (* [feed specialize] works on assumptions that are implications and opens
  subgoals to let us prove the premises of these applications. *)
  feed specialize Hv.
  { simp type_interp. simpl. done. }

  simp type_interp in Hv. destruct Hv as (v & Hb' & Hv).
  simp type_interp in Hv. rewrite /= /tau in Hv. subst v.

  eauto using big_step_val.
Qed.
