From stdpp Require Import base relations.
From ffpl.lib Require Import prelude.
From ffpl.lib Require Import facts.
From ffpl.type_systems.systemf Require Export lang notation types bigstep.

(** Here we define some tactics that use advanced Coq techniques.
We don't expect you to be able to define such tactics; we introduce them
to avoid getting bogged down in technical details in these proofs. *)

(** The tactic [bs_step_det] makes progress on a big-step goal,
but stops and waits for human input when there is a deciwsion to be made
that the tactic cannot predict, i.e., when reaching an [If]. *)
Ltac bs_step_det :=
  simpl;
  repeat match goal with
  | |- big_step ?e _ =>
      match e with
      (* case analysis, don't backtrack but pose the goal to the user *)
      | If _ _ _ => idtac
      (* use the value lemma *)
      | of_val _ => apply big_step_val; done
      (* try to use a [big_step] assumption, or else apply a constructor *)
      | _ => first [eassumption | econstructor]
      end
  | |- bin_op_eval _ _ _ = _ =>
      reflexivity
  end.
(** [bs_steps_det] applies [bs_step_det] as often as possible. *)
Ltac bs_steps_det := repeat bs_step_det.
