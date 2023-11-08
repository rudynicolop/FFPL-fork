From ffpl.lib Require Import prelude.
From ffpl.type_systems.stlc_extended Require Import lang.

(** *** Big-Step Semantics *)

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
  | BsPair e1 e2 (v w : val) :
      big_step e1 v ->
      big_step e2 w ->
      big_step (Pair e1 e2) (PairV v w)
  | BsProj1 e v w :
      big_step e (PairV v w) ->
      big_step (Proj1 e) v
  | BsProj2 e v w :
      big_step e (PairV v w) ->
      big_step (Proj2 e) w
.
#[export] Hint Constructors big_step : core.

(** We can show that values behave the way they should. *)
Lemma big_step_vals (v : val) : big_step (of_val v) v.
Proof.
  induction v; try constructor; done.
Qed.

Lemma big_step_inv_vals (v w : val) : big_step (of_val v) w -> v = w.
Proof.
  (** [inversion 1] means "do inversion on the first assumption in the goal",
  i.e., it is the same as [intros H; inversion H]. *)
  revert w.
  induction v; inversion 1; try reflexivity.
  simplify_eq. apply IHv2 in H4 as ->. apply IHv1 in H2 as ->. reflexivity.
Qed.
