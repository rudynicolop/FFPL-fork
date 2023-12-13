From stdpp Require Import gmap base relations.
From ffpl.lib Require Import prelude.
From ffpl.type_systems.systemf Require Import lang notation deterministic.
From Equations Require Import Equations.

(** * Big-step semantics *)

Implicit Types
  (v : val)
  (e : expr).

Inductive big_step : expr -> val -> Prop :=
  | bs_lit (l : base_lit) :
      big_step (Lit l) (LitV l)
  | bs_lam (e : expr) :
      big_step (lam: e)%E (lam: e)%V
  | bs_binop e1 e2 v1 v2 v' op :
      big_step e1 v1 ->
      big_step e2 v2 ->
      bin_op_eval op v1 v2 = Some v' ->
      big_step (BinOp op e1 e2) v'
  | bs_app e1 e2 e v2 v :
      big_step e1 (LamV e) ->
      big_step e2 v2 ->
      big_step e.[of_val v2/] v ->
      big_step (App e1 e2) v
  | bs_tapp e1 e2 v :
      big_step e1 (TLamV e2) ->
      big_step e2 v ->
      big_step (e1 <>) v
  | bs_tlam e :
      big_step (Lam: e)%E (Lam: e)%V
  | bs_pack e v :
      big_step e v ->
      big_step (pack e)%E (pack v)%V
  | bs_unpack e1 e2 v1 v2 :
      big_step e1 (pack v1)%V ->
      big_step e2.[of_val v1/] v2 ->
      big_step (unpack e1 in e2) v2
  | bs_if_true e0 e1 e2 v :
      big_step e0 #true ->
      big_step e1 v ->
     big_step (if: e0 then e1 else e2) v
  | bs_if_false e0 e1 e2 v :
      big_step e0 #false ->
      big_step e2 v ->
     big_step (if: e0 then e1 else e2) v
  | bs_pair e1 e2 v1 v2 :
      big_step e1 v1 ->
      big_step e2 v2 ->
      big_step (e1, e2) (v1, v2)
  | bs_fst e v1 v2 :
      big_step e (v1, v2) ->
      big_step (Fst e) v1
  | bs_snd e v1 v2 :
      big_step e (v1, v2) ->
      big_step (Snd e) v2
    .
#[export] Hint Constructors big_step : core.

(** We can show that values behave the way they should. *)

Lemma big_step_val v :
  big_step (of_val v) v.
Proof.
  induction v; simpl; eauto.
Qed.

Lemma big_step_val_inv v v' :
  big_step (of_val v) v' -> v' = v.
Proof.
  remember (of_val v) as e. intros Hb.
  induction Hb in v, Heqe |-*; subst; destruct v; inversion Heqe; subst; repeat f_equal; eauto.
Qed.

(** ** Big-step semantics implies contextual semantics *)

Lemma big_step_contextual e v :
  big_step e v -> rtc contextual_step e (of_val v).
Proof.
  induction 1.
  - constructor.
  - constructor.
  - (* binop *)
    etrans.
    { eapply (fill_rtc_contextual_step (BinOpRCtx _ _ HoleCtx)). eauto. }
    simpl. etrans.
    { eapply (fill_rtc_contextual_step (BinOpLCtx _ HoleCtx _)). eauto. }
    simpl. eapply rtc_once.
    apply base_contextual_step. econstructor; last done.
    all: apply to_of_val.
  - etrans.
    { eapply (fill_rtc_contextual_step (AppRCtx _ HoleCtx)). eauto. }
    etrans.
    { eapply (fill_rtc_contextual_step (AppLCtx HoleCtx _)). eauto. }
    simpl. etrans.
    { econstructor 2; last econstructor 1.
      apply base_contextual_step. constructor; [| reflexivity]. eauto.
    }
    eauto.
  - (* tapp *)
    etrans.
    { eapply (fill_rtc_contextual_step (TAppCtx HoleCtx)). eauto. }
    eapply rtc_l.
    { apply base_contextual_step. by constructor. }
    eauto.
  - constructor.
  - etrans.
    { eapply (fill_rtc_contextual_step (PackCtx HoleCtx)). eauto. }
    reflexivity.
  - etrans.
    { eapply (fill_rtc_contextual_step (UnpackCtx HoleCtx _)). eauto. }
    eapply rtc_l.
    { apply base_contextual_step. simpl. constructor; last reflexivity.
      eauto.
    }
    eauto.
  - etrans.
    { eapply (fill_rtc_contextual_step (IfCtx HoleCtx _ _)). eauto. }
    eapply rtc_l.
    { eapply base_contextual_step. econstructor. }
    eauto.
  - etrans.
    { eapply (fill_rtc_contextual_step (IfCtx HoleCtx _ _)). eauto. }
    eapply rtc_l.
    { eapply base_contextual_step. econstructor. }
    eauto.
  - etrans.
    { eapply (fill_rtc_contextual_step (PairRCtx _ HoleCtx)). eauto. }
    etrans.
    { eapply (fill_rtc_contextual_step (PairLCtx HoleCtx _)). eauto. }
    reflexivity.
  - etrans.
    { eapply (fill_rtc_contextual_step (FstCtx HoleCtx)). eauto. }
    econstructor.
    { eapply base_contextual_step. simpl. eauto. }
    econstructor.
  - etrans.
    { eapply (fill_rtc_contextual_step (SndCtx HoleCtx)). eauto. }
    econstructor.
    { eapply base_contextual_step. simpl. eauto.  }
    econstructor.
Qed.

(** Together with determinism, this means big-step captures all the program behaviors:
any execution that start at [e] can be completed to go to [v]. *)
Lemma big_step_complete {e e' v} :
  big_step e v ->
  rtc contextual_step e e' ->
  rtc contextual_step e' (of_val v).
Proof.
  intros Heval%big_step_contextual Hsteps.
  destruct (contextual_steps_det Heval Hsteps) as [Hsteps'|Hsteps'].
  - inversion Hsteps'; simplify_eq/=; first done.
    exfalso. eapply conextual_step_no_val; first done.
    eapply is_val_of_val. done.
  - done.
Qed.

(** As a consequence of that, terms that evaluate are safe. *)
Lemma big_step_safe e v :
  big_step e v ->
  safe e.
Proof.
  intros Hevals ? Hsteps.
  pose proof (big_step_complete Hevals Hsteps) as Hsteps'.
  inversion Hsteps'; simplify_eq/=.
  - left. eauto.
  - right. eauto.
Qed.
