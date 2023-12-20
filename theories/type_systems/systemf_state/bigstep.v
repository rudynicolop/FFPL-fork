From stdpp Require Import gmap base relations.
From ffpl.lib Require Import prelude.
From ffpl.type_systems.systemf_state Require Import lang notation deterministic.
From Equations Require Import Equations.

(** * Big-step semantics *)

Implicit Types
  (v : val)
  (e : expr)
  (h : heap).

Inductive big_step : heap * expr -> heap * val -> Prop :=
  | bs_lit h (l : base_lit) :
      big_step (h, Lit l) (h, LitV l)
  | bs_lam h (e : expr) :
      big_step (h, (lam: e)%E) (h, (lam: e)%V)
  | bs_binop h1 h2 h3 e1 e2 v1 v2 v' op :
      big_step (h1, e2) (h2, v2) ->
      big_step (h2, e1) (h3, v1) ->
      bin_op_eval op v1 v2 = Some v' ->
      big_step (h1, BinOp op e1 e2) (h3, v')
  | bs_app h1 h2 h3 h4 e1 e2 e v2 v :
      big_step (h1, e2) (h2, v2) ->
      big_step (h2, e1) (h3, LamV e) ->
      big_step (h3, e.[of_val v2/]) (h4, v) ->
      big_step (h1, App e1 e2) (h4, v)
  | bs_tapp h1 h2 h3 e1 e2 v :
      big_step (h1, e1) (h2, TLamV e2) ->
      big_step (h2, e2) (h3, v) ->
      big_step (h1, (e1 <>)%E) (h3, v)
  | bs_tlam h e :
      big_step (h, (Lam: e)%E) (h, (Lam: e)%V)
  | bs_pack h1 h2 e v :
      big_step (h1, e) (h2, v) ->
      big_step (h1, (pack e)%E) (h2, (pack v)%V)
  | bs_unpack h1 h2 h3 e1 e2 v1 v2 :
      big_step (h1, e1) (h2, (pack v1)%V) ->
      big_step (h2, e2.[of_val v1/]) (h3, v2) ->
      big_step (h1, (unpack e1 in e2)%E) (h3, v2)
  | bs_if_true h1 h2 h3 e0 e1 e2 v :
      big_step (h1, e0) (h2, #true) ->
      big_step (h2, e1) (h3, v) ->
      big_step (h1, (if: e0 then e1 else e2)%E) (h3, v)
  | bs_if_false h1 h2 h3 e0 e1 e2 v :
      big_step (h1, e0) (h2, #false) ->
      big_step (h2, e2) (h3, v) ->
      big_step (h1, (if: e0 then e1 else e2)%E) (h3, v)
  | bs_pair h1 h2 h3 e1 e2 v1 v2 :
      big_step (h1, e2) (h2, v2) ->
      big_step (h2, e1) (h3, v1) ->
      big_step (h1, (e1, e2)%E) (h3, (v1, v2)%V)
  | bs_fst h1 h2 e v1 v2 :
      big_step (h1, e) (h2, (v1, v2)%V) ->
      big_step (h1, Fst e) (h2, v1)
  | bs_snd h1 h2 e v1 v2 :
      big_step (h1, e) (h2, (v1, v2)%V) ->
      big_step (h1, Snd e) (h2, v2)
  | bs_new h1 h2 e v (l : loc) :
      big_step (h1, e) (h2, v) ->
      l = fresh (dom h2) ->
      big_step (h1, New e) (<[l:=v]> h2, #l)
  | bs_load h1 h2 e v (l : loc) :
      big_step (h1, e) (h2, #l) ->
      h2 !! l = Some v ->
      big_step (h1, Load e) (h2, v)
  | bs_store h1 h2 h3 e1 e2 v w (l : loc) :
      big_step (h1, e2) (h2, w) ->
      big_step (h2, e1) (h3, #l) ->
      h3 !! l = Some v ->
      big_step (h1, Store e1 e2) (<[l:=w]> h3, w)
.
#[export] Hint Constructors big_step : core.

(** We can show that values behave the way they should. *)

Lemma big_step_val h v :
  big_step (h, of_val v) (h, v).
Proof.
  induction v; simpl; eauto.
Qed.

Lemma big_step_val_inv h v h' v' :
  big_step (h, of_val v) (h', v') -> h' = h /\ v' = v.
Proof.
  remember (of_val v) as e. remember (h, e) as cfg. remember (h', v') as cfg'.
  induction 1 in h, e, Heqcfg, v, Heqe, h', v', Heqcfg' |-*.
  all: injection Heqcfg as [= <- <-]; injection Heqcfg' as [= <- <-].
  all: destruct v; inversion Heqe; subst; eauto.
  - (* pack *) edestruct IHbig_step; [|done|done|]; first done. simplify_eq/=. eauto.
  - (* pair *)
    edestruct IHbig_step1; [|done|done|]; first done.
    edestruct IHbig_step2; [|done|done|]; first done.
    simplify_eq/=. eauto.
Qed.

(** ** Big-step semantics implies contextual semantics *)

Lemma big_step_contextual h e h' v :
  big_step (h, e) (h', v) -> rtc contextual_step (h, e) (h', of_val v).
Proof.
  remember (h, e) as cfg. remember (h', v) as cfg'.
  induction 1 in h, e, Heqcfg, h', v, Heqcfg' |- *; simplify_eq/=.
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
  - etrans.
    { eapply (fill_rtc_contextual_step (NewCtx HoleCtx)). eauto. }
    eapply rtc_once, base_contextual_step. econstructor; first done.
    rewrite to_of_val. done.
  - etrans.
    { eapply (fill_rtc_contextual_step (LoadCtx HoleCtx)). eauto. }
    eapply rtc_once, base_contextual_step. econstructor. done.
  - etrans.
    { eapply (fill_rtc_contextual_step (StoreRCtx _ HoleCtx)). eauto. }
    etrans.
    { eapply (fill_rtc_contextual_step (StoreLCtx HoleCtx _)). eauto. }
    eapply rtc_once, base_contextual_step. econstructor; first done.
    rewrite to_of_val. done.
Qed.

(** Together with determinism, this means big-step captures all the program behaviors:
any execution that start at [e] can be completed to go to [v]. *)
Lemma big_step_complete {h e h' e' h'' v} :
  big_step (h, e) (h'', v) ->
  rtc contextual_step (h, e) (h', e') ->
  rtc contextual_step (h', e') (h'', of_val v).
Proof.
  intros Heval%big_step_contextual Hsteps.
  destruct (contextual_steps_det Heval Hsteps) as [Hsteps'|Hsteps'].
  - inversion Hsteps'; simplify_eq/=; first done.
    destruct y as [h''' e'''].
    exfalso. eapply conextual_step_no_val; first done.
    eapply is_val_of_val. done.
  - done.
Qed.

(** As a consequence of that, terms that evaluate are safe. *)
Lemma big_step_safe h e h' v :
  big_step (h, e) (h', v) ->
  safe h e.
Proof.
  intros Hevals ?? Hsteps.
  pose proof (big_step_complete Hevals Hsteps) as Hsteps'.
  inversion Hsteps' as [|? [h'' e'']]; simplify_eq/=.
  - left. eauto.
  - right. eauto.
Qed.
