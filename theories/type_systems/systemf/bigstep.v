From stdpp Require Import gmap base relations.
From ffpl.lib Require Import prelude.
From ffpl.lib Require Export debruijn.
From ffpl.type_systems.systemf Require Import lang notation.
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
  | bs_unop e v v' op :
      big_step e v ->
      un_op_eval op v = Some v' ->
      big_step (UnOp op e) v'
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
  | bs_injl e v :
      big_step e v ->
      big_step (InjL e) (InjLV v)
  | bs_injr e v :
      big_step e v ->
      big_step (InjR e) (InjRV v)
  | bs_casel e e1 e2 v v' :
      big_step e (InjLV v) ->
      big_step (e1 (of_val v)) v' ->
      big_step (Case e e1 e2) v'
  | bs_caser e e1 e2 v v' :
      big_step e (InjRV v) ->
      big_step (e2 (of_val v)) v' ->
      big_step (Case e e1 e2) v'
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
  enough (forall e, big_step e v' -> e = of_val v -> v' = v) by naive_solver.
  intros e Hb.
  induction Hb in v |-*; intros Heq; subst; destruct v; inversion Heq; subst; naive_solver.
Qed.

(** ** Big-step semantics implies contextual semantics *)

(** This is mostly a sanity check. It is also rather tedious for languages
with as many cases as ours. *)

Lemma fill_rtc_contextual_step {e1 e2} K :
  rtc contextual_step e1 e2 ->
  rtc contextual_step (fill K e1) (fill K e2).
Proof.
  induction 1 as [ | x y z H1 H2 IH]; first done.
  etrans; last apply IH.
  econstructor 2; last constructor 1.
  by apply fill_contextual_step.
Qed.

Lemma big_step_contextual e v :
  big_step e v -> rtc contextual_step e (of_val v).
Proof.
  induction 1 as [ | | e1 e2 v1 v2 v' op H1 IH1 H2 IH2 Hop | e v v' op H1 IH1 Hop
    | e1 e2 e v2 v H1 IH1 H2 IH2 H3 IH3 | e1 e2 v1 H1 IH1 H2 IH2 | |
    | e1 e2 v1 v2 H1 IH1 H2 IH2 | e0 e1 e2 v H1 IH1 H2 IH2 | e0 e1 e2 v H1 IH1 H2 IH2
    | e1 e2 v1 v2 H1 IH1 H2 IH2 | e v1 v2 H IH | e v1 v2 H IH | e v H IH | e v H IH
    | e e1 e2 v v' H1 IH1 H2 IH2 | e e1 e2 v v' H1 IH1 H2 IH2 ].
  - constructor.
  - constructor.
  - (* binop *)
    etrans.
    { eapply (fill_rtc_contextual_step (BinOpRCtx _ _ HoleCtx)). done. }
    etrans.
    { eapply (fill_rtc_contextual_step (BinOpLCtx _ HoleCtx _)). done. }
    simpl.
    etrans.
    { econstructor 2; last econstructor 1.
      apply base_contextual_step. econstructor; last done.
      all: apply to_of_val.
    }
    constructor.
  - (* unop *)
    etrans.
    { eapply (fill_rtc_contextual_step (UnOpCtx _ HoleCtx)). done. }
    simpl. etrans.
    { econstructor 2; last econstructor 1.
      apply base_contextual_step. econstructor; last done.
      all: apply to_of_val.
    }
    constructor.
  - etrans.
    { eapply (fill_rtc_contextual_step (AppRCtx _ HoleCtx)). done. }
    etrans.
    { eapply (fill_rtc_contextual_step (AppLCtx HoleCtx _)). done. }
    simpl. etrans.
    { econstructor 2; last econstructor 1.
      apply base_contextual_step. constructor; [| reflexivity]. eauto.
    }
    done.
  - etrans.
    { eapply (fill_rtc_contextual_step (TAppCtx HoleCtx)). done. }
    etrans. { econstructor 2; last constructor. apply base_contextual_step. by constructor. }
    done.
  - constructor.
  - etrans.
    { eapply (fill_rtc_contextual_step (PackCtx HoleCtx)). done. }
    done.
  - etrans.
    { eapply (fill_rtc_contextual_step (UnpackCtx HoleCtx e2)). done. }
    etrans.
    { econstructor 2; last constructor. apply base_contextual_step. simpl. constructor; last reflexivity.
      eauto.
    }
    done.
  - etrans.
    { eapply (fill_rtc_contextual_step (IfCtx HoleCtx _ _)). done. }
    etrans.
    { econstructor; last constructor. eapply base_contextual_step. econstructor. }
    done.
  - etrans.
    { eapply (fill_rtc_contextual_step (IfCtx HoleCtx _ _)). done. }
    etrans.
    { econstructor; last constructor. eapply base_contextual_step. econstructor. }
    done.
  - etrans.
    { eapply (fill_rtc_contextual_step (PairRCtx e1 HoleCtx)). done. }
    etrans.
    {  eapply (fill_rtc_contextual_step (PairLCtx HoleCtx v2)). done. }
    econstructor.
  - etrans.
    { eapply (fill_rtc_contextual_step (FstCtx HoleCtx)). done. }
    econstructor.
    { eapply base_contextual_step. simpl. eauto. }
    econstructor.
  - etrans.
    { eapply (fill_rtc_contextual_step (SndCtx HoleCtx)). done. }
    econstructor.
    { eapply base_contextual_step. simpl. eauto.  }
    econstructor.
  - etrans.
    { eapply (fill_rtc_contextual_step (InjLCtx HoleCtx)). done. }
    econstructor.
  - etrans.
    { eapply (fill_rtc_contextual_step (InjRCtx HoleCtx)). done. }
    econstructor.
  - etrans.
    { eapply (fill_rtc_contextual_step (CaseCtx HoleCtx e1 e2)). done. }
    simpl. econstructor.
    { eapply base_contextual_step. eauto.  }
    done.
  - etrans.
    { eapply (fill_rtc_contextual_step (CaseCtx HoleCtx e1 e2)). done. }
    simpl. econstructor.
    { eapply base_contextual_step. eauto. }
    done.
Qed.
