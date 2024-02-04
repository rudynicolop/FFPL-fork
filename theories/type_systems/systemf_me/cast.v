From Autosubst Require Export Autosubst.
(* Require Import AutosubstSsr. *)
From ffpl.lib Require Export maps.
From Equations Require Export Equations.

Inductive typ :=
(* Minmal System F types. *)
| Ident (X : var)
| Fun (A B : typ)
| Uni (A : {bind 1 of typ})
.

#[export] Instance Ids_typ : Ids typ. derive. Defined.
#[export] Instance Rename_typ : Rename typ. derive. Defined.
#[export] Instance Subst_typ : Subst typ. derive. Defined.

#[export] Instance SubstLemmas_typ : SubstLemmas typ. derive. Qed.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.
Bind Scope typ_scope with typ.

Coercion Ident : var >-> typ.
Infix "`→" :=
  Fun
    (at level 100, right associativity)
    : typ_scope.
Notation "'`∀' A" :=
  (Uni A%typ)
    (at level 100, A at level 200)
    : typ_scope.

Global Instance typ_eq_dec : EqDec typ.
Proof.
  unfold EqDec.
  intro A.
  induction A as [α | A1 IHA1 A2 IHA2 | A IHA]; intros [β | B1 B2 | B];
    try (right; discriminate).
  - pose proof nat_eqdec α β as [<- | H]; eauto.
    right. injection 1 as <-. contradiction.
  - specialize IHA1 with B1 as [<- | IHA1].
    + specialize IHA2 with B2 as [<- | IHA2]; eauto.
      right. injection 1 as <-. contradiction.
    + right. injection 1 as <- _. contradiction.
  - specialize IHA with B as [<- | IH]; eauto.
    right. injection 1 as <-. contradiction.
Defined.

Global Instance TypDecision (A B : typ) : Decision (A = B).
Proof.
  unfold Decision.
  apply typ_eq_dec.
Qed.

Inductive trm :=
(* Minimal System F runtime terms. *)
| ident (x : var)
| abs (A : typ) (M : {bind 1 of trm})
| app (M N : trm)
| tabs (M : {bind typ in trm})
| tapp (M : trm) (A : typ)
(* Casts. *)
| cast (A B : typ) (M N : trm)
.


#[export] Instance HSubst_trm : HSubst typ trm. derive. Defined.

#[export] Instance Ids_trm : Ids trm. derive. Defined.
#[export] Instance Rename_trm : Rename trm. derive. Defined.
#[export] Instance Subst_trm : Subst trm. derive. Defined.

#[export] Instance HSubstLemmas_trm : HSubstLemmas typ trm. derive. Qed.
#[export] Instance SubstHSubstComp_typ_trm : SubstHSubstComp typ trm. derive. Qed.
#[export] Instance SubstLemmas_trm : SubstLemmas trm. derive. Qed.

Declare Scope trm_scope.
Delimit Scope trm_scope with trm.
Bind Scope trm_scope with trm.

Notation "'λ:' A `, M" := (abs A%typ M%trm) (at level 100, right associativity) : trm_scope.
Notation "'Λ' M" := (tabs M%trm) (at level 100, right associativity) : trm_scope.
Notation "M '`[' A  ']`'" := (tapp M%trm A%typ) (at level 96, left associativity) : trm_scope.

Coercion ident : var >->trm.
Coercion app : trm >-> Funclass.

Variant val :=
  | abs__v (A : typ) (M : trm)
  | tabs__v (M : trm).

Declare Scope val_scope.
Delimit Scope val_scope with val.
Bind Scope val_scope with val.

Notation "'λ:' A `, M" := (abs__v A%typ M%trm) (at level 100, right associativity) : val_scope.
Notation "'Λ' M" := (tabs__v M%trm) (at level 100, right associativity) : val_scope.

Definition inj__v (v : val) : trm :=
  match v with
  | (λ: A `, M)%val => (λ: A `, M)%trm
  | (Λ M)%val => (Λ M)%trm
  end.

Definition is_val (M : trm) : Prop :=
  exists v, M = inj__v v.

Lemma abs_is_val A M :
  is_val (λ: A `, M)%trm.
Proof.
  exists (λ: A `, M)%val. reflexivity.
Qed.
Local Hint Resolve abs_is_val : core.

Lemma tabs_is_val M :
  is_val (Λ M)%trm.
Proof.
  exists (Λ M)%val. reflexivity.
Qed.
Local Hint Resolve tabs_is_val : core.

Lemma inj_is_val v :
  is_val (inj__v v).
Proof.
  eexists; reflexivity.
Qed.
Local Hint Resolve inj_is_val : core.

Lemma ident_is_not_val (x : var) :
  ~ is_val x.
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve ident_is_not_val : core.

Lemma app_is_not_val (M N : trm) :
  ~ is_val (M N).
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve app_is_not_val : core.

Lemma tapp_is_not_val M A :
  ~ is_val (M `[ A ]`)%trm.
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve tapp_is_not_val : core.

Lemma cast_is_not_val A B M N :
  ~ is_val (cast A B M N).
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve cast_is_not_val : core.

Coercion inj__v : val >-> trm.

Lemma inj_inj__v v1 v2 :
  inj__v v1 = inj__v v2 -> v1 = v2.
Proof.
  destruct v1, v2; discriminate || injection 1 as <- <- || injection 1 as <-; reflexivity.
Qed.

Lemma abs_inj__v A M v :
  (λ: A `, M)%trm = inj__v v -> v = (λ: A `, M)%val.
Proof.
  destruct v; discriminate || injection 1 as <- <-; reflexivity.
Qed.

Lemma tabs_inj__v M v :
  (Λ M)%trm = inj__v v -> v = (Λ M)%val.
Proof.
  destruct v; discriminate || injection 1 as <-; reflexivity.
Qed.

Lemma ident_not_inj__v (x : var) v :
  ident x <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma app_not_inj__v (M N : trm) v :
  M N <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma tapp_not_inj__v M A v :
  (M `[ A ]`)%trm <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma cast_not_inj__v A B M N v :
  cast A B M N <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Ltac elim_inj__v :=
  lazymatch goal with
  | H: inj__v _ = inj__v _ |- _ => specialize inj_inj__v with (1:=H) as ->
  | H: (λ: _ `, _)%trm = inj__v _ |- _ => specialize abs_inj__v with (1:=H) as ->
  | H: (Λ _)%trm = inj__v _ |- _ => specialize tabs_inj__v with (1:=H) as ->
  | H: inj__v _ = (λ: _ `, _)%trm |- _ => symmetry in H; specialize abs_inj__v with (1:=H) as ->
  | H: inj__v _ = (Λ _)%trm |- _ => symmetry in H; specialize tabs_inj__v with (1:=H) as ->
  | H: ident _ = inj__v _ |- _ => apply ident_not_inj__v in H; contradiction
  | H: app _ _ = inj__v _ |- _ => apply app_not_inj__v in H; contradiction
  | H: (_ `[ _ ]`)%trm = inj__v _ |- _ => apply tapp_not_inj__v in H; contradiction
  | H: cast _ _ _ _ = inj__v _ |- _ => apply cast_not_inj__v in H; contradiction
  | H: inj__v _ = ident _  |- _ => symmetry; apply ident_not_inj__v in H; contradiction
  | H: inj__v _ = app _ _ |- _ => symmetry; apply app_not_inj__v in H; contradiction
  | H: inj__v _ = (_ `[ _ ]`)%trm |- _ => symmetry; apply tapp_not_inj__v in H; contradiction
  | H: inj__v _ = cast _ _ _ _ |- _ => symmetry; apply cast_not_inj__v in H; contradiction
  end.

Local Hint Extern 0 => elim_inj__v : core.

Inductive ktx :=
| hole
| app__l (K : ktx) (v : val)
| app__r (M : trm) (K : ktx)
| tapp__k (K : ktx) (A : typ)
| cast__l (A B : typ) (K : ktx) (v : val)
| cast__r (A B : typ) (M : trm) (K : ktx).

Reserved Notation "K '[[' M ']]'"
  (at level 98, left associativity).

Fixpoint fill__k (K : ktx) (M : trm) : trm :=
  match K with
  | hole => M
  | app__l K v => app (K [[ M ]]) $ inj__v v
  | app__r N K => app N (K [[ M ]])
  | tapp__k K A => tapp (K [[ M ]]) A
  | cast__l A B K v => cast A B (K [[ M ]]) $ inj__v v
  | cast__r A B N K => cast A B N (K [[ M ]])
  end
where "K '[[' M ']]'" := (fill__k K M%trm) : trm_scope.

Reserved Infix "`∘" (at level 98, left associativity).

Fixpoint comp__k (K K' : ktx) : ktx :=
  match K with
  | hole => K'
  | app__l K v => app__l (K `∘ K') v
  | app__r M K => app__r M (K `∘ K')
  | tapp__k K A => tapp__k (K `∘ K') A
  | cast__l A B K v => cast__l A B (K `∘ K') v
  | cast__r A B M K => cast__r A B M (K `∘ K')
  end
where "K1 '`∘' K2" := (comp__k K1 K2).

Lemma fill_comp__k K K' M :
  ((K `∘ K') [[ M ]])%trm = (K [[ K' [[ M ]] ]])%trm.
Proof.
  induction K; cbn; f_equal; auto.
Qed.

Reserved Infix "~>b" (at level 80, no associativity).

Variant step__b : trm -> trm -> Prop :=
  | step_app_abs__b A M (n : val) :
    app (λ: A `, M) (inj__v n) ~>b M.[ inj__v n /]
  | step_tapp_tabs__b M A :
    (Λ M) `[A]` ~>b M.|[A/]
  | step_cast_eq__b A v1 v2 :
    cast A A (inj__v v1) (inj__v v2) ~>b v2
  | step_cast_neq__b A B v1 v2 :
    A <> B ->
    cast A B (inj__v v1) (inj__v v2) ~>b v1
where "M '~>b' N" := (step__b M N) : type_scope.

Reserved Infix "~>" (at level 80, no associativity).

Variant step : trm -> trm -> Prop :=
  | step_ktx M N K :
    M ~>b N ->
    (K [[ M ]])%trm ~> (K [[ N ]])%trm
where "M '~>' N" := (step M%trm N%trm) : type_scope.

Lemma inv_step KM KN :
  KM ~> KN -> exists M N K, KM = (K [[ M ]])%trm /\ KN = (K [[ N ]])%trm /\ M ~>b N.
Proof.
  inversion 1; subst.
  do 3 eexists. eauto.
Qed.

Local Hint Constructors step__b : core.
Local Hint Constructors step : core.

Lemma val_not_step__b (v : val) N :
  ~ (v ~>b N).
Proof.
  inversion 1; subst; try elim_inj__v.
Qed.

Local Hint Resolve val_not_step__b : core.

Lemma val_fill__k K M (v : val) :
  (K [[ M ]])%trm = v -> is_val M.
Proof.
  revert v.
  induction K; intros []; cbn; try discriminate;
    try (intros ->; auto; assumption).
Qed.

Local Hint Resolve val_fill__k : core.

Lemma val_not_step (v : val) N :
  ~ (v ~> N).
Proof.
  inversion 1; subst; eauto.
  apply val_fill__k in H0.
  destruct H0 as [v' ->].
  revert H1. apply val_not_step__b.
Qed.

Lemma ctx_lift M N K :
  M ~> N ->
  (K [[ M ]])%trm ~> (K [[ N ]])%trm.
Proof.
  inversion 1; subst.
  do 2 rewrite <- fill_comp__k.
  eauto.
Qed.

Local Hint Resolve ctx_lift : core.

Lemma step_app_abs A M (n : val) :
  app (λ: A `, M) (inj__v n) ~> M.[ inj__v n /].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_app_abs : core.

Lemma step_app_abs_is_val A M N :
  is_val N ->
  app (λ: A `, M) N ~> M.[ N /].
Proof.
  intros [n ->]. eauto.
Qed.

Local Hint Resolve step_app_abs_is_val : core.

Lemma step_tapp_tabs M A :
  (Λ M) `[A]` ~> M.|[A/].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_tapp_tabs : core.

Lemma step_cast_eq A v1 v2 :
  cast A A (inj__v v1) (inj__v v2) ~> v2.
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_cast_eq : core.

Lemma step_cast_eq_is_val A M N :
  is_val M -> is_val N ->
  cast A A M N ~> N.
Proof.
  intros [m ->] [n ->]; eauto.
Qed.

Local Hint Resolve step_cast_eq_is_val : core.

Lemma step_cast_neq A B v1 v2 :
  A <> B ->
  cast A B (inj__v v1) (inj__v v2) ~> v1.
Proof.
  intro H.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_cast_neq : core.

Lemma step_cast_neq_is_val A B M N :
  A <> B ->
  is_val M -> is_val N ->
  cast A B M N ~> M.
Proof.
  intros H [m ->] [n ->]; eauto.
Qed.

Local Hint Resolve step_cast_neq_is_val : core.

Lemma step_app__r (M N N' : trm) :
  N ~> N' ->
  app M N ~> app M N'.
Proof.
  replace (app M N) with (app__r M hole [[ N ]])%trm by reflexivity.
  replace (app M N') with (app__r M hole [[ N' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_app__r : core.

Lemma step_app__l M M' (v : val) :
  M ~> M' ->
  app M (inj__v v) ~> app M' (inj__v v).
Proof.
  replace (app M (inj__v v)) with (app__l hole v [[ M ]])%trm by reflexivity.
  replace (app M' (inj__v v)) with (app__l hole v [[ M' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_app__l : core.

Lemma step_app_is_val__l M M' N :
  is_val N ->
  M ~> M' ->
  app M N ~> app M' N.
Proof.
  intros [n ->]. eauto.
Qed.

Local Hint Resolve step_app_is_val__l : core.

Lemma step_tapp M M' A :
  M ~> M' ->
  (M `[A]`)%trm ~> (M' `[A]`)%trm.
Proof.
  replace (M `[A]`)%trm with (tapp__k hole A [[ M ]])%trm by reflexivity.
  replace (M' `[A]`)%trm with (tapp__k hole A [[ M' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_tapp : core.

Lemma step_cast__r A B M N N' :
  N ~> N' ->
  cast A B M N ~> cast A B M N'.
Proof.
  replace (cast A B M N) with (cast__r A B M hole [[ N ]])%trm by reflexivity.
  replace (cast A B M N') with (cast__r A B M hole [[ N' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_cast__r : core.

Lemma step_cast__l A B M M' n :
  M ~> M' ->
  cast A B M (inj__v n) ~> cast A B M' (inj__v n).
Proof.
  replace (cast A B M (inj__v n)) with (cast__l A B hole n [[ M ]])%trm by reflexivity.
  replace (cast A B M' (inj__v n)) with (cast__l A B hole n [[ M' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_cast__l : core.

Lemma step_cast_is_val__l A B M M' N :
  is_val N ->
  M ~> M' ->
  cast A B M N ~> cast A B M' N.
Proof.
  intros [n ->]; eauto.
Qed.

Local Hint Resolve step_cast_is_val__l : core.

Reserved Infix "⊢wf" (at level 80).

Inductive wf_typ (Δ : nat) : typ -> Prop :=
| wf_Ident (X : var) :
  X < Δ ->
  Δ ⊢wf X
| wf_Fun A B :
  Δ ⊢wf A ->
  Δ ⊢wf B ->
  Δ ⊢wf (A `→ B)
| wf_Uni A :
  S Δ ⊢wf A ->
  Δ ⊢wf `∀ A
where "Δ '⊢wf' τ" := (wf_typ Δ%nat τ%typ) : type_scope.

Local Hint Constructors wf_typ : core.

Definition up__Γ (Γ : list typ) : list typ:= subst (ren S) <$> Γ.

Reserved Notation "Δ '`;' Γ '⊢' M '`:' τ" (at level 80).

Inductive judge (Δ : nat) (Γ : list typ) : trm -> typ -> Prop :=
| judge_ident (x : var) A :
  Γ !! x = Some A ->
  Δ `; Γ ⊢ ident x `: A
| judge_abs M A B :
  Δ ⊢wf A ->
  Δ `; A :: Γ ⊢ M `: B ->
  Δ `; Γ ⊢ λ: A `, M `: (A `→ B)
| judge_app M N A B :
  Δ `; Γ ⊢ M `: (A `→ B)%typ ->
  Δ `; Γ ⊢ N `: A ->
  Δ `; Γ ⊢ app M N `: B
| judge_tabs M A :
  S Δ `; up__Γ Γ ⊢ M `: A ->
  Δ `; Γ ⊢ Λ M `: `∀ A
| judge_tapp M (A B : typ) :
  Δ ⊢wf B ->
  Δ `; Γ ⊢ M `: (`∀ A)%typ ->
  Δ `; Γ ⊢ M `[ B ]` `: A.[ B /]
| judge_cast A B M N :
  Δ `; Γ ⊢ M `: B ->
  Δ `; Γ ⊢ N `: A ->
  Δ `; Γ ⊢ cast A B M N `: B
where "Δ `; Γ '⊢' M '`:' τ" := (judge Δ%nat Γ M%trm τ%typ).

Local Hint Constructors judge : core.

Section inv.
  Variable Δ : nat.
  Variable Γ : list typ.
  
  Lemma inv_judge_ident x A :
    Δ `; Γ ⊢ ident x `: A ->
    Γ !! x = Some A.
  Proof.
    inversion 1; auto.
  Qed.

  Lemma inv_judge_abs M A C :
    Δ `; Γ ⊢ λ: A `, M `: C ->
    exists B, C = (A `→ B)%typ /\ Δ ⊢wf A /\ Δ `; A :: Γ ⊢ M `: B.
  Proof.
    inversion 1; subst.
    eauto.
  Qed.

  Lemma inv_judge_app M N B :
    Δ `; Γ ⊢ app M N `: B ->
    exists A, Δ `; Γ ⊢ M `: (A `→ B) /\ Δ `; Γ ⊢ N `: A.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_tabs M A :
    Δ `; Γ ⊢ Λ M `: (`∀ A) ->
    S Δ `; up__Γ Γ ⊢ M `: A.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_tapp M B C :
    Δ `; Γ ⊢ M `[B]` `: C ->
    exists A, C = A.[B/] /\ Δ ⊢wf B /\ Δ `; Γ ⊢ M `: (`∀ A).
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_cast A B C M N :
    Δ `; Γ ⊢ cast A B M N `: C ->
    C = B /\ Δ `; Γ ⊢ M `: B /\ Δ `; Γ ⊢ N `: A.
  Proof.
    inversion 1; subst; eauto.
  Qed.  
End inv.

Section canon.
  Variable Δ : nat.
  Variable Γ : list typ.
  
  Lemma canon_fun (v : val) A B :
    Δ `; Γ ⊢ v `: (A `→ B)%typ ->
    exists N, v = (λ: A `, N)%val.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma canon_uni (v : val) A :
    Δ `; Γ ⊢ v `: (`∀ A)%typ ->
    exists M, v = (Λ M)%val.
  Proof.
    inversion 1; subst; eauto.
  Qed.
End canon.

Definition progressive (M : trm) : Prop :=
  (exists N, M ~> N) \/ is_val M.

Theorem progress_trm M A :
  0 `; [] ⊢ M `: A -> progressive M.
Proof.
  remember 0 as Δ eqn:eqΔ.
  remember [] as Γ eqn:eqΓ.
  induction 1; subst; auto;
    repeat match goal with
      | h: 0 = 0 -> [] = [] -> _ |- _
        => specialize h with (1:=eq_refl) (2:=eq_refl)
      end.
  - rewrite lookup_nil in H. discriminate.
  - right; auto.
  - left.
    destruct IHjudge2 as [(N' & HN) | (n & ->)]; eauto.
    destruct IHjudge1 as [(M' & HM) | (m & ->)]; eauto.
    specialize canon_fun with (1:=H) as [M ->].
    exists (M.[inj__v n/]). apply step_app_abs.
  - right; auto.
  - left.
    destruct IHjudge as [(M' & HM) | (m & ->)]; eauto.
    specialize canon_uni with (1:=H0) as [M ->].
    exists (M.|[B/]). apply step_tapp_tabs.
  - left.
    destruct IHjudge2 as [(N' & HN) | (n & ->)]; eauto.
    destruct IHjudge1 as [(M' & HM) | (m & ->)]; eauto.
    destruct (decide (A = B)) as [<- | HAB]; eauto.
Qed.

Definition wf_tsubst Δ1 Δ2 σ :=
  forall α, α < Δ1 -> Δ2 ⊢wf σ α.

Definition wf_tren Δ1 Δ2 (δ : var -> var) :=
  forall α, α < Δ1 -> δ α < Δ2.

Definition wf_tren_le Δ1 Δ2 :
  Δ1 <= Δ2 -> wf_tren Δ1 Δ2 id.
Proof.
  unfold wf_tren. cbn. lia.
Qed.

Lemma wf_tren_S Δ :
  wf_tren Δ (S Δ) S.
Proof.
  unfold wf_tren. lia.
Qed.

Local Hint Resolve wf_tren_S : core.

Lemma wf_tren_up δ Δ1 Δ2 :
  wf_tren Δ1 Δ2 δ -> wf_tren (S Δ1) (S Δ2) (upren δ).
Proof.
  unfold wf_tren.
  intros Htren [| α] HΔ1; asimpl.
  - lia.
  - specialize Htren with α. lia.
Qed.

Local Hint Resolve wf_tren_up : core.

Lemma wf_typ_rename Δ1 Δ2 A δ :
  wf_tren Δ1 Δ2 δ ->
  Δ1 ⊢wf A ->
  Δ2 ⊢wf A.[ren δ].
Proof.
  intros Htren.
  induction 1 in Δ2, Htren, δ |-*; asimpl; eauto.
Qed.

Local Hint Resolve wf_typ_rename : core.

Lemma wf_typ_S Δ B :
  Δ ⊢wf B → S Δ ⊢wf B.[ren S].
Proof.
  eauto.
Qed.

Lemma Forall_wf_typ_S Δ Γ :
  Forall (wf_typ Δ) Γ -> Forall (wf_typ (S Δ)) (up__Γ Γ).
Proof.
  unfold up__Γ.
  rewrite Forall_fmap.
  apply List.Forall_impl. cbn.
  apply wf_typ_S.
Qed.

Lemma wf_typ_weaken Δ1 Δ2 A :
  Δ1 <= Δ2 -> Δ1 ⊢wf A -> Δ2 ⊢wf A.
Proof.
  intros H%wf_tren_le H1.
  replace A with A.[ren id] by by asimpl.
  eauto.
Qed.

Lemma wf_tsubst_S Δ :
  wf_tsubst Δ (S Δ) (ren S).
Proof.
  unfold wf_tsubst.
  intros X HX.
  constructor. lia.
Qed.

Local Hint Resolve wf_tsubst_S : core.

Lemma wf_tsubst_up σ Δ1 Δ2 :
  wf_tsubst Δ1 Δ2 σ -> wf_tsubst (S Δ1) (S Δ2) (up σ).
Proof.
  unfold wf_tsubst.
  intros Hwftsubst [| α]; asimpl.
  - eauto with lia.
  - intros H%Arith_prebase.lt_S_n. eauto.
Qed.

Local Hint Resolve wf_tsubst_up : core.

Lemma wf_tren_tsubst Δ1 Δ2 (δ : var -> var) :
  wf_tren Δ1 Δ2 δ <-> wf_tsubst Δ1 Δ2 (ren δ).
Proof.
  unfold wf_tren, wf_tsubst. split.
  - intros Htren α HΔ1.
    specialize Htren with (1:=HΔ1).
    constructor. eauto.
  - intros Htsubst α HΔ1.
    specialize Htsubst with (1:=HΔ1).
    inversion Htsubst; subst.
    assumption.
Qed.

Lemma wf_tsubst_single Δ A :
  Δ ⊢wf A ->
  wf_tsubst (S Δ) Δ (A .: ids).
Proof.
  intros Hwf [| α] Hα; asimpl; eauto.
  constructor. lia.
Qed.

Local Hint Resolve wf_tsubst_single : core.

Lemma wf_tsubst_wf_typ Δ1 Δ2 σ A :
  wf_tsubst Δ1 Δ2 σ ->
  Δ1 ⊢wf A ->
  Δ2 ⊢wf A.[σ].
Proof.
  intros Hwftsub.
  induction 1 in Δ2, Hwftsub, σ |- *; asimpl; eauto.
Qed.
  
Local Hint Resolve wf_tsubst_wf_typ : core.

Lemma up_subst σ Γ :
  up__Γ (subst σ <$> Γ) = subst (up σ) <$> up__Γ Γ.
Proof.
  rewrite /up__Γ.
  apply list_eq.
  intro x.
  rewrite !list_lookup_fmap.
  destruct (Γ !! x) as [A |] eqn:HA; asimpl; auto.
Qed.

Lemma judge_tsubst Δ1 Δ2 Γ M A σ :
  wf_tsubst Δ1 Δ2 σ ->
  Δ1 `; Γ ⊢ M `: A ->
  Δ2 `; (subst σ) <$> Γ ⊢ M.|[σ] `: A.[σ].
Proof.
  intros Hσ.
  induction 1 in Hσ, σ, Δ2 |- *; cbn; eauto.
  - constructor.
    rewrite list_lookup_fmap.
    apply fmap_Some_2. assumption.
  - constructor.
    rewrite up_subst. eauto.
  - replace (A.[B/].[σ]) with (A.[up σ].[B.[σ]/])
      by by asimpl. asimpl in IHjudge.
    eauto.
Qed.

Local Hint Resolve judge_tsubst : core.

Lemma judge_tsubst_single Δ Γ M A B :
  Δ ⊢wf B ->
  S Δ `; Γ ⊢ M `: A ->
  Δ `; (fun C => C.[B/]) <$> Γ ⊢ M.|[B/] `: A.[ B /].
Proof.
  eauto.
Qed.

Local Hint Resolve judge_tsubst_single : core.

Definition lookup_ren (Γ1 Γ2 : list typ) (δ : var -> var) :=
  forall x A, Γ1 !! x = Some A -> Γ2 !! (δ x) = Some A.

Lemma lookup_ren_S Γ A :
  lookup_ren Γ (A :: Γ) S.
Proof.
  unfold lookup_ren.
  auto.
Qed.

Local Hint Resolve lookup_ren_S : core.

Lemma lookup_ren_upren A Γ1 Γ2 δ :
  lookup_ren Γ1 Γ2 δ ->
  lookup_ren (A :: Γ1) (A :: Γ2) (upren δ).
Proof.
  unfold lookup_ren.
  intros Hlook x B HB.
  destruct x as [| x]; cbn in *; auto.
Qed.
  
Local Hint Resolve lookup_ren_upren : core.

Lemma lookup_ren_up__Γ Γ1 Γ2 δ :
  lookup_ren Γ1 Γ2 δ ->
  lookup_ren (up__Γ Γ1) (up__Γ Γ2) δ.
Proof.
  unfold lookup_ren, up__Γ.
  intros Hlook x B HB.
  rewrite list_lookup_fmap in HB.
  rewrite list_lookup_fmap.
  apply fmap_Some in HB as (C & HxC & ->).
  specialize Hlook with (1:=HxC).
  rewrite Hlook. reflexivity.
Qed.

Local Hint Resolve lookup_ren_up__Γ : core.

Lemma judge_rename δ Δ Γ1 Γ2 M A :
  lookup_ren Γ1 Γ2 δ ->
  Δ `; Γ1 ⊢ M `: A ->
  Δ `; Γ2 ⊢ M.[ren δ] `: A.
Proof.
  intros Hlookup.
  induction 1 in Γ2, δ, Hlookup |- *; asimpl; eauto.
Qed.

Local Hint Resolve judge_rename : core.

Definition lookup_subst Δ (Γ1 Γ2 : list typ) (σ : var -> trm) :=
  forall x B, Γ1 !! x = Some B -> Δ `; Γ2 ⊢ σ x `: B.

Lemma lookup_subst_up Δ A Γ1 Γ2 σ :
  lookup_subst Δ Γ1 Γ2 σ ->
  lookup_subst Δ (A :: Γ1) (A :: Γ2) (up σ).
Proof.
  unfold lookup_subst.
  intros Hlook [| x] B HB; asimpl in *.
  - injection HB as <-. constructor.
    reflexivity.
  - specialize Hlook with (1:=HB). eauto.
Qed.

Local Hint Resolve lookup_subst_up : core.

Lemma lookup_subst_up__Γ Δ Γ1 Γ2 σ :
  lookup_subst Δ Γ1 Γ2 σ ->
  lookup_subst (S Δ) (up__Γ Γ1) (up__Γ Γ2) (σ >>| ren S).
Proof.
  unfold lookup_subst, up__Γ.
  intros Hlook x B HB.
  rewrite list_lookup_fmap in HB.
  apply fmap_Some in HB as (A & HxA & ->).
  specialize Hlook with (1:=HxA).
  apply judge_tsubst with (Δ1 := Δ); eauto.
Qed.

Local Hint Resolve lookup_subst_up__Γ : core.

Lemma judge_subst σ Δ M Γ1 Γ2 A :
  lookup_subst Δ Γ1 Γ2 σ ->
  Δ `; Γ1 ⊢ M `: A ->
  Δ `; Γ2 ⊢ M.[σ] `: A.
Proof.
  intros Hlook.
  induction 1 in Γ2, σ, Hlook |- *; asimpl; eauto.
Qed.

Local Hint Resolve judge_subst : core.

Lemma lookup_subst_cons Δ A Γ N :
  Δ `; Γ ⊢ N `: A ->
  lookup_subst Δ (A :: Γ) Γ (N .: ids).
Proof.
  unfold lookup_subst.
  intros HN [| x] B HxB; asimpl in *.
  - injection HxB as <-. assumption.
  - constructor. assumption.
Qed.

Local Hint Resolve lookup_subst_cons : core.

Lemma judge_subst_single Δ M N Γ A B :
  Δ `; Γ ⊢ N `: A ->
  Δ `; A :: Γ ⊢ M `: B ->
  Δ `; Γ ⊢ M.[N/] `: B.
Proof.
  eauto.
Qed.

Lemma wf_judge Δ Γ M A :
  Δ `; Γ ⊢ M `: A ->
  Forall (wf_typ Δ) Γ ->
  Δ ⊢wf A.
Proof.
  induction 1; intro HG;
    repeat lazymatch goal with
      | IH: ?A -> _, H: ?A |- _ => specialize IH with (1:=H)
      | IH: Forall (wf_typ (S ?D)) (up__Γ ?G) -> _, H: Forall (wf_typ ?D) ?G
        |- _ => specialize IH with (1:=Forall_wf_typ_S _ _ HG)
      end;
    eauto.
  - specialize (Forall_lookup_1 (A:=typ)) with (1:=HG) (2:=H). auto.
  - inversion IHjudge1; subst. assumption.
  - inversion IHjudge; subst. eauto.
Qed.

Lemma preservation__b M N A :
  M ~>b N -> 0 `; [] ⊢ M `: A -> 0 `; [] ⊢ N `: A.
Proof.
  inversion 1; subst.
  - intros (B & (C & [= <- <-] & HB & HM)%inv_judge_abs & Hn)%inv_judge_app.
    eauto.
  - intros (B & -> & HA & HM%inv_judge_tabs)%inv_judge_tapp.
    cbn in HM.
    specialize judge_tsubst_single with (1:=HA) (2:=HM); cbn.
    auto.
  - intros (-> & Hv1 & Hv2)%inv_judge_cast; auto.
  - intros (-> & Hv1 & Hv2)%inv_judge_cast; auto.
Qed.

Definition judge__k K A B :=
  forall M, 0 `; [] ⊢ M `: A -> 0 `; [] ⊢ K [[ M ]] `: B.

Notation "'⊢k' K '`:' A '`⇒' B" := (judge__k K A B) (at level 80) : type_scope.

Ltac solve_decomp :=
  inversion 1; subst;
  lazymatch goal with
  | IH: (forall _, 0 `; [] ⊢ ?K [[ ?M ]] `: _ -> _),
      H: (0 `; [] ⊢ ?K [[ ?M ]] `: _) |- _ =>
      specialize IH with (1:=H) as (? & ? & ?);
      eexists; split; eauto; intros ? ?; cbn; eauto
  end.

Lemma decomp__k K M B :
  0 `; [] ⊢ K [[ M ]] `: B ->
  exists A, 0 `; [] ⊢ M `: A /\ ⊢k K `: A `⇒ B.
Proof.
  induction K in B |- *; cbn;
    try solve_decomp.
  - intros HM. exists B. split; eauto.
    intros N HN; cbn. assumption.
Qed.

Lemma composition__k K M A B :
  ⊢k K `: A `⇒ B -> 0 `; [] ⊢ M `: A -> 0 `; [] ⊢ K [[ M ]] `: B.
Proof.
  unfold judge__k. eauto.
Qed.

Lemma preservation M M' A :
  M ~> M' -> 0 `; [] ⊢ M `: A -> 0 `; [] ⊢ M' `: A.
Proof.
  intros (N & N' & K & -> & -> & HNN')%inv_step HKN.
  pose proof decomp__k _ _ _ HKN as (B & HN & HK).
  pose proof preservation__b _ _ _ HNN' HN as HN'.
  eauto.
Qed.

Infix "~>*" := (rtc step) (at level 80) : type_scope.

Definition safe M := forall M', M ~>* M' -> progressive M'.

Lemma safety M A :
  0 `; [] ⊢ M `: A -> safe M.
Proof.
  intros HM M' HMM'.
  induction HMM'.
  - eauto using progress_trm.
  - pose proof preservation _ _ _ H HM as Hy.
    auto.
Qed.

Reserved Infix "↓" (at level 80, no associativity).

Inductive big : trm -> val -> Prop :=
| big_abs A M :
  (λ: A `, M)%trm ↓ (λ: A `, M)%val
| big_app A (L M N : trm) m v :
  L ↓ (λ: A `, N)%val ->
  M ↓ m ->
  N.[inj__v m/] ↓ v ->
  L M ↓ v
| big_tabs M :
  (Λ M)%trm ↓ (Λ M)%val
| big_tapp M N A v :
  M ↓ (Λ N)%val ->
  N.|[A/] ↓ v ->
  (M `[A]`)%trm ↓ v
where "M '↓' v" := (big M%trm v%val) : type_scope.

Section castbad.
  Let D := (`∀ Ident 0 `→ Ident 0)%typ.

  Let callD M := (M `[D]`)%trm.

  Let makeD M := (Λ cast (D `→ D) (Ident 0 `→ Ident 0) (λ: Ident 0 `, ident 0) M)%trm.
  
  Let ω := makeD (λ: D `, (callD (ident 0)) (ident 0))%trm.

  Let Ω := (callD ω) ω.

  Lemma D_wf Δ :
    Δ ⊢wf D.
  Proof.
    constructor.
    constructor; eauto with lia.
  Qed.

  Local Hint Resolve D_wf : core.
  
  Lemma callD_judge Δ Γ M A :
    Δ `; Γ ⊢ M `: (`∀ A)%typ ->
    Δ `; Γ ⊢ callD M `: A.[D/].
  Proof.
    intros HM.
    constructor; eauto.
  Qed.

  Local Hint Resolve callD_judge : core.
  
  Lemma makeD_judge Δ Γ M :
    S Δ `; up__Γ Γ ⊢ M `: (D `→ D)%typ ->
    Δ `; Γ ⊢ makeD M `: D.
  Proof.
    constructor.
    constructor; eauto with lia.
  Qed.

  Local Hint Resolve makeD_judge : core.

  Lemma judge_ω Δ Γ :
    Δ `; Γ ⊢ ω `: D.
  Proof.
    apply makeD_judge.
    constructor; eauto.
    econstructor; eauto.
    replace (D `→ D)%typ with ((Ident 0 `→ Ident 0)%typ.[D/]) by by asimpl.
    eauto.
  Qed.

  Local Hint Resolve judge_ω : core.

  Lemma judge_Ω Δ Γ :
    Δ `; Γ ⊢ Ω `: D.
  Proof.
    econstructor; eauto.
    replace (D `→ D)%typ with ((Ident 0 `→ Ident 0)%typ.[D/]) by by asimpl.
    eauto.
  Qed.

  Lemma rew_ω :
    ω = (Λ cast (D `→ D) (Ident 0 `→ Ident 0) (λ: Ident 0 `, ident 0) (λ: D `, (ident 0 `[ D ]`) (ident 0)))%trm.
  Proof.
    reflexivity.
  Qed.

  Lemma rew_Ω :
    Ω = (ω `[ D ]`)%trm ω.
  Proof.
    reflexivity.
  Qed.

  Lemma ω_is_val : is_val ω.
  Proof.
    rewrite rew_ω.
    eauto.
  Qed.

  Local Hint Resolve ω_is_val : core.
  
  Lemma Ω_bad :
    Ω ~>* Ω.
  Proof.
    rewrite rew_Ω.
    rewrite {1} rew_ω.
    apply rtc_l with (y:=(cast (D `→ D) (Ident 0 `→ Ident 0) (λ: Ident 0 `, ident 0) (λ: D `, (ident 0 `[ D ]`) (ident 0)))%trm.|[D/] ω); eauto.
    asimpl.
    apply rtc_l with (y:=(λ: D `, (ident 0 `[ D ]`) (ident 0))%trm ω); eauto.
    apply rtc_l with (y:=(ω `[D]`)%trm ω); eauto.
    reflexivity.
  Qed.
    
End castbad.

