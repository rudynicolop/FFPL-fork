From Autosubst Require Export Autosubst.
From ffpl.lib Require Export maps.
From Equations Require Export Equations.

Inductive typ :=
(* Minmal System F types. *)
| Ident (X : var)
| Fun (A B : typ)
| Uni (A : {bind 1 of typ})
(* Existentials. *)
| Exi (A : {bind 1 of typ})
(* Simple types. *)
(* | Unit *)
(* | Bool *)
(* | Int *)
(* | Prd (A B : typ) *)
(* | Sum (A B : typ) *)
.
  
#[export] Instance Ids_typ : Ids typ. derive. Defined.
#[export] Instance Rename_typ : Rename typ. derive. Defined.
#[export] Instance Subst_typ : Subst typ. derive. Defined.
#[export] Instance SubstLemmas_typr : SubstLemmas typ. derive. Qed.

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
Notation "'`∃' A" :=
  (Exi A%typ)
    (at level 100, A at level 200)
    : typ_scope.
(* Infix "×" := *)
(*   Prd *)
(*     (at level 100, right associativity) *)
(*     : typ_scope. *)
(* Infix "`+" := *)
(*   Sum *)
(*     (at level 100, right associativity) *)
(*     : typ_scope. *)

(* Variant exec := Done | More. *)

Section trm.
  Variable (T : Type).

  Inductive trm : (*exec ->*) Type :=
  (* Minimal System F runtime terms. *)
  | ident
      (x : var)
  (* : trm More *)
  | abs
      (* {e : exec} *)
      (A : T)
      (M : {bind 1 of trm})
  (* : trm Done *)
  | app
      (* {e1 e2 : exec} *)
      (M : trm)
      (N : trm)
  (* : trm More *)
  | tabs
      (* {e : exec} *)
      (M : trm)
  (* : trm e *)
  | tapp
      (* {e : exec} *)
      (N : trm)
      (A : T)
  (* : trm More *)
  (* Existential terms *)
  | pack
      (* {e : exec} *)
      (A : T)
      (M : trm)
  (* : trm e *)
  | unpack
      (* {e1 e2 : exec} *)
      (M : trm)
      (N : {bind 1 of trm})
  (* : trm More *)
  (* Simple terms. *)
  (* | one *)
  (* | two (b : bool) *)
  (* | int (z : Z) *)
  .

  #[export] Instance Ids_trm : Ids trm. derive. Defined.
  #[export] Instance Rename_trm : Rename trm. derive. Defined.
  #[export] Instance Subst_trm : Subst trm. derive. Defined.
  #[export] Instance SubstLemmas_trm : SubstLemmas trm. derive. Qed.
End trm.

Arguments ident {_}.
Arguments abs {_}.
Arguments app {_}.
Arguments tabs {_}.
Arguments tapp {_}.
Arguments pack {_}.
Arguments unpack {_}.

Definition strm := trm typ.
Definition rtrm := trm unit.

Declare Scope strm_scope.
Delimit Scope strm_scope with strm.
Bind Scope strm_scope with strm.

Declare Scope rtrm_scope.
Delimit Scope rtrm_scope with rtrm.
Bind Scope rtrm_scope with rtrm.

(* Coercion ident : var >-> strm. *)
(* Coercion app : strm >-> Funclass. *)
(* Coercion ident : var >-> rtrm. *)
(* Coercion app : rtrm >-> Funclass. *)

Notation "'λ:' A `, M" := (abs A%typ M%strm) (at level 100, right associativity) : strm_scope.
Notation "'`λ' M" := (abs tt M%rtrm) (at level 100, right associativity) : rtrm_scope.
Notation "'Λ' M" := (tabs M%strm) (at level 100, right associativity) : strm_scope.
Notation "'Λ' M" := (tabs M%rtrm) (at level 100, right associativity) : rtrm_scope.
Notation "M '`[' A  ']`'" := (tapp M%strm A%typ) (at level 98, left associativity) : strm_scope.
Notation "M '[-]'" := (tapp M%rtrm tt) (at level 98, left associativity) : rtrm_scope.

Inductive val :=
| abs__v (M : rtrm)
| tabs__v (M : rtrm)
| pack__v (v : val).

Declare Scope val_scope.
Delimit Scope val_scope with val.
Bind Scope val_scope with val.

Notation "'λv' M" := (abs__v M%rtrm) (at level 100, right associativity) : val_scope.
Notation "'Λv' M" := (tabs__v M%rtrm) (at level 100, right associativity) : val_scope.

Fixpoint inj__v (v : val) : rtrm :=
  match v with
  | (λv M)%val => `λ M
  | (Λv M)%val => Λ M
  | (pack__v v)%val => pack tt $ inj__v v
  end.

Lemma inj_inj__v v1 v2 :
  inj__v v1 = inj__v v2 -> v1 = v2.
Proof.
  induction v1 as [M1 | M1 | v1 IHv1] in v2 |- *;
    destruct v2 as [M2 | M2 | v2]; cbn;
    discriminate || (try injection 1 as <-); try reflexivity.
  - injection 1 as Hv.
    specialize IHv1 with (1:=Hv) as <-. reflexivity.
Qed.

Definition is_val (M : rtrm) : Prop :=
  exists v, inj__v v = M.

Lemma val_is_val (v : val) :
  is_val (inj__v v).
Proof.
  eexists; eauto.
Qed.

Lemma abs_is_val M : is_val (`λ M)%rtrm.
Proof.
  unfold is_val.
  exists (λv M)%val.
  reflexivity.
Qed.

Lemma tabs_is_val M : is_val (Λ M)%rtrm.
Proof.
  exists (Λv M)%val.
  reflexivity.
Qed.

Lemma pack_is_val M :
  is_val M -> is_val (pack tt M).
Proof.
  unfold is_val.
  intros (v & <-).
  exists (pack__v v).
  reflexivity.
Qed.

Local Hint Resolve abs_is_val : core.
Local Hint Resolve tabs_is_val : core.
Local Hint Resolve pack_is_val : core.
Local Hint Resolve val_is_val : core.

Coercion inj__v : val >-> rtrm.

Definition ident_not_val x (v : val) :
  ident x <> inj__v v.
Proof.
  destruct v; cbn; discriminate.
Qed.

Definition app_not_val M N (v : val) :
  app M N <> inj__v v.
Proof.
  destruct v; cbn; discriminate.
Qed.

Definition tapp_not_val M (v : val) :
  (M [-])%rtrm <> inj__v v.
Proof.
  destruct v; cbn; discriminate.
Qed.

Definition unpack_not_val M N (v : val) :
  unpack M N <> inj__v v.
Proof.
  destruct v; cbn; discriminate.
Qed.

Inductive ktx :=
| hole
| app__l (K : ktx) (v : val)
| app__r (M : rtrm) (K : ktx)
| tapp__k (K : ktx)
| pack__k (K : ktx)
| unpack__k (K : ktx) (N : rtrm).

Reserved Notation "K '[[' M ']]'"
  (at level 98, left associativity).

Fixpoint fill__k (K : ktx) (M : rtrm) : rtrm :=
  match K with
  | hole => M
  | app__l K N => app (K [[ M ]]) $ inj__v N
  | app__r N K => app N (K [[ M ]])
  | tapp__k K  => tapp (K [[ M ]]) tt
  | pack__k K  => pack tt (K [[ M ]])
  | unpack__k K N => unpack (K [[ M ]]) N
  end
where "K '[[' M ']]'" :=
  (fill__k K M%rtrm) : rtrm_scope.

Reserved Infix "`∘" (at level 98, left associativity).

Fixpoint comp__k (K K' : ktx) : ktx :=
  match K with
  | hole => K'
  | app__l K N => app__l (K `∘ K') N
  | app__r N K => app__r N (K `∘ K')
  | tapp__k K  => tapp__k (K `∘ K')
  | pack__k K  => pack__k (K `∘ K')
  | unpack__k K N => unpack__k (K `∘ K') N
  end
where "K1 '`∘' K2" := (comp__k K1 K2).

Lemma fill_comp__k K K' M :
  ((K `∘ K') [[ M ]])%rtrm = (K [[ K' [[ M ]] ]])%rtrm.
Proof.
  induction K; cbn; f_equal; auto.
Qed.

Reserved Infix "~>b" (at level 80, no associativity).

Variant step__b : rtrm -> rtrm -> Prop :=
| step_abs_beta M (n : val) :
  app (`λ M) (inj__v n) ~>b M.[ inj__v n /]
| step_tabs_beta M :
  (Λ M) [-] ~>b M
| step_unpack_beta (v : val) N :
  unpack (pack tt (inj__v v)) N ~>b N.[ inj__v v /]
where "M '~>b' N" := (step__b M%rtrm N%rtrm) : type_scope.

Reserved Infix "~>" (at level 80, no associativity).

Variant step : rtrm -> rtrm -> Prop :=
  | step_ktx M N K :
    M ~>b N ->
    (K [[ M ]])%rtrm ~> (K [[ N ]])%rtrm
where "M '~>' N" := (step M%rtrm N%rtrm) : type_scope.

Lemma inv_step KM KN :
  KM ~> KN -> exists M N K, KM = (K [[ M ]])%rtrm /\ KN = (K [[ N ]])%rtrm /\ M ~>b N.
Proof.
  inversion 1; subst.
  do 3 eexists. eauto.
Qed.

Local Hint Constructors step__b : core.
Local Hint Constructors step : core.

Ltac solve_ident_not_val :=
  match goal with
    H : _ = inj__v _ |- _ =>
      apply ident_not_val in H; contradiction
  end.
Local Hint Extern 0 => solve_ident_not_val : core.
Ltac solve_app_not_val :=
  match goal with
    H : _ = inj__v _ |- _ =>
      apply app_not_val in H; contradiction
  end.
Local Hint Extern 0 => solve_app_not_val : core.
Ltac solve_tapp_not_val :=
  match goal with
    H : _ = inj__v _ |- _ =>
      apply tapp_not_val in H; contradiction
  end.
Local Hint Extern 0 => solve_tapp_not_val : core.
Ltac solve_unpack_not_val :=
  match goal with
    H : _ = inj__v _ |- _ =>
      apply unpack_not_val in H; contradiction
  end.
Local Hint Extern 0 => solve_unpack_not_val : core.

Lemma val_not_step__b (v : val) N :
  ~ (v ~>b N).
Proof.
  inversion 1; subst; eauto.
Qed.

Local Hint Resolve val_not_step__b : core.

Lemma val_fill__k K M (v : val) :
  (K [[ M ]])%rtrm = v -> is_val M.
Proof.
  revert v.
  induction K; intros []; cbn; try discriminate.
  - intros ->; auto.
  - intros ->; auto.
  - intros ->; auto.
  - injection 1 as hv. eauto.
Qed.

Local Hint Resolve val_fill__k : core.

Lemma val_not_step (v : val) N :
  ~ (v ~> N).
Proof.
  inversion 1; subst; eauto.
  apply val_fill__k in H0.
  destruct H0 as [v' <-].
  revert H1. apply val_not_step__b.
Qed.

Lemma ctx_lift M N K :
  M ~> N ->
  (K [[ M ]])%rtrm ~> (K [[ N ]])%rtrm.
Proof.
  inversion 1; subst.
  do 2 rewrite <- fill_comp__k.
  eauto.
Qed.

Local Hint Resolve ctx_lift : core.

Lemma abs_beta M (n : val) :
  app (`λ M) (inj__v n) ~> M.[ inj__v n /].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve abs_beta : core.

Lemma tabs_beta M :
  (Λ M) [-] ~> M.
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve tabs_beta : core.

Lemma unpack_pack (v : val) N :
  unpack (pack tt (inj__v v)) N ~> N.[ inj__v v /].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve unpack_pack : core.

Lemma step_app__r (M N N' : rtrm) :
  N ~> N' ->
  app M N ~> app M N'.
Proof.
  replace (app M N) with (app__r M hole [[ N ]])%rtrm by reflexivity.
  replace (app M N') with (app__r M hole [[ N' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_app__r : core.

Lemma step_app__l M M' (v : val) :
  M ~> M' ->
  app M (inj__v v) ~> app M' (inj__v v).
Proof.
  replace (app M (inj__v v)) with (app__l hole v [[ M ]])%rtrm by reflexivity.
  replace (app M' (inj__v v)) with (app__l hole v [[ M' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_app__l : core.

Lemma step_tapp M M' :
  M ~> M' ->
  (M [-])%rtrm ~> (M' [-])%rtrm.
Proof.
  replace (M [-])%rtrm with (tapp__k hole [[ M ]])%rtrm by reflexivity.
  replace (M' [-])%rtrm with (tapp__k hole [[ M' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_tapp : core.
  
Lemma step_pack M M' :
  M ~> M' ->
  pack tt M ~> pack tt M'.
Proof.
  replace (pack tt M) with (pack__k hole [[ M ]])%rtrm by reflexivity.
  replace (pack tt M') with (pack__k hole [[ M' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_pack : core.

Lemma step_unpack M M' N :
  M ~> M' ->
  unpack M N ~> unpack M' N.
Proof.
  replace (unpack M N) with (unpack__k hole N [[ M ]])%rtrm by reflexivity.
  replace (unpack M' N) with (unpack__k hole N [[ M' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_unpack : core.

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
| wf_Exi A :
  S Δ ⊢wf A ->
  Δ ⊢wf `∃ A
where "Δ '⊢wf' τ" := (wf_typ Δ%nat τ%typ) : type_scope.

Definition up__Γ (Γ : list typ) : list typ:= subst (ren S) <$> Γ.

Reserved Notation "Δ '`;;' Γ '⊢' M '`:' τ" (at level 80).

Inductive judge__s (Δ : nat) (Γ : list typ) : strm -> typ -> Prop :=
| judge_ident__s (x : var) A :
  Γ !! x = Some A ->
  Δ `;; Γ ⊢ ident x `: A
| judge_abs__s M A B :
  Δ ⊢wf A ->
  Δ `;; A :: Γ ⊢ M `: B ->
  Δ `;; Γ ⊢ λ: A `, M `: (A `→ B)
| judge_app__s M N A B :
  Δ `;; Γ ⊢ M `: (A `→ B)%typ ->
  Δ `;; Γ ⊢ N `: A ->
  Δ `;; Γ ⊢ app M N `: B
| judge_tabs__s M A :
  S Δ `;; up__Γ Γ ⊢ M `: A ->
  Δ `;; Γ ⊢ Λ M `: `∀ A
| judge_tapp__s M (A B : typ) :
  Δ ⊢wf B ->
  Δ `;; Γ ⊢ M `: (`∀ A)%typ ->
  Δ `;; Γ ⊢ M `[ B ]` `: A.[ B /]
| judge_pack__s M A B :
  Δ ⊢wf B ->
  Δ `;; Γ ⊢ M `: A.[ B /] ->
  Δ `;; Γ ⊢ pack B M `: `∃ A
| judge_unpack__s M N A B :
  Δ ⊢wf B ->
  Δ `;; Γ ⊢ M `: (`∃ A) ->
  S Δ `;; A :: up__Γ Γ ⊢ N `: subst (ren S) B ->
  Δ `;; Γ ⊢ unpack M N `: B
where "Δ `;; Γ '⊢' M '`:' τ" := (judge__s Δ%nat Γ M%strm τ%typ).

Reserved Notation "Δ `; Γ '⊢' M '`:' τ" (at level 80).

Inductive judge__r (Δ : nat) (Γ : list typ) : rtrm -> typ -> Prop :=
| judge_ident__r (x : var) A :
  Γ !! x = Some A ->
  Δ `; Γ ⊢ ident x `: A
| judge_abs__r M A B :
  Δ ⊢wf A ->
  Δ `; A :: Γ ⊢ M `: B ->
  Δ `; Γ ⊢ `λ M `: (A `→ B)
| judge_app__r M N A B :
  Δ `; Γ ⊢ M `: (A `→ B)%typ ->
  Δ `; Γ ⊢ N `: A ->
  Δ `; Γ ⊢ app M N `: B
| judge_tabs__r M A :
  S Δ `; up__Γ Γ ⊢ M `: A ->
  Δ `; Γ ⊢ Λ M `: `∀ A
| judge_tapp__r M (A B : typ) :
  Δ ⊢wf B ->
  Δ `; Γ ⊢ M `: (`∀ A)%typ ->
  Δ `; Γ ⊢ M [-] `: A.[ B /]
| judge_pack__r M A B :
  Δ ⊢wf B ->
  Δ `; Γ ⊢ M `: A.[ B /] ->
  Δ `; Γ ⊢ pack tt M `: `∃ A
| judge_unpack__r M N A B :
  Δ ⊢wf B ->
  Δ `; Γ ⊢ M `: (`∃ A) ->
  S Δ `; A :: up__Γ Γ ⊢ N `: subst (ren S) B ->
  Δ `; Γ ⊢ unpack M N `: B
where "Δ `; Γ '⊢' M '`:' τ" := (judge__r Δ%nat Γ M%rtrm τ%typ).

Section inv.

  Variable Δ : nat.
  Variable Γ : list typ.
  
  Lemma inv_judge_ident__r x A :
    Δ `; Γ ⊢ ident x `: A ->
    Γ !! x = Some A.
  Proof.
    inversion 1; auto.
  Qed.

  Lemma inv_judge_abs__r M C :
    Δ `; Γ ⊢ `λ M `: C ->
    exists A B, C = (A `→ B)%typ /\ Δ ⊢wf A /\ Δ `; A :: Γ ⊢ M `: B.
  Proof.
    inversion 1; subst.
    eauto.
  Qed.

  Lemma inv_judge_app__r M N B :
    Δ `; Γ ⊢ app M N `: B ->
    exists A, Δ `; Γ ⊢ M `: (A `→ B) /\ Δ `; Γ ⊢ N `: A.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_tabs__r M A :
    Δ `; Γ ⊢ Λ M `: (`∀ A) ->
    S Δ `; up__Γ Γ ⊢ M `: A.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_tapp__r M C :
    Δ `; Γ ⊢ M [-] `: C ->
    exists A B, C = A.[B/] /\ Δ ⊢wf B /\ Δ `; Γ ⊢ M `: (`∀ A).
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_pack__r M C :
    Δ `; Γ ⊢ pack tt M `: C ->
    exists A B, C = (`∃ A)%typ /\ Δ ⊢wf B /\ Δ `; Γ ⊢ M `: A.[B/].
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_unpack__r M N B :
    Δ `; Γ ⊢ unpack M N `: B ->
    exists A, Δ ⊢wf B /\ Δ `; Γ ⊢ M `: (`∃ A) /\ S Δ `; A :: up__Γ Γ ⊢ N `: subst (ren S) B.
  Proof.
    inversion 1; subst; eauto.
  Qed.
End inv.

Fixpoint map_trm {A B} (f : A -> B) (M : trm A) : trm B :=
  match M with
  | ident x    => ident x
  | abs a M    => abs (f a) $ map_trm f M
  | app M N    => app (map_trm f M) $ map_trm f N
  | tabs M     => tabs $ map_trm f M
  | tapp M a   => tapp (map_trm f M) $ f a
  | pack a M   => pack (f a) $ map_trm f M
  | unpack M N => unpack (map_trm f M) $ map_trm f N
  end.

Definition erase : strm -> rtrm := map_trm (fun _ => tt).

Local Hint Constructors judge__s : core.
Local Hint Constructors judge__r : core.

Lemma judge_erase Δ Γ M A :
  Δ `;; Γ ⊢ M `: A ->
  Δ `;  Γ ⊢ erase M `: A.
Proof.
  induction 1; cbn; eauto.
Qed.

Section canon.
  Variable Δ : nat.
  Variable Γ : list typ.
  
  Lemma canon_fun (v : val) A B :
    Δ `; Γ ⊢ v `: (A `→ B)%typ ->
    exists N, v = (λv N)%val.
  Proof.
    inversion 1; subst; eauto.
    - exists M. destruct v; inversion H0; reflexivity.
  Qed.

  Lemma canon_uni (v : val) A :
    Δ `; Γ ⊢ v `: (`∀ A)%typ ->
    exists M, v = (Λv M)%val.
  Proof.
    inversion 1; subst; eauto.
    exists M. destruct v; inversion H0; reflexivity.
  Qed.

  Lemma canon_exi (v : val) A :
    Δ `; Γ ⊢ v `: (`∃ A) ->
    exists v', v = pack__v v'.
  Proof.
    inversion 1; subst; eauto.
    destruct v; inversion H0; eauto.
  Qed.
End canon.

Definition progressive (M : rtrm) : Prop :=
  (exists N, M ~> N) \/ is_val M.

Theorem progress_rtrm M A :
  0 `; [] ⊢ M `: A -> progressive M.
Proof.
  remember 0 as Δ eqn:eqΔ.
  remember [] as Γ eqn:eqΓ.
  induction 1; subst; auto;
    repeat match goal with
      | h: 0 = 0 -> [] = [] -> _ |- _
        => specialize h with (1:=eq_refl) (2:=eq_refl)
      end.
  - rewrite lookup_nil in H.
    discriminate.
  - right; auto.
  - left.
    destruct IHjudge__r2 as [(N' & HN) | (n & <-)].
    + exists (app M N'). auto.
    + destruct IHjudge__r1 as [(M' & HM) | (m & <-)].
      * exists (app M' (inj__v n)). auto.
      * apply canon_fun in H as [M ->]. cbn. eauto.
  - right; auto.
  - left. destruct IHjudge__r as [(M' & HM) | (m & <-)].
    + exists (M' [-])%rtrm. auto.
    + apply canon_uni in H0 as [M ->]. cbn. eauto.
  - destruct IHjudge__r as [(M' & HM) | (m & <-)].
    + left. exists (pack tt M'). auto.
    + right. exists (pack__v m). auto.
  - clear IHjudge__r2. left.
    destruct IHjudge__r1 as [(M' & HM) | (m & <-)].
    + exists (unpack M' N). auto.
    + apply canon_exi in H0 as [v ->].
      exists N.[(inj__v v) /]. cbn. auto.
Qed.

Definition wf_tsubst Δ1 Δ2 σ :=
  forall α, α < Δ1 -> Δ2 ⊢wf σ α.

Definition wf_tren Δ1 Δ2 (δ : var -> var) :=
  forall α, α < Δ1 -> δ α < Δ2.

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

Local Hint Constructors wf_typ : core.

Lemma wf_typ_rename Δ1 Δ2 A δ :
  wf_tren Δ1 Δ2 δ ->
  Δ1 ⊢wf A ->
  Δ2 ⊢wf A.[ren δ].
Proof.
  intros Htren.
  induction 1 in Δ2, Htren, δ |-*; asimpl; eauto.
Qed.

Local Hint Resolve wf_typ_rename : core.

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
  Δ2 `; (subst σ) <$> Γ ⊢ M `: A.[σ].
Proof.
  intros Hσ.
  induction 1 in Hσ, σ, Δ2 |- *; cbn; eauto.
  - constructor.
    rewrite list_lookup_fmap.
    apply fmap_Some_2. assumption.
  - constructor.
    rewrite up_subst. eauto.
  - replace (A.[B/].[σ]) with (A.[up σ].[B.[σ]/])
      by by asimpl. eauto.
  - apply judge_pack__r with (B := subst σ B); eauto.
    replace (A.[up σ].[B.[ σ]/]) with (A.[B/].[σ])
      by by asimpl. eauto.
  - apply judge_unpack__r with (A:=A.[up σ]); eauto.
    rewrite up_subst. asimpl in IHjudge__r2.
    replace (B.[σ].[ren S]) with (B.[ren S].[up σ])
      by by asimpl. eauto.
Qed.

Local Hint Resolve judge_tsubst : core.

Lemma judge_tsubst_single Δ Γ M A B :
  Δ ⊢wf B ->
  S Δ `; Γ ⊢ M `: A ->
  Δ `; (fun C => C.[B/]) <$> Γ ⊢ M `: A.[ B /].
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
  - constructor. eauto.
  - econstructor; eauto.
Qed.

Local Hint Resolve judge_rename : core.

Definition lookup_subst Δ (Γ1 Γ2 : list typ) (σ : var -> rtrm) :=
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
  lookup_subst (S Δ) (up__Γ Γ1) (up__Γ Γ2) σ.
Proof.
  unfold lookup_subst, up__Γ.
  intros Hlook x B HB.
  rewrite list_lookup_fmap in HB.
  apply fmap_Some in HB as (A & HxA & ->).
  specialize Hlook with (1:=HxA).
  apply judge_tsubst with (Δ1 := Δ); eauto.
  rewrite <- wf_tren_tsubst. eauto.
Qed.

Local Hint Resolve lookup_subst_up__Γ : core.

Lemma judge_subst σ Δ M Γ1 Γ2 A :
  lookup_subst Δ Γ1 Γ2 σ ->
  Δ `; Γ1 ⊢ M `: A ->
  Δ `; Γ2 ⊢ M.[σ] `: A.
Proof.
  intros Hlook.
  induction 1 in Γ2, σ, Hlook |- *; asimpl; eauto.
  - econstructor; eauto.
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

Lemma preservation__b M N A :
  M ~>b N -> 0 `; [] ⊢ M `: A -> 0 `; [] ⊢ N `: A.
Proof.
  inversion 1; subst.
  - intros (B & (C & D & HCD & HC & HM)%inv_judge_abs__r & HN)%inv_judge_app__r.
    injection HCD as <- <-. eauto.
  - intros (B & C & -> & HB & HM%inv_judge_tabs__r)%inv_judge_tapp__r; cbn in *.
    replace [] with ((fun A => A.[C/]) <$> []) by reflexivity. eauto.
  - (** Tricksy **)
    intros (B & HA & (C & D & HCD & HD & Hv)%inv_judge_pack__r & HN)%inv_judge_unpack__r.
    injection HCD as <-. cbn in *.
    apply judge_subst_single with (A:=B.[D/]); eauto.
    replace A with (A.[ren S].[D/]) by by asimpl.
    replace [B.[D/]] with ((fun C => C.[D/]) <$> [B]) by reflexivity. eauto.
Qed.

Definition judge__k K A B :=
  forall M, 0 `; [] ⊢ M `: A -> 0 `; [] ⊢ K [[ M ]] `: B.

Notation "'⊢k' K '`:' A '`⇒' B" := (judge__k K A B) (at level 80) : type_scope.

Lemma decomp__k K M B :
  0 `; [] ⊢ K [[ M ]] `: B ->
  exists A, 0 `; [] ⊢ M `: A /\ ⊢k K `: A `⇒ B.
Proof.
  induction K in B |- *; cbn.
  - intros HM. exists B. split; eauto.
    intros N HN; cbn. assumption.
  - intros (A & HKM & Hv)%inv_judge_app__r.
    specialize IHK with (1:=HKM).
    destruct IHK as (C & HM & HK).
    eexists; split; eauto.
    intros N HN. cbn. eauto.
  - intros (A & HM0 & HKM)%inv_judge_app__r.
    specialize IHK with (1:=HKM).
    destruct IHK as (C & HM & HK).
    eexists; split; eauto.
    intros N HN. cbn. eauto.
  - intros (C & D & -> & HB & HKM)%inv_judge_tapp__r.
    specialize IHK with (1:=HKM).
    destruct IHK as (A & HM & HK).
    eexists; split; eauto.
    intros N HN. cbn. eauto.
  - intros (A & C & -> & HB & HKM)%inv_judge_pack__r.
    specialize IHK with (1:=HKM).
    destruct IHK as (B & HM & HK).
    eexists; split; eauto.
    intros N HN. cbn. eauto.
  - intros (A & HB & HKM & HN)%inv_judge_unpack__r.
    specialize IHK with (1:=HKM).
    destruct IHK as (C & HM & HK).
    cbn in *. eexists; split; eauto.
    intros O HO. cbn. eauto.
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
  - eauto using progress_rtrm.
  - pose proof preservation _ _ _ H HM as Hy.
    auto.
Qed.

Reserved Infix "⇓" (at level 80, no associativity).

Inductive big : rtrm -> val -> Prop :=
| big_abs M :
  (`λ M)%rtrm ⇓ (λv M)%val
| big_app (L M N : rtrm) m v :
  L ⇓ (λv N)%val ->
  M ⇓ m ->
  N.[inj__v m/] ⇓ v ->
  app L M ⇓ v
| big_tabs M :
  (Λ M)%rtrm ⇓ (Λv M)%rtrm
| big_tapp M N v :
  M ⇓ (Λv N)%val ->
  N ⇓ v ->
  (M [-])%rtrm ⇓ v
| big_pack M v :
  M ⇓ v ->
  pack tt M ⇓ pack__v v
| big_unpack M N m v :
  M ⇓ pack__v m ->
  N.[inj__v m/] ⇓ v ->
  unpack M N ⇓ v
where "M '⇓' v" := (big M%rtrm v%val) : type_scope.

Equations size__t : typ -> nat :=
| Ident _ := 1
| (A `→ B)%typ := 1 + size__t A + size__t B
| (`∀ A)%typ := 2 + size__t A
| (`∃ A)%typ := 2 + size__t A.

Lemma zero_size__t A :
  0 < size__t A.
Proof.
  funelim (size__t A); eauto with lia.
Qed.

Local Hint Resolve zero_size__t : core.

Equations measure_interp__t : val + rtrm -> typ -> nat :=
| inl _, A := size__t A
| inr _, A := 1 + size__t A.

Definition sem__t := val -> Prop.

Equations interp__t
  (ve : val + rtrm)
  (A : typ)
  (δ : var -> sem__t)
  : Prop by wf (measure_interp__t ve A) :=
| (inl v), Ident α, δ := δ α v
| (inl v), (A `→ B)%typ, δ :=
    exists M, v = (λv M)%val /\ forall v, interp__t (inl v) A δ -> interp__t (inr M.[inj__v v/]) B δ
| (inl v), (`∀ A)%typ, δ :=
    exists M, v = (Λv M)%val /\ forall τ : sem__t, interp__t (inr M) A (τ .: δ)
| (inl v), (`∃ A)%typ, δ :=
    exists m, v = pack__v m /\ exists τ : sem__t,
        interp__t (inl m) A (τ .: δ)
| (inr M), A, δ :=
    exists v, M ⇓ v /\ interp__t (inl v) A δ.
Next Obligation.
  simp measure_interp__t.
  simp size__t. lia.
Qed.
Next Obligation.
  simp measure_interp__t.
  simp size__t.
  pose proof zero_size__t A. lia.
Qed.
Next Obligation.
  simp measure_interp__t.
  simp size__t. lia.
Qed.

Notation "'V⟦' A '⟧'" :=
  (fun δ v => interp__t (inl v%val) A%typ δ)
    (at level 80) : type_scope.

Notation "'E⟦' A '⟧'" :=
  (fun δ M => interp__t (inr M%rtrm) A%typ δ)
    (at level 80) : type_scope.

Definition sem__Γ (Γ : list typ) (δ : var -> sem__t) (γ : var -> rtrm) :=
  forall x A, Γ !! x = Some A -> E⟦ A ⟧ δ (γ x).

Notation "'G⟦' Γ '⟧'" :=
  (sem__Γ Γ) (at level 80) : type_scope.

Local Hint Constructors big : core.

Lemma big__v (v : val) : v ⇓ v.
Proof.
  induction v as [M | M | v ih]; cbn; eauto.
Qed.

Local Hint Resolve big__v : core.

Lemma incl__v A δ v :
  V⟦ A ⟧ δ v -> E⟦ A ⟧ δ v.
Proof.
  intros Hv. cbn in Hv |- *.
  simp interp__t. eauto.
Qed.

Local Hint Resolve incl__v : core.

Lemma nil_sem__Γ δ γ : G⟦ [] ⟧ δ γ.
Proof.
  intros x A HxA. discriminate.
Qed.

Lemma cons_sem__Γ A Γ δ v γ :
  V⟦ A ⟧ δ v ->
  G⟦ Γ ⟧ δ γ ->
  G⟦ A :: Γ ⟧ δ (inj__v v .: γ).
Proof.
  intros Hv HG [| x] B HB; cbn in HB |- *; eauto.
  injection HB as <-. eauto.
Qed.

Definition sem_judge Γ M A :=
  forall δ γ, G⟦ Γ ⟧ δ γ -> E⟦ A ⟧ δ M.[γ].

Notation "Γ '⊨' M '`:' A" := (sem_judge Γ M%rtrm A%typ) (at level 80, no associativity) : type_scope.

Module boring.
  Lemma cons__δ (δ δ' : var -> sem__t) τ :
    (forall α v, δ α v -> δ' α v) ->
    (forall α v, (τ .: δ) α v -> (τ .: δ') α v).
  Proof.
    intros H [| α] v Hv; asimpl in *; auto.
  Qed.

  Local Hint Resolve cons__δ : core.
  
  Lemma l__v1 A (δ δ' : var -> sem__t) v :
    (forall α v, δ α v <-> δ' α v) ->
    V⟦ A ⟧ δ v -> V⟦ A ⟧ δ' v.
  Proof.
    intros H.
    unfold "<->" in H.
    setoid_rewrite forall_and_distr in H.
    rewrite forall_and_distr in H.
    destruct H as [Hδ Hδ'].
    induction A in δ, δ', v, Hδ, Hδ' |- *;
      intros Hv; simp interp__t in Hv |- *.
    - destruct Hv as (M & -> & HM).
      exists M. split; eauto.
      intros v Hv.
      specialize IHA1 with (1:=Hδ') (2:=Hδ) (3:=Hv).
      specialize IHA2 with (1:=Hδ) (2:=Hδ').
      specialize HM with (1:=IHA1).
      simp interp__t in HM |- *.
      destruct HM as (m & HM & Hm).
      specialize IHA2 with (1:=Hm).
      eauto.
    - destruct Hv as (M & -> & HM).
      exists M. split; auto.
      intros τ.
      specialize HM with (τ:=τ).
      simp interp__t in HM |- *.
      destruct HM as (v & HM & Hv). eauto 7.
    - destruct Hv as (m & -> & τ & Hm). eauto 7.
  Qed.

  Local Hint Resolve l__v1 : core.
  
  Lemma l__v A (δ δ' : var -> sem__t) v :
    (forall α v, δ α v <-> δ' α v) ->
    V⟦ A ⟧ δ v <-> V⟦ A ⟧ δ' v.
  Proof.
    split; eauto using iff_sym.
  Qed.

  Lemma l__e1 A (δ δ' : var -> sem__t) M :
    (forall α v, δ α v <-> δ' α v) ->
    E⟦ A ⟧ δ M -> E⟦ A ⟧ δ' M.
  Proof.
    intros H HM; cbn in HM |- *.
    simp interp__t in HM |- *.
    destruct HM as (v & HM & Hv).
    eexists; eauto.
  Qed.

  Local Hint Resolve l__e1 : core.
  
  Lemma l__e A (δ δ' : var -> sem__t) M :
    (forall α v, δ α v <-> δ' α v) ->
    E⟦ A ⟧ δ M <-> E⟦ A ⟧ δ' M.
  Proof.
    split; eauto using iff_sym.
  Qed.

  Lemma l__Γ1 Γ (δ δ' : var -> sem__t) γ :
    (forall α v, δ α v <-> δ' α v) ->
    G⟦ Γ ⟧ δ γ -> G⟦ Γ ⟧ δ' γ.
  Proof.
    intros H Hγ α A HA.
    unfold sem__Γ in Hγ.
    specialize Hγ with (1:=HA).
    simp interp__t in Hγ |- *.
    destruct Hγ as (v & Hα & Hv).
    eauto.
  Qed.

  Local Hint Resolve l__Γ1 : core.

  Lemma l__Γ Γ (δ δ' : var -> sem__t) γ :
    (forall α v, δ α v <-> δ' α v) ->
    G⟦ Γ ⟧ δ γ <-> G⟦ Γ ⟧ δ' γ.
  Proof.
    split; eauto using iff_sym.
  Qed.

  Lemma ren_sem__tv A (δ : var -> sem__t) (ρ : var -> var) v :
    V⟦ A ⟧ (ρ >>> δ) v <-> V⟦ A.[ren ρ] ⟧ δ v.
  Proof.
    induction A in δ, ρ, v |- *;
      asimpl; simp interp__t; eauto.
    - split; intros (M & -> & HM);
        eexists; split; eauto;
        intros v Hv.
      + rewrite <- IHA1 in Hv.
        specialize HM with (1:=Hv).
        simp interp__t in HM |- *.
        destruct HM as (m & HM & Hm).
        rewrite IHA2 in Hm.
        eexists; split; eauto.
      + rewrite IHA1 in Hv.
        specialize HM with (1:=Hv).
        simp interp__t in HM |- *.
        destruct HM as (m & HM & Hm).
        rewrite <- IHA2 in Hm.
        eexists; eauto.
    - split; intros (M & -> & HM);
        esplit; split; eauto;
        intros τ; specialize HM with (τ:=τ);
        simp interp__t in HM |- *;
        destruct HM as (m & HM & Hm);
        esplit; split; eauto.
      + rewrite <- IHA.
        revert Hm.
        apply l__v1.
        intros [| α] v; asimpl; auto.
      + rewrite <- IHA in Hm.
        revert Hm.
        apply l__v1.
        intros [| α] v; asimpl; auto.
    - split; intros (m & -> & τ & Hm);
        eexists; split; eauto; exists τ.
      + rewrite <- IHA.
        revert Hm.
        apply l__v1.
        intros [| α] v; asimpl; auto.
      + rewrite <- IHA in Hm.
        revert Hm.
        apply l__v1.
        intros [| α] v; asimpl; auto.
  Qed.

  Lemma ren_sem__te A (δ : var -> sem__t) (ρ : var -> var) M :
    E⟦ A ⟧ (ρ >>> δ) M <-> E⟦ A.[ren ρ] ⟧ δ M.
  Proof.
    cbn. simp interp__t.
    split; intros (m & HM & Hm).
    - rewrite ren_sem__tv in Hm.
      eexists; eauto.
    - rewrite <- ren_sem__tv in Hm.
      eexists; eauto.
  Qed.

  (* Lemma up_sem__Γ Γ δ γ : *)
  (*   G⟦ Γ ⟧ δ γ -> *)
  (*   G⟦ up__Γ Γ ⟧ δ (up γ). *)
  (* Proof. *)
  (*   unfold sem__Γ. *)
  (*   intros HG x A HxA. *)
  (*   unfold up__Γ in HxA. *)
  (*   rewrite list_lookup_fmap_Some in HxA. *)
  (*   destruct HxA as (B & HxB & ->). *)
  (*   specialize HG with (1:=HxB). *)
  (*   simp interp__t in HG. *)
  (*   destruct HG as (v & Hxv & Hv). *)
  (*   eexists; split; eauto. *)
  (*   rewrite <- ren_sem__tv. *)
  (*   revert Hv. *)
  (*   apply l__v1. *)
  (*   intros [| α] V; asimpl; eauto. *)
  (* Qed. *)
  
  Lemma sem__upΓ1 Γ τ δ γ :
    (G⟦ Γ ⟧) δ γ ->
    (G⟦ up__Γ Γ ⟧) (τ .: δ) γ.
  Proof.
    intros HG x A HxA.
    simp interp__t.
    unfold sem__Γ in HG.
    unfold up__Γ in HxA.
    rewrite list_lookup_fmap_Some in HxA.
    destruct HxA as (B & HxB & ->).
    specialize HG with (1:=HxB).
    simp interp__t in HG.
    destruct HG as (v & Hxv & Hv).
    eexists; split; eauto.
    rewrite <- ren_sem__tv.
    revert Hv.
    apply l__v1.
    intros [| α] V; asimpl; eauto.
  Qed.

  Lemma subst_interp__tv v A (δ : var -> sem__t) (σ : var -> typ) :
    V⟦ A.[σ] ⟧ δ v <-> V⟦ A ⟧ (fun α => V⟦ σ α ⟧ δ) v.
  Proof.
    induction A in v, δ, σ |- *; asimpl; simp interp__t; eauto.
    - split; intros (M & -> & HM); eexists;
        split; eauto; intros v Hv; simp interp__t.
      + rewrite <- IHA1 in Hv.
        setoid_rewrite <- IHA2.
        specialize HM with (1:=Hv).
        simp interp__t in HM.
      + setoid_rewrite <- IHA1 in HM.
        specialize HM with (1:=Hv).
        simp interp__t in HM.
        setoid_rewrite <- IHA2 in HM.
        destruct HM as (m & HM & Hm). eauto.
    - split; intros (M & -> & HM);
        eexists; split; eauto; intros τ;
        specialize HM with τ;
        simp interp__t in HM |- *;
        destruct HM as (m & HM & Hm).
      + rewrite IHA in Hm.
        eexists; split; eauto.
        revert Hm. apply l__v1.
        intros [| α] v; repeat (asimpl; simp interp__t); eauto.
        rewrite <- ren_sem__tv, lift_scons. asimpl. auto.
      + setoid_rewrite IHA.
        eexists; split; eauto.
        revert Hm. apply l__v1.
        intros [| α] v; repeat (asimpl; simp interp__t); eauto.
        rewrite <- ren_sem__tv, lift_scons. asimpl. auto.
    - split; intros (m & -> & τ & Hm); eexists; split; eauto; exists τ.
      + rewrite IHA in Hm.
        revert Hm. apply l__v1.
        intros [| α] v; repeat (asimpl; simp interp__t); eauto.
        rewrite <- ren_sem__tv, lift_scons. asimpl. auto.
      + rewrite IHA.
        revert Hm. apply l__v1.
        intros [| α] v; repeat (asimpl; simp interp__t); eauto.
        rewrite <- ren_sem__tv, lift_scons. asimpl. auto.
  Qed.

  Lemma subst_interp__te M A (δ : var -> sem__t) (σ : var -> typ) :
    E⟦ A.[σ] ⟧ δ M <-> E⟦ A ⟧ (fun α => V⟦ σ α ⟧ δ) M.
  Proof.
    cbn. simp interp__t.
    apply exist_proper.
    intro v.
    apply and_iff_compat_l.
    eauto using subst_interp__tv.
  Qed.

  Lemma single_subst_interp__tv v A B (δ : var -> sem__t) :
    V⟦ B.[A/] ⟧ δ v <-> V⟦ B ⟧ (V⟦ A ⟧ δ .: δ) v.
  Proof.
    asimpl.
    rewrite subst_interp__tv.
    apply l__v.
    intros [| α] V; repeat (asimpl; simp interp__t); eauto.
  Qed.

  Lemma single_subst_interp__te M A B (δ : var -> sem__t) :
    E⟦ B.[A/] ⟧ δ M <-> E⟦ B ⟧ (V⟦ A ⟧ δ .: δ) M.
  Proof.
    asimpl.
    rewrite subst_interp__te.
    apply l__e.
    intros [| α] V; repeat (asimpl; simp interp__t); eauto.
  Qed.
End boring.

Section compat.
  Variable Γ : list typ.

  Lemma ident_compat x A :
    Γ !! x = Some A ->
    Γ ⊨ ident x `: A.
  Proof.
    intros HA δ γ HG.
    cbv in HG.
    specialize HG with (1:=HA).
    simp interp__t in HG |- *.
  Qed.

  Lemma abs_compat M A B :
    A :: Γ ⊨ M `: B ->
    Γ ⊨ `λ M `: (A `→ B)%typ.
  Proof.
    intros HM δ γ HG.
    unfold sem_judge in HM.
    Search (G⟦ _ :: _ ⟧).
    simp interp__t.
    eexists; split; cbn; eauto.
    simp interp__t.
    eexists; split; eauto.
    intros v Hv.
    rewrite subst_comp.
    apply HM. asimpl.
    eauto using cons_sem__Γ.
  Qed.

  Lemma app_compat M N A B :
    Γ ⊨ M `: (A `→ B)%typ ->
    Γ ⊨ N `: A ->
    Γ ⊨ app M N `: B.
  Proof.
    intros HM HN δ γ HG.
    unfold sem_judge in HM, HN.
    specialize HM with (1:=HG).
    specialize HN with (1:=HG).
    simp interp__t in HM, HN |- *.
    destruct HM as (m & HM & Hm).
    destruct HN as (n & HN & Hn).
    simp interp__t in Hm.
    destruct Hm as (L & -> & HL).
    specialize HL with (1:=Hn).
    simp interp__t in HL.
    destruct HL as (v & HL & Hv). cbn.
    eexists; split; eauto.
  Qed.

  Lemma tabs_compat M A :
    up__Γ Γ ⊨ M `: A ->
    Γ ⊨ Λ M `: `∀ A.
  Proof.
    intros HM δ γ HG.
    simp interp__t. cbn.
    eexists; split; eauto.
    simp interp__t.
    eexists; split; eauto.
    intros τ. unfold sem_judge in HM.
    eauto using boring.sem__upΓ1.
  Qed.

  Lemma tapp_compat M (A B : typ) :
    Γ ⊨ M `: (`∀ A)%typ ->
    Γ ⊨ M [-] `: A.[B/].
  Proof.
    intros HM δ γ HG.
    unfold sem_judge in HM.
    specialize HM with (1:=HG).
    simp interp__t in HM |- *.
    destruct HM as (m & HM & Hm).
    simp interp__t in Hm.
    destruct Hm as (L & -> & HL).
    specialize HL with (V⟦ B ⟧ δ).
    simp interp__t in HL.
    destruct HL as (v & HLv & Hv).
    cbn. eexists;split; eauto.
    rewrite <- boring.single_subst_interp__tv in Hv. assumption.
  Qed.

  Lemma pack_compat M A B :
    Γ ⊨ M `: A.[B/] ->
    Γ ⊨ pack tt M `: `∃ A.
  Proof.
    unfold sem_judge.
    intros HM δ γ HG.
    specialize HM with (1:=HG).
    cbn. simp interp__t in HM |- *.
    destruct HM as (m & HM & Hv).
    eexists; split; eauto.
    simp interp__t.
    eexists; split; eauto.
    exists (V⟦ B ⟧ δ).
    rewrite <- boring.single_subst_interp__tv.
    assumption.
  Qed.
  
  Lemma unpack_compat M N A B :
    Γ ⊨ M `: (`∃ A) ->
    A :: up__Γ Γ ⊨ N `: B.[ren S] ->
    Γ ⊨ unpack M N `: B.
  Proof.
    unfold sem_judge. cbn.
    intros HM HN δ γ HG.
    specialize HM with (1:=HG).
    simp interp__t in HM |- *.
    destruct HM as (m & HM & Hm).
    simp interp__t in Hm.
    destruct Hm as (v & -> & τ & Hv).
    apply boring.sem__upΓ1 with (τ:=τ) in HG.
    apply cons_sem__Γ with (1:=Hv) in HG.
    specialize HN with (1:=HG).
    rewrite <- boring.ren_sem__te in HN.
    asimpl in HN.
    simp interp__t in HN.
    destruct HN as (n & HN & Hn).
    asimpl in Hn. eexists; split; eauto.
    econstructor; eauto.
    asimpl. assumption.
  Qed.
End compat.

Local Hint Resolve ident_compat : core.
Local Hint Resolve abs_compat : core.
Local Hint Resolve app_compat : core.
Local Hint Resolve tabs_compat : core.
Local Hint Resolve tapp_compat : core.
Local Hint Resolve pack_compat : core.
Local Hint Resolve unpack_compat : core.

Theorem sem_sound Δ Γ M A :
  Δ `; Γ ⊢ M `: A ->
  Γ ⊨ M `: A.
Proof.
  induction 1; eauto.
Qed.

Lemma det_step__b M M1 M2 :
  M ~>b M1 -> M ~>b M2 -> M1 = M2.
Proof.
  inversion 1; inversion 1; subst; auto.
Qed.

Ltac val_tedium :=
  lazymatch goal with
    H: ?M = (_ [[ _ ]])%rtrm |- _
    => assert (is_val M) as [? HM] by eauto;
      rewrite <- HM in H
  end.

Local Hint Extern 3 => val_tedium : core.

Ltac tedium :=
  lazymatch goal with
    H : inj__v _ = (_ [[ ?N ]])%rtrm |- ?N ~>b _ -> _
    => symmetry in H;
      apply val_fill__k in H as (? & <-);
      intros ?%val_not_step__b; contradiction
  end.

Local Hint Extern 0 => tedium : core.

Lemma uniq_decomp__k KM KN M N M' N' :
  (KM [[ M ]])%rtrm = (KN [[ N ]])%rtrm ->
  M ~>b M' -> N ~>b N' ->
  KM = KN /\ M = N.
Proof.
  induction KM in KN, M, N, M', N' |- *;
    destruct KN; cbn; try discriminate;
    try (intros ->; inversion 1; subst; auto; contradiction);
    try (intros <- HM; inversion 1; subst; revert HM; auto; contradiction).
  - injection 1 as HKMN <-%inj_inj__v.
    intros HM HN.
    specialize IHKM with (1:=HKMN) (2:=HM) (3:=HN) as [<- <-].
    split; reflexivity.
  - injection 1 as <- HNv.
    symmetry in HNv.
    apply val_fill__k in HNv as (n & <-).
    intros _ HN%val_not_step__b; contradiction.
  - injection 1 as -> (m & <-)%val_fill__k.
    intros HN%val_not_step__b; contradiction.
  - injection 1 as -> HKMN.
    intros HM HN.
    specialize IHKM with (1:=HKMN) (2:=HM) (3:=HN) as (<- & <-).
    split; reflexivity.
  - injection 1 as HKMN.
    intros HM HN.
    specialize IHKM with (1:=HKMN) (2:=HM) (3:=HN) as (<- & <-).
    split; reflexivity.
  - injection 1 as HKMN.
    intros HM HN.
    specialize IHKM with (1:=HKMN) (2:=HM) (3:=HN) as (<- & <-).
    split; reflexivity.
  - injection 1 as HKMN ->.
    intros HM HN.
    specialize IHKM with (1:=HKMN) (2:=HM) (3:=HN) as (<- & <-).
    split; reflexivity.
Qed.

Lemma det_step M M1 M2 :
  M ~> M1 -> M ~> M2 -> M1 = M2.
Proof.
  intros (N1 & N1' & K1 & -> & -> & HN1)%inv_step.
  intros (N2 & N2' & K2 & HK12 & -> & HN2)%inv_step.
  specialize uniq_decomp__k with (1:=HK12) (2:=HN1) (3:=HN2) as [<- <-].
  specialize det_step__b with (1:=HN1) (2:=HN2) as <-. reflexivity.
Qed.

Local Hint Constructors rtc : core.

Lemma steps_abs M :
  (`λ M)%rtrm ~>* (λv M)%val.
Proof.
  eauto.
Qed.

Lemma steps_app__l M M' (n : val) :
  M ~>* M' ->
  app M (inj__v n) ~>* app M' (inj__v n).
Proof.
  induction 1; eauto using step_app__l.
Qed.

Lemma steps_app__r M N N' :
  N ~>* N' ->
  app M N ~>* app M N'.
Proof.
  induction 1; eauto using step_app__r.
Qed.

Lemma steps_app L M N N' (m : val) :
  L ~>* (λv N)%val ->
  M ~>* m ->
  N.[inj__v m/] ~>* N' ->
  app L M ~>* N'.
Proof.
  intros HL HM HN.
  transitivity N.[inj__v m/]; auto.
  apply rtc_r with (y:=app (`λ N)%rtrm (inj__v m)); auto.
  transitivity (app L (inj__v m)); auto using steps_app__l, steps_app__r.
Qed.

Lemma steps_tabs M :
  (Λ M)%rtrm ~>* (Λv M)%val.
Proof.
  eauto.
Qed.

Lemma steps_tapp__i M M' :
  M ~>* M' ->
  (M [-])%rtrm ~>* (M' [-])%rtrm.
Proof.
  induction 1; eauto using step_tapp.
Qed.

Lemma steps_tapp L M M' :
  L ~>* (Λv M)%val ->
  M ~>* M' ->
  (L [-])%rtrm ~>* M'.
Proof.
  intros HL HM.
  transitivity M; auto.
  apply rtc_r with (y:=((Λ M) [-])%rtrm); auto using steps_tapp__i.
Qed.

Lemma steps_pack M M' :
  M ~>* M' ->
  pack tt M ~>* pack tt M'.
Proof.
  induction 1; eauto using step_pack.
Qed.

Lemma steps_unpack__l M M' N :
  M ~>* M' ->
  unpack M N ~>* unpack M' N.
Proof.
  induction 1; eauto using step_unpack.
Qed.

Lemma steps_unpack M N N' (m : val) :
  M ~>* pack__v m ->
  N.[inj__v m/] ~>* N' ->
  unpack M N ~>* N'.
Proof.
  intros HM HN.
  transitivity N.[inj__v m/]; auto.
  apply rtc_r with (y:=unpack (inj__v (pack__v m)) N); eauto using unpack_pack, steps_unpack__l.
Qed.

Lemma big_steps M v :
  M ⇓ v -> M ~>* v.
Proof.
  induction 1; eauto using steps_app, steps_tapp, steps_pack, steps_unpack.
Qed.

Lemma step__b_big M M' m :
  M ~>b M' -> M' ⇓ m -> M ⇓ m.
Proof.
  inversion 1; subst; eauto.
Qed.

Lemma step_big M M' m :
  M ~> M' -> M' ⇓ m -> M ⇓ m.
Proof.
  intros (N & N' & K & -> & -> & H)%inv_step.
  induction K in N, N', m, H |- *; cbn;
    eauto using step__b_big;
    inversion 1; subst; eauto.
Qed.

Lemma steps_big1 M M' m :
  M ~>* M' -> M' ⇓ m -> M ⇓ m.
Proof.
  induction 1; eauto using step_big.
Qed.

Lemma steps_big M (m : val) :
  M ~>* m -> M ⇓ m.
Proof.
  remember (inj__v m) as V eqn:HV.
  induction 1 in m, HV; subst; eauto using steps_big1.
Qed.

Lemma big_safe M v :
  M ⇓ v -> safe M.
Proof.
  unfold safe, progressive.
  intros HMv M' HMM'.
  left. exists v. eauto using 

Qed.
