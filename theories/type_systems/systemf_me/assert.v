From Autosubst Require Export Autosubst.
(* Require Import AutosubstSsr. *)
From ffpl.lib Require Export maps.
From Equations Require Export Equations Signature.

Variant typ__base : Set :=
  | Unit
  | Bool
  | Int
.

Set Transparent Obligations.
Equations Derive NoConfusion NoConfusionHom Subterm EqDec for typ__base.

Global Instance decide_eq_typ__base (A B : typ__base) : Decision (A = B).
Proof.
  apply typ__base_EqDec.
Qed.

Definition denote_typ__base (B : typ__base) : Set :=
  match B with
  | Unit => unit
  | Bool => bool
  | Int  => Z
  end.

Inductive typ :=
(* Minmal System F types. *)
| Ident (X : var)
| Fun (A B : typ)
| Uni (A : {bind 1 of typ})
(* Existentials. *)
| Exi (A : {bind 1 of typ})
(* Simple types *)
| Base (A : typ__base)
| Prod (A B : typ)
.

Equations Derive NoConfusion NoConfusionHom Subterm EqDec for typ.

#[export] Instance Ids_typ : Ids typ. derive. Defined.
#[export] Instance Rename_typ : Rename typ. derive. Defined.
#[export] Instance Subst_typ : Subst typ. derive. Defined.

#[export] Instance SubstLemmas_typ : SubstLemmas typ. derive. Qed.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.
Bind Scope typ_scope with typ.

Coercion Ident : var >-> typ.
Coercion Base : typ__base >-> typ.
Infix "`->" :=
  Fun
    (at level 100, right associativity)
    : typ_scope.
Notation "'forall,' A" :=
  (Uni A%typ)
    (at level 100, A at level 200)
    : typ_scope.
Notation "'exists,' A" :=
  (Exi A%typ)
    (at level 100, A at level 200)
    : typ_scope.
Infix "`×" :=
  Prod
    (at level 100, right associativity)
    : typ_scope.

Variant atom : typ__base -> Set :=
  | ttt          : atom Unit
  | bewl (b : bool) : atom Bool
  | int (z : Z)  : atom Int
.
Equations Derive NoConfusion NoConfusionHom Subterm EqDec for unit.
Equations Derive NoConfusion NoConfusionHom Subterm EqDec for Z.
Next Obligation.
  apply Z.eq_dec.
Defined.
Equations Derive Signature NoConfusion NoConfusionHom Subterm EqDec for atom.

Global Instance atom_eq_Decision {B} (a1 a2 : atom B) : Decision (a1 = a2).
Proof.
  apply atom_EqDec.
Defined.

Lemma atom_existT_inj__r {B} (a1 a2 : atom B) : existT B a1 = existT B a2 -> a1 = a2.
Proof.
  intros <-%inj_right_pair.
  reflexivity.
Qed.
Local Hint Resolve atom_existT_inj__r : core.

Ltac destr_inj_right_pair :=
  lazymatch goal with
    H: existT ?B _ = existT ?B _
    |- _ => apply inj_right_pair in H; subst
  end.
Local Hint Extern 2 => destr_inj_right_pair : core.

Coercion bewl : bool >-> atom.
Coercion int : Z >-> atom.

Equations denote_atom : forall {B : typ__base}, atom B -> denote_typ__base B :=
| ttt    => tt
| bewl b => b
| int z  => z
.

Equations to_atom : forall B, denote_typ__base B -> atom B :=
| Unit, tt => ttt
| Bool, b  => b
| Int,  z  => z
.

Variant una : typ__base ->  Set :=
  | Not : una Bool
  | Neg : una Int
.

Equations Derive Signature NoConfusion NoConfusionHom Subterm EqDec for una.
Global Instance una_eq_Decision {B} (f g : una B) : Decision (f = g).
Proof.
  apply una_EqDec.
Defined.

Declare Scope una_scope.
Delimit Scope una_scope with una.
Bind Scope una_scope with una.

Notation "`-" := Neg : una_scope.
Notation "`!" := Not : una_scope.

Definition denote_una_typ {B : typ__base} (op : una B) : Set := denote_typ__base B.

Equations denote_una : forall {B} (op : una B), denote_typ__base B -> denote_typ__base B :=
| Not := negb
| Neg := Z.opp
.

Variant bin : typ__base -> typ__base -> Set :=
  | Add : bin Int Int
  | Sub : bin Int Int
  | Mul : bin Int Int
  | Eq  : bin Int Bool
  | Lt  : bin Int Bool
  | And : bin Bool Bool
  | Or  : bin Bool Bool
.

Equations Derive Signature NoConfusion NoConfusionHom Subterm EqDec for bin.
Global Instance bin_eq_Decision {A B} (f g : bin A B) : Decision (f = g).
Proof.
  apply bin_EqDec.
Defined.

Declare Scope bin_scope.
Delimit Scope bin_scope with bin.
Bind Scope bin_scope with bin.

Notation "`+" := Add : bin_scope.
Notation "`-" := Sub : bin_scope.
Notation "`*" := Mul : bin_scope.
Notation "`=" := Eq : bin_scope.
Notation "`<`" := Lt : bin_scope.
Notation "`/\" := And : bin_scope.
Notation "`\/" := Or : bin_scope.

Definition denote_bin_typs {A B} (op : bin A B) : Set * Set := (denote_typ__base A, denote_typ__base B).

Equations denote_bin : forall {A B} (op : bin A B), denote_typ__base A -> denote_typ__base A -> denote_typ__base B :=
| Add => Z.add
| Sub => Z.sub
| Mul => Z.mul
| Eq  => Z.eqb
| Lt  => Z.ltb
| And => andb
| Or  => orb
.

(* Variant una_atom : una -> atom -> atom -> Prop := *)
(*   | una_atom_not (b : bool) : *)
(*     una_atom `!%una b (negb b) *)
(*   | una_atom_neg (z : Z) : *)
(*     una_atom `-%una z (Z.opp z). *)

(* Variant bin_atom : bin -> atom -> atom -> atom -> Prop :=. *)

Inductive trm :=
(* Minimal System F runtime terms. *)
| ident (x : var)
| abs (M : {bind 1 of trm})
| app (M N : trm)
| tabs (M : trm)
| tapp (M : trm)
(* Existential terms *)
| pack (M : trm)
| unpack (M : trm) (N : {bind 1 of trm})
(* Simple terms *)
| base {B} (a : atom B)
| uop {B} (op : una B) (M : trm)
| bop {A B} (op : bin A B) (M N : trm)
| duo (M N : trm)
| prj (b : bool) (P : trm)
| cond (L M N : trm)
| letin (M : trm) (N : {bind 1 of trm})
(* Assert. *)
| ass (M : trm)
.

#[export] Instance Ids_trm : Ids trm. derive. Defined.
#[export] Instance Rename_trm : Rename trm. derive. Defined.
#[export] Instance Subst_trm : Subst trm. derive. Defined.
#[export] Instance SubstLemmas_trm : SubstLemmas trm. derive. Qed.

Ltac dec_eq_ind :=
  lazymatch goal with
  | |- dec_eq ?x ?x => left; reflexivity
  | H: _ <> _ |- dec_eq _ _ => right; intros [=]; subst; try contradiction
  | x : ?A, y : ?A, IH : forall y, dec_eq ?x y |- dec_eq _ _ =>
      specialize IH with y as [<- | ?]; clear IH
  end.

Equations Derive NoConfusion NoConfusionHom Subterm EqDec for trm.
Next Obligation.
  induction x in y |- *; destruct y; try (right; discriminate);
    try (repeat dec_eq_ind; done).
  - destruct (decide (x = x0)) as [<- | H]; dec_eq_ind.
  - destruct (decide (B = B0)) as [<- | H]; try dec_eq_ind.
    
    depelim a; depelim a0; try dec_eq_ind.
    + destruct (decide (b = b0)) as [<- | H]; dec_eq_ind.
    + destruct (decide (z = z0)) as [<- | H]; dec_eq_ind.
  - destruct (decide (B = B0)) as [<- | H]; try dec_eq_ind;
    depelim op; depelim op0; dec_eq_ind.
  - destruct (decide (A = A0)) as [<- | HA]; repeat dec_eq_ind.
    destruct (decide (B = B0)) as [<- | H]; try dec_eq_ind;
      depelim op; depelim op0; cbn; try dec_eq_ind; try (right; intros [=]).
  - repeat dec_eq_ind.
    destruct (decide (b = b0)) as [<- | H]; dec_eq_ind.
Defined.
Global Instance trm_eq_Decision (M N : trm) : Decision (M = N).
Proof.
  apply trm_EqDec.
Defined.

Declare Scope trm_scope.
Delimit Scope trm_scope with trm.
Bind Scope trm_scope with trm.

Notation "'fun,' M" := (abs M%trm) (at level 100, right associativity) : trm_scope.
Notation "'Λ' M" := (tabs M%trm) (at level 100, right associativity) : trm_scope.
Notation "M '[-]'" := (tapp M%trm) (at level 96, left associativity) : trm_scope.
Notation "'unpack,' M 'in' N" := (unpack M%trm N%trm) (at level 100, right associativity) : trm_scope.
Notation "'let,' M 'in' N" := (letin M%trm N%trm) (at level 100, right associativity) : trm_scope.
Notation "'if,' L 'then,' M 'else,' N" := (cond L%trm M%trm N%trm) (at level 100, right associativity) : trm_scope.
Notation "'`(' M , N ')`'" := (duo M%trm N%trm) (at level 100, right associativity) : trm_scope.
Notation "'`(' x , .. , y  , z ')`'" := (duo x%trm .. (duo y%trm z%trm) ..) : trm_scope.
Notation "'`<' u '>`' M" := (uop u%una M%trm) (at level 100) : trm_scope.
Notation "M '<`' b '`>' N" := (bop b%bin M%trm N%trm) (at level 96, left associativity) : trm_scope.

Coercion ident : var >->trm.
Coercion base : atom >-> trm.
Coercion app : trm >-> Funclass.

Inductive val :=
| abs__v (M : trm)
| tabs__v (M : trm)
| pack__v (v : val)
| base__v {T} (a : atom T)
| duo__v (v1 v2 : val)
.

Equations Derive NoConfusion NoConfusionHom Subterm EqDec for val.
Next Obligation.
  induction x in y |- *; destruct y; try (right; discriminate); try (repeat dec_eq_ind; done).
  - destruct (decide (M = M0)) as [<- | HM]; dec_eq_ind.
  - destruct (decide (M = M0)) as [<- | HM]; dec_eq_ind.
  - destruct (decide (T = T0)) as [<- | HT]; try dec_eq_ind.
    destruct (decide (a = a0)) as [<- | Ha]; try dec_eq_ind.
    destr_inj_right_pair. contradiction.
Defined.
Global Instance val_eq_Decision (v1 v2 : val) : Decision (v1 = v2).
Proof.
  apply val_EqDec.
Qed.

Declare Scope val_scope.
Delimit Scope val_scope with val.
Bind Scope val_scope with val.

Notation "fun, M" := (abs__v M%trm) (at level 100, right associativity) : val_scope.
Notation "'Λ' M" := (tabs__v M%trm) (at level 100, right associativity) : val_scope.
Notation "'(`' M , N '`)'" := (duo__v M%val N%val) (at level 100, right associativity) : val_scope.
Notation "'(`' x , .. , y  , z '`)'" := (duo__v x%val .. (duo__v y%val z%val) ..) : val_scope.

Coercion base__v : atom >-> val.

Fixpoint inj__v (v : val) : trm :=
  match v with
  | base__v a    => a
  | (fun, M)%val => (fun, M)%trm
  | (Λ M)%val  => (Λ M)%trm
  | pack__v v    => pack $ inj__v v
  | (`v1, v2`)%val => `(inj__v v1, inj__v v2)`
  end.

Definition is_val (M : trm) : Prop :=
  exists v, M = inj__v v.

Lemma abs_is_val M :
  is_val (fun, M)%trm.
Proof.
  exists (fun, M)%val. reflexivity.
Qed.
Local Hint Resolve abs_is_val : core.

Lemma tabs_is_val M :
  is_val (Λ M)%trm.
Proof.
  exists (Λ M)%val. reflexivity.
Qed.
Local Hint Resolve tabs_is_val : core.

Lemma pack_is_val M :
  is_val M ->
  is_val (pack M).
Proof.
  intros [m ->].
  exists (pack__v m). reflexivity.
Qed.
Local Hint Resolve pack_is_val : core.

Lemma base_is_val {T} (a : atom T) :
  is_val a.
Proof.
  exists a. reflexivity.
Qed.
Local Hint Resolve base_is_val : core.

Lemma duo_is_val (M N : trm) :
  is_val M -> is_val N ->
  is_val `(M, N)`%trm.
Proof.
  intros [m ->] [n ->].
  exists ((` m, n `))%val.
  reflexivity.
Qed.
Local Hint Resolve duo_is_val : core.
  
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

Lemma tapp_is_not_val M :
  ~ is_val (M [-])%trm.
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve tapp_is_not_val : core.

Lemma unpack_is_not_val M N :
  ~ is_val (unpack M N).
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve unpack_is_not_val : core.

Lemma cond_is_not_val L M N :
  ~ is_val (if, L then, M else, N).
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve cond_is_not_val : core.

Lemma letin_is_not_val M N :
  ~ is_val (let, M in N)%trm.
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve letin_is_not_val : core.

Lemma uop_is_not_val {B} (op : una B) M :
  ~ is_val ( `< op >` M)%trm.
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve uop_is_not_val : core.

Lemma bop_is_not_val {A B} (op : bin A B) M N :
  ~ is_val (M <` op `> N)%trm.
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve bop_is_not_val : core.

Lemma prj_is_not_val b P :
  ~ is_val (prj b P).
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve prj_is_not_val : core.

Lemma ass_is_not_val M :
  ~ is_val (ass M).
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve ass_is_not_val : core.

Lemma inj_inj__v v1 v2 :
  inj__v v1 = inj__v v2 -> v1 = v2.
Proof.
  induction v1 as [M1 | M1 | v1 IHv1 | a1 | m1 IHm1 n1 IHn1] in v2 |- *;
    destruct v2 as [M2 | M2 | v2 | a2 | m2 n2]; cbn; try discriminate;
    try injection 1 as <-; try reflexivity.
  - intros [= <-%IHv1]. reflexivity.
  - apply inj_right_pair in H as <-. reflexivity.
  - intros [= <-%IHm1 <-%IHn1]. reflexivity.
Qed.

Lemma abs_inj__v M v :
  (fun, M)%trm = inj__v v -> v = (fun, M)%val.
Proof.
  destruct v; discriminate || injection 1 as <-; reflexivity.
Qed.

Lemma tabs_inj__v M v :
  (Λ M)%trm = inj__v v -> v = (Λ M)%val.
Proof.
  destruct v; discriminate || injection 1 as <-; reflexivity.
Qed.

Lemma pack_inj__v M v :
  pack M = inj__v v -> exists m, M = inj__v m /\ v = pack__v m.
Proof.
  destruct v; try discriminate; cbn.
  intros [= ->]. eauto.
Qed.

Lemma base_inj__v {T} (a : atom T) v :
  base a = inj__v v -> v = a.
Proof.
  destruct v; cbn; try discriminate.
  intros [= <-].
  apply inj_right_pair in H0 as <-. reflexivity.
Qed.

Lemma duo_inj__v M N v :
  `(M, N)`%trm = inj__v v -> exists m n, M = inj__v m /\ N = inj__v n /\ v = ((`m, n`))%val.
Proof.
  destruct v; discriminate || intros [= -> ->]. eauto.
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

Lemma tapp_not_inj__v M v :
  (M [-])%trm <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma unpack_not_inj__v M N v :
  unpack M N <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma uop_not_inj__v {B} (op : una B) M v :
  ( `< op >` M)%trm <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma bop_not_inj__v {A B} (op : bin A B) M N v :
  (M <` op `> N)%trm <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma prj_not_inj__v b P v :
  (prj b P)%trm <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma cond_not_inj__v L M N v :
  (if, L then, M else, N)%trm <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma letin_not_inj__v M N v :
  (let, M in N)%trm <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma ass_not_inj__v M v :
  ass M <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Ltac elim_inj__v :=
  lazymatch goal with
  | H: inj__v _ = inj__v _ |- _ => specialize inj_inj__v with (1:=H) as ->
  | H: (fun, _)%trm = inj__v _ |- _ => specialize abs_inj__v with (1:=H) as ->
  | H: inj__v _ = (fun, _)%trm |- _ => symmetry in H; specialize abs_inj__v with (1:=H) as ->
  | H: (Λ _)%trm = inj__v _ |- _ => specialize tabs_inj__v with (1:=H) as ->
  | H: inj__v _ = (Λ _)%trm |- _ => symmetry in H; specialize tabs_inj__v with (1:=H) as ->
  | H: pack _ = inj__v _ |- _ => specialize pack_inj__v with (1:=H) as (? & -> & ->)
  | H: inj__v _ = pack _ |- _ => symmetry in H; specialize pack_inj__v with (1:=H) as (? & -> & ->)
  | H: @base ?T _ = inj__v _ |- _ => specialize (base_inj__v (T:=T)) with (1:=H)
  | H: inj__v _ = @base ?T _ |- _ => symmetry in H; specialize (base_inj__v (T:=T)) with (1:=H)
  | H: `(_, _)`%trm = inj__v _ |- _ => specialize duo_inj__v with (1:=H) as (? & ? & -> & -> & ->)
  | H: inj__v _ = `(_, _)`%trm |- _ => symmetry in H; specialize duo_inj__v with (1:=H) as (? & ? & -> & -> & ->)
  | H: ident _ = inj__v _ |- _ => apply ident_not_inj__v in H; contradiction
  | H: inj__v _ = ident _  |- _ => symmetry; apply ident_not_inj__v in H; contradiction
  | H: app _ _ = inj__v _ |- _ => apply app_not_inj__v in H; contradiction
  | H: inj__v _ = app _ _ |- _ => symmetry; apply app_not_inj__v in H; contradiction
  | H: (_ [-])%trm = inj__v _ |- _ => apply tapp_not_inj__v in H; contradiction
  | H: inj__v _ = (_ [-])%trm |- _ => symmetry; apply tapp_not_inj__v in H; contradiction
  | H: (unpack, _ in _)%trm = inj__v _ |- _ => apply unpack_not_inj__v in H; contradiction
  | H: inj__v _ = (unpack, _ in _)%trm |- _ => symmetry in H; apply unpack_not_inj__v in H; contradiction
  | H: uop _ _ = inj__v _ |- _ => apply uop_not_inj__v in H; contradiction
  | H: inj__v _ = uop _ _ |- _ => symmetry in H; apply uop_not_inj__v in H; contradiction
  | H: bop _ _ _ = inj__v _ |- _ => apply bop_not_inj__v in H; contradiction
  | H: inj__v _ = bop _ _ _ |- _ => symmetry in H; apply bop_not_inj__v in H; contradiction
  | H: prj _ _ = inj__v _ |- _ => apply prj_not_inj__v in H; contradiction
  | H: inj__v _ = prj _ _ |- _ => symmetry in H; apply prj_not_inj__v in H; contradiction
  | H: cond _ _ _ = inj__v _ |- _ => apply cond_not_inj__v in H; contradiction
  | H: inj__v _ = cond _ _ _  |- _ => symmetry in H; apply cond_not_inj__v in H; contradiction
  | H: (let, _ in _)%trm = inj__v _ |- _ => apply letin_not_inj__v in H; contradiction
  | H: inj__v _ = (let, _ in _)%trm |- _ => symmetry in H; apply letin_not_inj__v in H; contradiction
  | H: ass _ = inj__v _ |- _ => apply ass_not_inj__v in H; contradiction
  | H: inj__v _ = ass _ |- _ => symmetry; apply ass_not_inj__v in H; contradiction
  end.

Local Hint Extern 0 => elim_inj__v : core.

Coercion inj__v : val >-> trm.

Inductive ktx :=
| hole
| app__l (K : ktx) (v : val)
| app__r (M : trm) (K : ktx)
| tapp__k (K : ktx)
| pack__k (K : ktx)
| unpack__k (K : ktx) (N : trm)
| uop__k {B} (op : una B) (K : ktx)
| bop__l {A B} (op : bin A B) (K : ktx) (v : val)
| bop__r {A B} (op : bin A B) (M : trm) (K : ktx)
| duo__l (K : ktx) (v : val)
| duo__r (M : trm) (K : ktx)
| prj__k (b : bool) (K : ktx)
| cond__k (K : ktx) (M N : trm)
| letin__k (K : ktx) (N : trm)
| ass__k (K : ktx)
.

Reserved Notation "K '[[' M ']]'"
  (at level 98, left associativity).

Fixpoint fill__k (K : ktx) (M : trm) : trm :=
  match K with
  | hole     => M
  | app__l K v => (K [[ M ]]) (inj__v v)
  | app__r N K => N (K [[ M ]])
  | tapp__k K  => K [[ M ]] [-]
  | pack__k K  => pack (K [[ M ]])
  | unpack__k K N => unpack, K [[ M ]] in N
  | uop__k op K   => `< op >` K [[ M ]]
  | bop__l op K v => K [[ M ]] <` op `> inj__v v
  | bop__r op N K => N <` op `> (K [[ M ]])
  | duo__l K v    => `(K [[ M ]], inj__v v)`
  | duo__r N K    => `(N, K [[ M ]])`
  | prj__k b K    => prj b (K [[M]])
  | cond__k K L N => cond (K [[M]]) L N
  | letin__k K N  => let, K [[ M ]] in N
  | ass__k K      => ass (K [[ M ]])
  end
where "K '[[' M ']]'" := (fill__k K M%trm) : trm_scope.

Reserved Infix "`∘" (at level 98, left associativity).

Fixpoint comp__k (K K' : ktx) : ktx :=
  match K with
  | hole => K'
  | app__l K v => app__l (K `∘ K') v
  | app__r M K => app__r M (K `∘ K')
  | tapp__k K => tapp__k (K `∘ K')
  | pack__k K  => pack__k (K `∘ K')
  | unpack__k K N => unpack__k (K `∘ K') N
  | uop__k op K  => uop__k op (K `∘ K')
  | bop__l op K v => bop__l op (K `∘ K') v
  | bop__r op M K => bop__r op M (K `∘ K')
  | duo__l K v => duo__l (K `∘ K') v
  | duo__r M K => duo__r M (K `∘ K')
  | prj__k b K  => prj__k b (K `∘ K')
  | cond__k K M N => cond__k (K `∘ K') M N
  | letin__k K N  => letin__k (K `∘ K') N
  | ass__k K => ass__k (K `∘ K')
  end
where "K1 '`∘' K2" := (comp__k K1 K2).

Lemma fill_comp__k K K' M :
  ((K `∘ K') [[ M ]])%trm = (K [[ K' [[ M ]] ]])%trm.
Proof.
  induction K; cbn; f_equal; auto.
Qed.

Reserved Infix "~>b" (at level 80, no associativity).

Variant step__b : trm -> trm -> Prop :=
  | step_app_abs__b M (n : val) :
    (fun, M) (inj__v n) ~>b M.[ inj__v n /]
  | step_tapp_tabs__b M :
    (Λ M) [-] ~>b M
  | step_unpack_pack__b (v : val) N :
    (unpack, pack (inj__v v) in N)%trm ~>b N.[ inj__v v /]
  | step_una_base__b {B} (op : una B) (a : atom B) :
    ( `< op >` a)%trm ~>b to_atom B (denote_una op (denote_atom a))
  | step_bin_base__b {A B} (op : bin A B) (a1 a2 : atom A) :
    (a1 <` op `> a2)%trm ~>b to_atom B (denote_bin op (denote_atom a1) (denote_atom a2))
  | step_prj_duo__b b (m n : val) :
    prj b `(m, n)`%trm ~>b if b then m else n
  | step_cond__b (b : bool) M N :
    (if, b then, M else, N) ~>b if b then M else N
  | step_letin__b (v : val) N :
    (let, inj__v v in N)%trm ~>b N.[ inj__v v /]
  | step_ass__b :
    ass true ~>b ttt
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

Lemma det_step__b L M N :
  L ~>b M -> L ~>b N -> M = N.
Proof.
  inversion 1; inversion 1; subst; repeat elim_inj__v;
    repeat destr_inj_right_pair;
    try reflexivity.
Qed.

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
  - intros [= H%IHK]. assumption.
  - intros [= H%IHK <-%inj_inj__v]. assumption.
  - intros [= -> H%IHK]. assumption.
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

Ltac val_tedium :=
  lazymatch goal with
    H: ?M = (_ [[ _ ]])%trm |- _
    => assert (is_val M) as [? HM] by eauto;
      rewrite HM in H
  end.

Local Hint Extern 3 => val_tedium : core.

Ltac tedium :=
  lazymatch goal with
    H : inj__v _ = (_ [[ ?N ]])%trm |- ?N ~>b _ -> _
    => symmetry in H;
      apply val_fill__k in H as (? & ->);
      intros ?%val_not_step__b; contradiction
  end.

Local Hint Extern 0 => tedium : core.

Lemma uniq_decomp__k KM KN M N M' N' :
  (KM [[ M ]])%trm = (KN [[ N ]])%trm ->
  M ~>b M' -> N ~>b N' ->
  KM = KN /\ M = N.
Proof.
  induction KM in KN, M, N, M', N' |- *;
    destruct KN; cbn; try discriminate;
    try (intros ->; inversion 1; subst; auto; contradiction);
    try (intros <- HM; inversion 1; subst; revert HM; auto; contradiction);
    try (intros [= HKMN] HM [<- <-]%(IHKM _ _ _ _ _ HKMN HM); subst; auto).
  - intros [= <- [n ->]%eq_sym%val_fill__k] _ H%val_not_step__b. contradiction.
  - intros [= -> [m ->]%val_fill__k] H%val_not_step__b. contradiction.
  - intros [= <- HKMN] HM [<- <-]%(IHKM _ _ _ _ _ HKMN HM). auto.
  - intros [= <- <-%inj_right_pair HKMN] HM [<- <-]%(IHKM _ _ _ _ _ HKMN HM). auto.
  - intros [= <- <- <-%inj_right_pair%inj_right_pair HKMN <-%inj_inj__v] HM [<- <-]%(IHKM _ _ _ _ _ HKMN HM). auto.
  - intros [= <- <- <-%inj_right_pair%inj_right_pair <- [n ->]%eq_sym%val_fill__k] _ H%val_not_step__b. contradiction.
  - intros [= <- <- <-%inj_right_pair%inj_right_pair -> [m ->]%val_fill__k] HM%val_not_step__b. contradiction.
  - intros [= <- <- <-%inj_right_pair%inj_right_pair <- HKMN] HM [<- <-]%(IHKM _ _ _ _ _ HKMN HM). auto.
  - intros [= <- [n ->]%eq_sym%val_fill__k] _ HN%val_not_step__b. contradiction.
  - intros [= -> [m ->]%val_fill__k] HM%val_not_step__b. contradiction.
  - intros [= <- HKMN] HM [<- <-]%(IHKM _ _ _ _ _ HKMN HM). auto.
  - intros [= <- HKMN] HM [<- <-]%(IHKM _ _ _ _ _ HKMN HM). auto.
Qed.

Lemma det_step L M N :
  L ~> M -> L ~> N -> M = N.
Proof.
  intros (L' & M' & KM & -> & -> & HLM)%inv_step (L'' & N' & KN & H & -> & HLN)%inv_step.
  specialize uniq_decomp__k with (1:=H) (2:=HLM) (3:=HLN) as [<- <-].
  specialize det_step__b with (1:=HLM) (2:=HLN) as <-. reflexivity.
Qed.

Lemma step_app_abs M (n : val) :
  app (fun, M) (inj__v n) ~> M.[ inj__v n /].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_app_abs : core.

Lemma step_app_abs_is_val M N :
  is_val N ->
  (fun, M) N ~> M.[ N /].
Proof.
  intros [n ->]. eauto.
Qed.

Local Hint Resolve step_app_abs_is_val : core.

Lemma step_tapp_tabs M :
  (Λ M) [-] ~> M.
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_tapp_tabs : core.

Lemma step_unpack_pack (v : val) N :
  (unpack, pack (inj__v v) in N)%trm ~> N.[ inj__v v /].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_unpack_pack : core.

Lemma step_unpack_pack_is_val M N :
  is_val M ->
  unpack (pack M) N ~> N.[ M /].
Proof.
  intros [v ->]. eauto.
Qed.

Local Hint Resolve step_unpack_pack_is_val : core.

Lemma step_una_base {B} (op : una B) (a : atom B) :
  ( `< op >` a)%trm ~> to_atom B (denote_una op (denote_atom a)).
Proof.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_una_base : core.

Lemma step_bin_base {A B} (op : bin A B) (a1 a2 : atom A) :
  (a1 <` op `> a2)%trm ~> to_atom B (denote_bin op (denote_atom a1) (denote_atom a2)).
Proof.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_bin_base : core.

Lemma step_prj_duo b (m n : val) :
  prj b `(m, n)`%trm ~> if b then m else n.
Proof.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_prj_duo : core.

Lemma step_cond (b : bool) M N :
  (if, b then, M else, N) ~> if b then M else N.
Proof.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_cond : core.

Lemma step_letin (v : val) N :
  (let, inj__v v in N)%trm ~> N.[inj__v v/].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_letin : core.

Lemma step_letin_is_val M N :
  is_val M ->
  (let, M in N)%trm ~> N.[M/].
Proof.
  intros [v ->]; eauto.
Qed.

Local Hint Resolve step_letin_is_val : core.

Lemma step_ass :
  ass true ~> ttt.
Proof.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_ass : core.

Lemma step_app__r (M N N' : trm) :
  N ~> N' ->
  M N ~> M N'.
Proof.
  replace (app M N) with (app__r M hole [[ N ]])%trm by reflexivity.
  replace (app M N') with (app__r M hole [[ N' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_app__r : core.

Lemma step_app__l M M' (v : val) :
  M ~> M' ->
  M (inj__v v) ~> M' (inj__v v).
Proof.
  replace (app M (inj__v v)) with (app__l hole v [[ M ]])%trm by reflexivity.
  replace (app M' (inj__v v)) with (app__l hole v [[ M' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_app__l : core.

Lemma step_app_is_val__l M M' N :
  is_val N ->
  M ~> M' ->
  M N ~> M' N.
Proof.
  intros [n ->]. eauto.
Qed.

Local Hint Resolve step_app_is_val__l : core.

Lemma step_tapp M M' :
  M ~> M' ->
  (M [-])%trm ~> (M' [-])%trm.
Proof.
  replace (M [-])%trm with (tapp__k hole [[ M ]])%trm by reflexivity.
  replace (M' [-])%trm with (tapp__k hole [[ M' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_tapp : core.

Lemma step_pack M M' :
  M ~> M' ->
  pack M ~> pack M'.
Proof.
  replace (pack M) with (pack__k hole [[ M ]])%trm by reflexivity.
  replace (pack M') with (pack__k hole [[ M' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_pack : core.

Lemma step_unpack M M' N :
  M ~> M' ->
  unpack M N ~> unpack M' N.
Proof.
  replace (unpack M N) with (unpack__k hole N [[ M ]])%trm by reflexivity.
  replace (unpack M' N) with (unpack__k hole N [[ M' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_unpack : core.

Lemma step_uop__i {B} (op : una B) M M' :
  M ~> M' ->
  ( `< op >` M)%trm ~> ( `< op >` M')%trm.
Proof.
  replace ( `< op >` M)%trm with (uop__k op hole [[ M ]])%trm by reflexivity.
  replace ( `< op >` M')%trm with (uop__k op hole [[ M' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_uop__i : core.

Lemma step_bop__r {A B} (op : bin A B) M N N' :
  N ~> N' ->
  (M <` op `> N)%trm ~> (M <` op `> N')%trm.
Proof.
  replace (M <` op `> N)%trm with (bop__r op M hole [[ N ]])%trm by reflexivity.
  replace (M <` op `> N')%trm with (bop__r op M hole [[ N' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_bop__r : core.

Lemma step_bop__l {A B} (op : bin A B) M M' (v : val) :
  M ~> M' ->
  (M <` op `> v)%trm ~> (M' <` op `> v)%trm.
Proof.
  replace (M <` op `> v)%trm with (bop__l op hole v [[ M ]])%trm by reflexivity.
  replace (M' <` op `> v)%trm with (bop__l op hole v [[ M' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_bop__l : core.

Lemma step_bop_is_val__l {A B} (op : bin A B) M M' N :
  is_val N ->
  M ~> M' ->
  (M <` op `> N)%trm ~> (M' <` op `> N)%trm.
Proof.
  intros [n ->]. eauto.
Qed.

Local Hint Resolve step_bop_is_val__l : core.

Lemma step_duo__r M N' N :
  N ~> N' ->
  `(M, N)` ~> `(M, N')`.
Proof.
  replace `(M, N)`%trm with (duo__r M hole [[ N ]])%trm by reflexivity.
  replace `(M, N')`%trm with (duo__r M hole [[ N' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_duo__r : core.

Lemma step_duo__l M M' (v : val) :
  M ~> M' ->
  `(M, inj__v v)` ~> `(M', inj__v v)`.
Proof.
  replace `(M, inj__v v)`%trm with (duo__l hole v [[ M ]])%trm by reflexivity.
  replace `(M', inj__v v)`%trm with (duo__l hole v [[ M' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_duo__l : core.

Lemma step_duo_is_val__l M M' N :
  is_val N ->
  M ~> M' ->
  `(M, N)` ~> `(M', N)`.
Proof.
  intros [n ->]. eauto.
Qed.

Local Hint Resolve step_duo_is_val__l : core.

Lemma step_prj__i b P P' :
  P ~> P' ->
  prj b P ~> prj b P'.
Proof.
  replace (prj b P) with (prj__k b hole [[ P ]])%trm by reflexivity.
  replace (prj b P') with (prj__k b hole [[ P' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_prj__i : core.

Lemma step_cond__l L L' M N :
  L ~> L' ->
  (if, L then, M else, N) ~> if, L' then, M else, N.
Proof.
  replace (if, L then, M else, N)%trm with (cond__k hole M N [[ L ]])%trm by reflexivity.
  replace (if, L' then, M else, N)%trm with (cond__k hole M N [[ L' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_cond__l : core.

Lemma step_letin__l M M' N :
  M ~> M' ->
  letin M N ~> letin M' N.
Proof.
  replace (letin M N) with (letin__k hole N [[ M ]])%trm by reflexivity.
  replace (letin M' N) with (letin__k hole N [[ M' ]])%trm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_letin__l : core.

Lemma step_ass__i M M' :
  M ~> M' ->
  ass M ~> ass M'.
Proof.
  replace (ass M) with (ass__k hole [[ M ]])%trm by reflexivity.
  replace (ass M') with (ass__k hole [[ M' ]])%trm by reflexivity.
  eauto.
Qed.

Reserved Infix "⊢wf" (at level 80).

Inductive wf_typ (Δ : nat) : typ -> Prop :=
| wf_Ident (X : var) :
  X < Δ ->
  Δ ⊢wf X
| wf_Fun A B :
  Δ ⊢wf A ->
  Δ ⊢wf B ->
  Δ ⊢wf (A `-> B)
| wf_Uni A :
  S Δ ⊢wf A ->
  Δ ⊢wf (forall, A)
| wf_Exi A :
  S Δ ⊢wf A ->
  Δ ⊢wf (exists, A)
| wf_Base (B : typ__base) :
  Δ ⊢wf B
| wf_Prod A B :
  Δ ⊢wf A ->
  Δ ⊢wf B ->
  Δ ⊢wf (A `× B)
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
  Δ `; Γ ⊢ (fun, M) `: (A `-> B)
| judge_app M N A B :
  Δ `; Γ ⊢ M `: (A `-> B)%typ ->
  Δ `; Γ ⊢ N `: A ->
  Δ `; Γ ⊢ M N `: B
| judge_tabs M A :
  S Δ `; up__Γ Γ ⊢ M `: A ->
  Δ `; Γ ⊢ Λ M `: (forall, A)
| judge_tapp M (A B : typ) :
  Δ ⊢wf B ->
  Δ `; Γ ⊢ M `: (forall, A)%typ ->
  Δ `; Γ ⊢ M [-] `: A.[ B /]
| judge_pack M A B :
  Δ ⊢wf B ->
  Δ `; Γ ⊢ M `: A.[ B /] ->
  Δ `; Γ ⊢ pack M `: (exists, A)
| judge_unpack M N A B :
  Δ ⊢wf B ->
  Δ `; Γ ⊢ M `: (exists, A) ->
  S Δ `; A :: up__Γ Γ ⊢ N `: subst (ren S) B ->
  Δ `; Γ ⊢ unpack M N `: B
| judge_base (B : typ__base) (a : atom B) :
  Δ `; Γ ⊢ a `: B
| judge_uop (B : typ__base) (op : una B) M :
  Δ `; Γ ⊢ M `: B ->
  Δ `; Γ ⊢ `< op >` M `: B
| judge_bop (A B : typ__base) (op : bin A B) M N :
  Δ `; Γ ⊢ M `: A ->
  Δ `; Γ ⊢ N `: A ->
  Δ `; Γ ⊢ M <` op `> N `: B
| judge_cond A L M N :
  Δ `; Γ ⊢ L `: Bool ->
  Δ `; Γ ⊢ M `: A ->
  Δ `; Γ ⊢ N `: A ->
  Δ `; Γ ⊢ if, L then, M else, N `: A
| judge_duo M N A B :
  Δ `; Γ ⊢ M `: A ->
  Δ `; Γ ⊢ N `: B ->
  Δ `; Γ ⊢ `(M, N)` `: (A `× B)
| judge_prj b P A B :
  Δ `; Γ ⊢ P `: (A `× B) ->
  Δ `; Γ ⊢ prj b P `: if b then A else B
| judge_letin M N A B :
  Δ `; Γ ⊢ M `: A ->
  Δ `; A :: Γ ⊢ N `: B ->
  Δ `; Γ ⊢ (let, M in N)%trm `: B
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

  Lemma inv_judge_abs M C :
    Δ `; Γ ⊢ fun, M `: C ->
    exists A B, C = (A `-> B)%typ /\ Δ ⊢wf A /\ Δ `; A :: Γ ⊢ M `: B.
  Proof.
    inversion 1; subst.
    eauto.
  Qed.

  Lemma inv_judge_app (M N : trm) B :
    Δ `; Γ ⊢ M N `: B ->
    exists A, Δ `; Γ ⊢ M `: (A `-> B) /\ Δ `; Γ ⊢ N `: A.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_tabs M C :
    Δ `; Γ ⊢ Λ M `: C ->
    exists A, C = (forall, A)%typ /\ S Δ `; up__Γ Γ ⊢ M `: A.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_tapp M C :
    Δ `; Γ ⊢ M [-] `: C ->
    exists A B, C = A.[B/] /\ Δ ⊢wf B /\ Δ `; Γ ⊢ M `: (forall, A).
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_pack M C :
    Δ `; Γ ⊢ pack M `: C ->
    exists A B, C = (exists, A)%typ /\ Δ ⊢wf B /\ Δ `; Γ ⊢ M `: A.[B/].
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_unpack M N B :
    Δ `; Γ ⊢ unpack M N `: B ->
    exists A, Δ ⊢wf B /\ Δ `; Γ ⊢ M `: (exists, A) /\ S Δ `; A :: up__Γ Γ ⊢ N `: subst (ren S) B.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_letin M N B :
    Δ `; Γ ⊢ letin M N `: B ->
    exists A, Δ `; Γ ⊢ M `: A /\ Δ `; A :: Γ ⊢ N `: B.
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma inv_judge_base B (a : atom B) C :
    Δ `; Γ ⊢ a `: C -> C = B.
  Proof.
    inversion 1; subst. reflexivity.
  Qed.

  Lemma inv_judge_uop B (op : una B) M C :
    Δ `; Γ ⊢ `< op >` M `: C -> C = B /\ Δ `; Γ ⊢ M `: B.
  Proof.
    inversion 1; subst; auto.
  Qed.

  Lemma inv_judge_bop A B (op : bin A B) M N C :
    Δ `; Γ ⊢ M <` op `> N `: C -> C = B /\ Δ `; Γ ⊢ M `: A /\ Δ `; Γ ⊢ N `: A.
  Proof.
    inversion 1; subst; auto.
  Qed.

  Lemma inv_judge_cond L M N C :
    Δ `; Γ ⊢ if, L then, M else, N `: C -> Δ `; Γ ⊢ L `: Bool /\  Δ `; Γ ⊢ M `: C /\ Δ `; Γ ⊢ N `: C.
  Proof.
    inversion 1; subst; auto.
  Qed.

  Lemma inv_judge_duo M N C :
    Δ `; Γ ⊢ `(M, N)` `: C -> exists A B, C = (A `× B)%typ /\ Δ `; Γ ⊢ M `: A /\ Δ `; Γ ⊢ N `: B.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_prj b P C :
    Δ `; Γ ⊢ prj b P `: C -> exists A B, C = (if b then A else B) /\ Δ `; Γ ⊢ P `: (A `× B)%typ.
  Proof.
    inversion 1; subst; eauto.
  Qed.
End inv.

Section canon.
  Variable Δ : nat.
  Variable Γ : list typ.
  
  Lemma canon_fun (v : val) A B :
    Δ `; Γ ⊢ v `: (A `-> B)%typ ->
    exists N, v = (fun, N)%val.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma canon_uni (v : val) A :
    Δ `; Γ ⊢ v `: (forall, A)%typ ->
    exists M, v = (Λ M)%val.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma canon_exi (v : val) A :
    Δ `; Γ ⊢ v `: (exists, A) ->
    exists v', v = pack__v v'.
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma canon_base (v : val) (B : typ__base) :
    Δ `; Γ ⊢ v `: B ->
    exists (a : atom B), v = a.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma canon_prod (v : val) A B :
    Δ `; Γ ⊢ v `: (A `× B) -> exists m n, v = ((`m, n`))%val.
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
    exists M. apply step_tapp_tabs.
  - destruct IHjudge as [(M' & HM) | (m & ->)]; eauto.
    + left. eauto.
    + right. eauto.
  - left. destruct IHjudge1 as [(M' & HM) | (m & ->)]; eauto.
    specialize canon_exi with (1:=H0) as [v ->].
    exists (N.[inj__v v/]).
    apply step_unpack_pack.
  - right. auto.
  - left. destruct IHjudge as [(M' & HM) | (m & ->)]; eauto.
    specialize canon_base with (1:=H) as [a ->].
    eexists; eauto using step_una_base.
  - left. destruct IHjudge2 as [(N' & HN) | (n & ->)]; eauto.
    destruct IHjudge1 as [(M' & HM) | (m & ->)]; eauto.
    specialize canon_base with (1:=H) as [x ->].
    specialize canon_base with (1:=H0) as [y ->].
    eexists; eauto using step_bin_base.
  - left. destruct IHjudge1 as [(L' & HL) | (l & ->)]; eauto.
    specialize canon_base with (1:=H) as [a ->].
    depelim a. eauto using step_cond.
  - destruct IHjudge2 as [(N' & HN) | (n & ->)]; eauto.
    + left. eauto.
    + destruct IHjudge1 as [(M' & HM) | (m & ->)]; eauto.
      * left. eauto.
      * right. eauto.
  - left. destruct IHjudge as [(P' & HP) | (p & ->)]; eauto.
    specialize canon_prod with (1:=H) as (m & n & ->).
    eauto using step_prj_duo.
  - left. destruct IHjudge1 as [(M' & HM) | (m & ->)]; eauto.
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

Lemma distr_if_booll {A B} (f : A -> B) (b : bool) (x y : A) :
  f (if b then x else y) = if b then f x else f y.
Proof.
  destruct b; reflexivity.
Qed.

Lemma distr_if_boolr {A B} (f g : A -> B) (b : bool) (a : A) :
  (if b then f else g) a = if b then f a else g a.
Proof.
  destruct b; reflexivity.
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
  - apply judge_pack  with (B:= B.[σ]); eauto.
    replace (A.[up σ].[B.[ σ]/]) with (A.[B/].[σ])
      by by asimpl. eauto.
  - apply judge_unpack with (A:=A.[up σ]); eauto.
    rewrite up_subst. asimpl in IHjudge2.
    replace (B.[σ].[ren S]) with (B.[ren S].[up σ])
      by by asimpl. eauto.
  - asimpl in IHjudge. rewrite distr_if_booll.
    eauto.
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
  induction 1 in Γ2, δ, Hlookup |- *; asimpl; eauto 6.
Qed.

Local Hint Resolve judge_rename : core.

Lemma judge_rename_single Δ Γ M A B :
  Δ `; Γ ⊢ M `: B ->
  Δ `; A :: Γ ⊢ M.[ren S] `: B.
Proof.
  intro HM.
  eapply judge_rename; eauto.
Qed.

Local Hint Resolve judge_rename_single : core.

Definition lookup_ren_inv (Γ1 Γ2 : list typ) (δ : var -> var) :=
  forall x A, Γ2 !! (δ x) = Some A -> Γ1 !! x = Some A.

Lemma lookup_ren_inv_upren A Γ1 Γ2 δ :
  lookup_ren_inv Γ1 Γ2 δ ->
  lookup_ren_inv (A :: Γ1) (A :: Γ2) (upren δ).
Proof.
  unfold lookup_ren_inv.
  intros Hlook [| x] B; cbn; auto.
Qed.

Lemma lookup_ren_inv_up__Γ Γ1 Γ2 δ :
  lookup_ren_inv Γ1 Γ2 δ ->
  lookup_ren_inv (up__Γ Γ1) (up__Γ Γ2) δ.
Proof.
  unfold lookup_ren_inv.
  intros Hlook x B HB.
  rewrite list_lookup_fmap in HB.
  rewrite list_lookup_fmap.
  apply fmap_Some in HB as (C & HxC & ->).
  specialize Hlook with (1:=HxC).
  rewrite Hlook. reflexivity.
Qed.

Lemma judge_rename_inv δ Δ Γ1 Γ2 M A :
  lookup_ren_inv Γ1 Γ2 δ ->
  Δ `; Γ2 ⊢ M.[ren δ] `: A ->
  Δ `; Γ1 ⊢ M `: A.
Proof.
  induction M in δ, Δ, Γ1, Γ2, A |- *; intros Hlookup; asimpl; cbn.
  - unfold lookup_ren_inv in Hlookup.
    intros H%inv_judge_ident. eauto.
  - intros (B & C & -> & HB & HM)%inv_judge_abs.
    specialize lookup_ren_inv_upren with (A:=B) (1:=Hlookup) as Hlook.
    specialize IHM with (1:=Hlook) as IH. eauto.
  - intros (B & HM & HN)%inv_judge_app; eauto.
  - intros (B & -> & HM)%inv_judge_tabs.
    specialize lookup_ren_inv_up__Γ with (1:=Hlookup) as Hlook. eauto.
  - intros (B & C & -> & HC & HM)%inv_judge_tapp.
    eauto.
  - intros (B & C & -> & HC & HM)%inv_judge_pack. eauto.
  - intros (B & HA & HM & HN)%inv_judge_unpack.
    econstructor; eauto.
    eauto using lookup_ren_inv_upren, lookup_ren_inv_up__Γ.
  - intros ->%inv_judge_base. eauto.
  - intros (-> & HM)%inv_judge_uop. eauto.
  - intros (-> & HM & HN)%inv_judge_bop. eauto.
  - intros (B & C & -> & HM & HN)%inv_judge_duo. eauto.
  - intros (B & C & -> & HM)%inv_judge_prj. eauto.
  - intros (HL & HM & HN)%inv_judge_cond. eauto.
  - intros (B & HM & HN)%inv_judge_letin.
    eauto using lookup_ren_inv_upren.
  - inversion 1.
Qed.

Lemma lookup_ren_inv_S Γ A :
  lookup_ren_inv Γ (A :: Γ) S.
Proof.
  unfold lookup_ren_inv.
  intros [| x] B; cbn; auto.
Qed.

Lemma judge_rename_inv_single Δ Γ M A B :
  Δ `; A :: Γ ⊢ M.[ren S] `: B ->
  Δ `; Γ ⊢ M `: B.
Proof.
  eauto using lookup_ren_inv_S, judge_rename_inv.
Qed.

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
  lookup_subst (S Δ) (up__Γ Γ1) (up__Γ Γ2) σ.
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
  - intros (B & (C & D & [= <- <-] & HC & HM)%inv_judge_abs & HN)%inv_judge_app. eauto.
  - intros (B & C & -> & HB & (D & [= <-] & HM)%inv_judge_tabs)%inv_judge_tapp; cbn in *.
    replace [] with ((fun A => A.[C/]) <$> []) by reflexivity. eauto.
  - intros (B & HA & (C & D & [= <-] & HD & Hv)%inv_judge_pack & HN)%inv_judge_unpack.
    cbn in *. apply judge_subst_single with (A:=B.[D/]); eauto.
    replace A with (A.[ren S].[D/]) by by asimpl.
    replace [B.[D/]] with ((fun C => C.[D/]) <$> [B]) by by asimpl. eauto.
  - intros (-> & Ha%inv_judge_base)%inv_judge_uop. eauto.
  - intros (-> & HM & HN)%inv_judge_bop. eauto.
  - intros (B & C & -> & (D & E & [= <- <-] & Hm & Hn)%inv_judge_duo)%inv_judge_prj.
    destruct b; auto.
  - intros (Hb & HM & HN)%inv_judge_cond.
    destruct b; auto.
  - intros (B & Hv & HN)%inv_judge_letin. eauto.
  - inversion 1.
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
| big_abs M :
  (fun, M)%trm ↓ (fun, M)%val
| big_app (L M N : trm) m v :
  L ↓ (fun, N)%val ->
  M ↓ m ->
  N.[inj__v m/] ↓ v ->
  L M ↓ v
| big_tabs M :
  (Λ M)%trm ↓ (Λ M)%val
| big_tapp M N v :
  M ↓ (Λ N)%val ->
  N ↓ v ->
  (M [-])%trm ↓ v
| big_pack M m :
  M ↓ m ->
  pack M ↓ pack__v m
| big_unpack M N m n :
  M ↓ pack__v m ->
  N.[inj__v m/] ↓ n ->
  unpack M N ↓ n
| big_base {B} (a : atom B) :
  a ↓ a
| big_uop {B} (op : una B) M (a : atom B) :
  M ↓ a ->
  ( `< op >` M)%trm ↓ (to_atom B (denote_una op (denote_atom a)))
| big_bop {A B} (op : bin A B) M N (m n : atom A) :
  M ↓ m ->
  N ↓ n ->
  (M <` op `> N)%trm ↓ (to_atom B (denote_bin op (denote_atom m) (denote_atom n)))
| big_cond L M N (b : bool) v :
  L ↓ b ->
  (if b then M else N) ↓ v ->
  (if, L then, M else, N)%trm ↓ v
| big_duo M N m n :
  M ↓ m ->
  N ↓ n ->
  `(M, N)` ↓ ((`m, n`))%val
| big_prj (b : bool) P u v :
  P ↓ ((`u, v`))%val ->
  prj b P ↓ if b then u else v
| big_letin M N m n :
  M ↓ m ->
  N.[inj__v m/] ↓ n ->
  letin M N ↓ n
| big_ass M :
  M ↓ true ->
  ass M ↓ ttt
where "M ↓ v" := (big M v).

Lemma big_uop_alt {B} (op : una B) M (a v : atom B) :
  M ↓ a ->
  v = (to_atom B (denote_una op (denote_atom a))) ->
  ( `< op >` M)%trm ↓ v.
Proof.
  intros HM ->.
  eauto using big_uop.
Qed.
  
Lemma big_bop_alt {A B} (op : bin A B) M N (m n : atom A) (a : atom B) :
  M ↓ m ->
  N ↓ n ->
  a = (to_atom B (denote_bin op (denote_atom m) (denote_atom n))) ->
  (M <` op `> N)%trm ↓ a.
Proof.
  intros HM HN ->.
  eauto using big_bop.
Qed.

Section big_step.
  Local Hint Constructors rtc : core.

  Lemma steps_app__l M M' (n : val) :
    M ~>* M' ->
    M n ~>* M' n.
  Proof.
    induction 1; eauto.
  Qed.
  Local Hint Resolve steps_app__l : core.

  Lemma steps_app_is_val__l (M M' N : trm) :
    is_val N ->
    M ~>* M' ->
    M N ~>* M' N.
  Proof.
    intros [n ->]; eauto.
  Qed.
  Local Hint Resolve steps_app_is_val__l : core.

  Lemma steps_app__r (M N N' : trm) :
    N ~>* N' ->
    M N ~>* M N'.
  Proof.
    induction 1; eauto using step_app__r.
  Qed.
  Local Hint Resolve steps_app__r : core.
  
  Lemma steps_app_abs L M N N' (m : val) :
    L ~>* (fun, N)%val ->
    M ~>* m ->
    N.[inj__v m/] ~>* N' ->
    L M ~>* N'.
  Proof.
    intros HL HM HN.
    transitivity N.[inj__v m/]; auto.
    apply rtc_r with (y:=(fun, N)%trm m); eauto.
    transitivity (L m); eauto.
  Qed.
  Local Hint Resolve steps_app_abs : core.

  Lemma steps_tapp M M' :
    M ~>* M' ->
    (M [-])%trm ~>* (M' [-])%trm.
  Proof.
    induction 1; eauto.
  Qed.
  Local Hint Resolve steps_tapp : core.
  
  Lemma steps_tapp_tabs M N N' :
    M ~>* (Λ N)%trm ->
    N ~>* N' ->
    (M [-])%trm ~>* N'.
  Proof.
    intros HM HN.
    transitivity N; auto.
    apply rtc_r with (y:=((Λ N) [-])%trm); auto.
  Qed.
  Local Hint Resolve steps_tapp_tabs : core.

  Lemma steps_pack M M' :
    M ~>* M' ->
    pack M ~>* pack M'.
  Proof.
    induction 1; eauto.
  Qed.
  Local Hint Resolve steps_pack : core.

  Lemma steps_unpack M M' N :
    M ~>* M' ->
    unpack M N ~>* unpack M' N.
  Proof.
    induction 1; eauto.
  Qed.
  Local Hint Resolve steps_unpack : core.
  
  Lemma steps_unpack_pack M N N' (v : val) :
    M ~>* pack v ->
    N.[inj__v v/] ~>* N' ->
    unpack M N ~>* N'.
  Proof.
    intros HM HN.
    transitivity N.[inj__v v/]; auto.
    apply rtc_r with (y:=unpack (pack v) N); auto.
  Qed.
  Local Hint Resolve steps_unpack_pack : core.

  Lemma steps_uop {B} (op : una B) M M' :
    M ~>* M' ->
    ( `< op >` M)%trm ~>* ( `< op >` M')%trm.
  Proof.
    induction 1; eauto.
  Qed.
  Local Hint Resolve steps_uop : core.
  
  Lemma steps_uop_base {B} (op : una B) M (a : atom B) :
    M ~>* a ->
    ( `< op >` M)%trm ~>* to_atom B (denote_una op (denote_atom a)).
  Proof.
    intro HM.
    apply rtc_r with (y:=( `< op >` a)%trm); auto.
  Qed.
  Local Hint Resolve steps_uop_base : core.

  Lemma steps_bop__l {A B} (op : bin A B) M M' (n : val) :
    M ~>* M' ->
    (M <` op `> n)%trm ~>* (M' <` op `> n)%trm.
  Proof.
    induction 1; eauto.
  Qed.
  Local Hint Resolve steps_bop__l : core.

  Lemma steps_bop_is_val__l {A B} (op : bin A B) M M' N :
    is_val N ->
    M ~>* M' ->
    (M <` op `> N)%trm ~>* (M' <` op `> N)%trm.
  Proof.
    intros [n ->]; auto.
  Qed.
  Local Hint Resolve steps_bop_is_val__l : core.

  Lemma steps_bop__r {A B} (op : bin A B) M N N' :
    N ~>* N' ->
    (M <` op `> N)%trm ~>* (M <` op `> N')%trm.
  Proof.
    induction 1; eauto.
  Qed.
  Local Hint Resolve steps_bop__r : core.
  
  Lemma steps_bop_base {A B} (op : bin A B) M N (m n : atom A) :
    M ~>* m ->
    N ~>* n ->
    (M <` op `> N)%trm ~>* to_atom B (denote_bin op (denote_atom m) (denote_atom n)).
  Proof.
    intros HM HN.
    apply rtc_r with (y:= (m <` op `> n)%trm); auto.
    transitivity (M <` op `> n)%trm; eauto.
  Qed.
  Local Hint Resolve steps_bop_base : core.

  Lemma steps_cond__l L L' M N :
    L ~>* L' ->
    (if, L then, M else, N)%trm ~>* (if, L' then, M else, N)%trm.
  Proof.
    induction 1; eauto.
  Qed.
  Local Hint Resolve steps_cond__l : core.
  
  Lemma steps_cond L M N (b : bool) P :
    L ~>* b ->
    (if b then M else N) ~>* P ->
    (if, L then, M else, N)%trm ~>* P.
  Proof.
    intros HL HMN.
    transitivity (if b then M else N); eauto.
    apply rtc_r with (y:=(if, b then, M else, N)%trm); eauto.
  Qed.
  Local Hint Resolve steps_cond : core.

  Lemma steps_duo__l M M' (n : val) :
    M ~>* M' ->
    `(M, n)`%trm ~>* `(M', n)`%trm.
  Proof.
    induction 1; eauto.
  Qed.
  Local Hint Resolve steps_duo__l : core.

  Lemma steps_duo__r M N N' :
    N ~>* N' ->
    `(M, N)`%trm ~>* `(M, N')`%trm.
  Proof.
    induction 1; eauto.
  Qed.
  Local Hint Resolve steps_duo__r : core.

  Lemma steps_duo M N (m n : val) :
    M ~>* m ->
    N ~>* n ->
    `(M, N)`%trm ~>* `(m , n)`%trm.
  Proof.
    intros HM HN.
    transitivity `(M, n)`%trm; eauto.
  Qed.
  Local Hint Resolve steps_duo : core.

  Lemma steps_prj b P P' :
    P ~>* P' ->
    prj b P ~>* prj b P'.
  Proof.
    induction 1; eauto.
  Qed.
  Local Hint Resolve steps_prj : core.
  
  Lemma steps_prj_duo b P (u v : val) :
    P ~>* `(u , v)`%trm ->
    prj b P ~>* inj__v (if b then u else v).
  Proof.
    intros HP.
    rewrite distr_if_booll.
    apply rtc_r with (y:=prj b `(u, v)`%trm); auto.
  Qed.
  Local Hint Resolve steps_prj_duo : core.

  Lemma steps_letin__l M M' N :
    M ~>* M' ->
    letin M N ~>* letin M' N.
  Proof.
    induction 1; eauto.
  Qed.
  Local Hint Resolve steps_letin__l : core.
  
  Lemma steps_letin M N N' (m : val) :
    M ~>* m ->
    N.[inj__v m/] ~>* N' ->
    letin M N ~>* N'.
  Proof.
    intros HM HN.
    transitivity N.[inj__v m/]; auto.
    apply rtc_r with (y:=letin m N); eauto.
  Qed.
  Local Hint Resolve steps_letin : core.

  Lemma steps_ass M M' :
    M ~>* M' ->
    ass M ~>* ass M'.
  Proof.
    induction 1; eauto using step_ass__i.
  Qed.
  Local Hint Resolve steps_ass : core.

  Lemma steps_ass_true M :
    M ~>* true ->
    ass M ~>* ttt.
  Proof.
    intros HM.
    apply rtc_r with (y:=ass true); eauto.
  Qed.
  Local Hint Resolve steps_ass_true : core.
  
  Lemma big_sound M v :
    M ↓ v ->
    M ~>* v.
  Proof.
    induction 1; cbn in *; eauto 6.
  Qed.
End big_step.

Section step_big.
  Local Hint Constructors big : core.

  Lemma big__v (v : val) : v ↓ v.
  Proof.
    induction v; cbn; auto.
  Qed.
  Local Hint Resolve big__v : core.
  
  Lemma big_inj__v (v1 v2 : val) :
    v1 ↓ v2 -> v1 = v2.
  Proof.
    induction v1 in v2 |- *; inversion 1; subst; eauto;
      repeat lazymatch goal with
          IH : (forall v2, inj__v ?v1 ↓ v2 -> ?v1 = v2), H: (inj__v ?v1 ↓ _)
          |- _ => specialize IH with (1:=H) as <-
        end; try reflexivity.
  Qed.

  Lemma step__b_big M M' m :
    M ~>b M' -> M' ↓ m -> M ↓ m.
  Proof.
    inversion 1; subst; cbn; eauto.
    - inversion 1; subst.
      destr_inj_right_pair. auto.
    - inversion 1; subst.
      destr_inj_right_pair. auto.
    - rewrite <- distr_if_booll.
      intros <-%big_inj__v. auto.
    - inversion 1; subst.
      destr_inj_right_pair. auto.
  Qed.
  Local Hint Resolve step__b_big : core.

  Lemma step_big M M' m :
    M ~> M' -> M' ↓ m -> M ↓ m.
  Proof.
    intros (N & N' & K & -> & -> & H)%inv_step.
    induction K in N, N', m, H |- *; cbn;
      eauto using step__b_big;
      inversion 1; subst; eauto.
  Qed.
  
  Lemma steps_big M M' m :
    M ~>* M' -> M' ↓ m -> M ↓ m.
  Proof.
    induction 1; eauto using step_big.
  Qed.
  
  Lemma big_complete M (v : val) :
    M ~>* v -> M ↓ v.
  Proof.
    remember (inj__v v) as V eqn:HV.
    induction 1 in v, HV; subst; eauto.
    specialize IHrtc with (1:=eq_refl).
    eapply step_big; eauto.
  Qed.
End step_big.

Ltac reduce_big_det :=
  repeat lazymatch goal with
      IH: (forall v', ?M ↓ v' -> ?v = v'), H: (?M ↓ _)
      |- _ => specialize IH with (1:=H) as <- ||
             (specialize IH with (1:=H); injection IH as <- || injection IH as <- <-)
    end.

Lemma big_det M v1 v2 :
  M ↓ v1 -> M ↓ v2 -> v1 = v2.
Proof.
  induction 1 in v2 |- *; inversion 1; subst; auto;
    repeat destr_inj_right_pair;
    repeat (reduce_big_det; subst);  try reflexivity.
  - specialize IHbig with (1:=H5) as [= <-%inj_right_pair].
    reflexivity.
  - specialize IHbig1 with (1:=H8) as [= <-%inj_right_pair].
    specialize IHbig2 with (1:=H9) as [= <-%inj_right_pair].
    reflexivity.
Qed.

Lemma steps_order L M N :
  L ~>* M -> L ~>* N -> M ~>* N \/ N ~>* M.
Proof.
  induction 1 as [| L P M HLP HPM IHPM] in N |- *; eauto.
  inversion 1; subst.
  - right. transitivity P; eauto using rtc_once.
  - specialize det_step with (1:=H0) (2:=HLP) as ->. eauto.
Qed.

Lemma val_steps (m : val) M :
  m ~>* M -> M = m.
Proof.
  inversion 1; subst; try reflexivity.
  apply val_not_step in H0. contradiction.
Qed.

Equations size__t : typ -> nat :=
| Ident _ := 1
| (A `-> B)%typ := 1 + size__t A + size__t B
| (forall, A)%typ := 2 + size__t A
| (exists, A)%typ := 2 + size__t A
| Base _ := 1
| (A `× B)%typ := 1 + size__t A + size__t B
.

Lemma zero_size__t A :
  0 < size__t A.
Proof.
  funelim (size__t A); eauto with lia.
Qed.

Local Hint Resolve zero_size__t : core.

Equations measure_interp__t : val + trm -> typ -> nat :=
| inl _, A := size__t A
| inr _, A := 1 + size__t A.

Definition sem__t := val -> Prop.

Equations interp__t
  (ve : val + trm)
  (A : typ)
  (δ : var -> sem__t)
  : Prop by wf (measure_interp__t ve A) :=
| (inl v), Ident α, δ := δ α v
| (inl v), (A `-> B)%typ, δ :=
    exists M, v = (fun, M)%val /\ forall v, interp__t (inl v) A δ -> interp__t (inr M.[inj__v v/]) B δ
| (inl v), (forall, A)%typ, δ :=
    exists M, v = (Λ M)%val /\ forall τ : sem__t, interp__t (inr M) A (τ .: δ)
| (inl v), (exists, A)%typ, δ :=
    exists m, v = pack__v m /\ exists τ : sem__t,
        interp__t (inl m) A (τ .: δ)
| (inl v), Base B, δ := exists (a : atom B), v = a
| (inl v), (A `× B)%typ, δ :=
    exists m n, v = ((`m , n`))%val /\ interp__t (inl m) A δ /\ interp__t (inl n) B δ
| (inr M), A, δ :=
    exists v, M ↓ v /\ interp__t (inl v) A δ.
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
Next Obligation.
  simp measure_interp__t.
  simp size__t. lia.
Qed.
Next Obligation.
    simp measure_interp__t.
    simp size__t. lia.
Qed.

Notation "'V[|' A '|]'" :=
  (fun δ v => interp__t (inl v%val) A%typ δ)
    (at level 80) : type_scope.

Notation "'E[|' A '|]'" :=
  (fun δ M => interp__t (inr M%trm) A%typ δ)
    (at level 80) : type_scope.

Definition sem__Γ (Γ : list typ) (δ : var -> sem__t) (γ : var -> trm) :=
  forall x A, Γ !! x = Some A -> E[| A |] δ (γ x).

Notation "'G[|' Γ '|]'" :=
  (sem__Γ Γ) (at level 80) : type_scope.

Lemma incl__v A δ v :
  V[| A |] δ v -> E[| A |] δ v.
Proof.
  intros Hv. cbn in Hv |- *.
  simp interp__t. eauto using big__v.
Qed.

Local Hint Resolve incl__v : core.

Lemma nil_sem__Γ δ γ : G[| [] |] δ γ.
Proof.
  intros x A HxA. discriminate.
Qed.

Lemma cons_sem__Γ A Γ δ v γ :
  V[| A |] δ v ->
  G[| Γ |] δ γ ->
  G[| A :: Γ |] δ (inj__v v .: γ).
Proof.
  intros Hv HG [| x] B HB; cbn in HB |- *; eauto.
  injection HB as <-. eauto.
Qed.

Lemma understanding γ x (M : trm) :
  γ 0 = M ->
  (M .: S >>> γ) x = γ x.
Proof.
  destruct x as [| x]; asimpl; auto.
Qed.

Lemma inv_cons_sem__Γ A Γ δ γ :
  G[| A :: Γ |] δ γ -> exists v, V[| A |] δ v /\ G[| Γ |] δ (S >>> γ).
Proof.
  unfold sem__Γ.
  intros HG.
  specialize HG with (x:=0) (A:=A) (1:=eq_refl) as H.
  simp interp__t in H. destruct H as (v & H0 & Hv).
  exists v. split; auto.
  intros y B HB.
  simp interp__t.
  specialize HG with (x:=S y) (A:=B) (1:=HB) as HBy.
  simp interp__t in HBy.
Qed.

Definition sem_judge Γ M A :=
  forall δ γ, G[| Γ |] δ γ -> E[| A |] δ M.[γ].

Notation "Γ '|=' M '`:' A" := (sem_judge Γ M%trm A%typ) (at level 80, no associativity) : type_scope.


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
    V[| A |] δ v -> V[| A |] δ' v.
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
    - destruct Hv as (a & b & -> & Ha & Hb). eauto 7.
  Qed.

  Local Hint Resolve l__v1 : core.
  
  Lemma l__v A (δ δ' : var -> sem__t) v :
    (forall α v, δ α v <-> δ' α v) ->
    V[| A |] δ v <-> V[| A |] δ' v.
  Proof.
    split; eauto using iff_sym.
  Qed.

  Lemma l__e1 A (δ δ' : var -> sem__t) M :
    (forall α v, δ α v <-> δ' α v) ->
    E[| A |] δ M -> E[| A |] δ' M.
  Proof.
    intros H HM; cbn in HM |- *.
    simp interp__t in HM |- *.
    destruct HM as (v & HM & Hv).
    eexists; eauto.
  Qed.

  Local Hint Resolve l__e1 : core.
  
  Lemma l__e A (δ δ' : var -> sem__t) M :
    (forall α v, δ α v <-> δ' α v) ->
    E[| A |] δ M <-> E[| A |] δ' M.
  Proof.
    split; eauto using iff_sym.
  Qed.

  Lemma l__Γ1 Γ (δ δ' : var -> sem__t) γ :
    (forall α v, δ α v <-> δ' α v) ->
    G[| Γ |] δ γ -> G[| Γ |] δ' γ.
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
    G[| Γ |] δ γ <-> G[| Γ |] δ' γ.
  Proof.
    split; eauto using iff_sym.
  Qed.
  
  Global Instance sub_eq_impl : subrelation eq impl.
  Proof.
    unfold subrelation, impl.
    intros x y <-. auto.
  Qed.
  
  Lemma ren_sem__tv A (δ : var -> sem__t) (ρ : var -> var) v :
    V[| A |] (ρ >>> δ) v <-> V[| A.[ren ρ] |] δ v.
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
    - split; intros (a & b & -> & Ha & Hb);
        do 2 eexists; split; eauto.
      + rewrite IHA1 in Ha.
        rewrite IHA2 in Hb. auto.
      + rewrite IHA1.
        rewrite IHA2. auto.
  Qed.

  Lemma ren_sem__te A (δ : var -> sem__t) (ρ : var -> var) M :
    E[| A |] (ρ >>> δ) M <-> E[| A.[ren ρ] |] δ M.
  Proof.
    cbn. simp interp__t.
    split; intros (m & HM & Hm).
    - rewrite ren_sem__tv in Hm.
      eexists; eauto.
    - rewrite <- ren_sem__tv in Hm.
      eexists; eauto.
  Qed.
  
  Lemma sem__upΓ1 Γ τ δ γ :
    (G[| Γ |]) δ γ ->
    (G[| up__Γ Γ |]) (τ .: δ) γ.
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
    V[| A.[σ] |] δ v <-> V[| A |] (fun α => V[| σ α |] δ) v.
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
    - split; intros (a & b & -> & Ha & Hb); do 2 eexists; split; eauto;
        revert Ha Hb; rewrite <- IHA1; rewrite <- IHA2; auto.
  Qed.

  Lemma subst_interp__te M A (δ : var -> sem__t) (σ : var -> typ) :
    E[| A.[σ] |] δ M <-> E[| A |] (fun α => V[| σ α |] δ) M.
  Proof.
    cbn. simp interp__t.
    apply exist_proper.
    intro v.
    apply and_iff_compat_l.
    eauto using subst_interp__tv.
  Qed.

  Lemma single_subst_interp__tv v A B (δ : var -> sem__t) :
    V[| B.[A/] |] δ v <-> V[| B |] (V[| A |] δ .: δ) v.
  Proof.
    asimpl.
    rewrite subst_interp__tv.
    apply l__v.
    intros [| α] V; repeat (asimpl; simp interp__t); eauto.
  Qed.

  Lemma single_subst_interp__te M A B (δ : var -> sem__t) :
    E[| B.[A/] |] δ M <-> E[| B |] (V[| A |] δ .: δ) M.
  Proof.
    asimpl.
    rewrite subst_interp__te.
    apply l__e.
    intros [| α] V; repeat (asimpl; simp interp__t); eauto.
  Qed.
End boring.

Section compat.
  Variable Γ : list typ.

  Local Hint Constructors big : core.
  
  Lemma ident_compat x A :
    Γ !! x = Some A ->
    Γ |= ident x `: A.
  Proof.
    intros HA δ γ HG.
    cbv in HG.
    specialize HG with (1:=HA).
    simp interp__t in HG |- *.
  Qed.

  Lemma abs_compat M A B :
    A :: Γ |= M `: B ->
    Γ |= fun, M `: (A `-> B)%typ.
  Proof.
    intros HM δ γ HG.
    unfold sem_judge in HM.
    Search (G[| _ :: _ |]).
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
    Γ |= M `: (A `-> B)%typ ->
    Γ |= N `: A ->
    Γ |= M N `: B.
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
    up__Γ Γ |= M `: A ->
    Γ |= Λ M `: forall, A.
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
    Γ |= M `: (forall, A)%typ ->
    Γ |= M [-] `: A.[B/].
  Proof.
    intros HM δ γ HG.
    unfold sem_judge in HM.
    specialize HM with (1:=HG).
    simp interp__t in HM |- *.
    destruct HM as (m & HM & Hm).
    simp interp__t in Hm.
    destruct Hm as (L & -> & HL).
    specialize HL with (V[| B |] δ).
    simp interp__t in HL.
    destruct HL as (v & HLv & Hv).
    cbn. eexists;split; eauto.
    rewrite <- boring.single_subst_interp__tv in Hv. assumption.
  Qed.

  Lemma pack_compat M A B :
    Γ |= M `: A.[B/] ->
    Γ |= pack M `: exists, A.
  Proof.
    unfold sem_judge.
    intros HM δ γ HG.
    specialize HM with (1:=HG).
    cbn. simp interp__t in HM |- *.
    destruct HM as (m & HM & Hv).
    eexists; split; eauto.
    simp interp__t.
    eexists; split; eauto.
    exists (V[| B |] δ).
    rewrite <- boring.single_subst_interp__tv.
    assumption.
  Qed.
  
  Lemma unpack_compat M N A B :
    Γ |= M `: (exists, A) ->
    A :: up__Γ Γ |= N `: B.[ren S] ->
    Γ |= unpack M N `: B.
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

  Lemma letin_compat M N A B :
    Γ |= M `: A ->
    A :: Γ |= N `: B ->
    Γ |= letin M N `: B.
  Proof.
    intros HM HN δ γ HG; asimpl.
    unfold sem_judge in HM, HN.
    specialize HM with (1:=HG).
    simp interp__t in HM.
    destruct HM as (m & HM & Hm).
    specialize cons_sem__Γ with (1:=Hm) (2:=HG) as HGA.
    specialize HN with (1:=HGA).
    simp interp__t in HN |- *.
    destruct HN as (n & HN & Hn).
    eexists; split; eauto.
    econstructor; eauto.
    asimpl. assumption.
  Qed.

  Lemma base_compat B (a : atom B) :
    Γ |= a `: B.
  Proof.
    unfold sem_judge.
    intros δ γ HG.
    simp interp__t.
    eexists; cbn; split; eauto.
    simp interp__t. eauto.
  Qed.

  Lemma uop_compat B (op : una B) M :
    Γ |= M `: B ->
    Γ |= `< op >` M `: B.
  Proof.
    unfold sem_judge.
    intros HM δ γ HG.
    specialize HM with (1:=HG). cbn.
    simp interp__t in HM |- *.
    destruct HM as (m & HM & Hm).
    simp interp__t in Hm.
    destruct Hm as [a ->].
    eexists; split; eauto.
    simp interp__t.
    eauto.
  Qed.

  Lemma bop_compat A B (op : bin A B) M N :
    Γ |= M `: A ->
    Γ |= N `: A ->
    Γ |= M <` op `> N `: B.
  Proof.
    unfold sem_judge.
    intros HM HN δ γ HG.
    specialize HM with (1:=HG).
    specialize HN with (1:=HG).
    cbn. simp interp__t in HM, HN |- *.
    destruct HM as (m & HM & Hm).
    destruct HN as (n & HN & Hn).
    simp interp__t in Hm, Hn.
    destruct Hm as [am ->].
    destruct Hn as [an ->].
    eexists; split; eauto.
    simp interp__t. eauto.
  Qed.

  Lemma cond_compat L M N A :
    Γ |= L `: Bool ->
    Γ |= M `: A ->
    Γ |= N `: A ->
    Γ |= cond L M N `: A.
  Proof.
    unfold sem_judge.
    intros HL HM HN δ γ HG.
    specialize HL with (1:=HG).
    specialize HM with (1:=HG).
    specialize HN with (1:=HG).
    simp interp__t in HL, HM, HN |- *.
    destruct HL as (l & HL & Hl).
    destruct HM as (m & HM & Hm).
    destruct HN as (n & HN & Hn).
    simp interp__t in Hl.
    destruct Hl as [b ->].
    cbn. depelim b.
    exists (if b then m else n).
    split; eauto.
    - econstructor; eauto.
      destruct b; auto.
    - destruct b; auto.
  Qed.
  
  Lemma duo_compat M N A B :
    Γ |= M `: A ->
    Γ |= N `: B ->
    Γ |= `(M, N)` `: (A `× B)%typ.
  Proof.
    unfold sem_judge.
    intros HM HN δ γ HG.
    specialize HM with (1:=HG).
    specialize HN with (1:=HG).
    simp interp__t in HM, HN |- *.
    destruct HM as (m & HM & Hm).
    destruct HN as (n & HN & Hn).
    cbn. eexists; split; eauto.
    simp interp__t. eauto.
  Qed.

  Lemma prj_compat b M A B :
    Γ |= M `: (A `× B) ->
    Γ |= prj b M `: if b then A else B.
  Proof.
    unfold sem_judge.
    intros HM δ γ HG.
    specialize HM with (1:=HG).
    simp interp__t in HM |- *.
    destruct HM as (m & HM & Hm).
    simp interp__t in Hm.
    destruct Hm as (u & v & -> & Hu & Hv).
    cbn. eexists; split; eauto.
    destruct b; auto.
  Qed.
End compat.

Theorem sem_sound Δ Γ M A :
  Δ `; Γ ⊢ M `: A ->
  Γ |= M `: A.
Proof.
  induction 1; eauto using abs_compat, app_compat, ident_compat,
    tabs_compat, tapp_compat, pack_compat, unpack_compat,
    base_compat, uop_compat, bop_compat, cond_compat,
    duo_compat, prj_compat, letin_compat.
Qed.

Lemma big_safe M v :
  M ↓ v -> safe M.
Proof.
  unfold safe, progressive.
  intros HMv M' HMM'.
  specialize big_sound with (1:=HMv) as HMv__s.
  specialize steps_order with (1:=HMM') (2:=HMv__s) as [H | ->%val_steps]; eauto.
  inversion H; subst; eauto.
Qed.

Lemma sem_judge_safe M A :
  [] |= M `: A -> safe M.
Proof.
  unfold sem_judge.
  intro H.
  specialize H with (δ:=fun _ _ => False) (γ:=Ids_trm) (1:=nil_sem__Γ _ _).
  rewrite subst_id in H.
  simp interp__t in H.
  destruct H as (v & HMv & Hv).
  eauto using big_safe.
Qed.

Theorem termination M A :
  0 `; [] ⊢ M `: A ->
  exists v, M ↓ v.
Proof.
  intros H%sem_sound.
  unfold sem_judge in H.
  specialize H with (δ:=fun _ _ => False) (γ:=Ids_trm) (1:=nil_sem__Γ _ _).
  rewrite subst_id in H.
  simp interp__t in H.
  destruct H as (v & HMv & Hv).
  eauto.
Qed.

Notation "M ';,' N" := (let, M in N.[ren S])%trm (at level 97, right associativity) : trm_scope.

Lemma seq_subst M N σ :
  (M ;, N)%trm.[σ] = (M.[σ] ;, N.[σ])%trm.
Proof.
  autosubst.
Qed.

Lemma judge_seq Δ Γ M N A B :
  Δ `; Γ ⊢ M `: A ->
  Δ `; Γ ⊢ N `: B ->
  Δ `; Γ ⊢ M ;, N `: B.
Proof.
  intros HM HN.
  apply judge_letin with (A:=A); auto.
Qed.

Lemma inv_judge_seq Δ Γ M N B :
  Δ `; Γ ⊢ M ;, N `: B -> exists A, Δ `; Γ ⊢ M `: A /\ Δ `; Γ ⊢ N `: B.
Proof.
  intros (A & HM & HN)%inv_judge_letin.
  eexists; split; eauto using judge_rename_inv_single.
Qed.

Lemma big_seq M N m n :
  M ↓ m ->
  N ↓ n ->
  (M ;, N)%trm ↓ n.
Proof.
  intros HM HN.
  apply big_letin with (m:=m); asimpl; auto.
Qed.

Lemma seq_compat Γ M N A B :
  Γ |= M `: A ->
  Γ |= N `: B ->
  Γ |= M ;, N `: B.
Proof.
  intros HM HN.
  eapply letin_compat; eauto.
  unfold sem_judge in HN |- *.
  intros δ γ (a & Ha & HG)%inv_cons_sem__Γ.
  specialize HN with (1:=HG).
  simp interp__t in HN |- *.
  destruct HN as (n & HN & Hn).
  eexists; split; eauto.
  autosubst.
Qed.

Notation "fst," := (prj true).
Notation "snd," := (prj false).

Lemma judge_fst Δ Γ M A B :
  Δ `; Γ ⊢ M `: (A `× B)%typ ->
  Δ `; Γ ⊢ fst, M `: A.
Proof.
  intros H%(judge_prj _ _ true _ _ _). assumption.
Qed.
Local Hint Resolve judge_fst : core.

Lemma judge_snd Δ Γ M A B :
  Δ `; Γ ⊢ M `: (A `× B)%typ ->
  Δ `; Γ ⊢ snd, M `: B.
Proof.
  intros H%(judge_prj _ _ false _ _ _). assumption.
Qed.
Local Hint Resolve judge_snd : core.

Lemma big_fst P u v :
  P ↓ ((`u, v`))%val ->
  fst, P ↓ u.
Proof.
  intros H%(big_prj true). assumption.
Qed.
Local Hint Resolve big_fst : core.

Lemma big_snd P u v :
  P ↓ ((`u, v`))%val ->
  snd, P ↓ v.
Proof.
  intros H%(big_prj false). assumption.
Qed.
Local Hint Resolve big_snd : core.

Definition δ__emp : var -> sem__t := fun _ _ => False.

Lemma sem_closed M A :
  0 `; [] ⊢ M `: A -> E[| A |] δ__emp M.
Proof.
  intros HM%sem_sound.
  unfold sem_judge in HM.
  specialize HM with (1:=nil_sem__Γ δ__emp (@ids _ (Ids_trm))).
  cbn. simp interp__t in HM |- *.
  destruct HM as (v & HM & Hv).
  asimpl in HM. eauto.
Qed.

Section bit.
  Let BIT : typ := (exists, Ident 0 `× (Ident 0 `-> Ident 0) `× (Ident 0 `-> Bool))%typ.

  Lemma BIT_wf Δ :
    Δ ⊢wf BIT.
  Proof.
    econstructor; eauto.
    constructor; eauto with lia.
    constructor; eauto with lia.
  Qed.

  Local Hint Resolve BIT_wf : core.
  
  Let MyBit : trm := pack `(0%Z, (fun, 1%Z <` `- `> ident 0), (fun, 0%Z <` `<`  `> ident 0))`%trm.

  Lemma judge_MyBit Δ Γ :
    Δ `; Γ ⊢ MyBit `: BIT.
  Proof.
    unfold MyBit, BIT.
    apply judge_pack with (B:=Int); eauto. cbn.
    constructor; auto.
  Qed.

  Local Hint Resolve judge_MyBit : core.

  Let client : trm :=
        (
          unpack, MyBit in
          let, fst, (ident 0) in
          let, fst, (snd, (ident 1)) (ident 0) in
          let, fst, (snd, (ident 2)) (ident 0) in
          snd, (snd, (ident 3)) (ident 0)
        )%trm.

  Lemma judge_client Δ Γ :
    Δ `; Γ ⊢ client `: Bool.
  Proof.
    unfold client.
    apply judge_unpack with (A:=(Ident 0 `× (Ident 0 `-> Ident 0) `× (Ident 0 `-> Bool))%typ); auto. cbn.
    apply judge_letin with (A:=Ident 0); eauto.
    apply judge_letin with (A:=Ident 0).
    { apply judge_app with (A:=Ident 0); auto.
      apply judge_fst with (B:=(Ident 0 `-> Bool)%typ).
      apply judge_snd with (A:=Ident 0). auto. }
    apply judge_letin with (A:=Ident 0).
    { apply judge_app with (A:=Ident 0); auto.
      apply judge_fst with (B:=(Ident 0 `-> Bool)%typ).
      apply judge_snd with (A:=Ident 0). auto. }
    apply judge_app with (A:=Ident 0); auto.
    apply judge_snd with (A:=(Ident 0 `-> Ident 0)%typ).
    apply judge_snd with (A:=Ident 0). auto.
  Qed.
  Local Hint Resolve judge_client : core.

  Local Hint Constructors big : core.
  Local Hint Resolve big_bop_alt : core.
  
  Lemma big_client :
    client ↓ false.
  Proof.
    unfold client, MyBit.
    econstructor; eauto.
    apply big_letin with (m:=0%Z); cbn; eauto; asimpl.
    apply big_letin with (m:=1%Z); cbn; asimpl.
    { econstructor; eauto. asimpl.
      specialize (big_bop (A:=Int) (B:=Int)) with (op:=Sub) (M:=1%Z) (N:=0%Z) (m:=1%Z) (n:=0%Z) as H.
      specialize H with (1:=big_base 1%Z) (2:=big_base 0%Z).
      simp denote_atom in H. }
    apply big_letin with (m:=0%Z); cbn; asimpl.
    { econstructor; eauto. asimpl.
      specialize (big_bop (A:=Int) (B:=Int)) with (op:=Sub) (M:=1%Z) (N:=1%Z) (m:=1%Z) (n:=1%Z) as H.
      specialize H with (1:=big_base 1%Z) (2:=big_base 1%Z).
      simp denote_atom in H. }
    econstructor; eauto. asimpl.
    specialize (big_bop (A:=Int) (B:=Bool)) with (op:=Lt) (M:=0%Z) (N:=0%Z) (m:=0%Z) (n:=0%Z) as H.
    specialize H with (1:=big_base 0%Z) (2:=big_base 0%Z).
    simp denote_atom in H.
  Qed.                                          
  
  Let MyBit__unsafe : val :=
        pack__v
          ((`0%Z,
             (fun, (ass ((ident 0 <` `= `> 0%Z) <` `\/ `> (ident 0 <` `= `> 1%Z)));, 1%Z <` `- `> ident 0),
             (fun, (ass ((ident 0 <` `= `> 0%Z) <` `\/ `> (ident 0 <` `= `> 1%Z)));, 0%Z <` `<` `> ident 0)
               `))%val.

  Lemma not_judge_MyBit__unsafe Δ Γ A :
    ~ (Δ `; Γ ⊢ MyBit__unsafe `: A).
  Proof.
    intros
      (B & C & -> & _ &
                   (D & E & _ & _ &
                      (F & G & -> &
                                   (I & J & -> & _ &
                                                (K & HM & _)%inv_judge_seq
                                   )%inv_judge_abs & _
                      )%inv_judge_duo
                   )%inv_judge_duo
      )%inv_judge_pack.
    inversion HM.
  Qed.  
  
  Lemma sem_MyBit__unsafe δ :
    V[| BIT |] δ MyBit__unsafe.
  Proof.
    cbn. simp interp__t.
    subst MyBit__unsafe.
    subst BIT.
    simp interp__t.
    eexists; split; eauto.
    exists (fun (v : val) => v = 0%Z \/ v = 1%Z).
    simp interp__t.
    do 2 eexists; split; eauto. split.
    { simp interp__t. cbn. auto. }
    simp interp__t.
    do 2 eexists; split; eauto. split; simp interp__t.
    - eexists; split; eauto.
      intros v Hv. rewrite seq_subst. asimpl.
      simp interp__t in Hv |- *. cbn in Hv.
      destruct Hv as [-> | ->]; asimpl.
      + exists 1%Z. split.
        * econstructor; eauto. asimpl. eauto.
        * simp interp__t. cbn. auto.
      + exists 0%Z. split.
        * econstructor; eauto. asimpl. eauto.
        * simp interp__t. cbn. auto.
    - eexists; split; eauto.
      intros v Hv. rewrite seq_subst. asimpl.
      simp interp__t in Hv |- *. cbn in Hv.
      destruct Hv as [-> | ->]; asimpl.
      + exists false. split.
        * econstructor; eauto. asimpl. eauto.
        * simp interp__t. eauto.
      + exists true. split.
        * econstructor; eauto. asimpl. eauto.
        * simp interp__t. eauto.
  Qed.

  Lemma sem_client_MyBit__unsafe M A :
    0 `; [BIT] ⊢ M `: A ->
    safe (M.[inj__v MyBit__unsafe/]).
  Proof.
    intros HM%sem_sound.
    apply sem_judge_safe with (A:=A).
    unfold sem_judge in HM |- *.
    intros δ γ HG.
    specialize cons_sem__Γ with (1:=sem_MyBit__unsafe δ) (2:=HG) as H.
    specialize HM with (1:=H). autosubst.
  Qed.
End bit.
