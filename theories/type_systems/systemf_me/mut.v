From Autosubst Require Export Autosubst.
From ffpl.lib Require Export maps.
From Equations Require Export Equations Signature.

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

Set Transparent Obligations.
Equations Derive NoConfusion NoConfusionHom Subterm EqDec for unit.
Equations Derive NoConfusion NoConfusionHom Subterm EqDec for Z.
Next Obligation.
  apply Z.eq_dec.
Defined.

Variant prim : Set :=
  | Unit
  | Bool
  | Int
.

Equations Derive NoConfusion NoConfusionHom Subterm EqDec for prim.

Global Instance decide_eq_prim (A B : prim) : Decision (A = B).
Proof.
  apply prim_EqDec.
Qed.

Definition denote_prim (B : prim) : Set :=
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
| Base (A : prim)
| Prod (A B : typ)
| Sum (A B : typ)
(* Reference.  *)
| Ref (A : typ)
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
Coercion Base : prim >-> typ.
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
Infix "⊕" :=
  Sum
    (at level 100, right associativity)
    : typ_scope.

Variant atom : prim -> Set :=
  | ttt          : atom Unit
  | bewl (b : bool) : atom Bool
  | int (z : Z)  : atom Int
.
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

Ltac elim_inj_right_pair :=
  lazymatch goal with
    H: existT ?B _ = existT ?B _
    |- _ => apply inj_right_pair in H; subst
  end.
Local Hint Extern 2 => elim_inj_right_pair : core.

Coercion bewl : bool >-> atom.
Coercion int : Z >-> atom.

Equations denote_atom : forall {B : prim}, atom B -> denote_prim B :=
| ttt    => tt
| bewl b => b
| int z  => z
.

Equations to_atom : forall B, denote_prim B -> atom B :=
| Unit, tt => ttt
| Bool, b  => b
| Int,  z  => z
.

Variant una : prim ->  Set :=
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

Definition denote_una_typ {B : prim} (op : una B) : Set := denote_prim B.

Equations denote_una : forall {B} (op : una B), denote_prim B -> denote_prim B :=
| Not := negb
| Neg := Z.opp
.

Variant bin : prim -> prim -> Set :=
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

Definition denote_bin_typs {A B} (op : bin A B) : Set * Set := (denote_prim A, denote_prim B).

Equations denote_bin : forall {A B} (op : bin A B), denote_prim A -> denote_prim A -> denote_prim B :=
| Add => Z.add
| Sub => Z.sub
| Mul => Z.mul
| Eq  => Z.eqb
| Lt  => Z.ltb
| And => andb
| Or  => orb
.

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
| letin (M : trm) (N : {bind 1 of trm})
| cond (L M N : trm)
| inlr (b : bool) (M : trm)
| mtch (L : trm) (M N : {bind 1 of trm})
(* References and mutability  *)
| loc (l : nat)
| new (M : trm)
| deref (M : trm)
| store (M N : trm)
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
  - destruct (decide (b = b0)) as [<- | H]; repeat dec_eq_ind.
  - destruct (decide (l = l0)) as [<- | H]; dec_eq_ind.
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
Notation "'!,' M" := (deref M%trm) (at level 100, right associativity) : trm_scope.
Notation "M '<-' N" := (store M%trm N%trm) (at level 98, right associativity) : trm_scope.

Coercion ident : var >->trm.
Coercion base : atom >-> trm.
Coercion app : trm >-> Funclass.

Inductive val :=
| abs__v (M : trm)
| tabs__v (M : trm)
| pack__v (v : val)
| base__v {T} (a : atom T)
| duo__v (v1 v2 : val)
| inlr__v (b : bool) (v : val)
| loc__v (n : nat)
.

Equations Derive NoConfusion NoConfusionHom Subterm EqDec for val.
Next Obligation.
  induction x in y |- *; destruct y; try (right; discriminate); try (repeat dec_eq_ind; done).
  - destruct (decide (M = M0)) as [<- | HM]; dec_eq_ind.
  - destruct (decide (M = M0)) as [<- | HM]; dec_eq_ind.
  - destruct (decide (T = T0)) as [<- | HT]; try dec_eq_ind.
    destruct (decide (a = a0)) as [<- | Ha]; try dec_eq_ind.
    elim_inj_right_pair. contradiction.
  - destruct (decide (b = b0)) as [<- | Hb]; repeat dec_eq_ind.
  - destruct (decide (n = n0)) as [<- | H]; dec_eq_ind.
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
Coercion loc__v : nat >-> val.

Fixpoint inj__v (v : val) : trm :=
  match v with
  | base__v a    => a
  | (fun, M)%val => (fun, M)%trm
  | (Λ M)%val  => (Λ M)%trm
  | pack__v v    => pack $ inj__v v
  | (`v1, v2`)%val => `(inj__v v1, inj__v v2)`
  | inlr__v b v      => inlr b $ inj__v v
  | loc__v n         => loc n
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

Lemma inlr_is_val b M :
  is_val M ->
  is_val (inlr b M).
Proof.
  intros [m ->].
  exists (inlr__v b m); reflexivity.
Qed.
Local Hint Resolve inlr_is_val : core.

Lemma loc_is_val (l : nat) :
  is_val (loc l).
Proof.
  exists l. reflexivity.
Qed.
Local Hint Resolve loc_is_val : core.
  
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

Lemma mtch_is_not_val L M N :
  ~ is_val (mtch L M N).
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve mtch_is_not_val : core.

Lemma new_is_not_val M :
  ~ is_val (new M).
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve new_is_not_val : core.

Lemma deref_is_not_val M :
  ~ is_val (!, M)%trm.
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve deref_is_not_val : core.

Lemma store_is_not_val M N :
  ~ is_val (M <- N)%trm.
Proof.
  intros [[] H]; cbn in H; discriminate.
Qed.
Local Hint Resolve store_is_not_val : core.

Lemma inj_inj__v v1 v2 :
  inj__v v1 = inj__v v2 -> v1 = v2.
Proof.
  induction v1 as
    [M1 | M1 | v1 IHv1 | a1 | m1 IHm1 n1 IHn1 | b1 m1 IHm1 | l1]
    in v2 |- *;
    destruct v2 as [M2 | M2 | v2 | a2 | m2 n2 | b2 m2 | l2];
    cbn; try discriminate;
    try injection 1 as <-; try reflexivity.
  - intros [= <-%IHv1]. reflexivity.
  - apply inj_right_pair in H as <-. reflexivity.
  - intros [= <-%IHm1 <-%IHn1]. reflexivity.
  - specialize IHm1 with (1:=H) as <-.
    reflexivity.
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

Lemma inlr_inj__v b M v :
  inlr b M = inj__v v -> exists m, M = inj__v m /\ v = inlr__v b m.
Proof.
  destruct v; discriminate || intros [= -> ->]. eauto.
Qed.

Lemma loc_inj__v (l : nat) v :
  loc l = inj__v v -> v = l.
Proof.
  destruct v; discriminate || intros [= ->]. reflexivity.
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

Lemma mtch_not_inj__v L M N v :
  mtch L M N <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma new_not_inj__v M v :
  new M <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma deref_not_inj__v M v :
  (!, M)%trm <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma store_not_inj__v M N v :
  (M <- N)%trm <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Ltac elim_inj__v :=
  lazymatch goal with
  | H: inj__v _ = inj__v _ |- _ => apply inj_inj__v in H as ->
  | H: (fun, _)%trm = inj__v _ |- _ => apply abs_inj__v in H as ->
  | H: inj__v _ = (fun, _)%trm |- _ => symmetry in H; apply abs_inj__v in H as ->
  | H: (Λ _)%trm = inj__v _ |- _ => apply tabs_inj__v in H as ->
  | H: inj__v _ = (Λ _)%trm |- _ => symmetry in H; apply tabs_inj__v in H as ->
  | H: pack _ = inj__v _ |- _ => apply pack_inj__v in H as (? & -> & ->)
  | H: inj__v _ = pack _ |- _ => symmetry in H; apply pack_inj__v in H as (? & -> & ->)
  | H: @base ?T _ = inj__v _ |- _ => apply (base_inj__v (T:=T)) in H as ->
  | H: inj__v _ = @base ?T _ |- _ => symmetry in H; apply (base_inj__v (T:=T)) in H as ->
  | H: `(_, _)`%trm = inj__v _ |- _ => apply duo_inj__v in H as (? & ? & -> & -> & ->)
  | H: inj__v _ = `(_, _)`%trm |- _ => symmetry in H; apply duo_inj__v in H as (? & ? & -> & -> & ->)
  | H: inlr _ _ = inj__v _ |- _ => apply inlr_inj__v in H as (? & -> & ->)
  | H: inj__v _ = inlr _ _  |- _ => symmetry in H; apply inlr_inj__v in H as (? & -> & ->)
  | H: loc _ = inj__v _ |- _ => apply loc_inj__v in H as ->
  | H: inj__v _ = loc _ |- _ => symmetry in H; apply loc_inj__v in H as ->
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
  | H: mtch _ _ _ = inj__v _ |- _ => apply mtch_not_inj__v in H; contradiction
  | H: inj__v _ = mtch _ _ _  |- _ => symmetry in H; apply mtch_not_inj__v in H; contradiction
  | H: new _ = inj__v _ |- _ => apply new_not_inj__v in H; contradiction
  | H: inj__v _ = new _ |- _ => symmetry in H; apply new_not_inj__v in H; contradiction
  | H: (!, _)%trm = inj__v _ |- _ => apply deref_not_inj__v in H; contradiction
  | H: inj__v _ = (!, _)%trm |- _ => symmetry in H; apply deref_not_inj__v in H; contradiction
  | H: (_ <- _)%trm = inj__v _ |- _ => apply store_not_inj__v in H; contradiction
  | H: inj__v _ = (_ <- _)%trm |- _ => symmetry in H; apply store_not_inj__v in H; contradiction
  | H: ?a = ?a |- _ => clear H
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
| inlr__k (b : bool) (K : ktx)
| mtch__k (K : ktx) (M N : trm)
| new__k (K : ktx)
| deref__k (K : ktx)
| store__l (K : ktx) (v : val)
| store__r (M : trm) (K : ktx)
.

Reserved Notation "K '[[' M ']]'"
  (at level 96, left associativity).

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
  | inlr__k b K   => inlr b (K [[ M ]])
  | mtch__k K L N => mtch (K [[ M ]]) L N
  | new__k K      => new (K [[ M ]])
  | deref__k K    => !, (K [[ M ]])
  | store__l K v  => (K [[ M ]]) <- inj__v v
  | store__r N K  => N <- (K [[ M ]])
  end
where "K '[[' M ']]'" := (fill__k K M%trm) : trm_scope.

Reserved Infix "`∘" (at level 96, left associativity).

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
  | inlr__k b K   => inlr__k b (K `∘ K')
  | mtch__k K L N => mtch__k (K `∘ K') L N
  | new__k K      => new__k (K `∘ K')
  | deref__k K    => deref__k (K `∘ K')
  | store__l K v  => store__l (K `∘ K') v
  | store__r N K  => store__r N (K `∘ K')
  end
where "K1 '`∘' K2" := (comp__k K1 K2) : trm_scope.

Lemma fill_comp__k K K' M :
  ((K `∘ K') [[ M ]])%trm = (K [[ K' [[ M ]] ]])%trm.
Proof.
  induction K; cbn; f_equal; auto.
Qed.

Definition heap := gmap nat val.

Reserved Notation "h1 ',^' e1  '~>' h2 '^,' e2" (at level 80, no associativity).

Variant step__b (h : heap) : trm -> heap -> trm -> Prop :=
  | step_app_abs__b M (n : val) :
    h ,^ (fun, M) (inj__v n) ~> h ^, M.[ inj__v n /]
  | step_tapp_tabs__b M :
    h ,^ (Λ M) [-] ~> h ^, M
  | step_unpack_pack__b (v : val) N :
    h ,^ (unpack, pack (inj__v v) in N)%trm ~> h ^, N.[ inj__v v /]
  | step_una_base__b {B} (op : una B) (a : atom B) :
    h ,^ ( `< op >` a)%trm ~> h ^, to_atom B (denote_una op (denote_atom a))
  | step_bin_base__b {A B} (op : bin A B) (a1 a2 : atom A) :
    h ,^ (a1 <` op `> a2)%trm ~> h ^, to_atom B (denote_bin op (denote_atom a1) (denote_atom a2))
  | step_prj_duo__b b (m n : val) :
    h ,^ prj b `(m, n)`%trm ~> h ^, inj__v (if b then m else n)
  | step_cond_bool__b (b : bool) M N :
    h ,^ if, b then, M else, N ~> h ^, if b then M else N
  | step_letin__b (v : val) N :
    h ,^ (let, inj__v v in N)%trm ~> h ^, N.[ inj__v v /]
  | step_mtch_inlr__b b (v : val) M N :
    h ,^ mtch (inlr b v) M N ~> h ^, if b then M.[inj__v v/] else N.[inj__v v/]
  | step_new_alloc__b (l : nat) (v : val) :
    l = fresh (dom h) ->
    h ,^ (new (inj__v v))%trm ~> <[l:=v]> h ^, loc l
  | step_deref_loc__b (l : nat) (v : val) :
    h !! l = Some v ->
    h ,^ !, loc l ~> h ^, v
  | step_store_loc_val__b (l : nat) (v : val) :
    l ∈ dom h ->
    h ,^ loc l <- v ~> <[l:=v]> h ^, v 
where "h1 ',^' e1  '~>' h2 '^,' e2" := (step__b h1 e1%trm h2 e2%trm) : type_scope.

Reserved Notation "h1 ',`' M '~>' h2 '`,' N" (at level 80, no associativity).

Variant step (h : heap) : trm -> heap -> trm -> Prop :=
  | step_ktx M N K h' :
    h ,^ M ~> h' ^, N ->
    h ,` (K [[ M ]])%trm ~> h' `, (K [[ N ]])%trm
where "h1 ',`' M '~>' h2 '`,' N" := (step h1%list M%trm h2%list N%trm) : type_scope.

Lemma inv_step h h' KM KN :
  h ,` KM ~> h' `, KN -> exists M N K, KM = (K [[ M ]])%trm /\ KN = (K [[ N ]])%trm /\ h ,^ M ~> h' ^, N.
Proof.
  inversion 1; subst.
  do 3 eexists. repeat split; eauto.
Qed.

Local Hint Constructors step__b : core.

Lemma det_step__b h h__M h__N L M N :
  h ,^ L ~> h__M ^, M -> h ,^ L ~> h__N ^, N -> h__M = h__N /\ M = N.
Proof.
  inversion 1; inversion 1; subst; repeat elim_inj__v;
    repeat elim_inj_right_pair; auto.
  - rewrite H0 in H6.
    injection H6 as <-. auto.
Qed.

Local Hint Constructors step : core.

Lemma val_not_step__b h h' (v : val) N :
  ~ (h ,^ v ~> h' ^, N).
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
  - intros [= <- H%IHK]. assumption.
Qed.

Local Hint Resolve val_fill__k : core.

Ltac elim_val_fill__k :=
  lazymatch goal with
  | H: (_ [[ _ ]])%trm = inj__v _ |- _ => apply val_fill__k in H as [? ->]
  | H: inj__v _ = (_ [[ _ ]])%trm |- _ => symmetry in H; apply val_fill__k in H as [? ->]
  end.

(* Local Hint Extern 3 => elim_val_fill__k : core. *)

Lemma val_not_step (h h' : heap) (v : val) N :
  ~ (h ,` v ~> h' `, N).
Proof.
  inversion 1; subst; eauto.
  apply val_fill__k in H0.
  destruct H0 as [v' ->].
  revert H1. apply val_not_step__b.
Qed.

Lemma ctx_lift h h' M N K :
  h ,` M ~> h' `, N ->
  h ,` (K [[ M ]])%trm ~> h' `, (K [[ N ]])%trm.
Proof.
  inversion 1; subst.
  do 2 rewrite <- fill_comp__k.
  eauto.
Qed.

Local Hint Resolve ctx_lift : core.

Ltac val_tedium :=
  lazymatch goal with
    H: ?M = (_ [[ _ ]])%trm |- _
    => assert (is_val M) as [? HM__valeq] by eauto;
      rewrite HM__valeq in H
  end.

(* Local Hint Extern 3 => val_tedium : core. *)

Ltac tedium :=
  lazymatch goal with
    H : inj__v _ = (_ [[ ?N ]])%trm |- _ ,` ?N ~> _ `, _ -> _
    => elim_val_fill__k;
      intros ?%val_not_step__b; contradiction
  end.

(* Local Hint Extern 0 => tedium : core. *)

Ltac elim_det_step__b :=
  lazymatch goal with
  | |- ?h,^ ?N ~> _ ^, _ → ?h,^ ?N ~> _ ^, _ -> _ =>
      intros Hstep__b1 Hstep__b2;
      specialize det_step__b with (1:=Hstep__b1) (2:=Hstep__b2) as [<- <-]
  | Hstep__b1: ?h,^ ?N ~> _ ^, _ |- ?h,^ ?N ~> _ ^, _ -> _ =>
      intros Hstep__b2;
      specialize det_step__b with (1:=Hstep__b1) (2:=Hstep__b2) as [<- <-]
  | Hstep__b1: ?h,^ ?N ~> _ ^, _, Hstep__b2: ?h,^ ?N ~> _ ^, _ |- _ =>
      specialize det_step__b with (1:=Hstep__b1) (2:=Hstep__b2) as [<- <-]
  end.

Ltac ind_uniq_decomp__k :=
  lazymatch goal with
    IH: (∀ h h__M h__N KN M N M' N',
            (?KM [[M]])%trm = (KN [[N]])%trm →
            h,^ M ~> h__M ^, M' → h,^ N ~> h__N ^, N' → h__M = h__N ∧ ?KM = KN ∧ M = N),
      H: (?KM [[?M]])%trm = (?KN [[?N]])%trm
    |- ?h,^ ?M ~> ?h__M ^, ?M' → ?h,^ ?N ~> ?h__N ^, ?N' -> _
    => intros HM_step__b HN_step__b;
      specialize IH with (1:=H) (2:=HM_step__b) (3:=HN_step__b) as (<- & <- & <-)
  end.

Lemma uniq_decomp__k h h__M h__N KM KN M N M' N' :
  (KM [[ M ]])%trm = (KN [[ N ]])%trm ->
  h ,^ M ~> h__M ^, M' -> h ,^ N ~> h__N ^, N' ->
  h__M = h__N /\ KM = KN /\ M = N.
Proof.
  induction KM in h, h__M, h__N, KN, M, N, M', N' |- *;
    destruct KN; cbn; try discriminate;
    intro H; subst; try inversion H; subst;
    repeat elim_inj__v; try ind_uniq_decomp__k;
    try elim_det_step__b; auto;
    try (inversion 1; subst;
         repeat elim_inj_right_pair;
         try (try elim_inj__v; val_tedium);
         elim_val_fill__k;
         intros Hcontra%val_not_step__b;
         contradiction);
    try (intros Hcontra; inversion 1; subst;
         repeat elim_inj_right_pair;
         try (try elim_inj__v; val_tedium);
         elim_val_fill__k;
         apply val_not_step__b in Hcontra;
         contradiction).
Qed.

Lemma det_step h h__M h__N L M N :
  h ,` L ~> h__M `, M -> h ,` L ~> h__N `, N -> h__M = h__N /\ M = N.
Proof.
  intros (L' & M' & KM & -> & -> & HLM)%inv_step (L'' & N' & KN & H & -> & HLN)%inv_step.
  specialize uniq_decomp__k with (1:=H) (2:=HLM) (3:=HLN) as (<- & <- & <-).
  specialize det_step__b with (1:=HLM) (2:=HLN) as [_ <-]. done.
Qed.

Lemma step_app_abs h M (n : val) :
  h ,` (fun, M) (inj__v n) ~> h `, M.[ inj__v n /].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_app_abs : core.

Lemma step_app_abs_is_val h M N :
  is_val N ->
  h,` (fun, M) N ~> h`, M.[ N /].
Proof.
  intros [n ->]. eauto.
Qed.

Local Hint Resolve step_app_abs_is_val : core.

Lemma step_tapp_tabs h M :
  h,` (Λ M) [-] ~> h`, M.
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_tapp_tabs : core.

Lemma step_unpack_pack h (v : val) N :
  h,` (unpack, pack (inj__v v) in N)%trm ~> h`, N.[ inj__v v /].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_unpack_pack : core.

Lemma step_unpack_pack_is_val h M N :
  is_val M ->
  h,` unpack (pack M) N ~> h`, N.[ M /].
Proof.
  intros [v ->]. eauto.
Qed.

Local Hint Resolve step_unpack_pack_is_val : core.

Lemma step_una_base h {B} (op : una B) (a : atom B) :
  h,` ( `< op >` a)%trm ~> h`, to_atom B (denote_una op (denote_atom a)).
Proof.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_una_base : core.

Lemma step_una_base_equality h {B} (op : una B) (a v : atom B) :
  v = to_atom B (denote_una op (denote_atom a)) ->
  h,` ( `< op >` a)%trm ~> h`, v.
Proof.
  intros ->. eauto.
Qed.

Local Hint Resolve step_una_base_equality : core.

Lemma step_bin_base h {A B} (op : bin A B) (a1 a2 : atom A) :
  h,` (a1 <` op `> a2)%trm ~> h`, to_atom B (denote_bin op (denote_atom a1) (denote_atom a2)).
Proof.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_bin_base : core.

Lemma step_bin_base_equality h {A B} (op : bin A B) (a1 a2 : atom A) (a : atom B) :
  a = to_atom B (denote_bin op (denote_atom a1) (denote_atom a2)) ->
  h,` (a1 <` op `> a2)%trm ~> h`, a.
Proof.
  intros ->. eauto.
Qed.

Local Hint Resolve step_bin_base_equality : core.

Lemma step_prj_duo h b (m n : val) :
  h,` prj b `(m, n)`%trm ~> h`, inj__v (if b then m else n).
Proof.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_prj_duo : core.

Lemma step_prj_duo_equality h (b : bool) (m n v : val) :
  v = (if b then m else n) ->
  h,` prj b `(m, n)`%trm ~> h`, v.
Proof.
  intros ->. auto.
Qed.

Local Hint Resolve step_prj_duo_equality : core.

Lemma step_cond_bool h (b : bool) M N :
  h,` (if, b then, M else, N) ~> h`, if b then M else N.
Proof.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_cond_bool : core.

Lemma step_cond_bool_equality h (b : bool) M N O :
  O = (if b then M else N) ->
  h,` (if, b then, M else, N) ~> h`, O.
Proof.
  intros ->. auto.
Qed.

Local Hint Resolve step_cond_bool_equality : core.

Lemma step_letin h (v : val) N :
  h,` (let, inj__v v in N)%trm ~> h`, N.[inj__v v/].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_letin : core.

Lemma step_letin_is_val h M N :
  is_val M ->
  h,` (let, M in N)%trm ~> h`, N.[M/].
Proof.
  intros [v ->]; eauto.
Qed.

Local Hint Resolve step_letin_is_val : core.

Lemma step_mtch_inlr h (b : bool) (v : val) M N :
  h,` mtch (inlr b v) M N ~> h `, (if b then M.[inj__v v/] else N.[inj__v v/]).
Proof.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_mtch_inlr : core.

Lemma step_mtch_inlr_is_val h (b : bool) L M N :
  is_val L ->
  h,` mtch (inlr b L) M N ~> h `, (if b then M.[L/] else N.[L/]).
Proof.
  intros [v ->]. auto.
Qed.

Local Hint Resolve step_mtch_inlr_is_val : core.

Lemma step_mtch_inlr_equality h (b : bool) (v : val) M N O :
  O = (if b then M.[inj__v v/] else N.[inj__v v/]) ->
  h,` mtch (inlr b v) M N ~> h `, O.
Proof.
  intros ->. auto.
Qed.

Local Hint Resolve step_mtch_inlr_equality : core.

Lemma step_mtch_inlr_is_val_equality h (b : bool) L M N O :
  is_val L ->
  O = (if b then M.[L/] else N.[L/]) ->
  h,` mtch (inlr b L) M N ~> h `, O.
Proof.
  intros HL ->. auto.
Qed.

Local Hint Resolve step_mtch_inlr_is_val_equality : core.

Lemma step_new_alloc h (l : nat) (v : val) :
  l = fresh (dom h) ->
  h,` new v ~> <[l:=v]> h `, loc l.
Proof.
  intros Hl.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_new_alloc : core.
  
Lemma step_deref_loc h (l : nat) (v : val) :
  h !! l = Some v →
  h,` !, loc l ~> h `, v.
Proof.
  intro Hsome.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_deref_loc : core.

Lemma step_store_loc_val h (l : nat) (v : val) :
  l ∈ dom h ->
  h,` loc l <- v ~> <[l:=v]> h `, v.
Proof.
  intro Hlen.
  apply step_ktx with (K:=hole). auto.
Qed.

Local Hint Resolve step_store_loc_val : core.

Lemma step_app__r h h' (M N N' : trm) :
  h,` N ~> h' `, N' ->
  h,` M N ~> h' `, M N'.
Proof.
  replace (app M N) with (app__r M hole [[ N ]])%trm by reflexivity.
  replace (app M N') with (app__r M hole [[ N' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_app__r : core.

Lemma step_app__l h h' M M' (v : val) :
  h,` M ~> h' `, M' ->
  h,` M (inj__v v) ~> h' `, M' (inj__v v).
Proof.
  replace (app M (inj__v v)) with (app__l hole v [[ M ]])%trm by reflexivity.
  replace (app M' (inj__v v)) with (app__l hole v [[ M' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_app__l : core.

Lemma step_app_is_val__l h h' M M' N :
  is_val N ->
  h,` M ~> h' `, M' ->
  h,` M N ~> h' `, M' N.
Proof.
  intros [n ->]. auto.
Qed.

Local Hint Resolve step_app_is_val__l : core.

Lemma step_tapp h h' M M' :
  h,` M ~> h' `, M' ->
  h,` (M [-])%trm ~> h' `, (M' [-])%trm.
Proof.
  replace (M [-])%trm with (tapp__k hole [[ M ]])%trm by reflexivity.
  replace (M' [-])%trm with (tapp__k hole [[ M' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_tapp : core.

Lemma step_pack h h' M M' :
  h,` M ~> h' `, M' ->
  h,` pack M ~> h' `, pack M'.
Proof.
  replace (pack M) with (pack__k hole [[ M ]])%trm by reflexivity.
  replace (pack M') with (pack__k hole [[ M' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_pack : core.

Lemma step_unpack h h' M M' N :
  h,` M ~> h' `, M' ->
  h,` unpack M N ~> h' `, unpack M' N.
Proof.
  replace (unpack M N) with (unpack__k hole N [[ M ]])%trm by reflexivity.
  replace (unpack M' N) with (unpack__k hole N [[ M' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_unpack : core.

Lemma step_uop h h' {B} (op : una B) M M' :
  h,` M ~> h' `, M' ->
  h,` ( `< op >` M)%trm ~> h' `, ( `< op >` M')%trm.
Proof.
  replace ( `< op >` M)%trm with (uop__k op hole [[ M ]])%trm by reflexivity.
  replace ( `< op >` M')%trm with (uop__k op hole [[ M' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_uop : core.

Lemma step_bop__r h h' {A B} (op : bin A B) M N N' :
  h,` N ~> h' `, N' ->
  h,` (M <` op `> N)%trm ~> h' `, (M <` op `> N')%trm.
Proof.
  replace (M <` op `> N)%trm with (bop__r op M hole [[ N ]])%trm by reflexivity.
  replace (M <` op `> N')%trm with (bop__r op M hole [[ N' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_bop__r : core.

Lemma step_bop__l h h' {A B} (op : bin A B) M M' (v : val) :
  h,` M ~> h' `, M' ->
  h,` (M <` op `> v)%trm ~> h' `, (M' <` op `> v)%trm.
Proof.
  replace (M <` op `> v)%trm with (bop__l op hole v [[ M ]])%trm by reflexivity.
  replace (M' <` op `> v)%trm with (bop__l op hole v [[ M' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_bop__l : core.

Lemma step_bop_is_val__l h h' {A B} (op : bin A B) M M' N :
  is_val N ->
  h ,` M ~> h' `, M' ->
  h ,` (M <` op `> N)%trm ~> h' `, (M' <` op `> N)%trm.
Proof.
  intros [n ->]. auto.
Qed.

Local Hint Resolve step_bop_is_val__l : core.

Lemma step_duo__r h h' M N' N :
  h,` N ~> h' `, N' ->
  h,` `(M, N)` ~> h' `, `(M, N')`.
Proof.
  replace `(M, N)`%trm with (duo__r M hole [[ N ]])%trm by reflexivity.
  replace `(M, N')`%trm with (duo__r M hole [[ N' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_duo__r : core.

Lemma step_duo__l h h' M M' (v : val) :
  h,` M ~> h' `, M' ->
  h,` `(M, inj__v v)` ~> h' `, `(M', inj__v v)`.
Proof.
  replace `(M, inj__v v)`%trm with (duo__l hole v [[ M ]])%trm by reflexivity.
  replace `(M', inj__v v)`%trm with (duo__l hole v [[ M' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_duo__l : core.

Lemma step_duo_is_val__l h h' M M' N :
  is_val N ->
  h,` M ~> h' `, M' ->
  h,` `(M, N)` ~> h' `, `(M', N)`.
Proof.
  intros [n ->]. auto.
Qed.

Local Hint Resolve step_duo_is_val__l : core.

Lemma step_prj h h' b P P' :
  h,` P ~> h' `, P' ->
  h,` prj b P ~> h' `, prj b P'.
Proof.
  replace (prj b P) with (prj__k b hole [[ P ]])%trm by reflexivity.
  replace (prj b P') with (prj__k b hole [[ P' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_prj : core.

Lemma step_cond__l h h' L L' M N :
  h,` L ~> h' `, L' ->
  h,` (if, L then, M else, N) ~> h' `, if, L' then, M else, N.
Proof.
  replace (if, L then, M else, N)%trm with (cond__k hole M N [[ L ]])%trm by reflexivity.
  replace (if, L' then, M else, N)%trm with (cond__k hole M N [[ L' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_cond__l : core.

Lemma step_letin__l h h' M M' N :
  h,` M ~> h' `, M' ->
  h,` letin M N ~> h' `, letin M' N.
Proof.
  replace (letin M N) with (letin__k hole N [[ M ]])%trm by reflexivity.
  replace (letin M' N) with (letin__k hole N [[ M' ]])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_letin__l : core.

Lemma step_inlr h h' b M M' :
  h,` M ~> h' `, M' ->
  h,` inlr b M ~> h' `, inlr b M'.
Proof.
  replace (inlr b M) with (inlr__k b hole [[M]])%trm by reflexivity.
  replace (inlr b M') with (inlr__k b hole [[M']])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_inlr : core.

Lemma step_mtch h h' L L' M N :
  h,` L ~> h' `, L' ->
  h,` mtch L M N ~> h' `, mtch L' M N.
Proof.
  replace (mtch L M N) with (mtch__k hole M N [[L]])%trm by reflexivity.
  replace (mtch L' M N) with (mtch__k hole M N [[L']])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_mtch : core.

Lemma step_new h h' M M' :
  h,` M ~> h' `, M' ->
  h,` new M ~> h' `, new M'.
Proof.
  replace (new M) with (new__k hole [[M]])%trm by reflexivity.
  replace (new M') with (new__k hole [[M']])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_new : core.

Lemma step_deref h h' M M' :
  h,` M ~> h' `, M' ->
  h,` !, M ~> h' `, !, M'.
Proof.
  replace (!, M)%trm with (deref__k hole [[M]])%trm by reflexivity.
  replace (!, M')%trm with (deref__k hole [[M']])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_deref : core.

Lemma step_store__r h h' M N N' :
  h,` N ~> h' `, N' ->
  h,` (M <- N)%trm ~> h' `, (M <- N')%trm.
Proof.
  replace (M <- N)%trm with (store__r M hole [[N]])%trm by reflexivity.
  replace (M <- N')%trm with (store__r M hole [[N']])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_store__r : core.

Lemma step_store__l h h' M M' (n : val) :
  h,` M ~> h' `, M' ->
  h,` (M <- n)%trm ~> h' `, (M' <- n)%trm.
Proof.
  replace (M <- n)%trm with (store__l hole n [[M]])%trm by reflexivity.
  replace (M' <- n)%trm with (store__l hole n [[M']])%trm by reflexivity.
  auto.
Qed.

Local Hint Resolve step_store__l : core.

Lemma step_store_is_val__l h h' M M' N :
  is_val N ->
  h,` M ~> h' `, M' ->
  h,` (M <- N)%trm ~> h' `, (M' <- N)%trm.
Proof.
  intros [n ->]. auto.
Qed.

Local Hint Resolve step_store_is_val__l : core.

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
| wf_Base (B : prim) :
  Δ ⊢wf B
| wf_Prod A B :
  Δ ⊢wf A ->
  Δ ⊢wf B ->
  Δ ⊢wf (A `× B)
| wf_Sum A B :
  Δ ⊢wf A ->
  Δ ⊢wf B ->
  Δ ⊢wf (A ⊕ B)%typ
| wf_Ref A :
  Δ ⊢wf A ->
  Δ ⊢wf Ref A
where "Δ '⊢wf' τ" := (wf_typ Δ%nat τ%typ) : type_scope.

Local Hint Constructors wf_typ : core.

Definition up__typs (Γ : list typ) : list typ:= subst (ren S) <$> Γ.

Definition heap__typ := gmap nat typ.

Definition up__heap (Σ : heap__typ) : heap__typ := subst (ren S) <$> Σ.

Reserved Notation "Σ ';`' Δ '`;' Γ ⊢ M '`:' A"
  (at level 80, no associativity).

Inductive judge (Σ : heap__typ) (Δ : nat) (Γ : list typ) : trm -> typ -> Prop :=
| judge_ident (x : var) A :
  Γ !! x = Some A ->
  Σ ;` Δ `; Γ ⊢ x `: A
| judge_abs M A B :
  Δ ⊢wf A ->
  Σ ;` Δ `; A :: Γ ⊢ M `: B ->
  Σ ;` Δ `; Γ ⊢ (fun, M) `: (A `-> B)%typ
| judge_app M N A B :
  Σ ;` Δ `; Γ ⊢ M `: (A `-> B)%typ ->
  Σ ;` Δ `; Γ ⊢ N `: A ->
  Σ ;` Δ `; Γ ⊢ M N `: B
| judge_tabs M A :
  up__heap Σ ;` S Δ `; up__typs Γ ⊢ M `: A ->
  Σ ;` Δ `; Γ ⊢ Λ M `: (forall, A)
| judge_tapp M A B :
  Δ ⊢wf A ->
  Σ ;` Δ `; Γ ⊢ M `: (forall, B) ->
  Σ ;` Δ `; Γ ⊢ M [-] `: B.[A/]
| judge_pack M A B :
  Δ ⊢wf A ->
  Σ ;` Δ `; Γ ⊢ M `: B.[A/] ->
  Σ ;` Δ `; Γ ⊢ pack M `: (exists, B)
| judge_unpack M N A B :
  Δ ⊢wf B ->
  Σ ;` Δ `; Γ ⊢ M `: (exists, A) ->
  up__heap Σ ;` S Δ `; A :: up__typs Γ ⊢ N `: B.[ren S] ->
  Σ ;` Δ `; Γ ⊢ unpack M N `: B
| judge_base (B : prim) (a : atom B) :
  Σ ;` Δ `; Γ ⊢ a `: B
| judge_uop (B : prim) (op : una B) M :
  Σ ;` Δ `; Γ ⊢ M `: B ->
  Σ ;` Δ `; Γ ⊢ `< op >` M `: B
| judge_bop (A B : prim) (op : bin A B) M N :
  Σ ;` Δ `; Γ ⊢ M `: A ->
  Σ ;` Δ `; Γ ⊢ N `: A ->
  Σ ;` Δ `; Γ ⊢ M <` op `> N `: B
| judge_cond L M N A :
  Σ ;` Δ `; Γ ⊢ L `: Bool ->
  Σ ;` Δ `; Γ ⊢ M `: A ->
  Σ ;` Δ `; Γ ⊢ N `: A ->
  Σ ;` Δ `; Γ ⊢ if, L then, M else, N `: A
| judge_letin M N A B :
  Σ ;` Δ `; Γ ⊢ M `: A ->
  Σ ;` Δ `; A :: Γ ⊢ N `: B ->
  Σ ;` Δ `; Γ ⊢ let, M in N `: B
| judge_duo M N A B :
  Σ ;` Δ `; Γ ⊢ M `: A ->
  Σ ;` Δ `; Γ ⊢ N `: B ->
  Σ ;` Δ `; Γ ⊢ `(M, N)` `: (A `× B)
| judge_prj b P A B :
  Σ ;` Δ `; Γ ⊢ P `: (A `× B) ->
  Σ ;` Δ `; Γ ⊢ prj b P `: if b then A else B
| judge_inlr (b : bool) M A B :
  Δ ⊢wf (if b then B else A) ->
  Σ ;` Δ `; Γ ⊢ M `: (if b then A else B) ->
  Σ ;` Δ `; Γ ⊢ inlr b M `: (A ⊕ B)
| judge_mtch L M N A B C :
  Σ ;` Δ `; Γ ⊢ L `: (A ⊕ B) ->
  Σ ;` Δ `; A :: Γ ⊢ M `: C ->
  Σ ;` Δ `; B :: Γ ⊢ N `: C ->
  Σ ;` Δ `; Γ ⊢ mtch L M N `: C
| judge_loc (l : nat) A :
  Σ !! l = Some A ->
  Σ ;` Δ `; Γ ⊢ loc l `: Ref A
| judge_new M A :
  Σ ;` Δ `; Γ ⊢ M `: A ->
  Σ ;` Δ `; Γ ⊢ new M `: Ref A
| judge_deref M A :
  Σ ;` Δ `; Γ ⊢ M `: Ref A ->
  Σ ;` Δ `; Γ ⊢ !, M `: A
| judge_store M N A :
  Σ ;` Δ `; Γ ⊢ M `: Ref A ->
  Σ ;` Δ `; Γ ⊢ N `: A ->
  Σ ;` Δ `; Γ ⊢ M <- N `: A
where "Σ ';`' Δ '`;' Γ ⊢ M '`:' A" := (judge Σ Δ%nat Γ%list M%trm A%typ).

Section inv.
  Variable Σ : heap__typ.
  Variable Δ : nat.
  Variable Γ : list typ.
  
  Lemma inv_judge_ident (x : var) A :
    Σ ;` Δ `; Γ ⊢ x `: A ->
    Γ !! x = Some A.
  Proof.
    inversion 1; subst; auto.
  Qed.
    
  Lemma inv_judge_abs M C :
    Σ ;` Δ `; Γ ⊢ (fun, M) `: C ->
    exists A B, C = (A `-> B)%typ /\ Δ ⊢wf A /\ Σ ;` Δ `; A :: Γ ⊢ M `: B.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_app (M N : trm) B :
    Σ ;` Δ `; Γ ⊢ M N `: B ->
    exists A, Σ ;` Δ `; Γ ⊢ M `: (A `-> B)%typ /\ Σ ;` Δ `; Γ ⊢ N `: A.
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma inv_judge_tabs M C :
    Σ ;` Δ `; Γ ⊢ Λ M `: C ->
    exists A, C = (forall, A)%typ /\ up__heap Σ ;` S Δ `; up__typs Γ ⊢ M `: A.
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma inv_judge_tapp M C :
    Σ ;` Δ `; Γ ⊢ M [-] `: C ->
    exists A B, C = B.[A/] /\ Δ ⊢wf A /\ Σ ;` Δ `; Γ ⊢ M `: (forall, B).
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma inv_judge_pack M C :
    Σ ;` Δ `; Γ ⊢ pack M `: C ->
    exists A B, C = (exists, B)%typ /\ Δ ⊢wf A /\ Σ ;` Δ `; Γ ⊢ M `: B.[A/].
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma inv_judge_unpack M N B :
    Σ ;` Δ `; Γ ⊢ unpack M N `: B ->
    Δ ⊢wf B
    /\ exists A, Σ ;` Δ `; Γ ⊢ M `: (exists, A)
           /\ up__heap Σ ;` S Δ `; A :: up__typs Γ ⊢ N `: B.[ren S].
  Proof.
    inversion 1; subst; eauto.
  Qed.
    
  
  Lemma inv_judge_base (B : prim) (a : atom B) (C : typ) :
    Σ ;` Δ `; Γ ⊢ a `: C -> C = B.
  Proof.
    inversion 1; subst. auto.
  Qed.
    
  Lemma inv_judge_uop (B : prim) (op : una B) M (C : typ) :
    Σ ;` Δ `; Γ ⊢ `< op >` M `: C ->
    C = B /\ Σ ;` Δ `; Γ ⊢ M `: B.
  Proof.
    inversion 1; subst; auto.
  Qed.
  
  Lemma inv_judge_bop (A B : prim) (op : bin A B) M N (C : typ) :
    Σ ;` Δ `; Γ ⊢ M <` op `> N `: C ->
    C = B /\ Σ ;` Δ `; Γ ⊢ M `: A /\ Σ ;` Δ `; Γ ⊢ N `: A.
  Proof.
    inversion 1; subst; auto.
  Qed.
    
  Lemma inv_judge_cond L M N A :
    Σ ;` Δ `; Γ ⊢ (if, L then, M else, N) `: A ->
    Σ ;` Δ `; Γ ⊢ L `: Bool /\ Σ ;` Δ `; Γ ⊢ M `: A /\ Σ ;` Δ `; Γ ⊢ N `: A.
  Proof.
    inversion 1; subst; auto.
  Qed.
  
  Lemma inv_judge_letin M N B :
    Σ ;` Δ `; Γ ⊢ (let, M in N) `: B ->
    exists A, Σ ;` Δ `; Γ ⊢ M `: A /\ Σ ;` Δ `; A :: Γ ⊢ N `: B.
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma inv_judge_duo M N C :
    Σ ;` Δ `; Γ ⊢ `(M, N)` `: C ->
    exists A B, C = (A `× B)%typ /\ Σ ;` Δ `; Γ ⊢ M `: A /\ Σ ;` Δ `; Γ ⊢ N `: B.
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma inv_judge_prj b P C :
    Σ ;` Δ `; Γ ⊢ prj b P `: C ->
    exists A B, C = (if b then A else B) /\ Σ ;` Δ `; Γ ⊢ P `: (A `× B).
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma inv_judge_inlr (b : bool) M C :
    Σ ;` Δ `; Γ ⊢ inlr b M `: C ->
    exists A B, C = (A ⊕ B)%typ /\ Δ ⊢wf (if b then B else A)
           /\  Σ ;` Δ `; Γ ⊢ M `: (if b then A else B).
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma inv_judge_mtch L M N C :
    Σ ;` Δ `; Γ ⊢ mtch L M N `: C ->
    exists A B,
      Σ ;` Δ `; Γ ⊢ L `: (A ⊕ B)
      /\ Σ ;` Δ `; A :: Γ ⊢ M `: C
      /\ Σ ;` Δ `; B :: Γ ⊢ N `: C.
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma inv_judge_loc (l : nat) C :
    Σ ;` Δ `; Γ ⊢ loc l `: C ->
    exists A, C = Ref A /\ Σ !! l = Some A.
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma inv_judge_new M C :
    Σ ;` Δ `; Γ ⊢ new M `: C ->
    exists A, C = Ref A /\ Σ ;` Δ `; Γ ⊢ M `: A.
  Proof.
    inversion 1; subst; eauto.
  Qed.
  
  Lemma inv_judge_deref M A :
    Σ ;` Δ `; Γ ⊢ !, M `: A ->
    Σ ;` Δ `; Γ ⊢ M `: Ref A.
  Proof.
    inversion 1; subst; auto.
  Qed.
    
  Lemma inv_judge_store M N A :
    Σ ;` Δ `; Γ ⊢ M <- N `: A ->
    Σ ;` Δ `; Γ ⊢ M `: Ref A /\ Σ ;` Δ `; Γ ⊢ N `: A.
  Proof.
    inversion 1; subst; eauto.
  Qed.
End inv.

Section canon.
  Variable Σ : heap__typ.
  Variable Δ : nat.
  Variable Γ : list typ.

  Lemma canon_fun (v : val) A B :
    Σ ;` Δ `; Γ ⊢ v `: (A `-> B)%typ ->
    exists M, v = (fun, M)%val.
  Proof.
    inversion 1; subst; elim_inj__v. eauto.
  Qed.

  Lemma canon_uni (v : val) A :
    Σ ;` Δ `; Γ ⊢ v `: (forall, A) ->
    exists M, v = (Λ M)%val.
  Proof.
    inversion 1; subst; elim_inj__v. eauto.
  Qed.

  Lemma canon_exi (v : val) A :
    Σ ;` Δ `; Γ ⊢ v `: (exists, A) ->
    exists m, v = pack__v m.
  Proof.
    inversion 1; subst; elim_inj__v. eauto.
  Qed.

  Lemma canon_prim (v : val) (B : prim) :
    Σ ;` Δ `; Γ ⊢ v `: B ->
    exists (a : atom B), v = a.
  Proof.
    inversion 1; subst; elim_inj__v. eauto.
  Qed.

  Lemma canon_prod (v : val) A B :
    Σ ;` Δ `; Γ ⊢ v `: (A `× B) ->
    exists m n, v = (`m, n`)%val.
  Proof.
    inversion 1; subst; elim_inj__v. eauto.
  Qed.

  Lemma canon_sum (v : val) A B :
    Σ ;` Δ `; Γ ⊢ v `: (A ⊕ B) ->
    exists b m, v = inlr__v b m.
  Proof.
    inversion 1; subst; elim_inj__v. eauto.
  Qed.

  Lemma canon_ref (v : val) A :
    Σ ;` Δ `; Γ ⊢ v `: Ref A ->
    exists (l : nat), v = loc__v l.
  Proof.
    inversion 1; subst; elim_inj__v. eauto.
  Qed.
End canon.

Definition reducible (h : heap) (M : trm) : Prop :=
  exists h' M', h,` M ~> h' `, M'.

Definition progressive (h : heap) (M : trm) : Prop :=
  reducible h M \/ is_val M.

Definition heap_typing (h : heap) (Σ : heap__typ) : Prop :=
  forall l A,
    Σ !! l = Some A ->
    exists (v : val), h !! l = Some v /\ Σ ;` 0 `; [] ⊢ v `: A.

Infix "`::" := heap_typing (at level 80, no associativity) : type_scope.

Lemma heap_typing_lookup h Σ :
  h `:: Σ ->
  forall (l : nat) (A : typ),
    Σ !! l = Some A ->
    exists v : val, h !! l = Some v /\ Σ ;` 0 `; [] ⊢ v `: A.
Proof.
  unfold "`::". eauto.
Qed.
Local Hint Resolve heap_typing_lookup : core.

Lemma heap_typing_consistent h Σ (l : nat) (v : val) A :
  h `:: Σ ->
  h !! l = Some v ->
  Σ !! l = Some A ->
  Σ ;` 0 `; [] ⊢ v `: A.
Proof.
  unfold "`::".
  intros H Hhl HΣl.
  specialize H with (1:=HΣl) as (v' & Hhv' & Hv').
  rewrite Hhl in Hhv'.
  injection Hhv' as <-. assumption.
Qed.
Local Hint Resolve heap_typing_consistent : core.

(* Lemma heap_typing_length h Σ : *)
(*   h `:: Σ -> length h = length Σ. *)
(* Proof. *)
(*   intros H%List.Forall2_length. *)
(*   rewrite fmap_length in H. *)
(*   assumption. *)
(* Qed. *)

Theorem progress_trm Σ M A h :
  Σ ;` 0 `; [] ⊢ M `: A ->
  h `:: Σ ->
  progressive h M.
Proof.
  remember 0 as Δ eqn:eqΔ.
  remember [] as Γ eqn:eqΓ.
  intros H Hh.
  induction H in h, Hh, eqΔ, eqΓ |- *; subst; auto;
    repeat lazymatch goal with
      | IH: (forall h, 0 = 0 -> [] = [] -> h `:: ?Σ -> _), H: _ `:: ?Σ  |- _
        => specialize IH with (1:=eq_refl) (2:=eq_refl) (3:=H)
      | IH: forall _, _ = _ -> [_] = [] -> _ |- _ => clear IH
      | IH: forall _, 1 = 0 -> _ |- _ => clear IH
      end.
  - rewrite lookup_nil in H. discriminate.
  - right. auto.
  - left. destruct IHjudge2 as [(h' & N' & HN) | (n & ->)].
    + exists h', (M N'). auto.
    + destruct IHjudge1 as [(h' & M' & HM) | (m & ->)].
      * exists h', (M' n). auto.
      * specialize canon_fun with (1:=H) as [M ->].
        exists h, M.[inj__v n/].
        apply step_app_abs.
  - right. auto.
  - left. destruct IHjudge as [(h' & M' & HM) | (m & ->)].
    + exists h', (M' [-])%trm. auto.
    + specialize canon_uni with (1:=H0) as [M ->].
      exists h, M. apply step_tapp_tabs.
  - destruct IHjudge as [(h' & M' & HM) | (m & ->)].
    + left. exists h', (pack M'). auto.
    + right. auto.
  - left. destruct IHjudge1 as [(h' & M' & HM) | (m & ->)].
    + exists h', (unpack M' N). auto.
    + specialize canon_exi with (1:=H0) as [v ->].
      exists h, N.[inj__v v/]. apply step_unpack_pack.
  - right. auto.
  - left. destruct IHjudge as [(h' & M' & HM) | (m & ->)].
    + exists h', ( `< op >` M')%trm. auto.
    + specialize canon_prim with (1:=H) as [a ->].
      unfold reducible. cbn. eauto.
  - left. destruct IHjudge2 as [(h' & N' & HN) | (n & ->)].
    + exists h', (M <` op `> N')%trm. auto.
    + destruct IHjudge1 as [(h' & M' & HM) | (m & ->)].
      * exists h', (M' <` op `> n)%trm. auto.
      * specialize canon_prim with (1:=H) as [u ->].
        specialize canon_prim with (1:=H0) as [v ->].
        unfold reducible. cbn. eauto.
  - left. destruct IHjudge1 as [(h' & L' & HL) | (l & ->)].
    + exists h', (if, L' then, M else, N)%trm. auto.
    + specialize canon_prim with (1:=H) as [a ->].
      depelim a. exists h, (if b then M else N).
      apply step_cond_bool.
  - left. destruct IHjudge1 as [(h' & M' & HM) | (m & ->)].
    + exists h', (let, M' in N)%trm. auto.
    + exists h, N.[inj__v m/]. auto.
  - destruct IHjudge2 as [(h' & N' & HN) | (n & ->)].
    + left. exists h', `(M, N')`%trm. auto.
    + destruct IHjudge1 as [(h' & M' & HM) | (m & ->)].
      * left. exists h', `(M', n)`%trm. auto.
      * right. auto.
  - left. destruct IHjudge as [(h' & P' & HP) | (p & ->)].
    + exists h', (prj b P'). auto.
    + specialize canon_prod with (1:=H) as (u & v & ->).
      exists h, (if b then u else v). apply step_prj_duo.
  - destruct IHjudge as [(h' & M' & HM) | (m & ->)].
    + left. exists h', (inlr b M'). auto.
    + right. auto.
  - left. destruct IHjudge1 as [(h' & L' & HL) | (l & ->)].
    + exists h', (mtch L' M N). auto.
    + specialize canon_sum with (1:=H) as (b & v & ->).
      exists h, (if b then M.[inj__v v/] else N.[inj__v v/]).
      apply step_mtch_inlr.
  - right. auto.
  - left. destruct IHjudge as [(h' & M' & HM) | (m & ->)].
    + exists h', (new M'). auto.
    + remember (fresh (dom h)) as l eqn:Hl.
      exists (<[l:=m]> h), l. apply step_new_alloc.
      assumption.
  - left. destruct IHjudge as [(h' & M' & HM) | (m & ->)].
    + exists h', (!, M')%trm. auto.
    + specialize canon_ref with (1:=H) as [l ->].
      specialize inv_judge_loc with (1:=H) as (A' & [= <-] & HlA).
      specialize heap_typing_lookup with (1:=Hh) (2:=HlA) as (v & Hhlv & Hv).
      exists h, v. apply step_deref_loc. assumption.
  - left. destruct IHjudge2 as [(h' & N' & HN) | (n & ->)].
    + exists h', (M <- N')%trm. auto.
    + destruct IHjudge1 as [(h' & M' & HM) | (m & ->)].
      * exists h', (M' <- n)%trm. auto.
      * specialize canon_ref with (1:=H) as [l ->].
        specialize inv_judge_loc with (1:=H) as (A' & [= <-] & HlA).
        specialize heap_typing_lookup with (1:=Hh) (2:=HlA) as (v & Hhlv & Hv).
        exists (<[l:=n]> h), n. apply step_store_loc_val.
        eauto using elem_of_dom_2.
Qed.

Local Hint Constructors judge : core.

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
  Forall (wf_typ Δ) Γ -> Forall (wf_typ (S Δ)) (up__typs Γ).
Proof.
  unfold up__typs.
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

Definition wf_tsubst Δ1 Δ2 σ :=
  forall α, α < Δ1 -> Δ2 ⊢wf σ α.

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

Lemma up_subst__typs σ Γ :
  up__typs (subst σ <$> Γ) = subst (up σ) <$> up__typs Γ.
Proof.
  rewrite /up__typs.
  apply list_eq.
  intro x.
  rewrite !list_lookup_fmap.
  destruct (Γ !! x) as [A |] eqn:HA; asimpl; auto.
Qed.

Lemma up_subst__heap σ Σ :
  up__heap (subst σ <$> Σ) = subst (up σ) <$> up__heap Σ.
Proof.
  rewrite /up__heap.
  apply map_eq.
  intro l.
  rewrite !lookup_fmap.
  destruct (Σ !! l) as [A |] eqn:HA; asimpl; auto.
Qed.

Lemma judge_tsubst Σ Δ1 Δ2 Γ M A σ :
  wf_tsubst Δ1 Δ2 σ ->
  Σ ;` Δ1 `; Γ ⊢ M `: A ->
  (subst σ) <$> Σ ;` Δ2 `; (subst σ) <$> Γ ⊢ M `: A.[σ].
Proof.
  intros Hσ.
  induction 1 in Hσ, σ, Δ2 |- *; cbn; eauto.
  - constructor.
    rewrite list_lookup_fmap.
    apply fmap_Some_2. assumption.
  - constructor.
    rewrite up_subst__heap up_subst__typs. eauto.
  - replace (B.[A/].[σ]) with (B.[up σ].[A.[σ]/])
      by by asimpl. eauto.
  - apply judge_pack  with (A:= A.[σ]); eauto.
    replace (B.[up σ].[A.[ σ]/]) with (B.[A/].[σ])
      by by asimpl. eauto.
  - apply judge_unpack with (A:=A.[up σ]); eauto.
    rewrite up_subst__heap up_subst__typs. asimpl in IHjudge2.
    replace (B.[σ].[ren S]) with (B.[ren S].[up σ])
      by by asimpl. eauto.
  - asimpl in IHjudge. rewrite distr_if_booll.
    eauto.
  - setoid_rewrite distr_if_booll in IHjudge.
    constructor; eauto.
    destruct b; eauto.
  - constructor.
    rewrite lookup_fmap H.
    reflexivity.
Qed.

Local Hint Resolve judge_tsubst : core.

Lemma judge_tsubst_single Σ Δ Γ M A B :
  Δ ⊢wf B ->
  Σ ;` S Δ `; Γ ⊢ M `: A ->
  (fun C => C.[B/]) <$> Σ ;` Δ `; (fun C => C.[B/]) <$> Γ ⊢ M `: A.[ B /].
Proof.
  eauto.
Qed.

Local Hint Resolve judge_tsubst_single : core.

Definition lookup_ren {X} (Γ1 Γ2 : list X) (δ : var -> var) :=
  forall x A, Γ1 !! x = Some A -> Γ2 !! (δ x) = Some A.

Lemma lookup_ren_S X Γ (A : X) :
  lookup_ren Γ (A :: Γ) S.
Proof.
  unfold lookup_ren.
  auto.
Qed.

Local Hint Resolve lookup_ren_S : core.

Lemma lookup_ren_upren X (A : X) Γ1 Γ2 δ :
  lookup_ren Γ1 Γ2 δ ->
  lookup_ren (A :: Γ1) (A :: Γ2) (upren δ).
Proof.
  unfold lookup_ren.
  intros Hlook x B HB.
  destruct x as [| x]; cbn in *; auto.
Qed.
  
Local Hint Resolve lookup_ren_upren : core.

Lemma lookup_ren_up__typs (Γ1 Γ2 : list typ) δ :
  lookup_ren Γ1 Γ2 δ ->
  lookup_ren (up__typs Γ1) (up__typs Γ2) δ.
Proof.
  unfold lookup_ren, up__typs.
  intros Hlook x B HB.
  rewrite list_lookup_fmap in HB.
  rewrite list_lookup_fmap.
  apply fmap_Some in HB as (C & HxC & ->).
  specialize Hlook with (1:=HxC).
  rewrite Hlook. reflexivity.
Qed.

Local Hint Resolve lookup_ren_up__typs : core.

Lemma judge_rename δ Δ Σ Γ1 Γ2 M A :
  lookup_ren Γ1 Γ2 δ ->
  Σ ;` Δ `; Γ1 ⊢ M `: A ->
  Σ ;` Δ `; Γ2 ⊢ M.[ren δ] `: A.
Proof.
  intros Hlookup.
  induction 1 in Γ2, δ, Hlookup |- *; asimpl; eauto 7.
Qed.

Local Hint Resolve judge_rename : core.

Lemma judge_rename_single Σ Δ Γ M A B :
  Σ ;` Δ `; Γ ⊢ M `: B ->
  Σ ;` Δ `; A :: Γ ⊢ M.[ren S] `: B.
Proof.
  intro HM.
  eapply judge_rename; eauto.
Qed.

Local Hint Resolve judge_rename_single : core.

Definition lookup_ren_inv {X} (Γ1 Γ2 : list X) (δ : var -> var) :=
  forall x A, Γ2 !! (δ x) = Some A -> Γ1 !! x = Some A.

Lemma lookup_ren_inv_upren X (A : X) Γ1 Γ2 δ :
  lookup_ren_inv Γ1 Γ2 δ ->
  lookup_ren_inv (A :: Γ1) (A :: Γ2) (upren δ).
Proof.
  unfold lookup_ren_inv.
  intros Hlook [| x] B; cbn; auto.
Qed.

Lemma lookup_ren_inv_up__typs (Γ1 Γ2 : list typ) δ :
  lookup_ren_inv Γ1 Γ2 δ ->
  lookup_ren_inv (up__typs Γ1) (up__typs Γ2) δ.
Proof.
  unfold lookup_ren_inv.
  intros Hlook x B HB.
  rewrite list_lookup_fmap in HB.
  rewrite list_lookup_fmap.
  apply fmap_Some in HB as (C & HxC & ->).
  specialize Hlook with (1:=HxC).
  rewrite Hlook. reflexivity.
Qed.

Lemma judge_rename_inv δ Δ Σ Γ1 Γ2 M A :
  lookup_ren_inv Γ1 Γ2 δ ->
  Σ ;` Δ `; Γ2 ⊢ M.[ren δ] `: A ->
  Σ ;` Δ `; Γ1 ⊢ M `: A.
Proof.
  induction M in δ, Δ, Σ, Γ1, Γ2, A |- *; intros Hlookup; asimpl; cbn.
  - unfold lookup_ren_inv in Hlookup.
    intros H%inv_judge_ident. eauto.
  - intros (B & C & -> & HB & HM)%inv_judge_abs.
    specialize lookup_ren_inv_upren with (A:=B) (1:=Hlookup) as Hlook.
    specialize IHM with (1:=Hlook) as IH. eauto.
  - intros (B & HM & HN)%inv_judge_app; eauto.
  - intros (B & -> & HM)%inv_judge_tabs.
    specialize lookup_ren_inv_up__typs with (1:=Hlookup) as Hlook. eauto.
  - intros (B & C & -> & HC & HM)%inv_judge_tapp.
    eauto.
  - intros (B & C & -> & HC & HM)%inv_judge_pack. eauto.
  - intros (B & HA & HM & HN)%inv_judge_unpack.
    econstructor; eauto.
    eauto using lookup_ren_inv_upren, lookup_ren_inv_up__typs.
  - intros ->%inv_judge_base. eauto.
  - intros (-> & HM)%inv_judge_uop. eauto.
  - intros (-> & HM & HN)%inv_judge_bop. eauto.
  - intros (B & C & -> & HM & HN)%inv_judge_duo. eauto.
  - intros (B & C & -> & HM)%inv_judge_prj. eauto.
  - intros (B & HM & HN)%inv_judge_letin.
    eauto using lookup_ren_inv_upren.
  - intros (HL & HM & HN)%inv_judge_cond. eauto.
  - intros (B & C & -> & HBC & HM)%inv_judge_inlr. eauto.
  - intros (B & C & HL & HM & HN)%inv_judge_mtch.
    econstructor; eauto using lookup_ren_inv_upren.
  - intros (B & -> & Hl)%inv_judge_loc. auto.
  - intros (B & -> & HM)%inv_judge_new. eauto.
  - intros HM%inv_judge_deref. eauto.
  - intros (HM & HN)%inv_judge_store. eauto.
Qed.

Lemma lookup_ren_inv_S X Γ (A : X) :
  lookup_ren_inv Γ (A :: Γ) S.
Proof.
  unfold lookup_ren_inv.
  intros [| x] B; cbn; auto.
Qed.

Lemma judge_rename_inv_single Σ Δ Γ M A B :
  Σ ;` Δ `; A :: Γ ⊢ M.[ren S] `: B ->
  Σ ;` Δ `; Γ ⊢ M `: B.
Proof.
  eauto using lookup_ren_inv_S, judge_rename_inv.
Qed.

Definition lookup_subst Σ Δ (Γ1 Γ2 : list typ) (σ : var -> trm) :=
  forall x B, Γ1 !! x = Some B -> Σ ;` Δ `; Γ2 ⊢ σ x `: B.

Lemma lookup_subst_up Δ A Σ Γ1 Γ2 σ :
  lookup_subst Σ Δ Γ1 Γ2 σ ->
  lookup_subst Σ Δ (A :: Γ1) (A :: Γ2) (up σ).
Proof.
  unfold lookup_subst.
  intros Hlook [| x] B HB; asimpl in *.
  - injection HB as <-. constructor.
    reflexivity.
  - specialize Hlook with (1:=HB). eauto.
Qed.

Local Hint Resolve lookup_subst_up : core.

Lemma lookup_subst_up__typs Σ Δ Γ1 Γ2 σ :
  lookup_subst Σ Δ Γ1 Γ2 σ ->
  lookup_subst (up__heap Σ) (S Δ) (up__typs Γ1) (up__typs Γ2) σ.
Proof.
  unfold lookup_subst, up__typs.
  intros Hlook x B HB.
  rewrite list_lookup_fmap in HB.
  apply fmap_Some in HB as (A & HxA & ->).
  specialize Hlook with (1:=HxA).
  apply judge_tsubst with (Δ1 := Δ); eauto.
Qed.

Local Hint Resolve lookup_subst_up__typs : core.

Lemma judge_subst σ Σ Δ M Γ1 Γ2 A :
  lookup_subst Σ Δ Γ1 Γ2 σ ->
  Σ ;` Δ `; Γ1 ⊢ M `: A ->
  Σ ;` Δ `; Γ2 ⊢ M.[σ] `: A.
Proof.
  intros Hlook.
  induction 1 in Γ2, σ, Hlook |- *; asimpl; eauto 7.
Qed.

Local Hint Resolve judge_subst : core.

Lemma lookup_subst_cons Σ Δ A Γ N :
  Σ ;` Δ `; Γ ⊢ N `: A ->
  lookup_subst Σ Δ (A :: Γ) Γ (N .: ids).
Proof.
  unfold lookup_subst.
  intros HN [| x] B HxB; asimpl in *.
  - injection HxB as <-. assumption.
  - constructor. assumption.
Qed.

Local Hint Resolve lookup_subst_cons : core.

Lemma judge_subst_single Σ Δ M N Γ A B :
  Σ ;` Δ `; Γ ⊢ N `: A ->
  Σ ;` Δ `; A :: Γ ⊢ M `: B ->
  Σ ;` Δ `; Γ ⊢ M.[N/] `: B.
Proof.
  eauto.
Qed.

Lemma get_super_heap__typ (Σ Σ' : heap__typ) (l : nat) (A : typ) :
  Σ ⊆ Σ' -> Σ !! l = Some A -> Σ' !! l = Some A.
Proof.
  eauto using fin_maps.lookup_weaken.
Qed.
Local Hint Resolve get_super_heap__typ : core.

Lemma insert_super_heap__typ l A (Σ : heap__typ) :
  l ∉ dom Σ ->
  Σ ⊆ <[l:=A]> Σ.
Proof.
  rewrite not_elem_of_dom.
  apply insert_subseteq.
Qed.
Local Hint Resolve insert_super_heap__typ : core.

Lemma subst_super_heap__typ (Σ Σ' : heap__typ) σ :
  Σ ⊆ Σ' -> subst σ <$> Σ ⊆ subst σ <$> Σ'.
Proof.
  apply map_fmap_mono.
Qed.
Local Hint Resolve subst_super_heap__typ : core.

Lemma up_super_heap__typ Σ Σ' :
  Σ ⊆ Σ' -> up__heap Σ ⊆ up__heap Σ'.
Proof.
  rewrite /up__heap. auto.
Qed.
Local Hint Resolve up_super_heap__typ : core.

Lemma judge_super_heap__typ Σ Σ' Δ Γ M A :
  Σ ⊆ Σ' ->
  Σ ;` Δ `; Γ ⊢ M `: A ->
  Σ' ;` Δ `; Γ ⊢ M `: A.
Proof.
  intros HS Hjudge.
  induction Hjudge in Σ', HS |- *; eauto.
Qed.
Local Hint Resolve judge_super_heap__typ : core.

Lemma stupid_lemma Σ B :
  (λ C : typ, C.[B/]) <$> up__heap Σ = Σ.
Proof.
  apply map_eq.
  intro l.
  unfold up__heap.
  rewrite !lookup_fmap.
  destruct (Σ !! l) as [A |] eqn:HA; rewrite !HA; autosubst.
Qed.

Lemma heap_typing_dom h Σ :
  h `:: Σ ->
  dom Σ ⊆ dom h.
Proof.
  unfold "`::".
  rewrite elem_of_subseteq.
  setoid_rewrite elem_of_dom.
  intros H l [A (v & Hhlv & Hv)%H].
  eauto.
Qed.

Lemma fresh_dom_heap_typing h Σ :
  h `:: Σ ->
  fresh (dom h) ∉ dom Σ.
Proof.
  intros Hh H%(heap_typing_dom _ _ Hh)%is_fresh.
  contradiction.
Qed.
Local Hint Resolve fresh_dom_heap_typing : core.

Lemma heap_typing_extend h Σ (l : nat) (v : val) A :
  l = fresh (dom h) ->
  Σ ;` 0 `; [] ⊢ v `: A ->
  h `:: Σ ->
  <[l:=v]> h `:: <[l:=A]> Σ.
Proof.
  intros Hl Hv Hh l' B HB.
  destruct (decide (l = l')) as [<- | Hll'].
  - rewrite lookup_insert_eq in HB.
    injection HB as <-.
    exists v. rewrite lookup_insert_eq. subst l.
    split; eauto. 
  - rewrite lookup_insert_ne in HB.
    2:{ assumption. }
    unfold "`::" in Hh.
    specialize Hh with (1:=HB) as Hh'.
    destruct Hh' as (v' & Hlv' & Hv').
    exists v'. rewrite lookup_insert_ne.
    2:{ assumption. }
    subst l. eauto.
Qed.
Local Hint Resolve heap_typing_extend : core.

Lemma heap_typing_insert h Σ (l : nat) (v : val) A :
  Σ !! l = Some A ->
  Σ ;` 0 `; [] ⊢ v `: A ->
  h `:: Σ ->
  <[l:=v]> h `:: Σ.
Proof.
  intros HlA HvA Hh l' B.
  destruct (decide (l = l')) as [<- | Hll'].
  - rewrite HlA. intros [= <-].
    setoid_rewrite lookup_insert_eq. eauto.
  - intros (v' & Hlv' & Hv')%Hh.
    setoid_rewrite lookup_insert_ne; eauto.
Qed.
Local Hint Resolve heap_typing_insert : core.

Lemma pres__b Σ M M' A h h' :
  h ,^ M ~> h' ^, M' ->
  h `:: Σ ->
  Σ ;` 0 `; [] ⊢ M `: A ->
  exists Σ', Σ ⊆ Σ' /\ h' `:: Σ' /\ Σ' ;` 0 `; [] ⊢ M' `: A.
Proof.
  inversion 1; subst; intro Hh.
  - intros (B & (C & D & [= <- <-] & HB & HM)%inv_judge_abs & Hn)%inv_judge_app.
    specialize judge_subst_single with (1:=Hn) (2:=HM) as Hyp.
    eauto.
  - intros (B & C & -> & HB & (D & [= <-] & HM)%inv_judge_tabs)%inv_judge_tapp.
    specialize judge_tsubst_single with (1:=HB) (2:=HM) as IH.
    cbn in IH. rewrite stupid_lemma in IH. eauto.
  - intros (HA & B & (C & D & [= <-] & HC & Hv)%inv_judge_pack & HN)%inv_judge_unpack.
    specialize judge_tsubst_single with (1:=HC) (2:=HN) as HTS.
    cbn in HTS. rewrite stupid_lemma in HTS. asimpl in HTS.
    specialize judge_subst_single with (1:=Hv) (2:=HTS) as HJSS.
    eauto.
  - intros [-> HaB]%inv_judge_uop. eauto.
  - intros (-> & Ha1 & Ha2)%inv_judge_bop. eauto.
  - intros (B & C & -> & (? & ? & [= <- <-] & Hm & Hn)%inv_judge_duo)%inv_judge_prj.
    destruct b; eauto.
  - intros (Hb & HM & HN)%inv_judge_cond.
    destruct b; eauto.
  - intros (B & Hv & HN)%inv_judge_letin.
    specialize judge_subst_single with (1:=Hv) (2:=HN) as HSS. eauto.
  - intros (B & C & (? & ? & [= <- <-] & HCB & Hv)%inv_judge_inlr & HM & HN)%inv_judge_mtch.
    destruct b.
    + specialize judge_subst_single with (1:=Hv) (2:=HM) as HSS. eauto.
    + specialize judge_subst_single with (1:=Hv) (2:=HN) as HSS. eauto.
  - intros (B & -> & Hv)%inv_judge_new.
    exists (<[fresh (dom h) := B]> Σ).
    repeat split; auto.
    constructor. apply lookup_insert_eq.
  - intros (B & [= <-] & Hl)%inv_judge_deref%inv_judge_loc. eauto.
  - intros [(B & [= <-] & Hl)%inv_judge_loc Hv]%inv_judge_store. eauto.
Qed.

Definition ktx_typing (Σ : heap__typ) (K : ktx) (A B : typ) : Prop :=
  forall M Σ', Σ ⊆ Σ' -> Σ' ;` 0 `; [] ⊢ M `: A -> Σ' ;` 0 `; [] ⊢ K [[M]] `: B.

Notation "Σ '⊢k' K '`:' A '`=>' B" := (ktx_typing Σ%list K A%typ B%typ) (at level 80, no associativity) : type_scope.

Lemma decomp__k Σ K M B :
  Σ ;` 0 `; [] ⊢ K [[ M ]] `: B ->
  exists A, Σ ;` 0 `; [] ⊢ M `: A /\ Σ ⊢k K `: A `=> B.
Proof.
  unfold ktx_typing.
  induction K in Σ, M, B |- *; cbn.
  - intros HM. exists B. split; auto.
  - intros (C & (A & HM & HK)%IHK & Hv)%inv_judge_app.
    eexists; split; eauto.
  - intros (C & HN & (A & HM & HK)%IHK)%inv_judge_app.
    eexists; split; eauto.
  - intros (C & D & -> & HC & (A & HM & HK)%IHK)%inv_judge_tapp.
    eexists; split; eauto.
  - intros (C & D & -> & HC & (A & HM & HK)%IHK)%inv_judge_pack.
    eexists; split; eauto.
  - intros (HB & C & (A & HM & HK)%IHK & HN)%inv_judge_unpack.
    eexists; split; eauto.
  - intros [-> (A & HM & HK)%IHK]%inv_judge_uop.
    eexists; split; eauto.
  - intros (-> & (C & HM & HK)%IHK & Hv)%inv_judge_bop.
    eexists; split; eauto.
  - intros (-> & HN & (C & HM & HK)%IHK)%inv_judge_bop.
    eexists; split; eauto.
  - intros (C & D & -> & (A & HM & HK)%IHK & Hv)%inv_judge_duo.
    eexists; split; eauto.
  - intros (C & D & -> & HN & (A & HM & HK)%IHK)%inv_judge_duo.
    eexists; split; eauto.
  - intros (C & D & -> & (A & HM & HK)%IHK)%inv_judge_prj.
    eexists; eauto.
  - intros ((A & HM & HK)%IHK & HN1 & HN2)%inv_judge_cond.
    eexists; split; eauto.
  - intros (C & (A & HM & HK)%IHK & HN)%inv_judge_letin.
    eexists; split; eauto.
  - intros (C & D & -> & HCD & (A & HM & HK)%IHK)%inv_judge_inlr.
    eexists; split; eauto.
  - intros (C & D & (A & HM & HK)%IHK & HN1 & HN2)%inv_judge_mtch.
    eexists; split; eauto.
  - intros (C & -> & (A & HM & HK)%IHK)%inv_judge_new.
    eexists; split; eauto.
  - intros (A & HM & HK)%inv_judge_deref%IHK.
    eexists; split; eauto.
  - intros ((A & HM & HK)%IHK & HN)%inv_judge_store.
    eexists; split; eauto.
  - intros (HN & (A & HM & HK)%IHK)%inv_judge_store.
    eexists; split; eauto.
Qed.

Lemma composition__k Σ Σ' K M A B :
  Σ ⊢k K `: A `=> B -> Σ ⊆ Σ' -> Σ' ;` 0 `; [] ⊢ M `: A -> Σ' ;` 0 `; [] ⊢ K [[ M ]] `: B.
Proof.
  unfold ktx_typing. eauto.
Qed.

Lemma pres Σ M M' A h h' :
  h ,` M ~> h' `, M' ->
  h `:: Σ ->
  Σ ;` 0 `; [] ⊢ M `: A ->
  exists Σ', Σ ⊆ Σ' /\ h' `:: Σ' /\ Σ' ;` 0 `; [] ⊢ M' `: A.
Proof.
  intros (N & N' & K & -> & -> & HNN')%inv_step Hh (B & HNB & HK)%decomp__k.
  specialize pres__b with (1:=HNN') (2:=Hh) (3:=HNB) as (Σ' & HΣ' & Hh' & HN'B).  
  specialize composition__k with (1:=HK) (2:=HΣ') (3:=HN'B) as HKN'A. eauto.
Qed.

Definition steps (h : heap) (M : trm) (h' : heap) (M' : trm) : Prop :=
  rtc (fun '(h, M) '(h', M') => h ,` M ~> h' `, M') (h, M) (h', M').

Notation "h ',*' M '~>' h' '*,' M'" := (steps h M h' M') (at level 80, no associativity) : type_scope.

Definition safe (h : heap) (M : trm) : Prop :=
  forall h' M', h ,* M ~> h' *, M' -> progressive h' M'.

Lemma inv_steps h1 h3 M1 M3 :
  h1 ,* M1 ~> h3 *, M3 ->
  (h3 = h1 /\ M3 = M1) \/ (exists h2 M2, h1 ,` M1 ~> h2 `, M2 /\ h2 ,* M2 ~> h3 *, M3 ).
Proof.
  inversion 1; subst; auto.
  destruct y as [h2 M2]. eauto.
Qed.

Section steps_ind.
  Variable R : heap -> trm -> heap -> trm -> Prop.

  Hypothesis steps_refl : forall h M, R h M h M.

  Hypothesis steps_rtcl : forall h1 h2 h3 M1 M2 M3,
      h1 ,` M1 ~> h2 `, M2 -> h2 ,* M2 ~> h3 *, M3 -> R h2 M2 h3 M3 -> R h1 M1 h3 M3.

  Lemma steps_ind h M h' M' : h ,* M ~> h' *, M' -> R h M h' M'.
  Proof.
    unfold steps in *.
    remember (h, M) as hM eqn:HhM.
    remember (h', M') as hM' eqn:HhM'.
    induction 1 in h, h', M, M', HhM, HhM' |- *; subst.
    - injection HhM' as <- <-. apply steps_refl.
    - destruct y as [h'' M''].
      eauto.
  Defined.
End steps_ind.

Lemma steps_refl h M :
  h ,* M ~> h *, M.
Proof.
  unfold steps. constructor.
Qed.

Lemma steps_step_l h1 h2 h3 M1 M2 M3 :
  h1 ,` M1 ~> h2 `, M2 -> h2 ,* M2 ~> h3 *, M3 -> h1 ,* M1 ~> h3 *, M3.
Proof.
  intros H1.
  apply rtc_l. assumption.
Qed.

Lemma steps_step_r h1 h2 h3 M1 M2 M3 :
  h1 ,* M1 ~> h2 *, M2 -> h2 ,` M2 ~> h3 `, M3 -> h1 ,* M1 ~> h3 *, M3.
Proof.
  intros H1 H2.
  eapply rtc_r; eauto.
Qed.

Lemma steps_trans h1 h2 h3 M1 M2 M3 :
  h1 ,* M1 ~> h2 *, M2 -> h2 ,* M2 ~> h3 *, M3 -> h1 ,* M1 ~> h3 *, M3.
Proof.
  unfold steps.
  transitivity (h2, M2); auto.
Qed.

Lemma step_steps h h' M M' :
  h,` M ~> h' `, M' ->
  h,* M ~> h' *, M'.
Proof.
  intro HM.
  apply rtc_once. assumption.
Qed.

Lemma empty_heap_typing h : h `:: ∅.
Proof.
  intros l A.
  rewrite lookup_empty.
  discriminate.
Qed.

Theorem safety M A h :
  ∅ ;` 0 `; [] ⊢ M `: A -> safe h M.
Proof.
  unfold safe.
  intros HMA h' M' Hss.
  specialize empty_heap_typing with h as Hh.
  remember ∅ as Σ eqn:HΣ. clear HΣ.
  induction Hss using steps_ind in Σ, A, Hh, HMA |- *.
  - eauto using progress_trm.
  - specialize pres with (1:=H) (2:=Hh) (3:=HMA) as (Σ' & HΣ' & Hh2 & HM2).
    specialize IHHss with (1:=HM2) (2:=Hh2). assumption.
Qed.

(** Fist order types. *)
Inductive typ__fo : Set :=
| Base__fo (B : prim)
| Prod__fo (A B : typ__fo)
| Sum__fo (A B : typ__fo).
  
Equations Derive NoConfusion NoConfusionHom Subterm EqDec for typ__fo.

Declare Scope typ__fo_scope.
Delimit Scope typ__fo_scope with typ__fo.
Bind Scope typ__fo_scope with typ__fo.

Coercion Base__fo : prim >-> typ__fo.
Infix "`×" :=
  Prod__fo
    (at level 100, right associativity)
    : typ__fo_scope.
Infix "⊕" :=
  Sum__fo
    (at level 100, right associativity)
    : typ__fo_scope.

Reserved Notation "Γ '⊢fo' M '`:' a" (at level 80, no associativity).

Inductive judge__fo (Γ : list typ__fo) : trm -> typ__fo -> Prop :=
| judge_ident__fo (x : var) a :
  Γ !! x = Some a ->
  Γ ⊢fo x `: a
| judge_base__fo (B : prim) (a : atom B) :
  Γ ⊢fo a `: B
| judge_uop__fo (B : prim) (op : una B) M :
  Γ ⊢fo M `: B ->
  Γ ⊢fo `< op >` M `: B
| judge_bop__fo (A B : prim) (op : bin A B) M N :
  Γ ⊢fo M `: A ->
  Γ ⊢fo N `: A ->
  Γ ⊢fo M <` op `> N `: B
| judge_cond__fo L M N A :
  Γ ⊢fo L `: Bool ->
  Γ ⊢fo M `: A ->
  Γ ⊢fo N `: A ->
  Γ ⊢fo if, L then, M else, N `: A
| judge_letin__fo M N A B :
  Γ ⊢fo M `: A ->
  A :: Γ ⊢fo N `: B ->
  Γ ⊢fo let, M in N `: B
| judge_duo__fo M N A B :
  Γ ⊢fo M `: A ->
  Γ ⊢fo N `: B ->
  Γ ⊢fo `(M, N)` `: (A `× B)
| judge_prj__fo b P A B :
  Γ ⊢fo P `: (A `× B) ->
  Γ ⊢fo prj b P `: if b then A else B
| judge_inlr__fo (b : bool) M A B :
  Γ ⊢fo M `: (if b then A else B) ->
  Γ ⊢fo inlr b M `: (A ⊕ B)
| judge_mtch__fo L M N A B C :
  Γ ⊢fo L `: (A ⊕ B) ->
  A :: Γ ⊢fo M `: C ->
  B :: Γ ⊢fo N `: C ->
  Γ ⊢fo mtch L M N `: C
where "Γ '⊢fo' M '`:' a" := (judge__fo Γ M a) : type_scope.

Inductive typ__baby :=
(* Minmal System F types. *)
| Ident__baby (X : var)
| Fun__baby (A B : typ__baby)
| Uni__baby (A : {bind 1 of typ__baby})
(* Existentials. *)
| Exi__baby (A : {bind 1 of typ__baby})
(* Simple types *)
| Base__baby (A : prim)
| Prod__baby (A B : typ__baby)
| Sum__baby (A B : typ__baby)
(* References limited to first order types. *)
| Ref__baby (A : typ__fo)
.

Equations Derive NoConfusion NoConfusionHom Subterm EqDec for typ__baby.

#[export] Instance Ids_typ__baby : Ids typ__baby. derive. Defined.
#[export] Instance Rename_typ__baby : Rename typ__baby. derive. Defined.
#[export] Instance Subst_typ__baby : Subst typ__baby. derive. Defined.

#[export] Instance SubstLemmas_typ__baby : SubstLemmas typ__baby. derive. Qed.

Declare Scope typ__baby_scope.
Delimit Scope typ__baby_scope with typ__baby.
Bind Scope typ__baby_scope with typ__baby.

Coercion Ident__baby : var >-> typ__baby.
Coercion Base__baby : prim >-> typ__baby.
Infix "`->" :=
  Fun__baby
    (at level 100, right associativity)
    : typ__baby_scope.
Notation "'forall,' A" :=
  (Uni__baby A%typ__baby)
    (at level 100, A at level 200)
    : typ__baby_scope.
Notation "'exists,' A" :=
  (Exi__baby A%typ__baby)
    (at level 100, A at level 200)
    : typ__baby_scope.
Infix "`×" :=
  Prod__baby
    (at level 100, right associativity)
    : typ__baby_scope.
Infix "⊕" :=
  Sum__baby
    (at level 100, right associativity)
    : typ__baby_scope.

Fixpoint inj__fo (A : typ__fo) : typ__baby :=
  match A with
  | Base__fo B => B
  | (A `× B)%typ__fo => inj__fo A `× inj__fo B
  | (A ⊕ B)%typ__fo => inj__fo A ⊕ inj__fo B
  end.

Definition is_typ__fo (A : typ__baby) : Prop :=
  exists F, A = inj__fo F.

Lemma Base_is_typ__fo (B : prim) :
  is_typ__fo B.
Proof.
  exists B. reflexivity.
Qed.

Lemma Prod_is_typ__fo (A B : typ__baby) :
  is_typ__fo A -> is_typ__fo B ->
  is_typ__fo (A `× B).
Proof.
  intros [a ->] [b ->].
  exists (a `× b)%typ__fo. reflexivity.
Qed.

Lemma Sum_is_typ__fo (A B : typ__baby) :
  is_typ__fo A -> is_typ__fo B ->
  is_typ__fo (A ⊕ B).
Proof.
  intros [a ->] [b ->].
  exists (a ⊕ b)%typ__fo. reflexivity.
Qed.

Lemma Ident_is_not_fo (α : var) :
  ~ is_typ__fo α.
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Fun_is_not_fo A B :
  ~ is_typ__fo (A `-> B).
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Uni_is_not_fo (A : typ__baby) :
  ~ is_typ__fo (forall, A)%typ__baby.
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Exi_is_not_typ__fo A :
  ~ is_typ__fo (exists, A).
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Ref_is_not_fo A :
  ~ is_typ__fo (Ref__baby A).
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Base_inj__fo (B : prim) F :
  Base__baby B = inj__fo F -> F = B.
Proof.
  destruct F; discriminate || intros [= <-]. reflexivity.
Qed.

Lemma Prod_inj__fo A B F :
  (A `× B)%typ__baby = inj__fo F -> exists F1 F2, F = (F1 `× F2)%typ__fo /\ A = inj__fo F1 /\ B = inj__fo F2.
Proof.
  destruct F; discriminate || intros [= -> ->]. eauto.
Qed.

Lemma Sum_inj__fo A B F :
  (A ⊕ B)%typ__baby = inj__fo F -> exists F1 F2, F = (F1 ⊕ F2)%typ__fo /\ A = inj__fo F1 /\ B = inj__fo F2.
Proof.
  destruct F; discriminate || intros [= -> ->]. eauto.
Qed.

Lemma Ident_not_inj__fo α F :
  Ident__baby α <> inj__fo F.
Proof.
  destruct F; discriminate.
Qed.

Lemma Fun_not_inj__fo A B F :
  (A `-> B)%typ__baby <> inj__fo F.
Proof.
  destruct F; discriminate.
Qed.

Lemma Uni_not_inj__fo A F :
  (forall, A)%typ__baby <> inj__fo F.
Proof.
  destruct F; discriminate.
Qed.

Lemma Exi_not_inj__fo A F :
  (exists, A)%typ__baby <> inj__fo F.
Proof.
  destruct F; discriminate.
Qed.

Lemma Ref_not_inj__fo A F :
  Ref__baby A <> inj__fo F.
Proof.
  destruct F; discriminate.
Qed.

Ltac elim_inj__fo :=
  lazymatch goal with
  | H: Base__baby _ = inj__fo _ |- _ =>
      apply Base_inj__fo in H as ->
  | H: inj__fo _ = Base__baby _ |- _ =>
      symmetry in H; apply Base_inj__fo  in H as ->
  | H: (_ `× _)%typ__baby = inj__fo _ |- _ =>
      apply Prod_inj__fo in H as (? & ? & -> & -> & ->)
  | H: inj__fo _ = (_ `× _)%typ__baby |- _ =>
      symmetry in H; apply Prod_inj__fo in H as (? & ? & -> & -> & ->)
  | H: (_ ⊕ _)%typ__baby = inj__fo _ |- _ =>
      apply Sum_inj__fo in H as (? & ? & -> & -> & ->)
  | H: inj__fo _ = (_ ⊕ _)%typ__baby |- _ =>
      symmetry in H; apply Sum_inj__fo in H as (? & ? & -> & -> & ->)
  | H: Ident__baby _ = inj__fo _ |- _ =>
      apply Ident_not_inj__fo in H; contradiction
  | H: inj__fo _ = Ident__baby _ |- _ =>
      symmetry in H; apply Ident_not_inj__fo in H; contradiction
  | H: Ref__baby _ = inj__fo _ |- _ =>
      apply Ref_not_inj__fo in H; contradiction
  | H: inj__fo _ = Ref__baby _ |- _ =>
      symmetry in H; apply Ref_not_inj__fo in H; contradiction
  | H: (_ `-> _)%typ__baby = inj__fo _ |- _ =>
      apply Fun_not_inj__fo in H; contradiction
  | H: inj__fo _ = (_ `-> _)%typ__baby |- _ =>
      symmetry in H; apply Fun_not_inj__fo in H; contradiction
  | H: (forall, _)%typ__baby = inj__fo _ |- _ =>
      apply Uni_not_inj__fo in H; contradiction
  | H: inj__fo _ = (forall, _)%typ__baby |- _ =>
      symmetry in H; apply Uni_not_inj__fo in H; contradiction
  | H: (exists, _)%typ__baby = inj__fo _ |- _ =>
      apply Exi_not_inj__fo in H; contradiction
  | H: inj__fo _ = (exists, _)%typ__baby |- _ =>
      symmetry in H; apply Exi_not_inj__fo in H; contradiction
  end.

Fixpoint inj__fo_typ (A : typ__fo) : typ :=
  match A with
  | Base__fo B => B
  | (A `× B)%typ__fo => inj__fo_typ A `× inj__fo_typ B
  | (A ⊕ B)%typ__fo => inj__fo_typ A ⊕ inj__fo_typ B
  end.

Definition is_typ__fo_typ (A : typ) : Prop :=
  exists F, A = inj__fo_typ F.

Lemma Base_is_typ__fo_typ (B : prim) :
  is_typ__fo_typ B.
Proof.
  exists B. reflexivity.
Qed.

Lemma Prod_is_typ__fo_typ (A B : typ) :
  is_typ__fo_typ A -> is_typ__fo_typ B ->
  is_typ__fo_typ (A `× B).
Proof.
  intros [a ->] [b ->].
  exists (a `× b)%typ__fo. reflexivity.
Qed.

Lemma Sum_is_typ__fo_typ (A B : typ) :
  is_typ__fo_typ A -> is_typ__fo_typ B ->
  is_typ__fo_typ (A ⊕ B).
Proof.
  intros [a ->] [b ->].
  exists (a ⊕ b)%typ__fo. reflexivity.
Qed.

Lemma Ident_is_not_fo_typ (α : var) :
  ~ is_typ__fo_typ α.
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Fun_is_not_fo_typ A B :
  ~ is_typ__fo_typ (A `-> B).
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Uni_is_not_fo_typ (A : typ) :
  ~ is_typ__fo_typ (forall, A)%typ.
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Exi_is_not_typ__fo_typ A :
  ~ is_typ__fo_typ (exists, A).
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Ref_is_not_fo_typ A :
  ~ is_typ__fo_typ (Ref A).
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Base_inj__fo_typ (B : prim) F :
  Base B = inj__fo_typ F -> F = B.
Proof.
  destruct F; discriminate || intros [= <-]. reflexivity.
Qed.

Lemma Prod_inj__fo_typ A B F :
  (A `× B)%typ = inj__fo_typ F ->
  exists F1 F2, F = (F1 `× F2)%typ__fo /\ A = inj__fo_typ F1 /\ B = inj__fo_typ F2.
Proof.
  destruct F; discriminate || intros [= -> ->]. eauto.
Qed.

Lemma Sum_inj__fo_typ A B F :
  (A ⊕ B)%typ = inj__fo_typ F ->
  exists F1 F2, F = (F1 ⊕ F2)%typ__fo /\ A = inj__fo_typ F1 /\ B = inj__fo_typ F2.
Proof.
  destruct F; discriminate || intros [= -> ->]. eauto.
Qed.

Lemma Ident_not_inj__fo_typ α F :
  Ident α <> inj__fo_typ F.
Proof.
  destruct F; discriminate.
Qed.

Lemma Fun_not_inj__fo_typ A B F :
  (A `-> B)%typ <> inj__fo_typ F.
Proof.
  destruct F; discriminate.
Qed.

Lemma Uni_not_inj__fo_typ A F :
  (forall, A)%typ <> inj__fo_typ F.
Proof.
  destruct F; discriminate.
Qed.

Lemma Exi_not_inj__fo_typ A F :
  (exists, A)%typ <> inj__fo_typ F.
Proof.
  destruct F; discriminate.
Qed.

Lemma Ref_not_inj__fo_typ A F :
  Ref A <> inj__fo_typ F.
Proof.
  destruct F; discriminate.
Qed.

Ltac elim_inj__fo_typ :=
  lazymatch goal with
  | H: Base _ = inj__fo_typ _ |- _ =>
      apply Base_inj__fo_typ in H as ->
  | H: inj__fo_typ _ = Base _ |- _ =>
      symmetry in H; apply Base_inj__fo_typ  in H as ->
  | H: (_ `× _)%typ = inj__fo_typ _ |- _ =>
      apply Prod_inj__fo_typ in H as (? & ? & -> & -> & ->)
  | H: inj__fo_typ _ = (_ `× _)%typ |- _ =>
      symmetry in H; apply Prod_inj__fo_typ in H as (? & ? & -> & -> & ->)
  | H: (_ ⊕ _)%typ = inj__fo_typ _ |- _ =>
      apply Sum_inj__fo_typ in H as (? & ? & -> & -> & ->)
  | H: inj__fo_typ _ = (_ ⊕ _)%typ |- _ =>
      symmetry in H; apply Sum_inj__fo_typ in H as (? & ? & -> & -> & ->)
  | H: Ident _ = inj__fo_typ _ |- _ =>
      apply Ident_not_inj__fo_typ in H; contradiction
  | H: inj__fo_typ _ = Ident _ |- _ =>
      symmetry in H; apply Ident_not_inj__fo_typ in H; contradiction
  | H: Ref _ = inj__fo_typ _ |- _ =>
      apply Ref_not_inj__fo_typ in H; contradiction
  | H: inj__fo_typ _ = Ref _ |- _ =>
      symmetry in H; apply Ref_not_inj__fo_typ in H; contradiction
  | H: (_ `-> _)%typ = inj__fo_typ _ |- _ =>
      apply Fun_not_inj__fo_typ in H; contradiction
  | H: inj__fo_typ _ = (_ `-> _)%typ |- _ =>
      symmetry in H; apply Fun_not_inj__fo_typ in H; contradiction
  | H: (forall, _)%typ = inj__fo_typ _ |- _ =>
      apply Uni_not_inj__fo_typ in H; contradiction
  | H: inj__fo_typ _ = (forall, _)%typ |- _ =>
      symmetry in H; apply Uni_not_inj__fo_typ in H; contradiction
  | H: (exists, _)%typ = inj__fo_typ _ |- _ =>
      apply Exi_not_inj__fo_typ in H; contradiction
  | H: inj__fo_typ _ = (exists, _)%typ |- _ =>
      symmetry in H; apply Exi_not_inj__fo_typ in H; contradiction
  end.

(* Coercion inj__fo_typ : typ__fo >-> typ. *)
Coercion inj__fo : typ__fo >-> typ__baby.

Fixpoint inj__baby (A : typ__baby) : typ :=
  match A with
  | Ident__baby α => Ident α
  | (A `-> B)%typ__baby => inj__baby A `-> inj__baby B
  | (forall, A)%typ__baby => forall, inj__baby A
  | (exists, A)%typ__baby => exists, inj__baby A
  | Base__baby B => B
  | (A `× B)%typ__baby => inj__baby A `× inj__baby B
  | (A ⊕ B)%typ__baby => inj__baby A ⊕ inj__baby B
  | Ref__baby a => Ref $ inj__fo_typ a
  end.

Lemma fo_baby_typ (a : typ__fo) :
  inj__fo_typ a = inj__baby (inj__fo a).
Proof.
  induction a; cbn; f_equal; auto.
Qed.

Lemma Base_inj__baby (B : prim) F :
  Base B = inj__baby F -> F = B.
Proof.
  destruct F; discriminate || intros [= <-]. reflexivity.
Qed.

Lemma Prod_inj__baby A B F :
  (A `× B)%typ = inj__baby F -> exists F1 F2, F = (F1 `× F2)%typ__baby /\ A = inj__baby F1 /\ B = inj__baby F2.
Proof.
  destruct F; discriminate || intros [= -> ->]. eauto.
Qed.

Lemma Sum_inj__baby A B F :
  (A ⊕ B)%typ = inj__baby F -> exists F1 F2, F = (F1 ⊕ F2)%typ__baby /\ A = inj__baby F1 /\ B = inj__baby F2.
Proof.
  destruct F; discriminate || intros [= -> ->]. eauto.
Qed.

Lemma Ident_inj__baby α F :
  Ident α = inj__baby F -> F = α.
Proof.
  destruct F; discriminate || intros [= ->]. reflexivity.
Qed.

Lemma Fun_inj__baby A B F :
  (A `-> B)%typ = inj__baby F -> exists F1 F2, F = (F1 `-> F2)%typ__baby /\ A = inj__baby F1 /\ B = inj__baby F2.
Proof.
  destruct F; discriminate || intros [= -> ->]. eauto.
Qed.

Lemma Uni_inj__baby A F :
  (forall, A)%typ = inj__baby F -> exists B, F = (forall, B)%typ__baby /\ A = inj__baby B.
Proof.
  destruct F; discriminate || intros [= ->]; eauto.
Qed.

Lemma Exi_inj__baby A F :
  (exists, A)%typ = inj__baby F -> exists B, F = (exists, B)%typ__baby /\ A = inj__baby B.
Proof.
  destruct F; discriminate || intros [= ->]; eauto.
Qed.

Lemma Ref_inj__baby A F :
  Ref A = inj__baby F -> exists a, F = Ref__baby a /\ A = inj__fo_typ a.
Proof.
  destruct F; discriminate || intros [= ->]. eauto.
Qed.

Lemma inj_inj__fo_typ A B :
  inj__fo_typ A = inj__fo_typ B -> A = B.
Proof.
  induction A in B |- *; destruct B; cbn;
    inversion 1; subst; f_equal; eauto.
Qed.

Lemma inj_inj__baby A B :
  inj__baby A = inj__baby B -> A = B.
Proof.
  induction A in B |- *; destruct B; cbn;
    inversion 1; subst; f_equal; eauto using inj_inj__fo_typ.
Qed.

Ltac elim_inj__baby :=
  lazymatch goal with
  | H: inj__baby _ = inj__baby _ |- _ =>
      apply inj_inj__baby in H as ->
  | H: Base _ = inj__baby _ |- _ =>
      apply Base_inj__baby in H as ->
  | H: inj__baby _ = Base _ |- _ =>
      symmetry in H; apply Base_inj__baby  in H as ->
  | H: (_ `× _)%typ = inj__baby _ |- _ =>
      apply Prod_inj__baby in H as (? & ? & -> & -> & ->)
  | H: inj__baby _ = (_ `× _)%typ |- _ =>
      symmetry in H; apply Prod_inj__baby in H as (? & ? & -> & -> & ->)
  | H: (_ ⊕ _)%typ = inj__baby _ |- _ =>
      apply Sum_inj__baby in H as (? & ? & -> & -> & ->)
  | H: inj__baby _ = (_ ⊕ _)%typ |- _ =>
      symmetry in H; apply Sum_inj__baby in H as (? & ? & -> & -> & ->)
  | H: Ident _ = inj__baby _ |- _ =>
      apply Ident_inj__baby in H as (? & -> & ->)
  | H: inj__baby _ = Ident _ |- _ =>
      symmetry in H; apply Ident_inj__baby in H as (? & -> & ->)
  | H: Ref _ = inj__baby _ |- _ =>
      apply Ref_inj__baby in H as (? & -> & ->)
  | H: inj _ = Ref__baby _ |- _ =>
      symmetry in H; apply Ref_inj__baby in H as (? & -> & ->)
  | H: (_ `-> _)%typ = inj__baby _ |- _ =>
      apply Fun_inj__baby in H as (? & ? & ? & -> & -> & ->)
  | H: inj__baby _ = (_ `-> _)%typ |- _ =>
      symmetry in H; apply Fun_inj__baby in H as (? & ? & ? & -> & -> & ->)
  | H: (forall, _)%typ = inj__baby _ |- _ =>
      apply Uni_inj__baby in H as (? & -> & ->)
  | H: inj__baby _ = (forall, _)%typ |- _ =>
      symmetry in H; apply Uni_inj__baby in H as (? & -> & ->)
  | H: (exists, _)%typ = inj__baby _ |- _ =>
      apply Exi_inj__baby in H as (? & -> & ->)
  | H: inj__baby _ = (exists, _)%typ |- _ =>
      symmetry in H; apply Exi_inj__baby in H as (? & -> & ->)
  end.

Reserved Infix "⊢wf_baby" (at level 80).

Inductive wf_typ__baby (Δ : nat) : typ__baby -> Prop :=
| wf_Ident__baby (X : var) :
  X < Δ ->
  Δ ⊢wf_baby X
| wf_Fun__baby A B :
  Δ ⊢wf_baby A ->
  Δ ⊢wf_baby B ->
  Δ ⊢wf_baby (A `-> B)
| wf_Uni__baby A :
  S Δ ⊢wf_baby A ->
  Δ ⊢wf_baby (forall, A)
| wf_Exi__baby A :
  S Δ ⊢wf_baby A ->
  Δ ⊢wf_baby (exists, A)
| wf_Base__baby (B : prim) :
  Δ ⊢wf_baby B
| wf_Prod__baby A B :
  Δ ⊢wf_baby A ->
  Δ ⊢wf_baby B ->
  Δ ⊢wf_baby (A `× B)
| wf_Sum__baby A B :
  Δ ⊢wf_baby A ->
  Δ ⊢wf_baby B ->
  Δ ⊢wf_baby (A ⊕ B)%typ__baby
| wf_Ref__baby a :
  Δ ⊢wf_baby Ref__baby a
where "Δ '⊢wf_baby' τ" := (wf_typ__baby Δ%nat τ%typ__baby) : type_scope.

Local Hint Constructors wf_typ__baby : core.

Definition up__baby (Γ : list typ__baby) : list typ__baby := subst (ren S) <$> Γ.

Reserved Notation "Δ '!;' Γ ⊢ M '`:' A" (at level 80, no associativity).

Inductive judge__baby (Δ : nat) (Γ : list typ__baby) : trm -> typ__baby -> Prop :=
| judge_ident__baby (x : var) A :
  Γ !! x = Some A ->
  Δ !; Γ ⊢ x `: A
| judge_abs__baby M A B :
  Δ ⊢wf_baby A ->
  Δ !; A :: Γ ⊢ M `: B ->
  Δ !; Γ ⊢ (fun, M) `: (A `-> B)%typ__baby
| judge_app__baby M N A B :
  Δ !; Γ ⊢ M `: (A `-> B)%typ__baby ->
  Δ !; Γ ⊢ N `: A ->
  Δ !; Γ ⊢ M N `: B
| judge_tabs__baby M A :
  S Δ !; up__baby Γ ⊢ M `: A ->
  Δ !; Γ ⊢ Λ M `: (forall, A)
| judge_tapp__baby M A B :
  Δ ⊢wf_baby A ->
  Δ !; Γ ⊢ M `: (forall, B) ->
  Δ !; Γ ⊢ M [-] `: B.[A/]
| judge_pack__baby M A B :
  Δ ⊢wf_baby A ->
  Δ !; Γ ⊢ M `: B.[A/] ->
  Δ !; Γ ⊢ pack M `: (exists, B)
| judge_unpack__baby M N A B :
  Δ ⊢wf_baby B ->
  Δ !; Γ ⊢ M `: (exists, A) ->
  S Δ !; A :: up__baby Γ ⊢ N `: B.[ren S] ->
  Δ !; Γ ⊢ unpack M N `: B
| judge_base__baby (B : prim) (a : atom B) :
  Δ !; Γ ⊢ a `: B
| judge_uop__baby (B : prim) (op : una B) M :
  Δ !; Γ ⊢ M `: B ->
  Δ !; Γ ⊢ `< op >` M `: B
| judge_bop__baby (A B : prim) (op : bin A B) M N :
  Δ !; Γ ⊢ M `: A ->
  Δ !; Γ ⊢ N `: A ->
  Δ !; Γ ⊢ M <` op `> N `: B
| judge_cond__baby L M N A :
  Δ !; Γ ⊢ L `: Bool ->
  Δ !; Γ ⊢ M `: A ->
  Δ !; Γ ⊢ N `: A ->
  Δ !; Γ ⊢ if, L then, M else, N `: A
| judge_letin__baby M N A B :
  Δ !; Γ ⊢ M `: A ->
  Δ !; A :: Γ ⊢ N `: B ->
  Δ !; Γ ⊢ let, M in N `: B
| judge_duo__baby M N A B :
  Δ !; Γ ⊢ M `: A ->
  Δ !; Γ ⊢ N `: B ->
  Δ !; Γ ⊢ `(M, N)` `: (A `× B)
| judge_prj__baby b P A B :
  Δ !; Γ ⊢ P `: (A `× B) ->
  Δ !; Γ ⊢ prj b P `: if b then A else B
| judge_inlr__baby (b : bool) M A B :
  Δ ⊢wf_baby (if b then B else A) ->
  Δ !; Γ ⊢ M `: (if b then A else B) ->
  Δ !; Γ ⊢ inlr b M `: (A ⊕ B)
| judge_mtch__baby L M N A B C :
  Δ !; Γ ⊢ L `: (A ⊕ B) ->
  Δ !; A :: Γ ⊢ M `: C ->
  Δ !; B :: Γ ⊢ N `: C ->
  Δ !; Γ ⊢ mtch L M N `: C
| judge_new__baby M (a : typ__fo) :
  Δ !; Γ ⊢ M `: a ->
  Δ !; Γ ⊢ new M `: Ref__baby a
| judge_deref__baby M (a : typ__fo) :
  Δ !; Γ ⊢ M `: Ref__baby a ->
  Δ !; Γ ⊢ !, M `: a
| judge_store__baby M N (a : typ__fo) :
  Δ !; Γ ⊢ M `: Ref__baby a ->
  Δ !; Γ ⊢ N `: a ->
  Δ !; Γ ⊢ M <- N `: a
where "Δ '!;' Γ ⊢ M '`:' A" := (judge__baby Δ%nat Γ%list M%trm A%typ__baby).

Local Hint Constructors judge__baby : core.

Coercion inj__baby : typ__baby >-> typ.

Lemma wf_typ__fo Δ (a : typ__fo) :
  Δ ⊢wf a.
Proof.
  induction a as [p | a1 IHa1 a2 IHa2 | a1 IHa1 a2 IHa2]
    in Δ |- *; cbn; constructor; auto.
Qed. 

Lemma wf_typ__baby_wf_typ Δ A :
  Δ ⊢wf_baby A -> Δ ⊢wf A.
Proof.
  induction 1; constructor; auto.
  rewrite fo_baby_typ. apply wf_typ__fo.
Qed.

Lemma wf_typ_wf_typ__baby Δ (A : typ__baby) :
  Δ ⊢wf A -> Δ ⊢wf_baby A.
Proof.
  Local Hint Constructors wf_typ__baby : core.
  induction A in Δ |- *; cbn; inversion 1; subst; auto.
Qed.

Lemma iff_wf_typ__baby Δ A :
  Δ ⊢wf_baby A <-> Δ ⊢wf A.
Proof.
  split; auto using wf_typ_wf_typ__baby, wf_typ__baby_wf_typ.
Qed.

Lemma subst_inj__fo (a : typ__fo) σ :
  (inj__fo a).[σ] = inj__fo a.
Proof.
  induction a; cbn; f_equal; auto.
Qed.

Lemma subst_inj__fo_typ (a : typ__fo) σ :
  (inj__fo_typ a).[σ] = inj__fo_typ a.
Proof.
  induction a; cbn; f_equal; auto.
Qed.

Lemma ren_inj__baby (A : typ__baby) ρ :
  inj__baby A.[ren ρ] = (inj__baby A).[ren ρ].
Proof.
  induction A in ρ |- *; cbn; f_equal; eauto.
  - rewrite !up_upren_internal; eauto.
  - rewrite !up_upren_internal; eauto.
  - rewrite subst_inj__fo_typ. reflexivity.
Qed.

Lemma fuck (σ1 σ2 : var -> typ) :
  (forall α, σ1 α = σ2 α) -> forall α, up σ1 α = up σ2 α.
Proof.
  intros H [| α]; asimpl; eauto.
  rewrite H. reflexivity.
Qed.

Lemma goddamn (A : typ) σ1 σ2 :
  (forall α, σ1 α = σ2 α) -> A.[σ1] = A.[σ2].
Proof.
  induction A in σ1, σ2 |- *; cbn; intros Hσ; f_equal; eauto using fuck.
Qed.

Lemma rew_up_inj__baby σ α :
  (up σ >>> inj__baby) α = up (σ >>> inj__baby) α.
Proof.
  destruct α as [| α]; asimpl.
  - reflexivity.
  - rewrite ren_inj__baby.
    autosubst.
Qed.

Lemma subst_inj__baby (A : typ__baby) σ :
  inj__baby A.[σ] = (inj__baby A).[σ >>> inj__baby].
Proof.
  induction A in σ |- *; cbn; f_equal; eauto.
  - rewrite IHA. apply goddamn, rew_up_inj__baby.
  - rewrite IHA. apply goddamn, rew_up_inj__baby.
  - rewrite subst_inj__fo_typ. reflexivity.
Qed.

Lemma up_inj__baby (Γ : list typ__baby) :
  up__typs (inj__baby <$> Γ) = inj__baby <$> (up__baby Γ).
Proof.
  apply list_eq. intro x.
  rewrite !list_lookup_fmap.
  destruct (Γ !! x) as [A |]; asimpl; f_equal.
  rewrite ren_inj__baby. reflexivity.
Qed.

Lemma single_subst_inj__baby (A B : typ__baby):
  inj__baby A.[B/] = (inj__baby A).[inj__baby B/].
Proof.
  rewrite subst_inj__baby. autosubst.
Qed.

Lemma judge__baby_judge Δ Γ M A :
  Δ !; Γ ⊢ M `: A ->
  ∅ ;` Δ `; inj__baby <$> Γ ⊢ M `: A.
Proof.
  Local Hint Resolve wf_typ__baby_wf_typ : core.
  induction 1; cbn in *; eauto.
  - constructor.
    rewrite list_lookup_fmap H. reflexivity.
  - rewrite <- up_inj__baby in IHjudge__baby.
    econstructor; eauto; unfold up__heap; eauto.
    fold inj__baby. Search (_ <$> ∅).
    rewrite fmap_empty. assumption.
  - rewrite single_subst_inj__baby. eauto.
  - apply judge_pack with (A:=inj__baby A); auto; fold inj__baby.
    rewrite <- single_subst_inj__baby. assumption.
  - econstructor; eauto; fold inj__baby.
    unfold up__heap. rewrite fmap_empty.
    rewrite up_inj__baby. rewrite <- ren_inj__baby. auto.
  - rewrite distr_if_booll. eauto.
  - constructor; fold inj__baby; eauto; rewrite <- distr_if_booll; auto.
  - constructor. rewrite fo_baby_typ. auto.
  - constructor. rewrite fo_baby_typ in IHjudge__baby. assumption.
  - rewrite fo_baby_typ in IHjudge__baby1. eauto.
Qed.

Lemma judge_judge__baby Δ (Γ : list typ__baby) M (A : typ__baby) :
  ∅ ;` Δ `; inj__baby <$> Γ ⊢ M `: A -> Δ !; Γ ⊢ M `: A.
Proof.
  Local Hint Resolve wf_typ_wf_typ__baby : core.
  Local Hint Constructors judge__baby : core.
  induction M in Δ, Γ, A |- *; inversion 1; subst; repeat elim_inj__baby; auto.
  - rewrite list_lookup_fmap in H1.
    destruct (Γ !! x) as [B |] eqn:HB; rewrite HB in H1;
      cbn in H1; inversion H1; subst; elim_inj__baby; auto.
  - apply Fun_inj__baby in H1 as (C & D & [= ->] & -> & ->). eauto.
  - econstructor; eauto.
    + apply IHM1.
Abort.

Lemma wf_typ__baby_rename Δ1 Δ2 A δ :
  wf_tren Δ1 Δ2 δ ->
  Δ1 ⊢wf_baby A ->
  Δ2 ⊢wf_baby A.[ren δ].
Proof.
  intros Htren.
  induction 1 in Δ2, Htren, δ |-*; asimpl; eauto.
Qed.

Local Hint Resolve wf_typ__baby_rename : core.

Lemma wf_typ__baby_S Δ B :
  Δ ⊢wf_baby B → S Δ ⊢wf_baby B.[ren S].
Proof.
  eauto.
Qed.

Lemma Forall_wf_typ__baby_S Δ Γ :
  Forall (wf_typ__baby Δ) Γ -> Forall (wf_typ__baby (S Δ)) (up__baby Γ).
Proof.
  unfold up__baby.
  rewrite Forall_fmap.
  apply List.Forall_impl. cbn.
  apply wf_typ__baby_S.
Qed.

Lemma wf_typ__baby_weaken Δ1 Δ2 A :
  Δ1 <= Δ2 -> Δ1 ⊢wf A -> Δ2 ⊢wf A.
Proof.
  intros H%wf_tren_le H1.
  replace A with A.[ren id] by by asimpl.
  eauto.
Qed.

Definition wf_tsubst__baby Δ1 Δ2 σ :=
  forall α, α < Δ1 -> Δ2 ⊢wf_baby σ α.

Lemma wf_tsubst__baby_S Δ :
  wf_tsubst__baby Δ (S Δ) (ren S).
Proof.
  unfold wf_tsubst__baby.
  intros X HX.
  constructor. lia.
Qed.

Local Hint Resolve wf_tsubst__baby_S : core.

Lemma wf_tsubst__baby_up σ Δ1 Δ2 :
  wf_tsubst__baby Δ1 Δ2 σ -> wf_tsubst__baby (S Δ1) (S Δ2) (up σ).
Proof.
  unfold wf_tsubst__baby.
  intros Hwftsubst [| α]; asimpl.
  - eauto with lia.
  - intros H%Arith_prebase.lt_S_n. eauto.
Qed.

Local Hint Resolve wf_tsubst__baby_up : core.

Lemma wf_tren_tsubst__baby Δ1 Δ2 (δ : var -> var) :
  wf_tren Δ1 Δ2 δ <-> wf_tsubst__baby Δ1 Δ2 (ren δ).
Proof.
  unfold wf_tren, wf_tsubst__baby. split.
  - intros Htren α HΔ1.
    specialize Htren with (1:=HΔ1).
    constructor. eauto.
  - intros Htsubst α HΔ1.
    specialize Htsubst with (1:=HΔ1).
    inversion Htsubst; subst.
    assumption.
Qed.

Lemma wf_tsubst__baby_single Δ A :
  Δ ⊢wf_baby A ->
  wf_tsubst__baby (S Δ) Δ (A .: ids).
Proof.
  intros Hwf [| α] Hα; asimpl; eauto.
  constructor. lia.
Qed.

Local Hint Resolve wf_tsubst__baby_single : core.

Lemma wf_tsubst_wf_typ__baby Δ1 Δ2 σ (A : typ__baby) :
  wf_tsubst__baby Δ1 Δ2 σ ->
  Δ1 ⊢wf_baby A ->
  Δ2 ⊢wf_baby A.[σ].
Proof.
  intros Hwftsub.
  induction 1 in Δ2, Hwftsub, σ |- *; asimpl; eauto.
Qed.

Local Hint Resolve wf_tsubst_wf_typ__baby : core.

Lemma up_subst__baby σ Γ :
  up__baby (subst σ <$> Γ) = subst (up σ) <$> up__baby Γ.
Proof.
  rewrite /up__baby.
  apply list_eq.
  intro x.
  rewrite !list_lookup_fmap.
  destruct (Γ !! x) as [A |] eqn:HA; asimpl; auto.
Qed.

Lemma judge_tsubst__baby Δ1 Δ2 Γ M A σ :
  wf_tsubst__baby Δ1 Δ2 σ ->
  Δ1 !; Γ ⊢ M `: A ->
  Δ2 !; (subst σ) <$> Γ ⊢ M `: A.[σ].
Proof.
  intros Hσ.
  induction 1 in Hσ, σ, Δ2 |- *; cbn; eauto 4.
  - constructor.
    rewrite list_lookup_fmap.
    apply fmap_Some_2. assumption.
  - constructor.
    rewrite up_subst__baby. eauto.
  - replace (B.[A/].[σ]) with (B.[up σ].[A.[σ]/])
      by by asimpl. eauto.
  - apply judge_pack__baby  with (A:= A.[σ]); eauto.
    replace (B.[up σ].[A.[ σ]/]) with (B.[A/].[σ])
      by by asimpl. eauto.
  - apply judge_unpack__baby with (A:=A.[up σ]); eauto.
    rewrite up_subst__baby.
    rename H into H'.
    replace (B.[σ].[ren S]) with (B.[ren S].[up σ])
      by by asimpl. eauto.
  - eauto.
  - rewrite distr_if_booll.
    eauto.
  - setoid_rewrite distr_if_booll in IHjudge__baby.
    constructor; eauto.
    destruct b; eauto.
  - econstructor; eauto.
  - setoid_rewrite subst_inj__fo in IHjudge__baby. eauto.
  - asimpl in IHjudge__baby.
    rewrite subst_inj__fo. eauto.
  - asimpl in IHjudge__baby1.
    setoid_rewrite subst_inj__fo in IHjudge__baby2.
    rewrite subst_inj__fo. eauto.
Qed.

Local Hint Resolve judge_tsubst__baby : core.

Lemma judge_tsubst__baby_single Δ Γ M A B :
  Δ ⊢wf_baby B ->
  S Δ !; Γ ⊢ M `: A ->
  Δ !; (fun C => C.[B/]) <$> Γ ⊢ M `: A.[ B /].
Proof.
  eauto.
Qed.

Local Hint Resolve judge_tsubst__baby_single : core.

Lemma lookup_ren_up__baby (Γ1 Γ2 : list typ__baby) δ :
  lookup_ren Γ1 Γ2 δ ->
  lookup_ren (up__baby Γ1) (up__baby Γ2) δ.
Proof.
  unfold lookup_ren, up__baby.
  intros Hlook x B HB.
  rewrite list_lookup_fmap in HB.
  rewrite list_lookup_fmap.
  apply fmap_Some in HB as (C & HxC & ->).
  specialize Hlook with (1:=HxC).
  rewrite Hlook. reflexivity.
Qed.

Local Hint Resolve lookup_ren_up__baby : core.

Lemma judge_rename__baby δ Δ Γ1 Γ2 M A :
  lookup_ren Γ1 Γ2 δ ->
  Δ !; Γ1 ⊢ M `: A ->
  Δ !; Γ2 ⊢ M.[ren δ] `: A.
Proof.
  intros Hlookup.
  induction 1 in Γ2, δ, Hlookup |- *; asimpl; eauto 7.
Qed.

Local Hint Resolve judge_rename__baby : core.

Lemma judge_rename__baby_single Δ Γ M A B :
  Δ !; Γ ⊢ M `: B ->
  Δ !; A :: Γ ⊢ M.[ren S] `: B.
Proof.
  intro HM.
  eapply judge_rename__baby; eauto.
Qed.

Local Hint Resolve judge_rename__baby_single : core.

Lemma lookup_ren_inv_up__baby Γ1 Γ2 δ :
  lookup_ren_inv Γ1 Γ2 δ ->
  lookup_ren_inv (up__baby Γ1) (up__baby Γ2) δ.
Proof.
  unfold lookup_ren_inv.
  intros Hlook x B HB.
  rewrite list_lookup_fmap in HB.
  rewrite list_lookup_fmap.
  apply fmap_Some in HB as (C & HxC & ->).
  specialize Hlook with (1:=HxC).
  rewrite Hlook. reflexivity.
Qed.

Lemma judge_rename__baby_inv δ Δ Γ1 Γ2 M A :
  lookup_ren_inv Γ1 Γ2 δ ->
  Δ !; Γ2 ⊢ M.[ren δ] `: A ->
  Δ !; Γ1 ⊢ M `: A.
Proof.
  induction M in δ, Δ, Γ1, Γ2, A |- *; intros Hlookup; asimpl; cbn;
    inversion 1; subst; eauto.
  - specialize lookup_ren_inv_upren with (A:=A0) (1:=Hlookup) as Hlook.
    specialize IHM with (1:=Hlook) as IH. eauto.
  - specialize lookup_ren_inv_up__baby with (1:=Hlookup) as Hlook. eauto.
  - econstructor; eauto.
    eauto using lookup_ren_inv_upren, lookup_ren_inv_up__baby.
  - eauto using lookup_ren_inv_upren.
  - econstructor; eauto using lookup_ren_inv_upren.
Qed.

Lemma judge_rename__baby_inv_single Δ Γ M A B :
  Δ !; A :: Γ ⊢ M.[ren S] `: B ->
  Δ !; Γ ⊢ M `: B.
Proof.
  eauto using lookup_ren_inv_S, judge_rename__baby_inv.
Qed.

Definition lookup_subst__baby Δ (Γ1 Γ2 : list typ__baby) (σ : var -> trm) :=
  forall x B, Γ1 !! x = Some B -> Δ !; Γ2 ⊢ σ x `: B.

Lemma lookup_subst__baby_up Δ A Γ1 Γ2 σ :
  lookup_subst__baby Δ Γ1 Γ2 σ ->
  lookup_subst__baby Δ (A :: Γ1) (A :: Γ2) (up σ).
Proof.
  unfold lookup_subst__baby.
  intros Hlook [| x] B HB; asimpl in *.
  - injection HB as <-. constructor.
    reflexivity.
  - specialize Hlook with (1:=HB). eauto.
Qed.

Local Hint Resolve lookup_subst__baby_up : core.

Lemma lookup_subst_up__baby Δ Γ1 Γ2 σ :
  lookup_subst__baby Δ Γ1 Γ2 σ ->
  lookup_subst__baby (S Δ) (up__baby Γ1) (up__baby Γ2) σ.
Proof.
  unfold lookup_subst__baby, up__baby.
  intros Hlook x B HB.
  rewrite list_lookup_fmap in HB.
  apply fmap_Some in HB as (A & HxA & ->).
  specialize Hlook with (1:=HxA).
  apply judge_tsubst__baby with (Δ1 := Δ); eauto.
Qed.

Local Hint Resolve lookup_subst_up__baby : core.

Lemma judge_subst__baby σ Δ M Γ1 Γ2 A :
  lookup_subst__baby Δ Γ1 Γ2 σ ->
  Δ !; Γ1 ⊢ M `: A ->
  Δ !; Γ2 ⊢ M.[σ] `: A.
Proof.
  intros Hlook.
  induction 1 in Γ2, σ, Hlook |- *; asimpl; eauto 7.
Qed.

Local Hint Resolve judge_subst__baby : core.

Lemma lookup_subst__baby_cons Δ A Γ N :
  Δ !; Γ ⊢ N `: A ->
  lookup_subst__baby Δ (A :: Γ) Γ (N .: ids).
Proof.
  unfold lookup_subst__baby.
  intros HN [| x] B HxB; asimpl in *.
  - injection HxB as <-. assumption.
  - constructor. assumption.
Qed.

Local Hint Resolve lookup_subst__baby_cons : core.

Lemma judge_subst__baby_single Δ M N Γ A B :
  Δ !; Γ ⊢ N `: A ->
  Δ !; A :: Γ ⊢ M `: B ->
  Δ !; Γ ⊢ M.[N/] `: B.
Proof.
  eauto.
Qed.

Reserved Notation "h ',+' M ↓ h' '+,' val" (at level 80, no associativity).

Inductive big (h : heap) : trm -> heap -> val -> Prop :=
| big_abs M :
  h ,+ (fun, M) ↓ h +, (fun, M)
| big_app h__N h__M h__L M N L n v :
  h ,+ N ↓ h__N +, n ->
  h__N ,+ M ↓ h__M +, (fun, L) ->
  h__M ,+ L.[inj__v n/] ↓ h__L +, v ->
  h ,+ M N ↓ h__L +, v
| big_tabs M :
  h ,+ Λ M ↓ h +, Λ M
| big_tapp h__M h__N (M N : trm) n :
  h ,+ M ↓ h__M +, (Λ N)%val ->
  h__M ,+ N ↓ h__N +, n ->
  h ,+ M [-] ↓ h__N +, n
| big_pack h' M m :
  h ,+ M ↓ h' +, m ->
  h ,+ pack M ↓ h' +, pack__v m
| big_unpack h__M h__N M N m n :
  h ,+ M ↓ h__M +, pack__v m ->
  h__M ,+ N.[inj__v m/] ↓ h__N +, n ->
  h ,+ unpack M N ↓ h__N +, n
| big_base (B : prim) (a : atom B) :
  h ,+ a ↓ h +, a
| big_uop h' (B : prim) (op : una B) M (a : atom B) :
  h ,+ M ↓ h' +, a ->
  h ,+ `< op >` M ↓ h' +, to_atom B (denote_una op (denote_atom a))
| big_bop h__M h__N (A B : prim) (op : bin A B) M N (m n : atom A) :
  h ,+ N ↓ h__N +, n ->
  h__N ,+ M ↓ h__M +, m ->
  h ,+ M <` op `> N ↓ h__M +, to_atom B (denote_bin op (denote_atom m) (denote_atom n))
| big_duo h__M h__N M N m n :
  h ,+ N ↓ h__N +, n ->
  h__N ,+ M ↓ h__M +, m ->
  h ,+ `(M, N)` ↓ h__M +, (`m, n`)
| big_prj h' b P u v :
  h ,+ P ↓ h' +, (`u,v`) ->
  h ,+ prj b P ↓ h' +, if b then u else v
| big_let h__M h__N M N m n :
  h ,+ M ↓ h__M +, m ->
  h__M ,+ N.[inj__v m/] ↓ h__N +, n ->
  h ,+ letin M N ↓ h__N +, n
| big_cond h' h'' L M N (b : bool) v :
  h ,+ L ↓ h' +, b ->
  h' ,+ (if b then M else N) ↓ h'' +, v ->
  h ,+ if, L then, M else, N ↓ h'' +, v
| big_inlr h' b M m :
  h ,+ M ↓ h' +, m ->
  h ,+ inlr b M ↓ h' +, inlr__v b m
| big_mtch h' h'' L M N b l v :
  h ,+ L ↓ h' +, inlr__v b l ->
  h' ,+ (if b then M.[inj__v l/] else N.[inj__v l/]) ↓ h'' +, v ->
  h ,+ mtch L M N ↓ h'' +, v
| big_loc l :
  h ,+ loc l ↓ h +, loc__v l
| big_new h' l M m :
  h ,+ M ↓ h' +, m ->
  l = fresh (dom h') ->
  h ,+ new M ↓ <[l:=m]> h' +, loc__v l
| big_deref h' M l v :
  h' !! l = Some v ->
  h ,+ M ↓ h' +, loc__v l ->
  h ,+ !, M ↓ h' +, v
| big_store h__M h__N M N l n :
  h ,+ N ↓ h__N +, n ->
  h__N ,+ M ↓ h__M +, loc__v l ->
  l ∈ dom h__M ->
  h ,+ M <- N ↓ <[l:=n]> h__M +, n
where "h ',+' M ↓ h' '+,' v" := (big h M%trm h' v%val).

Lemma big_uop_eq h h' (B : prim) (op : una B) M (a v : atom B) :
  v = to_atom B (denote_una op (denote_atom a)) ->
  h ,+ M ↓ h' +, a ->
  h ,+ `< op >` M ↓ h' +, v.
Proof.
  intros ->. apply big_uop.
Qed.
  
Lemma big_bop_eq h h__M h__N (A B : prim) (op : bin A B) M N (m n : atom A) (a : atom B) :
  a = to_atom B (denote_bin op (denote_atom m) (denote_atom n)) ->
  h ,+ N ↓ h__N +, n ->
  h__N ,+ M ↓ h__M +, m ->
  h ,+ M <` op `> N ↓ h__M +, a.
Proof.
  intros ->. apply big_bop.
Qed.

Section big_sound.
  Local Hint Resolve steps_refl : core.
  Local Hint Resolve steps_step_l : core.
  Local Hint Resolve steps_step_r : core.
  Local Hint Resolve step_steps : core.

  Lemma steps_app__r h h' (M N N' : trm) :
    h ,* N ~> h' *, N' ->
    h ,* M N ~> h' *, M N'.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_app__r : core.

  Lemma steps_app__l h h' (M M' : trm) (n : val) :
    h ,* M ~> h' *, M' ->
    h ,* M n ~> h' *, M' n.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_app__l : core.
  
  Lemma steps_app_abs h h__L h__M h__N L M N O (n: val) :
    h,* N ~> h__N *, n ->
    h__N,* M ~> h__M *, (fun, L)%val ->
    h__M,* L.[inj__v n/] ~> h__L *, O ->
    h,* M N ~> h__L *, O.
  Proof.
    intros HN HM HL.
    apply steps_trans with (h2:=h__M) (M2:=L.[inj__v n/]); auto.
    apply steps_step_r with (h2:=h__M) (M2:= (fun, L)%trm n); auto.
    apply steps_trans with (h2:=h__N) (M2:=M n); auto.
  Qed.
  Local Hint Resolve steps_app_abs : core.

  Lemma steps_tapp h h' M M' :
    h ,* M ~> h' *, M' ->
    h ,* (M [-])%trm ~> h' *, (M' [-])%trm.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_tapp : core.
  
  Lemma steps_tapp_tabs h h__M h__N M N N' :
    h,* M ~> h__M *, (Λ N)%val ->
    h__M,* N ~> h__N *, N' ->
    h,* M [-] ~> h__N *, N'.
  Proof.
    intros HM HN.
    apply steps_trans with (h2:=h__M) (M2:=N); auto.
    apply steps_step_r with (h2:=h__M) (M2:=((Λ N) [-])%trm); auto.
  Qed.
  Local Hint Resolve steps_tapp_tabs : core.

  Lemma steps_pack h h' M M' :
    h ,* M ~> h' *, M' ->
    h ,* pack M ~> h' *, pack M'.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_pack : core.

  Lemma steps_unpack h h' M M' N :
    h ,* M ~> h' *, M' ->
    h ,* unpack M N ~> h' *, unpack M' N.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_unpack : core.
  
  Lemma steps_unpack_pack h h__M h__N M N N' (v : val) :
    h,* M ~> h__M *, pack v ->
    h__M,* N.[inj__v v/] ~> h__N *, N' ->
    h,* unpack, M in N ~> h__N *, N'.
  Proof.
    intros HM HN.
    apply steps_trans with (h2:=h__M) (M2:=N.[inj__v v/]); auto.
    apply steps_step_r with (h2:=h__M) (M2:=unpack (pack v) N); auto.
  Qed.
  Local Hint Resolve steps_unpack_pack : core.

  Lemma steps_uop h h' B (op : una B) M M' :
    h,* M ~> h' *, M' ->
    h,* `< op >` M ~> h' *, `< op >` M'.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_uop : core.
  
  Lemma steps_una h h' B (op : una B) M (a : atom B):
    h,* M ~> h' *, a ->
    h,* `< op >` M ~> h' *, to_atom B (denote_una op (denote_atom a)).
  Proof.
    intros HM.
    apply steps_step_r with (h2:=h') (M2:=uop op a); auto.
  Qed.
  Local Hint Resolve steps_una : core.

  Lemma steps_bop__r h h' A B (op : bin A B) M N N' :
    h,* N ~> h' *, N' ->
    h,* (M <` op `> N)%trm ~> h' *, (M <` op `> N')%trm.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_bop__r : core.

  Lemma steps_bop__l h h' A B (op : bin A B) M M' (n : val) :
    h,* M ~> h' *, M' ->
    h ,* (M <` op `> n)%trm ~> h' *, (M' <` op `> n)%trm.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_bop__l : core.

  Lemma steps_bin h h__M h__N A B (op : bin A B) M N (m n : atom A) :
    h,* N ~> h__N *, n ->
    h__N,* M ~> h__M *, m ->
    h,* (M <` op `> N)%trm ~> h__M *, to_atom B (denote_bin op (denote_atom m) (denote_atom n)).
  Proof.
    intros HN HM.
    apply steps_step_r with (h2:=h__M) (M2:=bop op m n); auto.
    apply steps_trans with (h2:=h__N) (M2:=bop op M n); auto.
    specialize steps_bop__l with (op:=op) (n:=n) (1:=HM) as H.
    assumption.
  Qed.
  Local Hint Resolve steps_bin : core.

  Lemma steps_letin__l h h' M M' N :
    h ,* M ~> h' *, M' ->
    h ,* letin M N ~> h' *, letin M' N.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_letin__l : core.
  
  Lemma steps_letin h h__M h__N M N N' (m : val) :
    h ,* M ~> h__M *, m ->
    h__M ,* N.[inj__v m/] ~> h__N *, N' ->
    h ,* letin M N ~> h__N *, N'.
  Proof.
    intros HM HN.
    apply steps_trans with (h2:=h__M) (M2:=letin m N); auto.
    apply steps_step_l with (h2:=h__M) (M2:=N.[inj__v m/]); auto.
  Qed.
  Local Hint Resolve steps_letin : core.

  Lemma steps_cond__l h h' L L' M N :
    h,* L ~> h' *, L' ->
    h,* if, L then, M else, N ~> h' *, if, L' then, M else, N.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_cond__l : core.

  Lemma steps_cond h h' h'' L M N O (b : bool):
    h,* L ~> h' *, b ->
    h',* (if b then M else N) ~> h'' *, O ->
    h,* if, L then, M else, N ~> h'' *, O.
  Proof.
    intros HL HMN.
    apply steps_trans with (h2:=h') (M2:=if b then M else N); auto.
    apply steps_step_r with (h2:=h') (M2:=cond b M N); auto.
  Qed.
  Local Hint Resolve steps_cond : core.
  
  Lemma steps_duo__r h h' M N N' :
    h,* N ~> h' *, N' ->
    h,* `(M, N)` ~> h' *, `(M, N')`.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_duo__r : core.

  Lemma steps_duo__l h h' M M' (n : val) :
    h,* M ~> h' *, M' ->
    h,* `(M, n)` ~> h' *, `(M', n)`.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_duo__l : core.

  Lemma steps_duo h h__N h__M M N (m n : val) :
    h,* N ~> h__N *, n ->
    h__N,* M ~> h__M *, m ->
    h,* `(M, N)` ~> h__M *, `(m, n)`.
  Proof.
    intros HN HM.
    apply steps_trans with (h2:=h__N) (M2:=`(M,n)`%trm); auto.
  Qed.
  Local Hint Resolve steps_duo : core.

  Lemma steps_prj h h' b P P' :
    h,* P ~> h' *, P' ->
    h,* prj b P ~> h' *, prj b P'.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_prj : core.

  Lemma steps_prj_duo h h' b P (u v : val) :
    h,* P ~> h' *, `(u, v)` ->
    h,* prj b P ~> h' *, inj__v (if b then u else v).
  Proof.
    intros HP.
    apply steps_step_r with (h2:=h') (M2:=prj b `(u,v)`%trm); auto.
  Qed.
  Local Hint Resolve steps_prj_duo : core.
  
  Lemma steps_inlr h h' b M M' :
    h,* M ~> h' *, M' ->
    h,* inlr b M ~> h' *, inlr b M'.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_inlr : core.

  Lemma steps_mtch h h' L L' M N :
    h,* L ~> h' *, L' ->
    h,* mtch L M N ~> h' *, mtch L' M N.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_mtch : core.

  Lemma steps_mtch_inlr h h' h'' L M N O (b : bool) (v : val) :
    h,* L ~> h' *, inlr b v ->
    h',* (if b then M.[inj__v v/] else N.[inj__v v/]) ~> h'' *, O ->
    h,* mtch L M N ~> h'' *, O.
  Proof.
    intros HL HMN.
    apply steps_trans with (h2:=h') (M2:=mtch (inlr b v) M N); auto.
    apply steps_step_l with (h2:=h') (M2:=if b then M.[inj__v v/] else N.[inj__v v/]); auto.
  Qed.
  Local Hint Resolve steps_mtch_inlr : core.
  
  Lemma steps_new h h' M M' :
    h,* M ~> h' *, M' ->
    h,* new M ~> h' *, new M'.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_new : core.

  Lemma steps_new_alloc h h' M (m : val) l :
    l = fresh (dom h') ->
    h,* M ~> h' *, m ->
    h,* new M ~> <[l:=m]> h' *, loc l.
  Proof.
    intros Hl HM.
    apply steps_step_r with (h2:=h') (M2:=new m); auto.
  Qed.
  Local Hint Resolve steps_new_alloc : core.
  
  Lemma steps_deref h h' M M' :
    h,* M ~> h' *, M' ->
    h,* !, M ~> h' *, !, M'.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_deref : core.

  Lemma steps_deref_loc (h h' : heap) M l (v : val) :
    h,* M ~> h' *, loc l ->
    h' !! l = Some v ->
    h,* !, M ~> h' *, v.
  Proof.
    intros HM Hl.
    apply steps_step_r with (h2:=h') (M2:=deref (loc l)); auto.
  Qed.
  Local Hint Resolve steps_deref_loc : core.
  
  Lemma steps_store__r h h' M N N' :
    h,* N ~> h' *, N' ->
    h,* (M <- N)%trm ~> h' *, (M <- N')%trm.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_store__r : core.

  Lemma steps_store__l h h' M M' (n : val) :
    h,* M ~> h' *, M' ->
    h,* (M <- n)%trm ~> h' *, (M' <- n)%trm.
  Proof.
    induction 1 using steps_ind; eauto.
  Qed.
  Local Hint Resolve steps_store__l : core.

  Lemma steps_store h h__N h__M M N (n : val) (l : nat) :
    h,* N ~> h__N *, n ->
    h__N,* M ~> h__M *, l ->
    l ∈ dom h__M ->
    h,* M <- N ~> <[l:=n]> h__M *, n.
  Proof.
    intros HN HM Hl.
    apply steps_trans with (h2:=h__N) (M2:=store M n); auto.
    apply steps_trans with (h2:=h__M) (M2:=store (loc l) n); auto.
  Qed.
  Local Hint Resolve steps_store : core.
  
  Lemma big_sound h h' M v :
    h ,+ M ↓ h' +, v ->
    h ,* M ~> h' *, v.
  Proof.
    induction 1; cbn; eauto 3.
  Qed.
End big_sound.

Section big_complete.
  Local Hint Constructors big : core.

  Lemma big__v h (v : val) : h,+ v ↓ h +, v.
  Proof.
    induction v; cbn; eauto.
  Qed.
  Local Hint Resolve big__v : core.

  Lemma big_inj__v h h' (u v : val) :
    h ,+ u ↓ h' +, v -> h = h' /\ u = v.
  Proof.
    induction u in h, h', v |- *; cbn;
      inversion 1; subst; auto.
    - specialize IHu with (1:=H1) as [<- <-]. auto.
    - specialize IHu1 with (1:=H5) as [<- <-].
      specialize IHu2 with (1:=H2) as [<- <-]. auto.
    - specialize IHu with (1:=H4) as [<- <-]. auto.
  Qed.

  Lemma step__b_big h1 h2 h3 M1 M2 (m  : val) :
    h1,^ M1 ~> h2 ^, M2 ->
    h2,+ M2 ↓ h3 +, m ->
    h1,+ M1 ↓ h3 +, m.
  Proof.
    inversion 1; subst; eauto.
    - inversion 1; subst.
      elim_inj_right_pair. auto.
    - inversion 1; subst.
      elim_inj_right_pair. eauto.
    - intros [<- <-]%big_inj__v. eauto.
    - inversion 1; subst. auto.
    - intros [<- <-]%big_inj__v. eauto.
    - intros [<- <-]%big_inj__v. eauto.
  Qed.

  Lemma big_heap_subset h h' M v :
    h,+ M ↓ h' +, v -> h ⊆ h'.
  Proof.
    induction 1; eauto.
    - transitivity h__N; auto.
      transitivity h__M; auto.
    - transitivity h__M; auto.
    - transitivity h__M; auto.
    - transitivity h__N; auto.
    - transitivity h__N; auto.
    - transitivity h__M; auto.
    - transitivity h'; auto.
    - transitivity h'; auto.
    - transitivity h'; auto.
      apply insert_subseteq.
      rewrite <- not_elem_of_dom.
      subst l. apply is_fresh.
    - transitivity h__N; auto.
      transitivity h__M; auto.
      (* Bad Lemma. *)
  Abort.
  
  Lemma step_big h1 h2 h3 M1 M2 m :
    h1,` M1 ~> h2 `, M2 ->
    h2,+ M2 ↓ h3 +, m ->
    h1,+ M1 ↓ h3 +, m.
  Proof.
    intros (N1 & N2 & K & -> & -> & H)%inv_step.
    induction K in h1, h2, h3, N1, N2, m, H |- *; cbn;
      eauto using step__b_big;
      inversion 1; subst; eauto.
    - apply big_inj__v in H3 as [<- <-]. eauto.
    - repeat elim_inj_right_pair.
      apply big_inj__v in H8 as [<- ->]. eauto.
    - apply big_inj__v in H3 as [<- <-]. eauto.
    - apply big_inj__v in H3 as [<- <-]. eauto. 
  Qed.

  Lemma steps_big h1 h2 h3 M1 M2 m :
    h1,* M1 ~> h2 *, M2 ->
    h2,+ M2 ↓ h3 +, m ->
    h1,+ M1 ↓ h3 +, m.
  Proof.
    induction 1 using steps_ind in h3, m |- *;
      eauto using step_big.
  Qed.
  
  Lemma big_complete h h' M (v : val) :
    h ,* M ~> h' *, v ->
    h ,+ M ↓ h' +, v.
  Proof.
    remember (inj__v v) as V eqn:HV.
    induction 1 using steps_ind in v, HV |- *; subst; auto.
    specialize IHsteps with (1:=eq_refl) as IH.
    apply steps_big with (2:=IH).
    apply step_steps. assumption.
  Qed.
End big_complete.

Lemma big__v_eq h M (v : val) :
  M = inj__v v ->
  h,+ M ↓ h +, v.
Proof.
  intros ->. apply big__v.
Qed.
Local Hint Resolve big__v_eq : core.

Definition Inv := heap -> Prop.

Definition World := list Inv.

Fixpoint wsat__ralf (h : heap) (W : World) : Prop :=
  match W with
  | [] => True
  | Invar :: W => exists h', Invar h' /\ h' ⊆ h /\ wsat__ralf (h `difference` h') W
  end.

Global Instance val_Equiv : Equiv val.
Proof.
  unfold Equiv, relation. exact eq.
Defined.

Lemma heap_equiv_subset (h1 h2 : heap) :
  h1 ≡ h2 -> h1 ⊆ h2.
Proof.
  rewrite map_equiv_iff.
  rewrite map_subseteq_spec.
  unfold "≡", option_equiv,equiv,val_Equiv.
  intros H i v Hiv. specialize H with (i:=i).
  inversion H; subst.
  - rewrite Hiv in H0. assumption.
  - rewrite Hiv in H1. discriminate.
Qed.
Local Hint Resolve heap_equiv_subset : core.

Reserved Infix "::`" (at level 80, no associativity).

Inductive wsat__rudy (h : heap) : World -> Prop :=
| wsat_nil :
  h ::` []
| wsat_cons h__Inv h__W (Invar : Inv) (W : World) :
  h = h__Inv ∪ h__W ->
  dom h__Inv ## dom h__W ->
  Invar h__Inv ->
  h__W ::` W ->
  h ::` (Invar :: W)
where "h '::`' W" := (wsat__rudy h W%list) : type_scope.

Definition disjoint_union (h1 h2 : heap) : option heap :=
  if gset_disjoint_dec (dom h1) (dom h2) then
    Some (h1 ∪ h2)
  else
    None.

Infix "`⊎" := disjoint_union (at level 30, right associativity).

Reserved Notation "⨄ hs" (at level 30, no associativity).

Fixpoint disjoint_unions (hs : list heap) : option heap :=
  match hs with
  | [] => Some ∅
  | h :: hs => ⨄ hs >>= (fun h' => h `⊎ h')
  end
where "⨄ hs" := (disjoint_unions hs).

Definition wsat__tex (h: heap) (W: World) : Prop :=
  exists (heaps : list heap) (h__disjoint : heap),
    ⨄ heaps = Some h__disjoint
    /\ h__disjoint ⊆ h
    /\ Forall2 (fun Invar => Invar) W heaps.

Infix "::*" := wsat__tex (at level 80, no associativity) : type_scope.

Local Hint Resolve map_disjoint_dom_2 : core.

Lemma wsat__rudy_notes h W :
  h ::` W -> h ::* W.
Proof.
  induction 1.
  - exists [], ∅.
    repeat split; eauto using map_empty_subseteq.
  - destruct IHwsat__rudy as (hs & hd & hdisj & hsub & hW).
    exists (h__Inv :: hs), (h__Inv ∪ hd).
    split_and! ; auto.
    + cbn. rewrite hdisj. cbn. unfold "`⊎".
      destruct (gset_disjoint_dec (dom h__Inv) (dom hd))
        as [_ | Hndisj]; auto.
      apply subseteq_dom in hsub.
      eapply disjoint_difference_l1 with (X1:=dom h__Inv) in hsub.
      apply difference_disjoint in H0.
      rewrite H0 in hsub. contradiction.
    + rewrite H. eapply map_union_mono_l. done.
Qed.

Lemma wsat__notes_rudy h W :
  h ::* W -> h ::` W.
Proof.
  intros (hs & hd & Hdisj & Hsub & Hinvs).
  induction Hinvs in hd, h, Hdisj, Hsub |- *;
    cbn in *.
  - econstructor.
  - destruct (⨄ l') as [h'' |]; try discriminate.
    cbn in Hdisj. unfold "`⊎" in Hdisj.
    destruct (gset_disjoint_dec (dom y) (dom h''))
      as [Hyh'' | Hyh'']; cbn in Hdisj; try discriminate.
    injection Hdisj as <-.
    eapply (wsat_cons _ y (h ∖ y)).
    { eapply map_eq_iff. intros i.
      destruct ((y ∪ h `difference` y) !! i) as [res|] eqn:Heq.
      - rewrite Heq. apply lookup_union_Some_raw in Heq as [H1|(H1&(H2&H3)%lookup_difference_Some)].
        + erewrite lookup_weaken; last eassumption.
          2: by eapply lookup_union_Some_l. done.
        + apply H2.
      - rewrite Heq. apply lookup_union_None_1 in Heq as (HN1&[HN2|(k&Hk)]%lookup_difference_None).
        1: done. by rewrite Hk in HN1. }
    { rewrite dom_difference. symmetry.
      eapply disjoint_difference_l1. done. }
    { done. }
    { eapply IHHinvs. 1: done. apply map_subseteq_spec.
      intros k v Hin. assert (y !! k = None) as HN.
      - eapply not_elem_of_dom. intros Hdom. apply elem_of_dom_2 in Hin.
        edestruct @elem_of_disjoint as [H1 H2]. eapply H1.
        all: eassumption.
      - apply lookup_difference_Some. split; last done.
        eapply lookup_weaken; last eassumption.
        rewrite lookup_union_r //. }
Qed.

Lemma wsat__rudy_ralf h W :
  h ::` W -> wsat__ralf h W.
Proof.
  induction 1; cbn; subst; auto.
  exists h__Inv. repeat split; auto.
  - apply map_union_subseteq_l.
  - rewrite map_difference_union'.
    2:{ apply map_disjoint_dom_2. assumption. }
    rewrite map_difference_diag.
    rewrite map_empty_union.
    rewrite <- map_disjoint_difference.
    2:{ apply map_disjoint_dom_2. symmetry. assumption. }
    assumption.
Qed.

Lemma wsat__ralf_rudy h W :
  wsat__ralf h W ->
  h ::` W.
Proof.
  induction W as [| INV W IHW] in h |- *; cbn.
  - intros _. constructor.
  - intros (h' & HINV & Hsub & IH%IHW).
    apply wsat_cons with (h__Inv:=h') (h__W:=h `difference` h'); auto.
    + rewrite map_difference_union; auto.
    + rewrite dom_difference.
      apply disjoint_difference_r1. auto.
Qed.

Infix "⊒" := (fun W' W => prefix W W') (at level 80, no associativity) : type_scope.


Definition LocTypeInv (l : nat) (a : typ__fo) : Inv :=
  fun h => exists v : val, h = {[l:=v]} /\ 0 !; [] ⊢ v `: a.

Record typ__sem :=
  mk_typ__sem {
      tau :>  World -> val -> Prop;
      tau__prop : forall W v, tau W v -> forall W', W' ⊒ W -> tau W' v;
    }.

Equations typ_size : typ__baby -> nat :=
| Ident__baby _ => 1
| Base__baby _ => 1
| (A `-> B)%typ__baby => 1 + typ_size A + typ_size B
| (forall, A)%typ__baby => 2 + typ_size A
| (exists, A)%typ__baby => 2 + typ_size A
| (A `× B)%typ__baby => 1 + typ_size A + typ_size B
| (A ⊕ B)%typ__baby => 1 + typ_size A + typ_size B
| Ref__baby _ => 2
.

Fact typ_size0 A : 0 < typ_size A.
Proof.
  funelim (typ_size A); lia.
Qed.

Equations measure_interp__typ : val + trm -> typ__baby -> nat :=
| inl _, A => typ_size A
| inr _, A => 1 + typ_size A
.

Definition interp__typvar := var -> typ__sem.

Equations interp__typ (vt : val + trm) (A : typ__baby)
  (δ : interp__typvar) (W : World) : Prop by wf (measure_interp__typ vt A) :=
| inl v, Ident__baby α, δ, W => δ α W v
| inl v, Base__baby B, δ, W => exists (a : atom B), v = a
| inl v, (A `-> B)%typ__baby, δ, W =>
    exists M, v = (fun, M)%val /\ forall W' (v' : val),
        W' ⊒ W ->
        interp__typ (inl v') A δ W' ->
        interp__typ (inr (M.[inj__v v'/])) B δ W'
| inl v, (forall, A)%typ__baby, δ, W =>
    exists M, v = (Λ M)%val /\ forall τ : typ__sem,
        interp__typ (inr M) A (τ .: δ) W
| inl v, (exists, A)%typ__baby, δ, W =>
    exists m, v = pack__v m /\ exists τ : typ__sem,
        interp__typ (inl m) A (τ .: δ) W
| inl v, (A `× B)%typ__baby, δ, W =>
    exists v1 v2, v = (`v1, v2`)%val /\
               interp__typ (inl v1) A δ W /\ interp__typ (inl v2) B δ W
| inl v, (A ⊕ B)%typ__baby, δ, W =>
    exists b m, v = inlr__v b m /\ interp__typ (inl m) (if b then A else B) δ W
| inl v, Ref__baby a, δ, W =>
    exists l i, v = loc__v l /\ W !! i = Some (LocTypeInv l a)
| inr M, A, δ, W =>
    forall W' h', W' ⊒ W -> h' ::` W' -> exists v h'' W'',
                 h',+ M ↓ h'' +, v /\ W'' ⊒ W' /\ h'' ::` W''
                 /\ interp__typ (inl v) A δ W''
.
Next Obligation.
  simp measure_interp__typ typ_size. lia.
Qed.
Next Obligation.
  simp measure_interp__typ typ_size.
  specialize typ_size0 with (A:=A).
  lia.
Qed.
Next Obligation.
  simp measure_interp__typ typ_size. lia.
Qed.
Next Obligation.
  simp measure_interp__typ typ_size. lia.
Qed.
Next Obligation.
  simp measure_interp__typ typ_size. lia.
Qed.
Next Obligation.
  simp measure_interp__typ typ_size.
  destruct b; lia.
Qed.

Notation "'V[|' A '|]'"
  := (fun δ W v => interp__typ (inl v) A%typ__baby δ W)
       (at level 50, no associativity) : type_scope.

Notation "'E[|' A '|]'"
  := (fun δ W M => interp__typ (inr M) A%typ__baby δ W)
       (at level 50, no associativity) : type_scope.

Lemma simple_typ1 (v : val) (a : typ__fo) δ W :
  0 !; [] ⊢ v `: a -> V[| a |] δ W v.
Proof.
  induction a as [p | a1 IHa1 a2 IHa2 | a1 IHa1 a2 IHa2]
    in v, δ, W |- *; cbn; simp interp__typ;
    inversion 1; subst; elim_inj__v; eauto.
  - repeat esplit; eauto.
  - exists b. destruct b; repeat esplit; eauto.
Qed.

Lemma simple_typ2 (v : val) (a : typ__fo) δ W :
  V[| a |] δ W v -> 0 !; [] ⊢ v `: a.
Proof.
  cbn. funelim (interp__typ (inl v) a δ W);
    try clear Heqcall; try elim_inj__fo;
    cbn; simp interp__typ.
  - intros [a ->]. constructor.
  - intros (v1 & v2 & -> & Hv1 & Hv2).
    constructor; eauto.
  - intros (b & m & -> & Hm).
    constructor.
    + rewrite <- distr_if_booll.
      rewrite iff_wf_typ__baby.
      apply wf_typ__fo.
    + specialize H with (b:=b).
      destruct b; eauto.
Qed.

Lemma rew_simple_typ (v : val) (a : typ__fo) δ W :
  V[| a |] δ W v <-> 0 !; [] ⊢ v `: a.
Proof.
  split; eauto using simple_typ1, simple_typ2.
Qed.

Definition interp__Γ
  (Γ : list typ__baby) (δ : interp__typvar)
  (W : World) (γ : var -> val) : Prop :=
  forall x A, Γ !! x = Some A -> V[| A |] δ W (γ x).

Notation "'G[|' Γ '|]'"
  := (interp__Γ Γ%list)
       (at level 50, no associativity) : type_scope.

Lemma nil_interp__Γ δ W γ : G[| [] |] δ W γ.
Proof.
  intros x A HxA. discriminate.
Qed.

Lemma cons_interp__Γ A Γ δ W v γ :
  V[| A |] δ W v ->
  G[| Γ |] δ W γ ->
  G[| A :: Γ |] δ W (v .: γ).
Proof.
  intros Hv HG [| x] B HB; cbn in HB, Hv |- *; eauto.
  injection HB as <-. assumption.
  (* eauto using incl__v. *)
Qed.

Lemma understanding γ x (M : trm) :
  γ 0 = M ->
  (M .: S >>> γ) x = γ x.
Proof.
  destruct x as [| x]; asimpl; auto.
Qed.

Lemma inv_cons_interp__Γ A Γ δ W γ :
  G[| A :: Γ |] δ W γ ->
  exists v, V[| A |] δ W v /\ G[| Γ |] δ W (S >>> γ).
Proof.
  unfold interp__Γ.
  intros HG.
  specialize HG with (x:=0) (A:=A) (1:=eq_refl) as H.
  simp interp__typ in H.
  eexists; split; eauto.
Qed.

Section future.
  Variables W W' : World.

  Hypothesis HW : W' ⊒ W.

  Lemma future_trm_interp__typ M A δ :
    E[| A |] δ W M -> E[| A |] δ W' M.
  Proof.
    cbn. simp interp__typ.
    intros H W'' h' HW' Hh'.
    apply H; auto.
    transitivity W'; auto.
  Qed.
  
  Lemma future_val_interp__typ v A δ :
    V[| A |] δ W v -> V[| A |] δ W' v.
  Proof.
    cbn.
    funelim (interp__typ (inl v) A δ W);
      simp interp__typ; try clear Heqcall.
    - intro H.
      specialize tau__prop with (1:=H) (2:=HW).
      done.
    - intros (M & -> & HM).
      eexists; split; eauto.
      intros W'' v' HW' Hv'.
      apply HM; auto.
      transitivity W'; auto.
    - intros (M & -> & HM).
      eexists; split; eauto.
      intro τ. specialize HM with τ.
      eauto using future_trm_interp__typ.
    - intros (m & -> & τ & Hm).
      eexists; split; eauto.
    - intros (v1 & v2 & -> & Hv1 & Hv2).
      do 2 eexists; split; eauto.
    - intros (b & m & -> & Hm).
      do 2 eexists; split; eauto.
    - intros (l & i & -> & HWl).
      repeat esplit; eauto using prefix_lookup.
  Qed.

  Lemma future_interp__Γ γ Γ δ :
    G[| Γ |] δ W γ -> G[| Γ |] δ W' γ.
  Proof.
    unfold interp__Γ. intros HG x A HxA.
    eauto using future_val_interp__typ.
  Qed.
End future.

Definition typ_to_typ__sem (A : typ__baby) (δ : interp__typvar) : typ__sem :=
  {| tau := V[| A |] δ;
    tau__prop :=
      fun W v τ W' HWW' =>
        future_val_interp__typ W W' HWW' v A δ τ |}.

Lemma incl__v A δ W v :
  V[| A |] δ W v -> E[| A |] δ W v.
Proof.
  cbn. simp interp__typ.
  intros Hv W' h' HW Hh'.
  exists v, h', W'. repeat split.
  - apply big__v.
  - reflexivity.
  - assumption.
  - eapply future_val_interp__typ; eauto.
Qed.

Lemma wsat_new W h1 h2 (INV : Inv) :
  h1 ::` W ->
  INV h2 ->
  dom h1 ## dom h2 ->
  (h2 ∪ h1) ::` (W ++ [INV]).
Proof.
  induction 1 in h2, INV |- *; cbn;
    intros HINV Hdisj; subst.
  - apply wsat_cons with (h__Inv:=h2) (h__W:=h); auto.
    constructor.
  - apply map_disjoint_dom_2 in Hdisj, H0.
    apply map_disjoint_union_l in Hdisj as [HH__Inv HH__W].
    apply wsat_cons with (h__Inv:=h__Inv) (h__W:=h2 ∪ h__W); auto.
    + do 2 rewrite map_union_assoc.
      rewrite (map_union_comm h2 h__Inv); auto.
    + apply map_disjoint_dom_1.
      apply map_disjoint_union_r_2; auto.
    + apply IHwsat__rudy; auto.
      apply map_disjoint_dom_1. assumption.
Qed.

Lemma wsat_alloc h W l (v : val) (a : typ__fo) :
  h ::` W -> l ∉ dom h -> 0 !; [] ⊢ v `: a  ->
  <[l:=v]> h ::` (W ++ [LocTypeInv l a]).
Proof.
  induction 1 in l, v, a |- *;
    intros Hldomh Hva; cbn; subst.
  - rewrite insert_union_singleton_l.
    apply wsat_cons with (h__Inv:={[l:=v]}) (h__W:=h); eauto using insert_union_singleton_l.
    + rewrite dom_singleton.
      rewrite disjoint_singleton_l. assumption.
    + unfold LocTypeInv. eauto.
    + constructor.
  - rewrite dom_union in Hldomh.
    rewrite not_elem_of_union in Hldomh.
    destruct Hldomh as [Hldomh__Inv Hldomh__W].
    rewrite insert_union_r.
    2:{ apply not_elem_of_dom. assumption. }
    apply wsat_cons with (h__Inv:=h__Inv) (h__W:=<[l:=v]> h__W); auto.
    rewrite dom_insert.
    rewrite disjoint_union_r.
    rewrite disjoint_singleton_r. auto.
Qed.

Lemma wsat_lookup_Forall2
  (W : World) (heaps : list heap) l INV :
  Forall2 (fun INV => INV) W heaps ->
  W !! l = Some INV ->
  exists h, heaps !! l = Some h /\ INV h.
Proof.
  induction 1 in l, INV |- *.
  - rewrite lookup_nil. discriminate.
  - destruct l; cbn.
    + intros [= <-].
      repeat esplit; eauto.
    + intros (h & Hh & HINV)%IHForall2.
      repeat esplit; eauto.
Qed.

Lemma wsat_lookup W h l INV :
  h ::` W ->
  W !! l = Some INV ->
  exists h', h' ⊆ h /\ INV h'.
Proof.
  induction 1 in l, INV |- *.
  - rewrite lookup_nil.
    discriminate.
  - subst. destruct l as [| l]; cbn.
    + intros [= ->].
      exists h__Inv. split; auto.
      apply map_union_subseteq_l.
    + intros (h' & Hsub & HINV)%IHwsat__rudy.
      exists h'. split; auto.
      transitivity h__W; auto.
      apply map_union_subseteq_r.
      apply map_disjoint_dom_2.
      assumption.
Qed.

Lemma wsat_deref (h : heap) (W : World) (l i : nat) (a : typ__fo) :
  h ::` W -> W !! i = Some (LocTypeInv l a) ->
  exists v : val, h !! l = Some v /\ 0 !; [] ⊢ v `: a.
Proof.
  intros HhW
    (h' & Hsub & (v & -> & Hv))%(wsat_lookup _ _ _ _ HhW).
  exists v. split; auto.
  apply map_singleton_subseteq_l.
  assumption.
Qed.

Lemma wsat_update W h (i l : nat) (v : val) (INV : Inv) :
  h ::` W ->
  W !! i = Some INV ->
  (forall h, INV h -> is_Some (h !! l) /\ INV (<[l:=v]> h)) ->
  <[l:=v]> h ::` W.
Proof.
  induction 1 in i, l, v, INV |- *.
  - rewrite lookup_nil. discriminate.
  - subst. destruct i as [| i]; cbn.
    + intros [= <-] Hyp.
      specialize Hyp with (1:=H1) as [Hhl HInv].
      rewrite insert_union_l.
      apply wsat_cons with (h__Inv:=<[l:=v]> h__Inv) (h__W:=h__W); auto.
      rewrite dom_insert.
      rewrite disjoint_union_l. split; auto.
      rewrite disjoint_singleton_l.
      apply map_disjoint_dom_2 in H0.
      destruct Hhl as [v' Hhl].
      eapply map_disjoint_Some_l in Hhl; eauto.
      rewrite not_elem_of_dom.
      assumption.
    + intros HInv HSome.
      specialize IHwsat__rudy with
        (1:=HInv) (2:=HSome) as HhW.
      specialize wsat_lookup with
        (1:=H2) (2:=HInv) as (h' & Hsub & Hh').
      specialize HSome with (1:=Hh') as (Hhl & HINV).
      assert (h__Inv !! l = None) as HNone.
      { destruct Hhl as (v' & Hhlv').
        assert (h__W !! l = Some v') as Hsome__w.
        { eapply fin_maps.lookup_weaken; eauto. }
        eapply map_disjoint_Some_r; eauto.
        apply map_disjoint_dom_2. assumption. }
      rewrite insert_union_r; eauto.
      econstructor; eauto.
      rewrite dom_insert.
      rewrite disjoint_union_r.
      split; auto.
      rewrite disjoint_singleton_r.
      rewrite not_elem_of_dom.
      assumption.
Qed.

Lemma wsat_store h W l i (a : typ__fo) (v : val) :
  h ::` W -> W !! i = Some (LocTypeInv l a) ->
  0 !; [] ⊢ v `: a ->
  <[l:=v]> h ::` W.
Proof.
  intros HhW HWl Hva.
  eapply wsat_update; eauto.
  unfold LocTypeInv.
  intros h' (v' & -> & Hv').
  unfold is_Some.
  rewrite insert_singleton.
  rewrite lookup_singleton.
  repeat esplit; eauto.
Qed.

Module boring.
  Lemma cons__δ (δ δ' : interp__typvar) τ :
    (forall α W v, δ α W v -> δ' α W v) ->
    (forall α W v, (τ .: δ) α W v -> (τ .: δ') α W v).
  Proof.
    intros H [| α] W v Hv; asimpl in *; auto.
  Qed.

  Local Hint Resolve cons__δ : core.
  
  Lemma l__v1 A (δ δ' : interp__typvar) W v :
    (forall α W v, δ α W v <-> δ' α W v) ->
    V[| A |] δ W v -> V[| A |] δ' W v.
  Proof.
    intros H.
    unfold "<->" in H.
    do 2 setoid_rewrite forall_and_distr in H.
    rewrite forall_and_distr in H.
    destruct H as [Hδ Hδ'].
    induction A in δ, δ', v, W, Hδ, Hδ' |- *;
      simp interp__typ.
    - intros (M & -> & HM).
      eexists; split; eauto.
      intros W' v1 HWW' Hv1.
      specialize IHA1 with
        (1:=Hδ') (2:=Hδ) (3:=Hv1).
      specialize HM with
        (1:=HWW') (2:=IHA1).
      simp interp__typ in HM |- *.
      intros W'' h'' HW'W'' HhW''.
      specialize HM with
        (1:=HW'W'') (2:=HhW'')
        as (m & h''' & W''' & HM & HW''W''' & HhW''' & Hm).
      specialize IHA2 with
        (1:=Hδ) (2:=Hδ') (3:=Hm).
      exists m, h''', W'''.
      repeat split; auto.
    - intros (M & -> & HM).
      eexists; split; eauto.
      intros τ.
      specialize HM with τ.
      simp interp__typ in HM |- *.
      intros W' h' HWW' HhW'.
      specialize HM with (1:=HWW') (2:=HhW')
        as (m & h'' & W'' & HM & HW'W'' & HhW'' & Hv).
      specialize cons__δ with (τ:=τ) (1:=Hδ) as Hδτ.
      specialize cons__δ with (τ:=τ) (1:=Hδ') as Hδτ'.
      specialize IHA with (1:=Hδτ) (2:=Hδτ') (3:=Hv).
      exists m, h'', W''.
      repeat split; auto.
    - intros (m & -> & τ & Hm). eauto 7.
    - intros (a & b & -> & Ha & Hb). eauto 7.
    - intros (b & m & -> & Hm).
      destruct b; eauto 7.
  Qed.

  Local Hint Resolve l__v1 : core.
  
  Lemma l__v A (δ δ' : interp__typvar) W v :
    (forall α W v, δ α W v <-> δ' α W v) ->
    V[| A |] δ W v <-> V[| A |] δ' W v.
  Proof.
    split; eauto using iff_sym.
  Qed.

  Lemma l__e1 A (δ δ' : interp__typvar) W M :
    (forall α W v, δ α W v <-> δ' α W v) ->
    E[| A |] δ W M -> E[| A |] δ' W M.
  Proof.
    cbn. intros H.
    simp interp__typ.
    intros HM W' h' HWW' HhW'.
    specialize HM with (1:=HWW') (2:=HhW') as
      (m & h'' & W'' & HM & HW'W'' & HhW'' & Hm).
    exists m, h'', W''.
    repeat split; auto.
    revert Hm.
    apply l__v1. assumption.
  Qed.

  Local Hint Resolve l__e1 : core.
  
  Lemma l__e A (δ δ' : interp__typvar) W M :
    (forall α W v, δ α W v <-> δ' α W v) ->
    E[| A |] δ W M <-> E[| A |] δ' W M.
  Proof.
    split; eauto using iff_sym.
  Qed.
  
  Lemma l__Γ1 Γ (δ δ' : interp__typvar) W γ :
    (forall α W v, δ α W v <-> δ' α W v) ->
    G[| Γ |] δ W γ -> G[| Γ |] δ' W γ.
  Proof.
    unfold interp__Γ.
    intros H HG α A HA.
    specialize HG with (1:=HA). eauto.
  Qed.

  Local Hint Resolve l__Γ1 : core.

  Lemma l__Γ Γ (δ δ' : interp__typvar) W γ :
    (forall α W v, δ α W v <-> δ' α W v) ->
    G[| Γ |] δ W γ <-> G[| Γ |] δ' W γ.
  Proof.
    split; eauto using iff_sym.
  Qed.
  
  Global Instance sub_eq_impl : subrelation eq impl.
  Proof.
    unfold subrelation, impl.
    intros x y <-. auto.
  Qed.
  
  Lemma ren_sem__tv A (δ : interp__typvar) (ρ : var -> var) W v :
    V[| A |] (ρ >>> δ) W v <-> V[| A.[ren ρ] |] δ W v.
  Proof.
    induction A in δ, ρ, W, v |- *;
      asimpl; simp interp__typ; eauto.
    - split; intros (M & -> & HM);
        eexists; split; eauto;
        intros W' v HWW' Hv.
      + rewrite <- IHA1 in Hv.
        specialize HM with (1:=HWW') (2:=Hv).
        simp interp__typ in HM |- *.
        intros W'' h'' HW'W'' HhW''.
        (* assert (W'' ⊒ W) as HWW''. *)
        (* { transitivity W'; auto. } *)
        specialize HM with (1:=HW'W'') (2:=HhW'') as
          (m & h''' & W''' & HM & HW'W''' & HhW''' & Hm).
        rewrite IHA2 in Hm.
        exists m, h''', W'''. repeat split; auto.
      + rewrite IHA1 in Hv.
        specialize HM with (1:=HWW') (2:=Hv).
        simp interp__typ in HM |- *.
        intros W'' h'' HW'W'' HhW''.
        specialize HM with (1:=HW'W'') (2:=HhW'')
          as (m & h''' & W''' & HM & HW''W''' & HhW''' & Hm).
        rewrite <- IHA2 in Hm.
        exists m, h''', W'''. repeat split; auto.
    - split; intros (M & -> & HM);
        esplit; split; eauto;
        intros τ; specialize HM with (τ:=τ);
        simp interp__typ in HM |- *;
        intros W' h' HWW' HhW';
        specialize HM with (1:=HWW') (2:=HhW') as (m & h'' & W'' & HM & HW'W'' & HhW'' & Hm).
      + exists m, h'', W''.
        rewrite <- IHA. asimpl. repeat split; auto.
      + rewrite <- IHA in Hm.
        exists m, h'', W''. asimpl in Hm.
        repeat split; auto.
    - split; intros (m & -> & τ & Hm);
        eexists; split; eauto; exists τ.
      + rewrite <- IHA. asimpl.
        revert Hm.
        apply l__v1.
        intros [| α] v; asimpl; auto.
      + rewrite <- IHA in Hm.
        revert Hm. asimpl.
        apply l__v1.
        intros [| α] v; asimpl; auto.
    - split; intros (a & b & -> & Ha & Hb);
        do 2 eexists; split; eauto.
      + rewrite IHA1 in Ha.
        rewrite IHA2 in Hb. auto.
      + rewrite IHA1.
        rewrite IHA2. auto.
    - split; intros (b & m & -> & Hm);
        do 3 eexists; repeat split; cbn; eauto.
      + destruct b; rewrite <- IHA1 || rewrite <- IHA2; auto.
      + destruct b; rewrite IHA1 || rewrite IHA2; auto.
  Qed.

  Lemma ren_sem__te A (δ : interp__typvar) (ρ : var -> var) W M :
    E[| A |] (ρ >>> δ) W M <-> E[| A.[ren ρ] |] δ W M.
  Proof.
    cbn. simp interp__typ.
    split; intros HM W' h' HWW' HhW';
      specialize HM with (1:=HWW') (2:=HhW')
      as (m & h'' & W'' & HM & HW'W'' & HhW'' & Hm);
      exists m, h'', W''; repeat split; auto.
    + rewrite <- ren_sem__tv. assumption.
    + rewrite ren_sem__tv. assumption.
  Qed.
  
  Lemma sem__upΓ1 Γ τ δ W γ :
    (G[| Γ |]) δ W γ ->
    (G[| up__baby Γ |]) (τ .: δ) W γ.
  Proof.
    unfold interp__Γ, up__typs.
    intros HG x A HxA.
    rewrite list_lookup_fmap_Some in HxA.
    destruct HxA as (B & HxB & ->).
    specialize HG with (1:=HxB).
    rewrite <- ren_sem__tv.
    revert HG.
    apply l__v1.
    intros [| α] V; asimpl; eauto.
  Qed.
  
  Lemma subst_interp__tv v W (A : typ__baby) (δ : interp__typvar) (σ : var -> typ__baby) :
    V[| A.[σ] |] δ W v <-> V[| A |] (fun α => typ_to_typ__sem (σ α) δ) W v.
  Proof.
    induction A in v, W, δ, σ |- *; asimpl; simp interp__typ; eauto.
    - split; intros (M & -> & HM); eexists;
        split; eauto; intros W' v HWW' Hv; simp interp__typ;
        intros W'' h'' HW'W'' HhW''.
      + rewrite <- IHA1 in Hv.
        specialize HM with (1:=HWW') (2:=Hv).
        simp interp__typ in HM.
        specialize HM with (1:=HW'W'') (2:=HhW'') as (m & h''' & W''' & HM & HW''W''' & HhW''' & Hm).
        setoid_rewrite <- IHA2.
        exists m, h''', W'''. repeat split; auto.
      + rewrite IHA1 in Hv.
        specialize HM with (1:=HWW') (2:=Hv).
        simp interp__typ in HM.
        specialize HM with (1:=HW'W'') (2:=HhW'') as (m & h''' & W''' & HM & HW''W''' & HhW''' & Hm).
        setoid_rewrite IHA2.
        exists m, h''', W'''. repeat split; auto.
    - split; intros (M & -> & HM);
        eexists; split; eauto; intros τ;
        specialize HM with τ;
        simp interp__typ in HM |- *;
        intros W' h' HWW' HhW';
        specialize HM with (1:=HWW') (2:=HhW')
        as (m & h'' & W'' & HM & HW'W'' & HhW'' & Hm);
        exists m, h'', W''; repeat split; auto; revert Hm;
        rewrite IHA; apply l__v1;
        intros [| α] W''' v; asimpl; simp interp__typ; auto;
        rewrite <- ren_sem__tv; asimpl; auto.
    - split; intros (m & -> & τ & Hm); eexists; split; eauto; exists τ.
      + rewrite IHA in Hm.
        revert Hm. apply l__v1.
        intros [| α] W''' v; repeat (asimpl; simp interp__t); eauto.
        rewrite <- ren_sem__tv, lift_scons. asimpl. auto.
      + rewrite IHA.
        revert Hm. apply l__v1.
        intros [| α] W''' v; repeat (asimpl; simp interp__t); eauto.
        rewrite <- ren_sem__tv, lift_scons. asimpl. auto.
    - split; intros (a & b & -> & Ha & Hb); do 2 eexists; split; eauto;
        revert Ha Hb; rewrite <- IHA1; rewrite <- IHA2; auto.
    - split; intros (b & m & -> & Hm); do 2 eexists; split; eauto;
        revert Hm; destruct b; rewrite IHA1 || rewrite IHA2; auto.
  Qed.

  Lemma subst_interp__te M W (A : typ__baby) (δ : interp__typvar) (σ : var -> typ__baby) :
    E[| A.[σ] |] δ W M <-> E[| A |] (fun α => typ_to_typ__sem (σ α) δ) W M.
  Proof.
    cbn. simp interp__typ.
    split; intros HM W' h' HWW' HhW';
      specialize HM with (1:=HWW') (2:=HhW') as(m & h'' & W'' & HM & HW'W'' & HhW'' & Hm);
      exists m, h'', W''; repeat split; auto;
      revert Hm; rewrite subst_interp__tv; auto.
  Qed.

  Lemma single_subst_interp__tv v W (A B : typ__baby) (δ : interp__typvar) :
    V[| B.[A/] |] δ W v <-> V[| B |] (typ_to_typ__sem A δ .: δ) W v.
  Proof.
    asimpl.
    rewrite subst_interp__tv.
    apply l__v.
    intros [| α] V; repeat (asimpl; simp interp__t); eauto.
  Qed.

  Lemma single_subst_interp__te M W A B (δ : interp__typvar) :
    E[| B.[A/] |] δ W M <-> E[| B |] (typ_to_typ__sem A δ .: δ) W M.
  Proof.
    asimpl.
    rewrite subst_interp__te.
    apply l__e.
    intros [| α] V; repeat (asimpl; simp interp__t); eauto.
  Qed.

  Lemma sem_up__baby Γ τ δ W γ :
    (G[| Γ |]) δ W γ ->
    (G[| up__baby Γ |]) (τ .: δ) W γ.
  Proof.
    intros HG x A HxA.
    simp interp__t.
    unfold interp__Γ in HG.
    unfold up__typs in HxA.
    rewrite list_lookup_fmap_Some in HxA.
    destruct HxA as (B & HxB & ->).
    specialize HG with (1:=HxB).
    rewrite <- ren_sem__tv.
    revert HG.
    apply l__v1.
    intros [| α] V; asimpl; eauto.
  Qed.
End boring.

Definition judge__sem (Γ : list typ__baby) (M : trm) (A : typ__baby) : Prop :=
  forall W δ γ, G[| Γ |] δ W γ -> E[| A |] δ W M.[γ >>> inj__v].

Notation "Γ '|=' M '`:' A" := (judge__sem Γ%list M%trm A%typ) (at level 80, no associativity) : type_scope.

Section compat.
  Local Hint Constructors big : core.
  
  Variable Γ : list typ__baby.

  Lemma ident_compat (x : var) A :
    Γ !! x = Some A ->
    Γ |= x `: A.
  Proof.
    intros HxA W δ γ HG.
    simp interp__typ.
    intros W' h' HW HhW'.
    unfold interp__Γ in HG.
    specialize HG with (1:=HxA) as Hγx.
    exists (γ x), h', W'. cbn. repeat split; auto.
    eapply future_val_interp__typ; eauto.
  Qed.

  Lemma abs_compat M A B :
    A :: Γ |= M `: B ->
    Γ |= (fun, M) `: (A `-> B)%typ__baby.
  Proof.
    unfold judge__sem.
    intros HM W δ γ HG.
    simp interp__typ.
    intros W' h' HW HhW'. cbn.
    exists (fun, M.[up (γ >>> inj__v)])%val, h', W'.
    repeat split; auto. 
    simp interp__typ. eexists; split; eauto.
    intros W'' v HW'' Hv.
    apply future_interp__Γ with (W':=W'') in HG.
    2:{ transitivity W'; auto. }
    specialize cons_interp__Γ with (1:=Hv) (2:=HG) as HGA.
    specialize HM with (1:=HGA).
    asimpl in HM. asimpl. assumption.
  Qed.

  Lemma app_compat M N A B :
    Γ |= M `: (A `-> B)%typ__baby ->
    Γ |= N `: A ->
    Γ |= M N `: B.
  Proof.
    unfold judge__sem.
    intros HM HN W δ γ HG. cbn.
    specialize HM with (1:=HG).
    specialize HN with (1:=HG).
    simp interp__typ in HM, HN |- *.
    intros W' h' HWW' HhW'.
    specialize HN with (1:=HWW') (2:=HhW') as (n & h'' & W'' & HN & HW'W'' & HhW'' & Hn).
    assert (HWW'' : W'' ⊒ W).
    { transitivity  W'; auto. }
    specialize HM with (1:=HWW'') (2:=HhW'') as (m & h''' & W''' & HM & HW''W''' & HhW''' & Hm).
    simp interp__typ in Hm.
    destruct Hm as (O & -> & HO).
    eapply future_val_interp__typ with (W':=W''') in Hn; eauto.
    assert (W''' ⊒ W''') as HW'''W''' by auto.
    specialize HO with (2:=Hn) (1:=HW'''W''').
    simp interp__typ in HO.
    specialize HO with (1:=HW'''W''') (2:=HhW''') as
      (v & h'''' & W'''' & HO & HW'''W'''' & HhW'''' & Hv).
    exists v, h'''', W''''. repeat split; auto.
    + econstructor; eauto.
    + transitivity W''; auto.
      transitivity W'''; auto.
  Qed.

  Lemma tabs_compat M A :
    up__baby Γ |= M `: A ->
    Γ |= Λ M `: (forall, A)%typ__baby.
  Proof.
    unfold judge__sem.
    intros HM W δ γ HG. asimpl.
    simp interp__typ.
    intros W' h' HWW' HhW'.
    exists (Λ M.[γ >>> inj__v])%val, h', W'.
    repeat split; auto.
    simp interp__typ.
    eexists; split; eauto.
    intros τ.
    apply boring.sem_up__baby with (τ:=τ) in HG.
    specialize future_interp__Γ with (1:=HWW') (2:=HG) as HG'. eauto.
  Qed.

  Lemma tapp_compat M A B :
    Γ |= M `: (forall, B)%typ__baby ->
    Γ |= M [-] `: B.[A/].
  Proof.
    unfold judge__sem.
    intros HM W δ γ HG.
    specialize HM with (1:=HG).
    asimpl. simp interp__typ in HM |- *.
    intros W' h' HWW' HhW'.
    specialize HM with (1:=HWW') (2:=HhW')
      as (m & h'' & W'' & HM & HW'W'' & HhW'' & Hm).
    simp interp__typ in Hm.
    destruct Hm as (L & -> & HL).
    specialize HL with (typ_to_typ__sem A δ).
    simp interp__typ in HL.
    assert (HW''W'' : W'' ⊒ W'') by reflexivity.
    specialize HL with (1:=HW''W'') (2:=HhW'') as
      (v & h''' & W''' & HL & HW''W''' & HhW''' & Hv).
    exists v, h''', W'''. repeat split; eauto.
    - transitivity W''; auto.
    - rewrite boring.single_subst_interp__tv.
      assumption.
  Qed.

  Lemma pack_compat M A B :
    Γ |= M `: B.[A/] ->
    Γ |= pack M `: (exists, B)%typ__baby.
  Proof.
    unfold judge__sem.
    intros HM W δ γ HG.
    specialize HM with (1:=HG).
    cbn. simp interp__typ in HM |- *.
    intros W' h' HWW' HhW'.
    specialize HM with (1:=HWW') (2:=HhW') as
      (m & h'' & W'' & HM & HW'W'' & HhW'' & Hm).
    exists (pack__v m), h'', W''.
    repeat split; auto.
    simp interp__typ.
    eexists; split; eauto.
    exists (typ_to_typ__sem A δ).
    rewrite <- boring.single_subst_interp__tv.
    assumption.
  Qed.

  Lemma unpack_compat M N A B :
    Γ |= M `: (exists, A)%typ__baby ->
    A :: up__baby Γ |= N `: B.[ren S] ->
    Γ |= unpack M N `: B.
  Proof.
    unfold judge__sem.
    intros HM HN W0 δ γ HG.
    specialize HM with (1:=HG).
    simp interp__typ in HM |- *.
    intros W1 h1 HW01 HhW1.
    specialize HM with (1:=HW01) (2:=HhW1) as
      (v & h2 & W2 & HM & HW12 & HhW2 & Hm).
    simp interp__typ in Hm.
    destruct Hm as (m & -> & τ & Hm).
    assert (HW02 : W2 ⊒ W0).
    { transitivity W1; auto. }
    apply future_interp__Γ with (1:=HW02) in HG.
    apply boring.sem_up__baby with (τ:=τ) in HG.
    apply cons_interp__Γ with (1:=Hm) in HG.
    specialize HN with (1:=HG).
    simp interp__typ in HN.
    assert (HW22 : W2 ⊒ W2) by reflexivity.
    specialize HN with (1:=HW22) (2:=HhW2)
      as (n & h3 & W3 & HN & HW23 & HhW3 & Hn).
    exists n, h3, W3. cbn. repeat split; eauto.
    - econstructor; eauto. asimpl in *. assumption.
    - transitivity W2; auto.
    - rewrite <- boring.ren_sem__tv in Hn.
      autosubst.
  Qed.

  Lemma base_compat (B : prim) (a : atom B) :
    Γ |= a `: B.
  Proof.
    unfold judge__sem.
    intros W δ γ HG. cbn.
    simp interp__typ.
    intros W' h' HWW' HhW'.
    exists a, h', W'. repeat split; auto.
    simp interp__typ. eauto.
  Qed.

  Lemma uop_compat B (op : una B) M :
    Γ |= M `: B ->
    Γ |= `< op >` M `: B.
  Proof.
    unfold judge__sem.
    intros HM W δ γ HG. cbn.
    specialize HM with (1:=HG).
    simp interp__typ in HM |- *.
    intros W' h' HWW' HhW'.
    specialize HM with (1:=HWW') (2:=HhW') as
      (m & h'' & W'' & HM & HW'W'' & HhW'' & Hm).
    simp interp__typ in Hm.
    destruct Hm as [a ->].
    exists (to_atom B (denote_una op (denote_atom a))), h'', W''. repeat split; eauto.
    simp interp__typ. eauto.
  Qed.

  Lemma bop_compat A B (op : bin A B) M N :
    Γ |= M `: A ->
    Γ |= N `: A ->
    Γ |= M <` op `> N `: B.
  Proof.
    unfold judge__sem.
    intros HM HN W δ γ HG.
    specialize HN with (1:=HG).
    simp interp__typ in HN |- *.
    intros W1 h1 HW1 HhW1.
    specialize HN with (1:=HW1) (2:=HhW1) as
      (n & h2 & W2 & HN & HW2 & Hh2 & Hn).
    simp interp__typ in Hn. destruct Hn as [a2 ->].
    assert (HW02 : W2 ⊒ W).
    { transitivity W1; auto. }
    apply future_interp__Γ with (1:=HW02) in HG.
    specialize HM with (1:=HG).
    simp interp__typ in HM.
    assert (HW22 : W2 ⊒ W2) by reflexivity.
    specialize HM with (1:=HW22) (2:=Hh2) as
      (m & h3 & W3 & HM & HW3 & HhW3 & Hm).
    simp interp__typ in Hm. destruct Hm as [a1 ->].
    exists (to_atom B (denote_bin op (denote_atom a1) (denote_atom a2))).
    exists h3, W3. cbn. repeat split; eauto.
    - transitivity W2; auto.
    - simp interp__typ. eauto.
  Qed.

  Lemma cond_compat L M N A :
    Γ |= L `: Bool ->
    Γ |= M `: A ->
    Γ |= N `: A ->
    Γ |= if, L then, M else, N `: A.
  Proof.
    unfold judge__sem.
    intros HL HM HN W δ γ HG.
    specialize HL with (1:=HG).
    simp interp__typ in HL |- *.
    intros W' h' HWW' HhW'.
    specialize HL with (1:=HWW') (2:=HhW') as
      (l & h'' & W'' & HL & HW'W'' & HhW'' & Hl).
    simp interp__typ in Hl. destruct Hl as [a ->].
    depelim a. cbn.
    assert (HWW'' : W'' ⊒ W).
    { transitivity W'; auto. }
    apply future_interp__Γ with (1:=HWW'') in HG.
    specialize HM with (1:=HG).
    specialize HN with (1:=HG).
    simp interp__typ in HM, HN.
    assert (HW''W'' : W'' ⊒ W'') by reflexivity.
    specialize HM with (1:=HW''W'') (2:=HhW'') as
      (m & h__M & W__M & HM & HW__M & HhW__M & Hm).
    specialize HN with (1:=HW''W'') (2:=HhW'') as
      (n & h__N & W__N & HN & HW__N & HhW__N & Hn).
    exists (if b then m else n), (if b then h__M else h__N), (if b then W__M else W__N).
    repeat split; destruct b; eauto; transitivity W''; auto.
  Qed.

  Lemma letin_compat M N A B :
    Γ |= M `: A ->
    A :: Γ |= N `: B ->
    Γ |= letin M N `: B.
  Proof.
    unfold judge__sem.
    intros HM HN W δ γ HG.
    specialize HM with (1:=HG).
    simp interp__typ in HM |- *.
    intros W' h' HWW' HhW'.
    specialize HM with (1:=HWW') (2:=HhW') as
      (m & h'' & W'' & HM & HW'W'' & HhW'' & Hm).
    assert (HWW'' : W'' ⊒ W).
    { transitivity W'; auto. }
    apply future_interp__Γ with (1:=HWW'') in HG.
    apply cons_interp__Γ with (1:=Hm) in HG.
    specialize HN with (1:=HG).
    simp interp__typ in HN.
    assert (HW''W'' : W'' ⊒ W'') by reflexivity.
    specialize HN with (1:=HW''W'') (2:=HhW'') as
      (n & h''' & W''' & HN & HW''W''' & HhW''' & Hn).
    exists n, h''', W'''. cbn. repeat split; auto.
    - econstructor; eauto. asimpl in *. auto.
    - transitivity W''; auto.
  Qed.

  Lemma duo_compat M N A B :
    Γ |= M `: A ->
    Γ |= N `: B ->
    Γ |= `(M, N)` `: (A `× B)%typ__baby.
  Proof.
    unfold judge__sem.
    intros HM HN W δ γ HG. cbn.
    specialize HN with (1:=HG).
    simp interp__typ in HN |- *.
    intros W' h' HWW' HhW'.
    specialize HN with (1:=HWW') (2:=HhW') as
      (n & h'' & W'' & HN & HW'W'' & HhW'' & Hn).
    assert (HWW'' : W'' ⊒ W) by (transitivity W'; auto).
    assert (HW''W'' : W'' ⊒ W'') by reflexivity.
    apply future_interp__Γ with (1:=HWW'') in HG.
    specialize HM with (1:=HG).
    simp interp__typ in HM.
    specialize HM with (1:=HW''W'') (2:=HhW'') as
      (m & h''' & W''' & HM & HW''W''' & HhW''' & Hm).
    exists (`m, n`)%val, h''', W'''. repeat split; eauto.
    - transitivity W''; eauto.
    - simp interp__typ. repeat esplit; eauto.
      revert Hn. apply future_val_interp__typ with (1:=HW''W''').
  Qed.

  Lemma prj_compat b P A B :
    Γ |= P `: (A `× B)%typ__baby ->
    Γ |= prj b P `: if b then A else B.
  Proof.
    unfold judge__sem.
    intros HP W δ γ HG. cbn.
    specialize HP with (1:=HG).
    simp interp__typ in HP |- *.
    intros W' h' HWW' HhW'.
    specialize HP with (1:=HWW') (2:=HhW') as
      (v & h'' & W'' & HP & HW'W'' & HhW'' & Hv).
    simp interp__typ in Hv. destruct Hv as (m & n & -> & Hm & Hn).
    exists (if b then m else n), h'', W''.
    repeat split; auto. destruct b; auto.
  Qed.

  Lemma inlr_compat (b : bool) M A B :
    Γ |= M `: (if b then A else B) ->
    Γ |= inlr b M `: (A ⊕ B)%typ__baby.
  Proof.
    unfold judge__sem.
    intros HM W δ γ HG. cbn.
    specialize HM with (1:=HG).
    simp interp__typ in HM |- *.
    intros W' h' HWW' HhW'.
    specialize HM with (1:=HWW') (2:=HhW') as
      (m & h'' & W'' & HM & HW'W'' & HhW'' & Hm).
    exists (inlr__v b m), h'', W''. repeat split; auto.
    simp interp__typ.
    repeat esplit; eauto.
  Qed.

  Lemma mtch_compat L M N A B C :
    Γ |= L `: (A ⊕ B)%typ__baby ->
    A :: Γ |= M `: C ->
    B :: Γ |= N `: C ->
    Γ |= mtch L M N `: C.
  Proof.
    unfold judge__sem.
    intros HL HM HN W δ γ HG.
    specialize HL with (1:=HG).
    simp interp__typ in HL |- *.
    intros W' h' HWW' HhW'.
    specialize HL with (1:=HWW') (2:=HhW') as
      (l & h'' & W'' & HL & HW'W'' & HhW'' & Hl).
    simp interp__typ in Hl. destruct Hl as (b & v & -> & Hv).
    assert (HWW'' : W'' ⊒ W) by (transitivity W'; auto).
    assert (HW''W'' : W'' ⊒ W'') by reflexivity.
    apply future_interp__Γ with (1:=HWW'') in HG.
    apply cons_interp__Γ with (1:=Hv) in HG.
    destruct b.
    - specialize HM with (1:=HG).
      simp interp__typ in HM.
      specialize HM with (1:=HW''W'') (2:=HhW'') as
        (m & h''' & W''' & HM & HW''W''' & HhW''' & Hm).
      exists m, h''', W'''. repeat split; eauto.
      + econstructor; eauto. cbn. asimpl in *. assumption.
      + transitivity W''; assumption.
    - specialize HN with (1:=HG).
      simp interp__typ in HN.
      specialize HN with (1:=HW''W'') (2:=HhW'') as
        (n & h''' & W''' & HN & HW''W''' & HhW''' & Hn).
      exists n, h''', W'''. repeat split; eauto.
      + econstructor; eauto. cbn. asimpl in *. assumption.
      + transitivity W''; assumption.
  Qed.

  Lemma new_compat M (a : typ__fo) :
    Γ |= M `: a ->
    Γ |= new M `: Ref__baby a.
  Proof.
    unfold judge__sem.
    intros HM W δ γ HG.
    specialize HM with (1:=HG).
    cbn. simp interp__typ in HM |- *.
    intros W' h' HWW' HhW'.
    specialize HM with (1:=HWW') (2:=HhW') as
      (v & h'' & W'' & HM & HW'W'' & HhW'' & Hv).
    assert (fresh (dom h'') ∉ dom h'') as Hfresh.
    { apply is_fresh. }
    exists (loc__v (fresh (dom h''))).
    specialize wsat_alloc with (1:=HhW'') (2:=Hfresh) (3:=simple_typ2 _ _ _ _ Hv) as Hwsat.
    exists (<[fresh (dom h''):=v]> h'').
    exists (W'' ++ [LocTypeInv (fresh (dom h'')) a]).
    repeat split; auto using prefix_app_r.
    simp interp__typ.
    exists (fresh (dom h'')), (length W''). split; first reflexivity.
    rewrite lookup_app_r; auto.
    replace (length W'' - length W'') with 0 by lia.
    reflexivity.
  Qed.
  
  Lemma deref_compat M A :
    Γ |= M `: Ref__baby A ->
    Γ |= !, M `: A.
  Proof.
    unfold judge__sem. intros H W δ γ HG.
    specialize H with (1:=HG).
    simp interp__typ in H |- *.
    intros W' h' HWW' HhW'.
    specialize H with (1:=HWW') (2:=HhW') as
      (m & h'' & W'' & HM & HW'W'' & HhW'' & Hm).
    simp interp__typ in Hm.
    destruct Hm as (l & i & -> & HWi).
    (* Search "wsat_". *)
    specialize wsat_deref with
      (1:=HhW'') (2:=HWi) as(v & Hhl & Hv).
    exists v, h'', W''. cbn. repeat split; auto.
    - econstructor; eauto.
    - rewrite rew_simple_typ. assumption.
  Qed.

  Lemma store_compat M N A :
    Γ |= M `: Ref__baby A ->
    Γ |= N `: A ->
    Γ |= M <- N `: A.
  Proof.
    unfold judge__sem.
    intros HM HN W δ γ HG. cbn.
    specialize HN with (1:=HG).
    simp interp__typ in HN |- *.
    intros W' h' HWW' HhW'.
    specialize HN with (1:=HWW') (2:=HhW') as
      (n & h'' & W'' & HN & HW'W'' & HhW'' & Hn).
    assert (HWW'': W'' ⊒ W).
    { transitivity W'; auto. }
    assert (HW''W'' : W'' ⊒ W'') by reflexivity.
    apply future_interp__Γ with (1:=HWW'') in HG.
    specialize HM with (1:=HG).
    simp interp__typ in HM.
    specialize HM with (1:=HW''W'') (2:=HhW'') as
      (m & h''' & W''' & HM & HW''W''' & HhW''' & Hm).
    simp interp__typ in Hm.
    destruct Hm as (l & i & -> & HWl).
    exists n, (<[l:=n]> h'''), W'''.
    (* specialize wsat_store with (1:=HhW''') (2:=HWl) (3:=simple_typ2 _ _ _ _ Hn). *)
    repeat split.
    - econstructor; eauto.
      specialize wsat_deref with (1:=HhW''') (2:=HWl) as (v & Hv & _).
      rewrite elem_of_dom.
      exists v. assumption.
    - transitivity W''; auto.
    - eapply wsat_store; eauto.
      rewrite <- rew_simple_typ. eassumption.
    - revert Hn. apply future_val_interp__typ.
      assumption.
  Qed.
End compat.

Section compat.
  Local Hint Resolve ident_compat : core.
  Local Hint Resolve abs_compat : core.
  Local Hint Resolve app_compat : core.
  Local Hint Resolve tabs_compat : core.
  Local Hint Resolve tapp_compat : core.
  Local Hint Resolve pack_compat : core.
  Local Hint Resolve unpack_compat : core.
  Local Hint Resolve letin_compat : core.
  Local Hint Resolve base_compat : core.
  Local Hint Resolve uop_compat : core.
  Local Hint Resolve bop_compat : core.
  Local Hint Resolve cond_compat : core.
  Local Hint Resolve duo_compat : core.
  Local Hint Resolve prj_compat : core.
  Local Hint Resolve inlr_compat : core.
  Local Hint Resolve mtch_compat : core.
  Local Hint Resolve new_compat : core.
  Local Hint Resolve deref_compat : core.
  Local Hint Resolve store_compat : core.

  Lemma sem_sound Δ (Γ : list typ__baby) M (A : typ__baby) :
    Δ !; Γ ⊢ M `: A ->
    Γ |= M `: A.
  Proof.
    induction 1; eauto.
  Qed.
End compat.

Lemma steps_order L M N h1 h2 h3 :
  h1 ,* L ~> h2 *, M -> h1 ,* L ~> h3 *, N -> h2 ,* M ~> h3 *, N \/ h3 ,* N ~> h2 *, M.
Proof.
  induction 1 using steps_ind in N |- *; eauto.
  inversion 1; subst.
  - right. apply steps_trans with (h2:=h2) (M2:=M2); eauto.
    apply step_steps. assumption.
  - destruct y as [h' M'].
    specialize det_step with (1:=H) (2:=H2) as [ -> -> ]. eauto.
Qed.

Lemma steps_inj__v h h' (v : val) M :
  h ,* v ~> h' *, M -> M = v /\ h' = h.
Proof.
  intro Hv.
  remember (inj__v v) as V eqn:HV.
  induction Hv using steps_ind in v, HV |- *; subst; eauto.
  apply val_not_step in H. contradiction.
Qed.

Lemma big_safe M v h h' :
  h ,+ M ↓ h' +, v -> safe h M.
Proof.
  unfold safe, progressive.
  intros HMv h'' M' HMM'.
  specialize big_sound with (1:=HMv) as HMv__s.
  specialize steps_order with (1:=HMM') (2:=HMv__s) as [ [ (-> & <-) | (h2 & M2 & HM2 & HM') ]%inv_steps | [-> ->]%steps_inj__v]; eauto.
  left. exists h2, M2. assumption.
Qed.

Definition δ__emp : var -> typ__sem :=
  fun α =>
    {| tau := fun _ _ => False;
      tau__prop := fun _ _ bad => except bad |}.

Lemma sem_judge_safe M A :
  [] |= M `: A -> forall h, safe h M.
Proof.
  unfold judge__sem.
  intro H.
  assert (exists γ : var -> val, G[| [] |] δ__emp [] γ) as [γ HG] by admit.
  specialize H with (1:=HG).
  replace M.[γ >>> inj__v] with M in H by admit.
  simp interp__typ in H.
  assert (Hnil : @nil Inv ⊒ []) by reflexivity.
  intro h.
  specialize H with (W':=[]) (h':=h) (1:=Hnil) (2:=wsat_nil _).
  destruct H as (v & h' & W' & HMv & _).
  eauto using big_safe.
Admitted.

Theorem termination h M A :
  0 !; [] ⊢ M `: A ->
  exists h' v, h ,+ M ↓ h' +, v.
Proof.
  intros H%sem_sound.
  unfold judge__sem in H.
  assert (exists γ : var -> val, G[| [] |] δ__emp [] γ) as [γ HG] by admit.
  specialize H with (1:=HG).
  replace M.[γ >>> inj__v] with M in H by admit.
  simp interp__typ in H.
  assert (Hnil : @nil Inv ⊒ []) by reflexivity.
  specialize H with (W':=[]) (h':=h) (1:=Hnil) (2:=wsat_nil _).
  destruct H as (v & h' & W' & HMv & _). eauto.
Admitted.

Notation "fst," := (prj true).
Notation "snd," := (prj false).

Lemma judge_fst Δ Γ M A B :
  Δ !; Γ ⊢ M `: (A `× B)%typ__baby ->
  Δ !; Γ ⊢ fst, M `: A.
Proof.
  intros H%(judge_prj__baby _ _ true _ _ _). assumption.
Qed.
Local Hint Resolve judge_fst : core.

Lemma judge_snd Δ Γ M A B :
  Δ !; Γ ⊢ M `: (A `× B)%typ__baby ->
  Δ !; Γ ⊢ snd, M `: B.
Proof.
  intros H%(judge_prj__baby _ _ false _ _ _). assumption.
Qed.
Local Hint Resolve judge_snd : core.

Lemma big_fst P u v h h' :
  h ,+ P ↓ h' +, ((`u, v`))%val ->
  h ,+ fst, P ↓ h' +, u.
Proof.
  intros H%(big_prj _ _ true). assumption.
Qed.
Local Hint Resolve big_fst : core.

Lemma big_snd P u v h h' :
  h ,+ P ↓ h' +, ((`u, v`))%val ->
  h ,+ snd, P ↓ h' +, v.
Proof.
  intros H%(big_prj _ _ false). assumption.
Qed.
Local Hint Resolve big_snd : core.

Notation "M ';;;' N" := (let, M in N.[ren S])%trm (at level 97, right associativity) : trm_scope.

Lemma seq_subst M N σ :
  (M ;;; N)%trm.[σ] = (M.[σ] ;;; N.[σ])%trm.
Proof.
  autosubst.
Qed.

Lemma judge_seq Δ Γ M N A B :
  Δ !; Γ ⊢ M `: A ->
  Δ !; Γ ⊢ N `: B ->
  Δ !; Γ ⊢ M ;;; N `: B.
Proof.
  intros HM HN.
  apply judge_letin__baby with (A:=A); auto.
Qed.

Lemma inv_judge_seq Δ Γ M N B :
  Δ !; Γ ⊢ M ;;; N `: B ->
  exists A, Δ !; Γ ⊢ M `: A /\ Δ !; Γ ⊢ N `: B.
Proof.
  inversion 1; subst.
  eexists; split; eauto using judge_rename__baby_inv_single.
Qed.

Lemma big_seq M N m n h1 h2 h3 :
  h1 ,+ M ↓ h2 +, m ->
  h2 ,+ N ↓ h3 +, n ->
  h1 ,+ (M ;;; N)%trm ↓ h3 +, n.
Proof.
  intros HM HN.
  econstructor; eauto. asimpl. auto.
Qed.

Lemma seq_compat Γ M N A B :
  Γ |= M `: A ->
  Γ |= N `: B ->
  Γ |= M ;;; N `: B.
Proof.
  intros HM HN.
  eapply letin_compat; eauto.
  unfold judge__sem in HN |- *.
  intros W δ γ (a & Ha & HG)%inv_cons_interp__Γ.
  specialize HN with (1:=HG).
  simp interp__typ in HN |- *.
  intros W' h' HWW' HhW'.
  specialize HN with (1:=HWW') (2:=HhW').
  destruct HN as (n & h'' & W'' & HN & HW'W'' & HhW'' & Hn).
  exists n, h'', W''.
  repeat split; auto.
  autosubst.
Qed.

Notation "'assrt' M" :=
  (if, M%trm then, ttt else, ttt ttt)%trm
    (at level 100, no associativity) : trm_scope.

Lemma big_assrt M h h' :
  h ,+ M ↓ h' +, true ->
  h ,+ assrt M ↓ h' +, ttt.
Proof.
  intro HM.
  econstructor; eauto.
Qed.

Section mutbit.
  Let MUTBIT := ((Unit `-> Unit) `× (Unit `-> Bool))%typ__baby.

  Let MyMutBit__unsafe :=
        (
          let, new 0%Z in
          `(
              (fun, (assrt (((!, ident 1) <` `= `> 0%Z) <` `\/ `> ((!, ident 1) <` `= `> 1%Z)));;;
                    ((ident 1) <- (1%Z <` `- `> !, ident 1));;; base ttt),
              
              (fun, (assrt (((!, ident 1) <` `= `> 0%Z) <` `\/ `> ((!, ident 1) <` `= `> 1%Z)));;;
                    0%Z <` `<` `> !, ident 1)
            )`
        )%trm.

  Local Hint Constructors big : core.
  Local Hint Resolve big_fst : core.
  Local Hint Resolve big_snd : core.
  Local Hint Resolve big_seq : core.
  Local Hint Constructors judge__baby : core.
  Local Hint Resolve big_uop_eq : core.
  Local Hint Resolve big_bop_eq : core.
  Local Hint Resolve big__v : core.

  Let Invar :=
        fun l (h : heap) => ∃ z : Z, h = {[l := base__v z]} ∧ (z = 0%Z \/ z = 1%Z).
  
  Lemma sem_safe_bits Γ :
    Γ |= MyMutBit__unsafe `: MUTBIT.
  Proof.
    subst MyMutBit__unsafe MUTBIT.
    unfold judge__sem.
    intros W0 δ γ HG.
    simp interp__typ.
    intros W1 h1 HW0W1 HhW1.
    eexists. exists (<[fresh (dom h1):=base__v 0%Z]> h1).
    exists (W1 ++ [Invar (fresh (dom h1))]).
    cbn. repeat split.
    - asimpl. econstructor; eauto. asimpl. eauto.
    - apply prefix_app_r. reflexivity.
    - rewrite insert_union_singleton_l.
      apply wsat_new; auto.
      + exists 0%Z. repeat split; eauto.
      + rewrite dom_singleton.
        Search (_ ## {[_]}).
        rewrite disjoint_singleton_r.
        apply is_fresh.
    - simp interp__typ.
      do 2 eexists. split; eauto. split.
      { simp interp__typ.
        eexists; split; eauto.
        intros W2 v HW1W2.
        simp interp__typ.
        intros [a ->] W3 h3 HW2W3 HhW3. depelim a.
        cbn. exists ttt.
        destruct HW1W2 as (W1' & ->).
        destruct HW2W3 as (W2 & ->).
        assert ((((W1 ++ [Invar (fresh (dom h1))]) ++ W1') ++ W2) !! length W1
                = Some (Invar (fresh (dom h1)))) as HWlook.
        { rewrite <- !app_assoc.
          rewrite lookup_app_r; try lia.
          2:{ done. }
          rewrite Nat.sub_diag. reflexivity. }
        specialize wsat_lookup with (1:=HhW3) (2:=HWlook)  as (h' & Hh'h3 & Hh').
        unfold Invar in Hh'.
        destruct Hh' as (z & -> & Hh').
        exists (<[fresh (dom h1) := base__v (1 - z)%Z]> h3).
        exists (((W1 ++ [Invar (fresh (dom h1))]) ++ W1') ++ W2).
        apply map_singleton_subseteq_l in Hh'h3.
        repeat split; auto.
        { apply big_let with (h__M:=h3) (m:=ttt).
          - apply big_cond with (h':=h3) (b:=true); eauto.
            destruct Hh' as [ -> | ->  ].
            + apply big_bop_eq with (h__N:=h3) (m:=true) (n:=false); eauto.
              * eapply big_bop_eq with (h__N:=h3) (m:=0%Z) (n:=1%Z); eauto.
              * eapply big_bop_eq with (h__N:=h3) (m:=0%Z) (n:=0%Z); eauto.
            + apply big_bop_eq with (h__N:=h3) (m:=false) (n:=true); eauto.
              * apply big_bop_eq with (h__N:=h3) (m:=1%Z) (n:=1%Z); eauto.
              * apply big_bop_eq with (h__N:=h3) (m:=1%Z) (n:=0%Z); eauto.
          - asimpl. apply big_let with (h__M:=<[fresh (dom h1):=base__v (1 - z)%Z]> h3) (m:=(1 - z)%Z); eauto.
            econstructor; eauto.
            + apply big_bop_eq with (h__N:=h3) (m:=1%Z) (n:=z); eauto.
            + rewrite elem_of_dom. eauto. }
        { eapply wsat_update; eauto.
          intros h Hh.
          unfold Invar in Hh.
          destruct Hh as (v & -> & Hh).
          Search ({[?l := _; ?l := _]}).
          rewrite insert_singleton. split.
          - exists v. rewrite lookup_singleton. reflexivity.
          - unfold Invar.
            repeat esplit; eauto.
            destruct Hh' as [ [= ->] | [= ->]  ]; auto. }
        simp interp__typ. eauto. }
      { simp interp__typ.
        eexists; split; eauto.
        intros W2 v HW1W2. simp interp__typ.
        intros [a ->]. depelim a.
        intros W3 h3 HW2W3 HhW3. cbn.
        destruct HW1W2 as (W1' & ->).
        destruct HW2W3 as (W2 & ->).
        assert ((((W1 ++ [Invar (fresh (dom h1))]) ++ W1') ++ W2) !! length W1
                = Some (Invar (fresh (dom h1)))) as HWlook.
        { rewrite <- !app_assoc.
          rewrite lookup_app_r; try lia.
          2:{ done. }
          rewrite Nat.sub_diag. reflexivity. }
        specialize wsat_lookup with (1:=HhW3) (2:=HWlook)  as (h' & Hh'h3 & Hh').
        unfold Invar in Hh'.
        destruct Hh' as (z & -> & Hh').
        exists (if decide (z = 0%Z) then false else true), h3, (((W1 ++ [Invar (fresh (dom h1))]) ++ W1') ++ W2).
        apply map_singleton_subseteq_l in Hh'h3.
        repeat split; eauto.
        { apply big_let with (h__M:=h3) (m:=ttt); auto.
          - apply big_assrt. destruct Hh' as [-> | ->].
            + apply big_bop_eq with (h__N:=h3) (m:=true) (n:=false); eauto.
              * apply big_bop_eq with (h__N:=h3) (m:=0%Z) (n:=1%Z); eauto.
              * apply big_bop_eq with (h__N:=h3) (m:=0%Z) (n:=0%Z); eauto.
            + apply big_bop_eq with (h__N:=h3) (m:=false) (n:=true); eauto.
              * apply big_bop_eq with (h__N:=h3) (m:=1%Z) (n:=1%Z); eauto.
              * apply big_bop_eq with (h__N:=h3) (m:=1%Z) (n:=0%Z); eauto.
          - asimpl.
            apply big_bop_eq with (h__N:=h3) (m:=0%Z) (n:=z); eauto.
            destruct (decide (z = 0%Z)); destruct Hh' as [-> | ->]; cbn; reflexivity || lia. }
        simp interp__typ. eauto. }
  Qed.

  Lemma sem_client_MyMutBit__unsafe M A :
    0 !; [MUTBIT] ⊢ M `: A ->
    forall h, safe h (M.[MyMutBit__unsafe/]).
  Proof.
    intros HM h.
    apply sem_sound in HM.
    apply sem_judge_safe with (A:=A).
    unfold judge__sem in HM |- *.
    intros W δ γ HG.
  Admitted.
End mutbit.





