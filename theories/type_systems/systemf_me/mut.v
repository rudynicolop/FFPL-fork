From Autosubst Require Export Autosubst.
From ffpl.lib Require Export maps.
From Equations Require Export Equations Signature.

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
Infix "`+" :=
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
Coercion loc : nat >-> trm.
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
  | loc__v n         => n
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
  is_val l.
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
  | H: ?a = ?a |- _ => clear H
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
  | H: inlr _ _ = inj__v _ |- _ => specialize inlr_inj__v with (1:=H) as (? & -> & ->)
  | H: inj__v _ = inlr _ _  |- _ => symmetry in H; specialize inlr_inj__v with (1:=H) as (? & -> & ->)
  | H: loc _ = inj__v _ |- _ => specialize loc_inj__v with (1:=H) as ->
  | H: inj__v _ = loc _ |- _ => symmetry in H; specialize loc_inj__v with (1:=H) as ->
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

Definition heap := list val.

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
    h ,^ prj b `(m, n)`%trm ~> h ^, if b then m else n
  | step_cond__b (b : bool) M N :
    h ,^ if, b then, M else, N ~> h ^, if b then M else N
  | step_letin__b (v : val) N :
    h ,^ (let, inj__v v in N)%trm ~> h ^, N.[ inj__v v /]
  | step_mtch_inlr__b b (v : val) M N :
    h ,^ mtch (inlr b v) M N ~> h ^, if b then M.[inj__v v/] else N.[inj__v v/]
  | step_new_alloc__b (v : val) :
    h ,^ (new (inj__v v))%trm ~> (h ++ [v]) ^, loc (length h)
  | step_deref_loc__b (l : nat) (v : val) :
    h !! l = Some v ->
    h ,^ !, l ~> h ^, v
  | step_store_loc_val (l : nat) (v : val) :
    l < length h ->
    h ,^ l <- v ~> <[l:=v]> h ^, v 
where "h1 ',^' e1  '~>' h2 '^,' e2" := (step__b h1%list e1%trm h2%list e2%trm) : type_scope.

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
    injection H6 as [= <-]. auto.
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
    => assert (is_val M) as [? HM] by eauto;
      rewrite HM in H
  end.

Local Hint Extern 3 => val_tedium : core.

Ltac tedium :=
  lazymatch goal with
    H : inj__v _ = (_ [[ ?N ]])%trm |- _ ,` ?N ~> _ `, _ -> _
    => elim_val_fill__k;
      intros ?%val_not_step__b; contradiction
  end.

Local Hint Extern 0 => tedium : core.

Lemma uniq_decomp__k h h__M h__N KM KN M N M' N' :
  (KM [[ M ]])%trm = (KN [[ N ]])%trm ->
  h ,^ M ~> h__M ^, M' -> h ,^ N ~> h__N ^, N' ->
  h__M = h__N /\ KM = KN /\ M = N.
Proof.
  induction KM in h, h__M, h__N, KN, M, N, M', N' |- *;
    destruct KN; cbn; try discriminate;
    try (intros ->; inversion 1; subst; auto; contradiction);
    try (intros <- HM; inversion 1; subst; revert HM; auto; contradiction).
  - intros -> HM HN.
    specialize det_step__b with (1:=HM) (2:=HN) as [<- <-]. auto.
  - intros ->. inversion 1; subst.
    elim_inj__v. val_tedium. elim_inj__v.
    elim_val_fill__k. elim_inj__v.
    intros ?%val_not_step__b. contradiction.
  - intros ->. inversion 1; subst.
    elim_val_fill__k.
    intros ?%val_not_step__b. contradiction.
  - intros ->. inversion 1; subst. val_tedium.
    elim_inj__v. tedium.
    (* lazymatch goal with *)
    (* | H:(fun, _)%trm = _ |- _ => specialize abs_inj__v with (1 := H) as -> *)
    (* | H:_ = (fun, _)%trm |- _ => symmetry in H; specialize abs_inj__v with (1 := H) as -> *)
    (* end. *)
    clear H2.
    elim_inj__v.
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
Abort.

Lemma det_step h h__M h__N L M N :
  h ,` L ~> h__M `, M -> h ,` L ~> h__N `, N -> h__M = h__N /\ M = N.
Proof.
  intros (L' & M' & KM & -> & -> & HLM)%inv_step (L'' & N' & KN & H & -> & HLN)%inv_step.
  specialize uniq_decomp__k with (1:=H) (2:=HLM) (3:=HLN) as [<- <-].
  specialize det_step__b with (1:=HLM) (2:=HLN) as <-. reflexivity.
Qed.

