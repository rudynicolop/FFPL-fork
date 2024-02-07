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
  | H: ?a = ?a |- _ => clear H
  | H: inj__v _ = inj__v _ |- _ => specialize inj_inj__v with (1:=H) as ->
  | H: (fun, _)%trm = inj__v _ |- _ => specialize abs_inj__v with (1:=H) as ->
  | H: inj__v _ = (fun, _)%trm |- _ => symmetry in H; specialize abs_inj__v with (1:=H) as ->
  | H: (Λ _)%trm = inj__v _ |- _ => specialize tabs_inj__v with (1:=H) as ->
  | H: inj__v _ = (Λ _)%trm |- _ => symmetry in H; specialize tabs_inj__v with (1:=H) as ->
  | H: pack _ = inj__v _ |- _ => specialize pack_inj__v with (1:=H) as (? & -> & ->)
  | H: inj__v _ = pack _ |- _ => symmetry in H; specialize pack_inj__v with (1:=H) as (? & -> & ->)
  | H: @base ?T _ = inj__v _ |- _ => specialize (base_inj__v (T:=T)) with (1:=H) as ->
  | H: inj__v _ = @base ?T _ |- _ => symmetry in H; specialize (base_inj__v (T:=T)) with (1:=H) as ->
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

Lemma lookup_ren_up__typs Γ1 Γ2 δ :
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

Definition lookup_ren_inv (Γ1 Γ2 : list typ) (δ : var -> var) :=
  forall x A, Γ2 !! (δ x) = Some A -> Γ1 !! x = Some A.

Lemma lookup_ren_inv_upren A Γ1 Γ2 δ :
  lookup_ren_inv Γ1 Γ2 δ ->
  lookup_ren_inv (A :: Γ1) (A :: Γ2) (upren δ).
Proof.
  unfold lookup_ren_inv.
  intros Hlook [| x] B; cbn; auto.
Qed.

Lemma lookup_ren_inv_up__typs Γ1 Γ2 δ :
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

Lemma lookup_ren_inv_S Γ A :
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

Fixpoint inj__fo (A : typ__fo) : typ :=
  match A with
  | Base__fo B => B
  | (A `× B)%typ__fo => inj__fo A `× inj__fo B
  | (A ⊕ B)%typ__fo => inj__fo A ⊕ inj__fo B
  end.

Definition is_typ__fo (A : typ) : Prop :=
  exists F, A = inj__fo F.

Lemma Base_is_typ__fo (B : prim) :
  is_typ__fo B.
Proof.
  exists B. reflexivity.
Qed.

Lemma Prod_is_typ__fo (A B : typ) :
  is_typ__fo A -> is_typ__fo B ->
  is_typ__fo (A `× B).
Proof.
  intros [a ->] [b ->].
  exists (a `× b)%typ__fo. reflexivity.
Qed.

Lemma Sum_is_typ__fo (A B : typ) :
  is_typ__fo A -> is_typ__fo B ->
  is_typ__fo (A ⊕ B).
Proof.
  intros [a ->] [b ->].
  exists (a ⊕ b)%typ__fo. reflexivity.
Qed.

Lemma Ident_is_not_typ__fo (α : var) :
  ~ is_typ__fo α.
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Fun_is_not_typ__fo A B :
  ~ is_typ__fo (A `-> B).
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Uni_is_not_typ__fo A :
  ~ is_typ__fo (forall, A).
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Exi_is_not_typ__fo A :
  ~ is_typ__fo (exists, A).
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Ref_is_not_typ__fo A :
  ~ is_typ__fo (Ref A).
Proof.
  intros ([] & H); discriminate.
Qed.

Lemma Base_inj__fo (B : prim) F :
  Base B = inj__fo F -> F = B.
Proof.
  destruct F; discriminate || intros [= <-]. reflexivity.
Qed.

Lemma Prod_inj__fo A B F :
  (A `× B)%typ = inj__fo F -> exists F1 F2, F = (F1 `× F2)%typ__fo /\ A = inj__fo F1 /\ B = inj__fo F2.
Proof.
  destruct F; discriminate || intros [= -> ->]. eauto.
Qed.

Lemma Sum_inj__fo A B F :
  (A ⊕ B)%typ = inj__fo F -> exists F1 F2, F = (F1 ⊕ F2)%typ__fo /\ A = inj__fo F1 /\ B = inj__fo F2.
Proof.
  destruct F; discriminate || intros [= -> ->]. eauto.
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
| big_bin h__M h__N (A B : prim) (op : bin A B) M N (m n : atom A) :
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
