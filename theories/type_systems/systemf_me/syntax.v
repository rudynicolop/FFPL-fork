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
| Unit
| Bool
| Int
| Prd (A B : typ)
| Sum (A B : typ)
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
Notation "'`∃' A" :=
  (Exi A%typ)
    (at level 100, A at level 200)
    : typ_scope.
Infix "×" :=
  Prd
    (at level 100, right associativity)
    : typ_scope.
Infix "`+" :=
  Sum
    (at level 100, right associativity)
    : typ_scope.

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
  | letin
      (M : trm)
      (N : {bind 1 of trm})
  (* Simple terms. *)
  | ttt
  | bewl (b : bool)
  | bewl1 (f : bool -> bool) (M : trm)
  | bewl2 (f : bool -> bool -> bool) (M N : trm)
  | int (z : Z)
  | int1 (f : Z -> Z) (M : trm)
  | int2 (f : Z -> Z -> Z) (M N : trm)
  | cmp (f : Z -> Z -> bool) (M N : trm)
  | cond (L M N : trm)
  | tuple (M N : trm)
  | proj (lr : bool) (M : trm)
  | inlr (lr : T + T) (M : trm)
  | mtch (L : trm)  (M N : {bind 1 of trm})
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
Arguments letin {_}.
Arguments ttt {_}.
Arguments bewl {_}.
Arguments bewl1 {_}.
Arguments bewl2 {_}.
Arguments int {_}.
Arguments int1 {_}.
Arguments int2 {_}.
Arguments cmp {_}.
Arguments cond {_}.
Arguments tuple {_}.
Arguments proj {_}.
Arguments inlr {_}.
Arguments mtch {_}.

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
Infix "⋅" := app (at level 97, left associativity) : rtrm_scope.
Infix "⋅" := app (at level 97, left associativity) : strm_scope.
Notation "'Λ' M" := (tabs M%strm) (at level 100, right associativity) : strm_scope.
Notation "'Λ' M" := (tabs M%rtrm) (at level 100, right associativity) : rtrm_scope.
Notation "M '`[' A  ']`'" := (tapp M%strm A%typ) (at level 96, left associativity) : strm_scope.
Notation "M '[-]'" := (tapp M%rtrm tt) (at level 96, left associativity) : rtrm_scope.
Notation "'`(' M , N ')`'" := (tuple M%strm N%strm) (at level 100, right associativity) : strm_scope.
Notation "'`(' M , N ')`'" := (tuple M%rtrm N%rtrm) (at level 100, right associativity) : rtrm_scope.
Notation "'`(' x , .. , y  , z ')`'" := (tuple x%strm .. (tuple y%strm z%strm) ..) : strm_scope.
Notation "'`(' x , .. , y  , z ')`'" := (tuple x%rtrm .. (tuple y%rtrm z%rtrm) ..) : rtrm_scope.

Inductive val :=
| abs__v (M : rtrm)
| tabs__v (M : rtrm)
| pack__v (v : val)
| ttt__v
| bewl__v (b : bool)
| int__v (z : Z)
| tuple__v (v1 v2 : val)
| inlr__v (lr : bool) (v : val)
.

Declare Scope val_scope.
Delimit Scope val_scope with val.
Bind Scope val_scope with val.

Notation "'`λ' M" := (abs__v M%rtrm) (at level 100, right associativity) : val_scope.
Notation "'Λ' M" := (tabs__v M%rtrm) (at level 100, right associativity) : val_scope.
Notation "'`(' M , N ')`'" := (tuple__v M%val N%val) (at level 100, right associativity) : val_scope.
Notation "'`(' x , .. , y  , z ')`'" := (tuple__v x%val .. (tuple__v y%val z%val) ..) : val_scope.

Section sumbool.
  Context {U V : Type}.

  Definition sum_of_bool (b : bool) (u : U) (v : V) : U + V :=
    if b then inl u else inr v.

  Lemma inj_sum_of_bool b1 b2 u1 u2 v1 v2 :
    sum_of_bool b1 u1 v1 = sum_of_bool b2 u2 v2 ->
    b1 = b2 /\ (u1 = u2 \/ v1 = v2).
  Proof.
    destruct b1, b2; cbn; discriminate || injection 1 as <-; auto.
  Qed.

  Definition bool_of_sum (uv : U + V) : bool := if uv then true else false.

  Lemma bool_of_sum_of_bool b u v :
    bool_of_sum (sum_of_bool b u v) = b.
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma sum_of_bool_of_sum__l u v :
    sum_of_bool (bool_of_sum (inl u)) u v = inl u.
  Proof.
    reflexivity.
  Qed.

  Lemma sum_of_bool_of_sum__r u v :
    sum_of_bool (bool_of_sum (inr v)) u v = inr v.
  Proof.
    reflexivity.
  Qed.

  Lemma sum_of_bool_if {A} b u v (x y : A) :
    (if sum_of_bool b u v then x else y) = if b then x else y.
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma bool_of_sum_if {A} uv (x y : A) :
    (if bool_of_sum uv then x else y) = if uv then x else y.
  Proof.
    destruct uv; reflexivity.
  Qed.
  
  Variant Forall_sum (P__l : U -> Prop) (P__r : V -> Prop) : U + V -> Prop :=
    | Forall_sum__l u : P__l u -> Forall_sum P__l P__r (inl u)
    | Forall_sum__r v : P__r v -> Forall_sum P__l P__r (inr v).
  
  Lemma sum_of_bool_of_sum uv u v :
        Forall_sum (eq u) (eq v) uv ->
        sum_of_bool (bool_of_sum uv) u v = uv.
  Proof.
    inversion 1; subst; reflexivity.
  Qed.
End sumbool.
  
Definition sum_of_bool__tt (b : bool) : unit + unit :=
  sum_of_bool b tt tt.

Lemma inj_sum_of_bool__tt b1 b2 :
  sum_of_bool__tt b1 = sum_of_bool__tt b2 -> b1 = b2.
Proof.
  intros [<- _]%inj_sum_of_bool. reflexivity.
Qed.

Lemma sum_of_bool_of_sum__tt lr :
  sum_of_bool__tt (bool_of_sum lr) = lr.
Proof.
  destruct lr as [[] | []]; reflexivity.
Qed.

Local Hint Rewrite sum_of_bool_of_sum__tt : core.

Lemma bool_of_sum_of_bool__tt b :
  bool_of_sum (sum_of_bool__tt b) = b.
Proof.
  apply bool_of_sum_of_bool.
Qed.

Local Hint Rewrite bool_of_sum_of_bool__tt : core.

Lemma sum_of_bool_if__tt {A} b (x y : A) :
  (if sum_of_bool__tt b then x else y) = if b then x else y.
Proof.
  rewrite sum_of_bool_if. reflexivity.
Qed.

Fixpoint inj__v (v : val) : rtrm :=
  match v with
  | (`λ M)%val   => `λ M
  | (Λ M)%val   => Λ M
  | pack__v v      => pack tt $ inj__v v
  | ttt__v         => ttt
  | bewl__v b      => bewl b
  | int__v z       => int z
  | `(v1 , v2)`%val => `(inj__v v1, inj__v v2)`
  | inlr__v b v       => inlr (sum_of_bool__tt b) $ inj__v v
  end.

Lemma inj_inj__v v1 v2 :
  inj__v v1 = inj__v v2 -> v1 = v2.
Proof.
  induction v1 as [M1 | M1 | v1 IHv1 | | b1 | z1 | v11 IHv11 v12 IHv12 | b1 v1 IHv1] in v2 |- *;
    destruct v2 as [M2 | M2 | v2 | | b2 | z2 | v21 v22 | b2 v2]; cbn;
    discriminate || (try injection 1 as <-); try reflexivity.
  - injection 1 as <-%IHv1. reflexivity.
  - injection 1 as <-%IHv11 <-%IHv12. reflexivity.
  - injection 1 as <-%inj_sum_of_bool__tt <-%IHv1. reflexivity.
Qed.

Definition is_val (M : rtrm) : Prop :=
  exists v, M = inj__v v.

Lemma val_is_val (v : val) :
  is_val (inj__v v).
Proof.
  eexists; eauto.
Qed.

Lemma abs_is_val M : is_val (`λ M)%rtrm.
Proof.
  unfold is_val.
  exists (`λ M)%val.
  reflexivity.
Qed.

Lemma tabs_is_val M : is_val (Λ M)%rtrm.
Proof.
  exists (Λ M)%val.
  reflexivity.
Qed.

Lemma pack_is_val M :
  is_val M -> is_val (pack tt M).
Proof.
  unfold is_val.
  intros (v & ->).
  exists (pack__v v).
  reflexivity.
Qed.

Lemma ttt_is_val : is_val ttt.
Proof.
  exists ttt__v; reflexivity.
Qed.

Lemma bewl_is_val b : is_val (bewl b).
Proof.
  exists (bewl__v b); reflexivity.
Qed.

Lemma int_is_val z : is_val (int z).
Proof.
  exists (int__v z); reflexivity.
Qed.

Lemma tuple_is_val M N :
  is_val M -> is_val N -> is_val `(M, N)`%rtrm.
Proof.
  intros (m & ->) (n & ->).
  exists (tuple__v m n). reflexivity.
Qed.

Lemma inlr_is_val lr M :
  is_val M -> is_val (inlr lr M).
Proof.
  intros [m ->].
  exists (inlr__v (bool_of_sum lr) m). cbn.
  rewrite sum_of_bool_of_sum__tt.
  reflexivity.
Qed.

Local Hint Resolve abs_is_val : core.
Local Hint Resolve tabs_is_val : core.
Local Hint Resolve pack_is_val : core.
Local Hint Resolve ttt_is_val : core.
Local Hint Resolve bewl_is_val : core.
Local Hint Resolve int_is_val : core.
Local Hint Resolve tuple_is_val : core.
Local Hint Resolve inlr_is_val : core.
Local Hint Resolve val_is_val : core.

Coercion inj__v : val >-> rtrm.

Lemma abs_inj__v (v : val) M :
  (`λ M)%rtrm = inj__v v -> v = (`λ M)%val.
Proof.
  destruct v; discriminate || injection 1 as <-; reflexivity.
Qed.

Lemma tabs_inj__v (v : val) M :
  (Λ M)%rtrm = inj__v v -> v = (Λ M)%val.
Proof.
  destruct v; discriminate || injection 1 as <-; reflexivity.
Qed.

Lemma pack_inj__v (v : val) M :
  pack tt M = inj__v v -> exists m, v = pack__v m /\ M = inj__v m.
Proof.
  destruct v; cbn; discriminate || injection 1 as ->; eauto.
Qed.

Lemma ttt_inj__v (v : val) :
  ttt = inj__v v -> v = ttt__v.
Proof.
  destruct v; discriminate || reflexivity.
Qed.

Lemma bewl_inj__v (v : val) b :
  bewl b = inj__v v -> v = bewl__v b.
Proof.
  destruct v; discriminate || injection 1 as <-; reflexivity.
Qed.

Lemma int_inj__v (v : val) z :
  int z = inj__v v -> v = int__v z.
Proof.
  destruct v; discriminate || injection 1 as <-; reflexivity.
Qed.

Lemma tuple_inj__v (v : val) M N :
  `(M, N)`%rtrm = inj__v v -> exists m n, v = `(m, n)`%val /\ M = inj__v m /\ N = inj__v n.
Proof.
  destruct v; discriminate || injection 1 as -> ->; eauto.
Qed.

Lemma inlr_inj__v (v : val) lr M :
  inlr lr M = inj__v v -> exists m, v = inlr__v (bool_of_sum lr) m /\ M = inj__v m.
Proof.
  destruct v; discriminate || injection 1 as -> ->; autorewrite with core; eauto.
Qed.

Ltac destr_inj__v :=
  lazymatch goal with
  | H: inj__v _ = inj__v _ |- _ => apply inj_inj__v in H as ->
  | H: (`λ _)%rtrm = inj__v _ |- _ => apply abs_inj__v in H as ->
  | H: (Λ _)%rtrm  = inj__v _ |- _ => apply tabs_inj__v in H as ->
  | H: pack _ _ = inj__v _ |- _ => apply pack_inj__v in H as (? & -> & ->)
  | H: ttt = inj__v _ |- _ => apply ttt_inj__v in H as ->
  | H: bewl _ = inj__v _ |- _ => apply bewl_inj__v in H as ->
  | H: int _ = inj__v _ |- _ => apply int_inj__v in H as ->
  | H: `(_,_)`%rtrm = inj__v _ |- _ => apply tuple_inj__v in H as (? & ? & -> & -> & ->)
  | H: inlr _ _ = inj__v _ |- _ => apply inlr_inj__v in H as (? & -> & ->)
  end.
Local Hint Extern 5 => destr_inj__v : core.

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

Definition letin_not_val M N (v : val) :
  letin M N <> inj__v v.
Proof.
  destruct v; cbn; discriminate.
Qed.

Lemma bewl1_not_val f M v :
  bewl1 f M <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma bewl2_not_val f M N v :
  bewl2 f M N <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma int1_not_val f M v :
  int1 f M <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma int2_not_val f M N v :
  int2 f M N <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma cmp_not_val f M N v :
  cmp f M N <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma cond_not_val L M N v:
  cond L M N <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma proj_not_val b M v :
  proj b M <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Lemma mtch_not_val L M N v :
  mtch L M N <> inj__v v.
Proof.
  destruct v; discriminate.
Qed.

Ltac solve_not_val :=
  lazymatch goal with
  | H: ident _ = inj__v _ |- _ => apply ident_not_val in H
  | H: app _ _ = inj__v _ |- _ => apply app_not_val in H
  | H: (_ [-])%rtrm = inj__v _ |- _ => apply tapp_not_val in H
  | H: unpack _ _ = inj__v _ |- _ => apply unpack_not_val in H
  | H: letin _ _ = inj__v _ |- _ => apply letin_not_val in H
  | H: bewl1 _ _ = inj__v _ |- _ => apply bewl1_not_val in H
  | H: bewl2 _ _ _ = inj__v _ |- _ => apply bewl2_not_val in H
  | H: int1 _ _ = inj__v _ |- _ => apply int1_not_val in H
  | H: int2 _ _ _ = inj__v _ |- _ => apply int2_not_val in H
  | H: cmp _ _ _ = inj__v _ |- _ => apply cmp_not_val in H
  | H: cond _ _ _ = inj__v _ |- _ => apply cond_not_val in H
  | H: proj _ _ = inj__v _ |- _ => apply proj_not_val in H
  | H: mtch _ _ _ = inj__v _ |- _ => apply mtch_not_val in H
  end;
  contradiction.
Local Hint Extern 0 => solve_not_val : core.

Inductive ktx :=
| hole
| app__l (K : ktx) (v : val)
| app__r (M : rtrm) (K : ktx)
| tapp__k (K : ktx)
| pack__k (K : ktx)
| unpack__k (K : ktx) (N : rtrm)
| letin__k (K : ktx) (N : rtrm)
| bewl1__k (f : bool -> bool) (K : ktx)
| bewl2__l (f : bool -> bool -> bool) (K : ktx) (v : val)
| bewl2__r (f : bool -> bool -> bool) (M : rtrm) (K : ktx)
| int1__k (f : Z -> Z) (K : ktx)
| int2__l (f : Z -> Z -> Z) (K : ktx) (v : val)
| int2__r (f : Z -> Z -> Z) (M : rtrm) (K : ktx)
| cmp__l (f : Z -> Z -> bool) (K : ktx) (v : val)
| cmp__r (f : Z -> Z -> bool) (M : rtrm) (K : ktx)
| cond__k (K : ktx) (M N : rtrm)
| tuple__l (K : ktx) (v : val)
| tuple__r (M : rtrm) (K : ktx)
| proj__k (b : bool) (K : ktx)
| inlr__k (lr : bool) (K : ktx)
| mtch__k (K : ktx) (M N : rtrm)
.

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
  | letin__k K N  => letin (K [[ M ]]) N
  | bewl1__k f K  => bewl1 f (K [[ M ]])
  | bewl2__l f K v => bewl2 f (K [[ M ]]) $ inj__v v
  | bewl2__r f N K => bewl2 f N (K [[ M ]])
  | int1__k f K    => int1 f (K [[ M ]])
  | int2__l f K v  => int2 f (K [[ M ]]) $ inj__v v
  | int2__r f N K  => int2 f N (K [[ M ]])
  | cmp__l f K v   => cmp f (K [[ M ]]) $ inj__v v
  | cmp__r f N K   => cmp f N (K [[ M ]])
  | cond__k K L N  => cond (K [[ M ]]) L N
  | tuple__l K v   => tuple (K [[ M ]]) $ inj__v v
  | tuple__r N K   => tuple N (K [[ M ]])
  | proj__k b K    => proj b (K [[ M ]])
  | inlr__k b K    => inlr (sum_of_bool__tt b) (K [[ M ]])
  | mtch__k K L N  => mtch (K [[ M ]]) L N
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
  | letin__k K N  => letin__k (K `∘ K') N
  | bewl1__k f K  => bewl1__k f (K `∘ K')
  | bewl2__l f K v => bewl2__l f (K `∘ K') v
  | bewl2__r f N K => bewl2__r f N (K `∘ K')
  | int1__k f K    => int1__k f (K `∘ K')
  | int2__l f K v  => int2__l f (K `∘ K') v
  | int2__r f N K  => int2__r f N (K `∘ K')
  | cmp__l f K v   => cmp__l f (K `∘ K') v
  | cmp__r f N K   => cmp__r f N (K `∘ K')
  | cond__k K L N  => cond__k (K `∘ K') L N
  | tuple__l K v   => tuple__l (K `∘ K') v
  | tuple__r N K   => tuple__r N (K `∘ K')
  | proj__k b K    => proj__k b (K `∘ K')
  | inlr__k b K    => inlr__k b (K `∘ K')
  | mtch__k K L N  => mtch__k (K `∘ K') L N
  end
where "K1 '`∘' K2" := (comp__k K1 K2).

Lemma fill_comp__k K K' M :
  ((K `∘ K') [[ M ]])%rtrm = (K [[ K' [[ M ]] ]])%rtrm.
Proof.
  induction K; cbn; f_equal; auto.
Qed.

Reserved Infix "~>b" (at level 80, no associativity).

Variant step__b : rtrm -> rtrm -> Prop :=
  | step_abs__b M (n : val) :
    app (`λ M) (inj__v n) ~>b M.[ inj__v n /]
  | step_tabs__b M :
    (Λ M) [-] ~>b M
  | step_unpack__b (v : val) N :
    unpack (pack tt (inj__v v)) N ~>b N.[ inj__v v /]
  | step_letin__b (v : val) N :
    letin (inj__v v) N ~>b N.[ inj__v v /]
  | step_bewl1__b f b :
    bewl1 f (bewl b) ~>b bewl (f b)
  | step_bewl2__b f b1 b2 :
    bewl2 f (bewl b1) (bewl b2) ~>b bewl (f b1 b2)
  | step_int1__b f z :
    int1 f (int z) ~>b int (f z)
  | step_int2__b f z1 z2 :
    int2 f (int z1) (int z2) ~>b int (f z1 z2)
  | step_cmp__b f z1 z2 :
    cmp f (int z1) (int z2) ~>b bewl (f z1 z2)
  | step_cond__b b M N :
    cond (bewl b) M N ~>b if b then M else N
  | step_proj__b b (v1 v2 : val) :
    proj b `(inj__v v1, inj__v v2)` ~>b if b then v1 else v2
  | step_mtch__b lr (v : val) M N :
    mtch (inlr lr (inj__v v)) M N ~>b if lr then M.[inj__v v/] else N.[inj__v v/]
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
  induction K; intros []; cbn; try discriminate;
    try (intros ->; auto; assumption).
  - injection 1 as hv. eauto.
  - injection 1 as (peter & ->)%IHK <-%inj_inj__v. eauto.
  - injection 1 as -> (johnny & ->)%IHK. eauto.
  - injection 1 as <-%inj_sum_of_bool__tt (rudy & ->)%IHK. eauto.
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
  (K [[ M ]])%rtrm ~> (K [[ N ]])%rtrm.
Proof.
  inversion 1; subst.
  do 2 rewrite <- fill_comp__k.
  eauto.
Qed.

Local Hint Resolve ctx_lift : core.

Lemma step_abs M (n : val) :
  app (`λ M) (inj__v n) ~> M.[ inj__v n /].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_abs : core.

Lemma step_tabs M :
  (Λ M) [-] ~> M.
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_tabs : core.

Lemma unpack_pack (v : val) N :
  unpack (pack tt (inj__v v)) N ~> N.[ inj__v v /].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve unpack_pack : core.

Lemma step_letin (v : val) N :
  letin (inj__v v) N ~> N.[inj__v v/].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_letin : core.

Lemma step_bewl1 f b :
  bewl1 f (bewl b) ~> bewl (f b).
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_bewl1 : core.

Lemma step_bewl2 f b1 b2 :
  bewl2 f (bewl b1) (bewl b2) ~> (bewl (f b1 b2)).
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_bewl2 : core.

Lemma step_int1 f z :
  int1 f (int z) ~> int (f z).
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_int1 : core.

Lemma step_int2 f z1 z2 :
  int2 f (int z1) (int z2) ~> int (f z1 z2).
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_int2 : core.

Lemma step_cmp f z1 z2 :
  cmp f (int z1) (int z2) ~> bewl (f z1 z2).
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_cmp : core.

Lemma step_cond b M N :
  cond (bewl b) M N ~> if b then M else N.
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_cond : core.

Lemma step_proj b v1 v2 :
  proj b `(inj__v v1, inj__v v2)` ~> if b then v1 else v2.
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_proj : core.

Lemma step_mtch lr v M N :
  mtch (inlr lr (inj__v v)) M N ~> if lr then M.[inj__v v/] else N.[inj__v v/].
Proof.
  apply step_ktx with (K:=hole). eauto.
Qed.

Local Hint Resolve step_mtch : core.

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

Lemma step_letin__l M M' N :
  M ~> M' ->
  letin M N ~> letin M' N.
Proof.
  replace (letin M N) with (letin__k hole N [[ M ]])%rtrm by reflexivity.
  replace (letin M' N) with (letin__k hole N [[ M' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_letin__l : core.

Lemma step_bewl1__i f M M' :
  M ~> M' ->
  bewl1 f M ~> bewl1 f M'.
Proof.
  replace (bewl1 f M) with (bewl1__k f hole [[ M ]])%rtrm by reflexivity.
  replace (bewl1 f M') with (bewl1__k f hole [[ M' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_bewl1__i : core.

Lemma step_bewl2__r f M N N' :
  N ~> N' ->
  bewl2 f M N ~> bewl2 f M N'.
Proof.
  replace (bewl2 f M N) with (bewl2__r f M hole [[ N ]])%rtrm by reflexivity.
  replace (bewl2 f M N') with (bewl2__r f M hole [[ N' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_bewl2__r : core.

Lemma step_bewl2__l f M M' (v : val) :
  M ~> M' ->
  bewl2 f M (inj__v v) ~> bewl2 f M' (inj__v v).
Proof.
  replace (bewl2 f M (inj__v v)) with (bewl2__l f hole v [[ M ]])%rtrm by reflexivity.
  replace (bewl2 f M' (inj__v v)) with (bewl2__l f hole v [[ M' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_bewl2__l : core.

Lemma step_int1__i f M M' :
  M ~> M' ->
  int1 f M ~> int1 f M'.
Proof.
  replace (int1 f M) with (int1__k f hole [[ M ]])%rtrm by reflexivity.
  replace (int1 f M') with (int1__k f hole [[ M' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_int1__i : core.

Lemma step_int2__r f M N N' :
  N ~> N' ->
  int2 f M N ~> int2 f M N'.
Proof.
  replace (int2 f M N) with (int2__r f M hole [[ N ]])%rtrm by reflexivity.
  replace (int2 f M N') with (int2__r f M hole [[ N' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_int2__r : core.

Lemma step_int2__l f M M' (v : val) :
  M ~> M' ->
  int2 f M (inj__v v) ~> int2 f M' (inj__v v).
Proof.
  replace (int2 f M (inj__v v)) with (int2__l f hole v [[ M ]])%rtrm by reflexivity.
  replace (int2 f M' (inj__v v)) with (int2__l f hole v [[ M' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_int2__l : core.

Lemma step_cmp__l f M M' (v : val) :
  M ~> M' ->
  cmp f M (inj__v v) ~> cmp f M' (inj__v v).
Proof.
  replace (cmp f M (inj__v v)) with (cmp__l f hole v [[ M ]])%rtrm by reflexivity.
  replace (cmp f M' (inj__v v)) with (cmp__l f hole v [[ M' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_cmp__l : core.

Lemma step_cmp__r f M N N' :
  N ~> N' ->
  cmp f M N ~> cmp f M N'.
Proof.
  replace (cmp f M N) with (cmp__r f M hole [[ N ]])%rtrm by reflexivity.
  replace (cmp f M N') with (cmp__r f M hole [[ N' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_cmp__r : core.

Lemma step_cond__l L L' M N :
  L ~> L' ->
  cond L M N ~> cond L' M N.
Proof.
  replace (cond L M N) with (cond__k hole M N [[ L ]])%rtrm by reflexivity.
  replace (cond L' M N) with (cond__k hole M N [[ L' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_cond__l : core.

Lemma step_tuple__l M M' (v : val) :
  M ~> M' ->
  `(M, inj__v v)` ~> `(M', inj__v v)`.
Proof.
  replace (tuple M (inj__v v)) with (tuple__l hole v [[ M ]])%rtrm by reflexivity.
  replace (tuple M' (inj__v v)) with (tuple__l hole v [[ M' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_tuple__l : core.

Lemma step_tuple__r M N N' :
    N ~> N' ->
    `(M, N)` ~> `(M, N')`.
Proof.
  replace (tuple M N) with (tuple__r M hole [[ N ]])%rtrm by reflexivity.
  replace (tuple M N') with (tuple__r M hole [[ N' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_tuple__r : core.

Lemma step_proj__i b M M' :
  M ~> M' ->
  proj b M ~> proj b M'.
Proof.
  replace (proj b M) with (proj__k b hole [[ M ]])%rtrm by reflexivity.
  replace (proj b M') with (proj__k b hole [[ M' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_proj__i : core.

Lemma step_inlr lr M M' :
  M ~> M' ->
  inlr lr M ~> inlr lr M'.
Proof.
  replace (inlr lr M) with (inlr__k (bool_of_sum lr) hole [[ M ]])%rtrm.
  2:{ cbn. rewrite sum_of_bool_of_sum__tt. reflexivity. }
  replace (inlr lr M') with (inlr__k (bool_of_sum lr) hole [[ M' ]])%rtrm.
  2:{ cbn. rewrite sum_of_bool_of_sum__tt. reflexivity. }
  eauto.
Qed.

Local Hint Resolve step_inlr : core.

Lemma step_mtch__l L L' M N :
  L ~> L' ->
  mtch L M N ~> mtch L' M N.
Proof.
  replace (mtch L M N) with (mtch__k hole M N [[ L ]])%rtrm by reflexivity.
  replace (mtch L' M N) with (mtch__k hole M N [[ L' ]])%rtrm by reflexivity.
  eauto.
Qed.

Local Hint Resolve step_mtch__l : core.
  
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
| wf_Unit :
  Δ ⊢wf Unit
| wf_Bool :
  Δ ⊢wf Bool
| wf_Int :
  Δ ⊢wf Int
| wf_Exi A :
  S Δ ⊢wf A ->
  Δ ⊢wf `∃ A
| wf_Prd A B :
  Δ ⊢wf A ->
  Δ ⊢wf B ->
  Δ ⊢wf (A × B)
| wf_Sum A B :
  Δ ⊢wf A ->
  Δ ⊢wf B ->
  Δ ⊢wf (A `+ B)
where "Δ '⊢wf' τ" := (wf_typ Δ%nat τ%typ) : type_scope.

Local Hint Constructors wf_typ : core.

Definition up__Γ (Γ : list typ) : list typ:= subst (ren S) <$> Γ.

Definition sum_typ_of_sum (A : typ) (lr : typ + typ) : typ :=
  match lr with
  | inl B => (A `+ B)%typ
  | inr B => (B `+ A)%typ
  end.

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
| judge_letin__s M N A B :
  Δ `;; Γ ⊢ M `: A ->
  Δ `;; A :: Γ ⊢ N `: B ->
  Δ `;; Γ ⊢ letin M N `: B
| judge_ttt__s :
  Δ `;; Γ ⊢ ttt `: Unit
| judge_bewl__s b :
  Δ `;; Γ ⊢ bewl b `: Bool
| judge_bewl1__s f M :
  Δ `;; Γ ⊢ M `: Bool ->
  Δ `;; Γ ⊢ bewl1 f M `: Bool
| judge_bewl2__s f M N :
  Δ `;; Γ ⊢ M `: Bool ->
  Δ `;; Γ ⊢ N `: Bool ->
  Δ `;; Γ ⊢ bewl2 f M N `: Bool
| judge_int__s z :
  Δ `;; Γ ⊢ int z `: Int
| judge_int1__s f M :
  Δ `;; Γ ⊢ M `: Int ->
  Δ `;; Γ ⊢ int1 f M `: Int
| judge_int2__s f M N :
  Δ `;; Γ ⊢ M `: Int ->
  Δ `;; Γ ⊢ N `: Int ->
  Δ `;; Γ ⊢ int2 f M N `: Int
| judge_cmp__s f M N :
  Δ `;; Γ ⊢ M `: Int ->
  Δ `;; Γ ⊢ N `: Int ->
  Δ `;; Γ ⊢ cmp f M N `: Bool
| judge_cond__s L M N A :
  Δ `;; Γ ⊢ L `: Bool ->
  Δ `;; Γ ⊢ M `: A ->
  Δ `;; Γ ⊢ N `: A ->
  Δ `;; Γ ⊢ cond L M N `: A
| judge_tuple__s M N A B :
  Δ `;; Γ ⊢ M `: A ->
  Δ `;; Γ ⊢ N `: B ->
  Δ `;; Γ ⊢ `(M, N)` `: (A × B)
| judge_proj__s b M A B :
  Δ `;; Γ ⊢ M `: (A × B) ->
  Δ `;; Γ ⊢ proj b M `: if b then A else B
| judge_inlr__s lr M A B :
  Forall_sum (eq B) (eq A) lr ->
  Δ ⊢wf (if lr then B else A) ->
  Δ `;; Γ ⊢ M `: (if lr then A else B) ->
  Δ `;; Γ ⊢ inlr lr M `: (A `+ B)
| judge_mtch__s L M N A B C :
  Δ `;; Γ ⊢ L `: (A `+ B) ->
  Δ `;; A :: Γ ⊢ M `: C ->
  Δ `;; B :: Γ ⊢ N `: C ->
  Δ `;; Γ ⊢ mtch L M N `: C
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
| judge_letin__r M N A B :
  Δ `; Γ ⊢ M `: A ->
  Δ `; A :: Γ ⊢ N `: B ->
  Δ `; Γ ⊢ letin M N `: B
| judge_ttt__r :
  Δ `; Γ ⊢ ttt `: Unit
| judge_bewl__r b :
  Δ `; Γ ⊢ bewl b `: Bool
| judge_bewl1__r f M :
  Δ `; Γ ⊢ M `: Bool ->
  Δ `; Γ ⊢ bewl1 f M `: Bool
| judge_bewl2__r f M N :
  Δ `; Γ ⊢ M `: Bool ->
  Δ `; Γ ⊢ N `: Bool ->
  Δ `; Γ ⊢ bewl2 f M N `: Bool
| judge_int__r z :
  Δ `; Γ ⊢ int z `: Int
| judge_int1__r f M :
  Δ `; Γ ⊢ M `: Int ->
  Δ `; Γ ⊢ int1 f M `: Int
| judge_int2__r f M N :
  Δ `; Γ ⊢ M `: Int ->
  Δ `; Γ ⊢ N `: Int ->
  Δ `; Γ ⊢ int2 f M N `: Int
| judge_cmp__r f M N :
  Δ `; Γ ⊢ M `: Int ->
  Δ `; Γ ⊢ N `: Int ->
  Δ `; Γ ⊢ cmp f M N `: Bool
| judge_cond__r L M N A :
  Δ `; Γ ⊢ L `: Bool ->
  Δ `; Γ ⊢ M `: A ->
  Δ `; Γ ⊢ N `: A ->
  Δ `; Γ ⊢ cond L M N `: A
| judge_tuple__r M N A B :
  Δ `; Γ ⊢ M `: A ->
  Δ `; Γ ⊢ N `: B ->
  Δ `; Γ ⊢ `(M, N)` `: (A × B)
| judge_proj__r b M A B :
  Δ `; Γ ⊢ M `: (A × B) ->
  Δ `; Γ ⊢ proj b M `: if b then A else B
| judge_inlr__r (lr : unit + unit) M A B :
  Δ ⊢wf (if lr then B else A) ->
  Δ `; Γ ⊢ M `: (if lr then A else B) ->
  Δ `; Γ ⊢ inlr lr M `: (A `+ B)
| judge_mtch__r L M N A B C :
  Δ `; Γ ⊢ L `: (A `+ B) ->
  Δ `; A :: Γ ⊢ M `: C ->
  Δ `; B :: Γ ⊢ N `: C ->
  Δ `; Γ ⊢ mtch L M N `: C
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

  Lemma inv_judge_letin__r M N B :
    Δ `; Γ ⊢ letin M N `: B ->
    exists A, Δ `; Γ ⊢ M `: A /\ Δ `; A :: Γ ⊢ N `: B.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_ttt__r C :
    Δ `; Γ ⊢ ttt `: C -> C = Unit.
  Proof.
    inversion 1; subst; reflexivity.
  Qed.

  Lemma inv_judge_bewl__r b C :
    Δ `; Γ ⊢ bewl b `: C -> C = Bool.
  Proof.
    inversion 1; subst; reflexivity.
  Qed.

  Lemma inv_judge_bewl1__r f M C :
    Δ `; Γ ⊢ bewl1 f M `: C ->
    C = Bool /\ Δ `; Γ ⊢ M `: Bool.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_bewl2__r f M N C :
    Δ `; Γ ⊢ bewl2 f M N `: C ->
    C = Bool /\ Δ `; Γ ⊢ M `: Bool /\ Δ `; Γ ⊢ N `: Bool.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_int__r z C :
    Δ `; Γ ⊢ int z `: C -> C = Int.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_int1__r f M C :
    Δ `; Γ ⊢ int1 f M `: C ->
    C = Int /\ Δ `; Γ ⊢ M `: Int.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_int2__r f M N C :
    Δ `; Γ ⊢ int2 f M N `: C ->
    C = Int /\ Δ `; Γ ⊢ M `: Int /\ Δ `; Γ ⊢ N `: Int.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_cmp__r f M N C :
    Δ `; Γ ⊢ cmp f M N `: C ->
    C = Bool /\ Δ `; Γ ⊢ M `: Int /\ Δ `; Γ ⊢ N `: Int.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_cond__r L M N A :
    Δ `; Γ ⊢ cond L M N `: A ->
    Δ `; Γ ⊢ L `: Bool /\ Δ `; Γ ⊢ M `: A /\ Δ `; Γ ⊢ N `: A.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_tuple__r M N C :
    Δ `; Γ ⊢ `(M, N)` `: C ->
    exists A B, C = (A × B)%typ /\ Δ `; Γ ⊢ M `: A /\ Δ `; Γ ⊢ N `: B.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_proj__r b M C :
    Δ `; Γ ⊢ proj b M `: C ->
    exists A B, C = (if b then A else B) /\ Δ `; Γ ⊢ M `: (A × B).
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_inlr__r lr M C :
    Δ `; Γ ⊢ inlr lr M `: C ->
    exists A B, C = (A `+ B)%typ /\ Δ ⊢wf (if lr then B else A) /\ Δ `; Γ ⊢ M `: if lr then A else B.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma inv_judge_mtch__r L M N C :
    Δ `; Γ ⊢ mtch L M N `: C ->
    exists A B, Δ `; Γ ⊢ L `: (A `+ B) /\ Δ `; A :: Γ ⊢ M `: C /\ Δ `; B :: Γ ⊢ N `: C.
  Proof.
    inversion 1; subst; eauto.
  Qed.
End inv.

Section map_trm.
  Context {A B : Type}.
  Variable f : A -> B.

  Fixpoint map_trm (M : trm A) : trm B :=
    match M with
    | ident x    => ident x
    | abs a M    => abs (f a) $ map_trm M
    | app M N    => app (map_trm M) $ map_trm N
    | tabs M     => tabs $ map_trm M
    | tapp M a   => tapp (map_trm M) $ f a
    | pack a M   => pack (f a) $ map_trm M
    | unpack M N => unpack (map_trm M) $ map_trm N
    | letin M N  => letin (map_trm M) $ map_trm N
    | ttt        => ttt
    | bewl b     => bewl b
    | bewl1 f M  => bewl1 f $ map_trm M
    | bewl2 f M N => bewl2 f (map_trm M) $ map_trm N
    | int z       => int z
    | int1 f M    => int1 f $ map_trm M
    | int2 f M N  => int2 f (map_trm M) $ map_trm N
    | cmp f M N   => cmp f (map_trm M) $ map_trm N
    | cond L M N  => cond (map_trm L) (map_trm M) $ map_trm N
    | tuple M N   => tuple (map_trm M) $ map_trm N
    | proj b M    => proj b $ map_trm M
    | inlr lr M   => inlr (sum_map f f lr) $ map_trm M
    | mtch L M N  => mtch (map_trm L) (map_trm M) $ map_trm N
    end.

  Lemma map_trm_rename M ρ :
    map_trm M.[ren ρ] = (map_trm M).[ren ρ].
  Proof.
    induction M in ρ |- *; cbn; asimpl; try (f_equal; eauto; reflexivity).
  Qed.
End map_trm.

Definition erase : strm -> rtrm := map_trm (fun _ => tt).

Local Hint Constructors judge__s : core.
Local Hint Constructors judge__r : core.

Lemma judge_erase Δ Γ M A :
  Δ `;; Γ ⊢ M `: A ->
  Δ `;  Γ ⊢ erase M `: A.
Proof.
  induction 1; cbn; eauto.
  - constructor; destruct lr; cbn in *; eauto.
Qed.

Section canon.
  Variable Δ : nat.
  Variable Γ : list typ.
  
  Lemma canon_fun (v : val) A B :
    Δ `; Γ ⊢ v `: (A `→ B)%typ ->
    exists N, v = (`λ N)%val.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma canon_uni (v : val) A :
    Δ `; Γ ⊢ v `: (`∀ A)%typ ->
    exists M, v = (Λ M)%val.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma canon_exi (v : val) A :
    Δ `; Γ ⊢ v `: (`∃ A) ->
    exists v', v = pack__v v'.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma canon_unit (v : val) :
    Δ `; Γ ⊢ v `: Unit -> v = ttt__v.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma canon_bool (v : val) :
    Δ `; Γ ⊢ v `: Bool ->
    exists b, v = bewl__v b.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma canon_int (v : val) :
    Δ `; Γ ⊢ v `: Int ->
    exists z, v = int__v z.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma canon_prd (v : val) A B :
    Δ `; Γ ⊢ v `: (A × B)%typ ->
    exists m n, v = `(m, n)`%val /\ Δ `; Γ ⊢ m `: A /\ Δ `; Γ ⊢ n `: B.
  Proof.
    inversion 1; subst; eauto 6.
  Qed.

  Lemma canon_sum (v : val) A B :
    Δ `; Γ ⊢ v `: (A `+ B)%typ ->
    exists b m, v = inlr__v b m /\ Δ ⊢wf (if b then B else A) /\ Δ `; Γ ⊢ m `: if b then A else B.
  Proof.
    inversion 1; subst; eauto.
    destr_inj__v.
    do 2 eexists; split; try reflexivity.
    destruct lr; cbn in *; eauto.
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
    destruct IHjudge__r2 as [(N' & HN) | (n & ->)].
    + exists (app M N'). auto.
    + destruct IHjudge__r1 as [(M' & HM) | (m & ->)].
      * exists (app M' (inj__v n)). auto.
      * apply canon_fun in H as [M ->]. cbn. eauto.
  - right; auto.
  - left. destruct IHjudge__r as [(M' & HM) | (m & ->)].
    + exists (M' [-])%rtrm. auto.
    + apply canon_uni in H0 as [M ->]. cbn. eauto.
  - destruct IHjudge__r as [(M' & HM) | (m & ->)].
    + left. exists (pack tt M'). auto.
    + right. exists (pack__v m). auto.
  - clear IHjudge__r2. left.
    destruct IHjudge__r1 as [(M' & HM) | (m & ->)].
    + exists (unpack M' N). auto.
    + apply canon_exi in H0 as [v ->].
      exists N.[(inj__v v) /]. cbn. auto.
  - clear IHjudge__r2. left.
    destruct IHjudge__r1 as [(M' & HM) | (m & ->)].
    + exists (letin M' N). auto.
    + eauto.
  - right. auto.
  - right. auto.
  - left.
    destruct IHjudge__r as [(M' & HM) | (m & ->)].
    + exists (bewl1 f M'). auto.
    + apply canon_bool in H as [b ->]. cbn. eauto.
  - left.
    destruct IHjudge__r2 as [(N' & HN) | (n & ->)].
    + exists (bewl2 f M N'). auto.
    + destruct IHjudge__r1 as [(M' & HM) | (m & ->)].
      * exists (bewl2 f M' (inj__v n)). auto.
      * apply canon_bool in H as (b1 & ->).
        apply canon_bool in H0 as (b2 & ->). cbn. eauto.
  - right. auto.
  - left.
    destruct IHjudge__r as [(M' & HM) | (m & ->)].
    + exists (int1 f M'). auto.
    + apply canon_int in H as (z & ->). cbn. eauto.
  - left.
    destruct IHjudge__r2 as [(N' & HN) | (n & ->)].
    + exists (int2 f M N'). eauto.
    + destruct IHjudge__r1 as [(M' & HM) | (m & ->)].
      * exists (int2 f M' (inj__v n)). eauto.
      * apply canon_int in H, H0.
        destruct H as (z1 & ->).
        destruct H0 as (z2 & ->).
        cbn. eauto.
  - left.
    destruct IHjudge__r2 as [(N' & HN) | (n & ->)].
    + exists (cmp f M N'). eauto.
    + destruct IHjudge__r1 as [(M' & HM) | (m & ->)].
      * exists (cmp f M' (inj__v n)). eauto.
      * apply canon_int in H, H0.
        destruct H as (z1 & ->).
        destruct H0 as (z2 & ->).
        cbn. eauto.
  - left.
    destruct IHjudge__r1 as [(L' & HL) | (l & ->)].
    + exists (cond L' M N). eauto.
    + apply canon_bool in H as [b ->]. cbn. eauto.
  - destruct IHjudge__r2 as [(N' & HN) | (n & ->)].
    + left. exists `(M, N')`%rtrm. auto.
    + destruct IHjudge__r1 as [(M' & HM) | (m & ->)].
      * left. exists `(M', inj__v n)`%rtrm. auto.
      * right. auto.
  - left.
    destruct IHjudge__r as [(M' & HM) | (m & ->)].
    + exists (proj b M'). eauto.
    + apply canon_prd in H as (v1 & v2 & -> & Hv1 & Hv2).
      cbn. eauto.
  - destruct IHjudge__r as [(M' & HM) | (m & ->)].
    + left. exists (inlr lr M'). eauto.
    + right. eauto.
  - clear IHjudge__r2 IHjudge__r3. left.
    destruct IHjudge__r1 as [(L' & HL) | (l & ->)].
    + exists (mtch L' M N). eauto.
    + apply canon_sum in H as (b & m & -> & Hwf & Hm).
      cbn. eauto.
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

Lemma wf_tsubst_wf_typ_inv Δ1 Δ2 σ A :
  (∀ α : nat, Δ2 ⊢wf σ α -> α < Δ1) ->
  Δ2 ⊢wf A.[σ] ->
  Δ1 ⊢wf A.
Proof.
  unfold wf_tsubst.
  intros Hwfinv.
  induction A in Δ1, Δ2, σ, Hwfinv |- *; asimpl; eauto.
  - inversion 1; subst. eauto.
  - inversion 1; subst.
Abort.

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

Lemma distr_if_suml {A B U V} (f : A -> B) (b : U + V) (x y : A) :
  f (if b then x else y) = if b then f x else f y.
Proof.
  destruct b; reflexivity.
Qed.

Lemma distr_if_boolr {A B} (f g : A -> B) (b : bool) (a : A) :
  (if b then f else g) a = if b then f a else g a.
Proof.
  destruct b; reflexivity.
Qed.

Lemma distr_if_sumr {A B U V} (f g : A -> B) (b : U + V) (a : A) :
  (if b then f else g) a = if b then f a else g a.
Proof.
  destruct b; reflexivity.
Qed.

Lemma judge_tsubst__r Δ1 Δ2 Γ M A σ :
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
  - asimpl in *. rewrite distr_if_booll.
    eauto.
  - setoid_rewrite distr_if_suml in IHjudge__r.
    constructor.
    + rewrite <- distr_if_suml. eauto.
    + eauto.
Qed.

Local Hint Resolve judge_tsubst__r : core.

(* Lemma judge_tsubst__s Δ1 Δ2 Γ M A σ : *)
(*   wf_tsubst Δ1 Δ2 σ -> *)
(*   Δ1 `;; Γ ⊢ M `: A -> *)
(*   Δ2 `;; (subst σ) <$> Γ ⊢ M `: A.[σ]. *)
(* Proof. *)
(*   intros Hσ. *)
(*   induction 1 in Hσ, σ, Δ2 |- *; cbn; eauto. *)
(*   - constructor. *)
(*     rewrite list_lookup_fmap. *)
(*     apply fmap_Some_2. assumption. *)
(*   - Search judge__s abs. *)
(*     apply judge_abs__s. *)
(*     constructor. *)
(*     rewrite up_subst. eauto. *)
(*   - replace (A.[B/].[σ]) with (A.[up σ].[B.[σ]/]) *)
(*       by by asimpl. eauto. *)
(*   - apply judge_pack__r with (B := subst σ B); eauto. *)
(*     replace (A.[up σ].[B.[ σ]/]) with (A.[B/].[σ]) *)
(*       by by asimpl. eauto. *)
(*   - apply judge_unpack__r with (A:=A.[up σ]); eauto. *)
(*     rewrite up_subst. asimpl in IHjudge__r2. *)
(*     replace (B.[σ].[ren S]) with (B.[ren S].[up σ]) *)
(*       by by asimpl. eauto. *)
(*   - asimpl in *. rewrite distr_if_booll. *)
(*     eauto. *)
(*   - setoid_rewrite distr_if_suml in IHjudge__r. *)
(*     constructor. *)
(*     + rewrite <- distr_if_suml. eauto. *)
(*     + eauto. *)
(* Qed. *)

(* Local Hint Resolve judge_tsubst__s : core. *)

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
  apply judge_tsubst__r with (Δ1 := Δ); eauto.
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

Lemma wf_judge__s Δ Γ M A :
  Δ `;; Γ ⊢ M `: A ->
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
  - inversion IHjudge__s1; subst. assumption.
  - inversion IHjudge__s; subst. eauto.
  - constructor.
Abort.

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
  - intros (B & HM & HN)%inv_judge_letin__r.
    apply judge_subst_single with (A:=B); auto.
  - intros [-> Hb]%inv_judge_bewl1__r. auto.
  - intros (-> & Hb1 & Hb2)%inv_judge_bewl2__r. auto.
  - intros [-> Hz]%inv_judge_int1__r. auto.
  - intros (-> & Hz1 & Hz2)%inv_judge_int2__r. auto.
  - intros (-> & Hz1 & Hz2)%inv_judge_cmp__r. auto.
  - intros (Hb & HM & HN)%inv_judge_cond__r.
    destruct b; auto.
  - intros (B & C & -> & (D & E & HDE & Hv1 & Hv2)%inv_judge_tuple__r)%inv_judge_proj__r.
    injection HDE as <- <-.
    destruct b; auto.
  - intros (B & C & (D & E & HDE & Hwf & Hv)%inv_judge_inlr__r & HM & HN)%inv_judge_mtch__r.
    injection HDE as <- <-.
    destruct lr; eauto.
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
  - eauto using progress_rtrm.
  - pose proof preservation _ _ _ H HM as Hy.
    auto.
Qed.

Reserved Infix "⇓" (at level 80, no associativity).

Inductive big : rtrm -> val -> Prop :=
| big_abs M :
  (`λ M)%rtrm ⇓ (`λ M)%val
| big_app (L M N : rtrm) m v :
  L ⇓ (`λ N)%val ->
  M ⇓ m ->
  N.[inj__v m/] ⇓ v ->
  app L M ⇓ v
| big_tabs M :
  (Λ M)%rtrm ⇓ (Λ M)%val
| big_tapp M N v :
  M ⇓ (Λ N)%val ->
  N ⇓ v ->
  (M [-])%rtrm ⇓ v
| big_pack M v :
  M ⇓ v ->
  pack tt M ⇓ pack__v v
| big_unpack M N m v :
  M ⇓ pack__v m ->
  N.[inj__v m/] ⇓ v ->
  unpack M N ⇓ v
| big_letin M N m n :
  M ⇓ m ->
  N.[inj__v m/] ⇓ n ->
  letin M N ⇓ n
| big_ttt :
  ttt ⇓ ttt__v
| big_bewl b :
  bewl b ⇓ bewl__v b
| big_bewl1 f M b :
  M ⇓ bewl__v b ->
  bewl1 f M ⇓ bewl__v (f b)
| big_bewl2 f M N x y :
  M ⇓ bewl__v x ->
  N ⇓ bewl__v y ->
  bewl2 f M N ⇓ bewl__v (f x y)
| big_int z :
  int z ⇓ int__v z
| big_int1 f M z :
  M ⇓ int__v z ->
  int1 f M ⇓ int__v (f z)
| big_int2 f M N m n :
  M ⇓ int__v m ->
  N ⇓ int__v n ->
  int2 f M N ⇓ int__v (f m n)
| big_cmp f M N m n :
  M ⇓ int__v m ->
  N ⇓ int__v n ->
  cmp f M N ⇓ bewl__v (f m n)
| big_cond L M N b v :
  L ⇓ bewl__v b ->
  (if b then M else N) ⇓ v ->
  cond L M N ⇓ v
| big_tuple M N m n :
  M ⇓ m ->
  N ⇓ n ->
  `(M, N)` ⇓ `(m, n)`
| big_proj b M x y :
  M ⇓ `(x, y)` ->
  proj b M ⇓ if b then x else y
| big_inlr lr M m :
  M ⇓ m ->
  inlr lr M ⇓ inlr__v (bool_of_sum lr) m
| big_mtch L M N b l v :
  L ⇓ inlr__v b l ->
  (if b then M else N).[inj__v l/] ⇓ v ->
  mtch L M N ⇓ v
where "M '⇓' v" := (big M%rtrm v%val) : type_scope.

Equations size__t : typ -> nat :=
| Ident _ := 1
| (A `→ B)%typ := 1 + size__t A + size__t B
| (`∀ A)%typ := 2 + size__t A
| (`∃ A)%typ := 2 + size__t A
| Unit := 1
| Bool := 1
| Int := 1
| (A × B)%typ := 1 + size__t A + size__t B
| (A `+ B)%typ := 1 + size__t A + size__t B
.

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
    exists M, v = (`λ M)%val /\ forall v, interp__t (inl v) A δ -> interp__t (inr M.[inj__v v/]) B δ
| (inl v), (`∀ A)%typ, δ :=
    exists M, v = (Λ M)%val /\ forall τ : sem__t, interp__t (inr M) A (τ .: δ)
| (inl v), (`∃ A)%typ, δ :=
    exists m, v = pack__v m /\ exists τ : sem__t,
        interp__t (inl m) A (τ .: δ)
| (inl v), Unit, δ := v = ttt__v
| (inl v), Bool, δ := exists b, v = bewl__v b
| (inl v), Int, δ := exists z, v = int__v z
| (inl v), (A × B)%typ, δ :=
    exists a b, v = `(a, b)`%val /\ interp__t (inl a) A δ /\ interp__t (inl b) B δ
| (inl v), (A `+ B)%typ, δ :=
    exists b m, v = inlr__v b m /\ interp__t (inl m) (if b then A else B) δ
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
  simp size__t.
  destruct b;
  lia.
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
  induction v; cbn; eauto.
  - replace lr with (bool_of_sum (sum_of_bool__tt lr)) at 2
      by (rewrite bool_of_sum_of_bool__tt; reflexivity).
    eauto.
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
    - destruct Hv as (a & b & -> & Ha & Hb). eauto 7.
    - destruct Hv as (b & m & -> & Hm).
      destruct b; eauto 7.
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

  Global Instance sub_iff_eq : subrelation iff eq.
  Proof.
    unfold subrelation.
  Abort.

  
  Global Instance sub_eq_impl : subrelation eq impl.
  Proof.
    unfold subrelation, impl.
    intros x y <-. auto.
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
    - split; intros (a & b & -> & Ha & Hb);
        do 2 eexists; split; eauto.
      + rewrite IHA1 in Ha.
        rewrite IHA2 in Hb. auto.
      + rewrite IHA1.
        rewrite IHA2. auto.
    - split; intros ([] & m & -> & Hm);
        do 2 eexists; split; eauto; cbn;
        revert Hm; rewrite IHA1 || rewrite IHA2; auto.
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
    - split; intros (a & b & -> & Ha & Hb); do 2 eexists; split; eauto;
        revert Ha Hb; rewrite <- IHA1; rewrite <- IHA2; auto.
    - split; intros ([] & m & -> & Hm); do 2 eexists; split; eauto;
        revert Hm; rewrite <- IHA1 || rewrite <- IHA2; auto.
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

  Lemma letin_compat M N A B :
    Γ ⊨ M `: A ->
    A :: Γ ⊨ N `: B ->
    Γ ⊨ letin M N `: B.
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

  Lemma ttt_compat :
    Γ ⊨ ttt `: Unit.
  Proof.
    intros δ γ HG.
    simp interp__t. cbn.
    eexists; split; eauto.
    simp interp__t. reflexivity.
  Qed.

  Lemma bewl_compat b :
    Γ ⊨ bewl b `: Bool.
  Proof.
    intros δ γ HG.
    simp interp__t. cbn.
    eexists; split; eauto.
    simp interp__t. eauto.
  Qed.

  Lemma bewl1_compat f M :
    Γ ⊨ M `: Bool ->
    Γ ⊨ bewl1 f M `: Bool.
  Proof.
    unfold sem_judge.
    intros HM δ γ HG.
    specialize HM with (1:=HG).
    simp interp__t in HM |- *.
    destruct HM as (v & HM & Hv).
    simp interp__t in Hv.
    destruct Hv as [b ->]. cbn.
    eexists; split; eauto.
    simp interp__t. eauto.
  Qed.

  Lemma bewl2_compat f M N :
    Γ ⊨ M `: Bool ->
    Γ ⊨ N `: Bool ->
    Γ ⊨ bewl2 f M N `: Bool.
  Proof.
    unfold sem_judge.
    intros HM HN δ γ HG. cbn.
    specialize HM with (1:=HG).
    specialize HN with (1:=HG).
    simp interp__t in HM, HN |- *.
    destruct HM as (m & HM & Hm).
    destruct HN as (n & HN & Hn).
    simp interp__t in Hm, Hn.
    destruct Hm as [b1 ->].
    destruct Hn as [b2 ->].
    eexists; split; eauto.
    simp interp__t. eauto.
  Qed.
  
  Lemma int_compat z :
    Γ ⊨ int z `: Int.
  Proof.
    intros δ γ HG.
    simp interp__t. cbn.
    eexists; split; eauto.
    simp interp__t. eauto.
  Qed.

  Lemma int1_compat f M :
    Γ ⊨ M `: Int ->
    Γ ⊨ int1 f M `: Int.
  Proof.
    unfold sem_judge.
    intros HM δ γ HG.
    specialize HM with (1:=HG).
    simp interp__t in HM |- *.
    destruct HM as (m & HM & Hm).
    simp interp__t in Hm.
    destruct Hm as (z & ->).
    cbn. eexists; split; eauto.
    simp interp__t. eauto.
  Qed.

  Lemma int2_compat f M N :
    Γ ⊨ M `: Int ->
    Γ ⊨ N `: Int ->
    Γ ⊨ int2 f M N `: Int.
  Proof.
    unfold sem_judge.
    intros HM HN δ γ HG.
    specialize HM with (1:=HG).
    specialize HN with (1:=HG).
    simp interp__t in HM, HN |- *.
    destruct HM as (m & HM & Hm).
    destruct HN as (n & HN & Hn).
    simp interp__t in Hm, Hn.
    destruct Hm as (z1 & ->).
    destruct Hn as (z2 & ->).
    cbn. eexists; split; eauto.
    simp interp__t. eauto.
  Qed.

  Lemma cmp_compat f M N :
    Γ ⊨ M `: Int ->
    Γ ⊨ N `: Int ->
    Γ ⊨ cmp f M N `: Bool.
  Proof.
    unfold sem_judge.
    intros HM HN δ γ HG.
    specialize HM with (1:=HG).
    specialize HN with (1:=HG).
    simp interp__t in HM, HN |- *.
    destruct HM as (m & HM & Hm).
    destruct HN as (n & HN & Hn).
    simp interp__t in Hm, Hn.
    destruct Hm as (z1 & ->).
    destruct Hn as (z2 & ->).
    cbn. eexists; split; eauto.
    simp interp__t. eauto.
  Qed.

  Lemma cond_compat L M N A :
    Γ ⊨ L `: Bool ->
    Γ ⊨ M `: A ->
    Γ ⊨ N `: A ->
    Γ ⊨ cond L M N `: A.
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
    cbn.
    exists (if b then m else n).
    split; eauto.
    - econstructor; eauto.
      destruct b; auto.
    - destruct b; auto.
  Qed.

  Lemma tuple_compat M N A B :
    Γ ⊨ M `: A ->
    Γ ⊨ N `: B ->
    Γ ⊨ `(M, N)` `: (A × B)%typ.
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

  Lemma proj_compat b M A B :
    Γ ⊨ M `: (A × B) ->
    Γ ⊨ proj b M `: if b then A else B.
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

  Lemma inlr_compat (lr : unit + unit) M A B :
    Γ ⊨ M `: (if lr then A else B) ->
    Γ ⊨ inlr lr M `: (A `+ B).
  Proof.
    unfold sem_judge.
    intros HM δ γ HG.
    specialize HM with (1:=HG).
    simp interp__t in HM |- *.
    destruct HM as (m & HM & Hm).
    cbn. exists (inlr__v (bool_of_sum lr) m).
    split; auto.
    simp interp__t.
    do 2 eexists; split; eauto.
    destruct lr; auto.
  Qed.

  Lemma mtch_compat L M N A B C :
    Γ ⊨ L `: (A `+ B) ->
    A :: Γ ⊨ M `: C ->
    B :: Γ ⊨ N `: C ->
    Γ ⊨ mtch L M N `: C.
  Proof.
    unfold sem_judge.
    intros HL HM HN δ γ HG.
    specialize HL with (1:=HG).
    simp interp__t in HL |- *.
    destruct HL as (l & HL & Hl).
    simp interp__t in Hl. cbn.
    destruct Hl as ([] & v & -> & Hv).
    - specialize cons_sem__Γ with (1:=Hv) (2:=HG) as HGA.
      specialize HM with (1:=HGA).
      simp interp__t in HM.
      destruct HM as (m & HM & Hm).
      eexists; split; eauto.
      econstructor; eauto. asimpl. assumption.
    - specialize cons_sem__Γ with (1:=Hv) (2:=HG) as HGB.
      specialize HN with (1:=HGB).
      simp interp__t in HN.
      destruct HN as (n & HN & Hn).
      eexists; split; eauto.
      econstructor; eauto. asimpl. assumption.
  Qed.
End compat.

Local Hint Resolve ident_compat : core.
Local Hint Resolve abs_compat : core.
Local Hint Resolve app_compat : core.
Local Hint Resolve tabs_compat : core.
Local Hint Resolve tapp_compat : core.
Local Hint Resolve pack_compat : core.
Local Hint Resolve unpack_compat : core.
Local Hint Resolve letin_compat : core.
Local Hint Resolve ttt_compat : core.
Local Hint Resolve bewl_compat : core.
Local Hint Resolve bewl1_compat : core.
Local Hint Resolve bewl2_compat : core.
Local Hint Resolve int_compat : core.
Local Hint Resolve int1_compat : core.
Local Hint Resolve int2_compat : core.
Local Hint Resolve cmp_compat : core.
Local Hint Resolve cond_compat : core.
Local Hint Resolve tuple_compat : core.
Local Hint Resolve proj_compat : core.
Local Hint Resolve inlr_compat : core.
Local Hint Resolve mtch_compat : core.

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
      rewrite HM in H
  end.

Local Hint Extern 3 => val_tedium : core.

Ltac tedium :=
  lazymatch goal with
    H : inj__v _ = (_ [[ ?N ]])%rtrm |- ?N ~>b _ -> _
    => symmetry in H;
      apply val_fill__k in H as (? & ->);
      intros ?%val_not_step__b; contradiction
  end.

Local Hint Extern 0 => tedium : core.

Ltac solve_uniq_decomp__k :=
  lazymatch goal with
    IHKMN: (∀ KN M N M' N',
              (?KM [[M]])%rtrm = (KN [[N]])%rtrm →
              M ~>b M' → N ~>b N' → ?KM = KN ∧ M = N),
      HKMN: (?KM [[?M]])%rtrm = (?KN [[?N]])%rtrm
    |- ?M ~>b _ -> ?N ~>b _ -> _
    => intros HM HN;
      specialize IHKMN with (1:=HKMN) (2:=HM) (3:=HN) as (<- & <-);
      split; reflexivity
  end.

(* Why slow? *)
(* Local Hint Extern 0 => solve_uniq_decomp__k : core. *)

Lemma uniq_decomp__k KM KN M N M' N' :
  (KM [[ M ]])%rtrm = (KN [[ N ]])%rtrm ->
  M ~>b M' -> N ~>b N' ->
  KM = KN /\ M = N.
Proof.
  induction KM in KN, M, N, M', N' |- *;
    destruct KN; cbn; try discriminate;
    try (intros ->; inversion 1; subst; auto; contradiction);
    try (intros <- HM; inversion 1; subst; revert HM; auto; contradiction).
  - injection 1 as HKMN <-%inj_inj__v. solve_uniq_decomp__k.
  - injection 1 as <- HNv.
    symmetry in HNv.
    apply val_fill__k in HNv as (n & ->).
    intros _ HN%val_not_step__b; contradiction.
  - injection 1 as -> (m & ->)%val_fill__k.
    intros HN%val_not_step__b; contradiction.
  - injection 1 as -> HKMN. solve_uniq_decomp__k.
  - injection 1 as HKMN. solve_uniq_decomp__k.
  - injection 1 as HKMN. solve_uniq_decomp__k.
  - injection 1 as HKMN ->. solve_uniq_decomp__k.
  - injection 1 as HKMN <-. solve_uniq_decomp__k.
  - injection 1 as <- HKMN. solve_uniq_decomp__k.
  - injection 1 as <- HKMN <-%inj_inj__v. solve_uniq_decomp__k.
  - injection 1 as <- <- (n & ->)%eq_sym%val_fill__k.
    intros _ H%val_not_step__b. contradiction.
  - injection 1 as <- -> (n & ->)%val_fill__k.
    intros H%val_not_step__b. contradiction.
  - injection 1 as <- -> HKMN. solve_uniq_decomp__k.
  - injection 1 as <- HKMN. solve_uniq_decomp__k.
  - injection 1 as <- HKMN <-%inj_inj__v. solve_uniq_decomp__k.
  - injection 1 as <- <- (n & ->)%eq_sym%val_fill__k.
    intros _ H%val_not_step__b. contradiction.
  - injection 1 as <- -> (n & ->)%val_fill__k.
    intros H%val_not_step__b. contradiction.
  - injection 1 as <- -> HKMN. solve_uniq_decomp__k.
  - injection 1 as <- HKMN <-%inj_inj__v. solve_uniq_decomp__k.
  - injection 1 as <- <- (n & ->)%eq_sym%val_fill__k.
    intros _ H%val_not_step__b. contradiction.
  - injection 1 as <- -> (m & ->)%val_fill__k.
    intros H%val_not_step__b. contradiction.
  - injection 1 as <- -> HKMN. solve_uniq_decomp__k.
  - injection 1 as HKMN -> ->. solve_uniq_decomp__k.
  - injection 1 as HKMN <-%inj_inj__v. solve_uniq_decomp__k.
  - injection 1 as <- (n & ->)%eq_sym%val_fill__k.
    intros _ H%val_not_step__b. contradiction.
  - injection 1 as -> (m & ->)%val_fill__k.
    intros H%val_not_step__b. contradiction.
  - injection 1 as -> HKM. solve_uniq_decomp__k.
  - injection 1 as <- HKM. solve_uniq_decomp__k.
  - injection 1 as <-%inj_sum_of_bool__tt HKMN. solve_uniq_decomp__k.
  - injection 1 as HKMN -> ->. solve_uniq_decomp__k.
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
  (`λ M)%rtrm ~>* (`λ M)%val.
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
  L ~>* (`λ N)%val ->
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
  (Λ M)%rtrm ~>* (Λ M)%val.
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
  L ~>* (Λ M)%val ->
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

Lemma steps_letin__l M M' N :
  M ~>* M' ->
  letin M N ~>* letin M' N.
Proof.
  induction 1; eauto using step_letin__l.
Qed.

Lemma steps_letin M N N' (m : val) :
  M ~>* m ->
  N.[inj__v m/] ~>* N' ->
  letin M N ~>* N'.
Proof.
  intros HM HN.
  transitivity N.[inj__v m/]; auto.
  apply rtc_r with (y:=letin (inj__v m) N); auto using steps_letin__l.
Qed.

Lemma steps_ttt :
  ttt ~>* ttt__v.
Proof.
  eauto.
Qed.

Lemma steps_bewl b :
  bewl b ⇓ bewl__v b.
Proof.
  eauto.
Qed.

Lemma steps_bewl1__i f M M' :
  M ~>* M' ->
  bewl1 f M ~>* bewl1 f M'.
Proof.
  induction 1; eauto using step_bewl1__i.
Qed.

Lemma steps_bewl1 f M b :
  M ~>* bewl b ->
  bewl1 f M ~>* bewl (f b).
Proof.
  intros HM.
  apply rtc_r with (y:=bewl1 f (bewl b)); eauto using steps_bewl1__i.
Qed.

Lemma steps_bewl2__r f M N N' :
  N ~>* N' ->
  bewl2 f M N ~>* bewl2 f M N'.
Proof.
  induction 1; eauto using step_bewl2__r.
Qed.

Lemma steps_bewl2__l f M M' n :
  M ~>* M' ->
  bewl2 f M (inj__v n) ~>* bewl2 f M' (inj__v n).
Proof.
  induction 1; eauto using step_bewl2__l.
Qed.

Lemma steps_bewl2 f M N m n :
  M ~>* bewl m ->
  N ~>* bewl n ->
  bewl2 f M N ~>* bewl (f m n).
Proof.
  intros HM HN.
  apply rtc_r with (y:=bewl2 f (bewl m) (bewl n)); eauto.
  replace (bewl n) with (inj__v (bewl__v n)) by reflexivity.
  transitivity (bewl2 f M (inj__v (bewl__v n)));
    eauto using steps_bewl2__l, steps_bewl2__r.
Qed.

Lemma steps_int z :
  int z ⇓ int__v z.
Proof.
  eauto.
Qed.

Lemma steps_int1__i f M M' :
  M ~>* M' ->
  int1 f M ~>* int1 f M'.
Proof.
  induction 1; eauto using step_int1__i.
Qed.

Lemma steps_int1 f M z :
  M ~>* int z ->
  int1 f M ~>* int (f z).
Proof.
  intros HM.
  apply rtc_r with (y:=int1 f (int z)); eauto using steps_int1__i.
Qed.

Lemma steps_int2__r f M N N' :
  N ~>* N' ->
  int2 f M N ~>* int2 f M N'.
Proof.
  induction 1; eauto using step_int2__r.
Qed.

Lemma steps_int2__l f M M' n :
  M ~>* M' ->
  int2 f M (inj__v n) ~>* int2 f M' (inj__v n).
Proof.
  induction 1; eauto using step_int2__l.
Qed.

Lemma steps_int2 f M N m n :
  M ~>* int m ->
  N ~>* int n ->
  int2 f M N ~>* int (f m n).
Proof.
  intros HM HN.
  apply rtc_r with (y:=int2 f (int m) (int n)); eauto.
  replace (int n) with (inj__v (int__v n)) by reflexivity.
  transitivity (int2 f M (inj__v (int__v n)));
    eauto using steps_int2__l, steps_int2__r.
Qed.

Lemma steps_cmp__r f M N N' :
  N ~>* N' ->
  cmp f M N ~>* cmp f M N'.
Proof.
  induction 1; eauto using step_cmp__r.
Qed.

Lemma steps_cmp__l f M M' n :
  M ~>* M' ->
  cmp f M (inj__v n) ~>* cmp f M' (inj__v n).
Proof.
  induction 1; eauto using step_cmp__l.
Qed.

Lemma steps_cmp f M N m n :
  M ~>* int m ->
  N ~>* int n ->
  cmp f M N ~>* bewl (f m n).
Proof.
  intros HM HN.
  apply rtc_r with (y:=cmp f (int m) (int n)); eauto.
  replace (int n) with (inj__v (int__v n)) by reflexivity.
  transitivity (cmp f M (inj__v (int__v n)));
    eauto using steps_cmp__l, steps_cmp__r.
Qed.

Lemma steps_cond__l L L' M N :
  L ~>* L' ->
  cond L M N ~>* cond L' M N.
Proof.
  induction 1; eauto using step_cond__l.
Qed.

Lemma steps_cond L M N b v :
  L ~>* bewl b ->
  (if b then M else N) ~>* v ->
  cond L M N ~>* v.
Proof.
  intros HL HMN.
  transitivity (cond (bewl b) M N); eauto using steps_cond__l, step_cond.
Qed.

Lemma steps_tuple__r M N N' :
  N ~>* N' ->
  `(M, N)`%rtrm ~>* `(M, N')`%rtrm.
Proof.
  induction 1; eauto using step_tuple__r.
Qed.

Lemma steps_tuple__l M M' (n : val) :
  M ~>* M' ->
  `(M, inj__v n)`%rtrm ~>* `(M', inj__v n)`%rtrm.
Proof.
  induction 1; eauto using step_tuple__l.
Qed.

Lemma steps_tuple M N (m n : val) :
  M ~>* m ->
  N ~>* n ->
  `(M, N)`%rtrm ~>* `(m, n)`%val.
Proof.
  intros HM HN.
  transitivity `(M, inj__v n)`%rtrm; eauto using steps_tuple__r, steps_tuple__l.
Qed.

Lemma steps_proj__i b M M' :
  M ~>* M' ->
  proj b M ~>* proj b M'.
Proof.
  induction 1; eauto using step_proj__i.
Qed.

Lemma steps_proj b M (x y : val) :
  M ~>* `(x, y)`%val ->
  proj b M ~>* inj__v (if b then x else y).
Proof.
  intro HM.
  rewrite distr_if_booll.
  apply rtc_r with (y:=proj b `(inj__v x, inj__v y)`%rtrm);
    eauto using step_proj, steps_proj__i.
Qed.

Lemma steps_inlr__i lr M M' :
  M ~>* M' ->
  inlr lr M ~>* inlr lr M'.
Proof.
  induction 1; eauto using step_inlr.
Qed.

Lemma steps_inlr lr M (m : val) :
  M ~>* m ->
  inlr lr M ~>* inlr__v (bool_of_sum lr) m.
Proof.
  intros HM%(steps_inlr__i lr).
  transitivity (inlr lr (inj__v m)); try assumption.
  cbn. autorewrite with core. reflexivity.
Qed.

Lemma steps_mtch__l L L' M N :
  L ~>* L' ->
  mtch L M N ~>* mtch L' M N.
Proof.
  induction 1; eauto using step_mtch__l.
Qed.

Lemma steps_mtch L M N b (l v : val) :
  L ~>* inlr__v b l ->
  (if b then M else N).[inj__v l/] ~>* v ->
  mtch L M N ~>* v.
Proof.
  intros HL HMN.
  rewrite distr_if_booll in HMN.
  transitivity (mtch (inj__v (inlr__v b l)) M N); eauto using steps_mtch__l.
  apply rtc_l with (if b then M.[inj__v l/] else N.[inj__v l/]); eauto.
  cbn. rewrite <- sum_of_bool_if__tt.
  apply step_mtch.
Qed.

Lemma big_steps M v :
  M ⇓ v -> M ~>* v.
Proof.
  induction 1;
    eauto using steps_app, steps_tapp, steps_pack, steps_unpack,
    steps_letin, steps_bewl1, steps_bewl2, steps_int1, steps_int2,
    steps_cmp, steps_cond, steps_tuple, steps_proj, steps_inlr, steps_mtch.
Qed.

Lemma big_inj__v (v1 v2 : val) :
  v1 ⇓ v2 -> v1 = v2.
Proof.
  induction v1 in v2 |- *; inversion 1; subst; eauto;
    repeat lazymatch goal with
        IH : (forall v2, inj__v ?v1 ⇓ v2 -> ?v1 = v2), H: (inj__v ?v1 ⇓ _)
        |- _ => specialize IH with (1:=H) as <-
      end; autorewrite with core; reflexivity.
Qed.

Lemma step__b_big M M' m :
  M ~>b M' -> M' ⇓ m -> M ⇓ m.
Proof.
  inversion 1; subst; eauto;
    try (inversion 1; subst; eauto; assumption).
  - inversion H; subst. do 2 destr_inj__v.
    rewrite <- (distr_if_booll inj__v).
    intros <-%big_inj__v; eauto.
  - inversion H; subst. destr_inj__v.
    rewrite <- bool_of_sum_if.
    rewrite <- distr_if_booll.
    replace (inlr lr (inj__v v)) with (inj__v (inlr__v (bool_of_sum lr) v)).
    2:{ cbn. autorewrite with core. reflexivity. }
    eauto.
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

Ltac reduce_big_det :=
  repeat lazymatch goal with
      IH: (forall v', ?M ⇓ v' -> ?v = v'), H: (?M ⇓ _)
      |- _ => specialize IH with (1:=H) as <- ||
             (specialize IH with (1:=H); injection IH as <- || injection IH as <- <-)
    end.

Lemma big_det M v1 v2 :
  M ⇓ v1 -> M ⇓ v2 -> v1 = v2.
Proof.
  induction 1 in v2 |- *; inversion 1; subst; auto;
    repeat (reduce_big_det; subst); try reflexivity.
Qed.

Lemma steps_order L M N :
  L ~>* M -> L ~>* N -> M ~>* N \/ N ~>* M.
Proof.
  induction 1 as [| L P M HLP HPM IHPM] in N |- *; eauto.
  inversion 1; subst; eauto.
  specialize det_step with (1:=H0) (2:=HLP) as ->. eauto.
Qed.

Lemma val_steps (m : val) M :
  m ~>* M -> M = m.
Proof.
  inversion 1; subst; try reflexivity.
  apply val_not_step in H0. contradiction.
Qed.

Lemma big_safe M v :
  M ⇓ v -> safe M.
Proof.
  unfold safe, progressive.
  intros HMv M' HMM'.
  specialize big_steps with (1:=HMv) as HMv__s.
  specialize steps_order with (1:=HMM') (2:=HMv__s) as [H | ->%val_steps]; eauto.
  inversion H; subst; eauto.
Qed.

Lemma sem_judge_safe M A :
  [] ⊨ M `: A -> safe M.
Proof.
  unfold sem_judge.
  intro H.
  specialize H with (δ:=fun _ _ => False) (γ:=Ids_trm ()) (1:=nil_sem__Γ _ _).
  rewrite subst_id in H.
  simp interp__t in H.
  destruct H as (v & HMv & Hv).
  eauto using big_safe.
Qed.

Theorem termination M A :
  0 `; [] ⊢ M `: A ->
  exists v, M ⇓ v.
Proof.
  intros H%sem_sound.
  unfold sem_judge in H.
  specialize H with (δ:=fun _ _ => False) (γ:=Ids_trm ()) (1:=nil_sem__Γ _ _).
  rewrite subst_id in H.
  simp interp__t in H.
  destruct H as (v & HMv & Hv).
  eauto.
Qed.

Definition bool__sct := (`∀ Ident 0 `→ Ident 0 `→ Ident 0)%typ.
Definition true__sct := (Λ λ: Ident 0 `, λ: Ident 0 `, ident 1)%strm.
Definition false__sct := (Λ λ: Ident 0 `, λ: Ident 0 `, ident 0)%strm.
Definition cond__sct (A : typ) b M N := (b `[ A ]` ⋅ M ⋅ N)%strm.
Definition cond_exact__sct (A : typ) b M N :=
  (b `[Unit `→ A]` ⋅ (λ: Unit `, M) ⋅ (λ: Unit `, N) ⋅ ttt)%strm.

(* Definition nat__sct := (`∀ ((`∀ Ident 0 `→ (Ident 1 `→ Ident 0) `→ Ident 0) `→ Ident 0) `→ Ident 0)%typ. *)
(* Definition zero__sct := (Λ λ: Ident 0 `, λ: Ident 0 `→ Ident 0 `, ident 1)%strm. *)
(* Definition one__sct := (Λ λ: Ident 0 `, λ: Ident 0 `→ Ident 0 `, ident 0 ⋅ ident 1)%strm. *)
(* Definition succ__sct := (λ: nat__sct `, Λ λ: Ident 0 `, λ: Ident 0 `→ Ident 0 `, ident 0 ⋅ (ident 2 `[Ident 0 ]`))%strm. *)
(* Definition mtch_nat__sct (A : typ) n Z F := (n `[A]` ⋅ Z ⋅ F)%strm. *)

Definition prod__sct (A B : typ) : typ := (`∀ (A.[ren S] `→ B.[ren S] `→ Ident 0) `→ Ident 0)%typ.
Definition pair__sct A B M N : strm :=
  (letin N
     (letin M.[ren S]
                (Λ λ: A.[ren S] `→ B.[ren S] `→ Ident 0 `, ident 0 ⋅ ident 1 ⋅ ident 2)))%strm.
Definition mtch_pair__sct (A B R : typ) P F : strm := (P `[ R ]` ⋅ λ: A `, λ: B `, F)%strm.
Definition proj__sct (A B : typ) (b : bool) P :=
  (P `[ if b then A else B ]` ⋅ (λ: A `, λ: B `, ident (if b then 1 else 0)))%strm.

Definition sum__sct A B : typ :=
  (`∀ (A.[ren S] `→ Ident 0) `→ (B.[ren S] `→ Ident 0) `→ Ident 0)%typ.
Definition inlr__sct (A B : typ) M (b : bool) : strm :=
  (letin M
     (Λ λ: (A.[ren S] `→ Ident 0) `,
        λ: (B.[ren S] `→ Ident 0) `, ident (if b then 1 else 0) ⋅ ident 2))%strm.
Definition mtch_sum__sct (A B R : typ) L M N : strm :=
  (L `[ R ]` ⋅ (λ: A `, M) ⋅ (λ: B `, N))%strm.

Definition exists__sct (B : typ) : typ :=
  (`∀ (`∀ B.[Ident 0 .: ren (+2)] `→ Ident 1) `→ Ident 0)%typ.
Definition pack__sct (A B : typ) (M : strm) : strm :=
  letin M (Λ λ:`∀ B.[Ident 0 .: ren (+2)] `→ Ident 1 `, ident 0 `[ A.[ren S] ]` ⋅ ident 1)%strm.
Definition unpack__sct (B C : typ) (M N : strm) : strm :=
  (M `[ C ]` ⋅ (Λ λ: B `, N))%strm.

Lemma wf_tsubst_extra Δ :
  wf_tsubst (S Δ) (S (S Δ)) (Ident 0 .: ren (+2)).
Proof.
  unfold wf_tsubst.
  intros [| X] HX; cbn; eauto.
  constructor. lia.
Qed.

Local Hint Resolve wf_tsubst_extra : core.

Section wf__sct.
  Variable Δ : nat.
  
  Local Hint Constructors wf_typ : core.
  
  Lemma wf_bool__sct : Δ ⊢wf bool__sct.
  Proof.
    repeat (constructor; eauto with lia).
  Qed.

  Lemma wf_prod__sct A B :
    Δ ⊢wf A -> Δ ⊢wf B ->
    Δ ⊢wf prod__sct A B.
  Proof.
    repeat (constructor; eauto using wf_typ_weaken with lia).
  Qed.

  Lemma wf_sum__sct A B :
    Δ ⊢wf A -> Δ ⊢wf B ->
    Δ ⊢wf  sum__sct A B.
  Proof.
    repeat (constructor; eauto using wf_typ_weaken with lia).
  Qed.

  Lemma wf_exists__sct B :
    S Δ ⊢wf B ->
    Δ ⊢wf exists__sct B.
  Proof.
    intro H.
    constructor.
    constructor; eauto with lia.
  Qed.
End wf__sct.

Section judge__sct.
  Variable Δ : nat.
  Variable Γ : list typ.

  Local Hint Constructors wf_typ : core.
  Local Hint Constructors judge__s : core.
  
  Lemma judge_true__sct :
    Δ `;; Γ ⊢ true__sct `: bool__sct.
  Proof.
    constructor.
    apply judge_abs__s; auto with lia.
  Qed.
  
  Lemma judge_false__sct :
    Δ `;; Γ ⊢ true__sct `: bool__sct.
  Proof.
    constructor.
    apply judge_abs__s; auto with lia.
  Qed.

  Lemma judge_cond__sct b M N A :
    Δ ⊢wf A ->
    Δ `;; Γ ⊢ b `: bool__sct ->
    Δ `;; Γ ⊢ M `: A ->
    Δ `;; Γ ⊢ N `: A ->
    Δ `;; Γ ⊢ cond__sct A b M N `: A.
  Proof.
    intros HA Hb HM HN.
    econstructor; eauto.
    econstructor; eauto.
    replace (A `→ A `→ A)%typ with (Ident 0 `→ Ident 0 `→ Ident 0)%typ.[A/]
      by reflexivity.
    constructor; auto.
  Qed.
  
  Lemma judge_cond_exact__sct b M N A :
    Δ ⊢wf A ->
    Δ `;; Γ ⊢ b `: bool__sct ->
    Δ `;; Unit :: Γ ⊢ M `: A ->
    Δ `;; Unit :: Γ ⊢ N `: A ->
    Δ `;; Γ ⊢ cond_exact__sct A b M N `: A.
  Proof.
    intros HA Hb HM HN.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    replace ((Unit `→ A) `→ (Unit `→ A) `→ Unit `→ A)%typ with
      (Ident 0 `→ Ident 0 `→ Ident 0)%typ.[(Unit `→ A)%typ/]
      by reflexivity.
    eauto.
  Qed.

  (* Lemma judge_zero__sct : *)
  (*   Δ `;; Γ ⊢ zero__sct `: nat__sct. *)
  (* Proof. *)
  (*   constructor. *)
  (*   constructor; eauto with lia. *)
  (*   constructor; eauto with lia. *)
  (* Qed. *)

  (* Lemma judge_one__sct : *)
  (*   Δ `;; Γ ⊢ one__sct `: nat__sct. *)
  (* Proof. *)
  (*   constructor. *)
  (*   constructor; eauto with lia. *)
  (*   constructor; eauto with lia. *)
  (* Qed. *)

  (* Lemma judge_succ__sct : *)
  (*   Δ `;; Γ ⊢ succ__sct `: (nat__sct `→ nat__sct)%typ. *)
  (* Proof. *)
  (*   constructor. *)
  (*   1:{ constructor. repeat (constructor; eauto with lia). } *)
  (*   constructor. *)
  (*   constructor; auto with lia. *)
  (*   constructor; auto with lia. *)
  (*   constructor; eauto with lia. *)
  (*   constructor; eauto with lia. *)
  (* Qed. *)

  Local Hint Resolve judge_erase : core.
  
  Lemma judge_pair__sct A B M N :
    Δ ⊢wf A -> Δ ⊢wf B ->
    Δ `;; Γ ⊢ M `: A ->
    Δ `;; Γ ⊢ N `: B ->
    Δ `; Γ ⊢ erase (pair__sct A B M N) `: prod__sct A B.
  Proof.
    intros HA HB HM%judge_erase HN%judge_erase. cbn.
    econstructor; eauto.
    econstructor.
    1:{ unfold erase.
        rewrite map_trm_rename.
        eapply judge_rename with
          (Γ1 := Γ) (Γ2 := B :: Γ); eauto. }
    constructor; eauto.
    constructor; eauto.
    1:{ constructor;
        eauto using wf_typ_weaken with lia. }
    cbn. econstructor; eauto.
  Qed.

  Lemma judge_proj__sct A B P b :
    Δ ⊢wf A -> Δ ⊢wf B ->
    Δ `;; Γ ⊢ P `: prod__sct A B ->
    Δ `;; Γ ⊢ proj__sct A B b P `: if b then A else B.
  Proof.
    unfold prod__sct, proj__sct.
    intros HA HB HP.
    apply judge_tapp__s with (B:=if b then A else B) in HP.
    2:{ destruct b; assumption. }
    econstructor; eauto. asimpl in *.
    constructor; auto.
    constructor; auto.
    constructor.
    destruct b; reflexivity.
  Qed.

  Lemma judge_mtch_pair__sct A B R P F :
    Δ ⊢wf A -> Δ ⊢wf B -> Δ ⊢wf R ->
    Δ `;; Γ ⊢ P `: prod__sct A B ->
    Δ `;; B :: A :: Γ ⊢ F `: R ->
    Δ `;; Γ ⊢ mtch_pair__sct A B R P F `: R.
  Proof.
    unfold prod__sct, mtch_pair__sct.
    intros HA HB HR HP HF.
    apply judge_tapp__s with (B:=R) in HP; eauto.
    econstructor; eauto.
    asimpl in *.
    constructor; auto.
  Qed.

  Lemma judge_inlr__sct A B M (b : bool) :
    Δ ⊢wf A -> Δ ⊢wf B ->
    Δ `;; Γ ⊢ M `: (if b then A else B) ->
    Δ `;; Γ ⊢ inlr__sct A B M b `: sum__sct A B.
  Proof.
    intros HA HB HM.
    econstructor; eauto.
    constructor. cbn.
    constructor; eauto with lia.
    constructor; eauto with lia.
    econstructor; eauto.
    constructor.
    destruct b; reflexivity.
  Qed.

  Lemma judge_mtch_sum__sct A B R L M N :
    Δ ⊢wf A -> Δ ⊢wf B -> Δ ⊢wf R ->
    Δ `;; Γ ⊢ L `: sum__sct A B ->
    Δ `;; A :: Γ ⊢ M `: R ->
    Δ `;; B :: Γ ⊢ N `: R ->
    Δ `;; Γ ⊢ mtch_sum__sct A B R L M N `: R.
  Proof.
    intros HA HB HR HL HM HN.
    unfold sum__sct in HL.
    specialize judge_tapp__s with (B:=R) (1:=HR) (2:=HL) as H.
    asimpl in H.
    econstructor; eauto.
  Qed.

  Lemma judge_pack__sct A B M :
    Δ ⊢wf A ->
    S Δ ⊢wf B ->
    Δ `;; Γ ⊢ M `: B.[A/] ->
    Δ `;; Γ ⊢ pack__sct A B M `: exists__sct B.
  Proof.
    intros HA HB HM.
    unfold pack__sct, exists__sct.
    apply judge_letin__s with (A:=B.[A/]); auto.
    constructor. cbn.
    constructor; eauto with lia.
    econstructor; eauto.
    replace (B.[A/].[ren S] `→ Ident 0)%typ with
      (B.[Ident 0 .: ren (+2)] `→ Ident 1)%typ.[A.[ren S]/].
    2:{ asimpl. f_equal. }
    constructor; eauto.
  Qed.

  Lemma judge_unpack__sct B C M N :
    S Δ ⊢wf B ->
    Δ ⊢wf C ->
    Δ `;; Γ ⊢ M `: exists__sct B ->
    S Δ `;; B :: up__Γ Γ ⊢ N `: C.[ren S] ->
    Δ `; Γ ⊢ erase (unpack__sct B C M N) `: C.
  Proof.
    unfold exists__sct, unpack__sct. cbn.
    intros HB HC HM%judge_erase HN%judge_erase.
    specialize judge_tapp__r with (B:=C) (1:=HC) (2:=HM) as HMC.
    econstructor; eauto.
    asimpl. eauto.
  Qed.
End judge__sct.

Definition δ__emp : var -> sem__t := fun _ _ => False.

Section freedom.
  Lemma sem_closed M A :
    0 `; [] ⊢ M `: A -> E⟦ A ⟧ δ__emp M.
  Proof.
    intros HM%sem_sound.
    unfold sem_judge in HM.
    specialize HM with (1:=nil_sem__Γ δ__emp (@ids _ (Ids_trm unit))).
    cbn. simp interp__t in HM |- *.
    destruct HM as (v & HM & Hv).
    asimpl in HM. eauto.
  Qed.

  Lemma free_void :
    ~ exists M, 0 `; [] ⊢ M `: (`∀ Ident 0)%typ.
  Proof.
    intros [M HM%sem_closed].
    simp interp__t in HM.
    destruct HM as (m & HM & Hm).
    simp interp__t in Hm.
    destruct Hm as (L & -> & HL).
    specialize HL with (fun _ => False).
    simp interp__t in HL.
    destruct HL as (l & HL & Hl).
    simp interp__t in Hl. asimpl in Hl.
    contradiction.
  Qed.

  Lemma free_unit F (v : val) A :
    0 `; [] ⊢ F `: (`∀ Ident 0 `→ Ident 0)%typ ->
    0 `; [] ⊢ v `: A ->
    (F [-] ⋅ inj__v v)%rtrm ⇓ v.
  Proof.
    intros HF%sem_closed Hv%sem_closed.
    simp interp__t in HF, Hv.
    destruct HF as (f & HF & Hf).
    destruct Hv as (? & <-%big_inj__v & Hv).
    simp interp__t in Hf.
    destruct Hf as (M & -> & HM).
    specialize HM with (eq v).
    simp interp__t in HM.
    destruct HM as (m & HM & Hm).
    simp interp__t in Hm.
    destruct Hm as (N & -> & HN).
    specialize HN with v.
    simp interp__t in HN. asimpl in HN.
    specialize HN with (1:=eq_refl) as (n & HN & Hn).
    simp interp__t in Hn. asimpl in Hn. subst.
    eauto.
  Qed.

  Local Hint Constructors elem_of_list : core.
  
  Lemma free_bool_weak V (T F : val) A :
    0 `; [] ⊢ V `: bool__sct ->
    0 `; [] ⊢ T `: A ->
    0 `; [] ⊢ F `: A ->
    exists v', v' ∈ [T; F] /\ (V [-] ⋅ (inj__v T) ⋅ (inj__v F))%rtrm ⇓ v'.
  Proof.
    intros HV%sem_closed HT%sem_closed HF%sem_closed.
    simp interp__t in HV, HT, HF.
    destruct HT as (t & ->%big_inj__v & Ht).
    destruct HF as (f & ->%big_inj__v & Hf).
    destruct HV as (v & HV & Hv).
    unfold bool__sct in Hv.
    simp interp__t in Hv.
    destruct Hv as (L & -> & HL).
    specialize HL with (fun v : val => @elem_of _ _ (@elem_of_list val) v [t; f]).
    simp interp__t in HL.
    destruct HL as (l & HL & Hl).
    simp interp__t in Hl.
    destruct Hl as (M & -> & HM).
    specialize HM with t.
    simp interp__t in HM. asimpl in HM.
    assert (Htin: t ∈ [t; f]) by eauto.
    specialize HM with (1:=Htin).
    destruct HM as (m & HM & Hm).
    simp interp__t in Hm.
    destruct Hm as (N & -> & HN).
    specialize HN with f.
    simp interp__t in HN. asimpl in HN.
    assert (Hfin: f ∈ [t; f]) by eauto.
    specialize HN with (1:=Hfin).
    destruct HN as (n & HN & Hn).
    simp interp__t in Hn. asimpl in Hn.
    exists n. split; eauto.
  Qed.
End freedom.
