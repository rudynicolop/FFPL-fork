From stdpp Require Import gmap base relations.
From ffpl.lib Require Import prelude.
From ffpl.lib Require Export facts.
From ffpl.type_systems.systemf Require Import lang notation types bigstep.
From Equations Require Export Equations.


(** * Logical relation for SystemF *)

Implicit Types
  (Delta : nat)
  (Gamma : typing_context)
  (v : val)
  (alpha : var)
  (e : expr)
  (A : type).

(** ** Definition of the logrel *)

(** The logical relation is defined mutually recursively on expressions and values.
To encode this in Coq, we define a type that is "expression or value", and then
define the relation on that. The [inj_val] and [inj_expr] constructors
are used to convert values/expressions into that shared type. *)
Inductive val_or_expr : Type :=
| inj_val : val -> val_or_expr
| inj_expr : expr -> val_or_expr.

(** As before, we need to define a measure to prove that our recursive definitions are well-formed. *)
Equations type_size (A : type) : nat :=
  type_size Int := 1;
  type_size Bool := 1;
  type_size Unit := 1;
  type_size (A -> B) := type_size A + type_size B + 1;
  type_size (^alpha) := 1;
  type_size (forall: A) := type_size A + 2;
  type_size (exists: A) := type_size A + 2;
  type_size (A * B) := type_size A + type_size B + 1;
.

Equations type_interp_measure (ve : val_or_expr) (A : type) : nat :=
  type_interp_measure (inj_expr e) A := 1 + type_size A;
  type_interp_measure (inj_val v) A := type_size A.

(** Now that our types contain free variables, we need to parameterize the type interpretation
function by an interpretation for the free variables. This interpretation maps variable
names to "semantic types", which are sets of values / predicates over values. *)
Definition sem_type := val -> Prop.
Definition tyvar_interp := var -> sem_type.

Implicit Types
  (delta : tyvar_interp)
  (tau : sem_type)
.

(** The logical relation *)
Equations type_interp (ve : val_or_expr) (A : type) (delta : tyvar_interp) : Prop by wf (type_interp_measure ve A) := {
  type_interp (inj_val v) Int delta =>
    exists z : Z, v = #z ;
  type_interp (inj_val v) Bool delta =>
    exists b : bool, v = #b ;
  type_interp (inj_val v) Unit delta =>
    v = #LitUnit ;
  type_interp (inj_val v) (A * B) delta =>
    exists v1 v2 : val, v = (v1, v2)%V /\
      type_interp (inj_val v1) A delta /\ type_interp (inj_val v2) B delta ;
  type_interp (inj_val v) (A -> B) delta =>
    exists e, v = LamV e /\
      forall v',
        type_interp (inj_val v') A delta ->
        type_interp (inj_expr (e.[of_val v'/])) B delta;
  (** Type variable case *)
  type_interp (inj_val v) (^alpha) delta =>
    (delta alpha) v;
  (** forall case *)
  type_interp (inj_val v) (forall: A) delta =>
    exists e, v = TLamV e /\
      forall tau : sem_type, type_interp (inj_expr e) A (tau .: delta);
  (** exists case *)
  type_interp (inj_val v) (exists: A) delta =>
    exists v', v = PackV v' /\
      exists tau : sem_type, type_interp (inj_val v') A (tau .: delta);

  type_interp (inj_expr e) A delta =>
    exists v, big_step e v /\ type_interp (inj_val v) A delta
}.
Next Obligation. repeat simp type_interp_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp type_interp_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp type_interp_measure; simp type_size; lia. Qed.
Next Obligation.
  simp type_interp_measure. simp type_size.
  destruct A; repeat simp type_interp_measure; repeat simp type_size; lia.
Qed.
Next Obligation. repeat simp type_interp_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp type_interp_measure; simp type_size; lia. Qed.

(** Value relation and expression relation *)
Notation sem_val_rel A delta v := (type_interp (inj_val v) A delta).
Notation sem_expr_rel A delta e := (type_interp (inj_expr e) A delta).

(** Mapping syntactic type to semantic type *)
Definition syn_type_sem (A : type) delta : sem_type :=
  fun v => sem_val_rel A delta v.

(** Value inclusion lemma *)
Lemma val_inclusion A delta v :
  sem_val_rel A delta v -> sem_expr_rel A delta (of_val v).
Proof.
  intros Hv. simp type_interp. exists v.
  split; last done. apply big_step_val.
Qed.

(** ** Semantic typing of contexts *)

(** As before, we use maps to [expr] rather than [val] to represent "value
substitutions", this time because they can be directly used as substitutions with
Autosubst. *)
Implicit Types (gamma : var -> expr).

Definition sem_ctx_rel Gamma delta gamma :=
  forall x A, Gamma !! x = Some A -> exists v, gamma x = of_val v /\ sem_val_rel A delta v.

Lemma sem_ctx_rel_nil delta gamma : sem_ctx_rel [] delta gamma.
Proof.
  intros x A. rewrite lookup_nil. done.
Qed.

Lemma sem_ctx_rel_cons Gamma delta gamma v A :
  sem_val_rel A delta v ->
  sem_ctx_rel Gamma delta gamma ->
  sem_ctx_rel (A :: Gamma) delta (of_val v .: gamma).
Proof.
  intros Hv Hgamma [|x] B; simpl.
  - intros [= <-]. eauto.
  - eapply Hgamma.
Qed.

(** ** The semantic typing judgment *)
(** Now that [Delta] does not actually matter!
THis is because we use a total function for [delta], so *all* type variables have to map to *some*
semantic type. Only the type variables in [Delta] actually matter. *)
Definition sem_typed Delta Gamma e A :=
  forall delta gamma, sem_ctx_rel Gamma delta gamma -> sem_expr_rel A delta e.[gamma].
Notation "'TY' Delta ;  Gamma |= e : A" := (sem_typed Delta Gamma e A) (at level 74, e, A at next level).

(** ** Compatibility lemmas *)

Lemma compat_int Delta Gamma z : TY Delta; Gamma |= (Lit $ LitInt z) : Int.
Proof.
  intros delta gamma _. apply val_inclusion with (v := #z).
  simp type_interp. eauto.
Qed.

Lemma compat_bool Delta Gamma b : TY Delta; Gamma |= (Lit $ LitBool b) : Bool.
Proof.
  intros delta gamma _. apply val_inclusion with (v := #b).
  simp type_interp. eauto.
Qed.

Lemma compat_unit Delta Gamma : TY Delta; Gamma |= (Lit $ LitUnit) : Unit.
Proof.
  intros delta gamma _. apply val_inclusion with (v := #LitUnit).
  simp type_interp. done.
Qed.

Lemma compat_var Delta Gamma x A :
  Gamma !! x = Some A ->
  TY Delta; Gamma |= (Var x) : A.
Proof.
  intros Hx delta gamma Hctx; simpl.
  specialize (Hctx _ _ Hx) as (v & Heq & Hv).
  rewrite Heq. apply val_inclusion. done.
Qed.

Lemma compat_int_binop Delta Gamma op e1 e2 :
  bin_op_typed op Int Int Int ->
  TY Delta; Gamma |= e1 : Int ->
  TY Delta; Gamma |= e2 : Int ->
  TY Delta; Gamma |= (BinOp op e1 e2) : Int.
Proof.
  intros Hop He1 He2 delta gamma Hctx. simpl.
  simp type_interp.
  specialize (He1 _ _ Hctx). specialize (He2 _ _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst op.
  + exists #(z1 + z2)%Z. split.
    - econstructor; done.
    - exists (z1 + z2)%Z. done.
  + exists #(z1 - z2)%Z. split.
    - econstructor; done.
    - exists (z1 - z2)%Z. done.
  + exists #(z1 * z2)%Z. split.
    - econstructor; done.
    - exists (z1 * z2)%Z. done.
Qed.

Lemma compat_int_bool_binop Delta Gamma op e1 e2 :
  bin_op_typed op Int Int Bool ->
  TY Delta; Gamma |= e1 : Int ->
  TY Delta; Gamma |= e2 : Int ->
  TY Delta; Gamma |= (BinOp op e1 e2) : Bool.
Proof.
  intros Hop He1 He2 delta gamma Hctx. simpl.
  simp type_interp.
  specialize (He1 _ _ Hctx). specialize (He2 _ _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst op.
  + exists #(bool_decide (z1 < z2))%Z. split.
    - econstructor; done.
    - by eexists _.
  + exists #(bool_decide (z1 <= z2))%Z. split.
    - econstructor; done.
    - by eexists _.
  + exists #(bool_decide (z1 = z2))%Z. split.
    - econstructor; done.
    - eexists _. done.
Qed.

Lemma compat_binop Delta Gamma op A B C e1 e2 :
  bin_op_typed op A B C ->
  TY Delta; Gamma |= e1 : A ->
  TY Delta; Gamma |= e2 : B ->
  TY Delta; Gamma |= (BinOp op e1 e2) : C.
Proof.
  inversion 1; subst.
  1-3: by apply compat_int_binop.
  1-3: by apply compat_int_bool_binop.
Qed.

Lemma compat_if n Gamma e0 e1 e2 A :
  TY n; Gamma |= e0 : Bool ->
  TY n; Gamma |= e1 : A ->
  TY n; Gamma |= e2 : A ->
  TY n; Gamma |= (if: e0 then e1 else e2) : A.
Proof.
  intros He0 He1 He2 delta gamma Hctx. simpl.
  simp type_interp.
  specialize (He0 _ _ Hctx). simp type_interp in He0.
  specialize (He1 _ _ Hctx). simp type_interp in He1.
  specialize (He2 _ _ Hctx). simp type_interp in He2.

  destruct He0 as (v0 & Hb0 & Hv0). simp type_interp in Hv0. destruct Hv0 as (b & ->).
  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).

  destruct b.
  - exists v1. split; first by repeat econstructor. done.
  - exists v2. split; first by repeat econstructor. done.
Qed.

Lemma compat_app Delta Gamma e1 e2 A B :
  TY Delta; Gamma |= e1 : (A -> B) ->
  TY Delta; Gamma |= e2 : A ->
  TY Delta; Gamma |= (e1 e2) : B.
Proof.
  intros Hfun Harg delta gamma Hctx; simpl.
  specialize (Hfun _ _ Hctx). simp type_interp in Hfun. destruct Hfun as (v1 & Hbs1 & Hv1).
  simp type_interp in Hv1. destruct Hv1 as (e & -> & Hv1).
  specialize (Harg _ _ Hctx). simp type_interp in Harg.
  destruct Harg as (v2 & Hbs2 & Hv2).

  apply Hv1 in Hv2.
  simp type_interp in Hv2. destruct Hv2 as (v & Hbsv & Hv).

  simp type_interp.
  exists v. split; last done.
  eauto.
Qed.

Lemma compat_lam Delta Gamma e A B :
  TY Delta; (A :: Gamma) |= e : B ->
  TY Delta; Gamma |= (Lam e) : (A -> B).
Proof.
  intros Hbody delta gamma Hctxt. asimpl.
  apply val_inclusion with (v := (lam: _)%V).
  simp type_interp.
  eexists _. split; first done.

  intros v Hv.
  asimpl. apply (Hbody _ (of_val v .: gamma)).
  eapply sem_ctx_rel_cons; done.
Qed.

Lemma compat_pair Delta Gamma e1 e2 A B :
  TY Delta; Gamma |= e1 : A ->
  TY Delta; Gamma |= e2 : B ->
  TY Delta; Gamma |= (e1, e2) : A * B.
Proof.
  intros He1 He2 delta gamma Hctx. simpl.
  simp type_interp.
  specialize (He1 _ _ Hctx). simp type_interp in He1.
  destruct He1 as (v1 & Hb1 & Hv1).
  specialize (He2 _ _ Hctx). simp type_interp in He2.
  destruct He2 as (v2 & Hb2 & Hv2).
  exists (v1, v2)%V. split; first eauto.
  simp type_interp. exists v1, v2. done.
Qed.

Lemma compat_fst Delta Gamma e A B :
  TY Delta; Gamma |= e : A * B ->
  TY Delta; Gamma |= Fst e : A.
Proof.
  intros He delta gamma Hctx. simpl.
  simp type_interp.
  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  simp type_interp in Hv. destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).
  exists v1. split; first eauto. done.
Qed.

Lemma compat_snd Delta Gamma e A B :
  TY Delta; Gamma |= e : A * B ->
  TY Delta; Gamma |= Snd e : B.
Proof.
  intros He delta gamma Hctx. simpl.
  simp type_interp.
  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  simp type_interp in Hv. destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).
  exists v2. split; first eauto. done.
Qed.

(** The compatibility lemmas involving type variables require some technical but
boring helper lemmas. We encourage you to skip over the proofs of these lemmas. *)
Section boring_lemmas.
  (** When [delta] and [delta'] are pointwise equivalent, then they also make no
  difference for semantic interpration of values. *)
  (** "Boring Lemma 1" for the value relation. *)
  Lemma sem_val_rel_ext B delta delta' v :
    (forall n v, delta n v <-> delta' n v) ->
    sem_val_rel B delta v <-> sem_val_rel B delta' v.
  Proof.
    induction B in delta, delta', v |-*; simpl; simp type_interp; eauto; intros Hiff.
    - f_equiv; intros e. f_equiv.
      eapply forall_proper; intros tau.
      simp type_interp. f_equiv. intros w.
      f_equiv. etransitivity; last apply IHB; first done.
      intros [|m] ?; simpl; eauto.
    - f_equiv; intros w. f_equiv. f_equiv. intros tau.
      etransitivity; last apply IHB; first done.
      intros [|m] ?; simpl; eauto.
    - f_equiv. intros ?. f_equiv.
      eapply forall_proper. intros x.
      eapply if_iff; first eauto.
      simp type_interp. f_equiv. intros ?. f_equiv.
      eauto.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; eauto.
  Qed.

  (** Renaming in [B] is like renaming in [delta].
  (Usually we'd use [delta] as the name for the renaming, but in this file [delta]
  is already used for the type variable interpretation, so we use [sigma]. *)
  Lemma sem_val_rel_move_ren B delta (sigma : var -> var) v :
     sem_val_rel B.[ren sigma] delta v <-> sem_val_rel B (fun n => delta (sigma n)) v.
  Proof.
    induction B in sigma, delta, v |-*; simpl; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv.
      eapply forall_proper; intros tau.
      simp type_interp. f_equiv. intros w.
      f_equiv. asimpl. rewrite IHB.
      eapply sem_val_rel_ext; intros [|n] u; asimpl; done.
    - f_equiv; intros w. f_equiv. f_equiv. intros tau.
      asimpl. rewrite IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      +  simp type_interp. done.
      + simpl. rewrite /up. simpl. done.
    - f_equiv. intros ?. f_equiv.
      eapply forall_proper. intros x.
      eapply if_iff; first done.
      simp type_interp. f_equiv. intros ?. f_equiv.
      done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; done.
  Qed.

  (** Similarly, apply a substitution in [B] is like applying it in [delta],
  using [syn_type_sem] to interpret the substitution itself. *)
  Lemma sem_val_rel_move_subst B delta sigma v :
    sem_val_rel (B.[sigma]) delta v <-> sem_val_rel B (fun n => syn_type_sem (sigma n) delta) v.
  Proof.
    induction B in sigma, delta, v |-*; simpl; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv.
      eapply forall_proper; intros tau.
      simp type_interp. f_equiv. intros w.
      f_equiv. rewrite IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      + simp type_interp. done.
      + simpl. rewrite /syn_type_sem. simpl.
        asimpl. rewrite sem_val_rel_move_ren.
        simpl. done.
    - f_equiv; intros w. f_equiv. f_equiv. intros tau.
      rewrite IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      +  simp type_interp. done.
      + simpl. rewrite /syn_type_sem. simpl.
        asimpl. rewrite sem_val_rel_move_ren.
        simpl. done.
    - f_equiv. intros ?. f_equiv.
      eapply forall_proper. intros x.
      eapply if_iff; first done.
      simp type_interp. f_equiv. intros ?. f_equiv.
      done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; done.
  Qed.

  (** The previous lemma specialize to substituting a single variable. *)
  (** "Boring Lemma 2" for the value relation. *)
  Lemma sem_val_rel_move_single_subst A B delta v :
    sem_val_rel (B.[A/]) delta v <-> sem_val_rel B (syn_type_sem A delta .: delta) v.
  Proof.
    rewrite sem_val_rel_move_subst. eapply sem_val_rel_ext.
    intros [| n] w; simpl; done.
  Qed.

  (** Semantic typing is preserved when we bump up the free type variables,
  and add an arbitrary type interpretation [tau] for the new index 0.
  We need this in both directions. *)
  Lemma sem_val_rel_up A delta v tau :
    sem_val_rel A delta v <->
    sem_val_rel A.[ren (+1)] (tau .: delta) v.
  Proof.
    rewrite sem_val_rel_move_subst; simpl.
    eapply sem_val_rel_ext. done.
  Qed.

  (** Semantic typing of contexts is preserved when we bump up the free type
  variables *everywhere* and add an arbitrary [tau] for the new index 0. *)
  Lemma sem_ctx_rel_upctx Gamma delta gamma tau :
    sem_ctx_rel Gamma delta gamma ->
    sem_ctx_rel (upctx Gamma) (tau .: delta) gamma.
  Proof.
    intros Hctx x A. rewrite /upctx list_lookup_fmap.
    destruct (Gamma !! x) as [B|] eqn:EQ; rewrite EQ; last done.
    asimpl. intros [= <-].
    specialize (Hctx _ _ EQ) as (v & Heq & Hv).
    eexists. split; first done. rewrite -sem_val_rel_up. done.
  Qed.
End boring_lemmas.


Lemma compat_tapp Delta Gamma e A B :
  TY Delta; Gamma |= e : (forall: B) ->
  TY Delta; Gamma |= (e <>) : (B.[A/]).
Proof.
  intros He delta gamma Hctx. simpl.
  simp type_interp.

  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  simp type_interp in Hv.
  destruct Hv as (e1 & -> & He1).

  (* [set] is used to introduce a short-hand. It is basically a local definition. *)
  set tau := syn_type_sem A delta.
  specialize (He1 tau).
  simp type_interp in He1. destruct He1 as (v & Hb2 & Hv).
  exists v. split. { econstructor; done. }
  apply sem_val_rel_move_single_subst. done.
Qed.

Lemma compat_tlam Delta Gamma e A :
  TY S Delta; (upctx Gamma) |= e : A ->
  TY Delta; Gamma |= (Lam: e) : (forall: A).
Proof.
  intros He delta gamma Hctx. simpl.
  apply val_inclusion with (v := (Lam: _)%V).
  simp type_interp.
  eexists _. split_and!; first done.
  intros tau. eapply He.
  by eapply sem_ctx_rel_upctx.
Qed.

Lemma compat_pack Delta Gamma e n A B :
  TY n; Gamma |= e : A.[B/] ->
  TY n; Gamma |= (pack e) : (exists: A).
Proof.
  intros He delta gamma Hctx. simpl.
  simp type_interp.

  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  exists (PackV v). split; first eauto.

  simp type_interp. exists v. split; first done.
  exists (syn_type_sem B delta).
  apply sem_val_rel_move_single_subst. done.
Qed.

Lemma compat_unpack n Gamma A B e e' :
  TY n; Gamma |= e : (exists: A) ->
  TY S n; A :: (upctx Gamma) |= e' : B.[ren (+1)] ->
  TY n; Gamma |= (unpack e in e') : B.
Proof.
  intros He He' delta gamma Hctx. simpl. simp type_interp.

  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  simp type_interp in Hv. destruct Hv as (v' & -> & tau & Hv').

  specialize (He' (tau .: delta) (of_val v' .: gamma)).
  simp type_interp in He'.
  destruct He' as (v & Hb' & Hv).
  { eapply sem_ctx_rel_cons; first done. by apply sem_ctx_rel_upctx. }
  exists v. split.
  { econstructor; first done. asimpl. done. }
  by eapply sem_val_rel_up.
Qed.

(** Semantic soundness theorem *)

Theorem sem_soundness Delta Gamma e A :
  TY Delta; Gamma |- e : A ->
  TY Delta; Gamma |= e : A.
Proof.
  induction 1.
  - by eapply compat_var.
  - by eapply compat_lam.
  - by eapply compat_app.
  - by eapply compat_tlam.
  - by eapply compat_tapp.
  - by eapply compat_pack.
  - by eapply compat_unpack.
  - by eapply compat_int.
  - by eapply compat_bool.
  - by eapply compat_unit.
  - by eapply compat_if.
  - by eapply compat_binop.
  - by eapply compat_pair.
  - by eapply compat_fst.
  - by eapply compat_snd.
Qed.

(* Some dummy type interpretation. *)
Definition delta_emp : tyvar_interp := fun _ _ => False.

Corollary sem_soundness_closed e A :
  TY 0; [] |- e : A ->
  sem_expr_rel A delta_emp e.
Proof.
  intros Hsem%sem_soundness.
  specialize (Hsem delta_emp ids).
  asimpl in Hsem. apply Hsem. eapply sem_ctx_rel_nil.
Qed.

Corollary termination e A :
  (TY 0; [] |- e : A)%ty ->
  exists v, big_step e v.
Proof.
  intros Hsem%sem_soundness_closed.
  simp type_interp in Hsem.
  destruct Hsem as (v & Hbs & _).
  eauto.
Qed.

(** Semantic typing admits a substitution principle for values.
(The one for expressions is much harder to show.) *)
Lemma sem_type_subst delta v B e A :
  sem_val_rel B delta v ->
  TY 0; [B] |= e : A ->
  sem_expr_rel A delta e.[of_val v/].
Proof.
  intros Hv He. eapply He.
  intros x B'. rewrite list_lookup_singleton. destruct x; last done.
  intros [= <-]. simpl. eauto.
Qed.

(** We can even derive type safety from this result, completely bypassing the
syntactic type safety proof. This relies on our language being deterministic.
(For non-deterministic languages, we would have chosen a different expression
relation, so we could still obtain this same result. *)
Lemma sem_expr_rel_safe e A delta :
  sem_expr_rel A delta e ->
  safe e.
Proof.
  simp type_interp. intros Hsem.
  destruct Hsem as (v & Hevals & _).
  by eapply big_step_safe.
Qed.

Lemma sem_type_safety e A :
  TY 0; [] |= e : A ->
  safe e.
Proof.
  intros Hsem. eapply sem_expr_rel_safe.
  specialize (Hsem delta_emp ids).
  asimpl in Hsem. eapply Hsem.
  eapply sem_ctx_rel_nil.
Qed.

Corollary type_safety e A :
  TY 0; [] |- e : A ->
  safe e.
Proof.
  intros Htyped. eapply sem_type_safety. eapply sem_soundness. done.
Qed.
