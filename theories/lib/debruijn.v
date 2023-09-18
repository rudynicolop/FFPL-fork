From ffpl.lib Require Export prelude.
From Autosubst Require Export Autosubst.


(* [idss n sigma] alters the substitution [sigma] by
  "prepending" binders [0..n), so that [#i] is substituted for binder [i].
  After that, the binders from [sigma] follow.
 *)
Definition idss `{Ids X} (n : nat) (sigma : var -> X) (x : var) :=
  if decide (x < n) then ids x else sigma (x - n).
Lemma idss_0 `{Ids X} (sigma : var -> X) :
  idss 0 sigma = sigma.
Proof.
  f_ext. intros x; unfold idss. simpl.
  replace (x - 0) with x by lia. done.
Qed.
Lemma up_idss `{Ids X} `{Rename X} (sigma : var -> X) n :
  (* this precondition holds for the instances we are interested in,
    but is not a general law assumed by autosubst *)
  (forall x : var, rename (+1) (ids x) = ids (S x)) ->
  up (idss n sigma) = idss (S n) (sigma >>> rename (+1) ).
Proof.
  intros Hren_law.
  f_ext. intros x. destruct x as [ | x]; unfold idss; simpl; first done.
  unfold up. simpl.
  destruct (decide (x < n)).
  - rewrite decide_True; last lia. apply Hren_law.
  - rewrite decide_False; last lia. done.
Qed.

(* We will also need something like [idss] to shift variable renamings [var -> var].
  Instead of doing a separate definition like
  [ Definition idsc (n : nat) (sigma : var -> var) (x : var) := if decide (x < n) then x else sigma (x - n). ]
  we declare suitable instances to use [idss] for variable renamings.
*)
#[global] Instance Ids_var : Ids var. exact id. Defined.
#[global] Instance Rename_var : Rename var. exact id. Defined.

(* a lemma for the nat instance *)
Lemma upren_idss sigma n :
  upren (idss n sigma) = idss (S n) (sigma >>> S).
Proof.
  f_ext. intros x. destruct x as [ | x]; unfold idss; simpl; first done.
  destruct (decide (x < n)).
  - rewrite decide_True; [done | lia ].
  - rewrite decide_False; lia.
Qed.
