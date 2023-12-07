From Autosubst Require Export Autosubst.
From ffpl.lib Require Export maps.

Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

(** ** Expressions / Terms. *)

(** This language includes a few extensions:
- products
- booleans and a unit value
- more arithmetic operations *)

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp (* Arithmetic *)
  | LtOp | LeOp | EqOp. (* Comparison *)

(* literals and our operators have decidable equality. *)
Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.

Inductive expr :=
  (* Base lambda calculus *)
  | Var (x : var)
  | Lam (e : {bind 1 of expr})
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | Lit (l : base_lit)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Polymorphism *)
  | TApp (e : expr)
  | TLam (e : expr)
  | Pack (e : expr)
  | Unpack (e1 : expr) (e2 : {bind 1 of expr})
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
.

(* Autosubst magic *)
#[export] Instance Ids_expr : Ids expr. derive. Defined.
#[export] Instance Rename_expr : Rename expr. derive. Defined.
#[export] Instance Subst_expr : Subst expr. derive. Defined.
#[export] Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Bind Scope expr_scope with expr.

(** Values *)
Inductive val :=
  | LitV (l : base_lit)
  | LamV (e : expr)
  | TLamV (e : expr)
  | PackV (v : val)
  | PairV (v1 v2 : val)
.

Bind Scope val_scope with val.

(** Conversion between expressions and values *)
Fixpoint of_val (v : val) : expr :=
  match v with
  | LitV l => Lit l
  | LamV e => Lam e
  | TLamV e => TLam e
  | PackV v => Pack (of_val v)
  | PairV v1 v2 => Pair (of_val v1) (of_val v2)
  end.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | Lit l => Some $ LitV l
  | Lam e => Some (LamV e)
  | TLam e => Some (TLamV e)
  | Pack e =>
     to_val e >>= (fun v => Some $ PackV v)
  | Pair e1 e2 =>
    to_val e1 >>= (fun v1 => to_val e2 >>= (fun v2 => Some $ PairV v1 v2))
  | _ => None
  end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof.
  revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
Qed.

#[export] Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite <-!to_of_val, Hv. Qed.

(** We also define an [is_val] predicate. This has the big advantage that it
reduces even with partial knowledge of [e], making it behave much nicer in our
automated type safety proof. *)
Fixpoint is_val (e : expr) : Prop :=
  match e with
  | Lit l => True
  | Lam e => True
  | TLam e => True
  | Pack e => is_val e
  | Pair e1 e2 => is_val e1 /\ is_val e2
  | _ => False
  end.

(** We can rewrite terms that are values into the form [of_val v]. *)
Lemma is_val_rewrite e : is_val e -> exists v, e = of_val v.
Proof.
  intros He.
  (* [cut] is "it suffices to show". *)
  cut (exists v, to_val e = Some v).
  { intros [v ?]. exists v. symmetry. apply of_to_val. done. }
  (* There are many cases to consider. *)
  revert He.
  induction e as [ | e IH | e1 IH1 e2 IH2 | | ? e1 IH1 e2 IH2 | e1 IH1 e2 IH2 e3 IH3 | e IH | e IH | e IH | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH | e IH ];
    simpl; try by eauto.
  - intros (v & ->)%IH. eauto.
  - intros [(v1 & ->)%IH1 (v2 & ->)%IH2]. eauto.
Qed.

(** In fact, [is_val] is fully characterized by these new operations. *)
Lemma is_val_spec e : is_val e <-> exists v, e = of_val v.
Proof.
  split; first by apply is_val_rewrite.
  intros [v ->]. induction v; simpl; eauto.
Qed.

(* We teach [eauto] that [of_val] produces values.
Stating this with an equality makes it work automatically in more situations. *)
Lemma is_val_of_val e v : e = of_val v -> is_val e.
Proof.
  intros ->. apply is_val_spec. by eexists.
Qed.
Lemma is_val_to_val e v : to_val e = Some v -> is_val e.
Proof.
  intros ?%of_to_val. eapply is_val_of_val. done.
Qed.

#[export] Hint Resolve is_val_of_val is_val_to_val : core.

(** Being a value is stable under substitution. *)
Lemma is_val_subst v sigma :
  is_val (of_val v).[sigma].
Proof.
  induction v; simpl; eauto.
Qed.

(** *** Contextual Semantics *)

(** * Base reduction *)

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | LeOp => Some $ LitBool (bool_decide (n1 <= n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  end%Z.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  match v1, v2 with
  | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
  | _, _ => None
  end.

Inductive base_step : expr -> expr -> Prop :=
  | BetaS e1 e2 e' :
     is_val e2 ->
     e' = e1.[e2/] ->
     base_step (App (Lam e1) e2) e'
  | TBetaS e1 :
      base_step (TApp (TLam e1)) e1
  | UnpackS e1 e2 e' :
      is_val e1 ->
      e' = e2.[e1/] ->
      base_step (Unpack (Pack e1) e2) e'
  | BinOpS op e1 v1 e2 v2 v' :
     to_val e1 = Some v1 ->
     to_val e2 = Some v2 ->
     bin_op_eval op v1 v2 = Some v' ->
     base_step (BinOp op e1 e2) (of_val v')
  | IfTrueS e1 e2 :
     base_step (If (Lit $ LitBool true) e1 e2) e1
  | IfFalseS e1 e2 :
     base_step (If (Lit $ LitBool false) e1 e2) e2
  | FstS e1 e2 :
     is_val e1 ->
     is_val e2 ->
     base_step (Fst (Pair e1 e2)) e1
  | SndS e1 e2 :
     is_val e1 ->
     is_val e2 ->
     base_step (Snd (Pair e1 e2)) e2
.
#[export] Hint Constructors base_step : core.

(** Values do not step. We won't actually need this theorem, but it
is a sanity checking which makes sure our definition of [is_val]
is coherent with the operational semantis. *)
Lemma base_step_no_val e1 e2 :
  base_step e1 e2 -> ~is_val e1.
Proof.
  intros Hstep [v ->]%is_val_rewrite. induction v; inversion Hstep.
Qed.

(** * Evaluation contexts *)

(** This time, we do not use lists but match the definition on paper. *)
Inductive ectx :=
  | HoleCtx
  | AppLCtx (K: ectx) (v2 : val)
  | AppRCtx (e1 : expr) (K: ectx)
  | TAppCtx (K: ectx)
  | PackCtx (K: ectx)
  | UnpackCtx (K: ectx) (e2 : expr)
  | BinOpLCtx (op : bin_op) (K: ectx) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr) (K: ectx)
  | IfCtx (K: ectx) (e1 e2 : expr)
  | PairLCtx (K: ectx) (v2 : val)
  | PairRCtx (e1 : expr) (K: ectx)
  | FstCtx (K: ectx)
  | SndCtx (K: ectx)
.

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | AppLCtx K v2 => App (fill K e) (of_val v2)
  | AppRCtx e1 K => App e1 (fill K e)
  | TAppCtx K => TApp (fill K e)
  | PackCtx K => Pack (fill K e)
  | UnpackCtx K e2 => Unpack (fill K e) e2
  | BinOpLCtx op K v2 => BinOp op (fill K e) (of_val v2)
  | BinOpRCtx op e1 K => BinOp op e1 (fill K e)
  | IfCtx K e1 e2 => If (fill K e) e1 e2
  | PairLCtx K v2 => Pair (fill K e) (of_val v2)
  | PairRCtx e1 K => Pair e1 (fill K e)
  | FstCtx K => Fst (fill K e)
  | SndCtx K => Snd (fill K e)
  end.

Fixpoint comp_ectx (K: ectx) (K' : ectx) : ectx :=
  match K with
  | HoleCtx => K'
  | AppLCtx K v2 => AppLCtx (comp_ectx K K') v2
  | AppRCtx e1 K => AppRCtx e1 (comp_ectx K K')
  | TAppCtx K => TAppCtx (comp_ectx K K')
  | PackCtx K => PackCtx (comp_ectx K K')
  | UnpackCtx K e2 => UnpackCtx (comp_ectx K K') e2
  | BinOpLCtx op K v2 => BinOpLCtx op (comp_ectx K K') v2
  | BinOpRCtx op e1 K => BinOpRCtx op e1 (comp_ectx K K')
  | IfCtx K e1 e2 => IfCtx (comp_ectx K K') e1 e2
  | PairLCtx K v2 => PairLCtx (comp_ectx K K') v2
  | PairRCtx e1 K => PairRCtx e1 (comp_ectx K K')
  | FstCtx K => FstCtx (comp_ectx K K')
  | SndCtx K => SndCtx (comp_ectx K K')
  end.

(** Basic properties of contexts *)
Definition empty_ectx := HoleCtx.

Lemma fill_empty e : fill empty_ectx e = e.
Proof. done. Qed.

Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. induction K1; simpl; congruence. Qed.

Lemma fill_is_val_inv K e :
  is_val (fill K e) -> is_val e.
Proof.
  (* There are a lot of cases to consider here, but we can handle them
  all the same way. *)
  induction K; intros [v Hv]%is_val_rewrite; simpl in *.
  { subst. eauto. }
  all: destruct v; try done; simpl in Hv; simplify_eq; eauto.
Qed.

(** * Contextual step relation *)

Inductive contextual_step (e1 : expr) (e2 : expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' -> e2 = fill K e2' ->
    base_step e1' e2' -> contextual_step e1 e2.
#[export] Hint Constructors contextual_step : core.

(** Basic properties of small-step semantics. *)
Lemma base_contextual_step e1 e2 :
  base_step e1 e2 -> contextual_step e1 e2.
Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

Lemma conextual_step_no_val e1 e2 :
  contextual_step e1 e2 -> ~is_val e1.
Proof.
  intros [K' e1' e2' -> ->] Hval. eapply base_step_no_val; first done.
  eapply fill_is_val_inv. done.
Qed.

Lemma fill_contextual_step K e1 e2 :
  contextual_step e1 e2 -> contextual_step (fill K e1) (fill K e2).
Proof.
  destruct 1 as [K' e1' e2' -> ->].
  rewrite !fill_comp. by econstructor.
Qed.

Lemma fill_rtc_contextual_step {e1 e2} K :
  rtc contextual_step e1 e2 ->
  rtc contextual_step (fill K e1) (fill K e2).
Proof.
  induction 1 as [ | x y z H1 H2 IH]; first done.
  eapply rtc_l; last apply IH.
  by apply fill_contextual_step.
Qed.

(* It is very helpful if [eauto] can automatically step below
all our evaluation contexts, so we prove lemmas for that and register
them with the hint database.
(For STLC, registering the constructors of the structural semantics did something
similar, but for SystemF we are only considering the contextual semantics.) *)

Lemma contextual_step_app_l e1 e1' e2 :
  is_val e2 ->
  contextual_step e1 e1' ->
  contextual_step (App e1 e2) (App e1' e2).
Proof.
  intros [v ->]%is_val_rewrite.
  by eapply (fill_contextual_step (AppLCtx HoleCtx v)).
Qed.

Lemma contextual_step_app_r e1 e2 e2' :
  contextual_step e2 e2' ->
  contextual_step (App e1 e2) (App e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (AppRCtx e1 HoleCtx)).
Qed.

Lemma contextual_step_tapp e e' :
  contextual_step e e' ->
  contextual_step (TApp e) (TApp e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (TAppCtx HoleCtx)).
Qed.

Lemma contextual_step_pack e e' :
  contextual_step e e' ->
  contextual_step (Pack e) (Pack e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (PackCtx HoleCtx)).
Qed.

Lemma contextual_step_unpack e e' e2 :
  contextual_step e e' ->
  contextual_step (Unpack e e2) (Unpack e' e2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (UnpackCtx HoleCtx e2)).
Qed.

Lemma contextual_step_binop_l op e1 e1' e2 :
  is_val e2 ->
  contextual_step e1 e1' ->
  contextual_step (BinOp op e1 e2) (BinOp op e1' e2).
Proof.
  intros [v ->]%is_val_rewrite Hcontextual.
  by eapply (fill_contextual_step (BinOpLCtx op HoleCtx v)).
Qed.

Lemma contextual_step_binop_r op e1 e2 e2' :
  contextual_step e2 e2' ->
  contextual_step (BinOp op e1 e2) (BinOp op e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (BinOpRCtx op e1 HoleCtx)).
Qed.

Lemma contextual_step_if e e' e1 e2 :
  contextual_step e e' ->
  contextual_step (If e e1 e2) (If e' e1 e2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (IfCtx HoleCtx e1 e2)).
Qed.

Lemma contextual_step_pair_l e1 e1' e2 :
  is_val e2 ->
  contextual_step e1 e1' ->
  contextual_step (Pair e1 e2) (Pair e1' e2).
Proof.
  intros [v ->]%is_val_rewrite Hcontextual.
  by eapply (fill_contextual_step (PairLCtx HoleCtx v)).
Qed.

Lemma contextual_step_pair_r e1 e2 e2' :
  contextual_step e2 e2' ->
  contextual_step (Pair e1 e2) (Pair e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (PairRCtx e1 HoleCtx)).
Qed.

Lemma contextual_step_fst e e' :
  contextual_step e e' ->
  contextual_step (Fst e) (Fst e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (FstCtx HoleCtx)).
Qed.

Lemma contextual_step_snd e e' :
  contextual_step e e' ->
  contextual_step (Snd e) (Snd e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (SndCtx HoleCtx)).
Qed.

#[export]
Hint Resolve
  contextual_step_app_l contextual_step_app_r contextual_step_tapp
  contextual_step_binop_l contextual_step_binop_r contextual_step_if
  contextual_step_pack contextual_step_unpack
  contextual_step_pair_l contextual_step_pair_r contextual_step_fst contextual_step_snd
  : core.
