From Autosubst Require Export Autosubst.
From ffpl.lib Require Export maps.

Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

(** ** Expressions / Terms. *)

(** Locations are just integers.
This is vastly simplified compared to real languages, but will do for our purposes. *)
Definition loc := Z.

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc).
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
  (* State *)
  | Load (e : expr)
  | Store (e1 e2 : expr)
  | New (e : expr)
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
  induction e; simpl; try by eauto.
  - intros (v & ->)%IHe. eauto.
  - intros [(v1 & ->)%IHe1 (v2 & ->)%IHe2]. eauto.
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

(** *** Contextual Semantics *)

(** * Heaps *)

(** The heap maps locations to values *)
Definition heap := gmap loc val.

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

Inductive base_step : heap * expr -> heap * expr -> Prop :=
  | BetaS e1 e2 e' h :
     is_val e2 ->
     e' = e1.[e2/] ->
     base_step (h, App (Lam e1) e2) (h, e')
  | TBetaS e1 h :
      base_step (h, TApp (TLam e1)) (h, e1)
  | UnpackS e1 e2 e' h :
      is_val e1 ->
      e' = e2.[e1/] ->
      base_step (h, Unpack (Pack e1) e2) (h, e')
  | BinOpS op e1 v1 e2 v2 v' h :
     to_val e1 = Some v1 ->
     to_val e2 = Some v2 ->
     bin_op_eval op v1 v2 = Some v' ->
     base_step (h, BinOp op e1 e2) (h, of_val v')
  | IfTrueS e1 e2 h :
     base_step (h, If (Lit $ LitBool true) e1 e2) (h, e1)
  | IfFalseS e1 e2 h :
     base_step (h, If (Lit $ LitBool false) e1 e2) (h, e2)
  | FstS e1 e2 h :
     is_val e1 ->
     is_val e2 ->
     base_step (h, Fst (Pair e1 e2)) (h, e1)
  | SndS e1 e2 h :
     is_val e1 ->
     is_val e2 ->
     base_step (h, Snd (Pair e1 e2)) (h, e2)
  | NewS e v h l :
     l = fresh (dom h) ->
     to_val e = Some v ->
     base_step (h, New e) (<[l:=v]> h, Lit $ LitLoc l)
  | LoadS l v h :
     h !! l = Some v ->
     base_step (h, Load (Lit $ LitLoc l)) (h, of_val v)
  | StoreS l v w e2 h :
     h !! l = Some v ->
     to_val e2 = Some w ->
     base_step (h, Store (Lit $ LitLoc l) e2)
               (<[l:=w]> h, e2)
.
#[export] Hint Constructors base_step : core.

(** Values do not step. We won't actually need this theorem, but it
is a sanity checking which makes sure our definition of [is_val]
is coherent with the operational semantis. *)
Lemma base_step_no_val h1 e1 h2 e2 :
  base_step (h1, e1) (h2, e2) -> ~is_val e1.
Proof.
  intros Hstep [v ->]%is_val_rewrite. induction v; inversion Hstep.
Qed.

(** * Evaluation contexts *)

Inductive ectx :=
  | HoleCtx
  | AppLCtx (K : ectx) (v2 : val)
  | AppRCtx (e1 : expr) (K : ectx)
  | TAppCtx (K : ectx)
  | PackCtx (K : ectx)
  | UnpackCtx (K : ectx) (e2 : expr)
  | BinOpLCtx (op : bin_op) (K : ectx) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr) (K : ectx)
  | IfCtx (K : ectx) (e1 e2 : expr)
  | PairLCtx (K : ectx) (v2 : val)
  | PairRCtx (e1 : expr) (K : ectx)
  | FstCtx (K : ectx)
  | SndCtx (K : ectx)
  | LoadCtx (K : ectx)
  | StoreLCtx (K : ectx) (v2 : val)
  | StoreRCtx (e1 : expr) (K : ectx)
  | NewCtx (K : ectx)
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
  | LoadCtx K => Load (fill K e)
  | StoreLCtx K v2 => Store (fill K e) (of_val v2)
  | StoreRCtx e1 K => Store e1 (fill K e)
  | NewCtx K => New (fill K e)
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
  | LoadCtx K => LoadCtx (comp_ectx K K')
  | StoreLCtx K v2 => StoreLCtx (comp_ectx K K') v2
  | StoreRCtx e1 K => StoreRCtx e1 (comp_ectx K K')
  | NewCtx K => NewCtx (comp_ectx K K')
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

Inductive contextual_step : heap * expr -> heap * expr -> Prop :=
  Ectx_step K e1 e2 h1 h2 e1' e2' :
    e1 = fill K e1' -> e2 = fill K e2' ->
    base_step (h1, e1') (h2, e2') ->
    contextual_step (h1, e1) (h2, e2).
#[export] Hint Constructors contextual_step : core.

(** Basic properties of small-step semantics. *)
Lemma base_contextual_step e1 h1 e2 h2 :
  base_step (e1, h1) (e2, h2) -> contextual_step (e1, h1) (e2, h2).
Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

Lemma conextual_step_no_val e1 h1 e2 h2 :
  contextual_step (h1, e1) (h2, e2) -> ~is_val e1.
Proof.
  inversion 1; simplify_eq. intros Hval.
  eapply base_step_no_val; first done.
  eapply fill_is_val_inv. done.
Qed.

Lemma fill_contextual_step K e1 h1 e2 h2 :
  contextual_step (h1, e1) (h2, e2) ->
  contextual_step (h1, fill K e1) (h2, fill K e2).
Proof.
  inversion 1; simplify_eq.
  rewrite !fill_comp. by econstructor.
Qed.

Lemma fill_rtc_contextual_step {e1 h1 e2 h2} K :
  rtc contextual_step (h1, e1) (h2, e2) ->
  rtc contextual_step (h1, fill K e1) (h2, fill K e2).
Proof.
  remember (h1, e1) as cfg1 eqn:Hcfg1.
  remember (h2, e2) as cfg2 eqn:Hcfg2.
  induction 1 as [ | x [e' h'] z H1 H2 IH] in
    e1, h1, Hcfg1, e2, h2, Hcfg2 |- *; simplify_eq.
  { done. }
  eapply rtc_l; last by apply IH.
  by apply fill_contextual_step.
Qed.

(* It is very helpful if [eauto] can automatically step below
all our evaluation contexts, so we prove lemmas for that and register
them with the hint database.
(For STLC, registering the constructors of the structural semantics did something
similar, but for SystemF we are only considering the contextual semantics.) *)

Lemma contextual_step_app_l e1 e1' e2 h1 h2 :
  is_val e2 ->
  contextual_step (h1, e1) (h2, e1') ->
  contextual_step (h1, App e1 e2) (h2, App e1' e2).
Proof.
  intros [v ->]%is_val_rewrite.
  by eapply (fill_contextual_step (AppLCtx HoleCtx v)).
Qed.

Lemma contextual_step_app_r e1 e2 e2' h1 h2 :
  contextual_step (h1, e2) (h2, e2') ->
  contextual_step (h1, App e1 e2) (h2, App e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (AppRCtx e1 HoleCtx)).
Qed.

Lemma contextual_step_tapp e e' h1 h2 :
  contextual_step (h1, e) (h2, e') ->
  contextual_step (h1, TApp e) (h2, TApp e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (TAppCtx HoleCtx)).
Qed.

Lemma contextual_step_pack e e' h1 h2 :
  contextual_step (h1, e) (h2, e') ->
  contextual_step (h1, Pack e) (h2, Pack e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (PackCtx HoleCtx)).
Qed.

Lemma contextual_step_unpack e e' e2 h1 h2 :
  contextual_step (h1, e) (h2, e') ->
  contextual_step (h1, Unpack e e2) (h2, Unpack e' e2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (UnpackCtx HoleCtx e2)).
Qed.

Lemma contextual_step_binop_l op e1 e1' e2 h1 h2 :
  is_val e2 ->
  contextual_step (h1, e1) (h2, e1') ->
  contextual_step (h1, BinOp op e1 e2) (h2, BinOp op e1' e2).
Proof.
  intros [v ->]%is_val_rewrite Hcontextual.
  by eapply (fill_contextual_step (BinOpLCtx op HoleCtx v)).
Qed.

Lemma contextual_step_binop_r op e1 e2 e2' h1 h2 :
  contextual_step (h1, e2) (h2, e2') ->
  contextual_step (h1, BinOp op e1 e2) (h2, BinOp op e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (BinOpRCtx op e1 HoleCtx)).
Qed.

Lemma contextual_step_if e e' e1 e2 h1 h2 :
  contextual_step (h1, e) (h2, e') ->
  contextual_step (h1, If e e1 e2) (h2, If e' e1 e2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (IfCtx HoleCtx e1 e2)).
Qed.

Lemma contextual_step_pair_l e1 e1' e2 h1 h2 :
  is_val e2 ->
  contextual_step (h1, e1) (h2, e1') ->
  contextual_step (h1, Pair e1 e2) (h2, Pair e1' e2).
Proof.
  intros [v ->]%is_val_rewrite Hcontextual.
  by eapply (fill_contextual_step (PairLCtx HoleCtx v)).
Qed.

Lemma contextual_step_pair_r e1 e2 e2' h1 h2 :
  contextual_step (h1, e2) (h2, e2') ->
  contextual_step (h1, Pair e1 e2) (h2, Pair e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (PairRCtx e1 HoleCtx)).
Qed.

Lemma contextual_step_fst e e' h1 h2 :
  contextual_step (h1, e) (h2, e') ->
  contextual_step (h1, Fst e) (h2, Fst e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (FstCtx HoleCtx)).
Qed.

Lemma contextual_step_snd e e' h1 h2 :
  contextual_step (h1, e) (h2, e') ->
  contextual_step (h1, Snd e) (h2, Snd e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (SndCtx HoleCtx)).
Qed.

Lemma contextual_step_new e e' h1 h2 :
  contextual_step (h1, e) (h2, e') ->
  contextual_step (h1, New e) (h2, New e').
Proof. by apply (fill_contextual_step (NewCtx HoleCtx)). Qed.

Lemma contextual_step_load e e' h1 h2 :
  contextual_step (h1, e) (h2, e') ->
  contextual_step (h1, Load e) (h2, Load e').
Proof. by apply (fill_contextual_step (LoadCtx HoleCtx)). Qed.

Lemma contextual_step_store_r e1 e2 e2' h1 h2 :
  contextual_step (h1, e2) (h2, e2') ->
  contextual_step (h1, Store e1 e2) (h2, Store e1 e2').
Proof. by apply (fill_contextual_step (StoreRCtx _ HoleCtx)). Qed.

Lemma contextual_step_store_l e1 e1' e2 h1 h2 :
  is_val e2 ->
  contextual_step (h1, e1) (h2, e1') ->
  contextual_step (h1, Store e1 e2) (h2, Store e1' e2).
Proof.
  intros [v ->]%is_val_rewrite Hcontextual.
  by eapply (fill_contextual_step (StoreLCtx HoleCtx _)).
Qed.

#[export]
Hint Resolve
  contextual_step_app_l contextual_step_app_r contextual_step_tapp
  contextual_step_binop_l contextual_step_binop_r contextual_step_if
  contextual_step_pack contextual_step_unpack
  contextual_step_pair_l contextual_step_pair_r contextual_step_fst contextual_step_snd
  contextual_step_new contextual_step_load contextual_step_store_r contextual_step_store_l
   : core.

(** * Define various notions of "good" terms. *)

(** A term is reducible if it can take a step. *)
Definition reducible (h : heap) (e : expr) :=
  exists h' e', contextual_step (h, e) (h', e').

(** A term is progressive if it either is a value or it is reducible. *)
Definition progressive (h : heap) (e : expr) :=
  is_val e \/ reducible h e.

(** A term is safe if every term it can reach is progressive. *)
Definition safe h e :=
  forall h' e', rtc contextual_step (h, e) (h', e') -> progressive h' e'.

(** We instruct [eauto] to unfold [reducible] and [progressive]
in order to make progress on the goal. *)
#[export]
Hint Unfold reducible progressive : core.
