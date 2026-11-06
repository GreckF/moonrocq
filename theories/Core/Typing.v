(** * Core IR: declarative typing rules

    [has_type ge Γ e τ] is the specification of well-typedness.  It is an
    inductive relation in [Prop]; the executable checker in [Check.v]
    produces derivations of it (soundness by construction) and is proved
    complete for it in [CheckComplete.v]. *)

From Stdlib Require Import List.
From MoonRocq.Prelude Require Import Ident.
From MoonRocq.Core Require Import Syntax Prim Subst.
Import ListNotations.

(** Typing context: index [0] is the innermost binder. *)
Definition ctx : Type := list ty.

Section Typing.
  Variable ge : genv.

  Inductive has_type : ctx -> expr -> ty -> Prop :=
  | T_Var Γ x τ :
      nth_error Γ x = Some τ ->
      has_type Γ (EVar x) τ
  | T_Global Γ f ts fd :
      lookup_fn ge f = Some fd ->
      length ts = fd_tparams fd ->
      has_type Γ (EGlobal f ts)
        (TArrow (map (tsubst (inst ts)) (fd_params fd)) (tsubst (inst ts) (fd_ret fd)))
  | T_Lit Γ l :
      has_type Γ (ELit l) (TBase (lit_ty l))
  | T_Lam Γ ps r b :
      has_type (ps ++ Γ) b r ->
      has_type Γ (ELam ps r b) (TArrow ps r)
  | T_App Γ f args ps r :
      has_type Γ f (TArrow ps r) ->
      has_types Γ args ps ->
      has_type Γ (EApp f args) r
  | T_Let Γ e1 e2 τ1 τ2 :
      has_type Γ e1 τ1 ->
      has_type (τ1 :: Γ) e2 τ2 ->
      has_type Γ (ELet e1 e2) τ2
  | T_If Γ c t e τ :
      has_type Γ c TBool ->
      has_type Γ t τ ->
      has_type Γ e τ ->
      has_type Γ (EIf c t e) τ
  | T_Tuple Γ es τs :
      has_types Γ es τs ->
      has_type Γ (ETuple es) (TTuple τs)
  | T_Proj Γ e i τs τ :
      has_type Γ e (TTuple τs) ->
      nth_error τs i = Some τ ->
      has_type Γ (EProj e i) τ
  | T_Prim Γ op args :
      has_types Γ args (fst (prim_sig op)) ->
      has_type Γ (EPrim op args) (snd (prim_sig op))

  with has_types : ctx -> list expr -> list ty -> Prop :=
  | Ts_nil Γ : has_types Γ [] []
  | Ts_cons Γ e es τ τs :
      has_type Γ e τ ->
      has_types Γ es τs ->
      has_types Γ (e :: es) (τ :: τs).

  (** A top-level function is well typed when its body has the declared
      return type in the context of its parameters. *)
  Definition fdef_ok (fd : fdef) : Prop :=
    has_type (fd_params fd) (fd_body fd) (fd_ret fd).
End Typing.

Scheme has_type_mut := Minimality for has_type Sort Prop
  with has_types_mut := Minimality for has_types Sort Prop.
Combined Scheme has_type_mutind from has_type_mut, has_types_mut.

(** A well-formed global environment: names are unique and every function
    is well typed against the whole environment (mutual recursion). *)
Definition genv_ok (ge : genv) : Prop :=
  NoDup (map fd_name ge) /\ Forall (fdef_ok ge) ge.

(** ** Basic facts about [has_types] *)

Lemma has_types_length ge Γ es τs : has_types ge Γ es τs -> length es = length τs.
Proof. induction 1; simpl; auto. Qed.

Lemma has_types_app ge Γ es1 es2 τs1 τs2 :
  has_types ge Γ es1 τs1 -> has_types ge Γ es2 τs2 ->
  has_types ge Γ (es1 ++ es2) (τs1 ++ τs2).
Proof. induction 1; simpl; auto using has_types. Qed.

Lemma has_types_nth ge Γ es τs x τ d :
  has_types ge Γ es τs -> nth_error τs x = Some τ -> has_type ge Γ (nth x es d) τ.
Proof.
  intros H; revert x; induction H as [|Γ e es τ' τs He Hs IH]; intros [|x] Hx;
    simpl in *; try discriminate.
  - inversion Hx; subst; exact He.
  - eauto.
Qed.

Lemma has_types_nth_error ge Γ es τs x τ :
  has_types ge Γ es τs -> nth_error τs x = Some τ ->
  exists e, nth_error es x = Some e /\ has_type ge Γ e τ.
Proof.
  intros H; revert x; induction H as [|Γ e es τ' τs He Hs IH]; intros [|x] Hx;
    simpl in *; try discriminate.
  - inversion Hx; subst; eauto.
  - eauto.
Qed.

Lemma has_types_app_inv ge Γ es τs1 τs2 :
  has_types ge Γ es (τs1 ++ τs2) ->
  exists es1 es2, es = es1 ++ es2 /\ has_types ge Γ es1 τs1 /\ has_types ge Γ es2 τs2.
Proof.
  revert es; induction τs1 as [|τ τs1 IH]; simpl; intros es H.
  - exists [], es; repeat split; auto using has_types.
  - inversion H as [|? e es' ? ? He Hs]; subst.
    destruct (IH _ Hs) as (es1 & es2 & -> & H1 & H2).
    exists (e :: es1), es2; repeat split; auto using has_types.
Qed.
