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

(** ** Judgment notations

    - [Γ ⊢[ge] e : τ]    : expression [e] has type [τ] in context [Γ]
                           under global environment [ge] ([has_type]);
    - [Γ ⊢*[ge] es : τs] : pointwise typing of a list ([has_types]). *)

Reserved Notation "Γ ⊢[ ge ] e : τ"
  (at level 70, ge at level 200, e at level 60, τ at level 60, no associativity,
   format "Γ  ⊢[ ge ]  e  :  τ").
Reserved Notation "Γ ⊢*[ ge ] es : τs"
  (at level 70, ge at level 200, es at level 60, τs at level 60, no associativity,
   format "Γ  ⊢*[ ge ]  es  :  τs").

Inductive has_type (ge : genv) : ctx -> expr -> ty -> Prop :=
| T_Var Γ x τ :
    nth_error Γ x = Some τ ->
    Γ ⊢[ge] EVar x : τ
| T_Global Γ f ts fd :
    lookup_fn ge f = Some fd ->
    length ts = fd_tparams fd ->
    Γ ⊢[ge] EGlobal f ts
        : TArrow (map (tsubst (inst ts)) (fd_params fd)) (tsubst (inst ts) (fd_ret fd))
| T_Lit Γ l :
    Γ ⊢[ge] ELit l : TBase (lit_ty l)
| T_Lam Γ ps r b :
    ps ++ Γ ⊢[ge] b : r ->
    Γ ⊢[ge] ELam ps r b : TArrow ps r
| T_App Γ f args ps r :
    Γ ⊢[ge] f : TArrow ps r ->
    Γ ⊢*[ge] args : ps ->
    Γ ⊢[ge] EApp f args : r
| T_Let Γ e1 e2 τ1 τ2 :
    Γ ⊢[ge] e1 : τ1 ->
    τ1 :: Γ ⊢[ge] e2 : τ2 ->
    Γ ⊢[ge] ELet e1 e2 : τ2
| T_If Γ c t e τ :
    Γ ⊢[ge] c : TBool ->
    Γ ⊢[ge] t : τ ->
    Γ ⊢[ge] e : τ ->
    Γ ⊢[ge] EIf c t e : τ
| T_Tuple Γ es τs :
    Γ ⊢*[ge] es : τs ->
    Γ ⊢[ge] ETuple es : TTuple τs
| T_Proj Γ e i τs τ :
    Γ ⊢[ge] e : TTuple τs ->
    nth_error τs i = Some τ ->
    Γ ⊢[ge] EProj e i : τ
| T_Prim Γ op args :
    Γ ⊢*[ge] args : fst (prim_sig op) ->
    Γ ⊢[ge] EPrim op args : snd (prim_sig op)

with has_types (ge : genv) : ctx -> list expr -> list ty -> Prop :=
| Ts_nil Γ :
    Γ ⊢*[ge] [] : []
| Ts_cons Γ e es τ τs :
    Γ ⊢[ge] e : τ ->
    Γ ⊢*[ge] es : τs ->
    Γ ⊢*[ge] e :: es : τ :: τs

where "Γ ⊢[ ge ] e : τ" := (has_type ge Γ e τ)
  and "Γ ⊢*[ ge ] es : τs" := (has_types ge Γ es τs).

(** A top-level function is well typed when its body has the declared
    return type in the context of its parameters. *)
Definition fdef_ok (ge : genv) (fd : fdef) : Prop :=
  fd_params fd ⊢[ge] fd_body fd : fd_ret fd.

Scheme has_type_mut := Minimality for has_type Sort Prop
  with has_types_mut := Minimality for has_types Sort Prop.
Combined Scheme has_type_mutind from has_type_mut, has_types_mut.

(** A well-formed global environment: names are unique and every function
    is well typed against the whole environment (mutual recursion). *)
Definition genv_ok (ge : genv) : Prop :=
  NoDup (map fd_name ge) /\ Forall (fdef_ok ge) ge.

(** ** Basic facts about [has_types] *)

Lemma has_types_length ge Γ es τs : Γ ⊢*[ge] es : τs -> length es = length τs.
Proof. induction 1; simpl; auto. Qed.

Lemma has_types_app ge Γ es1 es2 τs1 τs2 :
  Γ ⊢*[ge] es1 : τs1 -> Γ ⊢*[ge] es2 : τs2 ->
  Γ ⊢*[ge] (es1 ++ es2) : (τs1 ++ τs2).
Proof. induction 1; simpl; auto using has_types. Qed.

Lemma has_types_nth ge Γ es τs x τ d :
  Γ ⊢*[ge] es : τs -> nth_error τs x = Some τ -> Γ ⊢[ge] nth x es d : τ.
Proof.
  intros H; revert x; induction H as [|Γ e es τ' τs He Hs IH]; intros [|x] Hx;
    simpl in *; try discriminate.
  - inversion Hx; subst; exact He.
  - eauto.
Qed.

Lemma has_types_nth_error ge Γ es τs x τ :
  Γ ⊢*[ge] es : τs -> nth_error τs x = Some τ ->
  exists e, nth_error es x = Some e /\ Γ ⊢[ge] e : τ.
Proof.
  intros H; revert x; induction H as [|Γ e es τ' τs He Hs IH]; intros [|x] Hx;
    simpl in *; try discriminate.
  - inversion Hx; subst; eauto.
  - eauto.
Qed.

Lemma has_types_app_inv ge Γ es τs1 τs2 :
  Γ ⊢*[ge] es : (τs1 ++ τs2) ->
  exists es1 es2, es = es1 ++ es2 /\ Γ ⊢*[ge] es1 : τs1 /\ Γ ⊢*[ge] es2 : τs2.
Proof.
  revert es; induction τs1 as [|τ τs1 IH]; simpl; intros es H.
  - exists [], es; repeat split; auto using has_types.
  - inversion H as [|? e es' ? ? He Hs]; subst.
    destruct (IH _ Hs) as (es1 & es2 & -> & H1 & H2).
    exists (e :: es1), es2; repeat split; auto using has_types.
Qed.
