(** * Core IR: declarative typing rules

    [has_type ge Γ e τ] is the specification of well-typedness.  It is an
    inductive relation in [Prop]; the executable checker in [Check.v]
    produces derivations of it (soundness by construction) and is proved
    complete for it in [CheckComplete.v]. *)

From Stdlib Require Import List Arith.
From MoonRocq.Prelude Require Import EqDec Ident.
From MoonRocq.Core Require Import Syntax Prim Subst.
Import ListNotations.

(** Typing context: index [0] is the innermost binder. *)
Definition ctx : Type := list ty.

(** ** Judgment notations

    - [Γ ⊢[ge;Σ;Λ] e : τ]    : expression [e] has type [τ] in context [Γ]
                               ([has_type], see below for [Σ] and [Λ]);
    - [Γ ⊢*[ge;Σ;Λ] es : τs] : pointwise typing of a list ([has_types]);
    - [Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ] : branches of a [match] ([has_branches]). *)

(** ** Patterns

    [⊢ᵖ[ge] p : τ ⇝ Δ] : pattern [p] matches values of type [τ] and binds
    variables of types [Δ] (leftmost first). *)

Reserved Notation "⊢ᵖ[ ge ] p : τ ⇝ Δ"
  (at level 70, ge at level 200, p at level 60, τ at level 60, Δ at level 60,
   no associativity, format "⊢ᵖ[ ge ]  p  :  τ  ⇝  Δ").
Reserved Notation "⊢ᵖ*[ ge ] ps : τs ⇝ Δ"
  (at level 70, ge at level 200, ps at level 60, τs at level 60, Δ at level 60,
   no associativity, format "⊢ᵖ*[ ge ]  ps  :  τs  ⇝  Δ").

Inductive pat_typed (ge : genv) : pat -> ty -> ctx -> Prop :=
| P_Wild τ :
    ⊢ᵖ[ge] PWild : τ ⇝ []
| P_Var τ :
    ⊢ᵖ[ge] PVar : τ ⇝ [τ]
| P_Lit l :
    ⊢ᵖ[ge] PLit l : TBase (lit_ty l) ⇝ []
| P_Tuple ps τs Δ :
    ⊢ᵖ*[ge] ps : τs ⇝ Δ ->
    ⊢ᵖ[ge] PTuple ps : TTuple τs ⇝ Δ
| P_Constr c ps T ts fs Δ :
    ctor_fields ge T c ts = Some fs ->
    ⊢ᵖ*[ge] ps : fs ⇝ Δ ->
    ⊢ᵖ[ge] PConstr c ps : TData T ts ⇝ Δ
| P_Ref p τ Δ :
    ⊢ᵖ[ge] p : τ ⇝ Δ ->
    ⊢ᵖ[ge] PRef p : TRef τ ⇝ Δ

with pats_typed (ge : genv) : list pat -> list ty -> ctx -> Prop :=
| Ps_nil :
    ⊢ᵖ*[ge] [] : [] ⇝ []
| Ps_cons p ps τ τs Δ1 Δ2 :
    ⊢ᵖ[ge] p : τ ⇝ Δ1 ->
    ⊢ᵖ*[ge] ps : τs ⇝ Δ2 ->
    ⊢ᵖ*[ge] p :: ps : τ :: τs ⇝ Δ1 ++ Δ2

where "⊢ᵖ[ ge ] p : τ ⇝ Δ" := (pat_typed ge p τ Δ)
  and "⊢ᵖ*[ ge ] ps : τs ⇝ Δ" := (pats_typed ge ps τs Δ).

Scheme pat_typed_mut := Minimality for pat_typed Sort Prop
  with pats_typed_mut := Minimality for pats_typed Sort Prop.
Combined Scheme pat_typed_mutind from pat_typed_mut, pats_typed_mut.

Lemma pat_typed_arity ge :
  (forall p τ Δ, ⊢ᵖ[ge] p : τ ⇝ Δ -> List.length Δ = pat_arity p) /\
  (forall ps τs Δ, ⊢ᵖ*[ge] ps : τs ⇝ Δ -> List.length Δ = list_sum (map pat_arity ps)).
Proof.
  apply pat_typed_mutind; intros; simpl; auto.
  rewrite length_app; auto.
Qed.

(** ** Expressions

    [Γ ⊢[ge;Σ;Λ] e : τ]: under global environment [ge] and store typing
    [Σ] (types of the store locations, milestone M3), with the enclosing
    loops [Λ] and the variables [Γ], expression [e] has type [τ].  A λ body
    starts with no enclosing loops: [break]/[continue] never cross a
    function boundary. *)

Reserved Notation "Γ ⊢[ ge ; Σ ; Λ ] e : τ"
  (at level 70, ge at level 200, Σ at level 200, Λ at level 200,
   e at level 60, τ at level 60, no associativity,
   format "Γ  ⊢[ ge ; Σ ; Λ ]  e  :  τ").
Reserved Notation "Γ ⊢*[ ge ; Σ ; Λ ] es : τs"
  (at level 70, ge at level 200, Σ at level 200, Λ at level 200,
   es at level 60, τs at level 60, no associativity,
   format "Γ  ⊢*[ ge ; Σ ; Λ ]  es  :  τs").
Reserved Notation "Γ ⊢ᵇ[ ge ; Σ ; Λ ] bs : τs ⇒ τ"
  (at level 70, ge at level 200, Σ at level 200, Λ at level 200,
   bs at level 60, τs at level 60, τ at level 60, no associativity,
   format "Γ  ⊢ᵇ[ ge ; Σ ; Λ ]  bs  :  τs  ⇒  τ").

Inductive has_type (ge : genv) (Σ : styping) : lblctx -> ctx -> expr -> ty -> Prop :=
| T_Var Λ Γ x τ :
    nth_error Γ x = Some τ ->
    Γ ⊢[ge;Σ;Λ] EVar x : τ
| T_Global Λ Γ f ts fd :
    lookup_fn ge f = Some fd ->
    length ts = fd_tparams fd ->
    Γ ⊢[ge;Σ;Λ] EGlobal f ts
        : TArrow (map (tsubst (inst ts)) (fd_params fd)) (tsubst (inst ts) (fd_ret fd))
| T_Lit Λ Γ l :
    Γ ⊢[ge;Σ;Λ] ELit l : TBase (lit_ty l)
| T_Lam Λ Γ ps r b :
    ps ++ Γ ⊢[ge;Σ;[]] b : r ->
    Γ ⊢[ge;Σ;Λ] ELam ps r b : TArrow ps r
| T_App Λ Γ f args ps r :
    Γ ⊢[ge;Σ;Λ] f : TArrow ps r ->
    Γ ⊢*[ge;Σ;Λ] args : ps ->
    Γ ⊢[ge;Σ;Λ] EApp f args : r
| T_Let Λ Γ e1 e2 τ1 τ2 :
    Γ ⊢[ge;Σ;Λ] e1 : τ1 ->
    τ1 :: Γ ⊢[ge;Σ;Λ] e2 : τ2 ->
    Γ ⊢[ge;Σ;Λ] ELet e1 e2 : τ2
| T_If Λ Γ c t e τ :
    Γ ⊢[ge;Σ;Λ] c : TBool ->
    Γ ⊢[ge;Σ;Λ] t : τ ->
    Γ ⊢[ge;Σ;Λ] e : τ ->
    Γ ⊢[ge;Σ;Λ] EIf c t e : τ
| T_Tuple Λ Γ es τs :
    Γ ⊢*[ge;Σ;Λ] es : τs ->
    Γ ⊢[ge;Σ;Λ] ETuple es : TTuple τs
| T_Proj Λ Γ e i τs τ :
    Γ ⊢[ge;Σ;Λ] e : TTuple τs ->
    nth_error τs i = Some τ ->
    Γ ⊢[ge;Σ;Λ] EProj e i : τ
| T_Prim Λ Γ op args :
    Γ ⊢*[ge;Σ;Λ] args : fst (prim_sig op) ->
    Γ ⊢[ge;Σ;Λ] EPrim op args : snd (prim_sig op)
| T_Constr Λ Γ T c ts e td cd :
    lookup_ty ge T = Some td ->
    length ts = td_tparams td ->
    lookup_ctor td c = Some cd ->
    Γ ⊢[ge;Σ;Λ] e : TTuple (map (tsubst (inst ts)) (cd_fields cd)) ->
    Γ ⊢[ge;Σ;Λ] EConstr T c ts e : TData T ts
| T_Match Λ Γ e τs τ bs :
    Γ ⊢[ge;Σ;Λ] e : τs ->
    Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ ->
    Γ ⊢[ge;Σ;Λ] EMatch e τ bs : τ
| T_Loc Λ Γ l s :
    nth_error Σ l = Some s ->
    Γ ⊢[ge;Σ;Λ] ELoc l : lty_ty s
| T_Mem Λ Γ op args :
    Γ ⊢*[ge;Σ;Λ] args : fst (mem_sig op) ->
    Γ ⊢[ge;Σ;Λ] EMem op args : snd (mem_sig op)
| T_Loop Λ Γ e ps τ b :
    Γ ⊢[ge;Σ;Λ] e : TTuple ps ->
    ps ++ Γ ⊢[ge;Σ;(ps, τ) :: Λ] b : τ ->
    Γ ⊢[ge;Σ;Λ] ELoop e ps τ b : τ
| T_Jump Λ Γ c k e τ lbl :
    nth_error Λ k = Some lbl ->
    Γ ⊢[ge;Σ;Λ] e : ctl_ty c lbl ->
    Γ ⊢[ge;Σ;Λ] EJump c k e τ : τ
(** [panic()] never returns, so it may have any type; the annotation keeps
    types unique. *)
| T_Abort Λ Γ τ :
    Γ ⊢[ge;Σ;Λ] EAbort τ : τ

with has_types (ge : genv) (Σ : styping) : lblctx -> ctx -> list expr -> list ty -> Prop :=
| Ts_nil Λ Γ :
    Γ ⊢*[ge;Σ;Λ] [] : []
| Ts_cons Λ Γ e es τ τs :
    Γ ⊢[ge;Σ;Λ] e : τ ->
    Γ ⊢*[ge;Σ;Λ] es : τs ->
    Γ ⊢*[ge;Σ;Λ] e :: es : τ :: τs

(** [Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ] : every branch matches a scrutinee of type
    [τs] and its body has type [τ] under the pattern's bindings. *)
with has_branches (ge : genv) (Σ : styping) :
    lblctx -> ctx -> list (pat * expr) -> ty -> ty -> Prop :=
| Bs_nil Λ Γ τs τ :
    Γ ⊢ᵇ[ge;Σ;Λ] [] : τs ⇒ τ
| Bs_cons Λ Γ p b bs τs τ Δ :
    ⊢ᵖ[ge] p : τs ⇝ Δ ->
    Δ ++ Γ ⊢[ge;Σ;Λ] b : τ ->
    Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ ->
    Γ ⊢ᵇ[ge;Σ;Λ] (p, b) :: bs : τs ⇒ τ

where "Γ ⊢[ ge ; Σ ; Λ ] e : τ" := (has_type ge Σ Λ Γ e τ)
  and "Γ ⊢*[ ge ; Σ ; Λ ] es : τs" := (has_types ge Σ Λ Γ es τs)
  and "Γ ⊢ᵇ[ ge ; Σ ; Λ ] bs : τs ⇒ τ" := (has_branches ge Σ Λ Γ bs τs τ).

(** A top-level function is well typed when its body has the declared
    return type in the context of its parameters (no store locations and
    no enclosing loops: source programs mention neither). *)
Definition fdef_ok (ge : genv) (fd : fdef) : Prop :=
  fd_params fd ⊢[ge;[];[]] fd_body fd : fd_ret fd.

Scheme has_type_mut := Minimality for has_type Sort Prop
  with has_types_mut := Minimality for has_types Sort Prop
  with has_branches_mut := Minimality for has_branches Sort Prop.
Combined Scheme has_type_mutind from has_type_mut, has_types_mut, has_branches_mut.

(** ** Well-formed types

    [ty_wf ge n t]: every data type in [t] exists and is applied to the
    right number of arguments, and type variables are below [n].  Soundness
    does not need it; it makes signatures and declarations meaningful (and
    makes [inst]'s default unreachable, decision 8). *)
Fixpoint ty_wfb (ge : genv) (n : nat) (t : ty) : bool :=
  match t with
  | TBase _ => true
  | TVar i => i <? n
  | TTuple ts => forallb (ty_wfb ge n) ts
  | TArrow ps r => forallb (ty_wfb ge n) ps && ty_wfb ge n r
  | TData T ts =>
      match lookup_ty ge T with
      | Some td => Nat.eqb (List.length ts) (td_tparams td) && forallb (ty_wfb ge n) ts
      | None => false
      end
  | TRef t => ty_wfb ge n t
  | TArray _ t => ty_wfb ge n t
  end.

Definition ty_wf (ge : genv) (n : nat) (t : ty) : Prop := ty_wfb ge n t = true.

Definition tdef_ok (ge : genv) (td : tdef) : Prop :=
  NoDup (map cd_name (td_ctors td)) /\
  Forall (fun cd => Forall (ty_wf ge (td_tparams td)) (cd_fields cd)) (td_ctors td).

Definition fsig_ok (ge : genv) (fd : fdef) : Prop :=
  Forall (ty_wf ge (fd_tparams fd)) (fd_params fd) /\ ty_wf ge (fd_tparams fd) (fd_ret fd).

(** A well-formed global environment: names are unique, data types are
    well formed, and every function has a well-formed signature and is well
    typed against the whole environment (mutual recursion). *)
Definition genv_ok (ge : genv) : Prop :=
  NoDup (map td_name (ge_types ge)) /\ Forall (tdef_ok ge) (ge_types ge) /\
  NoDup (map fd_name (ge_funs ge)) /\ Forall (fsig_ok ge) (ge_funs ge) /\
  Forall (fdef_ok ge) (ge_funs ge).

(** ** Basic facts about [has_types] *)

Section HasTypes.
  Variables (ge : genv) (Σ : styping) (Λ : lblctx).

  Lemma has_types_length Γ es τs : Γ ⊢*[ge;Σ;Λ] es : τs -> length es = length τs.
  Proof. induction 1; simpl; auto. Qed.

  Lemma has_types_app Γ es1 es2 τs1 τs2 :
    Γ ⊢*[ge;Σ;Λ] es1 : τs1 -> Γ ⊢*[ge;Σ;Λ] es2 : τs2 ->
    Γ ⊢*[ge;Σ;Λ] (es1 ++ es2) : (τs1 ++ τs2).
  Proof. induction 1; simpl; auto using has_types. Qed.

  Lemma has_types_nth Γ es τs x τ d :
    Γ ⊢*[ge;Σ;Λ] es : τs -> nth_error τs x = Some τ -> Γ ⊢[ge;Σ;Λ] nth x es d : τ.
  Proof.
    intros H; revert x; induction H as [|Λ' Γ' e es τ' τs He Hs IH]; intros [|x] Hx;
      simpl in *; try discriminate.
    - inversion Hx; subst; exact He.
    - eauto.
  Qed.

  Lemma has_types_nth_error Γ es τs x τ :
    Γ ⊢*[ge;Σ;Λ] es : τs -> nth_error τs x = Some τ ->
    exists e, nth_error es x = Some e /\ Γ ⊢[ge;Σ;Λ] e : τ.
  Proof.
    intros H; revert x; induction H as [|Λ' Γ' e es τ' τs He Hs IH]; intros [|x] Hx;
      simpl in *; try discriminate.
    - inversion Hx; subst; eauto.
    - eauto.
  Qed.

  Lemma has_types_app_inv Γ es τs1 τs2 :
    Γ ⊢*[ge;Σ;Λ] es : (τs1 ++ τs2) ->
    exists es1 es2, es = es1 ++ es2 /\ Γ ⊢*[ge;Σ;Λ] es1 : τs1 /\ Γ ⊢*[ge;Σ;Λ] es2 : τs2.
  Proof.
    revert es; induction τs1 as [|τ τs1 IH]; simpl; intros es H.
    - exists [], es; repeat split; auto using has_types.
    - inversion H as [|? ? e es' ? ? He Hs]; subst.
      destruct (IH _ Hs) as (es1 & es2 & -> & H1 & H2).
      exists (e :: es1), es2; repeat split; auto using has_types.
  Qed.
End HasTypes.
