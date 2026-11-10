(** * Surface: algorithmic elaboration (milestone M6b)

    The declarative rules of [ElabSpec.v] guess types: the type arguments
    of a generic call, the parameter types of an unannotated lambda.  The
    rules here are *algorithmic*: a guess is a fresh metavariable (a type
    variable at or above [ntp E], see [Unify.v]), solved later by
    unification; every choice is made on types to which the current
    substitution has been applied.  The judgments thread the substitution
    [θ] and the next free metavariable [n]:

    - [Γ ⊩ᵃ[E;L] s ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'] : synthesis;
    - [Γ ⊩ᵃ[E;L] s ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n'] : checking; a construct
      without a checking rule of its own ([chk_spec]) is synthesized, and
      the two types are made equal by unification (or the suberror is
      promoted).

    [alg_sound] states that an algorithmic derivation becomes a
    declarative one once any substitution [σ] solving the final [θ'] (and
    leaving the type parameters alone) is applied to everything.

    Covered so far: the language of milestone M1. *)

From Stdlib Require Import List ZArith String Bool Arith Lia.
From MoonRocq.Prelude Require Import Result EqDec Ident.
From MoonRocq.Core Require Import Syntax Prim Subst Typing.
From MoonRocq.Surface Require Import Syntax Resolve Base ElabSpec Unify.
Import ListNotations.

Local Open Scope string_scope.

(** ** Surface types denote types over the type parameters *)

Section sty_ind'.
  Variable P : sty -> Prop.
  Hypothesis HName : forall p n args, Forall P args -> P (SName p n args).
  Hypothesis HTuple : forall p ts, Forall P ts -> P (STuple p ts).
  Hypothesis HArrow : forall p ps r eff, Forall P ps -> P r -> (forall t, eff = Some t -> P t) ->
                      P (SArrow p ps r eff).
  Hypothesis HObj : forall p Tr, P (SObj p Tr).

  Fixpoint sty_ind' (t : sty) : P t :=
    let fix go (ts : list sty) : Forall P ts :=
      match ts with
      | [] => Forall_nil P
      | t :: ts' => Forall_cons t (sty_ind' t) (go ts')
      end in
    match t with
    | SName p n args => HName p n args (go args)
    | STuple p ts => HTuple p ts (go ts)
    | SArrow p ps r eff =>
        HArrow p ps r eff (go ps) (sty_ind' r)
          (match eff as o return (forall t, o = Some t -> P t) with
           | Some t => fun t' H => match H in _ = o return match o with Some u => P u | None => True end with
                                   | eq_refl => sty_ind' t end
           | None => fun t' H => False_ind (P t')
                                   (match H in _ = o return match o with Some _ => False | None => True end with
                                    | eq_refl => I end)
           end)
    | SObj p Tr => HObj p Tr
    end.
End sty_ind'.

Lemma builtin_closed n τ k : assoc n builtin_types = Some τ -> occurs k τ = false.
Proof.
  intros H; unfold builtin_types in H; simpl in H.
  repeat match type of H with
         | (if ?c then _ else _) = _ => destruct c; [injection H as <-; reflexivity|]
         end; discriminate.
Qed.

Lemma index_of_lt x l i : index_of x l = Some i -> i < List.length l.
Proof.
  revert i; induction l as [|y l IH]; simpl; intros i H; [discriminate|].
  match type of H with (if ?c then _ else _) = _ => destruct c end; [injection H as <-; lia|].
  destruct (index_of x l) as [j|] eqn:E; simpl in H; [injection H as <-|discriminate].
  specialize (IH j eq_refl); lia.
Qed.

Lemma elab_ty_vars tys tps t : forall τ, elab_ty tys tps t = Ok τ ->
  forall k, occurs k τ = true -> k < List.length tps.
Proof.
  induction t as [p n args IH|p ts IH|p ps r eff IHps IHr IHe|p Tr] using sty_ind';
    intros τ H k Hk; cbn [elab_ty] in H.
  - destruct (index_of n tps) as [i|] eqn:Ei.
    + simpl in H; destruct args; [|discriminate]. injection H as <-; simpl in Hk.
      apply Nat.eqb_eq in Hk; subst; exact (index_of_lt _ _ _ Ei).
    + destruct (assoc n builtin_types) as [τ0|] eqn:Eb.
      * cbn iota in H; destruct args; [|discriminate]. injection H as <-.
        rewrite (builtin_closed _ _ k Eb) in Hk; discriminate.
      * simpl in H; destruct (assoc n tys) as [m|]; simpl in H.
        -- destruct (Nat.eqb m (List.length args)); [|discriminate].
           apply bind_ok_inv in H as (τs & Hm & H); injection H as <-.
           apply mapM_ok_inv in Hm. simpl in Hk; apply existsb_occ in Hk as (u & Hu & Hk).
           clear -IH Hm Hu Hk. induction Hm as [|a b args bs Hab _ IHm]; [contradiction|].
           inversion IH as [|? ? IHa IHargs]; subst.
           destruct Hu as [<-|Hu]; [exact (IHa _ Hab k Hk)|exact (IHm IHargs Hu)].
        -- destruct (array_kind_of n) as [ak|]; [|discriminate].
           destruct args as [|a [|]]; try discriminate.
           apply bind_ok_inv in H as (τ0 & Ha & H); injection H as <-.
           inversion IH as [|? ? IHa _]; subst. exact (IHa _ Ha k Hk).
  - apply bind_ok_inv in H as (τs & Hm & H); injection H as <-.
    apply mapM_ok_inv in Hm. simpl in Hk; apply existsb_occ in Hk as (u & Hu & Hk).
    clear -IH Hm Hu Hk. induction Hm as [|a b ts bs Hab _ IHm]; [contradiction|].
    inversion IH as [|? ? IHa IHts]; subst.
    destruct Hu as [<-|Hu]; [exact (IHa _ Hab k Hk)|exact (IHm IHts Hu)].
  - apply bind_ok_inv in H as (τs & Hm & H).
    apply bind_ok_inv in H as (τr & Hr & H).
    apply bind_ok_inv in H as (ε & He & H); injection H as <-.
    simpl in Hk; rewrite !orb_true_iff in Hk; destruct Hk as [[Hk|Hk]|Hk].
    + apply mapM_ok_inv in Hm. apply existsb_occ in Hk as (u & Hu & Hk).
      clear -IHps Hm Hu Hk. induction Hm as [|a b ps bs Hab _ IHm]; [contradiction|].
      inversion IHps as [|? ? IHa IHps']; subst.
      destruct Hu as [<-|Hu]; [exact (IHa _ Hab k Hk)|exact (IHm IHps' Hu)].
    + exact (IHr _ Hr k Hk).
    + destruct eff as [t|]; [exact (IHe t eq_refl _ He k Hk)|injection He as <-; discriminate].
  - injection H as <-; discriminate.
Qed.

(** ** Metavariables *)

(** The type parameters of the current definition are the rigid variables. *)
Definition ntp (E : senv) : nat := List.length (se_tps E).

Lemma ety_rigid E t τ σ : ety E t = Ok τ -> rigid (ntp E) σ -> tsubst σ τ = τ.
Proof.
  intros H Hr. rewrite <- (tsubst_var τ) at 2. apply tsubst_ext_occ; intros k Hk.
  apply Hr. pose proof (elab_ty_vars _ _ _ _ H k Hk) as Hlt.
  unfold meta, ntp; apply Nat.leb_gt; exact Hlt.
Qed.

Definition fresh (n k : nat) : list ty := map TVar (seq n k).

(** The parameter types of a lambda: the annotation, or a fresh metavariable. *)
Fixpoint aparams (E : senv) (ps : list (ident * option sty)) (n : nat) : option (list ty * nat) :=
  match ps with
  | [] => Some ([], n)
  | (_, Some t) :: ps' =>
      match ety E t with
      | Ok τ => option_map (fun r => (τ :: fst r, snd r)) (aparams E ps' n)
      | Err _ => None
      end
  | (_, None) :: ps' => option_map (fun r => (TVar n :: fst r, snd r)) (aparams E ps' (S n))
  end.

(** The equations making a lambda fit an expected function type: its
    annotations against the expected parameter, result and effect types. *)
Fixpoint fit_params (E : senv) (ps : list (ident * option sty)) (τs : list ty) : option (list (ty * ty)) :=
  match ps, τs with
  | [], [] => Some []
  | (_, None) :: ps', _ :: τs' => fit_params E ps' τs'
  | (_, Some t) :: ps', τ :: τs' =>
      match ety E t with
      | Ok τ' => option_map (cons (τ', τ)) (fit_params E ps' τs')
      | Err _ => None
      end
  | _, _ => None
  end.

Definition fit_ann (E : senv) (a : option sty) (τ : ty) : option (list (ty * ty)) :=
  match a with
  | None => Some []
  | Some t => match ety E t with Ok τ' => Some [(τ', τ)] | Err _ => None end
  end.

Definition fit_eff (E : senv) (a : option (option sty)) (ε : ty) : option (list (ty * ty)) :=
  match a with
  | None => Some []
  | Some None => Some [(TNever, ε)]
  | Some (Some t) => match ety E t with Ok ε' => Some [(ε', ε)] | Err _ => None end
  end.

Definition fit_lam (E : senv) (ps : list (ident * option sty)) (ret : option sty) (a : option (option sty))
    (τs : list ty) (r ε : ty) : option (list (ty * ty)) :=
  match fit_params E ps τs, fit_ann E ret r, fit_eff E a ε with
  | Some e1, Some e2, Some e3 => Some (List.app e1 (List.app e2 e3))
  | _, _, _ => None
  end.

(** Unification of several equations, the metavariables being below [n]. *)
Definition unify_all (E : senv) (n : nat) (θ : sub) (eqs : list (ty * ty)) : option sub :=
  unify_n (ntp E) (n - ntp E) θ eqs.

(** ** Implicit conversion *)

Definition up_case (τ' τ : ty) : option ident :=
  match τ', τ with TData T [], TError => Some T | _, _ => None end.

Inductive acoerce (E : senv) : sub -> nat -> expr -> ty -> ty -> expr -> sub -> Prop :=
| ACo_Up θ n e τ' τ T :
    up_case (sapp θ τ') (sapp θ τ) = Some T ->
    err_type E T ->
    acoerce E θ n e τ' τ (EUp T e) θ
| ACo_Unify θ n e τ' τ θ' :
    up_case (sapp θ τ') (sapp θ τ) = None ->
    unify_all E n θ [(τ', τ)] = Some θ' ->
    acoerce E θ n e τ' τ e θ'.

(** ** Which constructs have a checking rule of their own

    against the (resolved) expected type [τ]. *)
Definition chk_spec (E : senv) (Γ : lctx) (s : sexpr) (τ : ty) : bool :=
  match s with
  | SLit _ (SLInt None _) => match τ with TBase (BInt _) => true | _ => false end
  | SUnary _ op (SLit _ (SLInt _ _)) => String.eqb op "-"
  | SInfix _ op _ _ =>
      match assoc op arith_ops with
      | Some _ => ty_eqb (binop_res op τ) τ
      | None => false
      end
  | SLet _ _ _ _ _ => true
  | SIf _ _ _ (Some _) => true
  | STup _ ss => match τ with TTuple ts => Nat.eqb (List.length ts) (List.length ss) | _ => false end
  | SLam _ ps _ _ _ => match τ with TArrow τs _ _ => Nat.eqb (List.length τs) (List.length ps) | _ => false end
  | SApp _ (SVar _ g) args =>
      match lookup_local g Γ, lookup_fn (se_hdr E) g with
      | None, None =>
          ((String.eqb g "panic" && Nat.eqb (List.length args) 0) ||
           (String.eqb g "abort" && Nat.eqb (List.length args) 1))%bool
      | _, _ => false
      end
  | _ => false
  end.

(** A call's error handling, with the error type that may escape resolved. *)
Definition wrap_r (θ : sub) (L : cenv) (ε r : ty) (f : expr) (es : list expr) : expr :=
  wrap_call (set_exn (sapp θ (ce_exn L)) L) (sapp θ ε) r f es.

(** ** The rules *)

Reserved Notation "Γ ⊩ᵃ[ E ; L ] s ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'"
  (at level 70, E at level 200, L at level 200, s at level 60, τ at level 60, e at level 60,
   θ at level 60, n at level 60, θ' at level 60, n' at level 60, no associativity).
Reserved Notation "Γ ⊩ᵃ[ E ; L ] s ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n'"
  (at level 70, E at level 200, L at level 200, s at level 60, τ at level 60, e at level 60,
   θ at level 60, n at level 60, θ' at level 60, n' at level 60, no associativity).
Reserved Notation "Γ ⊩ᵃ[ E ; L ] s ⦂ a ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'"
  (at level 70, E at level 200, L at level 200, s at level 60, a at level 60, τ at level 60,
   e at level 60, θ at level 60, n at level 60, θ' at level 60, n' at level 60, no associativity).
Reserved Notation "Γ ⊩ᵃ*[ E ; L ] ss ⇒ τs ⇝ es ∣ θ ; n ↦ θ' ; n'"
  (at level 70, E at level 200, L at level 200, ss at level 60, τs at level 60, es at level 60,
   θ at level 60, n at level 60, θ' at level 60, n' at level 60, no associativity).
Reserved Notation "Γ ⊩ᵃ*[ E ; L ] ss ⇐ τs ⇝ es ∣ θ ; n ↦ θ' ; n'"
  (at level 70, E at level 200, L at level 200, ss at level 60, τs at level 60, es at level 60,
   θ at level 60, n at level 60, θ' at level 60, n' at level 60, no associativity).

Inductive asyn (E : senv) : cenv -> lctx -> sexpr -> sub -> nat -> ty -> expr -> sub -> nat -> Prop :=
(* variables *)
| A_Var L Γ p x i τ θ n :
    lookup_local x Γ = Some i ->
    nth_error (ctx_of Γ) i = Some τ ->
    is_cell τ = false ->
    Γ ⊩ᵃ[E;L] SVar p x ⇒ τ ⇝ EVar i ∣ θ ; n ↦ θ ; n
| A_VarMut L Γ p x i τ θ n :
    lookup_local x Γ = Some i ->
    nth_error (ctx_of Γ) i = Some (TRef τ) ->
    Γ ⊩ᵃ[E;L] SVar p x ⇒ τ ⇝ EMem (MGet τ) [EVar i] ∣ θ ; n ↦ θ ; n
(** a global function used as a value, at fresh type arguments *)
| A_Global L Γ p x fd θ n :
    lookup_local x Γ = None ->
    lookup_fn (se_hdr E) x = Some fd ->
    sbounds E x = [] ->
    Γ ⊩ᵃ[E;L] SVar p x ⇒ fn_inst fd (fresh n (fd_tparams fd)) ⇝ EGlobal x (fresh n (fd_tparams fd))
      ∣ θ ; n ↦ θ ; n + fd_tparams fd
(* literals and operators *)
| A_Lit L Γ p l l' θ n :
    lit_of l = Some l' ->
    Γ ⊩ᵃ[E;L] SLit p l ⇒ TBase (lit_ty l') ⇝ ELit l' ∣ θ ; n ↦ θ ; n
| A_NegLit L Γ p q k z τ e θ n θ' n' :
    Γ ⊩ᵃ[E;L] SLit q (SLInt k (Z.opp z)) ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SUnary p "-" (SLit q (SLInt k z)) ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'
| A_Neg L Γ p a τ k a' θ n θ' n' :
    int_lit a = false ->
    Γ ⊩ᵃ[E;L] a ⇒ τ ⇝ a' ∣ θ ; n ↦ θ' ; n' ->
    sapp θ' τ = TInt k ->
    Γ ⊩ᵃ[E;L] SUnary p "-" a ⇒ TInt k ⇝ EPrim (PIntNeg k) [a'] ∣ θ ; n ↦ θ' ; n'
| A_Not L Γ p a a' θ n θ' n' :
    Γ ⊩ᵃ[E;L] a ⇐ TBool ⇝ a' ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SUnary p "!" a ⇒ TBool ⇝ EPrim PBoolNot [a'] ∣ θ ; n ↦ θ' ; n'
| A_And L Γ p a b a' b' θ n θ1 n1 θ2 n2 :
    Γ ⊩ᵃ[E;L] a ⇐ TBool ⇝ a' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] b ⇐ TBool ⇝ b' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ[E;L] SInfix p "&&" a b ⇒ TBool ⇝ EIf a' b' e_false ∣ θ ; n ↦ θ2 ; n2
| A_Or L Γ p a b a' b' θ n θ1 n1 θ2 n2 :
    Γ ⊩ᵃ[E;L] a ⇐ TBool ⇝ a' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] b ⇐ TBool ⇝ b' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ[E;L] SInfix p "||" a b ⇒ TBool ⇝ EIf a' e_true b' ∣ θ ; n ↦ θ2 ; n2
(** the operator is chosen on the resolved operand type *)
| A_BinL L Γ p op a b τ a' b' e θ n θ1 n1 θ2 n2 :
    (flexible a && negb (flexible b))%bool = false ->
    Γ ⊩ᵃ[E;L] a ⇒ τ ⇝ a' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] b ⇐ τ ⇝ b' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    elab_binop p op (sapp θ2 τ) a' b' = Ok e ->
    Γ ⊩ᵃ[E;L] SInfix p op a b ⇒ binop_res op (sapp θ2 τ) ⇝ e ∣ θ ; n ↦ θ2 ; n2
| A_BinR L Γ p op a b τ a' b' e θ n θ1 n1 θ2 n2 :
    flexible a = true ->
    flexible b = false ->
    Γ ⊩ᵃ[E;L] b ⇒ τ ⇝ b' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] a ⇐ τ ⇝ a' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    elab_binop p op (sapp θ2 τ) a' b' = Ok e ->
    Γ ⊩ᵃ[E;L] SInfix p op a b ⇒ binop_res op (sapp θ2 τ) ⇝ e ∣ θ ; n ↦ θ2 ; n2
(* binding and control *)
| A_Let L Γ p x a s1 s2 τ1 τ e1 e2 θ n θ1 n1 θ2 n2 :
    Γ ⊩ᵃ[E;L] s1 ⦂ a ⇒ τ1 ⇝ e1 ∣ θ ; n ↦ θ1 ; n1 ->
    (x, τ1) :: Γ ⊩ᵃ[E;L] s2 ⇒ τ ⇝ e2 ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ[E;L] SLet p x a s1 s2 ⇒ τ ⇝ ELet e1 e2 ∣ θ ; n ↦ θ2 ; n2
| A_Annot L Γ p s t τ e θ n θ' n' :
    ety E t = Ok τ ->
    Γ ⊩ᵃ[E;L] s ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SAnnot p s t ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'
| A_If L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 :
    (diverges t && negb (diverges f))%bool = false ->
    Γ ⊩ᵃ[E;L] c ⇐ TBool ⇝ c' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] t ⇒ τ ⇝ t' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ[E;L] f ⇐ τ ⇝ f' ∣ θ2 ; n2 ↦ θ3 ; n3 ->
    Γ ⊩ᵃ[E;L] SIf p c t (Some f) ⇒ τ ⇝ EIf c' t' f' ∣ θ ; n ↦ θ3 ; n3
| A_IfR L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 :
    diverges t = true ->
    diverges f = false ->
    Γ ⊩ᵃ[E;L] c ⇐ TBool ⇝ c' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] f ⇒ τ ⇝ f' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ[E;L] t ⇐ τ ⇝ t' ∣ θ2 ; n2 ↦ θ3 ; n3 ->
    Γ ⊩ᵃ[E;L] SIf p c t (Some f) ⇒ τ ⇝ EIf c' t' f' ∣ θ ; n ↦ θ3 ; n3
| A_If1 L Γ p c t c' t' θ n θ1 n1 θ2 n2 :
    Γ ⊩ᵃ[E;L] c ⇐ TBool ⇝ c' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] t ⇐ TUnit ⇝ t' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ[E;L] SIf p c t None ⇒ TUnit ⇝ EIf c' t' (ELit LUnit) ∣ θ ; n ↦ θ2 ; n2
(* tuples *)
| A_Tuple L Γ p ss τs es θ n θ' n' :
    Γ ⊩ᵃ*[E;L] ss ⇒ τs ⇝ es ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] STup p ss ⇒ TTuple τs ⇝ ETuple es ∣ θ ; n ↦ θ' ; n'
| A_Proj L Γ p s i τ0 τs τ e θ n θ' n' :
    Γ ⊩ᵃ[E;L] s ⇒ τ0 ⇝ e ∣ θ ; n ↦ θ' ; n' ->
    sapp θ' τ0 = TTuple τs ->
    nth_error τs i = Some τ ->
    Γ ⊩ᵃ[E;L] SProj p s i ⇒ τ ⇝ EProj e i ∣ θ ; n ↦ θ' ; n'
(* functions *)
| A_LamRet L Γ p ps t a body τs r ε b θ n n1 θ' n' :
    aparams E ps n = Some (τs, n1) ->
    ety E t = Ok r ->
    eff_syn E a ε ->
    List.app (lam_ctx ps τs) Γ ⊩ᵃ[E;fun_env r ε] body ⇐ r ⇝ b ∣ θ ; n1 ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SLam p ps (Some t) a body ⇒ TArrow τs r ε ⇝ ELam τs r ε (eblock r b) ∣ θ ; n ↦ θ' ; n'
| A_Lam L Γ p ps a body τs r ε b θ n n1 θ' n' :
    aparams E ps n = Some (τs, n1) ->
    eff_syn E a ε ->
    List.app (lam_ctx ps τs) Γ ⊩ᵃ[E;mk_cenv [] ε] body ⇒ r ⇝ b ∣ θ ; n1 ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SLam p ps None a body ⇒ TArrow τs r ε ⇝ ELam τs r ε b ∣ θ ; n ↦ θ' ; n'
(** a call of a global function at fresh type arguments *)
| A_Call L Γ p q g args fd es θ n θ' n' :
    lookup_local g Γ = None ->
    lookup_fn (se_hdr E) g = Some fd ->
    sbounds E g = [] ->
    Γ ⊩ᵃ*[E;L] args ⇐ map (tsubst (inst (fresh n (fd_tparams fd)))) (fd_params fd) ⇝ es
      ∣ θ ; n + fd_tparams fd ↦ θ' ; n' ->
    call_allowed E (sapp θ' (tsubst (inst (fresh n (fd_tparams fd))) (fd_eff fd))) (sapp θ' (ce_exn L)) ->
    Γ ⊩ᵃ[E;L] SApp p (SVar q g) args ⇒ tsubst (inst (fresh n (fd_tparams fd))) (fd_ret fd)
      ⇝ wrap_r θ' L (tsubst (inst (fresh n (fd_tparams fd))) (fd_eff fd))
                (tsubst (inst (fresh n (fd_tparams fd))) (fd_ret fd))
                (EGlobal g (fresh n (fd_tparams fd))) es ∣ θ ; n ↦ θ' ; n'
(** a call of any other function value, whose type must be known *)
| A_CallExpr L Γ p f args τf ps r ε f' es θ n θ1 n1 θ2 n2 :
    callee Γ f ->
    Γ ⊩ᵃ[E;L] f ⇒ τf ⇝ f' ∣ θ ; n ↦ θ1 ; n1 ->
    sapp θ1 τf = TArrow ps r ε ->
    Γ ⊩ᵃ*[E;L] args ⇐ ps ⇝ es ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    call_allowed E (sapp θ2 ε) (sapp θ2 (ce_exn L)) ->
    Γ ⊩ᵃ[E;L] SApp p f args ⇒ r ⇝ wrap_r θ2 L ε r f' es ∣ θ ; n ↦ θ2 ; n2
(* builtins *)
| A_BNot L Γ p q a a' θ n θ' n' :
    builtin E Γ "not" ->
    Γ ⊩ᵃ[E;L] a ⇐ TBool ⇝ a' ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SApp p (SVar q "not") [a] ⇒ TBool ⇝ EPrim PBoolNot [a'] ∣ θ ; n ↦ θ' ; n'
| A_Ignore L Γ p q a τ a' θ n θ' n' :
    builtin E Γ "ignore" ->
    Γ ⊩ᵃ[E;L] a ⇒ τ ⇝ a' ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SApp p (SVar q "ignore") [a] ⇒ TUnit ⇝ ELet a' (ELit LUnit) ∣ θ ; n ↦ θ' ; n'
| A_Panic L Γ p q θ n :
    builtin E Γ "panic" ->
    Γ ⊩ᵃ[E;L] SApp p (SVar q "panic") [] ⇒ TUnit ⇝ EAbort TUnit ∣ θ ; n ↦ θ ; n
| A_Abort L Γ p q a a' θ n θ' n' :
    builtin E Γ "abort" ->
    Γ ⊩ᵃ[E;L] a ⇐ TString ⇝ a' ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SApp p (SVar q "abort") [a] ⇒ TUnit ⇝ ELet a' (EAbort TUnit) ∣ θ ; n ↦ θ' ; n'

with achk (E : senv) : cenv -> lctx -> sexpr -> ty -> sub -> nat -> expr -> sub -> nat -> Prop :=
(** without a checking rule of its own: synthesize, then convert *)
| B_Sub L Γ s τ τ' e e' θ n θ1 n1 θ2 :
    chk_spec E Γ s (sapp θ τ) = false ->
    Γ ⊩ᵃ[E;L] s ⇒ τ' ⇝ e ∣ θ ; n ↦ θ1 ; n1 ->
    acoerce E θ1 n1 e τ' τ e' θ2 ->
    Γ ⊩ᵃ[E;L] s ⇐ τ ⇝ e' ∣ θ ; n ↦ θ2 ; n1
| B_Lit L Γ p z k τ θ n :
    sapp θ τ = TInt k ->
    int_in_range k z = true ->
    Γ ⊩ᵃ[E;L] SLit p (SLInt None z) ⇐ τ ⇝ ELit (LInt k z) ∣ θ ; n ↦ θ ; n
| B_NegLit L Γ p q k z τ e θ n θ' n' :
    Γ ⊩ᵃ[E;L] SLit q (SLInt k (Z.opp z)) ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SUnary p "-" (SLit q (SLInt k z)) ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n'
| B_Bin L Γ p op a b τ o a' b' e θ n θ1 n1 θ2 n2 :
    assoc op arith_ops = Some o ->
    binop_res op (sapp θ τ) = sapp θ τ ->
    Γ ⊩ᵃ[E;L] a ⇐ τ ⇝ a' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] b ⇐ τ ⇝ b' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    elab_binop p op (sapp θ τ) a' b' = Ok e ->
    Γ ⊩ᵃ[E;L] SInfix p op a b ⇐ τ ⇝ e ∣ θ ; n ↦ θ2 ; n2
| B_Let L Γ p x a s1 s2 τ1 τ e1 e2 θ n θ1 n1 θ2 n2 :
    Γ ⊩ᵃ[E;L] s1 ⦂ a ⇒ τ1 ⇝ e1 ∣ θ ; n ↦ θ1 ; n1 ->
    (x, τ1) :: Γ ⊩ᵃ[E;L] s2 ⇐ τ ⇝ e2 ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ[E;L] SLet p x a s1 s2 ⇐ τ ⇝ ELet e1 e2 ∣ θ ; n ↦ θ2 ; n2
| B_If L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 :
    Γ ⊩ᵃ[E;L] c ⇐ TBool ⇝ c' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] t ⇐ τ ⇝ t' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ[E;L] f ⇐ τ ⇝ f' ∣ θ2 ; n2 ↦ θ3 ; n3 ->
    Γ ⊩ᵃ[E;L] SIf p c t (Some f) ⇐ τ ⇝ EIf c' t' f' ∣ θ ; n ↦ θ3 ; n3
| B_Tuple L Γ p ss τ ts es θ n θ' n' :
    sapp θ τ = TTuple ts ->
    List.length ts = List.length ss ->
    Γ ⊩ᵃ*[E;L] ss ⇐ ts ⇝ es ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] STup p ss ⇐ τ ⇝ ETuple es ∣ θ ; n ↦ θ' ; n'
(** a lambda against a known function type: its annotations are unified
    with the expected types *)
| B_Lam L Γ p ps ret a body τ τs r ε eqs b θ n θ1 θ' n' :
    sapp θ τ = TArrow τs r ε ->
    List.length τs = List.length ps ->
    fit_lam E ps ret a τs r ε = Some eqs ->
    unify_all E n θ eqs = Some θ1 ->
    List.app (lam_ctx ps τs) Γ ⊩ᵃ[E;fun_env r ε] body ⇐ r ⇝ b ∣ θ1 ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SLam p ps ret a body ⇐ τ ⇝ ELam τs r ε (eblock r b) ∣ θ ; n ↦ θ' ; n'
| B_Panic L Γ p q τ θ n :
    builtin E Γ "panic" ->
    Γ ⊩ᵃ[E;L] SApp p (SVar q "panic") [] ⇐ τ ⇝ EAbort τ ∣ θ ; n ↦ θ ; n
| B_Abort L Γ p q a a' τ θ n θ' n' :
    builtin E Γ "abort" ->
    Γ ⊩ᵃ[E;L] a ⇐ TString ⇝ a' ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SApp p (SVar q "abort") [a] ⇐ τ ⇝ ELet a' (EAbort τ) ∣ θ ; n ↦ θ' ; n'

with abind (E : senv) : cenv -> lctx -> sexpr -> option sty -> sub -> nat -> ty -> expr -> sub -> nat -> Prop :=
| AB_Syn L Γ s τ e θ n θ' n' :
    Γ ⊩ᵃ[E;L] s ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] s ⦂ None ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'
| AB_Ann L Γ s t τ e θ n θ' n' :
    ety E t = Ok τ ->
    Γ ⊩ᵃ[E;L] s ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] s ⦂ Some t ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'

with asyns (E : senv) : cenv -> lctx -> list sexpr -> sub -> nat -> list ty -> list expr -> sub -> nat -> Prop :=
| ASs_nil L Γ θ n :
    Γ ⊩ᵃ*[E;L] [] ⇒ [] ⇝ [] ∣ θ ; n ↦ θ ; n
| ASs_cons L Γ s ss τ τs e es θ n θ1 n1 θ2 n2 :
    Γ ⊩ᵃ[E;L] s ⇒ τ ⇝ e ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ*[E;L] ss ⇒ τs ⇝ es ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ*[E;L] s :: ss ⇒ τ :: τs ⇝ e :: es ∣ θ ; n ↦ θ2 ; n2

with achks (E : senv) : cenv -> lctx -> list sexpr -> list ty -> sub -> nat -> list expr -> sub -> nat -> Prop :=
| ACs_nil L Γ θ n :
    Γ ⊩ᵃ*[E;L] [] ⇐ [] ⇝ [] ∣ θ ; n ↦ θ ; n
| ACs_cons L Γ s ss τ τs e es θ n θ1 n1 θ2 n2 :
    Γ ⊩ᵃ[E;L] s ⇐ τ ⇝ e ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ*[E;L] ss ⇐ τs ⇝ es ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ*[E;L] s :: ss ⇐ τ :: τs ⇝ e :: es ∣ θ ; n ↦ θ2 ; n2

where "Γ ⊩ᵃ[ E ; L ] s ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'" := (asyn E L Γ s θ n τ e θ' n')
  and "Γ ⊩ᵃ[ E ; L ] s ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n'" := (achk E L Γ s τ θ n e θ' n')
  and "Γ ⊩ᵃ[ E ; L ] s ⦂ a ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'" := (abind E L Γ s a θ n τ e θ' n')
  and "Γ ⊩ᵃ*[ E ; L ] ss ⇒ τs ⇝ es ∣ θ ; n ↦ θ' ; n'" := (asyns E L Γ ss θ n τs es θ' n')
  and "Γ ⊩ᵃ*[ E ; L ] ss ⇐ τs ⇝ es ∣ θ ; n ↦ θ' ; n'" := (achks E L Γ ss τs θ n es θ' n').

Scheme asyn_mut := Minimality for asyn Sort Prop
  with achk_mut := Minimality for achk Sort Prop
  with abind_mut := Minimality for abind Sort Prop
  with asyns_mut := Minimality for asyns Sort Prop
  with achks_mut := Minimality for achks Sort Prop.
Combined Scheme alg_mutind from asyn_mut, achk_mut, abind_mut, asyns_mut, achks_mut.

(** ** Applying a substitution to the environments *)

Definition gsub (σ : nat -> ty) (Γ : lctx) : lctx := map (fun p => (fst p, tsubst σ (snd p))) Γ.

Definition lsub (σ : nat -> ty) (l : lab) : lab :=
  mk_lab (lb_name l) (lb_kind l) (map (tsubst σ) (lb_ps l)) (tsubst σ (lb_res l)).

Definition csub (σ : nat -> ty) (L : cenv) : cenv :=
  mk_cenv (map (lsub σ) (ce_labs L)) (tsubst σ (ce_exn L)).

Lemma lookup_gsub σ x Γ : lookup_local x (gsub σ Γ) = lookup_local x Γ.
Proof.
  induction Γ as [|[[y|] t] Γ IH]; simpl; auto.
  - destruct (eqb x y); auto; rewrite IH; reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma ctx_gsub σ Γ : ctx_of (gsub σ Γ) = map (tsubst σ) (ctx_of Γ).
Proof. unfold ctx_of, gsub; rewrite !map_map; reflexivity. Qed.

Lemma nth_gsub σ Γ i τ :
  nth_error (ctx_of Γ) i = Some τ -> nth_error (ctx_of (gsub σ Γ)) i = Some (tsubst σ τ).
Proof. intros H; rewrite ctx_gsub, nth_error_map, H; reflexivity. Qed.

Lemma lam_gsub σ ps τs Γ :
  gsub σ (List.app (lam_ctx ps τs) Γ) = List.app (lam_ctx ps (map (tsubst σ) τs)) (gsub σ Γ).
Proof.
  unfold gsub, lam_ctx; rewrite map_app; f_equal.
  revert τs; induction ps as [|xa ps IH]; intros [|τ τs]; simpl; auto; f_equal; apply IH.
Qed.

Lemma builtin_gsub E σ Γ g : builtin E Γ g -> builtin E (gsub σ Γ) g.
Proof. unfold builtin; rewrite lookup_gsub; auto. Qed.

Lemma callee_gsub σ Γ f : callee Γ f -> callee (gsub σ Γ) f.
Proof. destruct f; simpl; auto; rewrite lookup_gsub; auto. Qed.

(** ** Substitution and the choices of the rules *)

Lemma binop_subst σ p op τ a b e :
  elab_binop p op τ a b = Ok e ->
  tsubst σ τ = τ /\ elab_binop p op τ (esubst_ty σ a) (esubst_ty σ b) = Ok (esubst_ty σ e).
Proof.
  unfold elab_binop; intros H.
  destruct (assoc op arith_ops) as [o|], (assoc op cmp_ops) as [c|], τ;
    try discriminate H;
    repeat match goal with
           | b0 : base_ty |- _ => destruct b0; try discriminate H
           | o0 : arith_op |- _ => destruct o0; try discriminate H
           | c0 : cmp_op |- _ => destruct c0; try discriminate H
           end;
    injection H as <-; split; reflexivity.
Qed.

Lemma binop_res_fixed σ op τ : tsubst σ τ = τ -> tsubst σ (binop_res op τ) = binop_res op τ.
Proof.
  intros H; unfold binop_res.
  destruct (assoc op arith_ops) as [[]|], τ as [[]| | | | | | |]; auto.
Qed.

Lemma call_allowed_refl E x : call_allowed E x x.
Proof. destruct x as [| | | | T [|] | | |]; simpl; right; reflexivity. Qed.

Lemma call_allowed_subst E σ ε ρ : call_allowed E ε ρ -> call_allowed E (tsubst σ ε) (tsubst σ ρ).
Proof.
  intros H.
  assert (Hc : (exists T, ε = TData T [] /\ ρ = TError /\ err_type E T) \/ eff_le ε ρ).
  { destruct ε as [| | | | T [|] | | |], ρ as [| | | | | | |]; simpl in H; auto; left; eauto. }
  destruct Hc as [(T & -> & -> & HT)|[ -> | -> ]].
  - exact HT.
  - destruct (tsubst σ ρ) as [| | | | T [|] | | |]; simpl; left; reflexivity.
  - apply call_allowed_refl.
Qed.

Lemma esubst_map_proj σ es :
  map (esubst_ty σ) (map (fun i => EProj (EVar 0) i) (seq 1 (List.length es))) =
  map (fun i => EProj (EVar 0) i) (seq 1 (List.length (map (esubst_ty σ) es))).
Proof. rewrite length_map, map_map; reflexivity. Qed.

Lemma wrap_same L x r f es : ce_exn L = x -> wrap_call L x r f es = EApp f es.
Proof. intros H; unfold wrap_call; rewrite H; destruct x as [| | | | T [|] | | |]; reflexivity. Qed.

Lemma wrap_r_subst E σ θ L ε r f es :
  absorbs σ θ -> call_allowed E (sapp θ ε) (sapp θ (ce_exn L)) ->
  esubst_ty σ (wrap_r θ L ε r f es) =
  wrap_call (csub σ L) (tsubst σ ε) (tsubst σ r) (esubst_ty σ f) (map (esubst_ty σ) es).
Proof.
  intros Hσ H.
  assert (Hc : (exists T, sapp θ ε = TData T [] /\ sapp θ (ce_exn L) = TError) \/
               eff_le (sapp θ ε) (sapp θ (ce_exn L))).
  { destruct (sapp θ ε) as [| | | | T [|] | | |], (sapp θ (ce_exn L)) as [| | | | | | |];
      simpl in H; auto; left; eauto. }
  unfold wrap_r.
  destruct Hc as [(T & E1 & E2)|[E1|E1]].
  - unfold wrap_call; simpl; rewrite E1, E2.
    rewrite <- (absorbs_sapp σ θ ε Hσ), <- (absorbs_sapp σ θ (ce_exn L) Hσ), E1, E2; simpl.
    unfold promote_call; simpl; rewrite esubst_map_proj; reflexivity.
  - unfold wrap_call; simpl; rewrite E1.
    rewrite <- (absorbs_sapp σ θ ε Hσ), E1; reflexivity.
  - rewrite (wrap_same _ (sapp θ ε)) by (simpl; symmetry; exact E1).
    rewrite (wrap_same (csub σ L) (tsubst σ ε)); [reflexivity|].
    simpl; rewrite <- (absorbs_sapp σ θ ε Hσ), <- (absorbs_sapp σ θ (ce_exn L) Hσ), E1; reflexivity.
Qed.

Lemma fresh_length n k : List.length (fresh n k) = k.
Proof. unfold fresh; rewrite length_map, length_seq; reflexivity. Qed.

Lemma fn_inst_subst σ fd ts : tsubst σ (fn_inst fd ts) = fn_inst fd (map (tsubst σ) ts).
Proof.
  unfold fn_inst; simpl; rewrite map_map, !tsubst_inst; f_equal.
  apply map_ext; intros t; apply tsubst_inst.
Qed.

Lemma eff_syn_fixed E σ a ε : eff_syn E a ε -> rigid (ntp E) σ -> tsubst σ ε = ε.
Proof.
  destruct a as [[t|]|]; simpl; intros H Hr; subst; try reflexivity.
  eapply ety_rigid; eauto.
Qed.

Lemma aparams_ann E σ ps : forall n τs n1,
  aparams E ps n = Some (τs, n1) -> rigid (ntp E) σ -> params_ann E ps (map (tsubst σ) τs).
Proof.
  induction ps as [|[x [t|]] ps IH]; simpl; intros n τs n1 H Hr.
  - injection H as <- <-; constructor.
  - destruct (ety E t) as [τ|] eqn:Ht; [|discriminate].
    destruct (aparams E ps n) as [[τs' n']|] eqn:Hp; simpl in H; [|discriminate].
    injection H as <- <-; simpl. constructor; [simpl; rewrite (ety_rigid E t τ σ Ht Hr); exact Ht|].
    eapply IH; eauto.
  - destruct (aparams E ps (S n)) as [[τs' n']|] eqn:Hp; simpl in H; [|discriminate].
    injection H as <- <-; simpl. constructor; [exact I|]. eapply IH; eauto.
Qed.

Lemma fit_params_ann E σ ps : forall τs eqs,
  fit_params E ps τs = Some eqs -> eqs_by σ eqs -> rigid (ntp E) σ ->
  params_ann E ps (map (tsubst σ) τs).
Proof.
  induction ps as [|[x [t|]] ps IH]; intros [|τ τs] eqs H He Hr; simpl in H; try discriminate.
  - constructor.
  - destruct (ety E t) as [τ'|] eqn:Ht; [|discriminate].
    destruct (fit_params E ps τs) as [eqs'|] eqn:Hp; simpl in H; [|discriminate].
    injection H as <-. inversion He as [|? ? H1 H2]; subst; simpl in H1.
    constructor; [simpl; rewrite <- H1, (ety_rigid E t τ' σ Ht Hr); exact Ht|eapply IH; eauto].
  - constructor; [exact I|eapply IH; eauto].
Qed.

Lemma fit_lam_spec E σ ps ret a τs r ε eqs :
  fit_lam E ps ret a τs r ε = Some eqs -> eqs_by σ eqs -> rigid (ntp E) σ ->
  params_ann E ps (map (tsubst σ) τs) /\ ann_ok E ret (tsubst σ r) /\ eff_ann E a (tsubst σ ε).
Proof.
  unfold fit_lam; intros H He Hr.
  destruct (fit_params E ps τs) as [e1|] eqn:H1, (fit_ann E ret r) as [e2|] eqn:H2,
           (fit_eff E a ε) as [e3|] eqn:H3; try discriminate.
  injection H as <-. apply eqs_by_app in He as [He1 He]; apply eqs_by_app in He as [He2 He3].
  split; [eapply fit_params_ann; eauto|split].
  - destruct ret as [t|]; simpl in *; [|exact I].
    destruct (ety E t) as [τ'|] eqn:Ht; [|discriminate]. injection H2 as <-.
    inversion He2 as [|? ? Hq _]; subst; simpl in Hq.
    rewrite <- Hq, (ety_rigid E t τ' σ Ht Hr); first [exact Ht|reflexivity].
  - destruct a as [[t|]|]; simpl in *; [| |exact I].
    + destruct (ety E t) as [ε'|] eqn:Ht; [|discriminate]. injection H3 as <-.
      inversion He3 as [|? ? Hq _]; subst; simpl in Hq.
      rewrite <- Hq, (ety_rigid E t ε' σ Ht Hr); first [exact Ht|reflexivity].
    + injection H3 as <-. inversion He3 as [|? ? Hq _]; subst; simpl in Hq. symmetry; exact Hq.
Qed.

Lemma unify_all_spec E n θ eqs θ' :
  idem θ -> unify_all E n θ eqs = Some θ' ->
  idem θ' /\ absorbs (look θ') θ /\ (forall σ, absorbs σ θ' -> eqs_by σ eqs).
Proof.
  intros Hid H; destruct (unify_n_sound _ _ _ _ _ Hid H) as (H1 & H2 & H3 & _).
  split; [exact H1|split; [exact H2|]].
  intros σ Hσ; unfold eqs_by in *; rewrite Forall_forall in *; intros p Hp.
  specialize (H3 p Hp); cbv beta in H3 |- *.
  rewrite <- (absorbs_sapp σ θ' (fst p) Hσ), <- (absorbs_sapp σ θ' (snd p) Hσ). f_equal; exact H3.
Qed.

Lemma acoerce_spec E Γ θ n e τ' τ e' θ' :
  acoerce E θ n e τ' τ e' θ' -> idem θ ->
  idem θ' /\ absorbs (look θ') θ /\
  (forall σ, absorbs σ θ' -> ⊩ᶜ[E;gsub σ Γ] esubst_ty σ e : tsubst σ τ' ≼ tsubst σ τ ⇝ esubst_ty σ e').
Proof.
  destruct 1 as [θ n e τ' τ T Hu HT|θ n e τ' τ θ' Hu Hun]; intros Hid.
  - split; [exact Hid|split; [apply idem_absorbs; exact Hid|]]. intros σ Hσ.
    unfold up_case in Hu.
    destruct (sapp θ τ') as [| | | | T' [|] | | |] eqn:E1; try discriminate;
      destruct (sapp θ τ) as [| | | | | | |] eqn:E2; try discriminate.
    injection Hu as <-.
    rewrite <- (absorbs_sapp σ θ τ' Hσ), <- (absorbs_sapp σ θ τ Hσ), E1, E2; simpl.
    apply Co_Up; exact HT.
  - destruct (unify_all_spec E n θ _ θ' Hid Hun) as (H1 & H2 & H3).
    split; [exact H1|split; [exact H2|]]. intros σ Hσ.
    specialize (H3 σ Hσ); inversion H3 as [|? ? Hq _]; subst; simpl in Hq.
    rewrite Hq; apply Co_Refl.
Qed.

(** ** Soundness: algorithmic derivations are declarative ones *)

(** [θ'] extends [θ]. *)
Definition ext (θ' θ : sub) : Prop := idem θ' /\ absorbs (look θ') θ.

Ltac zero Hid :=
  split; [split; [exact Hid|apply idem_absorbs; exact Hid]|]; intros σ Hσ Hr.

Ltac one IH Hid :=
  let Hi1 := fresh "Hi" in let Hx1 := fresh "Hx" in let D1 := fresh "D" in
  destruct (IH Hid) as [[Hi1 Hx1] D1];
  split; [split; [exact Hi1|exact Hx1]|]; intros σ Hσ Hr;
  specialize (D1 σ Hσ Hr).

Ltac two IH1 IH2 Hid :=
  let Hi1 := fresh "Hi" in let Hx1 := fresh "Hx" in let D1 := fresh "D" in
  let Hi2 := fresh "Hi" in let Hx2 := fresh "Hx" in let D2 := fresh "D" in
  destruct (IH1 Hid) as [[Hi1 Hx1] D1];
  destruct (IH2 Hi1) as [[Hi2 Hx2] D2];
  split; [split; [exact Hi2|exact (absorbs_trans _ _ _ Hx2 Hx1)]|]; intros σ Hσ Hr;
  specialize (D1 σ (absorbs_trans _ _ _ Hσ Hx2) Hr); specialize (D2 σ Hσ Hr).

Ltac three IH1 IH2 IH3 Hid :=
  let Hi1 := fresh "Hi" in let Hx1 := fresh "Hx" in let D1 := fresh "D" in
  let Hi2 := fresh "Hi" in let Hx2 := fresh "Hx" in let D2 := fresh "D" in
  let Hi3 := fresh "Hi" in let Hx3 := fresh "Hx" in let D3 := fresh "D" in
  destruct (IH1 Hid) as [[Hi1 Hx1] D1];
  destruct (IH2 Hi1) as [[Hi2 Hx2] D2];
  destruct (IH3 Hi2) as [[Hi3 Hx3] D3];
  split; [split; [exact Hi3|exact (absorbs_trans _ _ _ (absorbs_trans _ _ _ Hx3 Hx2) Hx1)]|];
  intros σ Hσ Hr;
  specialize (D1 σ (absorbs_trans _ _ _ (absorbs_trans _ _ _ Hσ Hx3) Hx2) Hr);
  specialize (D2 σ (absorbs_trans _ _ _ Hσ Hx3) Hr); specialize (D3 σ Hσ Hr).

Section Sound.
  Variable E : senv.

  Theorem alg_sound :
    (forall L Γ s θ n τ e θ' n', Γ ⊩ᵃ[E;L] s ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n' -> idem θ ->
       ext θ' θ /\ forall σ, absorbs σ θ' -> rigid (ntp E) σ ->
         gsub σ Γ ⊩[E;csub σ L] s ⇒ tsubst σ τ ⇝ esubst_ty σ e) /\
    (forall L Γ s τ θ n e θ' n', Γ ⊩ᵃ[E;L] s ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n' -> idem θ ->
       ext θ' θ /\ forall σ, absorbs σ θ' -> rigid (ntp E) σ ->
         gsub σ Γ ⊩[E;csub σ L] s ⇐ tsubst σ τ ⇝ esubst_ty σ e) /\
    (forall L Γ s a θ n τ e θ' n', Γ ⊩ᵃ[E;L] s ⦂ a ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n' -> idem θ ->
       ext θ' θ /\ forall σ, absorbs σ θ' -> rigid (ntp E) σ ->
         gsub σ Γ ⊩[E;csub σ L] s ⦂ a ⇒ tsubst σ τ ⇝ esubst_ty σ e) /\
    (forall L Γ ss θ n τs es θ' n', Γ ⊩ᵃ*[E;L] ss ⇒ τs ⇝ es ∣ θ ; n ↦ θ' ; n' -> idem θ ->
       ext θ' θ /\ forall σ, absorbs σ θ' -> rigid (ntp E) σ ->
         gsub σ Γ ⊩*[E;csub σ L] ss ⇒ map (tsubst σ) τs ⇝ map (esubst_ty σ) es) /\
    (forall L Γ ss τs θ n es θ' n', Γ ⊩ᵃ*[E;L] ss ⇐ τs ⇝ es ∣ θ ; n ↦ θ' ; n' -> idem θ ->
       ext θ' θ /\ forall σ, absorbs σ θ' -> rigid (ntp E) σ ->
         gsub σ Γ ⊩*[E;csub σ L] ss ⇐ map (tsubst σ) τs ⇝ map (esubst_ty σ) es).
  Proof.
    apply alg_mutind.
    - (* A_Var *) intros L Γ p x i τ θ n Hl Hn Hc Hid; zero Hid.
      apply S_Var; [rewrite lookup_gsub; exact Hl|apply nth_gsub; exact Hn].
    - (* A_VarMut *) intros L Γ p x i τ θ n Hl Hn Hid; zero Hid.
      apply S_VarMut; [rewrite lookup_gsub; exact Hl|apply (nth_gsub σ) in Hn; exact Hn].
    - (* A_Global *) intros L Γ p x fd θ n Hl Hf Hsb Hid; zero Hid.
      rewrite fn_inst_subst; simpl. apply S_Global; auto.
      + rewrite lookup_gsub; exact Hl.
      + rewrite length_map, fresh_length; reflexivity.
    - (* A_Lit *) intros L Γ p l l' θ n Hl Hid; zero Hid. apply S_Lit; exact Hl.
    - (* A_NegLit *) intros L Γ p q k z τ e θ n θ' n' _ IH Hid; one IH Hid. apply S_NegLit; exact D.
    - (* A_Neg *) intros L Γ p a τ k a' θ n θ' n' Hia _ IH Hk Hid; one IH Hid.
      rewrite <- (absorbs_sapp σ θ' τ Hσ), Hk in D. apply S_Neg; auto.
    - (* A_Not *) intros L Γ p a a' θ n θ' n' _ IH Hid; one IH Hid. apply S_Not; exact D.
    - (* A_And *) intros L Γ p a b a' b' θ n θ1 n1 θ2 n2 _ IH1 _ IH2 Hid; two IH1 IH2 Hid.
      apply S_And; auto.
    - (* A_Or *) intros L Γ p a b a' b' θ n θ1 n1 θ2 n2 _ IH1 _ IH2 Hid; two IH1 IH2 Hid.
      apply S_Or; auto.
    - (* A_BinL *) intros L Γ p op a b τ a' b' e θ n θ1 n1 θ2 n2 Hfl _ IH1 _ IH2 Hb Hid; two IH1 IH2 Hid.
      destruct (binop_subst σ _ _ _ _ _ _ Hb) as [Hfix Hb'].
      assert (Hτ : tsubst σ τ = sapp θ2 τ) by (rewrite <- (absorbs_sapp σ θ2 τ Hσ); exact Hfix).
      rewrite Hτ in D, D0. rewrite (binop_res_fixed σ op _ Hfix).
      eapply S_BinL; [exact Hfl|exact D|exact D0|exact Hb'].
    - (* A_BinR *) intros L Γ p op a b τ a' b' e θ n θ1 n1 θ2 n2 Hfa Hfb _ IH1 _ IH2 Hb Hid; two IH1 IH2 Hid.
      destruct (binop_subst σ _ _ _ _ _ _ Hb) as [Hfix Hb'].
      assert (Hτ : tsubst σ τ = sapp θ2 τ) by (rewrite <- (absorbs_sapp σ θ2 τ Hσ); exact Hfix).
      rewrite Hτ in D, D0. rewrite (binop_res_fixed σ op _ Hfix).
      eapply S_BinR; [exact Hfa|exact Hfb|exact D|exact D0|exact Hb'].
    - (* A_Let *) intros L Γ p x a s1 s2 τ1 τ e1 e2 θ n θ1 n1 θ2 n2 _ IH1 _ IH2 Hid; two IH1 IH2 Hid.
      eapply S_Let; [exact D|exact D0].
    - (* A_Annot *) intros L Γ p s t τ e θ n θ' n' Ht _ IH Hid; one IH Hid.
      rewrite (ety_rigid E t τ σ Ht Hr) in *. apply S_Annot; auto.
    - (* A_If *) intros L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 Hd _ IHc _ IHt _ IHf Hid.
      three IHc IHt IHf Hid. apply S_If; auto.
    - (* A_IfR *) intros L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 Hdt Hdf _ IHc _ IHf _ IHt Hid.
      three IHc IHf IHt Hid. apply S_IfR; auto.
    - (* A_If1 *) intros L Γ p c t c' t' θ n θ1 n1 θ2 n2 _ IHc _ IHt Hid; two IHc IHt Hid.
      apply S_If1; auto.
    - (* A_Tuple *) intros L Γ p ss τs es θ n θ' n' _ IH Hid; one IH Hid. apply S_Tuple; exact D.
    - (* A_Proj *) intros L Γ p s i τ0 τs τ e θ n θ' n' _ IH Hτ Hi Hid; one IH Hid.
      rewrite <- (absorbs_sapp σ θ' τ0 Hσ), Hτ in D; simpl in D.
      eapply S_Proj; [exact D|rewrite nth_error_map, Hi; reflexivity].
    - (* A_LamRet *) intros L Γ p ps t a body τs r ε b θ n n1 θ' n' Hp Ht He _ IH Hid; one IH Hid.
      rewrite lam_gsub in D. change (csub σ (fun_env r ε)) with (fun_env (tsubst σ r) (tsubst σ ε)) in D.
      rewrite (ety_rigid E t r σ Ht Hr), (eff_syn_fixed E σ a ε He Hr) in D.
      simpl; rewrite (ety_rigid E t r σ Ht Hr), (eff_syn_fixed E σ a ε He Hr).
      apply S_LamRet; auto. eapply aparams_ann; eauto.
    - (* A_Lam *) intros L Γ p ps a body τs r ε b θ n n1 θ' n' Hp He _ IH Hid; one IH Hid.
      rewrite lam_gsub in D. change (csub σ (mk_cenv [] ε)) with (mk_cenv [] (tsubst σ ε)) in D.
      rewrite (eff_syn_fixed E σ a ε He Hr) in D.
      simpl; rewrite (eff_syn_fixed E σ a ε He Hr).
      apply S_Lam; auto. eapply aparams_ann; eauto.
    - (* A_Call *) intros L Γ p q g args fd es θ n θ' n' Hl Hf Hsb _ IH Hca Hid; one IH Hid.
      rewrite (wrap_r_subst E σ θ' L _ _ _ _ Hσ Hca); simpl.
      rewrite !tsubst_inst.
      change (map (esubst_ty σ) es) with (List.app [] (map (esubst_ty σ) es)).
      eapply S_Call.
      + rewrite lookup_gsub; exact Hl.
      + exact Hf.
      + rewrite length_map, fresh_length; reflexivity.
      + unfold nbounds; rewrite Hsb; simpl; constructor.
      + unfold nbounds; rewrite Hsb; simpl. rewrite map_map in D.
        erewrite map_ext; [exact D|]. intros u; cbv beta; symmetry; apply tsubst_inst.
      + unfold call_ok; simpl.
        pose proof (call_allowed_subst E σ _ _ Hca) as Hc.
        rewrite (absorbs_sapp σ θ' _ Hσ), (absorbs_sapp σ θ' _ Hσ), tsubst_inst in Hc; exact Hc.
    - (* A_CallExpr *) intros L Γ p f args τf ps r ε f' es θ n θ1 n1 θ2 n2 Hc _ IHf Hτ _ IHa Hca Hid.
      two IHf IHa Hid.
      rewrite (wrap_r_subst E σ θ2 L _ _ _ _ Hσ Hca).
      assert (Hσ1 : absorbs σ θ1) by (eapply absorbs_trans; eauto).
      rewrite <- (absorbs_sapp σ θ1 τf Hσ1), Hτ in D; simpl in D.
      eapply S_CallExpr; [apply callee_gsub; exact Hc|exact D|exact D0|].
      unfold call_ok; simpl.
      pose proof (call_allowed_subst E σ _ _ Hca) as Hc'.
      rewrite (absorbs_sapp σ θ2 _ Hσ), (absorbs_sapp σ θ2 _ Hσ) in Hc'; exact Hc'.
    - (* A_BNot *) intros L Γ p q a a' θ n θ' n' Hb _ IH Hid; one IH Hid.
      apply S_BNot; [apply builtin_gsub; exact Hb|exact D].
    - (* A_Ignore *) intros L Γ p q a τ a' θ n θ' n' Hb _ IH Hid; one IH Hid.
      eapply S_Ignore; [apply builtin_gsub; exact Hb|exact D].
    - (* A_Panic *) intros L Γ p q θ n Hb Hid; zero Hid. apply S_Panic; apply builtin_gsub; exact Hb.
    - (* A_Abort *) intros L Γ p q a a' θ n θ' n' Hb _ IH Hid; one IH Hid.
      apply S_Abort; [apply builtin_gsub; exact Hb|exact D].
    - (* B_Sub *) intros L Γ s τ τ' e e' θ n θ1 n1 θ2 Hcs _ IH Hco Hid.
      destruct (IH Hid) as [[Hi1 Hx1] D1].
      destruct (acoerce_spec E Γ _ _ _ _ _ _ _ Hco Hi1) as (Hi2 & Hx2 & C).
      split; [split; [exact Hi2|exact (absorbs_trans _ _ _ Hx2 Hx1)]|]; intros σ Hσ Hr.
      eapply C_Sub; [exact (D1 σ (absorbs_trans _ _ _ Hσ Hx2) Hr)|exact (C σ Hσ)].
    - (* B_Lit *) intros L Γ p z k τ θ n Hτ Hz Hid; zero Hid.
      rewrite <- (absorbs_sapp σ θ τ Hσ), Hτ; simpl. apply C_Lit; exact Hz.
    - (* B_NegLit *) intros L Γ p q k z τ e θ n θ' n' _ IH Hid; one IH Hid. apply C_NegLit; exact D.
    - (* B_Bin *) intros L Γ p op a b τ o a' b' e θ n θ1 n1 θ2 n2 Ho Hres _ IHa _ IHb Hb Hid.
      destruct (IHa Hid) as [[Hi1 Hx1] D1]; destruct (IHb Hi1) as [[Hi2 Hx2] D2].
      split; [split; [exact Hi2|exact (absorbs_trans _ _ _ Hx2 Hx1)]|]; intros σ Hσ Hr.
      assert (Hσ1 : absorbs σ θ1) by (eapply absorbs_trans; eauto).
      assert (Hσ0 : absorbs σ θ) by (eapply absorbs_trans; eauto).
      specialize (D1 σ Hσ1 Hr); specialize (D2 σ Hσ Hr).
      destruct (binop_subst σ _ _ _ _ _ _ Hb) as [Hfix Hb'].
      assert (Hτ : tsubst σ τ = sapp θ τ) by (rewrite <- (absorbs_sapp σ θ τ Hσ0); exact Hfix).
      rewrite Hτ in D1, D2 |- *. eapply C_Bin; [exact Hres|exact D1|exact D2|exact Hb'].
    - (* B_Let *) intros L Γ p x a s1 s2 τ1 τ e1 e2 θ n θ1 n1 θ2 n2 _ IH1 _ IH2 Hid; two IH1 IH2 Hid.
      eapply C_Let; [exact D|exact D0].
    - (* B_If *) intros L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 _ IHc _ IHt _ IHf Hid.
      three IHc IHt IHf Hid. apply C_If; auto.
    - (* B_Tuple *) intros L Γ p ss τ ts es θ n θ' n' Hτ Hlen _ IH Hid.
      destruct (IH Hid) as [[Hi1 Hx1] D1].
      split; [split; [exact Hi1|exact Hx1]|]; intros σ Hσ Hr.
      assert (Hσ0 : absorbs σ θ) by (eapply absorbs_trans; eauto).
      rewrite <- (absorbs_sapp σ θ τ Hσ0), Hτ; simpl. apply C_Tuple; exact (D1 σ Hσ Hr).
    - (* B_Lam *) intros L Γ p ps ret a body τ τs r ε eqs b θ n θ1 θ' n' Hτ Hlen Hfit Hun _ IH Hid.
      destruct (unify_all_spec E n θ eqs θ1 Hid Hun) as (Hi1 & Hx1 & Heq).
      destruct (IH Hi1) as [[Hi2 Hx2] D].
      split; [split; [exact Hi2|exact (absorbs_trans _ _ _ Hx2 Hx1)]|]; intros σ Hσ Hr.
      assert (Hσ1 : absorbs σ θ1) by (eapply absorbs_trans; eauto).
      assert (Hσ0 : absorbs σ θ) by (eapply absorbs_trans; eauto).
      destruct (fit_lam_spec E σ ps ret a τs r ε eqs Hfit (Heq σ Hσ1) Hr) as (Hps & Hret & Heff).
      specialize (D σ Hσ Hr). rewrite lam_gsub in D.
      change (csub σ (fun_env r ε)) with (fun_env (tsubst σ r) (tsubst σ ε)) in D.
      rewrite <- (absorbs_sapp σ θ τ Hσ0), Hτ; simpl. apply C_Lam; auto.
    - (* B_Panic *) intros L Γ p q τ θ n Hb Hid; zero Hid. apply C_Panic; apply builtin_gsub; exact Hb.
    - (* B_Abort *) intros L Γ p q a a' τ θ n θ' n' Hb _ IH Hid; one IH Hid.
      apply C_Abort; [apply builtin_gsub; exact Hb|exact D].
    - (* AB_Syn *) intros L Γ s τ e θ n θ' n' _ IH Hid; one IH Hid. apply B_Syn; exact D.
    - (* AB_Ann *) intros L Γ s t τ e θ n θ' n' Ht _ IH Hid; one IH Hid.
      rewrite (ety_rigid E t τ σ Ht Hr) in *. apply B_Ann; auto.
    - (* ASs_nil *) intros L Γ θ n Hid; zero Hid. constructor.
    - (* ASs_cons *) intros L Γ s ss τ τs e es θ n θ1 n1 θ2 n2 _ IH1 _ IH2 Hid; two IH1 IH2 Hid.
      constructor; auto.
    - (* ACs_nil *) intros L Γ θ n Hid; zero Hid. constructor.
    - (* ACs_cons *) intros L Γ s ss τ τs e es θ n θ1 n1 θ2 n2 _ IH1 _ IH2 Hid; two IH1 IH2 Hid.
      constructor; auto.
  Qed.
End Sound.
