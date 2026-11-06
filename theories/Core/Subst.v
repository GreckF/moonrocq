(** * Substitution

    - [tsubst σ t]   : type substitution (no binders inside types, so no shifting);
    - [esubst_ty σ e]: type substitution inside the annotations of an expression;
    - [rename ξ e], [subst σ e]: parallel renaming / substitution of term
      variables, with [upren]/[upsub] lifting under an [n]-ary binder. *)

From Stdlib Require Import List Arith Lia.
From MoonRocq.Prelude Require Import Ident.
From MoonRocq.Core Require Import Syntax Prim.
Import ListNotations.

(** ** Types *)

Fixpoint tsubst (σ : nat -> ty) (t : ty) : ty :=
  match t with
  | TBase b => TBase b
  | TVar i => σ i
  | TTuple ts => TTuple (map (tsubst σ) ts)
  | TArrow ps r => TArrow (map (tsubst σ) ps) (tsubst σ r)
  | TData T ts => TData T (map (tsubst σ) ts)
  end.

(** Instantiation of the type parameters of a global with explicit type
    arguments.  Out-of-range indices are mapped to [Unit]; well-formed
    signatures never hit that case, and choosing a closed default makes
    [tsubst_inst] below hold unconditionally. *)
Definition inst (ts : list ty) (i : nat) : ty := nth i ts TUnit.

Lemma tsubst_ext σ σ' t : (forall i, σ i = σ' i) -> tsubst σ t = tsubst σ' t.
Proof.
  intros E; induction t as [b|i|ts IH|ps r IHps IHr|T ts IH] using ty_ind'; simpl; auto.
  - f_equal. induction IH; simpl; f_equal; auto.
  - f_equal; auto. induction IHps; simpl; f_equal; auto.
  - f_equal. induction IH; simpl; f_equal; auto.
Qed.

Lemma tsubst_comp σ ρ t : tsubst σ (tsubst ρ t) = tsubst (fun i => tsubst σ (ρ i)) t.
Proof.
  induction t as [b|i|ts IH|ps r IHps IHr|T ts IH] using ty_ind'; simpl; auto.
  - f_equal. rewrite map_map. induction IH; simpl; f_equal; auto.
  - f_equal; auto. rewrite map_map. induction IHps; simpl; f_equal; auto.
  - f_equal. rewrite map_map. induction IH; simpl; f_equal; auto.
Qed.

Lemma tsubst_inst σ ts t :
  tsubst σ (tsubst (inst ts) t) = tsubst (inst (map (tsubst σ) ts)) t.
Proof.
  rewrite tsubst_comp. apply tsubst_ext. intros i; unfold inst.
  change TUnit with (tsubst σ TUnit) at 2. now rewrite map_nth.
Qed.

Lemma prim_sig_closed σ op :
  map (tsubst σ) (fst (prim_sig op)) = fst (prim_sig op) /\
  tsubst σ (snd (prim_sig op)) = snd (prim_sig op).
Proof. destruct op; split; reflexivity. Qed.

(** Field types of constructor [c] of the data type [T[ts]]. *)
Definition ctor_fields (ge : genv) (T c : ident) (ts : list ty) : option (list ty) :=
  match lookup_ty ge T with
  | Some td =>
      match lookup_ctor td c with
      | Some cd => Some (map (tsubst (inst ts)) (cd_fields cd))
      | None => None
      end
  | None => None
  end.

Lemma ctor_fields_tsubst σ ge T c ts fs :
  ctor_fields ge T c ts = Some fs ->
  ctor_fields ge T c (map (tsubst σ) ts) = Some (map (tsubst σ) fs).
Proof.
  unfold ctor_fields. destruct (lookup_ty ge T) as [td|]; [|discriminate].
  destruct (lookup_ctor td c) as [cd|]; [|discriminate].
  intros E; inversion E; subst. f_equal.
  rewrite map_map. apply map_ext. intros; symmetry; apply tsubst_inst.
Qed.

(** ** Type substitution in expressions *)

Fixpoint esubst_ty (σ : nat -> ty) (e : expr) : expr :=
  match e with
  | EVar x => EVar x
  | EGlobal f ts => EGlobal f (map (tsubst σ) ts)
  | ELit l => ELit l
  | ELam ps r b => ELam (map (tsubst σ) ps) (tsubst σ r) (esubst_ty σ b)
  | EApp f args => EApp (esubst_ty σ f) (map (esubst_ty σ) args)
  | ELet e1 e2 => ELet (esubst_ty σ e1) (esubst_ty σ e2)
  | EIf c t e => EIf (esubst_ty σ c) (esubst_ty σ t) (esubst_ty σ e)
  | ETuple es => ETuple (map (esubst_ty σ) es)
  | EProj e i => EProj (esubst_ty σ e) i
  | EPrim op args => EPrim op (map (esubst_ty σ) args)
  | EConstr T c ts e => EConstr T c (map (tsubst σ) ts) (esubst_ty σ e)
  | EMatch e τ bs =>
      EMatch (esubst_ty σ e) (tsubst σ τ) (map (fun '(p, b) => (p, esubst_ty σ b)) bs)
  end.

(** ** Term variables *)

Definition upren (n : nat) (ξ : nat -> nat) (x : nat) : nat :=
  if x <? n then x else n + ξ (x - n).

Fixpoint rename (ξ : nat -> nat) (e : expr) : expr :=
  match e with
  | EVar x => EVar (ξ x)
  | EGlobal f ts => EGlobal f ts
  | ELit l => ELit l
  | ELam ps r b => ELam ps r (rename (upren (length ps) ξ) b)
  | EApp f args => EApp (rename ξ f) (map (rename ξ) args)
  | ELet e1 e2 => ELet (rename ξ e1) (rename (upren 1 ξ) e2)
  | EIf c t e => EIf (rename ξ c) (rename ξ t) (rename ξ e)
  | ETuple es => ETuple (map (rename ξ) es)
  | EProj e i => EProj (rename ξ e) i
  | EPrim op args => EPrim op (map (rename ξ) args)
  | EConstr T c ts e => EConstr T c ts (rename ξ e)
  | EMatch e τ bs =>
      EMatch (rename ξ e) τ (map (fun '(p, b) => (p, rename (upren (pat_arity p) ξ) b)) bs)
  end.

Definition upsub (n : nat) (σ : nat -> expr) (x : nat) : expr :=
  if x <? n then EVar x else rename (Nat.add n) (σ (x - n)).

Fixpoint subst (σ : nat -> expr) (e : expr) : expr :=
  match e with
  | EVar x => σ x
  | EGlobal f ts => EGlobal f ts
  | ELit l => ELit l
  | ELam ps r b => ELam ps r (subst (upsub (length ps) σ) b)
  | EApp f args => EApp (subst σ f) (map (subst σ) args)
  | ELet e1 e2 => ELet (subst σ e1) (subst (upsub 1 σ) e2)
  | EIf c t e => EIf (subst σ c) (subst σ t) (subst σ e)
  | ETuple es => ETuple (map (subst σ) es)
  | EProj e i => EProj (subst σ e) i
  | EPrim op args => EPrim op (map (subst σ) args)
  | EConstr T c ts e => EConstr T c ts (subst σ e)
  | EMatch e τ bs =>
      EMatch (subst σ e) τ (map (fun '(p, b) => (p, subst (upsub (pat_arity p) σ) b)) bs)
  end.

(** Substitution of the arguments [vs] for the [length vs] innermost
    variables, used for β-reduction and [let]. *)
Definition args_sub (vs : list expr) (x : nat) : expr :=
  nth x vs (EVar (x - length vs)).
