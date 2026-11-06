(** * Core IR: type checker, correct by construction

    [infer ge Γ e : result {τ | Γ ⊢[ge] e : τ} type_error]

    Every successful answer carries a typing derivation, so soundness of the
    checker holds by construction.  The derivations live in [Prop] and are
    erased by extraction: the extracted checker just returns the type.
    Completeness and decidability are proved in [CheckComplete.v].

    Recursion is structural on the expression; lists of sub-expressions are
    handled by [infer_list]/[check_list], which take the element checker as
    an argument and are unfolded by the guard checker (nested recursion). *)

From Stdlib Require Import List Arith PeanoNat.
From MoonRocq.Prelude Require Import Result EqDec Ident ListDec.
From MoonRocq.Core Require Import Syntax Prim Subst Typing.
Import ListNotations.

Inductive type_error : Type :=
| E_UnboundVar      (x : nat)
| E_UnknownGlobal   (f : ident)
| E_TypeArgArity    (f : ident) (expected got : nat)
| E_Mismatch        (expected got : ty)
| E_NotFunction     (t : ty)
| E_ArgArity        (expected got : nat)
| E_NotTuple        (t : ty)
| E_TupleIndex      (i : nat) (t : ty)
| E_DuplicateGlobal
| E_InGlobal        (f : ident) (e : type_error).

(** ** Certified building blocks *)

Definition of_option {A E} (o : option A) (err : E) : result {a | o = Some a} E :=
  match o as o' return result {a | o' = Some a} E with
  | Some a => Ok (exist _ a eq_refl)
  | None => Err err
  end.

Definition expect_ty (expected got : ty) : result (expected = got) type_error :=
  match ty_eq_dec expected got with
  | left H => Ok H
  | right _ => Err (E_Mismatch expected got)
  end.

Definition expect_nat (expected got : nat) (err : type_error) : result (got = expected) type_error :=
  match Nat.eq_dec got expected with
  | left H => Ok H
  | right _ => Err err
  end.

Definition as_arrow (t : ty) : result {ps : list ty & {r : ty | t = TArrow ps r}} type_error :=
  match t as t' return result {ps : list ty & {r : ty | t' = TArrow ps r}} type_error with
  | TArrow ps r => Ok (existT _ ps (exist _ r eq_refl))
  | t' => Err (E_NotFunction t')
  end.

Definition as_tuple (t : ty) : result {ts : list ty | t = TTuple ts} type_error :=
  match t as t' return result {ts : list ty | t' = TTuple ts} type_error with
  | TTuple ts => Ok (exist _ ts eq_refl)
  | t' => Err (E_NotTuple t')
  end.

Lemma cast_ty {ge Γ e τ τ'} : Γ ⊢[ge] e : τ -> τ = τ' -> Γ ⊢[ge] e : τ'.
Proof. intros H ->; exact H. Defined.

Section Check.
  Variable ge : genv.

  (** Synthesise the types of a list of expressions. *)
  Definition infer_list (Γ : ctx)
      (inf : forall e, result {τ | Γ ⊢[ge] e : τ} type_error) :
      forall es, result {τs | Γ ⊢*[ge] es : τs} type_error :=
    fix go es :=
      match es as es' return result {τs | Γ ⊢*[ge] es' : τs} type_error with
      | [] => Ok (exist _ [] (Ts_nil ge Γ))
      | e :: es' =>
          '(exist _ τ H) <- inf e ;;
          '(exist _ τs Hs) <- go es' ;;
          Ok (exist _ (τ :: τs) (Ts_cons ge Γ e es' τ τs H Hs))
      end.

  (** Check a list of expressions against a list of expected types.  Callers
      compare the lengths first, so that an arity error reports the totals. *)
  Definition check_list (Γ : ctx)
      (inf : forall e, result {τ | Γ ⊢[ge] e : τ} type_error) :
      forall es τs, result (Γ ⊢*[ge] es : τs) type_error :=
    fix go es τs :=
      match es as es', τs as τs' return result (Γ ⊢*[ge] es' : τs') type_error with
      | [], [] => Ok (Ts_nil ge Γ)
      | e :: es', τ :: τs' =>
          '(exist _ τe He) <- inf e ;;
          Heq <- expect_ty τ τe ;;
          Hs <- go es' τs' ;;
          Ok (Ts_cons ge Γ e es' τ τs' (cast_ty He (eq_sym Heq)) Hs)
      | es', τs' => Err (E_ArgArity (length τs') (length es'))
      end.

  Fixpoint infer (Γ : ctx) (e : expr) {struct e} : result {τ | Γ ⊢[ge] e : τ} type_error :=
    match e as e' return result {τ | Γ ⊢[ge] e' : τ} type_error with
    | EVar x =>
        '(exist _ τ H) <- of_option (nth_error Γ x) (E_UnboundVar x) ;;
        Ok (exist _ τ (T_Var ge Γ x τ H))
    | EGlobal f ts =>
        '(exist _ fd Hf) <- of_option (lookup_fn ge f) (E_UnknownGlobal f) ;;
        Hlen <- expect_nat (fd_tparams fd) (length ts)
                  (E_TypeArgArity f (fd_tparams fd) (length ts)) ;;
        Ok (exist _ _ (T_Global ge Γ f ts fd Hf Hlen))
    | ELit l =>
        Ok (exist _ _ (T_Lit ge Γ l))
    | ELam ps r b =>
        '(exist _ τb Hb) <- infer (ps ++ Γ) b ;;
        Heq <- expect_ty r τb ;;
        Ok (exist _ _ (T_Lam ge Γ ps r b (cast_ty Hb (eq_sym Heq))))
    | EApp f args =>
        '(exist _ τf Hf) <- infer Γ f ;;
        '(existT _ ps (exist _ r Ef)) <- as_arrow τf ;;
        _ <- expect_nat (length ps) (length args) (E_ArgArity (length ps) (length args)) ;;
        Hargs <- check_list Γ (infer Γ) args ps ;;
        Ok (exist _ r (T_App ge Γ f args ps r (cast_ty Hf Ef) Hargs))
    | ELet e1 e2 =>
        '(exist _ τ1 H1) <- infer Γ e1 ;;
        '(exist _ τ2 H2) <- infer (τ1 :: Γ) e2 ;;
        Ok (exist _ τ2 (T_Let ge Γ e1 e2 τ1 τ2 H1 H2))
    | EIf c t e0 =>
        '(exist _ τc Hc) <- infer Γ c ;;
        Hb <- expect_ty TBool τc ;;
        '(exist _ τt Ht) <- infer Γ t ;;
        '(exist _ τe He) <- infer Γ e0 ;;
        Heq <- expect_ty τt τe ;;
        Ok (exist _ τt (T_If ge Γ c t e0 τt (cast_ty Hc (eq_sym Hb)) Ht
                              (cast_ty He (eq_sym Heq))))
    | ETuple es =>
        '(exist _ τs Hs) <- infer_list Γ (infer Γ) es ;;
        Ok (exist _ _ (T_Tuple ge Γ es τs Hs))
    | EProj e0 i =>
        '(exist _ τ0 H0) <- infer Γ e0 ;;
        '(exist _ τs Et) <- as_tuple τ0 ;;
        '(exist _ τ Hi) <- of_option (nth_error τs i) (E_TupleIndex i τ0) ;;
        Ok (exist _ τ (T_Proj ge Γ e0 i τs τ (cast_ty H0 Et) Hi))
    | EPrim op args =>
        _ <- expect_nat (length (fst (prim_sig op))) (length args)
               (E_ArgArity (length (fst (prim_sig op))) (length args)) ;;
        Hargs <- check_list Γ (infer Γ) args (fst (prim_sig op)) ;;
        Ok (exist _ _ (T_Prim ge Γ op args Hargs))
    end.

  (** ** Global environment *)

  Definition check_fdef (fd : fdef) : result (fdef_ok ge fd) type_error :=
    map_err (E_InGlobal (fd_name fd))
      ('(exist _ τ H) <- infer (fd_params fd) (fd_body fd) ;;
       Heq <- expect_ty (fd_ret fd) τ ;;
       Ok (cast_ty H (eq_sym Heq))).

  Fixpoint check_fdefs (fds : list fdef) : result (Forall (fdef_ok ge) fds) type_error :=
    match fds as fds' return result (Forall (fdef_ok ge) fds') type_error with
    | [] => Ok (Forall_nil _)
    | fd :: fds' =>
        H <- check_fdef fd ;;
        Hs <- check_fdefs fds' ;;
        Ok (Forall_cons fd H Hs)
    end.
End Check.

Definition check_names (ge : genv) : result (NoDup (map fd_name ge)) type_error :=
  match NoDup_dec (map fd_name ge) with
  | left H => Ok H
  | right _ => Err E_DuplicateGlobal
  end.

Definition check_genv (ge : genv) : result (genv_ok ge) type_error :=
  Hn <- check_names ge ;;
  Hf <- check_fdefs ge ge ;;
  Ok (conj Hn Hf).
