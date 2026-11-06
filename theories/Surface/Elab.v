(** * Elaboration: Surface → Core (preliminary)

    Turns a named [sprog] into a Core global environment and entry
    expression.  It does
    - name resolution: locals become de Bruijn indices, other names become
      globals, builtin type names become Core base types, type parameters
      become [TVar];
    - operator resolution: [+], [==], ... are picked from the type of the
      left operand ([&&], [||] become [if]);
    - local type inference, bidirectional style: an expected type flows into
      literals, lambdas, tuples and branches; the type arguments of a generic
      call are found by first-order *matching* of the parameter types
      against the (already known) argument types.

    Types of already elaborated sub-terms are obtained from the certified
    Core checker [infer], run against a *header* environment that has the
    signatures of all top-level functions (bodies are irrelevant to [infer]).
    So there is a single definition of typing: the elaborator never decides
    a type on its own.

    Elaboration is *not* trusted: its output is checked again by
    [check_program].  What is not yet stated (future milestone) is the
    specification of elaboration itself, i.e. surface typing rules and a
    proof that elaboration is faithful to them.  Full MoonBit inference
    (unification variables, decision 11 in [docs/decisions.md]) is also
    future work: a lambda parameter needs either an annotation or an
    expected type. *)

From Stdlib Require Import List ZArith NArith String Bool Arith.
From MoonRocq.Prelude Require Import Result EqDec Ident.
From MoonRocq.Core Require Import Syntax Prim Subst Typing Check.
From MoonRocq.Surface Require Import Syntax.
Import ListNotations.

Local Open Scope string_scope.

Inductive elab_error : Type :=
| EE_Unbound       (p : pos) (x : ident)
| EE_UnknownType   (p : pos) (n : ident)
| EE_TypeArgs      (p : pos) (n : ident)       (** a type that takes no arguments was applied *)
| EE_CannotInfer   (p : pos) (f : ident)       (** type arguments of a generic function *)
| EE_LambdaParam   (p : pos) (x : ident)       (** lambda parameter without known type *)
| EE_IntRange      (p : pos) (k : int_kind) (z : Z)
| EE_NoOperator    (p : pos) (op : ident) (t : ty)
| EE_Annot         (p : pos) (expected got : ty)
| EE_Type          (p : pos) (e : type_error).

(** ** Small utilities *)

Fixpoint assoc {A} (x : ident) (l : list (ident * A)) : option A :=
  match l with
  | [] => None
  | (y, a) :: l' => if eqb x y then Some a else assoc x l'
  end.

Fixpoint index_of (x : ident) (l : list ident) : option nat :=
  match l with
  | [] => None
  | y :: l' => if eqb x y then Some 0 else option_map S (index_of x l')
  end.

Fixpoint set_nth {A} (i : nat) (x : A) (l : list A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: l', 0 => x :: l'
  | y :: l', S i' => y :: set_nth i' x l'
  end.

Fixpoint all_some {A} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | Some a :: l' => option_map (cons a) (all_some l')
  | None :: _ => None
  end.

(** ** Types *)

Definition builtin_types : list (ident * ty) :=
  [ ("Unit", TUnit); ("Bool", TBool);
    ("Int", TInt I32); ("Int16", TInt I16); ("Int64", TInt I64);
    ("UInt", TInt U32); ("UInt16", TInt U16); ("UInt64", TInt U64);
    ("Byte", TInt IByte); ("BigInt", TInt IBigInt);
    ("Char", TBase BChar); ("Double", TBase BDouble); ("Float", TBase BFloat);
    ("String", TString) ].

(** Type parameters shadow builtin type names. *)
Fixpoint elab_ty (tps : list ident) (t : sty) : result ty elab_error :=
  match t with
  | SName p n [] =>
      match index_of n tps with
      | Some i => Ok (TVar i)
      | None =>
          match assoc n builtin_types with
          | Some τ => Ok τ
          | None => Err (EE_UnknownType p n)
          end
      end
  | SName p n (_ :: _) => Err (EE_TypeArgs p n)
  | STuple _ ts =>
      τs <- mapM (elab_ty tps) ts ;;
      Ok (TTuple τs)
  | SArrow _ ps r =>
      τs <- mapM (elab_ty tps) ps ;;
      τ <- elab_ty tps r ;;
      Ok (TArrow τs τ)
  end.

(** ** Matching, for the type arguments of generic calls

    [tmatch p t s] extends the partial instantiation [s] (one slot per type
    parameter of the callee) so that [p] instantiated by [s] becomes [t].
    Mismatches are ignored here: the Core checker reports them later with a
    precise error.  The type variables of [t] (those of the caller) are
    never bound. *)
Fixpoint tmatch (p t : ty) (s : list (option ty)) {struct p} : list (option ty) :=
  let fix go (ps ts : list ty) (s : list (option ty)) : list (option ty) :=
    match ps, ts with
    | p :: ps', t :: ts' => go ps' ts' (tmatch p t s)
    | _, _ => s
    end in
  match p, t with
  | TVar i, _ =>
      match nth_error s i with
      | Some None => set_nth i (Some t) s
      | _ => s
      end
  | TTuple ps, TTuple ts => go ps ts s
  | TArrow ps r, TArrow ts u => tmatch r u (go ps ts s)
  | _, _ => s
  end.

(** [p] under [s], if all its type variables are determined. *)
Fixpoint resolve (s : list (option ty)) (p : ty) {struct p} : option ty :=
  let fix go (ps : list ty) : option (list ty) :=
    match ps with
    | [] => Some []
    | p :: ps' =>
        match resolve s p, go ps' with
        | Some t, Some ts => Some (t :: ts)
        | _, _ => None
        end
    end in
  match p with
  | TBase b => Some (TBase b)
  | TVar i => match nth_error s i with Some (Some t) => Some t | _ => None end
  | TTuple ps => option_map TTuple (go ps)
  | TArrow ps r =>
      match go ps, resolve s r with
      | Some ts, Some t => Some (TArrow ts t)
      | _, _ => None
      end
  end.

(** ** Literals and operators *)

Definition int_in_range (k : int_kind) (z : Z) : bool := Z.eqb (wrap k z) z.

Definition elab_lit (p : pos) (exp : option ty) (l : slit) : result expr elab_error :=
  let int k z :=
    if int_in_range k z then Ok (ELit (LInt k z)) else Err (EE_IntRange p k z) in
  match l with
  | SLUnit => Ok (ELit LUnit)
  | SLBool b => Ok (ELit (LBool b))
  | SLInt (Some k) z => int k z
  | SLInt None z =>
      match exp with
      | Some (TBase (BInt k)) => int k z
      | _ => int I32 z
      end
  | SLChar c => Ok (ELit (LChar c))
  | SLDouble b => Ok (ELit (LDouble b))
  | SLFloat b => Ok (ELit (LFloat b))
  | SLString s => Ok (ELit (LString s))
  end.

Definition arith_ops : list (ident * arith_op) :=
  [("+", AAdd); ("-", ASub); ("*", AMul); ("/", ADiv); ("%", AMod)].

Definition cmp_ops : list (ident * cmp_op) :=
  [("==", CEq); ("!=", CNe); ("<", CLt); ("<=", CLe); (">", CGt); (">=", CGe)].

Definition e_true  := ELit (LBool true).
Definition e_false := ELit (LBool false).

(** Resolve a binary operator from the type [ta] of its left operand. *)
Definition elab_binop (p : pos) (op : ident) (ta : ty) (a b : expr) : result expr elab_error :=
  match assoc op arith_ops, assoc op cmp_ops, ta with
  | Some o, _, TBase (BInt k) => Ok (EPrim (PIntArith o k) [a; b])
  | Some AAdd, _, TBase BString => Ok (EPrim PStrConcat [a; b])
  | _, Some c, TBase (BInt k) => Ok (EPrim (PIntCmp c k) [a; b])
  | _, Some c, TBase BChar => Ok (EPrim (PCharCmp c) [a; b])
  | _, Some CEq, TBase BBool => Ok (EPrim PBoolEq [a; b])
  | _, Some CNe, TBase BBool => Ok (EPrim PBoolNot [EPrim PBoolEq [a; b]])
  | _, Some CEq, TBase BString => Ok (EPrim PStrEq [a; b])
  | _, Some CNe, TBase BString => Ok (EPrim PBoolNot [EPrim PStrEq [a; b]])
  | _, _, _ => Err (EE_NoOperator p op ta)
  end.

(** An unsuffixed integer literal: its type is decided by the context. *)
Definition flexible (e : sexpr) : bool :=
  match e with
  | SLit _ (SLInt None _) => true
  | _ => false
  end.

(** ** Expressions *)

(** Local context: innermost binding first, [None] for [_]/sequencing. *)
Definition lctx : Type := list (option ident * ty).

Fixpoint lookup_local (x : ident) (Γ : lctx) : option nat :=
  match Γ with
  | [] => None
  | (Some y, _) :: Γ' => if eqb x y then Some 0 else option_map S (lookup_local x Γ')
  | (None, _) :: Γ' => option_map S (lookup_local x Γ')
  end.

Section Elab.
  Variable hdr : genv.          (** signatures of all top-level functions *)
  Variable tps : list ident.    (** type parameters in scope *)

  Definition type_of (p : pos) (Γ : lctx) (e : expr) : result ty elab_error :=
    match infer hdr (map snd Γ) e with
    | Ok (exist _ τ _) => Ok τ
    | Err err => Err (EE_Type p err)
    end.

  Definition arrow_params (t : ty) (n : nat) : list (option ty) :=
    match t with
    | TArrow ps _ => if Nat.eqb (List.length ps) n then map Some ps else repeat None n
    | _ => repeat None n
    end.

  (** A global function used as a value (not called): its type arguments
      come from the expected type. *)
  Definition elab_global (p : pos) (f : ident) (fd : fdef) (exp : option ty) :
      result expr elab_error :=
    match fd_tparams fd with
    | 0 => Ok (EGlobal f [])
    | n =>
        let s := match exp with
                 | Some t => tmatch (TArrow (fd_params fd) (fd_ret fd)) t (repeat None n)
                 | None => repeat None n
                 end in
        match all_some s with
        | Some ts => Ok (EGlobal f ts)
        | None => Err (EE_CannotInfer p f)
        end
    end.

  (** Types of lambda parameters: annotation, else expectation. *)
  Fixpoint param_tys (p : pos) (ps : list (ident * option sty)) (exps : list (option ty)) :
      result (list ty) elab_error :=
    match ps with
    | [] => Ok []
    | (x, ann) :: ps' =>
        let (ex, exps') := match exps with
                           | [] => (None, [])
                           | y :: ys => (y, ys)
                           end in
        τ <- match ann, ex with
             | Some t, _ => elab_ty tps t
             | None, Some τ => Ok τ
             | None, None => Err (EE_LambdaParam p x)
             end ;;
        τs <- param_tys p ps' exps' ;;
        Ok (τ :: τs)
    end.

  (** A lambda, from (possibly partial) expectations [pexps] for its
      parameter types and [rexp] for its result type; [elab_body] elaborates
      the body in the extended context. *)
  Definition elab_lam (Γ : lctx) (p : pos) (ps : list (ident * option sty)) (ret : option sty)
      (pexps : list (option ty)) (rexp : option ty)
      (elab_body : lctx -> option ty -> result expr elab_error) : result expr elab_error :=
    τs <- param_tys p ps pexps ;;
    let Γ' := List.app (combine (map (fun x => Some (fst x)) ps) τs) Γ in
    τr <- match ret with
          | Some t => map_result Some (elab_ty tps t)
          | None => Ok rexp
          end ;;
    body' <- elab_body Γ' τr ;;
    r <- match τr with
         | Some r => Ok r
         | None => type_of p Γ' body'
         end ;;
    Ok (ELam τs r body').

  (** A lambda whose parameter types must come from the context. *)
  Definition needs_context (e : sexpr) : bool :=
    match e with
    | SLam _ ps _ _ => existsb (fun xa => match snd xa with None => true | Some _ => false end) ps
    | _ => false
    end.

  Fixpoint elab (Γ : lctx) (exp : option ty) (e : sexpr) {struct e} : result expr elab_error :=
    (* elaborate a list against a list of expected types *)
    let fix elab_args (es : list sexpr) (exps : list (option ty)) : result (list expr) elab_error :=
      match es with
      | [] => Ok []
      | e :: es' =>
          let (x, exps') := match exps with
                            | [] => (None, [])
                            | x :: xs => (x, xs)
                            end in
          e' <- elab Γ x e ;;
          es2 <- elab_args es' exps' ;;
          Ok (e' :: es2)
      end in
    (* Arguments of a generic call, threading the partial instantiation [s].
       Pass 1 elaborates left to right, but postpones lambdas that have
       unannotated parameters and no known expected type; pass 2 elaborates
       those with what the other arguments taught us (possibly only their
       parameter types).  [gargs1] returns [None] for postponed arguments. *)
    let fix gargs1 (p : pos) (es : list sexpr) (ps : list ty) (s : list (option ty)) :
        result (list (option expr) * list (option ty)) elab_error :=
      match es with
      | [] => Ok ([], s)
      | e :: es' =>
          let (pt, ps') := match ps with
                           | [] => (None, [])
                           | t :: ts => (Some t, ts)
                           end in
          let ex := match pt with Some t => resolve s t | None => None end in
          if andb (needs_context e) (match ex with None => true | Some _ => false end) then
            '(r, s2) <- gargs1 p es' ps' s ;;
            Ok (None :: r, s2)
          else
            e' <- elab Γ ex e ;;
            s' <- match pt with
                  | Some t => τ <- type_of p Γ e' ;; Ok (tmatch t τ s)
                  | None => Ok s
                  end ;;
            '(r, s2) <- gargs1 p es' ps' s' ;;
            Ok (Some e' :: r, s2)
      end in
    let fix gargs2 (p : pos) (es : list sexpr) (pre : list (option expr)) (ps : list ty)
        (s : list (option ty)) : result (list expr * list (option ty)) elab_error :=
      match es with
      | [] => Ok ([], s)
      | e :: es' =>
          let (d, pre') := match pre with
                           | [] => (None, [])
                           | d :: ds => (d, ds)
                           end in
          let (pt, ps') := match ps with
                           | [] => (None, [])
                           | t :: ts => (Some t, ts)
                           end in
          e' <- match d with
                | Some e' => Ok e'
                | None =>
                    match e, pt with
                    | SLam q lps ret body, Some (TArrow pps pr) =>
                        let pexps := if Nat.eqb (List.length pps) (List.length lps)
                                     then map (resolve s) pps
                                     else repeat None (List.length lps) in
                        elab_lam Γ q lps ret pexps (resolve s pr) (fun Γ' t => elab Γ' t body)
                    | _, _ => elab Γ (match pt with Some t => resolve s t | None => None end) e
                    end
                end ;;
          s' <- match d, pt with
                | None, Some t => τ <- type_of p Γ e' ;; Ok (tmatch t τ s)
                | _, _ => Ok s
                end ;;
          '(r, s2) <- gargs2 p es' pre' ps' s' ;;
          Ok (e' :: r, s2)
      end in
    match e with
    | SVar p x =>
        match lookup_local x Γ with
        | Some i => Ok (EVar i)
        | None =>
            match lookup_fn hdr x with
            | Some fd => elab_global p x fd exp
            | None => Err (EE_Unbound p x)
            end
        end
    | SLit p l => elab_lit p exp l
    | SApp p f args =>
        match f with
        | SVar q g =>
            match lookup_local g Γ, lookup_fn hdr g with
            | None, Some fd =>
                match fd_tparams fd with
                | 0 =>
                    args' <- elab_args args (map Some (fd_params fd)) ;;
                    Ok (EApp (EGlobal g []) args')
                | n =>
                    let s0 := match exp with
                              | Some t => tmatch (fd_ret fd) t (repeat None n)
                              | None => repeat None n
                              end in
                    '(pre, s1) <- gargs1 p args (fd_params fd) s0 ;;
                    '(args', s) <- gargs2 p args pre (fd_params fd) s1 ;;
                    match all_some s with
                    | Some ts => Ok (EApp (EGlobal g ts) args')
                    | None => Err (EE_CannotInfer q g)
                    end
                end
            | None, None =>
                (* builtins that are not ordinary functions in Core *)
                if eqb g "not" then
                  args' <- elab_args args [Some TBool] ;;
                  Ok (EPrim PBoolNot args')
                else if eqb g "ignore" then
                  match args with
                  | [a] => a' <- elab Γ None a ;; Ok (ELet a' (ELit LUnit))
                  | _ => Err (EE_Unbound q g)
                  end
                else Err (EE_Unbound q g)
            | Some _, _ =>
                f' <- elab Γ None f ;;
                τf <- type_of p Γ f' ;;
                args' <- elab_args args (arrow_params τf (List.length args)) ;;
                Ok (EApp f' args')
            end
        | _ =>
            f' <- elab Γ None f ;;
            τf <- type_of p Γ f' ;;
            args' <- elab_args args (arrow_params τf (List.length args)) ;;
            Ok (EApp f' args')
        end
    | SInfix p op a b =>
        if eqb op "&&" then
          a' <- elab Γ (Some TBool) a ;;
          b' <- elab Γ (Some TBool) b ;;
          Ok (EIf a' b' e_false)
        else if eqb op "||" then
          a' <- elab Γ (Some TBool) a ;;
          b' <- elab Γ (Some TBool) b ;;
          Ok (EIf a' e_true b')
        else
          (* the expected type only flows into arithmetic operands *)
          let exp' := match assoc op arith_ops with Some _ => exp | None => None end in
          if andb (flexible a) (negb (flexible b)) then
            b' <- elab Γ exp' b ;;
            τ <- type_of p Γ b' ;;
            a' <- elab Γ (Some τ) a ;;
            elab_binop p op τ a' b'
          else
            a' <- elab Γ exp' a ;;
            τ <- type_of p Γ a' ;;
            b' <- elab Γ (Some τ) b ;;
            elab_binop p op τ a' b'
    | SUnary p op a =>
        if eqb op "-" then
          match a with
          | SLit q (SLInt k z) => elab_lit q exp (SLInt k (Z.opp z))
          | _ =>
              a' <- elab Γ exp a ;;
              τ <- type_of p Γ a' ;;
              match τ with
              | TBase (BInt k) => Ok (EPrim (PIntNeg k) [a'])
              | _ => Err (EE_NoOperator p op τ)
              end
          end
        else if eqb op "!" then
          a' <- elab Γ (Some TBool) a ;;
          Ok (EPrim PBoolNot [a'])
        else Err (EE_NoOperator p op TUnit)
    | SLet p x ann e1 body =>
        τann <- match ann with
                | Some t => map_result Some (elab_ty tps t)
                | None => Ok None
                end ;;
        e1' <- elab Γ τann e1 ;;
        τ1 <- type_of p Γ e1' ;;
        _ <- match τann with
             | Some t => if eqb t τ1 then Ok tt else Err (EE_Annot p t τ1)
             | None => Ok tt
             end ;;
        body' <- elab ((x, τ1) :: Γ) exp body ;;
        Ok (ELet e1' body')
    | SIf p c t oe =>
        c' <- elab Γ (Some TBool) c ;;
        match oe with
        | Some e0 =>
            t' <- elab Γ exp t ;;
            exp' <- match exp with
                    | Some τ => Ok (Some τ)
                    | None => map_result Some (type_of p Γ t')
                    end ;;
            e0' <- elab Γ exp' e0 ;;
            Ok (EIf c' t' e0')
        | None =>
            t' <- elab Γ (Some TUnit) t ;;
            Ok (EIf c' t' (ELit LUnit))
        end
    | STup p es =>
        let exps := match exp with
                    | Some (TTuple ts) =>
                        if Nat.eqb (List.length ts) (List.length es) then map Some ts
                        else repeat None (List.length es)
                    | _ => repeat None (List.length es)
                    end in
        es' <- elab_args es exps ;;
        Ok (ETuple es')
    | SProj p e0 i =>
        e0' <- elab Γ None e0 ;;
        Ok (EProj e0' i)
    | SLam p ps ret body =>
        let pexps := match exp with
                     | Some t => arrow_params t (List.length ps)
                     | None => repeat None (List.length ps)
                     end in
        let rexp := match exp with Some (TArrow _ r) => Some r | _ => None end in
        elab_lam Γ p ps ret pexps rexp (fun Γ' t => elab Γ' t body)
    | SAnnot p e0 t =>
        τ <- elab_ty tps t ;;
        e0' <- elab Γ (Some τ) e0 ;;
        τ0 <- type_of p Γ e0' ;;
        if eqb τ τ0 then Ok e0' else Err (EE_Annot p τ τ0)
    end.
End Elab.

(** ** Programs *)

Definition elab_sig (f : sfun) : result fdef elab_error :=
  τs <- mapM (fun xt => elab_ty (sf_tparams f) (snd xt)) (sf_params f) ;;
  τ <- match sf_ret f with
       | Some t => elab_ty (sf_tparams f) t
       | None => Ok TUnit
       end ;;
  Ok (mk_fdef (sf_name f) (List.length (sf_tparams f)) τs τ (ELit LUnit)).

Definition elab_fun (hdr : genv) (f : sfun) (sig : fdef) : result fdef elab_error :=
  let Γ := combine (map (fun xt => Some (fst xt)) (sf_params f)) (fd_params sig) in
  b <- elab hdr (sf_tparams f) Γ (Some (fd_ret sig)) (sf_body f) ;;
  Ok (mk_fdef (fd_name sig) (fd_tparams sig) (fd_params sig) (fd_ret sig) b).

Fixpoint elab_funs (hdr : genv) (fs : list sfun) (sigs : list fdef) : result genv elab_error :=
  match fs, sigs with
  | f :: fs', sig :: sigs' =>
      fd <- elab_fun hdr f sig ;;
      ge <- elab_funs hdr fs' sigs' ;;
      Ok (fd :: ge)
  | _, _ => Ok []
  end.

(** The entry expression is the body of [fn main] (checked against [Unit]),
    or [()] when there is none. *)
Definition elab_prog (sp : sprog) : result (genv * expr) elab_error :=
  hdr <- mapM elab_sig (sp_funs sp) ;;
  ge <- elab_funs hdr (sp_funs sp) hdr ;;
  main <- match sp_main sp with
          | Some e => elab hdr [] [] (Some TUnit) (SAnnot (sexpr_pos e) e (SName (sexpr_pos e) "Unit" []))
          | None => Ok (ELit LUnit)
          end ;;
  Ok (ge, main).
