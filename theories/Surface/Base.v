(** * Surface: shared definitions of elaboration

    The pieces used both by the declarative elaboration rules
    ([ElabSpec.v]) and by the elaborators: errors, the translation of
    surface types, literals and operators, labels and the control
    environment, local contexts, and what is known about traits
    (milestone M5). *)

From Stdlib Require Import List ZArith NArith String Bool Arith.
From MoonRocq.Prelude Require Import Result EqDec Ident ListDec.
From MoonRocq.Core Require Import Syntax Prim Subst Typing Check.
From MoonRocq.Surface Require Import Syntax Resolve.
Import ListNotations.

Local Open Scope string_scope.

Inductive elab_error : Type :=
| EE_Unbound       (p : pos) (x : ident)
| EE_UnknownType   (p : pos) (n : ident)
| EE_TypeArgs      (p : pos) (n : ident) (expected got : nat)  (** wrong number of type arguments *)
| EE_CannotInfer   (p : pos) (f : ident)       (** type arguments of a generic function / constructor *)
| EE_LambdaParam   (p : pos) (x : ident)       (** lambda parameter without known type *)
| EE_IntRange      (p : pos) (k : int_kind) (z : Z)
| EE_NoOperator    (p : pos) (op : ident) (t : ty)
| EE_Annot         (p : pos) (expected got : ty)
| EE_Type          (p : pos) (e : type_error)
| EE_UnknownCtor   (p : pos) (c : ident)
| EE_AmbiguousCtor (p : pos) (c : ident)
| EE_CtorArity     (p : pos) (c : ident) (expected got : nat)
| EE_NotRecord     (p : pos) (t : ty)
| EE_UnknownField  (p : pos) (f : ident)
| EE_MissingField  (p : pos) (f : ident)
| EE_PatType       (p : pos) (t : ty)          (** pattern shape does not fit the type *)
| EE_EmptyMatch    (p : pos)                   (** [match] without arms nor expected type *)
| EE_NotMutable    (p : pos) (x : ident)       (** assignment to an immutable variable / field *)
| EE_NoTarget      (p : pos)                   (** [break]/[continue]/[return] without a target *)
| EE_BadContinue   (p : pos) (expected got : nat)  (** wrong number of [continue] arguments *)
| EE_NoMethod      (p : pos) (m : ident) (t : ty)
| EE_NotError      (p : pos) (t : ty)
| EE_NoInstance    (p : pos) (Tr : ident) (t : ty)    (** no implementation of [Tr] for [t] *)
| EE_AmbiguousMethod (p : pos) (m : ident)
| EE_MissingMethod (p : pos) (Tr m : ident)
| EE_Overlap       (p : pos)                         (** two [impl]s of a trait for one type *)
| EE_NotObjectSafe (p : pos) (Tr : ident)
| EE_Unsupported   (p : pos) (what : ident).

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

Definition of_opt {A} (o : option A) (e : elab_error) : result A elab_error :=
  match o with Some a => Ok a | None => Err e end.

Definition tvars (n : nat) : list ty := map TVar (seq 0 n).

(** [Array] and [FixedArray]. *)
Definition array_kind_of (n : ident) : option array_kind :=
  if eqb n "Array" then Some AGrow
  else if eqb n "FixedArray" then Some AFixed
  else None.

(** ** Types *)

Definition builtin_types : list (ident * ty) :=
  [ ("Unit", TUnit); ("Bool", TBool);
    ("Int", TInt I32); ("Int16", TInt I16); ("Int64", TInt I64);
    ("UInt", TInt U32); ("UInt16", TInt U16); ("UInt64", TInt U64);
    ("Byte", TInt IByte); ("BigInt", TInt IBigInt);
    ("Char", TBase BChar); ("Double", TBase BDouble); ("Float", TBase BFloat);
    ("String", TString); ("Error", TError) ].

(** The builtin [struct Ref[T] { mut val : T }]. *)
Definition ref_tdef : tdef :=
  mk_tdef "Ref" 1 [mk_cdef "Ref" [TRef (TVar 0)]] false.

(** The builtin data type [Option[T] { None; Some(T) }]. *)
Definition option_tdef : tdef :=
  mk_tdef "Option" 1 [mk_cdef "None" []; mk_cdef "Some" [TVar 0]] false.

(** The builtin [enum Result[T, E] { Ok(T); Err(E) }]. *)
Definition result_tdef : tdef :=
  mk_tdef "Result" 2 [mk_cdef "Ok" [TVar 0]; mk_cdef "Err" [TVar 1]] false.

(** The builtin [suberror Failure { Failure(String) }], raised by [fail]. *)
Definition failure_tdef : tdef :=
  mk_tdef "Failure" 0 [mk_cdef "Failure" [TString]] true.

(** [tys]: the data types in scope with their number of parameters.
    Type parameters shadow everything else, then builtin types. *)
Fixpoint elab_ty (tys : list (ident * nat)) (tps : list ident) (t : sty) : result ty elab_error :=
  match t with
  | SName p n args =>
      match index_of n tps, assoc n builtin_types, assoc n tys with
      | Some i, _, _ =>
          match args with [] => Ok (TVar i) | _ => Err (EE_TypeArgs p n 0 (List.length args)) end
      | None, Some τ, _ =>
          match args with [] => Ok τ | _ => Err (EE_TypeArgs p n 0 (List.length args)) end
      | None, None, Some k =>
          if Nat.eqb k (List.length args) then
            τs <- mapM (elab_ty tys tps) args ;;
            Ok (TData n τs)
          else Err (EE_TypeArgs p n k (List.length args))
      | None, None, None =>
          match array_kind_of n, args with
          | Some k, [a] => τ <- elab_ty tys tps a ;; Ok (TArray k τ)
          | Some _, _ => Err (EE_TypeArgs p n 1 (List.length args))
          | None, _ => Err (EE_UnknownType p n)
          end
      end
  | STuple _ ts =>
      τs <- mapM (elab_ty tys tps) ts ;;
      Ok (TTuple τs)
  | SObj _ Tr => Ok (TData ("&" ++ Tr) [])
  | SArrow _ ps r eff =>
      τs <- mapM (elab_ty tys tps) ps ;;
      τ <- elab_ty tys tps r ;;
      ε <- match eff with
           | Some t => elab_ty tys tps t
           | None => Ok TNever
           end ;;
      Ok (TArrow τs τ ε)
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
  | TArrow ps r ε, TArrow ts u η => tmatch ε η (tmatch r u (go ps ts s))
  | TData T ps, TData U ts => if eqb T U then go ps ts s else s
  | TRef p, TRef t => tmatch p t s
  | TArray k p, TArray k' t => if eqb k k' then tmatch p t s else s
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
  | TArrow ps r ε =>
      match go ps, resolve s r, resolve s ε with
      | Some ts, Some t, Some η => Some (TArrow ts t η)
      | _, _, _ => None
      end
  | TData T ps => option_map (TData T) (go ps)
  | TRef p => option_map TRef (resolve s p)
  | TArray k p => option_map (TArray k) (resolve s p)
  | TError => Some TError
  end.

(** ** Literals and operators *)

Definition int_in_range (k : int_kind) (z : Z) : bool := Z.eqb (wrap k z) z.

Definition elab_lit (p : pos) (exp : option ty) (l : slit) : result lit elab_error :=
  let int k z :=
    if int_in_range k z then Ok (LInt k z) else Err (EE_IntRange p k z) in
  match l with
  | SLUnit => Ok LUnit
  | SLBool b => Ok (LBool b)
  | SLInt (Some k) z => int k z
  | SLInt None z =>
      match exp with
      | Some (TBase (BInt k)) => int k z
      | _ => int I32 z
      end
  | SLChar c => Ok (LChar c)
  | SLDouble b => Ok (LDouble b)
  | SLFloat b => Ok (LFloat b)
  | SLString s => Ok (LString s)
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

(** ** Labels

    One entry per Core [ELoop] between the current point and the enclosing
    function boundary, innermost first; its position is the de Bruijn index
    of [EJump]s that target it. *)
Inductive lab_kind : Type :=
| LKFun        (** a function body: the target of [return] *)
| LKBlock      (** a labelled block *)
| LKWhile      (** a [while] loop *)
| LKForBody    (** the body of a [for] loop; the loop itself is the next entry *)
| LKForInBody  (** the body of a [for .. in] loop; then the block computing the next
                   state, then the loop itself *)
| LKHead.      (** a loop seen from its condition, update or [nobreak]: transparent *)

Record lab : Type := mk_lab {
  lb_name : option ident;
  lb_kind : lab_kind;
  lb_ps   : list ty;
  lb_res  : ty
}.

Definition core_labels (L : list lab) : list (list ty * ty) :=
  map (fun l => (lb_ps l, lb_res l)) L.

Definition named (x : ident) (l : lab) : bool :=
  match lb_name l with Some y => eqb x y | None => false end.

(** The [for] loop of a [LKForBody] entry is the next entry. *)
Definition next_res (L : list lab) : ty :=
  match L with l :: _ => lb_res l | [] => TUnit end.
Definition next_ps (L : list lab) : list ty :=
  match L with l :: _ => lb_ps l | [] => [] end.
(** The state variables of a [for .. in] loop: the result of its state block. *)
Definition next_state (L : list lab) : list ty :=
  match L with l :: _ => match lb_res l with TTuple τs => τs | _ => [] end | [] => [] end.

(** [break] (labelled [Some x] or not): index and result type of the
    target.  An unlabelled [break] stops at a labelled block (it may not
    pass through one) and nothing crosses a function boundary. *)
Fixpoint break_target (x : option ident) (L : list lab) (k : nat) : option (nat * ty) :=
  match L with
  | [] => None
  | l :: L' =>
      match lb_kind l, x with
      | LKHead, _ => break_target x L' (S k)
      | LKFun, _ => None
      | LKBlock, None => None
      | LKWhile, None => Some (k, lb_res l)
      | LKForBody, None => Some (S k, next_res L')
      | LKForBody, Some y => if named y l then Some (S k, next_res L') else break_target x L' (S k)
      | LKForInBody, None => Some (S (S k), next_res (tl L'))
      | LKForInBody, Some y =>
          if named y l then Some (S (S k), next_res (tl L')) else break_target x L' (S k)
      | _, Some y => if named y l then Some (k, lb_res l) else break_target x L' (S k)
      end
  end.

Inductive cont_target : Type :=
| CTWhile (k : nat)                  (** re-enter the [while] loop [k] *)
| CTFor   (k : nat) (ps : list ty)   (** [for] body [k]; the loop is [S k], with variables [ps] *)
| CTForIn (k : nat) (ss : list ty).  (** [for .. in] body [k]; its state block is [S k] *)

Fixpoint cont_target_of (x : option ident) (L : list lab) (k : nat) : option cont_target :=
  match L with
  | [] => None
  | l :: L' =>
      match lb_kind l, x with
      | LKHead, _ => cont_target_of x L' (S k)
      | LKFun, _ => None
      | LKBlock, None => None
      | LKBlock, Some y => if named y l then None else cont_target_of x L' (S k)
      | LKWhile, None => Some (CTWhile k)
      | LKWhile, Some y => if named y l then Some (CTWhile k) else cont_target_of x L' (S k)
      | LKForBody, None => Some (CTFor k (next_ps L'))
      | LKForBody, Some y =>
          if named y l then Some (CTFor k (next_ps L')) else cont_target_of x L' (S k)
      | LKForInBody, None => Some (CTForIn k (next_state L'))
      | LKForInBody, Some y =>
          if named y l then Some (CTForIn k (next_state L')) else cont_target_of x L' (S k)
      end
  end.

Fixpoint return_target (L : list lab) (k : nat) : option (nat * ty) :=
  match L with
  | [] => None
  | l :: L' => match lb_kind l with LKFun => Some (k, lb_res l) | _ => return_target L' (S k) end
  end.

(** ** [for .. in]

    The sources supported so far: integer ranges and arrays.  A source is
    bound to two hidden variables before the loop: a range to its start and
    bound, an array to itself and its length (read once, as in MoonBit). *)
Inductive range_kind : Type :=
| RUpExcl      (** [a..<b]  *)
| RUpIncl      (** [a..<=b] *)
| RDownExcl    (** [a>..b]: from [a - 1] down to [b] *)
| RDownIncl.   (** [a>=..b] *)

Definition range_op (op : ident) : option range_kind :=
  if eqb op "..<" then Some RUpExcl
  else if eqb op "..<=" then Some RUpIncl
  else if eqb op ">.." then Some RDownExcl
  else if eqb op ">=.." then Some RDownIncl
  else None.

Inductive iter_src : Type :=
| IRange (rk : range_kind) (kk : int_kind)
| IArray (k : array_kind) (t : ty).

Definition int1 (kk : int_kind) : expr := ELit (LInt kk 1).
Definition iarith (o : arith_op) (kk : int_kind) (a b : expr) : expr := EPrim (PIntArith o kk) [a; b].
Definition icmp (c : cmp_op) (kk : int_kind) (a b : expr) : expr := EPrim (PIntCmp c kk) [a; b].

(** The control environment: the labels, and the error type that may
    escape at this point. *)
Record cenv : Type := mk_cenv {
  ce_labs : list lab;
  ce_exn  : ty
}.

Definition push_lab (l : lab) (L : cenv) : cenv := mk_cenv (l :: ce_labs L) (ce_exn L).
Definition set_exn (ε : ty) (L : cenv) : cenv := mk_cenv (ce_labs L) ε.

(** An error value of type [τ] where [Error] is expected is promoted. *)
Definition up_err (τ : ty) (e : expr) : expr :=
  match τ with
  | TData E [] => EUp E e
  | _ => e
  end.

Definition coerce (exp : option ty) (τ : ty) (e : expr) : expr :=
  match exp with
  | Some TError => up_err τ e
  | _ => e
  end.

(** [raise v] where [v : τ]. *)
Definition raise_val (L : cenv) (τ : ty) (v : expr) (τr : ty) : expr :=
  match ce_exn L with
  | TError => ERaise (up_err τ v) τr
  | _ => ERaise v τr
  end.

(** A call that raises [ε] where [Error] may escape: catch and promote. *)
Definition promote (L : cenv) (ε r : ty) (call : expr) : expr :=
  match ε, ce_exn L with
  | TData E [], TError => ETry call ε (ERaise (EUp E (EVar 0)) r) (EVar 0)
  | _, _ => call
  end.

(** What the patterns of a [catch] say about the error type of its body. *)
Inductive catch_info : Type := CINone | CIOne (T : ident) | CIMany.

(** The type given to a jump expression (it does not return). *)
Definition jty (exp : option ty) : ty := match exp with Some t => t | None => TUnit end.

(** A block-like Core loop without arguments. *)
Definition eblock (τ : ty) (b : expr) : expr := ELoop (ETuple []) [] τ b.

(** Expressions that certainly jump away, elaborated after their siblings
    so that the jump can take the siblings' type. *)
Fixpoint diverges (e : sexpr) : bool :=
  match e with
  | SBreak _ _ _ | SContinue _ _ _ | SReturn _ _ | SRaise _ _ => true
  | SApp _ (SVar _ g) _ => (eqb g "panic" || eqb g "abort" || eqb g "fail")%bool
  | SLet _ _ _ _ body | SLetMut _ _ _ _ body => diverges body
  | _ => false
  end.

(** ** Expressions *)

(** Local context: innermost binding first, [None] for [_]/sequencing.
    A [let mut] variable has a cell type [TRef τ] (surface types never
    are cells). *)
Definition lctx : Type := list (option ident * ty).

Fixpoint lookup_local (x : ident) (Γ : lctx) : option nat :=
  match Γ with
  | [] => None
  | (Some y, _) :: Γ' => if eqb x y then Some 0 else option_map S (lookup_local x Γ')
  | (None, _) :: Γ' => option_map S (lookup_local x Γ')
  end.

(** ** Traits (milestone M5)

    A trait is elaborated to a dictionary data type with one constructor
    (supertrait dictionaries first, then the methods), see [Resolve.v].
    Method signatures are over [Self = TVar 0]. *)

Record msig : Type := mk_msig {
  ms_name   : ident;
  ms_params : list ty;
  ms_ret    : ty;
  ms_eff    : ty
}.

Record trinfo : Type := mk_trinfo {
  ti_name     : ident;
  ti_supers   : list ident;
  ti_methods  : list msig;
  ti_defaults : list ident        (** methods with a default implementation *)
}.

(** What the elaborator knows about traits: the traits, the instances, the
    trait bounds of each global function, the methods [fn T::m] (type head,
    method), the object-safe traits, and the assumptions of the current
    definition (constraint, dictionary variable). *)
Record xenv : Type := mk_xenv {
  x_traits : list trinfo;
  x_insts  : list idef;
  x_bounds : list (ident * list (ident * nat));
  x_meths  : list (ident * ident);
  x_objs   : list ident;
  x_asm    : list (ident * ty * ident)
}.

Definition find_trait (trs : list trinfo) (Tr : ident) : option trinfo :=
  find (fun ti => eqb (ti_name ti) Tr) trs.

Definition nfields (ti : trinfo) : nat :=
  List.length (ti_supers ti) + List.length (ti_methods ti).

Definition dict_fields (ti : trinfo) : list ty :=
  List.app (map (fun Sn => TData Sn [TVar 0]) (ti_supers ti))
           (map (fun m => TArrow (ms_params m) (ms_ret m) (ms_eff m)) (ti_methods ti)).

Definition dict_tdef (ti : trinfo) : tdef :=
  mk_tdef (ti_name ti) 1 [mk_cdef (ti_name ti) (dict_fields ti)] false.

(** The field index of method [m] in the dictionary, and its signature. *)
Definition method_of (ti : trinfo) (m : ident) : option (nat * msig) :=
  let fix go (ms : list msig) (i : nat) :=
    match ms with
    | [] => None
    | s :: ms' => if eqb (ms_name s) m then Some (i, s) else go ms' (S i)
    end in
  go (ti_methods ti) (List.length (ti_supers ti)).

(** Field [i] of a dictionary (or object) [d] of data type [T], at type [τ]. *)
Definition field_of (T : ident) (n i : nat) (d : expr) (τ : ty) : expr :=
  EMatch d τ [(PConstr T (map (fun j => if Nat.eqb j i then PVar else PWild) (seq 0 n)), EVar 0)].

(** A trait and its supertraits, transitively, without repetition. *)
Fixpoint trait_closure (trs : list trinfo) (fuel : nat) (Tr : ident) : list ident :=
  match fuel with
  | 0 => [Tr]
  | S f =>
      Tr :: match find_trait trs Tr with
            | Some ti => List.concat (map (trait_closure trs f) (ti_supers ti))
            | None => []
            end
  end.

Definition closure (trs : list trinfo) (Tr : ident) : list ident :=
  nodup eq_dec (trait_closure trs (List.length trs) Tr).

(** ** Trait objects

    An object-safe trait [Tr] (every method of it and of its supertraits
    takes [Self] first and nowhere else) has an object type [&Tr]: a record
    of closures, one per method, with [self] already applied. *)

Fixpoint occurs0 (t : ty) : bool :=
  match t with
  | TVar i => Nat.eqb i 0
  | TBase _ | TError => false
  | TTuple ts | TData _ ts => existsb occurs0 ts
  | TArrow ps r ε => (existsb occurs0 ps || occurs0 r || occurs0 ε)%bool
  | TRef t | TArray _ t => occurs0 t
  end.

Definition obj_safe_m (m : msig) : bool :=
  match ms_params m with
  | TVar 0 :: ps => negb (existsb occurs0 ps || occurs0 (ms_ret m) || occurs0 (ms_eff m))
  | _ => false
  end.

Definition obj_safe (trs : list trinfo) (Tr : ident) : bool :=
  forallb (fun Sn => match find_trait trs Sn with
                    | Some ti => forallb obj_safe_m (ti_methods ti)
                    | None => false
                    end) (closure trs Tr).

Definition obj_name (Tr : ident) : ident := "&" ++ Tr.

(** The methods of an object: those of the trait and of its supertraits. *)
Definition obj_fields (trs : list trinfo) (Tr : ident) : list (ident * msig) :=
  List.concat (map (fun Sn => match find_trait trs Sn with
                             | Some ti => map (fun m => (Sn, m)) (ti_methods ti)
                             | None => []
                             end) (closure trs Tr)).

Definition obj_field_ty (m : msig) : ty := TArrow (tl (ms_params m)) (ms_ret m) (ms_eff m).

Definition obj_tdef (trs : list trinfo) (Tr : ident) : tdef :=
  mk_tdef (obj_name Tr) 0
    [mk_cdef (obj_name Tr) (map (fun sm => obj_field_ty (snd sm)) (obj_fields trs Tr))] false.

(** The type name of a type, for methods [fn T::m]. *)
Definition head_name (t : ty) : option ident :=
  match t with
  | TData T _ => Some T
  | TArray AGrow _ => Some "Array"
  | TArray AFixed _ => Some "FixedArray"
  | TBase b => option_map fst (find (fun nt => eqb (snd nt) (TBase b)) builtin_types)
  | TError => Some "Error"
  | _ => None
  end.

Definition dict_var (Tr X : ident) : ident := "$" ++ Tr ++ "$" ++ X.

(** The supertrait dictionaries of the bounds [(Tr, X, i)] (trait, type
    parameter, its index), as [let]s: [(S, X, i, from T, field j)]. *)
Fixpoint super_lets (trs : list trinfo) (fuel : nat) (have : list (ident * ident))
    (queue : list (ident * ident * nat)) : list (ident * ident * nat * ident * nat) :=
  match fuel, queue with
  | 0, _ | _, [] => []
  | S f, (T, X, i) :: q =>
      let sups := match find_trait trs T with Some ti => ti_supers ti | None => [] end in
      let fix add (ss : list ident) (j : nat) (have : list (ident * ident)) :=
        match ss with
        | [] => ([], have)
        | s :: ss' =>
            if existsb (fun p => (eqb (fst p) s && eqb (snd p) X)%bool) have
            then add ss' (S j) have
            else let '(r, h) := add ss' (S j) ((s, X) :: have) in ((s, X, i, T, j) :: r, h)
        end in
      let '(new, have') := add sups 0 have in
      List.app new (super_lets trs f have' (List.app q (map (fun l => let '(s, X', i', _, _) := l in (s, X', i')) new)))
  end.
