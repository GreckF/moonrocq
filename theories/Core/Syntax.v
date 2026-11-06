(** * Core IR: syntax

    The Core language is the explicitly typed kernel that every MoonBit
    surface program is elaborated into.  Design points (see DESIGN.md §4):

    - Church style: every binder carries its type, so types are unique and
      type checking needs no inference.
    - Term variables are de Bruijn indices.  A multi-parameter binder
      [ELam ps r b] binds [length ps] variables at once, the *first*
      parameter being index [0] (context [ps ++ Γ]).
    - Type variables are de Bruijn indices into the type parameters of the
      enclosing top-level function.  Polymorphism is rank-1: types contain
      no binders, so type substitution never needs shifting.
    - MoonBit functions are n-ary, not curried: [TArrow ps r ε], [EApp f args].
      The effect [ε] of a function type is the error type it may raise:
      [TNever] for [noraise], an error type for [raise E], a type variable
      for [raise?] (error polymorphism is ordinary type polymorphism).

    Milestone M1 covers primitive types, functions, [let], [if], tuples,
    (mutually) recursive generic top-level functions and primitive
    operators; M2 adds nominal data types and pattern matching; M3 adds the
    store (references and arrays) and loops with [break]/[continue]; M4 adds
    errors ([raise], [try]/[catch], [defer]/[errdefer]) and effects.
    Later milestones extend these inductive types. *)

From Stdlib Require Import List ZArith String.
From MoonRocq.Prelude Require Import EqDec Ident.
Import ListNotations.

(** ** Primitive types *)

(** Integer kinds.  [IByte] is MoonBit's [Byte] (unsigned 8-bit);
    [IBigInt] is unbounded. *)
Inductive int_kind : Type :=
| I16 | I32 | I64 | U16 | U32 | U64 | IByte | IBigInt.

Inductive base_ty : Type :=
| BUnit
| BBool
| BInt (k : int_kind)
| BChar
| BDouble
| BFloat
| BString
| BNever.     (** no values: the effect of [noraise] functions *)

Definition int_kind_eq_dec (x y : int_kind) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition base_ty_eq_dec (x y : base_ty) : {x = y} + {x <> y}.
Proof. decide equality. apply int_kind_eq_dec. Defined.

#[export] Instance EqDec_int_kind : EqDec int_kind := EqDec_of_dec int_kind_eq_dec.

(** MoonBit's [FixedArray[T]] and the growable [Array[T]]. *)
Inductive array_kind : Type := AFixed | AGrow.

Definition array_kind_eq_dec (x y : array_kind) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

#[export] Instance EqDec_array_kind : EqDec array_kind := EqDec_of_dec array_kind_eq_dec.
#[export] Instance EqDec_base_ty : EqDec base_ty := EqDec_of_dec base_ty_eq_dec.

(** ** Types *)

Inductive ty : Type :=
| TBase  (b : base_ty)
| TVar   (i : nat)
| TTuple (ts : list ty)
| TArrow (ps : list ty) (r : ty) (ε : ty)  (** [(ps) -> r raise ε] *)
| TData  (T : ident) (ts : list ty)        (** nominal type [T[ts]] (struct / enum) *)
| TRef   (t : ty)                          (** mutable cell (store location) *)
| TArray (k : array_kind) (t : ty)         (** array (store location) *)
| TError.                                  (** [Error]: a value of any error type *)

Abbreviation TUnit   := (TBase BUnit).
Abbreviation TBool   := (TBase BBool).
Abbreviation TInt k  := (TBase (BInt k)).
Abbreviation TString := (TBase BString).
Abbreviation TNever  := (TBase BNever).

(** Induction principle that sees through the nested lists. *)
Section ty_ind'.
  Variable P : ty -> Prop.
  Hypothesis HBase  : forall b, P (TBase b).
  Hypothesis HVar   : forall i, P (TVar i).
  Hypothesis HTuple : forall ts, Forall P ts -> P (TTuple ts).
  Hypothesis HArrow : forall ps r ε, Forall P ps -> P r -> P ε -> P (TArrow ps r ε).
  Hypothesis HData  : forall T ts, Forall P ts -> P (TData T ts).
  Hypothesis HRef   : forall t, P t -> P (TRef t).
  Hypothesis HArray : forall k t, P t -> P (TArray k t).
  Hypothesis HError : P TError.

  Fixpoint ty_ind' (t : ty) : P t :=
    let fix go (ts : list ty) : Forall P ts :=
      match ts with
      | [] => Forall_nil P
      | t :: ts' => Forall_cons t (ty_ind' t) (go ts')
      end in
    match t with
    | TBase b => HBase b
    | TVar i => HVar i
    | TTuple ts => HTuple ts (go ts)
    | TArrow ps r ε => HArrow ps r ε (go ps) (ty_ind' r) (ty_ind' ε)
    | TData T ts => HData T ts (go ts)
    | TRef t => HRef t (ty_ind' t)
    | TArray k t => HArray k t (ty_ind' t)
    | TError => HError
    end.
End ty_ind'.

(** Pointwise boolean equality on lists, parameterised by the element test.
    Used for nested recursion (the guard checker unfolds it). *)
Fixpoint forall2b {A} (f : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => (f x y && forall2b f xs' ys')%bool
  | _, _ => false
  end.

Lemma forall2b_eq {A} (f : A -> A -> bool) xs :
  Forall (fun x => forall y, f x y = true <-> x = y) xs ->
  forall ys, forall2b f xs ys = true <-> xs = ys.
Proof.
  induction 1 as [|x xs Hx _ IH]; intros [|y ys]; simpl; try (split; congruence).
  rewrite Bool.andb_true_iff, Hx, IH. split.
  - intros [-> ->]; reflexivity.
  - intros E; inversion E; auto.
Qed.

Fixpoint ty_eqb (a b : ty) : bool :=
  match a, b with
  | TBase x, TBase y => eqb x y
  | TVar i, TVar j => Nat.eqb i j
  | TTuple xs, TTuple ys => forall2b ty_eqb xs ys
  | TArrow ps r ε, TArrow qs s η => (forall2b ty_eqb ps qs && ty_eqb r s && ty_eqb ε η)%bool
  | TData T ts, TData U us => (eqb T U && forall2b ty_eqb ts us)%bool
  | TRef t, TRef u => ty_eqb t u
  | TArray k t, TArray k' u => (eqb k k' && ty_eqb t u)%bool
  | TError, TError => true
  | _, _ => false
  end.

Lemma ty_eqb_eq (a b : ty) : ty_eqb a b = true <-> a = b.
Proof.
  revert b; induction a as [x|i|xs IH|ps r ε IHps IHr IHε|T ts IH|t IH|k t IH|] using ty_ind';
    intros [y|j|ys|qs s η|U us|u|k' u|]; cbn [ty_eqb]; try (split; congruence).
  - rewrite eqb_eq. split; congruence.
  - rewrite Nat.eqb_eq. split; congruence.
  - rewrite (forall2b_eq _ _ IH). split; congruence.
  - rewrite !Bool.andb_true_iff, (forall2b_eq _ _ IHps), IHr, IHε. split.
    + intros [[-> ->] ->]; reflexivity.
    + intros E; inversion E; auto.
  - rewrite Bool.andb_true_iff, eqb_eq, (forall2b_eq _ _ IH). split.
    + intros [-> ->]; reflexivity.
    + intros E; inversion E; auto.
  - rewrite IH. split; congruence.
  - rewrite Bool.andb_true_iff, eqb_eq, IH. split.
    + intros [-> ->]; reflexivity.
    + intros E; inversion E; auto.
Qed.

#[export] Instance EqDec_ty : EqDec ty := { eqb := ty_eqb; eqb_eq := ty_eqb_eq }.

Definition ty_eq_dec : forall x y : ty, {x = y} + {x <> y} := eq_dec.

(** ** Literals *)

(** Values of primitive types.  Integers carry their kind and an
    (already wrapped) mathematical value.  Floating point literals are kept
    as their IEEE-754 bit pattern: the type system never inspects them, and
    floating point arithmetic is deferred to the primitive interface.
    Strings are sequences of UTF-16 code units, as in MoonBit. *)
Inductive lit : Type :=
| LUnit
| LBool   (b : bool)
| LInt    (k : int_kind) (z : Z)
| LChar   (c : Z)
| LDouble (bits : Z)
| LFloat  (bits : Z)
| LString (s : list Z).

Definition lit_eq_dec (x y : lit) : {x = y} + {x <> y}.
Proof.
  decide equality; apply eq_dec.
Defined.

#[export] Instance EqDec_lit : EqDec lit := EqDec_of_dec lit_eq_dec.

Definition lit_ty (l : lit) : base_ty :=
  match l with
  | LUnit => BUnit
  | LBool _ => BBool
  | LInt k _ => BInt k
  | LChar _ => BChar
  | LDouble _ => BDouble
  | LFloat _ => BFloat
  | LString _ => BString
  end.

(** ** Primitive operators *)

Inductive arith_op : Type := AAdd | ASub | AMul | ADiv | AMod.
Inductive cmp_op   : Type := CEq | CNe | CLt | CLe | CGt | CGe.

Inductive prim_op : Type :=
| PIntArith (o : arith_op) (k : int_kind)
| PIntNeg   (k : int_kind)
| PIntCmp   (c : cmp_op) (k : int_kind)
| PCharCmp  (c : cmp_op)
| PBoolNot
| PBoolEq
| PStrConcat
| PStrEq.

(** ** Store operations (milestone M3)

    Operations that read or write the store.  They carry the types they
    work at, so that [mem_sig] is a function and types stay unique. *)
Inductive mem_op : Type :=
| MRef      (t : ty)                        (** allocate a cell *)
| MGet      (t : ty)                        (** read a cell *)
| MSet      (t : ty)                        (** write a cell *)
| MArray    (k : array_kind) (t : ty) (n : nat)  (** allocate an array of [n] given elements *)
| MMake     (k : array_kind) (t : ty)       (** [make(n, v)]: [n] copies of [v] *)
| MIndex    (k : array_kind) (t : ty)       (** [a[i]] *)
| MSetIndex (k : array_kind) (t : ty)       (** [a[i] = v] *)
| MLength   (k : array_kind) (t : ty)       (** [a.length()] *)
| MPush     (t : ty).                       (** [a.push(v)] on a growable array *)

(** Indices and lengths are MoonBit [Int]s. *)
Abbreviation TIndex := (TBase (BInt I32)).

Definition mem_sig (op : mem_op) : list ty * ty :=
  match op with
  | MRef t => ([t], TRef t)
  | MGet t => ([TRef t], t)
  | MSet t => ([TRef t; t], TBase BUnit)
  | MArray k t n => (repeat t n, TArray k t)
  | MMake k t => ([TIndex; t], TArray k t)
  | MIndex k t => ([TArray k t; TIndex], t)
  | MSetIndex k t => ([TArray k t; TIndex; t], TBase BUnit)
  | MLength k t => ([TArray k t], TIndex)
  | MPush t => ([TArray AGrow t; t], TBase BUnit)
  end.

(** ** Store typing

    A store location holds either a cell or an array; the store typing
    records which, and the element type. *)
Inductive lty : Type :=
| LCell (t : ty)
| LArr  (k : array_kind) (t : ty).

Definition lty_ty (s : lty) : ty :=
  match s with
  | LCell t => TRef t
  | LArr k t => TArray k t
  end.

Definition styping : Type := list lty.

(** ** Non-local control

    [EJump CBreak k e τ] exits the [k]-th enclosing loop (de Bruijn,
    innermost [0]) with the value of [e]; [EJump CCont k e τ] re-enters it
    with the new loop arguments [e] (a tuple).  [return] is a [break] out of
    a loop wrapped around the function body. *)
Inductive ctl : Type := CBreak | CCont.

(** Label context: for each enclosing loop, its argument types and its
    result type (index [0] is the innermost loop). *)
Definition lblctx : Type := list (list ty * ty).

Definition ctl_ty (c : ctl) (lbl : list ty * ty) : ty :=
  match c with
  | CBreak => snd lbl
  | CCont => TTuple (fst lbl)
  end.

(** ** Control context (milestone M4)

    Where non-local control can go: the enclosing loops, and the error type
    that may escape ([TNever]: none). *)
Record cctx : Type := mk_cctx {
  cc_lbls : lblctx;
  cc_exn  : ty
}.

Definition push_lbl (lbl : list ty * ty) (Λ : cctx) : cctx :=
  mk_cctx (lbl :: cc_lbls Λ) (cc_exn Λ).

Definition with_exn (ε : ty) (Λ : cctx) : cctx := mk_cctx (cc_lbls Λ) ε.

(** The empty control context: no loops, no errors. *)
Definition cc0 : cctx := mk_cctx [] TNever.

(** An effect [ε] is allowed where errors of type [ρ] may escape: it raises
    nothing, or exactly [ρ] (MoonBit has no subtyping between effects; an
    error is promoted to [Error] explicitly, see [EUp]). *)
Definition eff_le (ε ρ : ty) : Prop := ε = TNever \/ ε = ρ.

(** ** Patterns

    Pattern variables are nameless: a pattern binds its [PVar]s from left
    to right, the leftmost becoming de Bruijn index [0] of the branch body
    (the same convention as the parameters of [ELam]). *)
Inductive pat : Type :=
| PWild
| PVar
| PLit    (l : lit)
| PTuple  (ps : list pat)
| PConstr (c : ident) (ps : list pat)       (** constructor of the scrutinee's type *)
| PRef    (p : pat)                         (** the current content of a cell *)
| PUp     (T : ident) (p : pat).            (** an [Error] of error type [T] *)

Fixpoint pat_arity (p : pat) : nat :=
  match p with
  | PWild | PLit _ => 0
  | PVar => 1
  | PTuple ps | PConstr _ ps => list_sum (map pat_arity ps)
  | PRef p | PUp _ p => pat_arity p
  end.

(** ** Expressions *)

Inductive expr : Type :=
| EVar    (x : nat)
| EGlobal (f : ident) (targs : list ty)      (** instantiated top-level function *)
| ELit    (l : lit)
| ELam    (ps : list ty) (r : ty) (ε : ty) (body : expr)
| EApp    (f : expr) (args : list expr)
| ELet    (e1 : expr) (e2 : expr)            (** binds one variable in [e2] *)
| EIf     (c t e : expr)
| ETuple  (es : list expr)
| EProj   (e : expr) (i : nat)
| EPrim   (op : prim_op) (args : list expr)
| EConstr (T c : ident) (ts : list ty) (e : expr)
    (** constructor [c] of [T[ts]]; the payload [e] is the tuple of fields *)
| EMatch  (e : expr) (τ : ty) (bs : list (pat * expr))
    (** [match e { p => b, .. } : τ]; the result type keeps types unique
        even for an empty [match] *)
| ELoc    (l : nat)                          (** store location (runtime only) *)
| EMem    (op : mem_op) (args : list expr)   (** store operation *)
| ELoop   (init : expr) (ps : list ty) (τ : ty) (body : expr)
    (** [init] is the tuple of initial loop arguments, bound like the
        parameters [ps] of a λ in [body]; [body] produces the loop's result
        of type [τ] unless it [continue]s *)
| EJump   (c : ctl) (k : nat) (e : expr) (τ : ty)
    (** [break]/[continue] to the [k]-th enclosing loop; [τ] is the type of
        the jump expression itself (it does not return) *)
| EAbort  (τ : ty)
    (** [panic()]: stops the program; [τ] is its type (it does not return) *)
(* ---- milestone M4: errors ---- *)
| EUp     (T : ident) (e : expr)             (** promote an error of type [T] to [Error] *)
| ERaise  (e : expr) (τ : ty)                (** [raise e]; [τ] is its own type *)
| ETry    (e : expr) (τe : ty) (h k : expr)
    (** [try e catch { x => h } noraise { y => k }]: [e] may raise [τe];
        [h] and [k] bind one variable *)
| EDefer  (onerr : bool) (c e : expr).
    (** [defer c; e] ([errdefer] when [onerr]): run [c] when leaving [e] *)

Abbreviation EBreak := (EJump CBreak).
Abbreviation EContinue := (EJump CCont).

(** ** Global environment *)

(** A top-level function [fn[X0 .. Xn-1] f(params) -> ret { body }].
    The body is typed in context [fd_params] with [fd_tparams] type
    variables in scope; all globals (including [f]) are visible, which gives
    (mutual) recursion. *)
Record fdef : Type := mk_fdef {
  fd_name    : ident;
  fd_tparams : nat;
  fd_params  : list ty;
  fd_ret     : ty;
  fd_eff     : ty;             (** the error type it may raise ([TNever]: none) *)
  fd_body    : expr
}.

(** A constructor and the types of its fields, over the type parameters of
    its data type. *)
Record cdef : Type := mk_cdef {
  cd_name   : ident;
  cd_fields : list ty
}.

(** A nominal data type [T[X0 .. Xn-1]] with its constructors.  MoonBit
    [enum]s map to it directly; a [struct] or tuple struct [T] is a single
    constructor also named [T] (field names live in the Surface layer). *)
Record tdef : Type := mk_tdef {
  td_name    : ident;
  td_tparams : nat;
  td_ctors   : list cdef;
  td_err     : bool            (** a [suberror]: its values may be raised *)
}.

Record genv : Type := mk_genv {
  ge_types : list tdef;
  ge_funs  : list fdef
}.

Definition lookup_fn (ge : genv) (f : ident) : option fdef :=
  find (fun fd => eqb (fd_name fd) f) (ge_funs ge).

Lemma lookup_fn_in ge f fd : lookup_fn ge f = Some fd -> In fd (ge_funs ge).
Proof. unfold lookup_fn; intros H; now apply find_some in H. Qed.

Definition lookup_ty (ge : genv) (T : ident) : option tdef :=
  find (fun td => eqb (td_name td) T) (ge_types ge).

Definition lookup_ctor (td : tdef) (c : ident) : option cdef :=
  find (fun cd => eqb (cd_name cd) c) (td_ctors td).
