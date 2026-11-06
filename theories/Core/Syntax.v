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
    - MoonBit functions are n-ary, not curried: [TArrow ps r], [EApp f args].

    Milestone M1 covers primitive types, functions, [let], [if], tuples,
    (mutually) recursive generic top-level functions and primitive
    operators.  Later milestones extend these inductive types. *)

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
| BString.

Definition int_kind_eq_dec (x y : int_kind) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition base_ty_eq_dec (x y : base_ty) : {x = y} + {x <> y}.
Proof. decide equality. apply int_kind_eq_dec. Defined.

#[export] Instance EqDec_int_kind : EqDec int_kind := EqDec_of_dec int_kind_eq_dec.
#[export] Instance EqDec_base_ty : EqDec base_ty := EqDec_of_dec base_ty_eq_dec.

(** ** Types *)

Inductive ty : Type :=
| TBase  (b : base_ty)
| TVar   (i : nat)
| TTuple (ts : list ty)
| TArrow (ps : list ty) (r : ty).

Notation TUnit   := (TBase BUnit).
Notation TBool   := (TBase BBool).
Notation TInt k  := (TBase (BInt k)).
Notation TString := (TBase BString).

(** Induction principle that sees through the nested lists. *)
Section ty_ind'.
  Variable P : ty -> Prop.
  Hypothesis HBase  : forall b, P (TBase b).
  Hypothesis HVar   : forall i, P (TVar i).
  Hypothesis HTuple : forall ts, Forall P ts -> P (TTuple ts).
  Hypothesis HArrow : forall ps r, Forall P ps -> P r -> P (TArrow ps r).

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
    | TArrow ps r => HArrow ps r (go ps) (ty_ind' r)
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
  | TArrow ps r, TArrow qs s => (forall2b ty_eqb ps qs && ty_eqb r s)%bool
  | _, _ => false
  end.

Lemma ty_eqb_eq (a b : ty) : ty_eqb a b = true <-> a = b.
Proof.
  revert b; induction a as [x|i|xs IH|ps r IHps IHr] using ty_ind';
    intros [y|j|ys|qs s]; cbn [ty_eqb]; try (split; congruence).
  - rewrite eqb_eq. split; congruence.
  - rewrite Nat.eqb_eq. split; congruence.
  - rewrite (forall2b_eq _ _ IH). split; congruence.
  - rewrite Bool.andb_true_iff, (forall2b_eq _ _ IHps), IHr. split.
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

(** ** Expressions *)

Inductive expr : Type :=
| EVar    (x : nat)
| EGlobal (f : ident) (targs : list ty)      (** instantiated top-level function *)
| ELit    (l : lit)
| ELam    (ps : list ty) (r : ty) (body : expr)
| EApp    (f : expr) (args : list expr)
| ELet    (e1 : expr) (e2 : expr)            (** binds one variable in [e2] *)
| EIf     (c t e : expr)
| ETuple  (es : list expr)
| EProj   (e : expr) (i : nat)
| EPrim   (op : prim_op) (args : list expr).

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
  fd_body    : expr
}.

Definition genv : Type := list fdef.

Definition lookup_fn (ge : genv) (f : ident) : option fdef :=
  find (fun fd => eqb (fd_name fd) f) ge.

Lemma lookup_fn_in ge f fd : lookup_fn ge f = Some fd -> In fd ge.
Proof. unfold lookup_fn; intros H; now apply find_some in H. Qed.
