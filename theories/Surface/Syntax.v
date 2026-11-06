(** * Surface syntax (preliminary)

    A named, lightly-desugared view of MoonBit programs: the shape that the
    front end (the official MoonBit parser plus a thin projection, see
    [extraction/]) hands to the elaborator.  It only covers the fragment that
    Core M1 can express; everything else is rejected by the front end as
    "unsupported" before reaching Rocq.

    Differences from the concrete syntax:
    - blocks [{ s1; ...; e }] are already nested [SLet]s ([e1; e2] is
      [SLet None None e1 e2]);
    - [if c { t }] without [else] keeps [None] (it has type [Unit]);
    - names are plain identifiers; resolution to de Bruijn indices,
      globals and builtin types happens in [Elab.v].

    Every node carries a source position for error reporting. *)

From Stdlib Require Import List ZArith NArith String.
From MoonRocq.Prelude Require Import Ident.
From MoonRocq.Core Require Import Syntax.
Import ListNotations.

(** Source position: 1-based line and column. *)
Record pos : Type := mk_pos { pos_line : N; pos_col : N }.

(** Surface types.  Builtin type names ([Int], [Bool], ...), user data
    types and the type parameters in scope are all [SName]s; [T?] is
    [SName "Option" [T]]. *)
Inductive sty : Type :=
| SName  (p : pos) (n : ident) (args : list sty)
| STuple (p : pos) (ts : list sty)
| SArrow (p : pos) (ps : list sty) (r : sty).

(** Literals.  [SLInt None z] is an unsuffixed integer literal: its kind
    comes from the expected type, defaulting to [Int]. *)
Inductive slit : Type :=
| SLUnit
| SLBool   (b : bool)
| SLInt    (k : option int_kind) (z : Z)
| SLChar   (c : Z)
| SLDouble (bits : Z)
| SLFloat  (bits : Z)
| SLString (s : list Z).

(** Patterns.  [SPConstr _ T c ps open] is [T::c(ps)] ([T] optional);
    [open] is a trailing [..] (remaining fields are wildcards).  A record
    pattern [{ x: p, y, .. }] lists fields by name; [y] is a pun for
    [y: y]. *)
Inductive spat : Type :=
| SPWild   (p : pos)
| SPVar    (p : pos) (x : ident)
| SPLit    (p : pos) (l : slit)
| SPTuple  (p : pos) (ps : list spat)
| SPConstr (p : pos) (T : option ident) (c : ident) (ps : list spat) (open : bool)
| SPRecord (p : pos) (fs : list (ident * spat)) (open : bool)
| SPAnnot  (p : pos) (q : spat) (t : sty).

Inductive sexpr : Type :=
| SVar   (p : pos) (x : ident)
| SLit   (p : pos) (l : slit)
| SApp   (p : pos) (f : sexpr) (args : list sexpr)
| SInfix (p : pos) (op : ident) (a b : sexpr)
| SUnary (p : pos) (op : ident) (a : sexpr)
| SLet   (p : pos) (x : option ident) (ann : option sty) (e1 body : sexpr)
| SIf    (p : pos) (c t : sexpr) (e : option sexpr)
| STup   (p : pos) (es : list sexpr)
| SProj  (p : pos) (e : sexpr) (i : nat)
| SLam   (p : pos) (ps : list (ident * option sty)) (ret : option sty) (body : sexpr)
| SAnnot (p : pos) (e : sexpr) (t : sty)
| SConstr (p : pos) (T : option ident) (c : ident)      (** constructor [T::c] or [c] *)
| SRecord (p : pos) (T : option ident) (fs : list (ident * sexpr))  (** [T::{ x: e, .. }] *)
| SField  (p : pos) (e : sexpr) (f : ident)                         (** [e.f] *)
| SMatch  (p : pos) (e : sexpr) (cases : list (spat * sexpr)).

(** A top-level function [fn[T, ..] f(x : A, ..) -> R { body }].
    A missing return type means [Unit], as in MoonBit. *)
Record sfun : Type := mk_sfun {
  sf_pos     : pos;
  sf_name    : ident;
  sf_tparams : list ident;
  sf_params  : list (ident * sty);
  sf_ret     : option sty;
  sf_body    : sexpr
}.

(** Type declarations: [enum T[..] { C(A, B), .. }], [struct T[..] { x : A, .. }]
    and the tuple struct [struct T[..](A, B)]. *)
Inductive sdecl : Type :=
| SDEnum        (cs : list (ident * list sty))
| SDStruct      (fs : list (ident * sty))
| SDTupleStruct (ts : list sty).

Record stype : Type := mk_stype {
  st_pos     : pos;
  st_name    : ident;
  st_tparams : list ident;
  st_body    : sdecl
}.

(** A program: type declarations, top-level functions and the body of
    [fn main], if any. *)
Record sprog : Type := mk_sprog {
  sp_types : list stype;
  sp_funs  : list sfun;
  sp_main  : option sexpr
}.

Definition sexpr_pos (e : sexpr) : pos :=
  match e with
  | SVar p _ | SLit p _ | SApp p _ _ | SInfix p _ _ _ | SUnary p _ _
  | SLet p _ _ _ _ | SIf p _ _ _ | STup p _ | SProj p _ _ | SLam p _ _ _
  | SAnnot p _ _ | SConstr p _ _ | SRecord p _ _ | SField p _ _ | SMatch p _ _ => p
  end.
