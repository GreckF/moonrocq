(** * Surface syntax (preliminary)

    A named, lightly-desugared view of MoonBit programs: the shape that the
    front end (the official MoonBit parser plus a thin projection, see
    [extraction/]) hands to the elaborator.  It only covers the fragment that
    Core can express so far; everything else is rejected by the front end as
    "unsupported" before reaching Rocq.

    Differences from the concrete syntax:
    - blocks [{ s1; ...; e }] are already nested [SLet]s ([e1; e2] is
      [SLet None None e1 e2]);
    - [if c { t }] without [else] keeps [None] (it has type [Unit]);
    - names are plain identifiers; resolution to de Bruijn indices,
      globals and builtin types happens in elaboration ([ElabSpec.v]).

    Every node carries a source position for error reporting. *)

From Stdlib Require Import List ZArith NArith String.
From MoonRocq.Prelude Require Import Ident.
From MoonRocq.Core Require Import Syntax.
Import ListNotations.

(** Source position: 1-based line and column. *)
Record pos : Type := mk_pos { pos_line : N; pos_col : N }.

(** Surface types.  Builtin type names ([Int], [Bool], [Error], ...), user
    data types and the type parameters in scope are all [SName]s; [T?] is
    [SName "Option" [T]].  The effect of a function type is [None] for
    [noraise] (the default) and [Some t] for [raise t]; a plain [raise] is
    [raise Error], and [raise?] is [raise ?] where [?] is a hidden type
    parameter of the enclosing signature. *)
Inductive sty : Type :=
| SName  (p : pos) (n : ident) (args : list sty)
| STuple (p : pos) (ts : list sty)
| SArrow (p : pos) (ps : list sty) (r : sty) (eff : option sty)
| SObj   (p : pos) (Tr : ident).                (** trait object [&Tr] *)

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
| SLam   (p : pos) (ps : list (ident * option sty)) (ret : option sty)
         (eff : option (option sty)) (body : sexpr)
    (** [eff]: [None] if not annotated, else the annotated effect *)
| SAnnot (p : pos) (e : sexpr) (t : sty)
| SConstr (p : pos) (T : option ident) (c : ident)      (** constructor [T::c] or [c] *)
| SRecord (p : pos) (T : option ident) (fs : list (ident * sexpr))  (** [T::{ x: e, .. }] *)
| SField  (p : pos) (e : sexpr) (f : ident)                         (** [e.f] *)
| SMatch  (p : pos) (e : sexpr) (cases : list (spat * sexpr))
(* ---- milestone M3: state and loops ---- *)
| SLetMut   (p : pos) (x : ident) (ann : option sty) (e1 body : sexpr)   (** [let mut x = e1; body] *)
| SAssign   (p : pos) (x : ident) (op : option ident) (e : sexpr)        (** [x = e], [x += e] *)
| SArray    (p : pos) (es : list sexpr)                                  (** [[e1, e2]] *)
| SIndex    (p : pos) (a i : sexpr)                                      (** [a[i]] *)
| SIndexSet (p : pos) (a i : sexpr) (op : option ident) (v : sexpr)      (** [a[i] = v], [a[i] += v] *)
| SFieldSet (p : pos) (e : sexpr) (f : ident) (op : option ident) (v : sexpr)  (** [e.f = v] *)
| SMethod   (p : pos) (e : sexpr) (m : ident) (args : list sexpr)        (** [e.m(args)] *)
| SQual     (p : pos) (T m : ident)                                      (** [T::m] *)
| SWhile    (p : pos) (l : option ident) (c body : sexpr) (nb : option sexpr)
    (** [l~: while c { body } nobreak { nb }] *)
| SFor      (p : pos) (l : option ident) (init : list (ident * sexpr)) (c : option sexpr)
            (upd : list (ident * sexpr)) (body : sexpr) (nb : option sexpr)
    (** [l~: for x = e, ..; c; x = u, .. { body } nobreak { nb }] *)
| SBlock    (p : pos) (l : ident) (body : sexpr)                         (** [l~: { body }] *)
| SBreak    (p : pos) (l : option ident) (arg : option sexpr)
| SContinue (p : pos) (l : option ident) (args : list sexpr)
| SReturn   (p : pos) (arg : option sexpr)
| SForIn    (p : pos) (l : option ident) (pats : list spat) (src : sexpr)
            (init upd : list (ident * sexpr)) (body : sexpr) (nb : option sexpr)
    (** [l~: for p, .. in src; s = e, ..; s = u, .. { body } nobreak { nb }] *)
(* ---- milestone M4: errors ---- *)
| SRaise    (p : pos) (e : sexpr)
| STry      (p : pos) (body : sexpr) (catch : list (spat * sexpr))
            (noraise : option (list (spat * sexpr)))
    (** [try body catch { arms } noraise { arms }] (also [body catch { .. }]) *)
| STryBang  (p : pos) (body : sexpr)                                  (** [try! body] *)
| SDefer    (p : pos) (onerr : bool) (c body : sexpr)                 (** [defer c; body] / [errdefer] *)
(* ---- milestone M5: traits ---- *)
| SAs       (p : pos) (e : sexpr) (Tr : ident).                       (** [e as &Tr] *)

(** A top-level function [fn[T : Tr, ..] f(x : A, ..) -> R { body }], or a
    method [fn T::f(self : T, ..)] ([sf_self = Some T]).  A missing return
    type means [Unit], as in MoonBit.  [sf_bounds] lists the trait bounds
    [(type parameter, trait)]. *)
Record sfun : Type := mk_sfun {
  sf_pos     : pos;
  sf_self    : option ident;
  sf_name    : ident;
  sf_tparams : list ident;
  sf_bounds  : list (ident * ident);
  sf_params  : list (ident * sty);
  sf_ret     : option sty;
  sf_eff     : option sty;     (** as for [SArrow] *)
  sf_body    : sexpr
}.

(** Type declarations: [enum T[..] { C(A, B), .. }], [struct T[..] { x : A, .. }]
    and the tuple struct [struct T[..](A, B)].  A struct field is
    [(name, mutable, type)]. *)
Inductive sdecl : Type :=
| SDEnum        (cs : list (ident * list sty))
| SDStruct      (fs : list (ident * bool * sty))
| SDTupleStruct (ts : list sty)
| SDError       (cs : list (ident * list sty)).   (** [suberror E { C(A), .. }] *)

Record stype : Type := mk_stype {
  st_pos     : pos;
  st_name    : ident;
  st_tparams : list ident;
  st_body    : sdecl
}.

(** A trait method signature; [Self] is the type name [Self]. *)
Record smeth : Type := mk_smeth {
  sm_name    : ident;
  sm_params  : list sty;
  sm_ret     : sty;
  sm_eff     : option sty;
  sm_default : bool            (** declared [= _]: has a default implementation *)
}.

(** [trait Tr : S1 + S2 { methods }] *)
Record strait : Type := mk_strait {
  str_pos     : pos;
  str_name    : ident;
  str_supers  : list ident;
  str_methods : list smeth
}.

(** One method of an [impl]: [with m(params) -> R raise E { body }]; the
    parameter types may be omitted (they come from the trait). *)
Record simethod : Type := mk_simethod {
  sim_name   : ident;
  sim_params : list (ident * option sty);
  sim_ret    : option sty;
  sim_eff    : option sty;
  sim_body   : sexpr
}.

(** [impl[X : B, ..] Tr for T with m(..) { .. }]; [si_self = None] is a
    default implementation [impl Tr with m(..)], and [si_method = None] a
    bare [impl Tr for T]. *)
Record simpl : Type := mk_simpl {
  si_pos     : pos;
  si_tparams : list ident;
  si_bounds  : list (ident * ident);
  si_trait   : ident;
  si_self    : option sty;
  si_method  : option simethod
}.

(** A program: type declarations, traits, impls, top-level functions and
    the body of [fn main], if any. *)
Record sprog : Type := mk_sprog {
  sp_types : list stype;
  sp_traits : list strait;
  sp_impls : list simpl;
  sp_funs  : list sfun;
  sp_main  : option sexpr
}.

Definition sexpr_pos (e : sexpr) : pos :=
  match e with
  | SVar p _ | SLit p _ | SApp p _ _ | SInfix p _ _ _ | SUnary p _ _
  | SLet p _ _ _ _ | SIf p _ _ _ | STup p _ | SProj p _ _ | SLam p _ _ _ _
  | SAnnot p _ _ | SConstr p _ _ | SRecord p _ _ | SField p _ _ | SMatch p _ _
  | SLetMut p _ _ _ _ | SAssign p _ _ _ | SArray p _ | SIndex p _ _ | SIndexSet p _ _ _ _
  | SFieldSet p _ _ _ _ | SMethod p _ _ _ | SQual p _ _ | SWhile p _ _ _ _
  | SFor p _ _ _ _ _ _ | SBlock p _ _ | SBreak p _ _ | SContinue p _ _ | SReturn p _
  | SForIn p _ _ _ _ _ _ _ | SRaise p _ | STry p _ _ _ | STryBang p _ | SDefer p _ _ _
  | SAs p _ _ => p
  end.
