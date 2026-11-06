(** * Primitive operators: signatures and semantics

    Primitives are monomorphic and only take/return primitive types.  The
    soundness proof needs exactly two facts about them, proved at the end of
    this file:
    - [prim_sig_args_base]: their argument types are primitive types
      (hence closed: see [Subst.prim_sig_closed]);
    - [prim_eval_progress]: on well-typed literal arguments they either
      produce a literal of the result type or abort (e.g. division by
      zero); they are never undefined. *)

From Stdlib Require Import List ZArith Bool.
From MoonRocq.Prelude Require Import EqDec.
From MoonRocq.Core Require Import Syntax.
Import ListNotations.

Local Open Scope Z_scope.

Definition prim_sig (op : prim_op) : list ty * ty :=
  match op with
  | PIntArith _ k => ([TInt k; TInt k], TInt k)
  | PIntNeg k     => ([TInt k], TInt k)
  | PIntCmp _ k   => ([TInt k; TInt k], TBool)
  | PCharCmp _    => ([TBase BChar; TBase BChar], TBool)
  | PBoolNot      => ([TBool], TBool)
  | PBoolEq       => ([TBool; TBool], TBool)
  | PStrConcat    => ([TString; TString], TString)
  | PStrEq        => ([TString; TString], TBool)
  end.

(** ** Machine integers: wrap-around to the width of the kind *)

Definition wrap_unsigned (n : Z) (z : Z) : Z := z mod 2 ^ n.

Definition wrap_signed (n : Z) (z : Z) : Z :=
  let r := z mod 2 ^ n in
  if r >=? 2 ^ (n - 1) then r - 2 ^ n else r.

Definition wrap (k : int_kind) (z : Z) : Z :=
  match k with
  | I16 => wrap_signed 16 z
  | I32 => wrap_signed 32 z
  | I64 => wrap_signed 64 z
  | U16 => wrap_unsigned 16 z
  | U32 => wrap_unsigned 32 z
  | U64 => wrap_unsigned 64 z
  | IByte => wrap_unsigned 8 z
  | IBigInt => z
  end.

Definition cmp_Z (c : cmp_op) (a b : Z) : bool :=
  match c with
  | CEq => a =? b
  | CNe => negb (a =? b)
  | CLt => a <? b
  | CLe => a <=? b
  | CGt => b <? a
  | CGe => b <=? a
  end.

(** ** Evaluation *)

Inductive prim_outcome : Type :=
| PVal (l : lit)      (** normal result *)
| PAbort              (** runtime panic, e.g. division by zero *)
| PBad.               (** arguments of the wrong shape: excluded by typing *)

(** Integer division truncates towards zero ([Z.quot]/[Z.rem]), as in
    MoonBit's backends.  The result is wrapped to the kind's width. *)
Definition int_arith (o : arith_op) (k : int_kind) (a b : Z) : prim_outcome :=
  match o with
  | AAdd => PVal (LInt k (wrap k (a + b)))
  | ASub => PVal (LInt k (wrap k (a - b)))
  | AMul => PVal (LInt k (wrap k (a * b)))
  | ADiv => if b =? 0 then PAbort else PVal (LInt k (wrap k (Z.quot a b)))
  | AMod => if b =? 0 then PAbort else PVal (LInt k (wrap k (Z.rem a b)))
  end.

Definition prim_eval (op : prim_op) (args : list lit) : prim_outcome :=
  match op, args with
  | PIntArith o k, [LInt _ a; LInt _ b] => int_arith o k a b
  | PIntNeg k,     [LInt _ a]           => PVal (LInt k (wrap k (- a)))
  | PIntCmp c _,   [LInt _ a; LInt _ b] => PVal (LBool (cmp_Z c a b))
  | PCharCmp c,    [LChar a; LChar b]   => PVal (LBool (cmp_Z c a b))
  | PBoolNot,      [LBool a]            => PVal (LBool (negb a))
  | PBoolEq,       [LBool a; LBool b]   => PVal (LBool (Bool.eqb a b))
  | PStrConcat,    [LString a; LString b] => PVal (LString (a ++ b))
  | PStrEq,        [LString a; LString b] => PVal (LBool (eqb a b))
  | _, _ => PBad
  end.

(** ** Facts used by the soundness proof *)

(** All argument types of primitives are primitive types. *)
Lemma prim_sig_args_base op :
  Forall (fun t => exists b, t = TBase b) (fst (prim_sig op)).
Proof. destruct op; simpl; repeat constructor; eauto. Qed.

(** A literal list matches a list of primitive types. *)
Definition lits_typed (ls : list lit) (ts : list ty) : Prop :=
  Forall2 (fun l t => TBase (lit_ty l) = t) ls ts.

Lemma lit_int_inv l k : TBase (lit_ty l) = TInt k -> exists z, l = LInt k z.
Proof. destruct l; simpl; intros H; inversion H; eauto. Qed.

Lemma lit_bool_inv l : TBase (lit_ty l) = TBool -> exists b, l = LBool b.
Proof. destruct l; simpl; intros H; inversion H; eauto. Qed.

Lemma lit_char_inv l : TBase (lit_ty l) = TBase BChar -> exists c, l = LChar c.
Proof. destruct l; simpl; intros H; inversion H; eauto. Qed.

Lemma lit_string_inv l : TBase (lit_ty l) = TString -> exists s, l = LString s.
Proof. destruct l; simpl; intros H; inversion H; eauto. Qed.

Lemma int_arith_progress o k a b :
  int_arith o k a b = PAbort \/
  exists l, int_arith o k a b = PVal l /\ TBase (lit_ty l) = TInt k.
Proof.
  destruct o; simpl; try (right; eexists; split; reflexivity);
    destruct (b =? 0); auto; right; eexists; split; reflexivity.
Qed.

Theorem prim_eval_progress op ls :
  lits_typed ls (fst (prim_sig op)) ->
  prim_eval op ls = PAbort \/
  exists l, prim_eval op ls = PVal l /\ TBase (lit_ty l) = snd (prim_sig op).
Proof.
  unfold lits_typed; intros H.
  destruct op; simpl in *;
    repeat match goal with
    | H : Forall2 _ _ (_ :: _) |- _ =>
        let Hl := fresh "Hl" in inversion H as [|? ? ? ? Hl ?]; subst; clear H
    | H : Forall2 _ _ [] |- _ => inversion H; subst; clear H
    | Hl : TBase (lit_ty _) = TInt _ |- _ =>
        apply lit_int_inv in Hl as (? & ->)
    | Hl : TBase (lit_ty _) = TBool |- _ =>
        apply lit_bool_inv in Hl as (? & ->)
    | Hl : TBase (lit_ty _) = TBase BChar |- _ =>
        apply lit_char_inv in Hl as (? & ->)
    | Hl : TBase (lit_ty _) = TString |- _ =>
        apply lit_string_inv in Hl as (? & ->)
    end; simpl;
    first [ apply int_arith_progress | right; eexists; split; reflexivity ].
Qed.
