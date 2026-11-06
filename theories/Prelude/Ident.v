(** * Identifiers

    Source-level names.  We use Stdlib [string] (a list of [Ascii]) so that
    all proofs stay axiom-free; at extraction time [ExtrOcamlNativeString]
    maps it to OCaml's native [string].  Code outside this file should only
    rely on [ident] having decidable equality, never on its representation,
    so the representation can be swapped later (e.g. for interned symbols). *)

From Stdlib Require Import String.
From MoonRocq.Prelude Require Import EqDec.

Definition ident : Type := string.

#[export] Instance EqDec_ident : EqDec ident := EqDec_string.

(** Package path, e.g. [@moonbitlang/core/builtin] as a list of segments. *)
Definition pkg_path : Type := list ident.

(** A name qualified by its defining package. Global entities (types, traits,
    top-level functions, constructors of extensible enums) are always
    referred to by qualified names after name resolution. *)
Record qname : Type := mk_qname { qn_pkg : pkg_path; qn_name : ident }.

Definition qname_eqb (a b : qname) : bool :=
  (eqb (qn_pkg a) (qn_pkg b) && eqb (qn_name a) (qn_name b))%bool.

Lemma qname_eqb_eq (x y : qname) : qname_eqb x y = true <-> x = y.
Proof.
  destruct x as [p n], y as [q m]; unfold qname_eqb; cbn [qn_pkg qn_name].
  rewrite Bool.andb_true_iff, !eqb_eq. split.
  - intros [-> ->]; reflexivity.
  - intros E; inversion E; auto.
Qed.

#[export] Instance EqDec_qname : EqDec qname := { eqb := qname_eqb; eqb_eq := qname_eqb_eq }.
