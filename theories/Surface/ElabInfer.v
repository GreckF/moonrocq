(** * Surface: the certified algorithmic elaborator (milestone M6b)

    [infer s L Γ m θ n] follows the rules of [ElabAlg.v]: it returns the
    type, the Core term, the new substitution and the next free
    metavariable, together with a derivation.  Its answer has the same
    shape in both modes (only the proof depends on the mode), so that it
    extracts without unsafe coercions.

    Covered so far: the language of milestone M1. *)

From Stdlib Require Import List ZArith String Bool Arith.
From MoonRocq.Prelude Require Import Result EqDec Ident.
From MoonRocq.Core Require Import Syntax Prim Subst Typing Check.
From MoonRocq.Surface Require Import Syntax Resolve Base ElabSpec Unify ElabAlg Elaborate.
Import ListNotations.

Local Open Scope string_scope.

(** ** Views

    Decisions on computed values return their evidence, so that the
    elaborator never matches dependently on a computed term (which keeps
    its completeness proof manageable). *)

Definition oview {A} (o : option A) : {a | o = Some a} + {o = None} :=
  match o as o' return {a | o' = Some a} + {o' = None} with
  | Some a => inleft (exist _ a eq_refl)
  | None => inright eq_refl
  end.

Definition bview (b : bool) : {b = true} + {b = false} :=
  match b as b' return {b' = true} + {b' = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition int_view (t : ty) : {k | t = TInt k} + {forall k, t <> TInt k}.
Proof.
  destruct t as [[]| | | | | | |]; try (left; eexists; reflexivity); right; intros k0; discriminate.
Defined.

Definition tuple_view (t : ty) : {ts | t = TTuple ts} + {forall ts, t <> TTuple ts}.
Proof.
  destruct t as [| |ts| | | | |]; try (left; eexists; reflexivity); right; intros ts'; discriminate.
Defined.

Definition arrow_view (t : ty) : {ps : list ty & {r : ty & {ε : ty | t = TArrow ps r ε}}} +
                                 {forall ps r ε, t <> TArrow ps r ε}.
Proof.
  destruct t as [| | |ps r ε| | | |]; try (left; exists ps, r, ε; reflexivity); right; intros ? ? ?; discriminate.
Defined.

Definition ref_view (t : ty) : {u | t = TRef u} + {is_cell t = false}.
Proof. destruct t as [| | | | |u| |]; try (left; exists u; reflexivity); right; reflexivity. Defined.

Definition rview {A Er} (r : result A Er) : {a | r = Ok a} + {err | r = Err err} :=
  match r as r0 return {a | r0 = Ok a} + {err | r0 = Err err} with
  | Ok a => inl (exist _ a eq_refl)
  | Err err => inr (exist _ err eq_refl)
  end.

Definition lview {A} (l : list A) : {l = []} + {l <> []}.
Proof. destruct l; [left; reflexivity|right; discriminate]. Defined.

Definition binop_v (p : pos) (op : ident) (τ : ty) (a b : expr) :
    result {e | elab_binop p op τ a b = Ok e} elab_error :=
  match rview (elab_binop p op τ a b) with
  | inl (exist _ e H) => Ok (exist _ e H)
  | inr (exist _ err _) => Err err
  end.

Section Infer.
  Variable E : senv.
  Abbreviation hdr := (se_hdr E).

  Definition aoutP (L : cenv) (Γ : lctx) (s : sexpr) (m : mode) (θ : sub) (n : nat)
      (τ : ty) (e : expr) (θ' : sub) (n' : nat) : Prop :=
    match m with
    | Syn => Γ ⊩ᵃ[E;L] s ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'
    | Chk τ0 => τ = τ0 /\ Γ ⊩ᵃ[E;L] s ⇐ τ0 ⇝ e ∣ θ ; n ↦ θ' ; n'
    end.

  Definition aout (L : cenv) (Γ : lctx) (s : sexpr) (m : mode) (θ : sub) (n : nat) : Type :=
    {τ : ty & {e : expr & {θ' : sub & {n' : nat | aoutP L Γ s m θ n τ e θ' n'}}}}.

  Definition acout (L : cenv) (Γ : lctx) (s : sexpr) (τ : ty) (θ : sub) (n : nat) : Type :=
    {e : expr & {θ' : sub & {n' : nat | Γ ⊩ᵃ[E;L] s ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n'}}}.

  Definition aok {L Γ s τ θ n} (e : expr) (θ' : sub) (n' : nat)
      (H : Γ ⊩ᵃ[E;L] s ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n') : result (aout L Γ s (Chk τ) θ n) elab_error :=
    Ok (existT _ τ (existT _ e (existT _ θ' (exist _ n' (conj eq_refl H))))).

  Definition ac {L Γ s τ θ n} (r : result (aout L Γ s (Chk τ) θ n) elab_error) :
      result (acout L Γ s τ θ n) elab_error :=
    match r with
    | Ok (existT _ _ (existT _ e (existT _ θ' (exist _ n' H)))) =>
        Ok (existT _ e (existT _ θ' (exist _ n' (proj2 H))))
    | Err err => Err err
    end.

  Definition ety_v (t : sty) : result {τ | ety E t = Ok τ} elab_error :=
    match rview (ety E t) with
    | inl (exist _ τ H) => Ok (exist _ τ H)
    | inr (exist _ err _) => Err err
    end.

  Definition eff_v (a : option (option sty)) : result {ε | eff_syn E a ε} elab_error :=
    match a as a0 return result {ε | eff_syn E a0 ε} elab_error with
    | None => Ok (exist _ TNever eq_refl)
    | Some None => Ok (exist _ TNever eq_refl)
    | Some (Some t) => '(exist _ ε H) <- ety_v t ;; Ok (exist _ ε H)
    end.

  Definition nb_v (p : pos) (g : ident) : result (sbounds E g = []) elab_error :=
    match lview (sbounds E g) with
    | left H => Ok H
    | right _ => Err (EE_Unsupported p "a function with trait bounds")
    end.

  Abbreviation infer_t :=
    (forall (s : sexpr) (L : cenv) (Γ : lctx) (m : mode) (θ : sub) (n : nat),
        result (aout L Γ s m θ n) elab_error).

  (** ** Building blocks *)

  Definition acoerce_dec (p : pos) (θ : sub) (n : nat) (e : expr) (τ' τ : ty) :
      result {e' : expr & {θ' : sub | acoerce E θ n e τ' τ e' θ'}} elab_error :=
    match oview (up_case (sapp θ τ') (sapp θ τ)) with
    | inleft (exist _ T Hu) =>
        H <- err_dec E p T ;;
        Ok (existT _ (EUp T e) (exist _ θ (ACo_Up E θ n e τ' τ T Hu H)))
    | inright Hu =>
        match oview (unify_all E n θ [(τ', τ)]) with
        | inleft (exist _ θ' Hun) => Ok (existT _ e (exist _ θ' (ACo_Unify E θ n e τ' τ θ' Hu Hun)))
        | inright _ => Err (EE_Annot p (sapp θ τ) (sapp θ τ'))
        end
    end.

  (** Checking by synthesis and conversion. *)
  Definition afin (p : pos) (L : cenv) (Γ : lctx) (s : sexpr) (τ : ty) (θ : sub) (n : nat)
      (Hcs : chk_spec E Γ s (sapp θ τ) = false) (r : result (aout L Γ s Syn θ n) elab_error) :
      result (aout L Γ s (Chk τ) θ n) elab_error :=
    '(existT _ τ' (existT _ e (existT _ θ1 (exist _ n1 H)))) <- r ;;
    '(existT _ e' (exist _ θ2 Hc)) <- acoerce_dec p θ1 n1 e τ' τ ;;
    aok e' θ2 n1 (B_Sub E L Γ s τ τ' e e' θ n θ1 n1 θ2 Hcs H Hc).

  (** In mode [m]: synthesis, or checking by [afin] when the construct has
      no checking rule of its own. *)
  Definition amode (p : pos) (L : cenv) (Γ : lctx) (s : sexpr) (m : mode) (θ : sub) (n : nat)
      (Hcs : forall τ, chk_spec E Γ s τ = false) (r : result (aout L Γ s Syn θ n) elab_error) :
      result (aout L Γ s m θ n) elab_error :=
    match m as m0 return result (aout L Γ s m0 θ n) elab_error with
    | Syn => r
    | Chk τ => afin p L Γ s τ θ n (Hcs (sapp θ τ)) r
    end.

  Definition asyns_dec (rec : infer_t) (L : cenv) (Γ : lctx) :
      forall ss θ n, result {τs : list ty & {es : list expr & {θ' : sub & {n' : nat |
                       Γ ⊩ᵃ*[E;L] ss ⇒ τs ⇝ es ∣ θ ; n ↦ θ' ; n'}}}} elab_error :=
    fix go ss θ n :=
      match ss as l return result {τs : list ty & {es : list expr & {θ' : sub & {n' : nat |
                             Γ ⊩ᵃ*[E;L] l ⇒ τs ⇝ es ∣ θ ; n ↦ θ' ; n'}}}} elab_error with
      | [] => Ok (existT _ [] (existT _ [] (existT _ θ (exist _ n (ASs_nil E L Γ θ n)))))
      | s :: ss' =>
          '(existT _ τ (existT _ e (existT _ θ1 (exist _ n1 H)))) <- rec s L Γ Syn θ n ;;
          '(existT _ τs (existT _ es (existT _ θ2 (exist _ n2 Hs)))) <- go ss' θ1 n1 ;;
          Ok (existT _ (τ :: τs) (existT _ (e :: es) (existT _ θ2 (exist _ n2
                (ASs_cons E L Γ s ss' τ τs e es θ n θ1 n1 θ2 n2 H Hs)))))
      end.

  Definition achks_dec (rec : infer_t) (p : pos) (L : cenv) (Γ : lctx) :
      forall ss τs θ n, result {es : list expr & {θ' : sub & {n' : nat |
                          Γ ⊩ᵃ*[E;L] ss ⇐ τs ⇝ es ∣ θ ; n ↦ θ' ; n'}}} elab_error :=
    fix go ss τs θ n :=
      match ss as l, τs as l' return result {es : list expr & {θ' : sub & {n' : nat |
                                       Γ ⊩ᵃ*[E;L] l ⇐ l' ⇝ es ∣ θ ; n ↦ θ' ; n'}}} elab_error with
      | [], [] => Ok (existT _ [] (existT _ θ (exist _ n (ACs_nil E L Γ θ n))))
      | s :: ss', τ :: τs' =>
          '(existT _ e (existT _ θ1 (exist _ n1 H))) <- ac (rec s L Γ (Chk τ) θ n) ;;
          '(existT _ es (existT _ θ2 (exist _ n2 Hs))) <- go ss' τs' θ1 n1 ;;
          Ok (existT _ (e :: es) (existT _ θ2 (exist _ n2
                (ACs_cons E L Γ s ss' τ τs' e es θ n θ1 n1 θ2 n2 H Hs))))
      | _, _ => Err (EE_Type p (E_ArgArity (List.length τs) (List.length ss)))
      end.

  Definition abind_dec (rec : infer_t) (L : cenv) (Γ : lctx) (s1 : sexpr) (ann : option sty) (θ : sub) (n : nat) :
      result {τ : ty & {e : expr & {θ' : sub & {n' : nat |
                Γ ⊩ᵃ[E;L] s1 ⦂ ann ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'}}}} elab_error :=
    match ann as a0 return result {τ : ty & {e : expr & {θ' : sub & {n' : nat |
                             Γ ⊩ᵃ[E;L] s1 ⦂ a0 ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'}}}} elab_error with
    | None =>
        '(existT _ τ (existT _ e (existT _ θ' (exist _ n' H)))) <- rec s1 L Γ Syn θ n ;;
        Ok (existT _ τ (existT _ e (existT _ θ' (exist _ n' (AB_Syn E L Γ s1 τ e θ n θ' n' H)))))
    | Some t =>
        '(exist _ τ Ht) <- ety_v t ;;
        '(existT _ e (existT _ θ' (exist _ n' H))) <- ac (rec s1 L Γ (Chk τ) θ n) ;;
        Ok (existT _ τ (existT _ e (existT _ θ' (exist _ n' (AB_Ann E L Γ s1 t τ e θ n θ' n' Ht H)))))
    end.

  (** Literals (not recursive). *)
  Definition alit_syn (p : pos) (L : cenv) (Γ : lctx) (l : slit) (θ : sub) (n : nat) :
      result (aout L Γ (SLit p l) Syn θ n) elab_error :=
    match oview (lit_of l) with
    | inleft (exist _ l' H) => Ok (existT _ _ (existT _ _ (existT _ θ (exist _ n (A_Lit E L Γ p l l' θ n H)))))
    | inright _ => Err (lit_err p l)
    end.

  Lemma cs_lit_false Γ p l τ :
    match l with SLInt None _ => match τ with TBase (BInt _) => False | _ => True end | _ => True end ->
    chk_spec E Γ (SLit p l) τ = false.
  Proof. destruct l as [| |[k|] z| | | |]; simpl; auto; destruct τ as [[]| | | | | | |]; tauto. Qed.

  Lemma cs_lit_int Γ p z τ : (forall k, τ <> TInt k) -> chk_spec E Γ (SLit p (SLInt None z)) τ = false.
  Proof. intros H; destruct τ as [[]| | | | | | |]; simpl; try reflexivity; exfalso; eapply H; reflexivity. Qed.

  Definition alit_m (p : pos) (L : cenv) (Γ : lctx) (l : slit) (m : mode) (θ : sub) (n : nat) :
      result (aout L Γ (SLit p l) m θ n) elab_error :=
    match m as m0 return result (aout L Γ (SLit p l) m0 θ n) elab_error with
    | Syn => alit_syn p L Γ l θ n
    | Chk τ =>
        match l as l0 return result (aout L Γ (SLit p l0) (Chk τ) θ n) elab_error with
        | SLInt None z =>
            match int_view (sapp θ τ) with
            | inleft (exist _ k Ht) =>
                Hz <- bcheck (int_in_range k z) (EE_IntRange p k z) ;;
                aok _ θ n (B_Lit E L Γ p z k τ θ n Ht Hz)
            | inright Hn => afin p L Γ (SLit p (SLInt None z)) τ θ n (cs_lit_int Γ p z (sapp θ τ) Hn)
                                 (alit_syn p L Γ (SLInt None z) θ n)
            end
        | l0 => afin p L Γ (SLit p l0) τ θ n (cs_lit_false Γ p l0 (sapp θ τ) I) (alit_syn p L Γ l0 θ n)
        end
    end.

  Definition syn_ok {L Γ s θ n} (τ : ty) (e : expr) (θ' : sub) (n' : nat)
      (H : Γ ⊩ᵃ[E;L] s ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n') : result (aout L Γ s Syn θ n) elab_error :=
    Ok (existT _ τ (existT _ e (existT _ θ' (exist _ n' H)))).

  (** *** Which constructs check by synthesis *)

  Lemma cs_unary_neg Γ p op a τ : int_lit a = false -> chk_spec E Γ (SUnary p op a) τ = false.
  Proof.
    destruct a; simpl; intros H; try reflexivity.
    match goal with l : slit |- _ => destruct l end; try reflexivity; discriminate.
  Qed.

  Lemma cs_unary_other Γ p op a τ : op <> "-" -> chk_spec E Γ (SUnary p op a) τ = false.
  Proof.
    intros H; destruct a; simpl; try reflexivity.
    match goal with l : slit |- _ => destruct l end; try reflexivity.
    apply String.eqb_neq; exact H.
  Qed.

  Lemma cs_call Γ p f q g args fd τ :
    f = SVar q g -> lookup_local g Γ = None -> lookup_fn hdr g = Some fd ->
    chk_spec E Γ (SApp p f args) τ = false.
  Proof. intros -> Hl Hf; simpl; rewrite Hl, Hf; reflexivity. Qed.

  Lemma cs_builtin Γ p f q g args τ :
    f = SVar q g -> lookup_local g Γ = None -> lookup_fn hdr g = None -> g = "not" \/ g = "ignore" ->
    chk_spec E Γ (SApp p f args) τ = false.
  Proof. intros -> Hl Hf Hg; simpl; rewrite Hl, Hf; destruct Hg as [->| ->]; reflexivity. Qed.

  Lemma cs_callee Γ p f args τ : callee Γ f -> chk_spec E Γ (SApp p f args) τ = false.
  Proof.
    destruct f; simpl; intros H; try contradiction; try reflexivity.
    destruct (lookup_local _ Γ); [reflexivity|contradiction].
  Qed.

  (** *** Rules up to equations *)

  Lemma aneg_lit L Γ p op a q k z τ e θ n θ' n' :
    op = "-" -> a = SLit q (SLInt k z) ->
    Γ ⊩ᵃ[E;L] SLit q (SLInt k (Z.opp z)) ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SUnary p op a ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'.
  Proof. intros -> ->; apply A_NegLit. Qed.

  Lemma aneg_lit_chk L Γ p op a q k z τ e θ n θ' n' :
    op = "-" -> a = SLit q (SLInt k z) ->
    Γ ⊩ᵃ[E;L] SLit q (SLInt k (Z.opp z)) ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SUnary p op a ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n'.
  Proof. intros -> ->; apply B_NegLit. Qed.

  Lemma aneg L Γ p op a τ k a' θ n θ' n' :
    op = "-" -> int_lit a = false -> Γ ⊩ᵃ[E;L] a ⇒ τ ⇝ a' ∣ θ ; n ↦ θ' ; n' -> sapp θ' τ = TInt k ->
    Γ ⊩ᵃ[E;L] SUnary p op a ⇒ TInt k ⇝ EPrim (PIntNeg k) [a'] ∣ θ ; n ↦ θ' ; n'.
  Proof. intros ->; apply A_Neg. Qed.

  Lemma anot L Γ p op a a' θ n θ' n' :
    op = "!" -> Γ ⊩ᵃ[E;L] a ⇐ TBool ⇝ a' ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SUnary p op a ⇒ TBool ⇝ EPrim PBoolNot [a'] ∣ θ ; n ↦ θ' ; n'.
  Proof. intros ->; apply A_Not. Qed.

  Lemma aand L Γ p op a b a' b' θ n θ1 n1 θ2 n2 :
    op = "&&" -> Γ ⊩ᵃ[E;L] a ⇐ TBool ⇝ a' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] b ⇐ TBool ⇝ b' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ[E;L] SInfix p op a b ⇒ TBool ⇝ EIf a' b' e_false ∣ θ ; n ↦ θ2 ; n2.
  Proof. intros ->; apply A_And. Qed.

  Lemma aor L Γ p op a b a' b' θ n θ1 n1 θ2 n2 :
    op = "||" -> Γ ⊩ᵃ[E;L] a ⇐ TBool ⇝ a' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] b ⇐ TBool ⇝ b' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ[E;L] SInfix p op a b ⇒ TBool ⇝ EIf a' e_true b' ∣ θ ; n ↦ θ2 ; n2.
  Proof. intros ->; apply A_Or. Qed.

  Lemma abinr L Γ p op a b τ a' b' e θ n θ1 n1 θ2 n2 :
    (flexible a && negb (flexible b))%bool = true ->
    Γ ⊩ᵃ[E;L] b ⇒ τ ⇝ b' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] a ⇐ τ ⇝ a' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    elab_binop p op (sapp θ2 τ) a' b' = Ok e ->
    Γ ⊩ᵃ[E;L] SInfix p op a b ⇒ binop_res op (sapp θ2 τ) ⇝ e ∣ θ ; n ↦ θ2 ; n2.
  Proof.
    intros Hc; apply andb_prop in Hc as [H1 H2]; apply negb_true_iff in H2; apply A_BinR; auto.
  Qed.

  Lemma aifr L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 :
    (diverges t && negb (diverges f))%bool = true ->
    Γ ⊩ᵃ[E;L] c ⇐ TBool ⇝ c' ∣ θ ; n ↦ θ1 ; n1 ->
    Γ ⊩ᵃ[E;L] f ⇒ τ ⇝ f' ∣ θ1 ; n1 ↦ θ2 ; n2 ->
    Γ ⊩ᵃ[E;L] t ⇐ τ ⇝ t' ∣ θ2 ; n2 ↦ θ3 ; n3 ->
    Γ ⊩ᵃ[E;L] SIf p c t (Some f) ⇒ τ ⇝ EIf c' t' f' ∣ θ ; n ↦ θ3 ; n3.
  Proof.
    intros Hd; apply andb_prop in Hd as [H1 H2]; apply negb_true_iff in H2; apply A_IfR; auto.
  Qed.

  Lemma asyn_app L Γ p f q g args τ e θ n θ' n' :
    f = SVar q g -> Γ ⊩ᵃ[E;L] SApp p (SVar q g) args ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SApp p f args ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'.
  Proof. intros ->; auto. Qed.

  Lemma achk_app L Γ p f q g args τ e θ n θ' n' :
    f = SVar q g -> Γ ⊩ᵃ[E;L] SApp p (SVar q g) args ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
    Γ ⊩ᵃ[E;L] SApp p f args ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n'.
  Proof. intros ->; auto. Qed.

  Lemma abuiltin_name {P : ident -> Prop} g g0 : g = g0 -> P g0 -> P g.
  Proof. intros ->; auto. Qed.

  (** *** Variables *)

  Definition avar (p : pos) (L : cenv) (Γ : lctx) (x : ident) (θ : sub) (n : nat) :
      result (aout L Γ (SVar p x) Syn θ n) elab_error :=
    match oview (lookup_local x Γ) with
    | inleft (exist _ i Hl) =>
        '(exist _ τ Hn) <- of_option (nth_error (ctx_of Γ) i) (EE_Unbound p x) ;;
        match ref_view τ with
        | inleft (exist _ u Hu) =>
            syn_ok u _ θ n (A_VarMut E L Γ p x i u θ n Hl (eq_trans Hn (f_equal Some Hu)))
        | inright Hc => syn_ok τ _ θ n (A_Var E L Γ p x i τ θ n Hl Hn Hc)
        end
    | inright Hl =>
        '(exist _ fd Hf) <- of_option (lookup_fn hdr x) (EE_Unbound p x) ;;
        Hb <- nb_v p x ;;
        syn_ok _ _ θ _ (A_Global E L Γ p x fd θ n Hl Hf Hb)
    end.

  (** The head of a call (without dependent matches on computed terms). *)
  Definition ahead_of (Γ : lctx) (f : sexpr) : head Γ f :=
    match f as f0 return head Γ f0 with
    | SVar q g =>
        match oview (lookup_local g Γ) with
        | inleft (exist _ i H) => HExpr Γ (SVar q g) (some_not_none _ i H)
        | inright H => HName Γ (SVar q g) q g eq_refl H
        end
    | SConstr q tq c => HCtor Γ (SConstr q tq c) q tq c eq_refl
    | SQual q T m => HQual Γ (SQual q T m) q T m eq_refl
    | f0 => HExpr Γ f0 I
    end.

  (** ** The elaborator *)

  Fixpoint infer (s : sexpr) (L : cenv) (Γ : lctx) (m : mode) (θ : sub) (n : nat) {struct s}
      : result (aout L Γ s m θ n) elab_error :=
    match s as s0 return result (aout L Γ s0 m θ n) elab_error with
    | SVar p x => amode p L Γ (SVar p x) m θ n (fun _ => eq_refl) (avar p L Γ x θ n)
    | SLit p l => alit_m p L Γ l m θ n
    | SUnary p op a =>
        match string_dec op "-" with
        | left Hop =>
            match int_lit_dec a with
            | inleft (existT _ q (existT _ k (exist _ z Ha))) =>
                match m as m0 return result (aout L Γ (SUnary p op a) m0 θ n) elab_error with
                | Syn =>
                    '(existT _ τ (existT _ e (existT _ θ' (exist _ n' H)))) <-
                      alit_syn q L Γ (SLInt k (Z.opp z)) θ n ;;
                    syn_ok τ e θ' n' (aneg_lit L Γ p op a q k z τ e θ n θ' n' Hop Ha H)
                | Chk τ =>
                    '(existT _ e (existT _ θ' (exist _ n' H))) <- ac (alit_m q L Γ (SLInt k (Z.opp z)) (Chk τ) θ n) ;;
                    aok e θ' n' (aneg_lit_chk L Γ p op a q k z τ e θ n θ' n' Hop Ha H)
                end
            | inright Hn =>
                amode p L Γ (SUnary p op a) m θ n (fun τ => cs_unary_neg Γ p op a τ Hn)
                  ('(existT _ τ (existT _ a' (existT _ θ' (exist _ n' Ha)))) <- infer a L Γ Syn θ n ;;
                   match int_view (sapp θ' τ) with
                   | inleft (exist _ k Hk) => syn_ok _ _ θ' n' (aneg L Γ p op a τ k a' θ n θ' n' Hop Hn Ha Hk)
                   | inright _ => Err (EE_NoOperator p op (sapp θ' τ))
                   end)
            end
        | right Hne =>
            match string_dec op "!" with
            | left Hop =>
                amode p L Γ (SUnary p op a) m θ n (fun τ => cs_unary_other Γ p op a τ Hne)
                  ('(existT _ a' (existT _ θ' (exist _ n' Ha))) <- ac (infer a L Γ (Chk TBool) θ n) ;;
                   syn_ok _ _ θ' n' (anot L Γ p op a a' θ n θ' n' Hop Ha))
            | right _ => Err (EE_NoOperator p op TUnit)
            end
        end
    | SInfix p op a b =>
        let bin_syn : result (aout L Γ (SInfix p op a b) Syn θ n) elab_error :=
          match string_dec op "&&" with
          | left Hop =>
              '(existT _ a' (existT _ θ1 (exist _ n1 Ha))) <- ac (infer a L Γ (Chk TBool) θ n) ;;
              '(existT _ b' (existT _ θ2 (exist _ n2 Hb))) <- ac (infer b L Γ (Chk TBool) θ1 n1) ;;
              syn_ok _ _ θ2 n2 (aand L Γ p op a b a' b' θ n θ1 n1 θ2 n2 Hop Ha Hb)
          | right _ =>
          match string_dec op "||" with
          | left Hop =>
              '(existT _ a' (existT _ θ1 (exist _ n1 Ha))) <- ac (infer a L Γ (Chk TBool) θ n) ;;
              '(existT _ b' (existT _ θ2 (exist _ n2 Hb))) <- ac (infer b L Γ (Chk TBool) θ1 n1) ;;
              syn_ok _ _ θ2 n2 (aor L Γ p op a b a' b' θ n θ1 n1 θ2 n2 Hop Ha Hb)
          | right _ =>
              match bview (flexible a && negb (flexible b))%bool with
              | right Hc =>
                  '(existT _ τ (existT _ a' (existT _ θ1 (exist _ n1 Ha)))) <- infer a L Γ Syn θ n ;;
                  '(existT _ b' (existT _ θ2 (exist _ n2 Hb))) <- ac (infer b L Γ (Chk τ) θ1 n1) ;;
                  '(exist _ e He) <- binop_v p op (sapp θ2 τ) a' b' ;;
                  syn_ok _ _ θ2 n2 (A_BinL E L Γ p op a b τ a' b' e θ n θ1 n1 θ2 n2 Hc Ha Hb He)
              | left Hc =>
                  '(existT _ τ (existT _ b' (existT _ θ1 (exist _ n1 Hb)))) <- infer b L Γ Syn θ n ;;
                  '(existT _ a' (existT _ θ2 (exist _ n2 Ha))) <- ac (infer a L Γ (Chk τ) θ1 n1) ;;
                  '(exist _ e He) <- binop_v p op (sapp θ2 τ) a' b' ;;
                  syn_ok _ _ θ2 n2 (abinr L Γ p op a b τ a' b' e θ n θ1 n1 θ2 n2 Hc Hb Ha He)
              end
          end
          end in
        match m as m0 return result (aout L Γ (SInfix p op a b) m0 θ n) elab_error with
        | Syn => bin_syn
        | Chk τ =>
            match bview (chk_spec E Γ (SInfix p op a b) (sapp θ τ)) with
            | right Hcs => afin p L Γ (SInfix p op a b) τ θ n Hcs bin_syn
            | left _ =>
                match oview (assoc op arith_ops) with
                | inleft (exist _ o Ho) =>
                    match ty_eq_dec (binop_res op (sapp θ τ)) (sapp θ τ) with
                    | left Hres =>
                        '(existT _ a' (existT _ θ1 (exist _ n1 Ha))) <- ac (infer a L Γ (Chk τ) θ n) ;;
                        '(existT _ b' (existT _ θ2 (exist _ n2 Hb))) <- ac (infer b L Γ (Chk τ) θ1 n1) ;;
                        '(exist _ e He) <- binop_v p op (sapp θ τ) a' b' ;;
                        aok e θ2 n2 (B_Bin E L Γ p op a b τ o a' b' e θ n θ1 n1 θ2 n2 Ho Hres Ha Hb He)
                    | right _ => Err (EE_NoOperator p op (sapp θ τ))
                    end
                | inright _ => Err (EE_NoOperator p op (sapp θ τ))
                end
            end
        end
    | SLet p x ann s1 s2 =>
        '(existT _ τ1 (existT _ e1 (existT _ θ1 (exist _ n1 H1)))) <-
          abind_dec infer L Γ s1 ann θ n ;;
        match m as m0 return result (aout L Γ (SLet p x ann s1 s2) m0 θ n) elab_error with
        | Syn =>
            '(existT _ τ (existT _ e2 (existT _ θ2 (exist _ n2 H2)))) <- infer s2 L ((x, τ1) :: Γ) Syn θ1 n1 ;;
            syn_ok _ _ θ2 n2 (A_Let E L Γ p x ann s1 s2 τ1 τ e1 e2 θ n θ1 n1 θ2 n2 H1 H2)
        | Chk τ =>
            '(existT _ e2 (existT _ θ2 (exist _ n2 H2))) <- ac (infer s2 L ((x, τ1) :: Γ) (Chk τ) θ1 n1) ;;
            aok _ θ2 n2 (B_Let E L Γ p x ann s1 s2 τ1 τ e1 e2 θ n θ1 n1 θ2 n2 H1 H2)
        end
    | SAnnot p s0 t =>
        amode p L Γ (SAnnot p s0 t) m θ n (fun _ => eq_refl)
          ('(exist _ τ Ht) <- ety_v t ;;
           '(existT _ e (existT _ θ' (exist _ n' H))) <- ac (infer s0 L Γ (Chk τ) θ n) ;;
           syn_ok _ _ θ' n' (A_Annot E L Γ p s0 t τ e θ n θ' n' Ht H))
    | SIf p c t oe =>
        match oe as o return result (aout L Γ (SIf p c t o) m θ n) elab_error with
        | None =>
            amode p L Γ (SIf p c t None) m θ n (fun _ => eq_refl)
              ('(existT _ c' (existT _ θ1 (exist _ n1 Hc))) <- ac (infer c L Γ (Chk TBool) θ n) ;;
               '(existT _ t' (existT _ θ2 (exist _ n2 Ht))) <- ac (infer t L Γ (Chk TUnit) θ1 n1) ;;
               syn_ok _ _ θ2 n2 (A_If1 E L Γ p c t c' t' θ n θ1 n1 θ2 n2 Hc Ht))
        | Some f =>
            '(existT _ c' (existT _ θ1 (exist _ n1 Hc))) <- ac (infer c L Γ (Chk TBool) θ n) ;;
            match m as m0 return result (aout L Γ (SIf p c t (Some f)) m0 θ n) elab_error with
            | Chk τ =>
                '(existT _ t' (existT _ θ2 (exist _ n2 Ht))) <- ac (infer t L Γ (Chk τ) θ1 n1) ;;
                '(existT _ f' (existT _ θ3 (exist _ n3 Hf))) <- ac (infer f L Γ (Chk τ) θ2 n2) ;;
                aok _ θ3 n3 (B_If E L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 Hc Ht Hf)
            | Syn =>
                match bview (diverges t && negb (diverges f))%bool with
                | right Hd =>
                    '(existT _ τ (existT _ t' (existT _ θ2 (exist _ n2 Ht)))) <- infer t L Γ Syn θ1 n1 ;;
                    '(existT _ f' (existT _ θ3 (exist _ n3 Hf))) <- ac (infer f L Γ (Chk τ) θ2 n2) ;;
                    syn_ok _ _ θ3 n3 (A_If E L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 Hd Hc Ht Hf)
                | left Hd =>
                    '(existT _ τ (existT _ f' (existT _ θ2 (exist _ n2 Hf)))) <- infer f L Γ Syn θ1 n1 ;;
                    '(existT _ t' (existT _ θ3 (exist _ n3 Ht))) <- ac (infer t L Γ (Chk τ) θ2 n2) ;;
                    syn_ok _ _ θ3 n3 (aifr L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 Hd Hc Hf Ht)
                end
            end
        end
    | STup p ss =>
        let syn_t : result (aout L Γ (STup p ss) Syn θ n) elab_error :=
          '(existT _ τs (existT _ es (existT _ θ' (exist _ n' Hs)))) <- asyns_dec infer L Γ ss θ n ;;
          syn_ok _ _ θ' n' (A_Tuple E L Γ p ss τs es θ n θ' n' Hs) in
        match m as m0 return result (aout L Γ (STup p ss) m0 θ n) elab_error with
        | Syn => syn_t
        | Chk τ =>
            match bview (chk_spec E Γ (STup p ss) (sapp θ τ)) with
            | right Hcs => afin p L Γ (STup p ss) τ θ n Hcs syn_t
            | left _ =>
                match tuple_view (sapp θ τ) with
                | inleft (exist _ ts Ht) =>
                    match Nat.eq_dec (List.length ts) (List.length ss) with
                    | left Hl =>
                        '(existT _ es (existT _ θ' (exist _ n' Hs))) <- achks_dec infer p L Γ ss ts θ n ;;
                        aok _ θ' n' (B_Tuple E L Γ p ss τ ts es θ n θ' n' Ht Hl Hs)
                    | right _ => Err (EE_Annot p (sapp θ τ) (TTuple ts))
                    end
                | inright _ => Err (EE_Annot p (sapp θ τ) (sapp θ τ))
                end
            end
        end
    | SProj p s0 i =>
        amode p L Γ (SProj p s0 i) m θ n (fun _ => eq_refl)
          ('(existT _ τ0 (existT _ e (existT _ θ' (exist _ n' H)))) <- infer s0 L Γ Syn θ n ;;
           match tuple_view (sapp θ' τ0) with
           | inleft (exist _ τs Ht) =>
               '(exist _ τ Hi) <- of_option (nth_error τs i) (EE_Type p (E_TupleIndex i (TTuple τs))) ;;
               syn_ok _ _ θ' n' (A_Proj E L Γ p s0 i τ0 τs τ e θ n θ' n' H Ht Hi)
           | inright _ => Err (EE_Type p (E_NotTuple (sapp θ' τ0)))
           end)
    | SLam p ps ret a body =>
        let syn_l : result (aout L Γ (SLam p ps ret a body) Syn θ n) elab_error :=
          '(exist _ (τs, n1) Hp) <- of_option (aparams E ps n) (EE_LambdaParam p "") ;;
          '(exist _ ε He) <- eff_v a ;;
          match ret as r0 return result (aout L Γ (SLam p ps r0 a body) Syn θ n) elab_error with
          | Some t =>
              '(exist _ r Hr) <- ety_v t ;;
              '(existT _ b (existT _ θ' (exist _ n' Hb))) <-
                ac (infer body (fun_env r ε) (List.app (lam_ctx ps τs) Γ) (Chk r) θ n1) ;;
              syn_ok _ _ θ' n' (A_LamRet E L Γ p ps t a body τs r ε b θ n n1 θ' n' Hp Hr He Hb)
          | None =>
              '(existT _ r (existT _ b (existT _ θ' (exist _ n' Hb)))) <-
                infer body (mk_cenv [] ε) (List.app (lam_ctx ps τs) Γ) Syn θ n1 ;;
              syn_ok _ _ θ' n' (A_Lam E L Γ p ps a body τs r ε b θ n n1 θ' n' Hp He Hb)
          end in
        match m as m0 return result (aout L Γ (SLam p ps ret a body) m0 θ n) elab_error with
        | Syn => syn_l
        | Chk τ =>
            match bview (chk_spec E Γ (SLam p ps ret a body) (sapp θ τ)) with
            | right Hcs => afin p L Γ (SLam p ps ret a body) τ θ n Hcs syn_l
            | left _ =>
                match arrow_view (sapp θ τ) with
                | inleft (existT _ τs (existT _ r (exist _ ε Ht))) =>
                    match Nat.eq_dec (List.length τs) (List.length ps) with
                    | left Hl =>
                        '(exist _ eqs Hfit) <- of_option (fit_lam E ps ret a τs r ε) (EE_LambdaParam p "") ;;
                        '(exist _ θ1 Hun) <- of_option (unify_all E n θ eqs) (EE_Annot p (sapp θ τ) (sapp θ τ)) ;;
                        '(existT _ b (existT _ θ' (exist _ n' Hb))) <-
                          ac (infer body (fun_env r ε) (List.app (lam_ctx ps τs) Γ) (Chk r) θ1 n) ;;
                        aok _ θ' n' (B_Lam E L Γ p ps ret a body τ τs r ε eqs b θ n θ1 θ' n' Ht Hl Hfit Hun Hb)
                    | right _ => Err (EE_Annot p (sapp θ τ) (sapp θ τ))
                    end
                | inright _ => Err (EE_Annot p (sapp θ τ) (sapp θ τ))
                end
            end
        end
    | SApp p f args =>
        match ahead_of Γ f with
        | HName _ _ q g Hf Hl =>
            match oview (lookup_fn hdr g) with
            | inleft (exist _ fd Hfd) =>
                amode p L Γ (SApp p f args) m θ n (fun τ => cs_call Γ p f q g args fd τ Hf Hl Hfd)
                  (Hb <- nb_v q g ;;
                   '(existT _ es (existT _ θ' (exist _ n' Hes))) <-
                     achks_dec infer p L Γ args (map (tsubst (inst (fresh n (fd_tparams fd)))) (fd_params fd))
                               θ (n + fd_tparams fd) ;;
                   Hok <- allowed_dec E p (sapp θ' (tsubst (inst (fresh n (fd_tparams fd))) (fd_eff fd)))
                                      (sapp θ' (ce_exn L)) ;;
                   syn_ok _ _ θ' n' (asyn_app L Γ p f q g args _ _ θ n θ' n' Hf
                                       (A_Call E L Γ p q g args fd es θ n θ' n' Hl Hfd Hb Hes Hok)))
            | inright Hfd =>
                let Hbi : builtin E Γ g := conj Hl Hfd in
                match string_dec g "not", args as a0
                      return result (aout L Γ (SApp p f a0) m θ n) elab_error with
                | left Hg, [a] =>
                    amode p L Γ (SApp p f [a]) m θ n (fun τ => cs_builtin Γ p f q g [a] τ Hf Hl Hfd (or_introl Hg))
                      ('(existT _ a' (existT _ θ' (exist _ n' Ha))) <- ac (infer a L Γ (Chk TBool) θ n) ;;
                       syn_ok _ _ θ' n' (asyn_app L Γ p f q g [a] _ _ θ n θ' n' Hf
                         (abuiltin_name (P := fun g0 => Γ ⊩ᵃ[E;L] SApp p (SVar q g0) [a] ⇒ TBool ⇝ EPrim PBoolNot [a']
                                                          ∣ θ ; n ↦ θ' ; n') g "not" Hg
                            (A_BNot E L Γ p q a a' θ n θ' n' (abuiltin_name (P := builtin E Γ) "not" g (eq_sym Hg) Hbi) Ha))))
                | _, a0 =>
                match string_dec g "ignore", a0 as a1
                      return result (aout L Γ (SApp p f a1) m θ n) elab_error with
                | left Hg, [a] =>
                    amode p L Γ (SApp p f [a]) m θ n (fun τ => cs_builtin Γ p f q g [a] τ Hf Hl Hfd (or_intror Hg))
                      ('(existT _ τ (existT _ a' (existT _ θ' (exist _ n' Ha)))) <- infer a L Γ Syn θ n ;;
                       syn_ok _ _ θ' n' (asyn_app L Γ p f q g [a] _ _ θ n θ' n' Hf
                         (abuiltin_name (P := fun g0 => Γ ⊩ᵃ[E;L] SApp p (SVar q g0) [a] ⇒ TUnit ⇝ ELet a' (ELit LUnit)
                                                          ∣ θ ; n ↦ θ' ; n') g "ignore" Hg
                            (A_Ignore E L Γ p q a τ a' θ n θ' n' (abuiltin_name (P := builtin E Γ) "ignore" g (eq_sym Hg) Hbi) Ha))))
                | _, a1 =>
                match string_dec g "panic", a1 as a2
                      return result (aout L Γ (SApp p f a2) m θ n) elab_error with
                | left Hg, [] =>
                    let Hb := abuiltin_name (P := builtin E Γ) "panic" g (eq_sym Hg) Hbi in
                    match m as m0 return result (aout L Γ (SApp p f []) m0 θ n) elab_error with
                    | Syn => syn_ok _ _ θ n (asyn_app L Γ p f q g [] _ _ θ n θ n Hf
                               (abuiltin_name (P := fun g0 => Γ ⊩ᵃ[E;L] SApp p (SVar q g0) [] ⇒ TUnit ⇝ EAbort TUnit
                                                                ∣ θ ; n ↦ θ ; n) g "panic" Hg
                                  (A_Panic E L Γ p q θ n Hb)))
                    | Chk τ => aok _ θ n (achk_app L Γ p f q g [] _ _ θ n θ n Hf
                               (abuiltin_name (P := fun g0 => Γ ⊩ᵃ[E;L] SApp p (SVar q g0) [] ⇐ τ ⇝ EAbort τ
                                                                ∣ θ ; n ↦ θ ; n) g "panic" Hg
                                  (B_Panic E L Γ p q τ θ n Hb)))
                    end
                | _, a2 =>
                match string_dec g "abort", a2 as a3
                      return result (aout L Γ (SApp p f a3) m θ n) elab_error with
                | left Hg, [a] =>
                    let Hb := abuiltin_name (P := builtin E Γ) "abort" g (eq_sym Hg) Hbi in
                    '(existT _ a' (existT _ θ' (exist _ n' Ha))) <- ac (infer a L Γ (Chk TString) θ n) ;;
                    match m as m0 return result (aout L Γ (SApp p f [a]) m0 θ n) elab_error with
                    | Syn => syn_ok _ _ θ' n' (asyn_app L Γ p f q g [a] _ _ θ n θ' n' Hf
                               (abuiltin_name (P := fun g0 => Γ ⊩ᵃ[E;L] SApp p (SVar q g0) [a] ⇒ TUnit ⇝ ELet a' (EAbort TUnit)
                                                                ∣ θ ; n ↦ θ' ; n') g "abort" Hg
                                  (A_Abort E L Γ p q a a' θ n θ' n' Hb Ha)))
                    | Chk τ => aok _ θ' n' (achk_app L Γ p f q g [a] _ _ θ n θ' n' Hf
                               (abuiltin_name (P := fun g0 => Γ ⊩ᵃ[E;L] SApp p (SVar q g0) [a] ⇐ τ ⇝ ELet a' (EAbort τ)
                                                                ∣ θ ; n ↦ θ' ; n') g "abort" Hg
                                  (B_Abort E L Γ p q a a' τ θ n θ' n' Hb Ha)))
                    end
                | _, _ => Err (EE_Unbound q g)
                end
                end
                end
                end
            end
        | HExpr _ _ Hc =>
            amode p L Γ (SApp p f args) m θ n (fun τ => cs_callee Γ p f args τ Hc)
              ('(existT _ τf (existT _ f' (existT _ θ1 (exist _ n1 Hf)))) <- infer f L Γ Syn θ n ;;
               match arrow_view (sapp θ1 τf) with
               | inleft (existT _ ps (existT _ r (exist _ ε Ht))) =>
                   '(existT _ es (existT _ θ2 (exist _ n2 Hes))) <- achks_dec infer p L Γ args ps θ1 n1 ;;
                   Hok <- allowed_dec E p (sapp θ2 ε) (sapp θ2 (ce_exn L)) ;;
                   syn_ok _ _ θ2 n2 (A_CallExpr E L Γ p f args τf ps r ε f' es θ n θ1 n1 θ2 n2 Hc Hf Ht Hes Hok)
               | inright _ => Err (EE_Type p (E_NotFunction (sapp θ1 τf)))
               end)
        | _ => Err (EE_Unsupported p "not yet in the inference")
        end
    | s0 => Err (EE_Unsupported (sexpr_pos s0) "not yet in the inference")
    end.

End Infer.

(** ** Completeness

    Whenever the algorithmic rules derive something, [infer] succeeds (and,
    the rules being deterministic, with that result). *)

Section Complete.
  Variable E : senv.
  Abbreviation hdr := (se_hdr E).

  (** *** The building blocks succeed when they should *)

  Lemma oview_some {A} (o : option A) a : o = Some a -> exists H, oview o = inleft (exist _ a H).
  Proof. intros ->; eexists; reflexivity. Qed.

  Lemma oview_none {A} (o : option A) : o = None -> exists H, oview o = inright H.
  Proof. intros ->; eexists; reflexivity. Qed.

  Lemma bview_true b : b = true -> exists H, bview b = left H.
  Proof. intros ->; eexists; reflexivity. Qed.

  Lemma bview_false b : b = false -> exists H, bview b = right H.
  Proof. intros ->; eexists; reflexivity. Qed.

  Lemma int_view_some t k : t = TInt k -> exists H, int_view t = inleft (exist _ k H).
  Proof. intros ->; eexists; reflexivity. Qed.

  Lemma tuple_view_some t ts : t = TTuple ts -> exists H, tuple_view t = inleft (exist _ ts H).
  Proof. intros ->; eexists; reflexivity. Qed.

  Lemma arrow_view_some t ps r ε :
    t = TArrow ps r ε -> exists H, arrow_view t = inleft (existT _ ps (existT _ r (exist _ ε H))).
  Proof. intros ->; eexists; reflexivity. Qed.

  Lemma ref_view_some t u : t = TRef u -> exists H, ref_view t = inleft (exist _ u H).
  Proof. intros ->; eexists; reflexivity. Qed.

  Lemma ref_view_none t : is_cell t = false -> exists H, ref_view t = inright H.
  Proof. destruct t; simpl; intros H; try discriminate; eexists; reflexivity. Qed.

  Lemma of_option_ok {A Er} (o : option A) (err : Er) a :
    o = Some a -> exists H, of_option o err = Ok (exist _ a H).
  Proof. intros ->; eexists; reflexivity. Qed.

  Lemma bcheck_ok b err : b = true -> exists H, bcheck b err = Ok H.
  Proof. intros ->; eexists; reflexivity. Qed.

  Lemma ety_v_ok t τ : ety E t = Ok τ -> exists H, ety_v E t = Ok (exist _ τ H).
  Proof.
    intros H; unfold ety_v; destruct (rview (ety E t)) as [[τ' H']|[err H']]; [|congruence].
    assert (τ' = τ) by congruence; subst; eexists; reflexivity.
  Qed.

  Lemma err_dec_ok p T : err_type E T -> exists H, err_dec E p T = Ok H.
  Proof.
    intros (td & Htd & Herr); unfold err_dec.
    destruct (of_option_ok (lookup_ty hdr T) (EE_NotError p (TData T [])) td Htd) as [H1 ->]; simpl.
    destruct (bcheck_ok (td_err td) (EE_NotError p (TData T [])) Herr) as [H2 ->]; simpl.
    eexists; reflexivity.
  Qed.

  Lemma eff_dec_ok p ε ρ : eff_le ε ρ -> exists H, eff_dec p ε ρ = Ok H.
  Proof.
    unfold eff_dec; intros [->| ->].
    - destruct (ty_eq_dec TNever TNever) as [Hn|Hn]; [eexists; reflexivity|congruence].
    - destruct (ty_eq_dec ρ TNever) as [Hn|Hn]; [eexists; reflexivity|].
      destruct (ty_eq_dec ρ ρ) as [Hq|Hq]; [eexists; reflexivity|congruence].
  Qed.

  Lemma allowed_ok p ε ρ : call_allowed E ε ρ -> exists H, allowed_dec E p ε ρ = Ok H.
  Proof.
    unfold allowed_dec.
    destruct ε as [| | | | T [|] | | |], ρ as [| | | | | | |]; simpl; intros H;
      try (apply eff_dec_ok; exact H); apply err_dec_ok; exact H.
  Qed.

  Lemma binop_ok p op τ a b e : elab_binop p op τ a b = Ok e -> exists H, binop_v p op τ a b = Ok (exist _ e H).
  Proof.
    intros H; unfold binop_v; destruct (rview (elab_binop p op τ a b)) as [[e' H']|[err H']]; [|congruence].
    assert (e' = e) by congruence; subst; eexists; reflexivity.
  Qed.

  Lemma eff_syn_ok a ε : eff_syn E a ε -> exists H, eff_v E a = Ok (exist _ ε H).
  Proof.
    destruct a as [[t|]|]; simpl; intros H; try (subst; eexists; reflexivity).
    destruct (ety_v_ok t ε H) as [H' ->]; simpl; eexists; reflexivity.
  Qed.

  Lemma no_bounds_ok p g : sbounds E g = [] -> exists H, nb_v E p g = Ok H.
  Proof. intros H; unfold nb_v; destruct (lview (sbounds E g)) as [H'|H']; [eexists; reflexivity|contradiction]. Qed.

  Lemma acoerce_ok p θ n e τ' τ e' θ' :
    acoerce E θ n e τ' τ e' θ' -> exists H, acoerce_dec E p θ n e τ' τ = Ok (existT _ e' (exist _ θ' H)).
  Proof.
    destruct 1 as [θ n e τ' τ T Hu HT|θ n e τ' τ θ' Hu Hun]; unfold acoerce_dec.
    - destruct (oview_some _ _ Hu) as [H1 ->]; simpl.
      destruct (err_dec_ok p T HT) as [H2 ->]; simpl; eexists; reflexivity.
    - destruct (oview_none _ Hu) as [H1 ->]; simpl.
      destruct (oview_some _ _ Hun) as [H2 ->]; simpl; eexists; reflexivity.
  Qed.
  Lemma afin_ok p L Γ s τ θ n Hcs τ' e θ1 n1 H e' θ2 :
    acoerce E θ1 n1 e τ' τ e' θ2 ->
    exists r, afin E p L Γ s τ θ n Hcs (Ok (existT _ τ' (existT _ e (existT _ θ1 (exist _ n1 H))))) = Ok r.
  Proof.
    intros Hco; unfold afin; simpl.
    destruct (acoerce_ok p _ _ _ _ _ _ _ Hco) as [Hc ->]; simpl; eexists; reflexivity.
  Qed.

  (** The components of an answer (without its proof). *)
  Definition comps {L Γ s m θ n} (r : result (aout E L Γ s m θ n) elab_error) : option (ty * expr * sub * nat) :=
    match r with
    | Ok (existT _ τ (existT _ e (existT _ θ' (exist _ n' _)))) => Some (τ, e, θ', n')
    | Err _ => None
    end.

  (** Checking without a rule of its own goes through the synthesis. *)
  Lemma infer_sub L Γ s τ θ n τ' e θ1 n1 H e' θ2 :
    chk_spec E Γ s (sapp θ τ) = false ->
    infer E s L Γ Syn θ n = Ok (existT _ τ' (existT _ e (existT _ θ1 (exist _ n1 H)))) ->
    acoerce E θ1 n1 e τ' τ e' θ2 ->
    exists r, infer E s L Γ (Chk τ) θ n = Ok r.
  Proof.
    intros Hcs Hs Hco. pose proof (f_equal comps Hs) as Hc; simpl in Hc.
    destruct s; simpl in Hs, Hc |- *;
      repeat first
        [ solve [rewrite Hs; eapply afin_ok; exact Hco]
        | solve [exfalso; simpl in Hcs; discriminate]
        | discriminate Hs
        | discriminate Hc
        | match goal with |- context [bview ?b] =>
            let Hb := fresh "Hb" in destruct (bview b) as [Hb|Hb]; [exfalso; simpl in Hcs; congruence|]
          end
        | match goal with |- context [int_view (sapp ?θ ?τ)] =>
            let Hk := fresh "Hk" in destruct (int_view (sapp θ τ)) as [[? Hk]|Hk];
              [exfalso; rewrite Hk in Hcs; simpl in Hcs; discriminate|]
          end
        | match goal with
          | Hf : ?f = SVar _ _ |- _ =>
              exfalso; subst f; subst; simpl in Hcs;
              repeat match goal with
                     | H : lookup_local _ _ = None |- _ => rewrite H in Hcs
                     | H : lookup_fn _ _ = None |- _ => rewrite H in Hcs
                     end; discriminate
          end
        | match goal with
          | Ho : ?op = "-", Ha : ?a = SLit _ (SLInt _ _) |- _ =>
              exfalso; subst op a; simpl in Hcs; discriminate
          end
        | match goal with |- context [acoerce_dec _ ?p _ _ _ _ _] =>
            injection Hc; intros; subst;
            let Hx := fresh in destruct (acoerce_ok p _ _ _ _ _ _ _ Hco) as [? Hx];
            rewrite Hx; simpl; eexists; reflexivity
          end
        | match goal with
          | |- context [match ?x with _ => _ end] =>
              lazymatch type of Hs with context [match x with _ => _ end] => destruct x end
          end; simpl in Hs, Hc |- *
        | match goal with l : slit |- _ => destruct l; simpl in Hs, Hc |- * end
        | match goal with |- context [match ?x with _ => _ end] => is_var x; destruct x; simpl in Hs, Hc |- * end ].
  Qed.

  Lemma ahead_name Γ q g : lookup_local g Γ = None -> exists H, ahead_of Γ (SVar q g) = HName Γ (SVar q g) q g eq_refl H.
  Proof. intros H; unfold ahead_of; destruct (oview_none _ H) as [H' ->]; eexists; reflexivity. Qed.

  Lemma ahead_expr Γ f : callee Γ f -> exists H, ahead_of Γ f = HExpr Γ f H.
  Proof.
    destruct f; simpl; intros Hc; try contradiction; try (eexists; reflexivity).
    destruct (oview (lookup_local _ Γ)) as [[i Hl]|Hl]; [eexists; reflexivity|contradiction].
  Qed.

  Ltac use_s IH D :=
    let r := fresh "r" in let Hr := fresh "Hr" in
    destruct IH as [r Hr]; rewrite Hr; simpl;
    let τ0 := fresh "τ" in let e0 := fresh "e" in let θ0 := fresh "θ" in
    let n0 := fresh "n" in let H0 := fresh "H" in
    destruct r as [τ0 [e0 [θ0 [n0 H0]]]]; simpl;
    let a := fresh in let b := fresh in let c := fresh in let d := fresh in
    destruct (proj1 (alg_det E) _ _ _ _ _ _ _ _ _ D _ _ _ _ H0) as (a & b & c & d); subst.

  Ltac use_c IH D :=
    let r := fresh "r" in let Hr := fresh "Hr" in
    destruct IH as [r Hr]; rewrite Hr; simpl;
    let τ0 := fresh "τ" in let e0 := fresh "e" in let θ0 := fresh "θ" in
    let n0 := fresh "n" in let Heq := fresh "Heq" in let H0 := fresh "H" in
    destruct r as [τ0 [e0 [θ0 [n0 [Heq H0]]]]]; simpl;
    let b := fresh in let c := fresh in let d := fresh in
    destruct (proj1 (proj2 (alg_det E)) _ _ _ _ _ _ _ _ _ D _ _ _ H0) as (b & c & d); subst.

  Ltac use_b IH D :=
    let r := fresh "r" in let Hr := fresh "Hr" in
    destruct IH as [r Hr]; rewrite Hr; simpl;
    let τ0 := fresh "τ" in let e0 := fresh "e" in let θ0 := fresh "θ" in
    let n0 := fresh "n" in let H0 := fresh "H" in
    destruct r as [τ0 [e0 [θ0 [n0 H0]]]]; simpl;
    let a := fresh in let b := fresh in let c := fresh in let d := fresh in
    destruct (proj1 (proj2 (proj2 (alg_det E))) _ _ _ _ _ _ _ _ _ _ D _ _ _ _ H0) as (a & b & c & d); subst.

  Ltac use_ss IH D :=
    let r := fresh "r" in let Hr := fresh "Hr" in
    destruct IH as [r Hr]; rewrite Hr; simpl;
    let τ0 := fresh "τs" in let e0 := fresh "es" in let θ0 := fresh "θ" in
    let n0 := fresh "n" in let H0 := fresh "H" in
    destruct r as [τ0 [e0 [θ0 [n0 H0]]]]; simpl;
    let a := fresh in let b := fresh in let c := fresh in let d := fresh in
    destruct (proj1 (proj2 (proj2 (proj2 (alg_det E)))) _ _ _ _ _ _ _ _ _ D _ _ _ _ H0) as (a & b & c & d); subst.

  Ltac use_cs IH D :=
    match goal with |- context [achks_dec E (infer E) ?p _ _ _ _ _ _] =>
      let r := fresh "r" in let Hr := fresh "Hr" in
      destruct (IH p) as [r Hr]; rewrite Hr; simpl;
      let e0 := fresh "es" in let θ0 := fresh "θ" in let n0 := fresh "n" in let H0 := fresh "H" in
      destruct r as [e0 [θ0 [n0 H0]]]; simpl;
      let b := fresh in let c := fresh in let d := fresh in
      destruct (proj2 (proj2 (proj2 (proj2 (alg_det E)))) _ _ _ _ _ _ _ _ _ D _ _ _ H0) as (b & c & d); subst
    end.

  Ltac done_ := eexists; reflexivity.

  Ltac oview_left H :=
    match goal with |- context [oview ?x] =>
      let a := fresh in let Ha := fresh in let Ht := fresh in
      destruct (oview x) as [[a Ha]|Ha]; [simpl | exfalso; pose proof H as Ht; simpl in Ht; congruence]
    end.

  Ltac bview_left H :=
    match goal with |- context [bview ?b] =>
      let Hb := fresh in let Ht := fresh in
      destruct (bview b) as [Hb|Hb]; [simpl | exfalso; pose proof H as Ht; simpl in Ht; congruence]
    end.

  Theorem infer_complete :
    (forall L Γ s θ n τ e θ' n', Γ ⊩ᵃ[E;L] s ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
       exists r, infer E s L Γ Syn θ n = Ok r) /\
    (forall L Γ s τ θ n e θ' n', Γ ⊩ᵃ[E;L] s ⇐ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
       exists r, infer E s L Γ (Chk τ) θ n = Ok r) /\
    (forall L Γ s a θ n τ e θ' n', Γ ⊩ᵃ[E;L] s ⦂ a ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
       exists r, abind_dec E (infer E) L Γ s a θ n = Ok r) /\
    (forall L Γ ss θ n τs es θ' n', Γ ⊩ᵃ*[E;L] ss ⇒ τs ⇝ es ∣ θ ; n ↦ θ' ; n' ->
       exists r, asyns_dec E (infer E) L Γ ss θ n = Ok r) /\
    (forall L Γ ss τs θ n es θ' n', Γ ⊩ᵃ*[E;L] ss ⇐ τs ⇝ es ∣ θ ; n ↦ θ' ; n' ->
       forall p, exists r, achks_dec E (infer E) p L Γ ss τs θ n = Ok r).
  Proof.
    apply alg_mutind.
    - (* A_Var *) intros L Γ p x i τ θ n Hl Hn Hc; simpl; unfold avar.
      destruct (oview_some _ _ Hl) as [? ->]; simpl.
      destruct (of_option_ok _ (EE_Unbound p x) _ Hn) as [? ->]; simpl.
      destruct (ref_view_none _ Hc) as [? ->]; done_.
    - (* A_VarMut *) intros L Γ p x i τ θ n Hl Hn; simpl; unfold avar.
      destruct (oview_some _ _ Hl) as [? ->]; simpl.
      destruct (of_option_ok _ (EE_Unbound p x) _ Hn) as [? ->]; simpl.
      done_.
    - (* A_Global *) intros L Γ p x fd θ n Hl Hf Hsb; simpl; unfold avar.
      destruct (oview_none _ Hl) as [? ->]; simpl.
      destruct (of_option_ok _ (EE_Unbound p x) _ Hf) as [? ->]; simpl.
      destruct (no_bounds_ok p x Hsb) as [? ->]; done_.
    - (* A_Lit *) intros L Γ p l l' θ n Hl; simpl; unfold alit_syn.
      destruct (oview_some _ _ Hl) as [? ->]; done_.
    - (* A_NegLit *) intros L Γ p q k z τ e θ n θ' n' D IH; simpl in IH |- *.
      use_s IH D; done_.
    - (* A_Neg *) intros L Γ p a τ k a' θ n θ' n' Hia D IH Hk; simpl.
      destruct (int_lit_dec a) as [[q [k' [z Ha]]]|Hn]; [subst; discriminate|]; simpl.
      use_s IH D. destruct (int_view_some _ _ Hk) as [? ->]; done_.
    - (* A_Not *) intros L Γ p a a' θ n θ' n' D IH; simpl. use_c IH D; done_.
    - (* A_And *) intros L Γ p a b a' b' θ n θ1 n1 θ2 n2 D1 IH1 D2 IH2; simpl.
      use_c IH1 D1; use_c IH2 D2; done_.
    - (* A_Or *) intros L Γ p a b a' b' θ n θ1 n1 θ2 n2 D1 IH1 D2 IH2; simpl.
      use_c IH1 D1; use_c IH2 D2; done_.
    - (* A_BinL *) intros L Γ p op a b τ a' b' e θ n θ1 n1 θ2 n2 Hfl D1 IH1 D2 IH2 Hb; simpl.
      destruct (string_dec op "&&") as [->|Hne1]; [exfalso; eapply binop_and; eauto|].
      destruct (string_dec op "||") as [->|Hne2]; [exfalso; eapply binop_or; eauto|].
      destruct (bview_false _ Hfl) as [? ->]; simpl.
      use_s IH1 D1; use_c IH2 D2. destruct (binop_ok _ _ _ _ _ _ Hb) as [? ->]; done_.
    - (* A_BinR *) intros L Γ p op a b τ a' b' e θ n θ1 n1 θ2 n2 Hfa Hfb D1 IH1 D2 IH2 Hb; simpl.
      destruct (string_dec op "&&") as [->|Hne1]; [exfalso; eapply binop_and; eauto|].
      destruct (string_dec op "||") as [->|Hne2]; [exfalso; eapply binop_or; eauto|].
      assert (Hc : (flexible a && negb (flexible b))%bool = true) by (rewrite Hfa, Hfb; reflexivity).
      destruct (bview_true _ Hc) as [? ->]; simpl.
      use_s IH1 D1; use_c IH2 D2. destruct (binop_ok _ _ _ _ _ _ Hb) as [? ->]; done_.
    - (* A_Let *) intros L Γ p x a s1 s2 τ1 τ e1 e2 θ n θ1 n1 θ2 n2 D1 IH1 D2 IH2; simpl.
      use_b IH1 D1; use_s IH2 D2; done_.
    - (* A_Annot *) intros L Γ p s t τ e θ n θ' n' Ht D IH; simpl.
      destruct (ety_v_ok t τ Ht) as [? ->]; simpl. use_c IH D; done_.
    - (* A_If *) intros L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 Hd D1 IH1 D2 IH2 D3 IH3; simpl.
      use_c IH1 D1. destruct (bview_false _ Hd) as [? ->]; simpl.
      use_s IH2 D2; use_c IH3 D3; done_.
    - (* A_IfR *) intros L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 Hdt Hdf D1 IH1 D2 IH2 D3 IH3; simpl.
      use_c IH1 D1.
      assert (Hd : (diverges t && negb (diverges f))%bool = true) by (rewrite Hdt, Hdf; reflexivity).
      destruct (bview_true _ Hd) as [? ->]; simpl.
      use_s IH2 D2; use_c IH3 D3; done_.
    - (* A_If1 *) intros L Γ p c t c' t' θ n θ1 n1 θ2 n2 D1 IH1 D2 IH2; simpl.
      use_c IH1 D1; use_c IH2 D2; done_.
    - (* A_Tuple *) intros L Γ p ss τs es θ n θ' n' D IH; simpl. use_ss IH D; done_.
    - (* A_Proj *) intros L Γ p s i τ0 τs τ e θ n θ' n' D IH Hτ Hi; simpl.
      use_s IH D. destruct (tuple_view_some _ _ Hτ) as [? ->]; simpl.
      destruct (of_option_ok _ (EE_Type p (E_TupleIndex i (TTuple τs))) _ Hi) as [? ->]; done_.
    - (* A_LamRet *) intros L Γ p ps t a body τs r ε b θ n n1 θ' n' Hp Ht He D IH; simpl.
      destruct (of_option_ok _ (EE_LambdaParam p "") _ Hp) as [? ->]; simpl.
      destruct (eff_syn_ok a ε He) as [? ->]; simpl.
      destruct (ety_v_ok t r Ht) as [? ->]; simpl. use_c IH D; done_.
    - (* A_Lam *) intros L Γ p ps a body τs r ε b θ n n1 θ' n' Hp He D IH; simpl.
      destruct (of_option_ok _ (EE_LambdaParam p "") _ Hp) as [? ->]; simpl.
      destruct (eff_syn_ok a ε He) as [? ->]; simpl. use_s IH D; done_.
    - (* A_Call *) intros L Γ p q g args fd es θ n θ' n' Hl Hf Hsb D IH Hca; simpl.
      first [destruct (ahead_name Γ q g Hl) as [? ->] | destruct (oview_none _ Hl) as [? ->]]; simpl.
      destruct (oview_some _ _ Hf) as [? ->]; simpl.
      destruct (no_bounds_ok q g Hsb) as [? ->]; simpl.
      use_cs IH D. destruct (allowed_ok p _ _ Hca) as [? ->]; done_.
    - (* A_CallExpr *) intros L Γ p f args τf ps r ε f' es θ n θ1 n1 θ2 n2 Hc D1 IH1 Hτ D2 IH2 Hca; simpl.
      destruct (ahead_expr Γ f Hc) as [? ->]; simpl.
      use_s IH1 D1. destruct (arrow_view_some _ _ _ _ Hτ) as [? ->]; simpl.
      use_cs IH2 D2. destruct (allowed_ok p _ _ Hca) as [? ->]; done_.
    - (* A_BNot *) intros L Γ p q a a' θ n θ' n' [Hl Hf] D IH; simpl.
      first [destruct (ahead_name Γ q "not" Hl) as [? ->] | destruct (oview_none _ Hl) as [? ->]]; simpl.
      destruct (oview_none _ Hf) as [? ->]; simpl. use_c IH D; done_.
    - (* A_Ignore *) intros L Γ p q a τ a' θ n θ' n' [Hl Hf] D IH; simpl.
      first [destruct (ahead_name Γ q "ignore" Hl) as [? ->] | destruct (oview_none _ Hl) as [? ->]]; simpl.
      destruct (oview_none _ Hf) as [? ->]; simpl. use_s IH D; done_.
    - (* A_Panic *) intros L Γ p q θ n [Hl Hf]; simpl.
      first [destruct (ahead_name Γ q "panic" Hl) as [? ->] | destruct (oview_none _ Hl) as [? ->]]; simpl.
      destruct (oview_none _ Hf) as [? ->]; simpl; done_.
    - (* A_Abort *) intros L Γ p q a a' θ n θ' n' [Hl Hf] D IH; simpl.
      first [destruct (ahead_name Γ q "abort" Hl) as [? ->] | destruct (oview_none _ Hl) as [? ->]]; simpl.
      destruct (oview_none _ Hf) as [? ->]; simpl. use_c IH D; done_.
    - (* B_Sub *) intros L Γ s τ τ' e e' θ n θ1 n1 θ2 Hcs D IH Hco.
      destruct IH as [[τ0 [e0 [θ0 [n0 H0]]]] Hr].
      destruct (proj1 (alg_det E) _ _ _ _ _ _ _ _ _ D _ _ _ _ H0) as (? & ? & ? & ?); subst.
      eapply infer_sub; eauto.
    - (* B_Lit *) intros L Γ p z k τ θ n Hτ Hz; simpl.
      destruct (int_view_some _ _ Hτ) as [? ->]; simpl.
      destruct (bcheck_ok _ (EE_IntRange p k z) Hz) as [? ->]; done_.
    - (* B_NegLit *) intros L Γ p q k z τ e θ n θ' n' D IH; simpl in IH |- *.
      use_c IH D; done_.
    - (* B_Bin *) intros L Γ p op a b τ o a' b' e θ n θ1 n1 θ2 n2 Ho Hres D1 IH1 D2 IH2 Hb; simpl.
      destruct (string_dec op "&&") as [->|Hne1]; [discriminate|].
      destruct (string_dec op "||") as [->|Hne2]; [discriminate|].
      bview_left (cs_bin E Γ p op a b _ o Ho Hres).
      oview_left Ho.
      destruct (ty_eq_dec (binop_res op (sapp θ τ)) (sapp θ τ)) as [Hr|Hr]; [|contradiction]; simpl.
      use_c IH1 D1; use_c IH2 D2. destruct (binop_ok _ _ _ _ _ _ Hb) as [? ->]; done_.
    - (* B_Let *) intros L Γ p x a s1 s2 τ1 τ e1 e2 θ n θ1 n1 θ2 n2 D1 IH1 D2 IH2; simpl.
      use_b IH1 D1; use_c IH2 D2; done_.
    - (* B_If *) intros L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 D1 IH1 D2 IH2 D3 IH3; simpl.
      use_c IH1 D1; use_c IH2 D2; use_c IH3 D3; done_.
    - (* B_Tuple *) intros L Γ p ss τ ts es θ n θ' n' Hτ Hl D IH; simpl.
      bview_left (cs_tuple E Γ p ss _ ts Hτ Hl).
      destruct (tuple_view_some _ _ Hτ) as [? ->]; simpl.
      destruct (Nat.eq_dec (List.length ts) (List.length ss)) as [Hl'|Hl']; [|contradiction]; simpl.
      use_cs IH D; done_.
    - (* B_Lam *) intros L Γ p ps ret a body τ τs r ε eqs b θ n θ1 θ' n' Hτ Hl Hfit Hun D IH; simpl.
      bview_left (cs_lam E Γ p ps ret a body _ τs r ε Hτ Hl).
      destruct (arrow_view_some _ _ _ _ Hτ) as [? ->]; simpl.
      destruct (Nat.eq_dec (List.length τs) (List.length ps)) as [Hl'|Hl']; [|contradiction]; simpl.
      destruct (of_option_ok _ (EE_LambdaParam p "") _ Hfit) as [? ->]; simpl.
      destruct (of_option_ok _ (EE_Annot p (sapp θ τ) (sapp θ τ)) _ Hun) as [? ->]; simpl.
      use_c IH D; done_.
    - (* B_Panic *) intros L Γ p q τ θ n [Hl Hf]; simpl.
      first [destruct (ahead_name Γ q "panic" Hl) as [? ->] | destruct (oview_none _ Hl) as [? ->]]; simpl.
      destruct (oview_none _ Hf) as [? ->]; simpl; done_.
    - (* B_Abort *) intros L Γ p q a a' τ θ n θ' n' [Hl Hf] D IH; simpl.
      first [destruct (ahead_name Γ q "abort" Hl) as [? ->] | destruct (oview_none _ Hl) as [? ->]]; simpl.
      destruct (oview_none _ Hf) as [? ->]; simpl. use_c IH D; done_.
    - (* AB_Syn *) intros L Γ s τ e θ n θ' n' D IH; simpl. use_s IH D; done_.
    - (* AB_Ann *) intros L Γ s t τ e θ n θ' n' Ht D IH; simpl.
      destruct (ety_v_ok t τ Ht) as [? ->]; simpl. use_c IH D; done_.
    - (* ASs_nil *) intros L Γ θ n; done_.
    - (* ASs_cons *) intros L Γ s ss τ τs e es θ n θ1 n1 θ2 n2 D1 IH1 D2 IH2; simpl.
      use_s IH1 D1; use_ss IH2 D2; done_.
    - (* ACs_nil *) intros L Γ θ n p; done_.
    - (* ACs_cons *) intros L Γ s ss τ τs e es θ n θ1 n1 θ2 n2 D1 IH1 D2 IH2 p; simpl.
      use_c IH1 D1; use_cs IH2 D2; done_.
  Qed.

  (** Decidability: the algorithmic judgment holds exactly when [infer]
      succeeds, and then with the result of [infer] (by [alg_det]). *)
  Corollary infer_iff L Γ s θ n :
    (exists τ e θ' n', Γ ⊩ᵃ[E;L] s ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n') <->
    (exists r, infer E s L Γ Syn θ n = Ok r).
  Proof.
    split.
    - intros (τ & e & θ' & n' & D); exact (proj1 infer_complete _ _ _ _ _ _ _ _ _ D).
    - intros [[τ [e [θ' [n' D]]]] _]; exists τ, e, θ', n'; exact D.
  Qed.

  Corollary infer_result L Γ s θ n τ e θ' n' :
    Γ ⊩ᵃ[E;L] s ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n' ->
    exists r, infer E s L Γ Syn θ n = Ok r /\ comps (Ok r) = Some (τ, e, θ', n').
  Proof.
    intros D; destruct (proj1 infer_complete _ _ _ _ _ _ _ _ _ D) as [r Hr].
    exists r; split; [exact Hr|].
    destruct r as [τ0 [e0 [θ0 [n0 H0]]]].
    destruct (proj1 (alg_det E) _ _ _ _ _ _ _ _ _ D _ _ _ _ H0) as (-> & -> & -> & ->); reflexivity.
  Qed.
End Complete.

(** ** At the top of a definition

    The metavariables still unsolved at the end default to [Unit]. *)
Definition dflt (nt : nat) (k : nat) : ty := if Nat.ltb k nt then TVar k else TUnit.

Definition close (nt : nat) (θ : sub) (i : nat) : ty := tsubst (dflt nt) (look θ i).

Definition infer_top (E : senv) (s : sexpr) : result (ty * expr) elab_error :=
  '(existT _ τ (existT _ e (existT _ θ (exist _ _ _)))) <- infer E s (mk_cenv [] TNever) [] Syn [] (ntp E) ;;
  Ok (tsubst (close (ntp E) θ) τ, esubst_ty (close (ntp E) θ) e).
