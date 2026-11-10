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

  Abbreviation infer_t :=
    (forall (s : sexpr) (L : cenv) (Γ : lctx) (m : mode) (θ : sub) (n : nat),
        result (aout L Γ s m θ n) elab_error).

  (** ** Building blocks *)

  Definition acoerce_dec (p : pos) (θ : sub) (n : nat) (e : expr) (τ' τ : ty) :
      result {e' : expr & {θ' : sub | acoerce E θ n e τ' τ e' θ'}} elab_error :=
    match up_case (sapp θ τ') (sapp θ τ) as u
          return up_case (sapp θ τ') (sapp θ τ) = u -> result {e' : expr & {θ' : sub | acoerce E θ n e τ' τ e' θ'}} elab_error with
    | Some T => fun Hu =>
        H <- err_dec E p T ;;
        Ok (existT _ (EUp T e) (exist _ θ (ACo_Up E θ n e τ' τ T Hu H)))
    | None => fun Hu =>
        match unify_all E n θ [(τ', τ)] as o
              return unify_all E n θ [(τ', τ)] = o -> result {e' : expr & {θ' : sub | acoerce E θ n e τ' τ e' θ'}} elab_error with
        | Some θ' => fun Hun => Ok (existT _ e (exist _ θ' (ACo_Unify E θ n e τ' τ θ' Hu Hun)))
        | None => fun _ => Err (EE_Annot p (sapp θ τ) (sapp θ τ'))
        end eq_refl
    end eq_refl.

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

  (** Literals (not recursive). *)
  Definition alit_syn (p : pos) (L : cenv) (Γ : lctx) (l : slit) (θ : sub) (n : nat) :
      result (aout L Γ (SLit p l) Syn θ n) elab_error :=
    match lit_of l as o return lit_of l = o -> result (aout L Γ (SLit p l) Syn θ n) elab_error with
    | Some l' => fun H => Ok (existT _ _ (existT _ _ (existT _ θ (exist _ n (A_Lit E L Γ p l l' θ n H)))))
    | None => fun _ => Err (lit_err p l)
    end eq_refl.

  Lemma cs_lit_false Γ p l τ :
    match l with SLInt None _ => match τ with TBase (BInt _) => False | _ => True end | _ => True end ->
    chk_spec E Γ (SLit p l) τ = false.
  Proof. destruct l as [| |[k|] z| | | |]; simpl; auto; destruct τ as [[]| | | | | | |]; tauto. Qed.

  Definition alit_m (p : pos) (L : cenv) (Γ : lctx) (l : slit) (m : mode) (θ : sub) (n : nat) :
      result (aout L Γ (SLit p l) m θ n) elab_error :=
    match m as m0 return result (aout L Γ (SLit p l) m0 θ n) elab_error with
    | Syn => alit_syn p L Γ l θ n
    | Chk τ =>
        match l as l0 return result (aout L Γ (SLit p l0) (Chk τ) θ n) elab_error with
        | SLInt None z =>
            match sapp θ τ as t return sapp θ τ = t -> result (aout L Γ (SLit p (SLInt None z)) (Chk τ) θ n) elab_error with
            | TBase (BInt k) => fun Ht =>
                Hz <- bcheck (int_in_range k z) (EE_IntRange p k z) ;;
                aok _ θ n (B_Lit E L Γ p z k τ θ n Ht Hz)
            | t => fun Ht => afin p L Γ (SLit p (SLInt None z)) τ θ n
                               (cs_lit_false Γ p (SLInt None z) (sapp θ τ)
                                  (@eq_ind_r ty t (fun u => match u with TBase (BInt _) => False | _ => True end)
                                             I (sapp θ τ) Ht))
                               (alit_syn p L Γ (SLInt None z) θ n)
            end eq_refl
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
    match lookup_local x Γ as o return lookup_local x Γ = o -> result (aout L Γ (SVar p x) Syn θ n) elab_error with
    | Some i => fun Hl =>
        '(exist _ τ Hn) <- of_option (nth_error (ctx_of Γ) i) (EE_Unbound p x) ;;
        match τ as t return nth_error (ctx_of Γ) i = Some t -> result (aout L Γ (SVar p x) Syn θ n) elab_error with
        | TRef u => fun Hn => syn_ok u _ θ n (A_VarMut E L Γ p x i u θ n Hl Hn)
        | t => fun Hn => syn_ok t _ θ n (A_Var E L Γ p x i t θ n Hl Hn eq_refl)
        end Hn
    | None => fun Hl =>
        '(exist _ fd Hf) <- of_option (lookup_fn hdr x) (EE_Unbound p x) ;;
        Hb <- no_bounds E p x ;;
        syn_ok _ _ θ _ (A_Global E L Γ p x fd θ n Hl Hf Hb)
    end eq_refl.

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
                   match sapp θ' τ as t return sapp θ' τ = t -> result (aout L Γ (SUnary p op a) Syn θ n) elab_error with
                   | TBase (BInt k) => fun Hk => syn_ok _ _ θ' n' (aneg L Γ p op a τ k a' θ n θ' n' Hop Hn Ha Hk)
                   | t => fun _ => Err (EE_NoOperator p op t)
                   end eq_refl)
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
              match (flexible a && negb (flexible b))%bool as c
                    return (flexible a && negb (flexible b))%bool = c ->
                           result (aout L Γ (SInfix p op a b) Syn θ n) elab_error with
              | false => fun Hc =>
                  '(existT _ τ (existT _ a' (existT _ θ1 (exist _ n1 Ha)))) <- infer a L Γ Syn θ n ;;
                  '(existT _ b' (existT _ θ2 (exist _ n2 Hb))) <- ac (infer b L Γ (Chk τ) θ1 n1) ;;
                  '(exist _ e He) <- binop_dec p op (sapp θ2 τ) a' b' ;;
                  syn_ok _ _ θ2 n2 (A_BinL E L Γ p op a b τ a' b' e θ n θ1 n1 θ2 n2 Hc Ha Hb He)
              | true => fun Hc =>
                  '(existT _ τ (existT _ b' (existT _ θ1 (exist _ n1 Hb)))) <- infer b L Γ Syn θ n ;;
                  '(existT _ a' (existT _ θ2 (exist _ n2 Ha))) <- ac (infer a L Γ (Chk τ) θ1 n1) ;;
                  '(exist _ e He) <- binop_dec p op (sapp θ2 τ) a' b' ;;
                  syn_ok _ _ θ2 n2 (abinr L Γ p op a b τ a' b' e θ n θ1 n1 θ2 n2 Hc Hb Ha He)
              end eq_refl
          end
          end in
        match m as m0 return result (aout L Γ (SInfix p op a b) m0 θ n) elab_error with
        | Syn => bin_syn
        | Chk τ =>
            match chk_spec E Γ (SInfix p op a b) (sapp θ τ) as c
                  return chk_spec E Γ (SInfix p op a b) (sapp θ τ) = c ->
                         result (aout L Γ (SInfix p op a b) (Chk τ) θ n) elab_error with
            | false => fun Hcs => afin p L Γ (SInfix p op a b) τ θ n Hcs bin_syn
            | true => fun _ =>
                match assoc op arith_ops as o
                      return assoc op arith_ops = o -> result (aout L Γ (SInfix p op a b) (Chk τ) θ n) elab_error with
                | Some o => fun Ho =>
                    match ty_eq_dec (binop_res op (sapp θ τ)) (sapp θ τ) with
                    | left Hres =>
                        '(existT _ a' (existT _ θ1 (exist _ n1 Ha))) <- ac (infer a L Γ (Chk τ) θ n) ;;
                        '(existT _ b' (existT _ θ2 (exist _ n2 Hb))) <- ac (infer b L Γ (Chk τ) θ1 n1) ;;
                        '(exist _ e He) <- binop_dec p op (sapp θ τ) a' b' ;;
                        aok e θ2 n2 (B_Bin E L Γ p op a b τ o a' b' e θ n θ1 n1 θ2 n2 Ho Hres Ha Hb He)
                    | right _ => Err (EE_NoOperator p op (sapp θ τ))
                    end
                | None => fun _ => Err (EE_NoOperator p op (sapp θ τ))
                end eq_refl
            end eq_refl
        end
    | SLet p x ann s1 s2 =>
        '(existT _ τ1 (existT _ e1 (existT _ θ1 (exist _ n1 H1)))) <-
          (match ann as a0 return result {τ : ty & {e : expr & {θ' : sub & {n' : nat |
                                    Γ ⊩ᵃ[E;L] s1 ⦂ a0 ⇒ τ ⇝ e ∣ θ ; n ↦ θ' ; n'}}}} elab_error with
           | None =>
               '(existT _ τ (existT _ e (existT _ θ' (exist _ n' H)))) <- infer s1 L Γ Syn θ n ;;
               Ok (existT _ τ (existT _ e (existT _ θ' (exist _ n' (AB_Syn E L Γ s1 τ e θ n θ' n' H)))))
           | Some t =>
               '(exist _ τ Ht) <- ety_dec E t ;;
               '(existT _ e (existT _ θ' (exist _ n' H))) <- ac (infer s1 L Γ (Chk τ) θ n) ;;
               Ok (existT _ τ (existT _ e (existT _ θ' (exist _ n' (AB_Ann E L Γ s1 t τ e θ n θ' n' Ht H)))))
           end) ;;
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
          ('(exist _ τ Ht) <- ety_dec E t ;;
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
                match (diverges t && negb (diverges f))%bool as d
                      return (diverges t && negb (diverges f))%bool = d ->
                             result (aout L Γ (SIf p c t (Some f)) Syn θ n) elab_error with
                | false => fun Hd =>
                    '(existT _ τ (existT _ t' (existT _ θ2 (exist _ n2 Ht)))) <- infer t L Γ Syn θ1 n1 ;;
                    '(existT _ f' (existT _ θ3 (exist _ n3 Hf))) <- ac (infer f L Γ (Chk τ) θ2 n2) ;;
                    syn_ok _ _ θ3 n3 (A_If E L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 Hd Hc Ht Hf)
                | true => fun Hd =>
                    '(existT _ τ (existT _ f' (existT _ θ2 (exist _ n2 Hf)))) <- infer f L Γ Syn θ1 n1 ;;
                    '(existT _ t' (existT _ θ3 (exist _ n3 Ht))) <- ac (infer t L Γ (Chk τ) θ2 n2) ;;
                    syn_ok _ _ θ3 n3 (aifr L Γ p c t f τ c' t' f' θ n θ1 n1 θ2 n2 θ3 n3 Hd Hc Hf Ht)
                end eq_refl
            end
        end
    | STup p ss =>
        let syn_t : result (aout L Γ (STup p ss) Syn θ n) elab_error :=
          '(existT _ τs (existT _ es (existT _ θ' (exist _ n' Hs)))) <- asyns_dec infer L Γ ss θ n ;;
          syn_ok _ _ θ' n' (A_Tuple E L Γ p ss τs es θ n θ' n' Hs) in
        match m as m0 return result (aout L Γ (STup p ss) m0 θ n) elab_error with
        | Syn => syn_t
        | Chk τ =>
            match chk_spec E Γ (STup p ss) (sapp θ τ) as c
                  return chk_spec E Γ (STup p ss) (sapp θ τ) = c -> result (aout L Γ (STup p ss) (Chk τ) θ n) elab_error with
            | false => fun Hcs => afin p L Γ (STup p ss) τ θ n Hcs syn_t
            | true => fun _ =>
                match sapp θ τ as t0 return sapp θ τ = t0 -> result (aout L Γ (STup p ss) (Chk τ) θ n) elab_error with
                | TTuple ts => fun Ht =>
                    match Nat.eq_dec (List.length ts) (List.length ss) with
                    | left Hl =>
                        '(existT _ es (existT _ θ' (exist _ n' Hs))) <- achks_dec infer p L Γ ss ts θ n ;;
                        aok _ θ' n' (B_Tuple E L Γ p ss τ ts es θ n θ' n' Ht Hl Hs)
                    | right _ => Err (EE_Annot p (sapp θ τ) (TTuple ts))
                    end
                | t0 => fun _ => Err (EE_Annot p t0 t0)
                end eq_refl
            end eq_refl
        end
    | SProj p s0 i =>
        amode p L Γ (SProj p s0 i) m θ n (fun _ => eq_refl)
          ('(existT _ τ0 (existT _ e (existT _ θ' (exist _ n' H)))) <- infer s0 L Γ Syn θ n ;;
           match sapp θ' τ0 as t return sapp θ' τ0 = t -> result (aout L Γ (SProj p s0 i) Syn θ n) elab_error with
           | TTuple τs => fun Ht =>
               '(exist _ τ Hi) <- of_option (nth_error τs i) (EE_Type p (E_TupleIndex i (TTuple τs))) ;;
               syn_ok _ _ θ' n' (A_Proj E L Γ p s0 i τ0 τs τ e θ n θ' n' H Ht Hi)
           | t => fun _ => Err (EE_Type p (E_NotTuple t))
           end eq_refl)
    | SLam p ps ret a body =>
        let syn_l : result (aout L Γ (SLam p ps ret a body) Syn θ n) elab_error :=
          '(exist _ (τs, n1) Hp) <- of_option (aparams E ps n) (EE_LambdaParam p "") ;;
          '(exist _ ε He) <- eff_syn_dec E a ;;
          match ret as r0 return result (aout L Γ (SLam p ps r0 a body) Syn θ n) elab_error with
          | Some t =>
              '(exist _ r Hr) <- ety_dec E t ;;
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
            match chk_spec E Γ (SLam p ps ret a body) (sapp θ τ) as c
                  return chk_spec E Γ (SLam p ps ret a body) (sapp θ τ) = c ->
                         result (aout L Γ (SLam p ps ret a body) (Chk τ) θ n) elab_error with
            | false => fun Hcs => afin p L Γ (SLam p ps ret a body) τ θ n Hcs syn_l
            | true => fun _ =>
                match sapp θ τ as t0 return sapp θ τ = t0 -> result (aout L Γ (SLam p ps ret a body) (Chk τ) θ n) elab_error with
                | TArrow τs r ε => fun Ht =>
                    match Nat.eq_dec (List.length τs) (List.length ps) with
                    | left Hl =>
                        '(exist _ eqs Hfit) <- of_option (fit_lam E ps ret a τs r ε) (EE_LambdaParam p "") ;;
                        '(exist _ θ1 Hun) <- of_option (unify_all E n θ eqs) (EE_Annot p (sapp θ τ) (sapp θ τ)) ;;
                        '(existT _ b (existT _ θ' (exist _ n' Hb))) <-
                          ac (infer body (fun_env r ε) (List.app (lam_ctx ps τs) Γ) (Chk r) θ1 n) ;;
                        aok _ θ' n' (B_Lam E L Γ p ps ret a body τ τs r ε eqs b θ n θ1 θ' n' Ht Hl Hfit Hun Hb)
                    | right _ => Err (EE_Annot p (sapp θ τ) (sapp θ τ))
                    end
                | t0 => fun _ => Err (EE_Annot p t0 t0)
                end eq_refl
            end eq_refl
        end
    | SApp p f args =>
        match head_of Γ f with
        | HName _ _ q g Hf Hl =>
            match lookup_fn hdr g as o return lookup_fn hdr g = o -> result (aout L Γ (SApp p f args) m θ n) elab_error with
            | Some fd => fun Hfd =>
                amode p L Γ (SApp p f args) m θ n (fun τ => cs_call Γ p f q g args fd τ Hf Hl Hfd)
                  (Hb <- no_bounds E q g ;;
                   '(existT _ es (existT _ θ' (exist _ n' Hes))) <-
                     achks_dec infer p L Γ args (map (tsubst (inst (fresh n (fd_tparams fd)))) (fd_params fd))
                               θ (n + fd_tparams fd) ;;
                   Hok <- allowed_dec E p (sapp θ' (tsubst (inst (fresh n (fd_tparams fd))) (fd_eff fd)))
                                      (sapp θ' (ce_exn L)) ;;
                   syn_ok _ _ θ' n' (asyn_app L Γ p f q g args _ _ θ n θ' n' Hf
                                       (A_Call E L Γ p q g args fd es θ n θ' n' Hl Hfd Hb Hes Hok)))
            | None => fun Hfd =>
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
            end eq_refl
        | HExpr _ _ Hc =>
            amode p L Γ (SApp p f args) m θ n (fun τ => cs_callee Γ p f args τ Hc)
              ('(existT _ τf (existT _ f' (existT _ θ1 (exist _ n1 Hf)))) <- infer f L Γ Syn θ n ;;
               match sapp θ1 τf as t return sapp θ1 τf = t -> result (aout L Γ (SApp p f args) Syn θ n) elab_error with
               | TArrow ps r ε => fun Ht =>
                   '(existT _ es (existT _ θ2 (exist _ n2 Hes))) <- achks_dec infer p L Γ args ps θ1 n1 ;;
                   Hok <- allowed_dec E p (sapp θ2 ε) (sapp θ2 (ce_exn L)) ;;
                   syn_ok _ _ θ2 n2 (A_CallExpr E L Γ p f args τf ps r ε f' es θ n θ1 n1 θ2 n2 Hc Hf Ht Hes Hok)
               | t => fun _ => Err (EE_Type p (E_NotFunction t))
               end eq_refl)
        | _ => Err (EE_Unsupported p "not yet in the inference")
        end
    | s0 => Err (EE_Unsupported (sexpr_pos s0) "not yet in the inference")
    end.

End Infer.

(** ** At the top of a definition

    The metavariables still unsolved at the end default to [Unit]. *)
Definition dflt (nt : nat) (k : nat) : ty := if Nat.ltb k nt then TVar k else TUnit.

Definition close (nt : nat) (θ : sub) (i : nat) : ty := tsubst (dflt nt) (look θ i).

Definition infer_top (E : senv) (s : sexpr) : result (ty * expr) elab_error :=
  '(existT _ τ (existT _ e (existT _ θ (exist _ _ _)))) <- infer E s (mk_cenv [] TNever) [] Syn [] (ntp E) ;;
  Ok (tsubst (close (ntp E) θ) τ, esubst_ty (close (ntp E) θ) e).
