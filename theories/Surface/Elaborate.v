(** * Surface: the certified elaborator (milestone M6)

    [elab s L Γ m] elaborates the surface expression [s] in mode [m]
    (synthesis, or checking against a type) and returns the Core
    expression together with a derivation of the rules of [ElabSpec.v]:
    the elaborator is sound by construction.

    The type arguments of a generic call are found as in the preliminary
    elaborator: the expected result type and the types of the arguments
    are matched against the signature, and lambdas whose parameter types
    are not yet known are elaborated last.  This search is not trusted:
    the arguments are finally checked against the instantiated parameter
    types, and only then is a derivation built.

    Recursion is structural on the surface expression; list helpers take
    the elaborator as an argument and are unfolded by the guard checker. *)

From Stdlib Require Import List ZArith String Bool Arith.
From MoonRocq.Prelude Require Import Result EqDec Ident ListDec.
From MoonRocq.Core Require Import Syntax Prim Subst Typing Check.
From MoonRocq.Surface Require Import Syntax Base ElabSpec.
Import ListNotations.

Local Open Scope string_scope.

Inductive mode : Type := Syn | Chk (τ : ty).

Definition hint (m : mode) : option ty := match m with Syn => None | Chk τ => Some τ end.

Definition bcheck (b : bool) (err : elab_error) : result (b = true) elab_error :=
  match b as b' return result (b' = true) elab_error with
  | true => Ok eq_refl
  | false => Err err
  end.

(** A lambda whose parameter types must come from the context. *)
Definition postpone (s : sexpr) : bool :=
  match s with
  | SLam _ ps _ _ _ => existsb (fun xa => match snd xa with None => true | Some _ => false end) ps
  | _ => false
  end.

Definition int_lit_dec (a : sexpr) :
    {q : pos & {k : option int_kind & {z : Z | a = SLit q (SLInt k z)}}} + {int_lit a = false} :=
  match a as a0 return {q : pos & {k : option int_kind & {z : Z | a0 = SLit q (SLInt k z)}}}
                       + {int_lit a0 = false} with
  | SLit q (SLInt k z) => inleft (existT _ q (existT _ k (exist _ z eq_refl)))
  | _ => inright eq_refl
  end.

Lemma some_not_none {A} (o : option A) a : o = Some a -> o <> None.
Proof. intros -> H; discriminate. Qed.

Lemma cons_proj {A : Type} {P : A -> Type} (x : sigT P) rs s ss :
  map (@projT1 _ _) (x :: rs) = s :: ss -> projT1 x = s /\ map (@projT1 _ _) rs = ss.
Proof. simpl; intros H; injection H; auto. Qed.

Section Elaborate.
  Variable E : senv.
  Abbreviation hdr := (se_hdr E).

  Definition sout (L : cenv) (Γ : lctx) (s : sexpr) : Type :=
    {τ : ty & {e : expr | Γ ⊩[E;L] s ⇒ τ ⇝ e}}.
  Definition cout (L : cenv) (Γ : lctx) (s : sexpr) (τ : ty) : Type :=
    {e : expr | Γ ⊩[E;L] s ⇐ τ ⇝ e}.
  Definition out (L : cenv) (Γ : lctx) (s : sexpr) (m : mode) : Type :=
    match m with
    | Syn => sout L Γ s
    | Chk τ => cout L Γ s τ
    end.

  (** ** Building blocks *)

  Definition ety_dec (t : sty) : result {τ | ety E t = Ok τ} elab_error :=
    match ety E t as r return ety E t = r -> result {τ | ety E t = Ok τ} elab_error with
    | Ok τ => fun H => Ok (exist _ τ H)
    | Err err => fun _ => Err err
    end eq_refl.

  Definition err_dec (p : pos) (T : ident) : result (err_type E T) elab_error :=
    '(exist _ td Htd) <- of_option (lookup_ty hdr T) (EE_NotError p (TData T [])) ;;
    Hb <- bcheck (td_err td) (EE_NotError p (TData T [])) ;;
    Ok (ex_intro _ td (conj Htd Hb)).

  Definition eff_dec (p : pos) (ε ρ : ty) : result (eff_le ε ρ) elab_error :=
    match ty_eq_dec ε TNever with
    | left H => Ok (or_introl H)
    | right _ =>
        match ty_eq_dec ε ρ with
        | left H => Ok (or_intror H)
        | right _ => Err (EE_Type p (E_Effect ε ρ))
        end
    end.

  Definition allowed_dec (p : pos) (ε ρ : ty) : result (call_allowed E ε ρ) elab_error :=
    match ε as ε0, ρ as ρ0 return result (call_allowed E ε0 ρ0) elab_error with
    | TData T [], TError => err_dec p T
    | ε0, ρ0 => eff_dec p ε0 ρ0
    end.

  (** Implicit conversion of [e : τ'] to [τ]. *)
  Definition coerce (p : pos) (e : expr) (τ' τ : ty) :
      result {e' | ⊩ᶜ[E] e : τ' ≼ τ ⇝ e'} elab_error :=
    match ty_eq_dec τ' τ with
    | left H => Ok (exist _ e (eq_ind τ' (fun t => ⊩ᶜ[E] e : τ' ≼ t ⇝ e) (Co_Refl E e τ') τ H))
    | right _ =>
        match τ' as t1, τ as t2 return result {e' | ⊩ᶜ[E] e : t1 ≼ t2 ⇝ e'} elab_error with
        | TData T [], TError =>
            H <- err_dec p T ;;
            Ok (exist _ (EUp T e) (Co_Up E e T H))
        | t1, t2 => Err (EE_Annot p t2 t1)
        end
    end.

  (** The answer in mode [m], from a synthesis: check by subsumption. *)
  Definition fin (p : pos) (L : cenv) (Γ : lctx) (s : sexpr) (m : mode)
      (r : result (sout L Γ s) elab_error) : result (out L Γ s m) elab_error :=
    match m as m0 return result (out L Γ s m0) elab_error with
    | Syn => r
    | Chk τ =>
        '(existT _ τ' (exist _ e H)) <- r ;;
        '(exist _ e' Hc) <- coerce p e τ' τ ;;
        Ok (exist _ e' (C_Sub E L Γ s τ' τ e e' H Hc))
    end.

  Definition binop_dec (p : pos) (op : ident) (τ : ty) (a b : expr) :
      result {e | elab_binop p op τ a b = Ok e} elab_error :=
    match elab_binop p op τ a b as r
          return elab_binop p op τ a b = r -> result {e | elab_binop p op τ a b = Ok e} elab_error with
    | Ok e => fun H => Ok (exist _ e H)
    | Err err => fun _ => Err err
    end eq_refl.

  Definition fn_targs (p : pos) (g : ident) (fd : fdef) (st : list (option ty)) :
      result {ts | List.length ts = fd_tparams fd} elab_error :=
    match all_some st with
    | Some ts =>
        match Nat.eq_dec (List.length ts) (fd_tparams fd) with
        | left H => Ok (exist _ ts H)
        | right _ => Err (EE_CannotInfer p g)
        end
    | None => Err (EE_CannotInfer p g)
    end.

  Definition no_bounds (p : pos) (g : ident) : result (sbounds E g = []) elab_error :=
    match sbounds E g as b return result (b = []) elab_error with
    | [] => Ok eq_refl
    | _ => Err (EE_Unsupported p "a function with trait bounds")
    end.

  (** *** Lambdas *)

  Fixpoint params_ann_dec (p : pos) (ps : list (ident * option sty)) (exps : list (option ty)) :
      result {τs | params_ann E ps τs} elab_error :=
    match ps as ps0 return result {τs | params_ann E ps0 τs} elab_error with
    | [] => Ok (exist _ [] (Forall2_nil _))
    | (x, a) :: ps' =>
        '(exist _ τ Hτ) <-
          (match a as a0 return result {τ | ann_ok E a0 τ} elab_error with
           | Some t => '(exist _ τ H) <- ety_dec t ;; Ok (exist _ τ H)
           | None =>
               match hd_error exps with
               | Some (Some τ) => Ok (exist _ τ I)
               | _ => Err (EE_LambdaParam p x)
               end
           end) ;;
        '(exist _ τs Hs) <- params_ann_dec p ps' (tl exps) ;;
        Ok (exist _ (τ :: τs) (Forall2_cons (x, a) τ Hτ Hs))
    end.

  Fixpoint params_syn_dec (p : pos) (ps : list (ident * option sty)) :
      result {τs | params_syn E ps τs} elab_error :=
    match ps as ps0 return result {τs | params_syn E ps0 τs} elab_error with
    | [] => Ok (exist _ [] (Forall2_nil _))
    | (x, a) :: ps' =>
        '(exist _ τ Hτ) <-
          (match a as a0 return result {τ | exists t, a0 = Some t /\ ety E t = Ok τ} elab_error with
           | Some t => '(exist _ τ H) <- ety_dec t ;; Ok (exist _ τ (ex_intro _ t (conj eq_refl H)))
           | None => Err (EE_LambdaParam p x)
           end) ;;
        '(exist _ τs Hs) <- params_syn_dec p ps' ;;
        Ok (exist _ (τ :: τs) (Forall2_cons (x, a) τ Hτ Hs))
    end.

  (** Check that the parameters fit the expected types [τs]. *)
  Fixpoint params_fit (p : pos) (ps : list (ident * option sty)) (τs : list ty) :
      result (params_ann E ps τs) elab_error :=
    match ps as ps0, τs as τs0 return result (params_ann E ps0 τs0) elab_error with
    | [], [] => Ok (Forall2_nil _)
    | (x, a) :: ps', τ :: τs' =>
        H <- (match a as a0 return result (ann_ok E a0 τ) elab_error with
              | Some t =>
                  '(exist _ τ' Ht) <- ety_dec t ;;
                  match ty_eq_dec τ' τ with
                  | left Heq => Ok (eq_ind τ' (fun u => ety E t = Ok u) Ht τ Heq)
                  | right _ => Err (EE_Annot p τ τ')
                  end
              | None => Ok I
              end) ;;
        Hs <- params_fit p ps' τs' ;;
        Ok (Forall2_cons (x, a) τ H Hs)
    | _, _ => Err (EE_Type p (E_ArgArity (List.length τs) (List.length ps)))
    end.

  Definition ann_fit (p : pos) (a : option sty) (τ : ty) : result (ann_ok E a τ) elab_error :=
    match a as a0 return result (ann_ok E a0 τ) elab_error with
    | Some t =>
        '(exist _ τ' Ht) <- ety_dec t ;;
        match ty_eq_dec τ' τ with
        | left Heq => Ok (eq_ind τ' (fun u => ety E t = Ok u) Ht τ Heq)
        | right _ => Err (EE_Annot p τ τ')
        end
    | None => Ok I
    end.

  Definition eff_fit (p : pos) (a : option (option sty)) (ε : ty) : result (eff_ann E a ε) elab_error :=
    match a as a0 return result (eff_ann E a0 ε) elab_error with
    | None => Ok I
    | Some None =>
        match ty_eq_dec ε TNever with
        | left H => Ok H
        | right _ => Err (EE_Annot p TNever ε)
        end
    | Some (Some t) => ann_fit p (Some t) ε
    end.

  (** The effect of a lambda: annotation, else expectation, else [noraise]. *)
  Definition eff_pick (a : option (option sty)) (exp : option ty) :
      result {ε | eff_ann E a ε} elab_error :=
    match a as a0 return result {ε | eff_ann E a0 ε} elab_error with
    | None => Ok (exist _ (match exp with Some ε => ε | None => TNever end) I)
    | Some None => Ok (exist _ TNever eq_refl)
    | Some (Some t) => '(exist _ ε H) <- ety_dec t ;; Ok (exist _ ε H)
    end.

  Definition eff_syn_dec (a : option (option sty)) : result {ε | eff_syn E a ε} elab_error :=
    match a as a0 return result {ε | eff_syn E a0 ε} elab_error with
    | None => Ok (exist _ TNever eq_refl)
    | Some None => Ok (exist _ TNever eq_refl)
    | Some (Some t) => '(exist _ ε H) <- ety_dec t ;; Ok (exist _ ε H)
    end.

  (** *** Lists *)

  Definition chk_list (p : pos) (L : cenv) (Γ : lctx)
      (f : forall s τ, result (cout L Γ s τ) elab_error) :
      forall ss τs, result {es | Γ ⊩*[E;L] ss ⇐ τs ⇝ es} elab_error :=
    fix go ss τs :=
      match ss as ss0, τs as τs0 return result {es | Γ ⊩*[E;L] ss0 ⇐ τs0 ⇝ es} elab_error with
      | [], [] => Ok (exist _ [] (Cs_nil E L Γ))
      | s :: ss', τ :: τs' =>
          '(exist _ e H) <- f s τ ;;
          '(exist _ es Hs) <- go ss' τs' ;;
          Ok (exist _ (e :: es) (Cs_cons E L Γ s ss' τ τs' e es H Hs))
      | _, _ => Err (EE_Type p (E_ArgArity (List.length τs) (List.length ss)))
      end.

  Definition syn_list (L : cenv) (Γ : lctx) (f : forall s, result (sout L Γ s) elab_error) :
      forall ss, result {τs & {es | Γ ⊩*[E;L] ss ⇒ τs ⇝ es}} elab_error :=
    fix go ss :=
      match ss as ss0 return result {τs & {es | Γ ⊩*[E;L] ss0 ⇒ τs ⇝ es}} elab_error with
      | [] => Ok (existT _ [] (exist _ [] (Ss_nil E L Γ)))
      | s :: ss' =>
          '(existT _ τ (exist _ e H)) <- f s ;;
          '(existT _ τs (exist _ es Hs)) <- go ss' ;;
          Ok (existT _ (τ :: τs) (exist _ (e :: es) (Ss_cons E L Γ s ss' τ τs e es H Hs)))
      end.

  (** *** Generic calls

      Each argument is first checked (when its parameter type is already
      known), synthesized, or postponed ([ahd]); then the postponed
      lambdas are elaborated; finally every argument is checked against
      the instantiated parameter type. *)

  Inductive ahd (L : cenv) (Γ : lctx) (s : sexpr) : Type :=
  | AH_Chk (t : ty) (e : expr) (H : Γ ⊩[E;L] s ⇐ t ⇝ e)
  | AH_Syn (t : ty) (e : expr) (H : Γ ⊩[E;L] s ⇒ t ⇝ e)
  | AH_Post.

  Arguments AH_Chk {L Γ s}.
  Arguments AH_Syn {L Γ s}.
  Arguments AH_Post {L Γ s}.

  Definition ares (L : cenv) (Γ : lctx) (args : list sexpr) : Type :=
    {rs : list {s : sexpr & ahd L Γ s} | map (@projT1 _ _) rs = args}.

  Abbreviation elab_ty_t :=
    (forall (s : sexpr) (L : cenv) (Γ : lctx) (m : mode), result (out L Γ s m) elab_error).

  Definition is_none {A} (o : option A) : bool := match o with None => true | Some _ => false end.

  Definition split_hd (ps : list ty) : option ty * list ty :=
    match ps with [] => (None, []) | t :: ts => (Some t, ts) end.

  Definition pass1 (rec : elab_ty_t) (L : cenv) (Γ : lctx) :
      forall (args : list sexpr) (ps : list ty) (st : list (option ty)),
      result (ares L Γ args * list (option ty)) elab_error :=
    fix go args ps st :=
      match args as a0 return result (ares L Γ a0 * list (option ty)) elab_error with
      | [] => Ok (exist _ [] eq_refl, st)
      | s :: args' =>
          let (pt, ps') := split_hd ps in
          let ex := match pt with Some t => resolve st t | None => None end in
          '(h, st1) <-
            (if (postpone s && is_none ex)%bool then Ok (AH_Post, st)
             else
               match ex with
               | Some t => '(exist _ e H) <- rec s L Γ (Chk t) ;; Ok (AH_Chk t e H, st)
               | None =>
                   '(existT _ t (exist _ e H)) <- rec s L Γ Syn ;;
                   Ok (AH_Syn t e H, match pt with Some q => tmatch q t st | None => st end)
               end) ;;
          '(exist _ rs Hrs, st2) <- go args' ps' st1 ;;
          Ok (exist _ (existT _ s h :: rs) (f_equal (cons s) Hrs), st2)
      end.

  Lemma chk_cast L Γ s s' t τ e : s = s' -> t = τ -> Γ ⊩[E;L] s ⇐ t ⇝ e -> Γ ⊩[E;L] s' ⇐ τ ⇝ e.
  Proof. intros -> ->; auto. Qed.

  Lemma syn_cast L Γ s s' t e : s = s' -> Γ ⊩[E;L] s ⇒ t ⇝ e -> Γ ⊩[E;L] s' ⇒ t ⇝ e.
  Proof. intros ->; auto. Qed.

  Definition ahd_cast {L Γ s s'} (H : s = s') (h : ahd L Γ s) : ahd L Γ s' :=
    match h with
    | AH_Chk t e Hc => AH_Chk t e (chk_cast L Γ s s' t t e H eq_refl Hc)
    | AH_Syn t e Hs => AH_Syn t e (syn_cast L Γ s s' t e H Hs)
    | AH_Post => AH_Post
    end.

  (** A postponed lambda, with what the other arguments taught us about
      its type [pt]. *)
  Definition late_lam (rec : elab_ty_t) (L : cenv) (Γ : lctx) (pt : option ty)
      (st : list (option ty)) (s : sexpr) : result (ahd L Γ s * list (option ty)) elab_error :=
    let learn t := match pt with Some q => tmatch q t st | None => st end in
    match match pt with Some q => resolve st q | None => None end with
    | Some t => '(exist _ e H) <- rec s L Γ (Chk t) ;; Ok (AH_Chk t e H, st)
    | None =>
        match s as s0 return s0 = s -> result (ahd L Γ s * list (option ty)) elab_error with
        | SLam q lps ret a body => fun Heq =>
            let '(pexps, rexp, εexp) :=
              match pt with
              | Some (TArrow pps pr pε) =>
                  (if Nat.eqb (List.length pps) (List.length lps) then map (resolve st) pps
                   else repeat None (List.length lps),
                   resolve st pr, resolve st pε)
              | _ => (repeat None (List.length lps), None, None)
              end in
            '(exist _ τs Hps) <- params_ann_dec q lps pexps ;;
            '(exist _ ε Hε) <- eff_pick a εexp ;;
            let Γ' := List.app (lam_ctx lps τs) Γ in
            '(h, st') <-
              (match ret as r0, rexp
                     return result (ahd L Γ (SLam q lps r0 a body) * list (option ty)) elab_error with
               | None, None =>
                   '(existT _ r (exist _ b Hb)) <- rec body (mk_cenv [] ε) Γ' Syn ;;
                   Ok (AH_Chk (TArrow τs r ε) (ELam τs r ε b)
                              (C_LamSyn E L Γ q lps a body τs r ε b Hps Hε Hb),
                       learn (TArrow τs r ε))
               | r0, rx =>
                   '(exist _ r Hr) <-
                     (match r0 as r1 return result {r | ann_ok E r1 r} elab_error with
                      | Some t => '(exist _ r H) <- ety_dec t ;; Ok (exist _ r H)
                      | None =>
                          match rx with
                          | Some r => Ok (exist _ r I)
                          | None => Err (EE_LambdaParam q "result")
                          end
                      end) ;;
                   '(exist _ b Hb) <- rec body (fun_env r ε) Γ' (Chk r) ;;
                   Ok (AH_Chk (TArrow τs r ε) (ELam τs r ε (eblock r b))
                              (C_Lam E L Γ q lps r0 a body τs r ε b Hps Hr Hε Hb),
                       learn (TArrow τs r ε))
               end) ;;
            Ok (ahd_cast Heq h, st')
        | _ => fun _ =>
            '(existT _ t (exist _ e H)) <- rec s L Γ Syn ;;
            Ok (AH_Syn t e H, learn t)
        end eq_refl
    end.

  Definition pass2 (rec : elab_ty_t) (L : cenv) (Γ : lctx) :
      forall (args : list sexpr) (rs : list {s : sexpr & ahd L Γ s}),
      map (@projT1 _ _) rs = args -> list ty -> list (option ty) ->
      result (ares L Γ args * list (option ty)) elab_error :=
    fix go args :=
      match args as a0 return forall rs, map (@projT1 _ _) rs = a0 -> list ty -> list (option ty) ->
                              result (ares L Γ a0 * list (option ty)) elab_error with
      | [] => fun _ _ _ st => Ok (exist _ [] eq_refl, st)
      | s :: args' => fun rs =>
          match rs as rs0 return map (@projT1 _ _) rs0 = s :: args' -> list ty -> list (option ty) ->
                                 result (ares L Γ (s :: args') * list (option ty)) elab_error with
          | [] => fun H _ _ => match nil_cons H with end
          | x :: rs' => fun Hrs ps st =>
              let (pt, ps') := split_hd ps in
              let Hc := cons_proj x rs' s args' Hrs in
              match x as x0 return projT1 x0 = s -> result (ares L Γ (s :: args') * list (option ty)) elab_error with
              | existT _ s0 AH_Post => fun _ =>
                  '(h, st1) <- late_lam rec L Γ pt st s ;;
                  '(exist _ rs2 H2, st2) <- go args' rs' (proj2 Hc) ps' st1 ;;
                  Ok (exist _ (existT _ s h :: rs2) (f_equal (cons s) H2), st2)
              | existT _ s0 h => fun H1 =>
                  '(exist _ rs2 H2, st2) <- go args' rs' (proj2 Hc) ps' st ;;
                  Ok (exist _ (existT _ s0 h :: rs2) (f_equal2 cons H1 H2), st2)
              end (proj1 Hc)
          end
      end.

  (** Check every argument against its instantiated parameter type. *)
  Definition finish (p : pos) (L : cenv) (Γ : lctx) :
      forall (args : list sexpr) (rs : list {s : sexpr & ahd L Γ s}),
      map (@projT1 _ _) rs = args -> forall τs, result {es | Γ ⊩*[E;L] args ⇐ τs ⇝ es} elab_error :=
    fix go args :=
      match args as a0 return forall rs, map (@projT1 _ _) rs = a0 -> forall τs,
                              result {es | Γ ⊩*[E;L] a0 ⇐ τs ⇝ es} elab_error with
      | [] => fun _ _ τs =>
          match τs as t0 return result {es | Γ ⊩*[E;L] [] ⇐ t0 ⇝ es} elab_error with
          | [] => Ok (exist _ [] (Cs_nil E L Γ))
          | _ => Err (EE_Type p (E_ArgArity (List.length τs) 0))
          end
      | s :: args' => fun rs =>
          match rs as rs0 return map (@projT1 _ _) rs0 = s :: args' -> forall τs,
                                 result {es | Γ ⊩*[E;L] s :: args' ⇐ τs ⇝ es} elab_error with
          | [] => fun H _ => match nil_cons H with end
          | x :: rs' => fun Hrs τs =>
              let Hc := cons_proj x rs' s args' Hrs in
              match τs as t0 return result {es | Γ ⊩*[E;L] s :: args' ⇐ t0 ⇝ es} elab_error with
              | [] => Err (EE_Type p (E_ArgArity 0 (List.length args)))
              | τ :: τs' =>
                  '(exist _ e He) <-
                    (match x as x0 return projT1 x0 = s -> result (cout L Γ s τ) elab_error with
                     | existT _ s0 (AH_Chk t e H) => fun Hs =>
                         match ty_eq_dec t τ with
                         | left Ht => Ok (exist _ e (chk_cast L Γ s0 s t τ e Hs Ht H))
                         | right _ => Err (EE_Annot p τ t)
                         end
                     | existT _ s0 (AH_Syn t e H) => fun Hs =>
                         '(exist _ e' Hc') <- coerce p e t τ ;;
                         Ok (exist _ e' (C_Sub E L Γ s t τ e e' (syn_cast L Γ s0 s t e Hs H) Hc'))
                     | existT _ _ AH_Post => fun _ => Err (EE_CannotInfer p "argument")
                     end (proj1 Hc)) ;;
                  '(exist _ es Hes) <- go args' rs' (proj2 Hc) τs' ;;
                  Ok (exist _ (e :: es) (Cs_cons E L Γ s args' τ τs' e es He Hes))
              end
          end
      end.

  (** ** Rules up to equations

      The elaborator decides the shape of a term by computing (e.g.
      [string_dec op "-"]); these lemmas state the rules with the shape
      given as an equation. *)

  Lemma neg_lit_syn L Γ p op a q k z τ e :
    op = "-" -> a = SLit q (SLInt k z) ->
    Γ ⊩[E;L] SLit q (SLInt k (Z.opp z)) ⇒ τ ⇝ e -> Γ ⊩[E;L] SUnary p op a ⇒ τ ⇝ e.
  Proof. intros -> ->; apply S_NegLit. Qed.

  Lemma neg_lit_chk L Γ p op a q k z τ e :
    op = "-" -> a = SLit q (SLInt k z) ->
    Γ ⊩[E;L] SLit q (SLInt k (Z.opp z)) ⇐ τ ⇝ e -> Γ ⊩[E;L] SUnary p op a ⇐ τ ⇝ e.
  Proof. intros -> ->; apply C_NegLit. Qed.

  Lemma neg_syn L Γ p op a k a' :
    op = "-" -> int_lit a = false -> Γ ⊩[E;L] a ⇒ TInt k ⇝ a' ->
    Γ ⊩[E;L] SUnary p op a ⇒ TInt k ⇝ EPrim (PIntNeg k) [a'].
  Proof. intros ->; apply S_Neg. Qed.

  Lemma not_syn L Γ p op a a' :
    op = "!" -> Γ ⊩[E;L] a ⇐ TBool ⇝ a' -> Γ ⊩[E;L] SUnary p op a ⇒ TBool ⇝ EPrim PBoolNot [a'].
  Proof. intros ->; apply S_Not. Qed.

  Lemma and_syn L Γ p op a b a' b' :
    op = "&&" -> Γ ⊩[E;L] a ⇐ TBool ⇝ a' -> Γ ⊩[E;L] b ⇐ TBool ⇝ b' ->
    Γ ⊩[E;L] SInfix p op a b ⇒ TBool ⇝ EIf a' b' e_false.
  Proof. intros ->; apply S_And. Qed.

  Lemma or_syn L Γ p op a b a' b' :
    op = "||" -> Γ ⊩[E;L] a ⇐ TBool ⇝ a' -> Γ ⊩[E;L] b ⇐ TBool ⇝ b' ->
    Γ ⊩[E;L] SInfix p op a b ⇒ TBool ⇝ EIf a' e_true b'.
  Proof. intros ->; apply S_Or. Qed.

  Lemma binr_syn L Γ p op a b τ a' b' e :
    (flexible a && negb (flexible b))%bool = true ->
    Γ ⊩[E;L] b ⇒ τ ⇝ b' -> Γ ⊩[E;L] a ⇐ τ ⇝ a' -> elab_binop p op τ a' b' = Ok e ->
    Γ ⊩[E;L] SInfix p op a b ⇒ binop_res op τ ⇝ e.
  Proof.
    intros H; apply andb_true_iff in H as [H1 H2]; apply negb_true_iff in H2.
    eapply S_BinR; eauto.
  Qed.

  Lemma ifr_syn L Γ p c t f τ c' t' f' :
    (diverges t && negb (diverges f))%bool = true ->
    Γ ⊩[E;L] c ⇐ TBool ⇝ c' -> Γ ⊩[E;L] f ⇒ τ ⇝ f' -> Γ ⊩[E;L] t ⇐ τ ⇝ t' ->
    Γ ⊩[E;L] SIf p c t (Some f) ⇒ τ ⇝ EIf c' t' f'.
  Proof.
    intros H; apply andb_true_iff in H as [H1 H2]; apply negb_true_iff in H2.
    eapply S_IfR; eauto.
  Qed.

  Lemma app_syn L Γ p f q g args τ e :
    f = SVar q g -> Γ ⊩[E;L] SApp p (SVar q g) args ⇒ τ ⇝ e -> Γ ⊩[E;L] SApp p f args ⇒ τ ⇝ e.
  Proof. intros ->; auto. Qed.

  Lemma app_chk L Γ p f q g args τ e :
    f = SVar q g -> Γ ⊩[E;L] SApp p (SVar q g) args ⇐ τ ⇝ e -> Γ ⊩[E;L] SApp p f args ⇐ τ ⇝ e.
  Proof. intros ->; auto. Qed.

  Lemma bnot_syn L Γ p q g a a' :
    g = "not" -> builtin E Γ g -> Γ ⊩[E;L] a ⇐ TBool ⇝ a' ->
    Γ ⊩[E;L] SApp p (SVar q g) [a] ⇒ TBool ⇝ EPrim PBoolNot [a'].
  Proof. intros ->; apply S_BNot. Qed.

  Lemma ignore_syn L Γ p q g a τ a' :
    g = "ignore" -> builtin E Γ g -> Γ ⊩[E;L] a ⇒ τ ⇝ a' ->
    Γ ⊩[E;L] SApp p (SVar q g) [a] ⇒ TUnit ⇝ ELet a' (ELit LUnit).
  Proof. intros ->; apply S_Ignore. Qed.

  Lemma panic_syn L Γ p q g :
    g = "panic" -> builtin E Γ g -> Γ ⊩[E;L] SApp p (SVar q g) [] ⇒ TUnit ⇝ EAbort TUnit.
  Proof. intros ->; apply S_Panic. Qed.

  Lemma panic_chk L Γ p q g τ :
    g = "panic" -> builtin E Γ g -> Γ ⊩[E;L] SApp p (SVar q g) [] ⇐ τ ⇝ EAbort τ.
  Proof. intros ->; apply C_Panic. Qed.

  Lemma abort_syn L Γ p q g a a' :
    g = "abort" -> builtin E Γ g -> Γ ⊩[E;L] a ⇐ TString ⇝ a' ->
    Γ ⊩[E;L] SApp p (SVar q g) [a] ⇒ TUnit ⇝ ELet a' (EAbort TUnit).
  Proof. intros ->; apply S_Abort. Qed.

  Lemma abort_chk L Γ p q g a a' τ :
    g = "abort" -> builtin E Γ g -> Γ ⊩[E;L] a ⇐ TString ⇝ a' ->
    Γ ⊩[E;L] SApp p (SVar q g) [a] ⇐ τ ⇝ ELet a' (EAbort τ).
  Proof. intros ->; apply C_Abort. Qed.

  (** ** Literals and variables *)

  Definition lit_err (p : pos) (l : slit) : elab_error :=
    match l with
    | SLInt ko z => EE_IntRange p (match ko with Some k => k | None => I32 end) z
    | _ => EE_Unsupported p "literal"
    end.

  Definition lit_syn (p : pos) (L : cenv) (Γ : lctx) (l : slit) :
      result (sout L Γ (SLit p l)) elab_error :=
    match lit_of l as o return lit_of l = o -> result (sout L Γ (SLit p l)) elab_error with
    | Some l' => fun H => Ok (existT _ _ (exist _ _ (S_Lit E L Γ p l l' H)))
    | None => fun _ => Err (lit_err p l)
    end eq_refl.

  Definition lit_m (p : pos) (L : cenv) (Γ : lctx) (l : slit) (m : mode) :
      result (out L Γ (SLit p l) m) elab_error :=
    match m as m0 return result (out L Γ (SLit p l) m0) elab_error with
    | Syn => lit_syn p L Γ l
    | Chk τ =>
        match l as l0, τ as t0 return result (out L Γ (SLit p l0) (Chk t0)) elab_error with
        | SLInt None z, TBase (BInt k) =>
            H <- bcheck (int_in_range k z) (EE_IntRange p k z) ;;
            Ok (exist _ _ (C_Lit E L Γ p z k H))
        | l0, t0 => fin p L Γ (SLit p l0) (Chk t0) (lit_syn p L Γ l0)
        end
    end.

  Definition var_syn (p : pos) (L : cenv) (Γ : lctx) (x : ident) (h : option ty) :
      result (sout L Γ (SVar p x)) elab_error :=
    match lookup_local x Γ as o return lookup_local x Γ = o -> result (sout L Γ (SVar p x)) elab_error with
    | Some i => fun Hl =>
        '(exist _ τ Hn) <- of_option (nth_error (ctx_of Γ) i) (EE_Unbound p x) ;;
        match τ as t return nth_error (ctx_of Γ) i = Some t -> result (sout L Γ (SVar p x)) elab_error with
        | TRef u => fun Hn => Ok (existT _ u (exist _ _ (S_VarMut E L Γ p x i u Hl Hn)))
        | t => fun Hn => Ok (existT _ t (exist _ _ (S_Var E L Γ p x i t Hl Hn eq_refl)))
        end Hn
    | None => fun Hl =>
        '(exist _ fd Hf) <- of_option (lookup_fn hdr x) (EE_Unbound p x) ;;
        Hb <- no_bounds p x ;;
        let n := fd_tparams fd in
        '(exist _ ts Hts) <-
          fn_targs p x fd (match h with
                           | Some t => tmatch (TArrow (fd_params fd) (fd_ret fd) (fd_eff fd)) t (repeat None n)
                           | None => repeat None n
                           end) ;;
        Ok (existT _ _ (exist _ _ (S_Global E L Γ p x fd ts Hl Hf Hb Hts)))
    end eq_refl.

  (** ** Heads of calls *)

  Inductive head (Γ : lctx) (f : sexpr) : Type :=
  | HName (q : pos) (g : ident) (Hf : f = SVar q g) (Hl : lookup_local g Γ = None)
  | HExpr (H : callee Γ f)
  | HOther.

  Definition head_of (Γ : lctx) (f : sexpr) : head Γ f :=
    match f as f0 return head Γ f0 with
    | SVar q g =>
        match lookup_local g Γ as o return lookup_local g Γ = o -> head Γ (SVar q g) with
        | None => fun H => HName Γ (SVar q g) q g eq_refl H
        | Some i => fun H => HExpr Γ (SVar q g) (some_not_none _ i H)
        end eq_refl
    | SConstr _ _ _ => HOther Γ _
    | SQual _ _ _ => HOther Γ _
    | f0 => HExpr Γ f0 I
    end.

  (** ** Expressions *)

  Fixpoint elab (s : sexpr) (L : cenv) (Γ : lctx) (m : mode) {struct s}
      : result (out L Γ s m) elab_error :=
    match s as s0 return result (out L Γ s0 m) elab_error with
    | SVar p x => fin p L Γ (SVar p x) m (var_syn p L Γ x (hint m))
    | SLit p l => lit_m p L Γ l m
    | SUnary p op a =>
        match string_dec op "-" with
        | left Hop =>
            match int_lit_dec a with
            | inleft (existT _ q (existT _ k (exist _ z Ha))) =>
                match m as m0 return result (out L Γ (SUnary p op a) m0) elab_error with
                | Syn =>
                    '(existT _ τ (exist _ e H)) <- lit_syn q L Γ (SLInt k (Z.opp z)) ;;
                    Ok (existT _ τ (exist _ e (neg_lit_syn L Γ p op a q k z τ e Hop Ha H)))
                | Chk τ =>
                    '(exist _ e H) <- lit_m q L Γ (SLInt k (Z.opp z)) (Chk τ) ;;
                    Ok (exist _ e (neg_lit_chk L Γ p op a q k z τ e Hop Ha H))
                end
            | inright Hn =>
                fin p L Γ (SUnary p op a) m
                  ('(existT _ τ (exist _ a' Ha)) <- elab a L Γ Syn ;;
                   match τ as t return Γ ⊩[E;L] a ⇒ t ⇝ a' -> result (sout L Γ (SUnary p op a)) elab_error with
                   | TBase (BInt k) => fun Ha =>
                       Ok (existT _ _ (exist _ _ (neg_syn L Γ p op a k a' Hop Hn Ha)))
                   | t => fun _ => Err (EE_NoOperator p op t)
                   end Ha)
            end
        | right _ =>
            match string_dec op "!" with
            | left Hop =>
                fin p L Γ (SUnary p op a) m
                  ('(exist _ a' Ha) <- elab a L Γ (Chk TBool) ;;
                   Ok (existT _ _ (exist _ _ (not_syn L Γ p op a a' Hop Ha))))
            | right _ => Err (EE_NoOperator p op TUnit)
            end
        end
    | SInfix p op a b =>
        match string_dec op "&&" with
        | left Hop =>
            fin p L Γ (SInfix p op a b) m
              ('(exist _ a' Ha) <- elab a L Γ (Chk TBool) ;;
               '(exist _ b' Hb) <- elab b L Γ (Chk TBool) ;;
               Ok (existT _ _ (exist _ _ (and_syn L Γ p op a b a' b' Hop Ha Hb))))
        | right _ =>
        match string_dec op "||" with
        | left Hop =>
            fin p L Γ (SInfix p op a b) m
              ('(exist _ a' Ha) <- elab a L Γ (Chk TBool) ;;
               '(exist _ b' Hb) <- elab b L Γ (Chk TBool) ;;
               Ok (existT _ _ (exist _ _ (or_syn L Γ p op a b a' b' Hop Ha Hb))))
        | right _ =>
            let bin_syn :=
              match (flexible a && negb (flexible b))%bool as c
                    return (flexible a && negb (flexible b))%bool = c ->
                           result (sout L Γ (SInfix p op a b)) elab_error with
              | false => fun Hc =>
                  '(existT _ τ (exist _ a' Ha)) <- elab a L Γ Syn ;;
                  '(exist _ b' Hb) <- elab b L Γ (Chk τ) ;;
                  '(exist _ e He) <- binop_dec p op τ a' b' ;;
                  Ok (existT _ _ (exist _ _ (S_BinL E L Γ p op a b τ a' b' e Hc Ha Hb He)))
              | true => fun Hc =>
                  '(existT _ τ (exist _ b' Hb)) <- elab b L Γ Syn ;;
                  '(exist _ a' Ha) <- elab a L Γ (Chk τ) ;;
                  '(exist _ e He) <- binop_dec p op τ a' b' ;;
                  Ok (existT _ _ (exist _ _ (binr_syn L Γ p op a b τ a' b' e Hc Hb Ha He)))
              end eq_refl in
            match m as m0 return result (out L Γ (SInfix p op a b) m0) elab_error with
            | Syn => bin_syn
            | Chk τ =>
                match assoc op arith_ops, ty_eq_dec (binop_res op τ) τ with
                | Some _, left Hr =>
                    '(exist _ a' Ha) <- elab a L Γ (Chk τ) ;;
                    '(exist _ b' Hb) <- elab b L Γ (Chk τ) ;;
                    '(exist _ e He) <- binop_dec p op τ a' b' ;;
                    Ok (exist _ e (C_Bin E L Γ p op a b τ a' b' e Hr Ha Hb He))
                | _, _ => fin p L Γ (SInfix p op a b) (Chk τ) bin_syn
                end
            end
        end
        end
    | SLet p x ann s1 s2 =>
        '(existT _ τ1 (exist _ e1 H1)) <-
          (match ann as a0 return result {τ & {e | Γ ⊩[E;L] s1 ⦂ a0 ⇒ τ ⇝ e}} elab_error with
           | None =>
               '(existT _ τ (exist _ e H)) <- elab s1 L Γ Syn ;;
               Ok (existT _ τ (exist _ e (B_Syn E L Γ s1 τ e H)))
           | Some t =>
               '(exist _ τ Ht) <- ety_dec t ;;
               '(exist _ e H) <- elab s1 L Γ (Chk τ) ;;
               Ok (existT _ τ (exist _ e (B_Ann E L Γ s1 t τ e Ht H)))
           end) ;;
        match m as m0 return result (out L Γ (SLet p x ann s1 s2) m0) elab_error with
        | Syn =>
            '(existT _ τ (exist _ e2 H2)) <- elab s2 L ((x, τ1) :: Γ) Syn ;;
            Ok (existT _ τ (exist _ _ (S_Let E L Γ p x ann s1 s2 τ1 τ e1 e2 H1 H2)))
        | Chk τ =>
            '(exist _ e2 H2) <- elab s2 L ((x, τ1) :: Γ) (Chk τ) ;;
            Ok (exist _ _ (C_Let E L Γ p x ann s1 s2 τ1 τ e1 e2 H1 H2))
        end
    | SAnnot p s0 t =>
        fin p L Γ (SAnnot p s0 t) m
          ('(exist _ τ Ht) <- ety_dec t ;;
           '(exist _ e H) <- elab s0 L Γ (Chk τ) ;;
           Ok (existT _ τ (exist _ e (S_Annot E L Γ p s0 t τ e Ht H))))
    | SIf p c t oe =>
        '(exist _ c' Hc) <- elab c L Γ (Chk TBool) ;;
        match oe as o return result (out L Γ (SIf p c t o) m) elab_error with
        | None =>
            fin p L Γ (SIf p c t None) m
              ('(exist _ t' Ht) <- elab t L Γ (Chk TUnit) ;;
               Ok (existT _ _ (exist _ _ (S_If1 E L Γ p c t c' t' Hc Ht))))
        | Some f =>
            match m as m0 return result (out L Γ (SIf p c t (Some f)) m0) elab_error with
            | Chk τ =>
                '(exist _ t' Ht) <- elab t L Γ (Chk τ) ;;
                '(exist _ f' Hf) <- elab f L Γ (Chk τ) ;;
                Ok (exist _ _ (C_If E L Γ p c t f τ c' t' f' Hc Ht Hf))
            | Syn =>
                match (diverges t && negb (diverges f))%bool as d
                      return (diverges t && negb (diverges f))%bool = d ->
                             result (sout L Γ (SIf p c t (Some f))) elab_error with
                | false => fun Hd =>
                    '(existT _ τ (exist _ t' Ht)) <- elab t L Γ Syn ;;
                    '(exist _ f' Hf) <- elab f L Γ (Chk τ) ;;
                    Ok (existT _ τ (exist _ _ (S_If E L Γ p c t f τ c' t' f' Hd Hc Ht Hf)))
                | true => fun Hd =>
                    '(existT _ τ (exist _ f' Hf)) <- elab f L Γ Syn ;;
                    '(exist _ t' Ht) <- elab t L Γ (Chk τ) ;;
                    Ok (existT _ τ (exist _ _ (ifr_syn L Γ p c t f τ c' t' f' Hd Hc Hf Ht)))
                end eq_refl
            end
        end
    | STup p ss =>
        let syn_t :=
          '(existT _ τs (exist _ es Hs)) <- syn_list L Γ (fun s' => elab s' L Γ Syn) ss ;;
          Ok (existT _ _ (exist _ _ (S_Tuple E L Γ p ss τs es Hs))) in
        match m as m0 return result (out L Γ (STup p ss) m0) elab_error with
        | Syn => syn_t
        | Chk τ =>
            match τ as t0 return result (out L Γ (STup p ss) (Chk t0)) elab_error with
            | TTuple ts =>
                if Nat.eqb (List.length ts) (List.length ss) then
                  '(exist _ es Hs) <- chk_list p L Γ (fun s' τ' => elab s' L Γ (Chk τ')) ss ts ;;
                  Ok (exist _ _ (C_Tuple E L Γ p ss ts es Hs))
                else fin p L Γ (STup p ss) (Chk (TTuple ts)) syn_t
            | t0 => fin p L Γ (STup p ss) (Chk t0) syn_t
            end
        end
    | SProj p s0 i =>
        fin p L Γ (SProj p s0 i) m
          ('(existT _ τ0 (exist _ e H)) <- elab s0 L Γ Syn ;;
           match τ0 as t return Γ ⊩[E;L] s0 ⇒ t ⇝ e -> result (sout L Γ (SProj p s0 i)) elab_error with
           | TTuple τs => fun H =>
               '(exist _ τ Hi) <- of_option (nth_error τs i) (EE_Type p (E_TupleIndex i (TTuple τs))) ;;
               Ok (existT _ τ (exist _ _ (S_Proj E L Γ p s0 i τs τ e H Hi)))
           | t => fun _ => Err (EE_Type p (E_NotTuple t))
           end H)
    | SLam p ps ret a body =>
        let syn_l :=
          '(exist _ τs Hps) <- params_syn_dec p ps ;;
          '(exist _ ε Hε) <- eff_syn_dec a ;;
          match ret as r0 return result (sout L Γ (SLam p ps r0 a body)) elab_error with
          | Some t =>
              '(exist _ r Hr) <- ety_dec t ;;
              '(exist _ b Hb) <- elab body (fun_env r ε) (List.app (lam_ctx ps τs) Γ) (Chk r) ;;
              Ok (existT _ _ (exist _ _ (S_LamRet E L Γ p ps t a body τs r ε b Hps Hr Hε Hb)))
          | None =>
              '(existT _ r (exist _ b Hb)) <- elab body (mk_cenv [] ε) (List.app (lam_ctx ps τs) Γ) Syn ;;
              Ok (existT _ _ (exist _ _ (S_Lam E L Γ p ps a body τs r ε b Hps Hε Hb)))
          end in
        match m as m0 return result (out L Γ (SLam p ps ret a body) m0) elab_error with
        | Syn => syn_l
        | Chk τ =>
            match τ as t0 return result (out L Γ (SLam p ps ret a body) (Chk t0)) elab_error with
            | TArrow τs r ε =>
                if Nat.eqb (List.length τs) (List.length ps) then
                  Hps <- params_fit p ps τs ;;
                  Hr <- ann_fit p ret r ;;
                  Hε <- eff_fit p a ε ;;
                  '(exist _ b Hb) <- elab body (fun_env r ε) (List.app (lam_ctx ps τs) Γ) (Chk r) ;;
                  Ok (exist _ _ (C_Lam E L Γ p ps ret a body τs r ε b Hps Hr Hε Hb))
                else fin p L Γ (SLam p ps ret a body) (Chk (TArrow τs r ε)) syn_l
            | t0 => fin p L Γ (SLam p ps ret a body) (Chk t0) syn_l
            end
        end
    | SApp p f args =>
        match head_of Γ f with
        | HName _ _ q g Hf Hl =>
            match lookup_fn hdr g as o return lookup_fn hdr g = o -> result (out L Γ (SApp p f args) m) elab_error with
            | Some fd => fun Hfd =>
                fin p L Γ (SApp p f args) m
                  (Hb <- no_bounds q g ;;
                   let n := fd_tparams fd in
                   let ps := fd_params fd in
                   _ <- bcheck (Nat.eqb (List.length args) (List.length ps))
                               (EE_Type q (E_ArgArity (List.length ps) (List.length args))) ;;
                   let st0 := match hint m with
                              | Some t => tmatch (fd_ret fd) t (repeat None n)
                              | None => repeat None n
                              end in
                   '(exist _ rs1 H1, st1) <- pass1 elab L Γ args ps st0 ;;
                   '(exist _ rs2 H2, st2) <- pass2 elab L Γ args rs1 H1 ps st1 ;;
                   '(exist _ ts Hts) <- fn_targs q g fd st2 ;;
                   '(exist _ es Hes) <- finish p L Γ args rs2 H2 (map (tsubst (inst ts)) ps) ;;
                   Hok <- allowed_dec p (tsubst (inst ts) (fd_eff fd)) (ce_exn L) ;;
                   Ok (existT _ _ (exist _ _
                         (app_syn L Γ p f q g args _ _ Hf
                            (S_Call E L Γ p q g args fd ts es Hl Hfd Hb Hts Hes Hok)))))
            | None => fun Hfd =>
                let Hbi : builtin E Γ g := conj Hl Hfd in
                match string_dec g "not", args as a0
                      return result (out L Γ (SApp p f a0) m) elab_error with
                | left Hg, [a] =>
                    fin p L Γ (SApp p f [a]) m
                      ('(exist _ a' Ha) <- elab a L Γ (Chk TBool) ;;
                       Ok (existT _ _ (exist _ _ (app_syn L Γ p f q g [a] _ _ Hf
                                                    (bnot_syn L Γ p q g a a' Hg Hbi Ha)))))
                | _, a0 =>
                match string_dec g "ignore", a0 as a1
                      return result (out L Γ (SApp p f a1) m) elab_error with
                | left Hg, [a] =>
                    fin p L Γ (SApp p f [a]) m
                      ('(existT _ τ (exist _ a' Ha)) <- elab a L Γ Syn ;;
                       Ok (existT _ _ (exist _ _ (app_syn L Γ p f q g [a] _ _ Hf
                                                    (ignore_syn L Γ p q g a τ a' Hg Hbi Ha)))))
                | _, a1 =>
                match string_dec g "panic", a1 as a2
                      return result (out L Γ (SApp p f a2) m) elab_error with
                | left Hg, [] =>
                    match m as m0 return result (out L Γ (SApp p f []) m0) elab_error with
                    | Syn => Ok (existT _ _ (exist _ _ (app_syn L Γ p f q g [] _ _ Hf
                                                          (panic_syn L Γ p q g Hg Hbi))))
                    | Chk τ => Ok (exist _ _ (app_chk L Γ p f q g [] _ _ Hf
                                                (panic_chk L Γ p q g τ Hg Hbi)))
                    end
                | _, a2 =>
                match string_dec g "abort", a2 as a3
                      return result (out L Γ (SApp p f a3) m) elab_error with
                | left Hg, [a] =>
                    '(exist _ a' Ha) <- elab a L Γ (Chk TString) ;;
                    match m as m0 return result (out L Γ (SApp p f [a]) m0) elab_error with
                    | Syn => Ok (existT _ _ (exist _ _ (app_syn L Γ p f q g [a] _ _ Hf
                                                          (abort_syn L Γ p q g a a' Hg Hbi Ha))))
                    | Chk τ => Ok (exist _ _ (app_chk L Γ p f q g [a] _ _ Hf
                                                (abort_chk L Γ p q g a a' τ Hg Hbi Ha)))
                    end
                | _, _ => Err (EE_Unbound q g)
                end
                end
                end
                end
            end eq_refl
        | HExpr _ _ Hc =>
            fin p L Γ (SApp p f args) m
              ('(existT _ τf (exist _ f' Hf)) <- elab f L Γ Syn ;;
               match τf as t return Γ ⊩[E;L] f ⇒ t ⇝ f' -> result (sout L Γ (SApp p f args)) elab_error with
               | TArrow ps r ε => fun Hf =>
                   '(exist _ es Hes) <- chk_list p L Γ (fun s' τ' => elab s' L Γ (Chk τ')) args ps ;;
                   Hok <- allowed_dec p ε (ce_exn L) ;;
                   Ok (existT _ r (exist _ _ (S_CallExpr E L Γ p f args ps r ε f' es Hc Hf Hes Hok)))
               | t => fun _ => Err (EE_Type p (E_NotFunction t))
               end Hf)
        | HOther _ _ => Err (EE_Unsupported p "constructor or method call")
        end
    | _ => Err (EE_Unsupported (sexpr_pos s) "not yet in the certified elaborator")
    end.
End Elaborate.
