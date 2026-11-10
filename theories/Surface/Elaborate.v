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

Lemma pick_live cs sp b :
  find (fun c => negb (diverges (snd c))) cs = Some (sp, b) -> pick_arm cs = Some (sp, b).
Proof. unfold pick_arm; intros ->; reflexivity. Qed.

Lemma pick_first sp b cs :
  find (fun c => negb (diverges (snd c))) ((sp, b) :: cs) = None -> pick_arm ((sp, b) :: cs) = Some (sp, b).
Proof. unfold pick_arm; intros ->; reflexivity. Qed.

Section Elaborate.
  Variable E : senv.
  Abbreviation hdr := (se_hdr E).

  Definition sout (L : cenv) (Γ : lctx) (s : sexpr) : Type :=
    {τ : ty & {e : expr | Γ ⊩[E;L] s ⇒ τ ⇝ e}}.
  Definition cout (L : cenv) (Γ : lctx) (s : sexpr) (τ : ty) : Type :=
    {e : expr | Γ ⊩[E;L] s ⇐ τ ⇝ e}.
  (** The answer in mode [m].  Its shape does not depend on [m] (only its
      proof does), so that it is an ordinary type after extraction. *)
  Definition outP (L : cenv) (Γ : lctx) (s : sexpr) (m : mode) (τ : ty) (e : expr) : Prop :=
    match m with
    | Syn => Γ ⊩[E;L] s ⇒ τ ⇝ e
    | Chk τ' => τ = τ' /\ Γ ⊩[E;L] s ⇐ τ' ⇝ e
    end.
  Definition out (L : cenv) (Γ : lctx) (s : sexpr) (m : mode) : Type :=
    {τ : ty & {e : expr | outP L Γ s m τ e}}.

  Definition cO {L Γ s τ} (x : cout L Γ s τ) : out L Γ s (Chk τ) :=
    let '(exist _ e H) := x in existT _ τ (exist _ e (conj eq_refl H)).
  Definition Oc {L Γ s τ} (x : out L Γ s (Chk τ)) : cout L Γ s τ :=
    let '(existT _ _ (exist _ e H)) := x in exist _ e (proj2 H).
  Definition Okc {L Γ s τ} (x : cout L Γ s τ) : result (out L Γ s (Chk τ)) elab_error := Ok (cO x).
  Definition cres {L Γ s τ} (r : result (out L Γ s (Chk τ)) elab_error) : result (cout L Γ s τ) elab_error :=
    match r with Ok x => Ok (Oc x) | Err err => Err err end.

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

  Definition field_proj_dec (p : pos) (T : ident) (ts : list ty) (i : nat) (e : expr) :
      result {r | field_proj E T ts i e = Some r} elab_error :=
    match field_proj E T ts i e as o return field_proj E T ts i e = o -> result _ elab_error with
    | Some r => fun H => Ok (exist _ r H)
    | None => fun _ => Err (EE_Type p (E_TupleIndex i (TData T ts)))
    end eq_refl.

  (** *** Dictionaries and trait objects *)

  Definition dict_dec (p : pos) (Γ : lctx) (Tr : ident) (τ : ty) : result {d | dict E Γ Tr τ d} elab_error :=
    match Resolve.entails_dec (x_insts (se_x E)) (asm_of E Γ) Tr τ with
    | inleft (exist _ d H) => Ok (exist _ d H)
    | inright _ => Err (EE_NoInstance p Tr τ)
    end.

  Fixpoint dicts_dec (p : pos) (Γ : lctx) (τs : list ty) : result {ds | dicts E Γ τs ds} elab_error :=
    match τs as l return result {ds | dicts E Γ l ds} elab_error with
    | [] => Ok (exist _ [] (Forall2_nil _))
    | t :: τs' =>
        '(exist _ d Hd) <-
          (match t as t0 return result {d | exists Tr τ, t0 = TData Tr [τ] /\ dict E Γ Tr τ d} elab_error with
           | TData Tr [τ] =>
               '(exist _ d H) <- dict_dec p Γ Tr τ ;;
               Ok (exist _ d (ex_intro _ Tr (ex_intro _ τ (conj eq_refl H))))
           | _ => Err (EE_Unsupported p "dictionary parameter")
           end) ;;
        '(exist _ ds Hds) <- dicts_dec p Γ τs' ;;
        Ok (exist _ (d :: ds) (Forall2_cons t d Hd Hds))
    end.

  Lemma obj_meth_intro Γo τ sm ti i sg ps r ε d mv t :
    find_trait (trs E) (fst sm) = Some ti -> method_of ti (ms_name (snd sm)) = Some (i, sg) ->
    dict E (List.app (map (fun t => (None, t)) ps) Γo) (fst sm) τ d ->
    field_proj E (fst sm) [τ] i d = Some (mv, t) -> t = TArrow (τ :: ps) r ε ->
    obj_meth E Γo τ sm (TArrow ps r ε)
      (ELam ps r ε (EApp mv (EVar (List.length ps) :: map EVar (seq 0 (List.length ps))))).
  Proof.
    intros H1 H2 H3 H4 ->; unfold obj_meth.
    exists ti, i, sg, ps, r, ε, d, mv; repeat split; auto.
  Qed.

  Definition obj_meth_dec (p : pos) (Γo : lctx) (τ : ty) (sm : ident * msig) (fty : ty) :
      result {f | obj_meth E Γo τ sm fty f} elab_error :=
    '(exist _ ti Hti) <- of_option (find_trait (trs E) (fst sm)) (EE_NotObjectSafe p (fst sm)) ;;
    '(exist _ (i, sg) Hm) <- of_option (method_of ti (ms_name (snd sm))) (EE_NoMethod p (ms_name (snd sm)) τ) ;;
    match fty as t return result {f | obj_meth E Γo τ sm t f} elab_error with
    | TArrow ps r ε =>
        '(exist _ d Hd) <- dict_dec p (List.app (map (fun t => (None, t)) ps) Γo) (fst sm) τ ;;
        '(exist _ (mv, t) Hp) <- field_proj_dec p (fst sm) [τ] i d ;;
        match ty_eq_dec t (TArrow (τ :: ps) r ε) with
        | left Ht => Ok (exist _ _ (obj_meth_intro Γo τ sm ti i sg ps r ε d mv t Hti Hm Hd Hp Ht))
        | right _ => Err (EE_Annot p (TArrow (τ :: ps) r ε) t)
        end
    | _ => Err (EE_NotObjectSafe p (fst sm))
    end.

  Fixpoint obj_meths_dec (p : pos) (Γo : lctx) (τ : ty) (sms : list (ident * msig)) (ftys : list ty) :
      result {fs | obj_meths E Γo τ sms ftys fs} elab_error :=
    match sms as l1, ftys as l2 return result {fs | obj_meths E Γo τ l1 l2 fs} elab_error with
    | [], [] => Ok (exist _ [] I)
    | sm :: sms', t :: ts' =>
        '(exist _ f Hf) <- obj_meth_dec p Γo τ sm t ;;
        '(exist _ fs Hfs) <- obj_meths_dec p Γo τ sms' ts' ;;
        Ok (exist _ (f :: fs) (conj Hf Hfs))
    | _, _ => Err (EE_NotObjectSafe p "object")
    end.

  Definition obj_coerce (p : pos) (Γ : lctx) (e : expr) (τ τ' : ty) (Tr : ident)
      (Ho : obj_of E τ' = Some Tr) (Hne : τ <> τ') :
      result {e' | ⊩ᶜ[E;Γ] e : τ ≼ τ' ⇝ e'} elab_error :=
    '(exist _ td Htd) <- of_option (lookup_ty hdr (obj_name Tr)) (EE_UnknownType p (obj_name Tr)) ;;
    match Nat.eq_dec (td_tparams td) 0 with
    | left Hn =>
        '(exist _ cd Hc) <- of_option (lookup_ctor td (obj_name Tr)) (EE_UnknownCtor p (obj_name Tr)) ;;
        '(exist _ fs Hfs) <- obj_meths_dec p ((None, τ) :: Γ) τ (obj_fields (trs E) Tr)
                                           (map (tsubst (inst [])) (cd_fields cd)) ;;
        Ok (exist _ _ (Co_Obj E Γ e τ τ' Tr td cd fs Ho Hne Htd Hn Hc Hfs))
    | right _ => Err (EE_UnknownType p (obj_name Tr))
    end.

  (** Implicit conversion of [e : τ'] to [τ]. *)
  Definition coerce (p : pos) (Γ : lctx) (e : expr) (τ' τ : ty) :
      result {e' | ⊩ᶜ[E;Γ] e : τ' ≼ τ ⇝ e'} elab_error :=
    match ty_eq_dec τ' τ with
    | left H => Ok (exist _ e (eq_ind τ' (fun t => ⊩ᶜ[E;Γ] e : τ' ≼ t ⇝ e) (Co_Refl E Γ e τ') τ H))
    | right Hne =>
        match obj_of E τ as o return obj_of E τ = o -> result {e' | ⊩ᶜ[E;Γ] e : τ' ≼ τ ⇝ e'} elab_error with
        | Some Tr => fun Ho => obj_coerce p Γ e τ' τ Tr Ho Hne
        | None => fun _ =>
            match τ' as t1, τ as t2 return result {e' | ⊩ᶜ[E;Γ] e : t1 ≼ t2 ⇝ e'} elab_error with
            | TData T [], TError =>
                H <- err_dec p T ;;
                Ok (exist _ (EUp T e) (Co_Up E Γ e T H))
            | t1, t2 => Err (EE_Annot p t2 t1)
            end
        end eq_refl
    end.

  (** The answer in mode [m], from a synthesis: check by subsumption. *)
  Definition fin (p : pos) (L : cenv) (Γ : lctx) (s : sexpr) (m : mode)
      (r : result (sout L Γ s) elab_error) : result (out L Γ s m) elab_error :=
    match m as m0 return result (out L Γ s m0) elab_error with
    | Syn => r
    | Chk τ =>
        '(existT _ τ' (exist _ e H)) <- r ;;
        '(exist _ e' Hc) <- coerce p Γ e τ' τ ;;
        Okc (exist _ e' (C_Sub E L Γ s τ' τ e e' H Hc))
    end.

  Definition binop_dec (p : pos) (op : ident) (τ : ty) (a b : expr) :
      result {e | elab_binop p op τ a b = Ok e} elab_error :=
    match elab_binop p op τ a b as r
          return elab_binop p op τ a b = r -> result {e | elab_binop p op τ a b = Ok e} elab_error with
    | Ok e => fun H => Ok (exist _ e H)
    | Err err => fun _ => Err err
    end eq_refl.

  Definition targs (p : pos) (g : ident) (n : nat) (st : list (option ty)) :
      result {ts | List.length ts = n} elab_error :=
    match all_some st with
    | Some ts =>
        match Nat.eq_dec (List.length ts) n with
        | left H => Ok (exist _ ts H)
        | right _ => Err (EE_CannotInfer p g)
        end
    | None => Err (EE_CannotInfer p g)
    end.

  Definition fn_targs (p : pos) (g : ident) (fd : fdef) (st : list (option ty)) :
      result {ts | List.length ts = fd_tparams fd} elab_error :=
    targs p g (fd_tparams fd) st.

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
               | Some t => '(exist _ e H) <- cres (rec s L Γ (Chk t)) ;; Ok (AH_Chk t e H, st)
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
    | Some t => '(exist _ e H) <- cres (rec s L Γ (Chk t)) ;; Ok (AH_Chk t e H, st)
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
                   '(exist _ b Hb) <- cres (rec body (fun_env r ε) Γ' (Chk r)) ;;
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
                         '(exist _ e' Hc') <- coerce p Γ e t τ ;;
                         Ok (exist _ e' (C_Sub E L Γ s t τ e e' (syn_cast L Γ s0 s t e Hs H) Hc'))
                     | existT _ _ AH_Post => fun _ => Err (EE_CannotInfer p "argument")
                     end (proj1 Hc)) ;;
                  '(exist _ es Hes) <- go args' rs' (proj2 Hc) τs' ;;
                  Ok (exist _ (e :: es) (Cs_cons E L Γ s args' τ τs' e es He Hes))
              end
          end
      end.

  (** The arguments of a call of a generic function or method with
      parameters [ps] (after the dictionaries) and [n] type parameters. *)
  Definition gargs (rec : elab_ty_t) (p q : pos) (L : cenv) (Γ : lctx) (args : list sexpr)
      (ps : list ty) (n : nat) (st0 : list (option ty)) (g : ident) :
      result {ts : list ty & {es | List.length ts = n /\ Γ ⊩*[E;L] args ⇐ map (tsubst (inst ts)) ps ⇝ es}}
             elab_error :=
    _ <- bcheck (Nat.eqb (List.length args) (List.length ps))
                (EE_Type q (E_ArgArity (List.length ps) (List.length args))) ;;
    '(exist _ rs1 H1, st1) <- pass1 rec L Γ args ps st0 ;;
    '(exist _ rs2 H2, st2) <- pass2 rec L Γ args rs1 H1 ps st1 ;;
    '(exist _ ts Hts) <- targs q g n st2 ;;
    '(exist _ es Hes) <- finish p L Γ args rs2 H2 (map (tsubst (inst ts)) ps) ;;
    Ok (existT _ ts (exist _ es (conj Hts Hes))).

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
            Okc (exist _ _ (C_Lit E L Γ p z k H))
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
        | t => fun Hn => Ok (existT _ t (exist _ _ (S_Var E L Γ p x i t Hl Hn)))
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

  (** ** Data types *)

  Definition tq_dec (p : pos) (tq : option ident) (T : ident) (err : elab_error) :
      result (tq_ok tq T) elab_error :=
    match tq as o return result (tq_ok o T) elab_error with
    | Some T' => match eq_dec T' T with left H => Ok H | right _ => Err err end
    | None => Ok I
    end.

  Definition ctor_pick_dec (p : pos) (tq : option ident) (c : ident) :
      result {T | ctor_pick E tq c T} elab_error :=
    match tq as o return result {T | ctor_pick E o c T} elab_error with
    | Some T => Ok (exist _ T eq_refl)
    | None =>
        match map td_name (filter (fun td => negb (is_rec E (td_name td)) && ctor_in c td)
                                  (ge_types hdr)) as l
              return map td_name (filter (fun td => negb (is_rec E (td_name td)) && ctor_in c td)
                                         (ge_types hdr)) = l ->
                     result {T | ctor_pick E None c T} elab_error with
        | [T] => fun H => Ok (exist _ T H)
        | [] => fun _ => Err (EE_UnknownCtor p c)
        | _ => fun _ => Err (EE_AmbiguousCtor p c)
        end eq_refl
    end.

  Definition err_owner_dec (p : pos) (tq : option ident) (c : ident) :
      result {T | err_owner E tq c T} elab_error :=
    match tq as o return result {T | err_owner E o c T} elab_error with
    | Some T => Ok (exist _ T eq_refl)
    | None =>
        match map td_name (filter (fun td => td_err td && ctor_in c td) (ge_types hdr)) as l
              return map td_name (filter (fun td => td_err td && ctor_in c td) (ge_types hdr)) = l ->
                     result {T | err_owner E None c T} elab_error with
        | [T] => fun H => Ok (exist _ T H)
        | [] => fun _ => Err (EE_UnknownCtor p c)
        | _ => fun _ => Err (EE_AmbiguousCtor p c)
        end eq_refl
    end.

  Definition single_ctor (p : pos) (td : tdef) (t : ty) : result {cd | td_ctors td = [cd]} elab_error :=
    match td_ctors td as l return result {cd | l = [cd]} elab_error with
    | [cd] => Ok (exist _ cd eq_refl)
    | _ => Err (EE_NotRecord p t)
    end.

  (** ** Patterns *)

  Abbreviation pout sp τ := {q : pat & {Δ : lctx | ⊩ᵖ[E] sp : τ ⇝ q ⊣ Δ}}.

  Definition fpat (rec : forall sp τ, result (pout sp τ) elab_error) (sp : spat) (τ : ty) :
      result {q : pat & {Δ : lctx | ⊩ᶠ[E] sp : τ ⇝ q ⊣ Δ}} elab_error :=
    match τ as t return result {q : pat & {Δ : lctx | ⊩ᶠ[E] sp : t ⇝ q ⊣ Δ}} elab_error with
    | TRef u =>
        '(existT _ q (exist _ Δ H)) <- rec sp u ;;
        Ok (existT _ (PRef q) (exist _ Δ (FP_Cell E sp u q Δ H)))
    | t =>
        '(existT _ q (exist _ Δ H)) <- rec sp t ;;
        Ok (existT _ q (exist _ Δ (FP_Plain E sp t q Δ eq_refl H)))
    end.

  (** Sub-patterns against a prefix [fs1] of the field types [fs]. *)
  Definition fpats_prefix (rec : forall sp τ, result (pout sp τ) elab_error) (err : elab_error) :
      forall sps fs, result {qs : list pat & {Δ : lctx & {fs1 : list ty & {fs2 : list ty |
                       fs = List.app fs1 fs2 /\ ⊩ᶠ*[E] sps : fs1 ⇝ qs ⊣ Δ}}}} elab_error :=
    fix go sps fs :=
      match sps as sps0 return result {qs : list pat & {Δ : lctx & {fs1 : list ty & {fs2 : list ty |
                                  fs = List.app fs1 fs2 /\ ⊩ᶠ*[E] sps0 : fs1 ⇝ qs ⊣ Δ}}}} elab_error with
      | [] => Ok (existT _ [] (existT _ [] (existT _ [] (exist _ fs (conj eq_refl (FPs_nil E))))))
      | sp :: sps' =>
          match fs as fs0 return result {qs : list pat & {Δ : lctx & {fs1 : list ty & {fs2 : list ty |
                                   fs0 = List.app fs1 fs2 /\ ⊩ᶠ*[E] sp :: sps' : fs1 ⇝ qs ⊣ Δ}}}} elab_error with
          | [] => Err err
          | τ :: fs' =>
              '(existT _ q (exist _ Δ1 H1)) <- fpat rec sp τ ;;
              '(existT _ qs (existT _ Δ2 (existT _ fs1 (exist _ fs2 (conj Hfs H2))))) <- go sps' fs' ;;
              Ok (existT _ (q :: qs) (existT _ (List.app Δ1 Δ2) (existT _ (τ :: fs1) (exist _ fs2
                    (conj (f_equal (cons τ) Hfs) (FPs_cons E sp sps' τ fs1 q qs Δ1 Δ2 H1 H2))))))
          end
      end.

  Definition named_pats (rec : forall sp τ, result (pout sp τ) elab_error) (p : pos)
      (names : list ident) (fs : list ty) :
      forall fps, result {given | ⊩ⁿ[E] fps : names ; fs ⇝ given} elab_error :=
    fix go fps :=
      match fps as fps0 return result {given | ⊩ⁿ[E] fps0 : names ; fs ⇝ given} elab_error with
      | [] => Ok (exist _ [] (FN_nil E names fs))
      | (f, sp) :: fps' =>
          '(exist _ i Hi) <- of_option (index_of f names) (EE_UnknownField p f) ;;
          '(exist _ τ Hτ) <- of_option (nth_error fs i) (EE_UnknownField p f) ;;
          '(existT _ q (exist _ Δ H)) <- fpat rec sp τ ;;
          '(exist _ given Hg) <- go fps' ;;
          Ok (exist _ ((i, q, Δ) :: given) (FN_cons E f sp fps' names fs i τ q Δ given Hi Hτ H Hg))
      end.

  Definition open_ok (p : pos) (τ : ty) (op : bool) (fs2 : list ty) :
      result (op = false -> fs2 = []) elab_error :=
    match op as o return result (o = false -> fs2 = []) elab_error with
    | true => Ok (fun H => match Bool.diff_true_false H with end)
    | false =>
        match fs2 as f return result (false = false -> f = []) elab_error with
        | [] => Ok (fun _ => eq_refl)
        | _ => Err (EE_PatType p τ)
        end
    end.

  (** The first field that a closed record pattern does not mention. *)
  Definition missing_field (names : list ident) (given : list (nat * pat * lctx)) : ident :=
    match find (fun f => match index_of f names with
                         | Some j => negb (existsb (fun x => Nat.eqb (fst (fst x)) j) given)
                         | None => false
                         end) names with
    | Some f => f
    | None => ""
    end.

  Fixpoint epat (sp : spat) (τ : ty) {struct sp} : result (pout sp τ) elab_error :=
    match sp as sp0 return result (pout sp0 τ) elab_error with
    | SPWild p => Ok (existT _ PWild (exist _ [] (SP_Wild E p τ)))
    | SPVar p x => Ok (existT _ PVar (exist _ [(Some x, τ)] (SP_Var E p x τ)))
    | SPLit p l =>
        match elab_lit p (Some τ) l as r return elab_lit p (Some τ) l = r -> result (pout (SPLit p l) τ) elab_error with
        | Ok l' => fun H =>
            match ty_eq_dec (TBase (lit_ty l')) τ with
            | left Ht => Ok (existT _ (PLit l') (exist _ [] (SP_Lit E p l l' τ H Ht)))
            | right _ => Err (EE_PatType p τ)
            end
        | Err err => fun _ => Err err
        end eq_refl
    | SPTuple p sps =>
        match τ as t return result (pout (SPTuple p sps) t) elab_error with
        | TTuple τs =>
            '(existT _ qs (existT _ Δ (existT _ fs1 (exist _ fs2 (conj Hfs H))))) <-
              fpats_prefix epat (EE_PatType p (TTuple τs)) sps τs ;;
            match fs2 as f return τs = List.app fs1 f -> result (pout (SPTuple p sps) (TTuple τs)) elab_error with
            | [] => fun Hfs =>
                Ok (existT _ (PTuple qs) (exist _ Δ
                      (eq_ind_r (fun u => ⊩ᵖ[E] SPTuple p sps : TTuple u ⇝ PTuple qs ⊣ Δ)
                                (SP_Tuple E p sps fs1 qs Δ H) (eq_trans Hfs (app_nil_r fs1)))))
            | _ => fun _ => Err (EE_PatType p (TTuple τs))
            end Hfs
        | t => Err (EE_PatType p t)
        end
    | SPConstr p tq c sps op =>
        match τ as t return result (pout (SPConstr p tq c sps op) t) elab_error with
        | TData T ts =>
            Htq <- tq_dec p tq T (EE_PatType p (TData T ts)) ;;
            '(exist _ td Htd) <- of_option (lookup_ty hdr T) (EE_UnknownType p T) ;;
            '(exist _ cd Hcd) <- of_option (lookup_ctor td c) (EE_UnknownCtor p c) ;;
            '(existT _ qs (existT _ Δ (existT _ fs1 (exist _ fs2 (conj Hfs H))))) <-
              fpats_prefix epat (EE_PatType p (TData T ts)) sps (map (tsubst (inst ts)) (cd_fields cd)) ;;
            Hop <- open_ok p (TData T ts) op fs2 ;;
            Ok (existT _ _ (exist _ Δ
                  (SP_Constr E p tq c sps op T ts td cd fs1 fs2 qs Δ Htq Htd Hcd Hfs H Hop)))
        | TError =>
            '(exist _ T Ho) <- err_owner_dec p tq c ;;
            '(exist _ td Htd) <- of_option (lookup_ty hdr T) (EE_UnknownType p T) ;;
            '(exist _ cd Hcd) <- of_option (lookup_ctor td c) (EE_UnknownCtor p c) ;;
            '(existT _ qs (existT _ Δ (existT _ fs1 (exist _ fs2 (conj Hfs H))))) <-
              fpats_prefix epat (EE_PatType p TError) sps (map (tsubst (inst [])) (cd_fields cd)) ;;
            Hop <- open_ok p TError op fs2 ;;
            Ok (existT _ _ (exist _ Δ
                  (SP_Up E p tq c sps op T td cd fs1 fs2 qs Δ Ho Htd Hcd Hfs H Hop)))
        | t => Err (EE_PatType p t)
        end
    | SPRecord p fps op =>
        match τ as t return result (pout (SPRecord p fps op) t) elab_error with
        | TData T ts =>
            '(exist _ names Hn) <- of_option (assoc T (se_sinfo E)) (EE_NotRecord p (TData T ts)) ;;
            '(exist _ td Htd) <- of_option (lookup_ty hdr T) (EE_UnknownType p T) ;;
            '(exist _ cd Hc) <- single_ctor p td (TData T ts) ;;
            '(exist _ given Hg) <- named_pats epat p names (map (tsubst (inst ts)) (cd_fields cd)) fps ;;
            match assemble op given 0 (map (tsubst (inst ts)) (cd_fields cd)) as o
                  return assemble op given 0 (map (tsubst (inst ts)) (cd_fields cd)) = o ->
                         result (pout (SPRecord p fps op) (TData T ts)) elab_error with
            | Some (qs, Δ) => fun Ha =>
                Ok (existT _ _ (exist _ Δ (SP_Record E p fps op T ts names td cd given qs Δ Hn Htd Hc Hg Ha)))
            | None => fun _ => Err (EE_MissingField p (missing_field names given))
            end eq_refl
        | t => Err (EE_NotRecord p t)
        end
    | SPAnnot p sp0 t =>
        '(exist _ τ' Ht) <- ety_dec t ;;
        match ty_eq_dec τ' τ with
        | left Heq =>
            '(existT _ q (exist _ Δ H)) <- epat sp0 τ ;;
            Ok (existT _ q (exist _ Δ
                  (SP_Annot E p sp0 t τ q Δ (eq_ind τ' (fun u => ety E t = Ok u) Ht τ Heq) H)))
        | right _ => Err (EE_Annot p τ' τ)
        end
    end.

  (** *** [match] *)

  Definition arm_live (c : spat * sexpr) : bool := negb (diverges (snd c)).

  (** The arm that gives the type of a [match], synthesized. *)
  Definition arm_syn L Γ τs (sp : spat) (b : sexpr) (τ : ty) : Prop :=
    exists q Δ b', ⊩ᵖ[E] sp : τs ⇝ q ⊣ Δ /\ List.app Δ Γ ⊩[E;L] b ⇒ τ ⇝ b'.

  Lemma find_skip {A} (f : A -> bool) x l : f x = false -> find f (x :: l) = find f l.
  Proof. simpl; intros ->; reflexivity. Qed.

  Lemma find_hit {A} (f : A -> bool) x l : f x = true -> find f (x :: l) = Some x.
  Proof. simpl; intros ->; reflexivity. Qed.

  Definition live_arm (rec : elab_ty_t) (L : cenv) (Γ : lctx) (τs : ty) :
      forall cs, result ({τ | exists sp b, find arm_live cs = Some (sp, b) /\ arm_syn L Γ τs sp b τ}
                         + {find arm_live cs = None}) elab_error :=
    fix go cs :=
      match cs as cs0 return result ({τ | exists sp b, find arm_live cs0 = Some (sp, b) /\ arm_syn L Γ τs sp b τ}
                                     + {find arm_live cs0 = None}) elab_error with
      | [] => Ok (inright eq_refl)
      | (sp, b) :: cs' =>
          match arm_live (sp, b) as d return arm_live (sp, b) = d -> result _ elab_error with
          | true => fun Hd =>
              '(existT _ q (exist _ Δ Hp)) <- epat sp τs ;;
              '(existT _ τ (exist _ b' Hb)) <- rec b L (List.app Δ Γ) Syn ;;
              Ok (inleft (exist _ τ (ex_intro _ sp (ex_intro _ b
                    (conj (find_hit arm_live (sp, b) cs' Hd)
                          (ex_intro _ q (ex_intro _ Δ (ex_intro _ b' (conj Hp Hb)))))))))
          | false => fun Hd =>
              r <- go cs' ;;
              match r with
              | inleft (exist _ τ H) =>
                  Ok (inleft (exist _ τ (eq_ind_r (fun o => exists sp0 b0, o = Some (sp0, b0) /\ arm_syn L Γ τs sp0 b0 τ)
                                                 H (find_skip arm_live (sp, b) cs' Hd))))
              | inright H => Ok (inright (eq_trans (find_skip arm_live (sp, b) cs' Hd) H))
              end
          end eq_refl
      end.

  Definition pick_syn (rec : elab_ty_t) (p : pos) (L : cenv) (Γ : lctx) (τs : ty) (cs : list (spat * sexpr)) :
      result {τ | exists sp b, pick_arm cs = Some (sp, b) /\ arm_syn L Γ τs sp b τ} elab_error :=
    r <- live_arm rec L Γ τs cs ;;
    match r with
    | inleft (exist _ τ H) =>
        Ok (exist _ τ (match H with ex_intro _ sp (ex_intro _ b (conj Hf Ha)) =>
                         ex_intro _ sp (ex_intro _ b (conj (pick_live cs sp b Hf) Ha)) end))
    | inright Hn =>
        match cs as cs0 return find arm_live cs0 = None ->
                               result {τ | exists sp b, pick_arm cs0 = Some (sp, b) /\ arm_syn L Γ τs sp b τ} elab_error with
        | [] => fun _ => Err (EE_EmptyMatch p)
        | (sp, b) :: cs' => fun Hn =>
            '(existT _ q (exist _ Δ Hp)) <- epat sp τs ;;
            '(existT _ τ (exist _ b' Hb)) <- rec b L (List.app Δ Γ) Syn ;;
            Ok (exist _ τ (ex_intro _ sp (ex_intro _ b
                  (conj (pick_first sp b cs' Hn)
                        (ex_intro _ q (ex_intro _ Δ (ex_intro _ b' (conj Hp Hb))))))))
        end Hn
    end.

  Definition arms_list (rec : elab_ty_t) (L : cenv) (Γ : lctx) (τs τ : ty) :
      forall cs, result {bs | Γ ⊩ᵇ[E;L] cs : τs ⇐ τ ⇝ bs} elab_error :=
    fix go cs :=
      match cs as cs0 return result {bs | Γ ⊩ᵇ[E;L] cs0 : τs ⇐ τ ⇝ bs} elab_error with
      | [] => Ok (exist _ [] (Ar_nil E L Γ τs τ))
      | (sp, b) :: cs' =>
          '(existT _ q (exist _ Δ Hp)) <- epat sp τs ;;
          '(exist _ b' Hb) <- cres (rec b L (List.app Δ Γ) (Chk τ)) ;;
          '(exist _ bs Hbs) <- go cs' ;;
          Ok (exist _ ((q, b') :: bs) (Ar_cons E L Γ sp b cs' τs τ q Δ b' bs Hp Hb Hbs))
      end.

  Lemma match_syn L Γ p s cases τs τ e bs :
    Γ ⊩[E;L] s ⇒ τs ⇝ e ->
    (exists sp b, pick_arm cases = Some (sp, b) /\ arm_syn L Γ τs sp b τ) ->
    Γ ⊩ᵇ[E;L] cases : τs ⇐ τ ⇝ bs ->
    Γ ⊩[E;L] SMatch p s cases ⇒ τ ⇝ EMatch e τ bs.
  Proof.
    intros Hs (sp & b & Hp & q & Δ & b' & Hq & Hb) Hbs; eapply S_Match; eauto.
  Qed.

  Definition nil_fields (p : pos) (c : ident) (cd : cdef) : result (cd_fields cd = []) elab_error :=
    match cd_fields cd as l return result (l = []) elab_error with
    | [] => Ok eq_refl
    | l => Err (EE_CtorArity p c (List.length l) 0)
    end.

  Lemma ctor_syn L Γ p f q tq c args T td cd ts es :
    f = SConstr q tq c -> ctor_pick E tq c T -> lookup_ty hdr T = Some td -> lookup_ctor td c = Some cd ->
    List.length ts = td_tparams td ->
    Γ ⊩*[E;L] args ⇐ map (tsubst (inst ts)) (cd_fields cd) ⇝ es ->
    Γ ⊩[E;L] SApp p f args ⇒ TData T ts ⇝ EConstr T c ts (ETuple es).
  Proof. intros ->; apply S_Ctor. Qed.

  Lemma ctor_chk L Γ p f q tq c args T ts td cd es :
    f = SConstr q tq c -> tq_ok tq T -> lookup_ty hdr T = Some td -> lookup_ctor td c = Some cd ->
    List.length ts = td_tparams td ->
    Γ ⊩*[E;L] args ⇐ map (tsubst (inst ts)) (cd_fields cd) ⇝ es ->
    Γ ⊩[E;L] SApp p f args ⇐ TData T ts ⇝ EConstr T c ts (ETuple es).
  Proof. intros ->; apply C_Ctor. Qed.

  (** *** Records *)

  Definition rec_pick_dec (p : pos) (tq : option ident) (written : list ident) :
      result {T | rec_pick E tq written T} elab_error :=
    match tq as o return result {T | rec_pick E o written T} elab_error with
    | Some T => Ok (exist _ T eq_refl)
    | None =>
        match map fst (filter (fun tf => same_fields (snd tf) written) (se_sinfo E)) as l
              return map fst (filter (fun tf => same_fields (snd tf) written) (se_sinfo E)) = l ->
                     result {T | rec_pick E None written T} elab_error with
        | [T] => fun H => Ok (exist _ T H)
        | _ => fun _ => Err (EE_NotRecord p TUnit)
        end eq_refl
    end.

  Definition rfields_dec (rec : elab_ty_t) (p : pos) (L : cenv) (Γ : lctx) (names : list ident)
      (fs : list ty) :
      forall fes, result {es : list expr & {ixs : list nat | Γ ⊩ʳ[E;L] fes : names ; fs ⇝ es ; ixs}} elab_error :=
    fix go fes :=
      match fes as f0 return result {es : list expr & {ixs : list nat | Γ ⊩ʳ[E;L] f0 : names ; fs ⇝ es ; ixs}} elab_error with
      | [] => Ok (existT _ [] (exist _ [] (RF_nil E L Γ names fs)))
      | (f, fe) :: fes' =>
          '(exist _ i Hi) <- of_option (index_of f names) (EE_UnknownField p f) ;;
          '(exist _ τ Hτ) <- of_option (nth_error fs i) (EE_UnknownField p f) ;;
          match τ as t return nth_error fs i = Some t ->
                              result {es : list expr & {ixs : list nat |
                                Γ ⊩ʳ[E;L] (f, fe) :: fes' : names ; fs ⇝ es ; ixs}} elab_error with
          | TRef u => fun Hτ =>
              '(exist _ e He) <- cres (rec fe L Γ (Chk u)) ;;
              '(existT _ es (exist _ ixs Hr)) <- go fes' ;;
              Ok (existT _ _ (exist _ _ (RF_cell E L Γ f fe fes' names fs i u e es ixs Hi Hτ He Hr)))
          | t => fun Hτ =>
              '(exist _ e He) <- cres (rec fe L Γ (Chk t)) ;;
              '(existT _ es (exist _ ixs Hr)) <- go fes' ;;
              Ok (existT _ _ (exist _ _ (RF_plain E L Γ f fe fes' names fs i t e es ixs Hi Hτ eq_refl He Hr)))
          end Hτ
      end.

  Definition rec_vars_dec (p : pos) (names : list ident) (ixs : list nat) :
      result {vs | rec_vars ixs (List.length names) = Some vs} elab_error :=
    match rec_vars ixs (List.length names) as o
          return rec_vars ixs (List.length names) = o -> result {vs | rec_vars ixs (List.length names) = Some vs} elab_error with
    | Some vs => fun H => Ok (exist _ vs H)
    | None => fun _ =>
        match find (fun f => match index_of f names with
                             | Some j => negb (existsb (Nat.eqb j) ixs)
                             | None => false
                             end) names with
        | Some f => Err (EE_MissingField p f)
        | None => Err (EE_UnknownField p "")
        end
    end eq_refl.

  Definition len_dec (p : pos) (T : ident) (a b : nat) : result (a = b) elab_error :=
    match Nat.eq_dec a b with
    | left H => Ok H
    | right _ => Err (EE_NotRecord p (TData T []))
    end.

  Definition content (t : ty) : ty := match t with TRef u => u | _ => t end.

  (** The type arguments of a generic record struct, learned from the fields
      whose type is not yet known (they are checked again afterwards). *)
  Definition rpass (rec : elab_ty_t) (L : cenv) (Γ : lctx) (names : list ident) (fs0 : list ty) :
      list (ident * sexpr) -> list (option ty) -> result (list (option ty)) elab_error :=
    fix go fes st :=
      match fes with
      | [] => Ok st
      | (f, fe) :: fes' =>
          let pt := match index_of f names with
                    | Some i => content (nth i fs0 TUnit)
                    | None => TUnit
                    end in
          st' <- (match resolve st pt with
                  | Some _ => Ok st
                  | None => '(existT _ t _) <- rec fe L Γ Syn ;; Ok (tmatch pt t st)
                  end) ;;
          go fes' st'
      end.

  (** *** State and loops (milestone M3) *)

  Definition upd_rhs_dec (p : pos) (op : option ident) (τ : ty) (cur v : expr) :
      result {e | upd_rhs p op τ cur v e} elab_error :=
    match op as o return result {e | upd_rhs p o τ cur v e} elab_error with
    | None => Ok (exist _ v eq_refl)
    | Some o =>
        match ty_eq_dec (binop_res o τ) τ with
        | left Hr =>
            '(exist _ e He) <- binop_dec p o τ cur v ;;
            Ok (exist _ e (conj Hr He))
        | right _ => Err (EE_NoOperator p o τ)
        end
    end.

  Definition field_cell_dec (p : pos) (f : ident) (T : ident) (ts : list ty) (i : nat) :
      result {r | field_cell E T ts i = Some r} elab_error :=
    match field_cell E T ts i as o return field_cell E T ts i = o -> result {r | field_cell E T ts i = Some r} elab_error with
    | Some r => fun H => Ok (exist _ r H)
    | None => fun _ => Err (EE_NotMutable p f)
    end eq_refl.

  Definition ref_ok_dec (p : pos) : result (ref_ok E) elab_error :=
    '(exist _ td Htd) <- of_option (lookup_ty hdr "Ref") (EE_UnknownType p "Ref") ;;
    match Nat.eq_dec (td_tparams td) 1 with
    | left Hn =>
        '(exist _ cd Hc) <- of_option (lookup_ctor td "Ref") (EE_UnknownCtor p "Ref") ;;
        match list_eq_dec ty_eq_dec (cd_fields cd) [TRef (TVar 0)] with
        | left Hf => Ok (ex_intro _ td (ex_intro _ cd (conj Htd (conj Hn (conj Hc Hf)))))
        | right _ => Err (EE_UnknownType p "Ref")
        end
    | right _ => Err (EE_UnknownType p "Ref")
    end.

  Definition sinits_dec (rec : elab_ty_t) (L : cenv) (Γ : lctx) :
      forall inits, result {τs & {es | Γ ⊩ⁱ[E;L] inits ⇒ τs ⇝ es}} elab_error :=
    fix go inits :=
      match inits as i0 return result {τs & {es | Γ ⊩ⁱ[E;L] i0 ⇒ τs ⇝ es}} elab_error with
      | [] => Ok (existT _ [] (exist _ [] (In_nil E L Γ)))
      | (x, s) :: inits' =>
          '(existT _ τ (exist _ e H)) <- rec s L Γ Syn ;;
          '(existT _ τs (exist _ es Hs)) <- go inits' ;;
          Ok (existT _ (τ :: τs) (exist _ (e :: es) (In_cons E L Γ x s inits' τ τs e es H Hs)))
      end.

  Definition supds_dec (rec : elab_ty_t) (p : pos) (L : cenv) (Γ : lctx) (names : list ident) (τs : list ty) :
      forall upds, result {us | Γ ⊩ᵘ[E;L] upds : names ; τs ⇝ us} elab_error :=
    fix go upds :=
      match upds as u0 return result {us | Γ ⊩ᵘ[E;L] u0 : names ; τs ⇝ us} elab_error with
      | [] => Ok (exist _ [] (Up_nil E L Γ names τs))
      | (y, s) :: upds' =>
          '(exist _ i Hi) <- of_option (index_of y names) (EE_Unbound p y) ;;
          '(exist _ τ Hτ) <- of_option (nth_error τs i) (EE_Unbound p y) ;;
          '(exist _ u Hu) <- cres (rec s L Γ (Chk τ)) ;;
          '(exist _ us Hus) <- go upds' ;;
          Ok (exist _ ((y, u) :: us) (Up_cons E L Γ y s upds' names τs i τ u us Hi Hτ Hu Hus))
      end.

  Definition ochk_dec (rec : elab_ty_t) (L : cenv) (Γ : lctx) (τ : ty) :
      forall os, result {oe | Γ ⊩ᵒ[E;L] os ⇐ τ ⇝ oe} elab_error :=
    fun os =>
      match os as o return result {oe | Γ ⊩ᵒ[E;L] o ⇐ τ ⇝ oe} elab_error with
      | None => Ok (exist _ None (Oc_None E L Γ τ))
      | Some s => '(exist _ e H) <- cres (rec s L Γ (Chk τ)) ;; Ok (exist _ (Some e) (Oc_Some E L Γ s τ e H))
      end.

  Definition label_at (p : pos) (L : cenv) (k : nat) : result {lbl | nth_error (core_labels (ce_labs L)) k = Some lbl} elab_error :=
    of_option (nth_error (core_labels (ce_labs L)) k) (EE_NoTarget p).

  Lemma lbl_res {L : cenv} {k ps r r'} :
    nth_error (core_labels (ce_labs L)) k = Some (ps, r) -> r = r' ->
    nth_error (core_labels (ce_labs L)) k = Some (ps, r').
  Proof. intros H <-; exact H. Qed.

  Lemma lbl_ps {L : cenv} {k ps ps' r} :
    nth_error (core_labels (ce_labs L)) k = Some (ps, r) -> ps = ps' ->
    nth_error (core_labels (ce_labs L)) k = Some (ps', r).
  Proof. intros H <-; exact H. Qed.

  Lemma tgt_res {x : option ident} {L : cenv} {k r r'} :
    break_target x (ce_labs L) 0 = Some (k, r) -> r = r' -> break_target x (ce_labs L) 0 = Some (k, r').
  Proof. intros H <-; exact H. Qed.

  Lemma ret_res {L : cenv} {k r r'} :
    return_target (ce_labs L) 0 = Some (k, r) -> r = r' -> return_target (ce_labs L) 0 = Some (k, r').
  Proof. intros H <-; exact H. Qed.

  Lemma cons_not_nil {A} (a : A) l : a :: l <> [].
  Proof. discriminate. Qed.

  Lemma meth_syn L Γ p s m m' args τ e :
    m = m' -> Γ ⊩[E;L] SMethod p s m' args ⇒ τ ⇝ e -> Γ ⊩[E;L] SMethod p s m args ⇒ τ ⇝ e.
  Proof. intros ->; auto. Qed.

  Lemma qual_eq p f q T T' m m' args :
    f = SQual q T m -> T = T' -> m = m' -> SApp p (SQual q T' m') args = SApp p f args.
  Proof. intros -> -> ->; reflexivity. Qed.

  Lemma ty_data_eq (R : ident) ts : R = "Ref" -> TData "Ref" ts = TData R ts.
  Proof. intros ->; reflexivity. Qed.

  (** *** [for .. in] *)

  Lemma fsrc_cast L Γ s s' e1 e2 it :
    s = s' -> Γ ⊩ˢ[E;L] s ⇝ e1 ; e2 ; it -> Γ ⊩ˢ[E;L] s' ⇝ e1 ; e2 ; it.
  Proof. intros ->; auto. Qed.

  Definition array_src (rec : elab_ty_t) (p : pos) (L : cenv) (Γ : lctx) (src : sexpr)
      (Hr : range_of src = None) :
      result {e1 : expr & {e2 : expr & {it : iter_src | Γ ⊩ˢ[E;L] src ⇝ e1 ; e2 ; it}}} elab_error :=
    '(existT _ τ (exist _ a Ha)) <- rec src L Γ Syn ;;
    match τ as t return Γ ⊩[E;L] src ⇒ t ⇝ a ->
                        result {e1 : expr & {e2 : expr & {it : iter_src | Γ ⊩ˢ[E;L] src ⇝ e1 ; e2 ; it}}} elab_error with
    | TArray k t => fun Ha =>
        Ok (existT _ a (existT _ _ (exist _ (IArray k t) (Fs_Array E L Γ src k t a Hr Ha))))
    | t => fun _ => Err (EE_NoMethod p "iter" t)
    end Ha.

  Definition fsrc_dec (rec : elab_ty_t) (p : pos) (L : cenv) (Γ : lctx) (src : sexpr) :
      result {e1 : expr & {e2 : expr & {it : iter_src | Γ ⊩ˢ[E;L] src ⇝ e1 ; e2 ; it}}} elab_error :=
    match src as s0 return s0 = src ->
          result {e1 : expr & {e2 : expr & {it : iter_src | Γ ⊩ˢ[E;L] src ⇝ e1 ; e2 ; it}}} elab_error with
    | SInfix q op lo hi => fun Heq =>
        match range_op op as r return range_op op = r ->
              result {e1 : expr & {e2 : expr & {it : iter_src | Γ ⊩ˢ[E;L] src ⇝ e1 ; e2 ; it}}} elab_error with
        | Some rk => fun Hr =>
            '(existT _ τ (exist _ lo' Hlo)) <- rec lo L Γ Syn ;;
            match τ as t return Γ ⊩[E;L] lo ⇒ t ⇝ lo' ->
                  result {e1 : expr & {e2 : expr & {it : iter_src | Γ ⊩ˢ[E;L] src ⇝ e1 ; e2 ; it}}} elab_error with
            | TBase (BInt kk) => fun Hlo =>
                '(exist _ hi' Hhi) <- cres (rec hi L ((None, TInt kk) :: Γ) (Chk (TInt kk))) ;;
                Ok (existT _ lo' (existT _ hi' (exist _ (IRange rk kk)
                      (fsrc_cast L Γ _ _ _ _ _ Heq (Fs_Range E L Γ q op lo hi rk kk lo' hi' Hr Hlo Hhi)))))
            | t => fun _ => Err (EE_NoOperator q op t)
            end Hlo
        | None => fun Hr =>
            array_src rec p L Γ src (eq_ind (SInfix q op lo hi) (fun s1 => range_of s1 = None) Hr src Heq)
        end eq_refl
    | s0 => fun Heq => array_src rec p L Γ src (eq_ind s0 (fun s1 => range_of s1 = None) eq_refl src Heq)
    end eq_refl.

  Definition fi_pat_dec (p : pos) (it : iter_src) (τs : list ty) (pats : list spat) :
      result {q : pat & {Δ : lctx & {scrut : expr & {sty : ty |
                fi_pat E it pats (fi_elem it (fi_n it τs)) q Δ scrut sty}}}} elab_error :=
    match pats as ps0 return result {q : pat & {Δ : lctx & {scrut : expr & {sty : ty |
                fi_pat E it ps0 (fi_elem it (fi_n it τs)) q Δ scrut sty}}}} elab_error with
    | [sp] =>
        '(existT _ q (exist _ Δ H)) <- epat sp (fi_elem_ty it) ;;
        Ok (existT _ q (existT _ Δ (existT _ _ (exist _ _ (FIP_One E it sp _ q Δ H)))))
    | [sp1; sp2] =>
        match it as i0 return it = i0 ->
              result {q : pat & {Δ : lctx & {scrut : expr & {sty : ty |
                fi_pat E it [sp1; sp2] (fi_elem it (fi_n it τs)) q Δ scrut sty}}}} elab_error with
        | IArray k t => fun Hit =>
            '(existT _ q1 (exist _ Δ1 H1)) <- epat sp1 TIndex ;;
            '(existT _ q2 (exist _ Δ2 H2)) <- epat sp2 t ;;
            Ok (existT _ _ (existT _ _ (existT _ _ (exist _ _
                  (FIP_Two E it k t sp1 sp2 _ q1 q2 Δ1 Δ2 Hit H1 H2)))))
        | _ => fun _ => Err (EE_PatType p (fi_elem_ty it))
        end eq_refl
    | _ => Err (EE_PatType p (fi_elem_ty it))
    end.

  (** *** Errors *)

  Lemma try_err_one cases T : catch_of E cases = CIOne T -> try_err E cases (TData T []).
  Proof. unfold try_err; intros ->; reflexivity. Qed.

  Lemma try_err_many cases : catch_of E cases = CIMany -> try_err E cases TError.
  Proof. unfold try_err; intros ->; reflexivity. Qed.

  Lemma try_err_none cases : catch_of E cases = CINone -> try_err E cases TError.
  Proof. unfold try_err; intros ->; left; reflexivity. Qed.

  Lemma try_err_owner cases T : catch_of E cases = CINone -> err_type E T -> try_err E cases (TData T []).
  Proof. unfold try_err; intros -> H; right; eauto. Qed.

  (** The error types the body elaborates with. *)
  Definition try_cands (rec : elab_ty_t) (p : pos) (L : cenv) (Γ : lctx) (body : sexpr) (bm : mode) :
      list ident -> list {T : ident & (err_type E T * out (set_exn (TData T []) L) Γ body bm)%type} :=
    fix go Ts :=
      match Ts with
      | [] => []
      | T :: Ts' =>
          match err_dec p T, rec body (set_exn (TData T []) L) Γ bm with
          | Ok H, Ok o => existT _ T (H, o) :: go Ts'
          | _, _ => go Ts'
          end
      end.

  (** The body of [try .. catch], with its error type. *)
  Definition try_pick (rec : elab_ty_t) (p : pos) (L : cenv) (Γ : lctx) (cases : list (spat * sexpr))
      (body : sexpr) (bm : mode) :
      result {τe : ty & (try_err E cases τe * out (set_exn τe L) Γ body bm)%type} elab_error :=
    match catch_of E cases as ci
          return catch_of E cases = ci ->
                 result {τe : ty & (try_err E cases τe * out (set_exn τe L) Γ body bm)%type} elab_error with
    | CIOne T => fun H =>
        o <- rec body (set_exn (TData T []) L) Γ bm ;;
        Ok (existT _ (TData T []) (try_err_one cases T H, o))
    | CIMany => fun H =>
        o <- rec body (set_exn TError L) Γ bm ;;
        Ok (existT _ TError (try_err_many cases H, o))
    | CINone => fun H =>
        match try_cands rec p L Γ body bm (map td_name (filter td_err (ge_types hdr))) with
        | [existT _ T (He, o)] => Ok (existT _ (TData T []) (try_err_owner cases T H He, o))
        | _ =>
            o <- rec body (set_exn TError L) Γ bm ;;
            Ok (existT _ TError (try_err_none cases H, o))
        end
    end eq_refl.

  Definition failure_ok_dec (p : pos) : result (failure_ok E) elab_error :=
    '(exist _ td Htd) <- of_option (lookup_ty hdr "Failure") (EE_UnknownType p "Failure") ;;
    match Nat.eq_dec (td_tparams td) 0 with
    | left Hn =>
        '(exist _ cd Hc) <- of_option (lookup_ctor td "Failure") (EE_UnknownCtor p "Failure") ;;
        match list_eq_dec ty_eq_dec (cd_fields cd) [TString] with
        | left Hf => Ok (ex_intro _ td (ex_intro _ cd (conj Htd (conj Hn (conj Hc Hf)))))
        | right _ => Err (EE_UnknownType p "Failure")
        end
    | right _ => Err (EE_UnknownType p "Failure")
    end.

  Lemma fail_syn L Γ p q g a a' v :
    g = "fail" -> builtin E Γ g -> failure_ok E -> Γ ⊩[E;L] a ⇐ TString ⇝ a' ->
    ⊩ᶜ[E;Γ] fail_val a' : TData "Failure" [] ≼ ce_exn L ⇝ v ->
    Γ ⊩[E;L] SApp p (SVar q g) [a] ⇒ TUnit ⇝ ERaise v TUnit.
  Proof. intros ->; apply S_Fail. Qed.

  Lemma fail_chk L Γ p q g a τ a' v :
    g = "fail" -> builtin E Γ g -> failure_ok E -> Γ ⊩[E;L] a ⇐ TString ⇝ a' ->
    ⊩ᶜ[E;Γ] fail_val a' : TData "Failure" [] ≼ ce_exn L ⇝ v ->
    Γ ⊩[E;L] SApp p (SVar q g) [a] ⇐ τ ⇝ ERaise v τ.
  Proof. intros ->; apply C_Fail. Qed.

  Lemma trynr_syn L Γ p body cases ncs τe τ0 τ b hbs kbs :
    try_err E cases τe ->
    Γ ⊩[E;set_exn τe L] body ⇒ τ0 ⇝ b ->
    (exists sp h, pick_arm cases = Some (sp, h) /\ arm_syn L ((None, τe) :: Γ) τe sp h τ) ->
    (None, τe) :: Γ ⊩ᵇ[E;L] cases : τe ⇐ τ ⇝ hbs ->
    (None, τ0) :: Γ ⊩ᵇ[E;L] ncs : τ0 ⇐ τ ⇝ kbs ->
    Γ ⊩[E;L] STry p body cases (Some ncs) ⇒ τ
      ⇝ ETry b τe (EMatch (EVar 0) τ hbs) (EMatch (EVar 0) τ kbs).
  Proof. intros Ht Hb (sp & h & Hp & q & Δ & h' & Hq & Hh) Hc Hk; eapply S_TryNr; eauto. Qed.

  (** *** Trait and method calls *)

  Lemma some_inj {A} (a b : A) : Some a = Some b -> a = b.
  Proof. intros H; injection H; auto. Qed.

  Lemma none_some {A} (a : A) (P : Prop) : None = Some a -> P.
  Proof. discriminate. Qed.

  Lemma qt_trait T mn ti τs : find_trait (trs E) T = Some ti -> qual_trait E T mn T τs.
  Proof. unfold qual_trait; intros ->; reflexivity. Qed.

  Lemma qt_param T mn i Tr :
    find_trait (trs E) T = None -> index_of T (se_tps E) = Some i ->
    hd_error (filter (declares E mn) (asm_traits E (TVar i))) = Some Tr -> qual_trait E T mn Tr (TVar i).
  Proof. unfold qual_trait; intros -> -> H; auto. Qed.

  Lemma qt_any T mn Tr τs :
    find_trait (trs E) T = None -> index_of T (se_tps E) = None ->
    filter (declares E mn) (map ti_name (trs E)) = [Tr] -> qual_trait E T mn Tr τs.
  Proof. unfold qual_trait; intros -> -> H; exact H. Qed.

  Definition qual_trait_dec (q : pos) (T mn : ident) :
      result {Tr : ident & {os : option ty | forall τs, (forall t, os = Some t -> τs = t) ->
                                             qual_trait E T mn Tr τs}} elab_error :=
    match find_trait (trs E) T as o
          return find_trait (trs E) T = o ->
                 result {Tr : ident & {os : option ty | forall τs, (forall t, os = Some t -> τs = t) ->
                                                        qual_trait E T mn Tr τs}} elab_error with
    | Some ti => fun H1 => Ok (existT _ T (exist _ None (fun τs _ => qt_trait T mn ti τs H1)))
    | None => fun H1 =>
        match index_of T (se_tps E) as o
              return index_of T (se_tps E) = o ->
                     result {Tr : ident & {os : option ty | forall τs, (forall t, os = Some t -> τs = t) ->
                                                            qual_trait E T mn Tr τs}} elab_error with
        | Some i => fun H2 =>
            match hd_error (filter (declares E mn) (asm_traits E (TVar i))) as h
                  return hd_error (filter (declares E mn) (asm_traits E (TVar i))) = h ->
                         result {Tr : ident & {os : option ty | forall τs, (forall t, os = Some t -> τs = t) ->
                                                                qual_trait E T mn Tr τs}} elab_error with
            | Some Tr => fun H3 =>
                Ok (existT _ Tr (exist _ (Some (TVar i))
                      (fun (τs : ty) (Hs : forall t, Some (TVar i) = Some t -> τs = t) =>
                         eq_ind_r (fun u => qual_trait E T mn Tr u)
                                  (qt_param T mn i Tr H1 H2 H3) (Hs (TVar i) eq_refl))))
            | None => fun _ => Err (EE_NoMethod q mn (TVar i))
            end eq_refl
        | None => fun H2 =>
            match filter (declares E mn) (map ti_name (trs E)) as l
                  return filter (declares E mn) (map ti_name (trs E)) = l ->
                         result {Tr : ident & {os : option ty | forall τs, (forall t, os = Some t -> τs = t) ->
                                                                qual_trait E T mn Tr τs}} elab_error with
            | [Tr] => fun H3 => Ok (existT _ Tr (exist _ None (fun τs _ => qt_any T mn Tr τs H1 H2 H3)))
            | [] => fun _ => Err (EE_NoMethod q mn TUnit)
            | _ => fun _ => Err (EE_AmbiguousMethod q mn)
            end eq_refl
        end eq_refl
    end eq_refl.

  (** The first argument, already synthesized (it gave [Self]). *)
  Definition pre_t (L : cenv) (Γ : lctx) (args : list sexpr) : Type :=
    {t : ty & {e : expr | forall a0 rest, args = a0 :: rest -> Γ ⊩[E;L] a0 ⇒ t ⇝ e}}.

  Lemma pre_intro L Γ a0 rest t e :
    Γ ⊩[E;L] a0 ⇒ t ⇝ e -> forall b0 rest', a0 :: rest = b0 :: rest' -> Γ ⊩[E;L] b0 ⇒ t ⇝ e.
  Proof. intros H b0 rest' Heq; injection Heq as <- _; exact H. Qed.

  (** [Self] of a trait method call: given, or the type of the first
      argument if the method takes [Self] first, or the expected type if it
      returns [Self]. *)
  Definition tself (rec : elab_ty_t) (q : pos) (L : cenv) (Γ : lctx) (os : option ty) (sg : msig)
      (args : list sexpr) (hm : option ty) :
      result {τs : ty & {pre : option (pre_t L Γ args) | forall t, os = Some t -> τs = t}} elab_error :=
    match os as o return result {τs : ty & {pre : option (pre_t L Γ args) | forall t, o = Some t -> τs = t}}
                                elab_error with
    | Some t => Ok (existT _ t (exist _ None (fun t' H => some_inj t t' H)))
    | None =>
        match ms_params sg, args as a
              return result {τs : ty & {pre : option (pre_t L Γ a) | forall t, None = Some t -> τs = t}}
                            elab_error with
        | TVar 0 :: _, a0 :: rest =>
            '(existT _ t (exist _ e H)) <- rec a0 L Γ Syn ;;
            Ok (existT _ t (exist _ (Some (existT _ t (exist _ e (pre_intro L Γ a0 rest t e H))))
                                  (fun t' Hn => none_some t' _ Hn)))
        | _, _ =>
            match ms_ret sg, hm with
            | TVar 0, Some t => Ok (existT _ t (exist _ None (fun t' Hn => none_some t' _ Hn)))
            | _, _ => Err (EE_CannotInfer q (ms_name sg))
            end
        end
    end.

  Definition pre_args (rec : elab_ty_t) (p : pos) (L : cenv) (Γ : lctx) (args : list sexpr)
      (pre : option (pre_t L Γ args)) (ps : list ty) :
      result {es | Γ ⊩*[E;L] args ⇐ ps ⇝ es} elab_error :=
    match args as a return option (pre_t L Γ a) -> result {es | Γ ⊩*[E;L] a ⇐ ps ⇝ es} elab_error with
    | a0 :: rest => fun pre =>
        match pre with
        | Some (existT _ t (exist _ e0 H0)) =>
            match ps as l return result {es | Γ ⊩*[E;L] a0 :: rest ⇐ l ⇝ es} elab_error with
            | p0 :: ps' =>
                match ty_eq_dec t p0 with
                | left Ht =>
                    '(exist _ es Hes) <- chk_list p L Γ (fun s' τ' => cres (rec s' L Γ (Chk τ'))) rest ps' ;;
                    Ok (exist _ (e0 :: es)
                          (Cs_cons E L Γ a0 rest p0 ps' e0 es
                             (C_Sub E L Γ a0 t p0 e0 e0 (H0 a0 rest eq_refl)
                                (eq_ind t (fun u => ⊩ᶜ[E;Γ] e0 : t ≼ u ⇝ e0) (Co_Refl E Γ e0 t) p0 Ht)) Hes))
                | right _ => Err (EE_Annot p p0 t)
                end
            | [] => Err (EE_Type p (E_ArgArity 0 (List.length (a0 :: rest))))
            end
        | None => chk_list p L Γ (fun s' τ' => cres (rec s' L Γ (Chk τ'))) (a0 :: rest) ps
        end
    | [] => fun _ => chk_list p L Γ (fun s' τ' => cres (rec s' L Γ (Chk τ'))) [] ps
    end pre.

  (** [Tr::m(..)], [X::m(..)]: a trait method. *)
  Definition tcall (rec : elab_ty_t) (p q : pos) (L : cenv) (Γ : lctx) (f : sexpr) (T mn : ident)
      (args : list sexpr) (Hf : f = SQual q T mn) (Hqb : qual_builtin T mn (List.length args) = false)
      (Hm : has_meth E T mn = false) (hm : option ty) : result (sout L Γ (SApp p f args)) elab_error :=
    '(existT _ Tr (exist _ os Hq)) <- qual_trait_dec q T mn ;;
    '(exist _ ti Hti) <- of_option (find_trait (trs E) Tr) (EE_NoMethod q mn TUnit) ;;
    '(exist _ (i, sg) Hmi) <- of_option (method_of ti mn) (EE_NoMethod q mn TUnit) ;;
    '(existT _ τs (exist _ pre Hpre)) <- tself rec q L Γ os sg args hm ;;
    '(exist _ d Hd) <- dict_dec q Γ Tr τs ;;
    '(exist _ (mv, t) Hp) <- field_proj_dec q Tr [τs] i d ;;
    match t as t0 return field_proj E Tr [τs] i d = Some (mv, t0) -> result (sout L Γ (SApp p f args)) elab_error with
    | TArrow ps r ε => fun Hp =>
        '(exist _ es Hes) <- pre_args rec p L Γ args pre ps ;;
        Hok <- allowed_dec p ε (ce_exn L) ;;
        Ok (existT _ _ (exist _ _ (syn_cast L Γ _ _ _ _ (qual_eq p f q T T mn mn args Hf eq_refl eq_refl)
              (S_TCall E L Γ p q T mn args Tr τs ti i sg d mv ps r ε es Hqb Hm (Hq τs Hpre) Hti Hmi Hd Hp Hes Hok))))
    | t0 => fun _ => Err (EE_Type q (E_NotFunction t0))
    end Hp.

  (** [T::m(..)]: a method [fn T::m], or a trait method. *)
  Definition qcall (rec : elab_ty_t) (p q : pos) (L : cenv) (Γ : lctx) (f : sexpr) (T mn : ident)
      (args : list sexpr) (Hf : f = SQual q T mn) (Hqb : qual_builtin T mn (List.length args) = false)
      (hm : option ty) : result (sout L Γ (SApp p f args)) elab_error :=
    match has_meth E T mn as b return has_meth E T mn = b -> result (sout L Γ (SApp p f args)) elab_error with
    | true => fun Hm =>
        '(exist _ fd Hfd) <- of_option (lookup_fn hdr (meth_name T mn)) (EE_Unbound q (meth_name T mn)) ;;
        let n := nbounds E (meth_name T mn) in
        let st0 := match hm with
                   | Some t => tmatch (fd_ret fd) t (repeat None (fd_tparams fd))
                   | None => repeat None (fd_tparams fd)
                   end in
        '(existT _ ts (exist _ es (conj Hts Hes))) <-
          gargs rec p q L Γ args (skipn n (fd_params fd)) (fd_tparams fd) st0 (meth_name T mn) ;;
        '(exist _ ds Hds) <- dicts_dec q Γ (map (tsubst (inst ts)) (firstn n (fd_params fd))) ;;
        Hok <- allowed_dec p (tsubst (inst ts) (fd_eff fd)) (ce_exn L) ;;
        Ok (existT _ _ (exist _ _ (syn_cast L Γ _ _ _ _ (qual_eq p f q T T mn mn args Hf eq_refl eq_refl)
              (S_QualFn E L Γ p q T mn args fd ts ds es Hqb Hm Hfd Hts Hds Hes Hok))))
    | false => fun Hm => tcall rec p q L Γ f T mn args Hf Hqb Hm hm
    end eq_refl.

  (** [x.m(..)]: a method [fn T::m] of the type of [x], a method of a trait
      object, or a trait method. *)
  Definition dcall (rec : elab_ty_t) (p : pos) (L : cenv) (Γ : lctx) (s : sexpr) (mn : ident)
      (args : list sexpr) (τr : ty) (r' : expr) (Hr : Γ ⊩[E;L] s ⇒ τr ⇝ r')
      (Hab : arr_builtin τr mn (List.length args) = false) (hm : option ty) :
      result (sout L Γ (SMethod p s mn args)) elab_error :=
    match meth_fn E τr mn as b return meth_fn E τr mn = b -> result (sout L Γ (SMethod p s mn args)) elab_error with
    | true => fun _ =>
        '(exist _ H Hh) <- of_option (head_name τr) (EE_NoMethod p mn τr) ;;
        Hm <- bcheck (has_meth E H mn) (EE_NoMethod p mn τr) ;;
        '(exist _ fd Hfd) <- of_option (lookup_fn hdr (meth_name H mn)) (EE_Unbound p (meth_name H mn)) ;;
        let n := nbounds E (meth_name H mn) in
        match skipn n (fd_params fd) as l
              return skipn n (fd_params fd) = l -> result (sout L Γ (SMethod p s mn args)) elab_error with
        | p0 :: ps => fun Hs =>
            let st0 := match hm with
                       | Some t => tmatch (fd_ret fd) t (repeat None (fd_tparams fd))
                       | None => repeat None (fd_tparams fd)
                       end in
            '(existT _ ts (exist _ es (conj Hts Hes))) <-
              gargs rec p p L Γ args ps (fd_tparams fd) (tmatch p0 τr st0) (meth_name H mn) ;;
            match ty_eq_dec (tsubst (inst ts) p0) τr with
            | left Hp0 =>
                '(exist _ ds Hds) <- dicts_dec p Γ (map (tsubst (inst ts)) (firstn n (fd_params fd))) ;;
                Hok <- allowed_dec p (tsubst (inst ts) (fd_eff fd)) (ce_exn L) ;;
                Ok (existT _ _ (exist _ _ (S_MethFn E L Γ p s mn args τr r' H fd ts p0 ps ds es
                                             Hr Hab Hh Hm Hfd Hts Hs Hp0 Hds Hes Hok)))
            | right _ => Err (EE_Annot p (tsubst (inst ts) p0) τr)
            end
        | [] => fun _ => Err (EE_Type p (E_ArgArity 0 (List.length args)))
        end eq_refl
    | false => fun Hmf =>
        match obj_of E τr as o return obj_of E τr = o -> result (sout L Γ (SMethod p s mn args)) elab_error with
        | Some Tr => fun Ho =>
            '(exist _ j Hj) <- of_option (obj_index (obj_fields (trs E) Tr) mn) (EE_NoMethod p mn τr) ;;
            '(exist _ (fv, t) Hp) <- field_proj_dec p (obj_name Tr) [] j r' ;;
            match t as t0 return field_proj E (obj_name Tr) [] j r' = Some (fv, t0) ->
                                 result (sout L Γ (SMethod p s mn args)) elab_error with
            | TArrow ps r ε => fun Hp =>
                '(exist _ es Hes) <- chk_list p L Γ (fun s' τ' => cres (rec s' L Γ (Chk τ'))) args ps ;;
                Hok <- allowed_dec p ε (ce_exn L) ;;
                Ok (existT _ _ (exist _ _ (S_MethObj E L Γ p s mn args τr r' Tr j fv ps r ε es
                                             Hr Hmf Ho Hj Hp Hes Hok)))
            | t0 => fun _ => Err (EE_Type p (E_NotFunction t0))
            end Hp
        | None => fun Ho =>
            Hdt <- bcheck (dot_traits τr) (EE_NoMethod p mn τr) ;;
            match dot_trait E Γ mn τr as l
                  return dot_trait E Γ mn τr = l -> result (sout L Γ (SMethod p s mn args)) elab_error with
            | [Tr] => fun Hdl =>
                '(exist _ ti Hti) <- of_option (find_trait (trs E) Tr) (EE_NoMethod p mn τr) ;;
                '(exist _ (i, sg) Hmi) <- of_option (method_of ti mn) (EE_NoMethod p mn τr) ;;
                '(exist _ d Hd) <- dict_dec p Γ Tr τr ;;
                '(exist _ (mv, t) Hp) <- field_proj_dec p Tr [τr] i d ;;
                match t as t0 return field_proj E Tr [τr] i d = Some (mv, t0) ->
                                     result (sout L Γ (SMethod p s mn args)) elab_error with
                | TArrow (p0 :: ps) r ε => fun Hp =>
                    match ty_eq_dec p0 τr with
                    | left Hp0 =>
                        '(exist _ es Hes) <- chk_list p L Γ (fun s' τ' => cres (rec s' L Γ (Chk τ'))) args ps ;;
                        Hok <- allowed_dec p ε (ce_exn L) ;;
                        Ok (existT _ _ (exist _ _ (S_MethTrait E L Γ p s mn args τr r' Tr ti i sg d mv ps r ε es
                              Hr Hmf Ho Hdt Hdl Hti Hmi Hd
                              (eq_ind p0 (fun u => field_proj E Tr [τr] i d = Some (mv, TArrow (u :: ps) r ε))
                                      Hp τr Hp0) Hes Hok)))
                    | right _ => Err (EE_Annot p τr p0)
                    end
                | t0 => fun _ => Err (EE_Type p (E_NotFunction t0))
                end Hp
            | [] => fun _ => Err (EE_NoMethod p mn τr)
            | _ => fun _ => Err (EE_AmbiguousMethod p mn)
            end eq_refl
        end eq_refl
    end eq_refl.

  (** ** Heads of calls *)

  Inductive head (Γ : lctx) (f : sexpr) : Type :=
  | HName (q : pos) (g : ident) (Hf : f = SVar q g) (Hl : lookup_local g Γ = None)
  | HExpr (H : callee Γ f)
  | HCtor (q : pos) (tq : option ident) (c : ident) (Hf : f = SConstr q tq c)
  | HQual (q : pos) (T m : ident) (Hf : f = SQual q T m)
  | HOther.

  Definition head_of (Γ : lctx) (f : sexpr) : head Γ f :=
    match f as f0 return head Γ f0 with
    | SVar q g =>
        match lookup_local g Γ as o return lookup_local g Γ = o -> head Γ (SVar q g) with
        | None => fun H => HName Γ (SVar q g) q g eq_refl H
        | Some i => fun H => HExpr Γ (SVar q g) (some_not_none _ i H)
        end eq_refl
    | SConstr q tq c => HCtor Γ (SConstr q tq c) q tq c eq_refl
    | SQual q T m => HQual Γ (SQual q T m) q T m eq_refl
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
                    '(exist _ e H) <- cres (lit_m q L Γ (SLInt k (Z.opp z)) (Chk τ)) ;;
                    Okc (exist _ e (neg_lit_chk L Γ p op a q k z τ e Hop Ha H))
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
                  ('(exist _ a' Ha) <- cres (elab a L Γ (Chk TBool)) ;;
                   Ok (existT _ _ (exist _ _ (not_syn L Γ p op a a' Hop Ha))))
            | right _ => Err (EE_NoOperator p op TUnit)
            end
        end
    | SInfix p op a b =>
        match string_dec op "&&" with
        | left Hop =>
            fin p L Γ (SInfix p op a b) m
              ('(exist _ a' Ha) <- cres (elab a L Γ (Chk TBool)) ;;
               '(exist _ b' Hb) <- cres (elab b L Γ (Chk TBool)) ;;
               Ok (existT _ _ (exist _ _ (and_syn L Γ p op a b a' b' Hop Ha Hb))))
        | right _ =>
        match string_dec op "||" with
        | left Hop =>
            fin p L Γ (SInfix p op a b) m
              ('(exist _ a' Ha) <- cres (elab a L Γ (Chk TBool)) ;;
               '(exist _ b' Hb) <- cres (elab b L Γ (Chk TBool)) ;;
               Ok (existT _ _ (exist _ _ (or_syn L Γ p op a b a' b' Hop Ha Hb))))
        | right _ =>
            let bin_syn :=
              match (flexible a && negb (flexible b))%bool as c
                    return (flexible a && negb (flexible b))%bool = c ->
                           result (sout L Γ (SInfix p op a b)) elab_error with
              | false => fun Hc =>
                  '(existT _ τ (exist _ a' Ha)) <- elab a L Γ Syn ;;
                  '(exist _ b' Hb) <- cres (elab b L Γ (Chk τ)) ;;
                  '(exist _ e He) <- binop_dec p op τ a' b' ;;
                  Ok (existT _ _ (exist _ _ (S_BinL E L Γ p op a b τ a' b' e Hc Ha Hb He)))
              | true => fun Hc =>
                  '(existT _ τ (exist _ b' Hb)) <- elab b L Γ Syn ;;
                  '(exist _ a' Ha) <- cres (elab a L Γ (Chk τ)) ;;
                  '(exist _ e He) <- binop_dec p op τ a' b' ;;
                  Ok (existT _ _ (exist _ _ (binr_syn L Γ p op a b τ a' b' e Hc Hb Ha He)))
              end eq_refl in
            match m as m0 return result (out L Γ (SInfix p op a b) m0) elab_error with
            | Syn => bin_syn
            | Chk τ =>
                match assoc op arith_ops, ty_eq_dec (binop_res op τ) τ with
                | Some _, left Hr =>
                    '(exist _ a' Ha) <- cres (elab a L Γ (Chk τ)) ;;
                    '(exist _ b' Hb) <- cres (elab b L Γ (Chk τ)) ;;
                    '(exist _ e He) <- binop_dec p op τ a' b' ;;
                    Okc (exist _ e (C_Bin E L Γ p op a b τ a' b' e Hr Ha Hb He))
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
               '(exist _ e H) <- cres (elab s1 L Γ (Chk τ)) ;;
               Ok (existT _ τ (exist _ e (B_Ann E L Γ s1 t τ e Ht H)))
           end) ;;
        match m as m0 return result (out L Γ (SLet p x ann s1 s2) m0) elab_error with
        | Syn =>
            '(existT _ τ (exist _ e2 H2)) <- elab s2 L ((x, τ1) :: Γ) Syn ;;
            Ok (existT _ τ (exist _ _ (S_Let E L Γ p x ann s1 s2 τ1 τ e1 e2 H1 H2)))
        | Chk τ =>
            '(exist _ e2 H2) <- cres (elab s2 L ((x, τ1) :: Γ) (Chk τ)) ;;
            Okc (exist _ _ (C_Let E L Γ p x ann s1 s2 τ1 τ e1 e2 H1 H2))
        end
    | SAnnot p s0 t =>
        fin p L Γ (SAnnot p s0 t) m
          ('(exist _ τ Ht) <- ety_dec t ;;
           '(exist _ e H) <- cres (elab s0 L Γ (Chk τ)) ;;
           Ok (existT _ τ (exist _ e (S_Annot E L Γ p s0 t τ e Ht H))))
    | SIf p c t oe =>
        '(exist _ c' Hc) <- cres (elab c L Γ (Chk TBool)) ;;
        match oe as o return result (out L Γ (SIf p c t o) m) elab_error with
        | None =>
            fin p L Γ (SIf p c t None) m
              ('(exist _ t' Ht) <- cres (elab t L Γ (Chk TUnit)) ;;
               Ok (existT _ _ (exist _ _ (S_If1 E L Γ p c t c' t' Hc Ht))))
        | Some f =>
            match m as m0 return result (out L Γ (SIf p c t (Some f)) m0) elab_error with
            | Chk τ =>
                '(exist _ t' Ht) <- cres (elab t L Γ (Chk τ)) ;;
                '(exist _ f' Hf) <- cres (elab f L Γ (Chk τ)) ;;
                Okc (exist _ _ (C_If E L Γ p c t f τ c' t' f' Hc Ht Hf))
            | Syn =>
                match (diverges t && negb (diverges f))%bool as d
                      return (diverges t && negb (diverges f))%bool = d ->
                             result (sout L Γ (SIf p c t (Some f))) elab_error with
                | false => fun Hd =>
                    '(existT _ τ (exist _ t' Ht)) <- elab t L Γ Syn ;;
                    '(exist _ f' Hf) <- cres (elab f L Γ (Chk τ)) ;;
                    Ok (existT _ τ (exist _ _ (S_If E L Γ p c t f τ c' t' f' Hd Hc Ht Hf)))
                | true => fun Hd =>
                    '(existT _ τ (exist _ f' Hf)) <- elab f L Γ Syn ;;
                    '(exist _ t' Ht) <- cres (elab t L Γ (Chk τ)) ;;
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
                  '(exist _ es Hs) <- chk_list p L Γ (fun s' τ' => cres (elab s' L Γ (Chk τ'))) ss ts ;;
                  Okc (exist _ _ (C_Tuple E L Γ p ss ts es Hs))
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
           | TData T ts => fun H =>
               '(exist _ (e', τ) Hf) <- field_proj_dec p T ts i e ;;
               Ok (existT _ τ (exist _ e' (S_ProjData E L Γ p s0 i T ts e e' τ H Hf)))
           | t => fun _ => Err (EE_Type p (E_NotTuple t))
           end H)
    | SLam p ps ret a body =>
        let syn_l :=
          '(exist _ τs Hps) <- params_syn_dec p ps ;;
          '(exist _ ε Hε) <- eff_syn_dec a ;;
          match ret as r0 return result (sout L Γ (SLam p ps r0 a body)) elab_error with
          | Some t =>
              '(exist _ r Hr) <- ety_dec t ;;
              '(exist _ b Hb) <- cres (elab body (fun_env r ε) (List.app (lam_ctx ps τs) Γ) (Chk r)) ;;
              Ok (existT _ _ (exist _ _ (S_LamRet E L Γ p ps t a body τs r ε b (params_syn_ann E ps τs Hps) Hr Hε Hb)))
          | None =>
              '(existT _ r (exist _ b Hb)) <- elab body (mk_cenv [] ε) (List.app (lam_ctx ps τs) Γ) Syn ;;
              Ok (existT _ _ (exist _ _ (S_Lam E L Γ p ps a body τs r ε b (params_syn_ann E ps τs Hps) Hε Hb)))
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
                  '(exist _ b Hb) <- cres (elab body (fun_env r ε) (List.app (lam_ctx ps τs) Γ) (Chk r)) ;;
                  Okc (exist _ _ (C_Lam E L Γ p ps ret a body τs r ε b Hps Hr Hε Hb))
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
                  (let n := nbounds E g in
                   let st0 := match hint m with
                              | Some t => tmatch (fd_ret fd) t (repeat None (fd_tparams fd))
                              | None => repeat None (fd_tparams fd)
                              end in
                   '(existT _ ts (exist _ es (conj Hts Hes))) <-
                     gargs elab p q L Γ args (skipn n (fd_params fd)) (fd_tparams fd) st0 g ;;
                   '(exist _ ds Hds) <- dicts_dec q Γ (map (tsubst (inst ts)) (firstn n (fd_params fd))) ;;
                   Hok <- allowed_dec p (tsubst (inst ts) (fd_eff fd)) (ce_exn L) ;;
                   Ok (existT _ _ (exist _ _
                         (app_syn L Γ p f q g args _ _ Hf
                            (S_Call E L Γ p q g args fd ts ds es Hl Hfd Hts Hds Hes Hok)))))
            | None => fun Hfd =>
                let Hbi : builtin E Γ g := conj Hl Hfd in
                match string_dec g "not", args as a0
                      return result (out L Γ (SApp p f a0) m) elab_error with
                | left Hg, [a] =>
                    fin p L Γ (SApp p f [a]) m
                      ('(exist _ a' Ha) <- cres (elab a L Γ (Chk TBool)) ;;
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
                    | Chk τ => Okc (exist _ _ (app_chk L Γ p f q g [] _ _ Hf
                                                (panic_chk L Γ p q g τ Hg Hbi)))
                    end
                | _, a2 =>
                match string_dec g "abort", a2 as a3
                      return result (out L Γ (SApp p f a3) m) elab_error with
                | left Hg, [a] =>
                    '(exist _ a' Ha) <- cres (elab a L Γ (Chk TString)) ;;
                    match m as m0 return result (out L Γ (SApp p f [a]) m0) elab_error with
                    | Syn => Ok (existT _ _ (exist _ _ (app_syn L Γ p f q g [a] _ _ Hf
                                                          (abort_syn L Γ p q g a a' Hg Hbi Ha))))
                    | Chk τ => Okc (exist _ _ (app_chk L Γ p f q g [a] _ _ Hf
                                                (abort_chk L Γ p q g a a' τ Hg Hbi Ha)))
                    end
                | _, a3 =>
                match string_dec g "fail", a3 as a4
                      return result (out L Γ (SApp p f a4) m) elab_error with
                | left Hg, [a] =>
                    Hfo <- failure_ok_dec q ;;
                    '(exist _ a' Ha) <- cres (elab a L Γ (Chk TString)) ;;
                    '(exist _ v Hv) <- coerce q Γ (fail_val a') (TData "Failure" []) (ce_exn L) ;;
                    match m as m0 return result (out L Γ (SApp p f [a]) m0) elab_error with
                    | Syn => Ok (existT _ _ (exist _ _ (app_syn L Γ p f q g [a] _ _ Hf
                                                          (fail_syn L Γ p q g a a' v Hg Hbi Hfo Ha Hv))))
                    | Chk τ => Okc (exist _ _ (app_chk L Γ p f q g [a] _ _ Hf
                                                (fail_chk L Γ p q g a τ a' v Hg Hbi Hfo Ha Hv)))
                    end
                | _, _ => Err (EE_Unbound q g)
                end
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
                   '(exist _ es Hes) <- chk_list p L Γ (fun s' τ' => cres (elab s' L Γ (Chk τ'))) args ps ;;
                   Hok <- allowed_dec p ε (ce_exn L) ;;
                   Ok (existT _ r (exist _ _ (S_CallExpr E L Γ p f args ps r ε f' es Hc Hf Hes Hok)))
               | t => fun _ => Err (EE_Type p (E_NotFunction t))
               end Hf)
        | HCtor _ _ q tq c Hf =>
            let syn_c :=
              '(exist _ T Hpick) <- ctor_pick_dec q tq c ;;
              '(exist _ td Htd) <- of_option (lookup_ty hdr T) (EE_UnknownType q T) ;;
              '(exist _ cd Hcd) <- of_option (lookup_ctor td c) (EE_UnknownCtor q c) ;;
              let ps := cd_fields cd in
              _ <- bcheck (Nat.eqb (List.length args) (List.length ps))
                          (EE_CtorArity q c (List.length ps) (List.length args)) ;;
              '(exist _ rs1 H1, st1) <- pass1 elab L Γ args ps (repeat None (td_tparams td)) ;;
              '(exist _ rs2 H2, st2) <- pass2 elab L Γ args rs1 H1 ps st1 ;;
              '(exist _ ts Hts) <- targs q c (td_tparams td) st2 ;;
              '(exist _ es Hes) <- finish p L Γ args rs2 H2 (map (tsubst (inst ts)) ps) ;;
              Ok (existT _ _ (exist _ _ (ctor_syn L Γ p f q tq c args T td cd ts es Hf Hpick Htd Hcd Hts Hes))) in
            match m as m0 return result (out L Γ (SApp p f args) m0) elab_error with
            | Syn => syn_c
            | Chk τ =>
                match τ as t0 return result (out L Γ (SApp p f args) (Chk t0)) elab_error with
                | TData T ts =>
                    match lookup_ty hdr T as o return lookup_ty hdr T = o -> result (out L Γ (SApp p f args) (Chk (TData T ts))) elab_error with
                    | Some td => fun Htd =>
                        match lookup_ctor td c as o return lookup_ctor td c = o -> result (out L Γ (SApp p f args) (Chk (TData T ts))) elab_error with
                        | Some cd => fun Hcd =>
                            Htq <- tq_dec q tq T (EE_UnknownCtor q c) ;;
                            Hts <- (match Nat.eq_dec (List.length ts) (td_tparams td) with
                                    | left H => Ok H
                                    | right _ => Err (EE_TypeArgs q T (td_tparams td) (List.length ts))
                                    end) ;;
                            _ <- bcheck (Nat.eqb (List.length args) (List.length (cd_fields cd)))
                                        (EE_CtorArity q c (List.length (cd_fields cd)) (List.length args)) ;;
                            '(exist _ es Hes) <- chk_list p L Γ (fun s' τ' => cres (elab s' L Γ (Chk τ'))) args
                                                   (map (tsubst (inst ts)) (cd_fields cd)) ;;
                            Okc (exist _ _ (ctor_chk L Γ p f q tq c args T ts td cd es Hf Htq Htd Hcd Hts Hes))
                        | None => fun _ => fin p L Γ (SApp p f args) (Chk (TData T ts)) syn_c
                        end eq_refl
                    | None => fun _ => fin p L Γ (SApp p f args) (Chk (TData T ts)) syn_c
                    end eq_refl
                | t0 => fin p L Γ (SApp p f args) (Chk t0) syn_c
                end
            end
        | HQual _ _ q T mn Hf =>
            match qual_builtin T mn (List.length args) as qb
                  return qual_builtin T mn (List.length args) = qb -> result (out L Γ (SApp p f args) m) elab_error with
            | false => fun Hqb => fin p L Γ (SApp p f args) m (qcall elab p q L Γ f T mn args Hf Hqb (hint m))
            | true => fun _ =>
            (* [Ref::new(v)], [Array::make(n, v)], [FixedArray::make(n, v)], [Array::new()] *)
            match string_dec T "Ref", string_dec mn "new", args as a0
                  return result (out L Γ (SApp p f a0) m) elab_error with
            | left HT, left Hm, [v] =>
                let Heq := qual_eq p f q T "Ref" mn "new" [v] Hf HT Hm in
                Hr <- ref_ok_dec q ;;
                match m as m0 return result (out L Γ (SApp p f [v]) m0) elab_error with
                | Chk τ =>
                    let syn_r :=
                      '(existT _ t (exist _ v' Hv)) <- elab v L Γ Syn ;;
                      Ok (existT _ _ (exist _ _ (syn_cast L Γ _ _ _ _ Heq (S_RefNew E L Γ p q v t v' Hr Hv)))) in
                    match τ as t0 return result (out L Γ (SApp p f [v]) (Chk t0)) elab_error with
                    | TData R [t] =>
                        match string_dec R "Ref" with
                        | left HR =>
                            '(exist _ v' Hv) <- cres (elab v L Γ (Chk t)) ;;
                            Okc (exist _ _ (chk_cast L Γ _ _ _ _ _ Heq (ty_data_eq R [t] HR)
                                             (C_RefNew E L Γ p q v t v' Hr Hv)))
                        | right _ => fin p L Γ (SApp p f [v]) (Chk (TData R [t])) syn_r
                        end
                    | t0 => fin p L Γ (SApp p f [v]) (Chk t0) syn_r
                    end
                | Syn =>
                    '(existT _ t (exist _ v' Hv)) <- elab v L Γ Syn ;;
                    Ok (existT _ _ (exist _ _ (syn_cast L Γ _ _ _ _ Heq (S_RefNew E L Γ p q v t v' Hr Hv))))
                end
            | _, _, a0 =>
            match array_kind_of T as ok return array_kind_of T = ok -> result (out L Γ (SApp p f a0) m) elab_error with
            | Some k => fun Hk =>
                match string_dec mn "make", string_dec mn "new", a0 as a1
                      return result (out L Γ (SApp p f a1) m) elab_error with
                | left Hm, _, [n; v] =>
                    let Heq := qual_eq p f q T T mn "make" [n; v] Hf eq_refl Hm in
                    '(exist _ n' Hn) <- cres (elab n L Γ (Chk TIndex)) ;;
                    let syn_m :=
                      '(existT _ t (exist _ v' Hv)) <- elab v L Γ Syn ;;
                      Ok (existT _ _ (exist _ _ (syn_cast L Γ _ _ _ _ Heq (S_Make E L Γ p q T n v k t n' v' Hk Hn Hv)))) in
                    match m as m0 return result (out L Γ (SApp p f [n; v]) m0) elab_error with
                    | Syn => syn_m
                    | Chk τ =>
                        match τ as t0 return result (out L Γ (SApp p f [n; v]) (Chk t0)) elab_error with
                        | TArray k' t =>
                            match array_kind_eq_dec k k' with
                            | left Hkk =>
                                '(exist _ v' Hv) <- cres (elab v L Γ (Chk t)) ;;
                                Okc (exist _ _ (chk_cast L Γ _ _ _ _ _ Heq (f_equal (fun kk => TArray kk t) Hkk)
                                                 (C_Make E L Γ p q T n v k t n' v' Hk Hn Hv)))
                            | right _ => fin p L Γ (SApp p f [n; v]) (Chk (TArray k' t)) syn_m
                            end
                        | t0 => fin p L Γ (SApp p f [n; v]) (Chk t0) syn_m
                        end
                    end
                | _, left Hm, [] =>
                    let Heq := qual_eq p f q T T mn "new" [] Hf eq_refl Hm in
                    match m as m0 return result (out L Γ (SApp p f []) m0) elab_error with
                    | Chk τ =>
                        match τ as t0 return result (out L Γ (SApp p f []) (Chk t0)) elab_error with
                        | TArray k' t =>
                            match array_kind_eq_dec k k' with
                            | left Hkk =>
                                Okc (exist _ _ (chk_cast L Γ _ _ _ _ _ Heq (f_equal (fun kk => TArray kk t) Hkk)
                                                 (C_ArrNew E L Γ p q T k t Hk)))
                            | right _ => Err (EE_CannotInfer q mn)
                            end
                        | _ => Err (EE_CannotInfer q mn)
                        end
                    | Syn => Err (EE_CannotInfer q mn)
                    end
                | _, _, _ => Err (EE_Unsupported p "method call")
                end
            | None => fun _ => Err (EE_Unsupported p "method call")
            end eq_refl
            end
            end eq_refl
        | HOther _ _ => Err (EE_Unsupported p "method call")
        end
    | SConstr p tq c =>
        let syn_c :=
          '(exist _ T Hpick) <- ctor_pick_dec p tq c ;;
          '(exist _ td Htd) <- of_option (lookup_ty hdr T) (EE_UnknownType p T) ;;
          '(exist _ cd Hcd) <- of_option (lookup_ctor td c) (EE_UnknownCtor p c) ;;
          Hnil <- nil_fields p c cd ;;
          '(exist _ ts Hts) <- targs p c (td_tparams td) (repeat None (td_tparams td)) ;;
          Ok (existT _ _ (exist _ _ (S_Ctor0 E L Γ p tq c T td cd ts Hpick Htd Hcd Hts Hnil))) in
        match m as m0 return result (out L Γ (SConstr p tq c) m0) elab_error with
        | Syn => syn_c
        | Chk τ =>
            match τ as t0 return result (out L Γ (SConstr p tq c) (Chk t0)) elab_error with
            | TData T ts =>
                match lookup_ty hdr T as o return lookup_ty hdr T = o -> result (out L Γ (SConstr p tq c) (Chk (TData T ts))) elab_error with
                | Some td => fun Htd =>
                    match lookup_ctor td c as o return lookup_ctor td c = o -> result (out L Γ (SConstr p tq c) (Chk (TData T ts))) elab_error with
                    | Some cd => fun Hcd =>
                        Htq <- tq_dec p tq T (EE_UnknownCtor p c) ;;
                        Hts <- (match Nat.eq_dec (List.length ts) (td_tparams td) with
                                | left H => Ok H
                                | right _ => Err (EE_TypeArgs p T (td_tparams td) (List.length ts))
                                end) ;;
                        Hnil <- nil_fields p c cd ;;
                        Okc (exist _ _ (C_Ctor0 E L Γ p tq c T ts td cd Htq Htd Hcd Hts Hnil))
                    | None => fun _ => fin p L Γ (SConstr p tq c) (Chk (TData T ts)) syn_c
                    end eq_refl
                | None => fun _ => fin p L Γ (SConstr p tq c) (Chk (TData T ts)) syn_c
                end eq_refl
            | t0 => fin p L Γ (SConstr p tq c) (Chk t0) syn_c
            end
        end
    | SRecord p tq fes =>
        let syn_r :=
          '(exist _ T Hpick) <- rec_pick_dec p tq (map fst fes) ;;
          '(exist _ names Hn) <- of_option (assoc T (se_sinfo E)) (EE_NotRecord p (TData T [])) ;;
          '(exist _ td Htd) <- of_option (lookup_ty hdr T) (EE_UnknownType p T) ;;
          '(exist _ cd Hc) <- single_ctor p td (TData T []) ;;
          Hlen <- len_dec p T (List.length (cd_fields cd)) (List.length names) ;;
          '(exist _ ts Hts) <-
            (match td_tparams td as n return td_tparams td = n -> result {ts | List.length ts = td_tparams td} elab_error with
             | 0 => fun H => Ok (exist _ [] (eq_sym H))
             | _ => fun _ =>
                 (* type arguments from the fields, as for a generic call *)
                 st <- rpass elab L Γ names (cd_fields cd) fes (repeat None (td_tparams td)) ;;
                 targs p T (td_tparams td) st
             end eq_refl) ;;
          '(existT _ es (exist _ ixs Hr)) <- rfields_dec elab p L Γ names (map (tsubst (inst ts)) (cd_fields cd)) fes ;;
          '(exist _ vs Hv) <- rec_vars_dec p names ixs ;;
          Ok (existT _ _ (exist _ _ (S_Record E L Γ p tq fes T ts names td cd es ixs vs
                                              Hpick Hn Htd Hc Hts Hlen Hr Hv))) in
        match m as m0 return result (out L Γ (SRecord p tq fes) m0) elab_error with
        | Syn => syn_r
        | Chk τ =>
            match τ as t0 return result (out L Γ (SRecord p tq fes) (Chk t0)) elab_error with
            | TData T ts =>
                match assoc T (se_sinfo E) as o
                      return assoc T (se_sinfo E) = o -> result (out L Γ (SRecord p tq fes) (Chk (TData T ts))) elab_error with
                | Some names => fun Hn =>
                    Htq <- tq_dec p tq T (EE_NotRecord p (TData T ts)) ;;
                    '(exist _ td Htd) <- of_option (lookup_ty hdr T) (EE_UnknownType p T) ;;
                    '(exist _ cd Hc) <- single_ctor p td (TData T ts) ;;
                    Hts <- len_dec p T (List.length ts) (td_tparams td) ;;
                    Hlen <- len_dec p T (List.length (cd_fields cd)) (List.length names) ;;
                    '(existT _ es (exist _ ixs Hr)) <- rfields_dec elab p L Γ names (map (tsubst (inst ts)) (cd_fields cd)) fes ;;
                    '(exist _ vs Hv) <- rec_vars_dec p names ixs ;;
                    Okc (exist _ _ (C_Record E L Γ p tq fes T ts names td cd es ixs vs Htq Hn Htd Hc Hts Hlen Hr Hv))
                | None => fun _ => fin p L Γ (SRecord p tq fes) (Chk (TData T ts)) syn_r
                end eq_refl
            | t0 => fin p L Γ (SRecord p tq fes) (Chk t0) syn_r
            end
        end
    | SLetMut p x ann s1 s2 =>
        '(existT _ τ1 (exist _ e1 H1)) <-
          (match ann as a0 return result {τ & {e | Γ ⊩[E;L] s1 ⦂ a0 ⇒ τ ⇝ e}} elab_error with
           | None =>
               '(existT _ τ (exist _ e H)) <- elab s1 L Γ Syn ;;
               Ok (existT _ τ (exist _ e (B_Syn E L Γ s1 τ e H)))
           | Some t =>
               '(exist _ τ Ht) <- ety_dec t ;;
               '(exist _ e H) <- cres (elab s1 L Γ (Chk τ)) ;;
               Ok (existT _ τ (exist _ e (B_Ann E L Γ s1 t τ e Ht H)))
           end) ;;
        match m as m0 return result (out L Γ (SLetMut p x ann s1 s2) m0) elab_error with
        | Syn =>
            '(existT _ τ (exist _ e2 H2)) <- elab s2 L ((Some x, TRef τ1) :: Γ) Syn ;;
            Ok (existT _ τ (exist _ _ (S_LetMut E L Γ p x ann s1 s2 τ1 τ e1 e2 H1 H2)))
        | Chk τ =>
            '(exist _ e2 H2) <- cres (elab s2 L ((Some x, TRef τ1) :: Γ) (Chk τ)) ;;
            Okc (exist _ _ (C_LetMut E L Γ p x ann s1 s2 τ1 τ e1 e2 H1 H2))
        end
    | SAssign p x op s0 =>
        fin p L Γ (SAssign p x op s0) m
          ('(exist _ i Hl) <- of_option (lookup_local x Γ) (EE_NotMutable p x) ;;
           '(exist _ τc Hn) <- of_option (nth_error (ctx_of Γ) i) (EE_NotMutable p x) ;;
           match τc as t return nth_error (ctx_of Γ) i = Some t -> result (sout L Γ (SAssign p x op s0)) elab_error with
           | TRef τ => fun Hn =>
               '(exist _ v Hv) <- cres (elab s0 L Γ (Chk τ)) ;;
               '(exist _ e He) <- upd_rhs_dec p op τ (EMem (MGet τ) [EVar i]) v ;;
               Ok (existT _ _ (exist _ _ (S_Assign E L Γ p x op s0 i τ v e Hl Hn Hv He)))
           | _ => fun _ => Err (EE_NotMutable p x)
           end Hn)
    | SArray p ss =>
        let syn_a :=
          match ss as l return result (sout L Γ (SArray p l)) elab_error with
          | s0 :: ss' =>
              '(existT _ t (exist _ e H)) <- elab s0 L Γ Syn ;;
              '(exist _ es Hs) <- chk_list p L Γ (fun s' τ' => cres (elab s' L Γ (Chk τ'))) ss' (repeat t (List.length ss')) ;;
              Ok (existT _ _ (exist _ _ (S_Array E L Γ p s0 ss' t e es H Hs)))
          | [] => Err (EE_CannotInfer p "[]")
          end in
        match m as m0 return result (out L Γ (SArray p ss) m0) elab_error with
        | Syn => syn_a
        | Chk τ =>
            match τ as t0 return result (out L Γ (SArray p ss) (Chk t0)) elab_error with
            | TArray k t =>
                '(exist _ es Hs) <- chk_list p L Γ (fun s' τ' => cres (elab s' L Γ (Chk τ'))) ss (repeat t (List.length ss)) ;;
                Okc (exist _ _ (C_Array E L Γ p ss k t es Hs))
            | t0 => fin p L Γ (SArray p ss) (Chk t0) syn_a
            end
        end
    | SIndex p a i =>
        fin p L Γ (SIndex p a i) m
          ('(existT _ τa (exist _ a' Ha)) <- elab a L Γ Syn ;;
           match τa as t return Γ ⊩[E;L] a ⇒ t ⇝ a' -> result (sout L Γ (SIndex p a i)) elab_error with
           | TArray k t => fun Ha =>
               '(exist _ i' Hi) <- cres (elab i L Γ (Chk TIndex)) ;;
               Ok (existT _ _ (exist _ _ (S_Index E L Γ p a i k t a' i' Ha Hi)))
           | t => fun _ => Err (EE_NoMethod p "[]" t)
           end Ha)
    | SIndexSet p a i op v =>
        fin p L Γ (SIndexSet p a i op v) m
          ('(existT _ τa (exist _ a' Ha)) <- elab a L Γ Syn ;;
           match τa as t return Γ ⊩[E;L] a ⇒ t ⇝ a' -> result (sout L Γ (SIndexSet p a i op v)) elab_error with
           | TArray k t => fun Ha =>
               match op as o return result (sout L Γ (SIndexSet p a i o v)) elab_error with
               | None =>
                   '(exist _ i' Hi) <- cres (elab i L Γ (Chk TIndex)) ;;
                   '(exist _ v' Hv) <- cres (elab v L Γ (Chk t)) ;;
                   Ok (existT _ _ (exist _ _ (S_IndexSet E L Γ p a i v k t a' i' v' Ha Hi Hv)))
               | Some o =>
                   '(exist _ i' Hi) <- cres (elab i L ((None, TArray k t) :: Γ) (Chk TIndex)) ;;
                   '(exist _ v' Hv) <- cres (elab v L ((None, TIndex) :: (None, TArray k t) :: Γ) (Chk t)) ;;
                   match ty_eq_dec (binop_res o t) t with
                   | left Hr =>
                       '(exist _ rhs He) <- binop_dec p o t (EMem (MIndex k t) [EVar 1; EVar 0]) v' ;;
                       Ok (existT _ _ (exist _ _ (S_IndexUpd E L Γ p a i o v k t a' i' v' rhs Ha Hi Hv Hr He)))
                   | right _ => Err (EE_NoOperator p o t)
                   end
               end
           | t => fun _ => Err (EE_NoMethod p "[]=" t)
           end Ha)
    | SFieldSet p s0 f op v =>
        fin p L Γ (SFieldSet p s0 f op v) m
          ('(existT _ τ0 (exist _ e H)) <- elab s0 L Γ Syn ;;
           match τ0 as t return Γ ⊩[E;L] s0 ⇒ t ⇝ e -> result (sout L Γ (SFieldSet p s0 f op v)) elab_error with
           | TData T ts => fun H =>
               '(exist _ names Hn) <- of_option (assoc T (se_sinfo E)) (EE_NotRecord p (TData T ts)) ;;
               '(exist _ i Hi) <- of_option (index_of f names) (EE_UnknownField p f) ;;
               '(exist _ (c, n, t) Hc) <- field_cell_dec p f T ts i ;;
               '(exist _ v' Hv) <- cres (elab v L ((None, TRef t) :: Γ) (Chk t)) ;;
               '(exist _ rhs He) <- upd_rhs_dec p op t (EMem (MGet t) [EVar 0]) v' ;;
               Ok (existT _ _ (exist _ _ (S_FieldSet E L Γ p s0 f op v T ts e names i c n t v' rhs H Hn Hi Hc Hv He)))
           | t => fun _ => Err (EE_NotRecord p t)
           end H)
    | SMethod p s0 mn args =>
        fin p L Γ (SMethod p s0 mn args) m
          ('(existT _ τ0 (exist _ e H)) <- elab s0 L Γ Syn ;;
           match arr_builtin τ0 mn (List.length args) as ab
                 return arr_builtin τ0 mn (List.length args) = ab -> result (sout L Γ (SMethod p s0 mn args)) elab_error with
           | false => fun Hab => dcall elab p L Γ s0 mn args τ0 e H Hab (hint m)
           | true => fun _ =>
           match string_dec mn "length", string_dec mn "push", args as a0
                 return result (sout L Γ (SMethod p s0 mn a0)) elab_error with
           | left Hm, _, [] =>
               match τ0 as t return Γ ⊩[E;L] s0 ⇒ t ⇝ e -> result (sout L Γ (SMethod p s0 mn [])) elab_error with
               | TArray k t => fun H =>
                   Ok (existT _ _ (exist _ _ (meth_syn L Γ p s0 mn "length" [] _ _ Hm (S_Length E L Γ p s0 k t e H))))
               | t => fun _ => Err (EE_NoMethod p mn t)
               end H
           | _, left Hm, [a] =>
               match τ0 as t return Γ ⊩[E;L] s0 ⇒ t ⇝ e -> result (sout L Γ (SMethod p s0 mn [a])) elab_error with
               | TArray AGrow t => fun H =>
                   '(exist _ a' Ha) <- cres (elab a L Γ (Chk t)) ;;
                   Ok (existT _ _ (exist _ _ (meth_syn L Γ p s0 mn "push" [a] _ _ Hm (S_Push E L Γ p s0 a t e a' H Ha))))
               | t => fun _ => Err (EE_NoMethod p mn t)
               end H
           | _, _, _ => Err (EE_Unsupported p "method call")
           end
           end eq_refl)
    | SWhile p x c body onb =>
        match onb as o return result (out L Γ (SWhile p x c body o) m) elab_error with
        | None =>
            fin p L Γ (SWhile p x c body None) m
              ('(exist _ c' Hc) <- cres (elab c (hd_env [] TUnit L) Γ (Chk TBool)) ;;
               '(exist _ b' Hb) <- cres (elab body (push_lab (mk_lab x LKWhile [] TUnit) L) Γ (Chk TUnit)) ;;
               Ok (existT _ _ (exist _ _ (S_While E L Γ p x c body c' b' Hc Hb))))
        | Some nb =>
            match m as m0 return result (out L Γ (SWhile p x c body (Some nb)) m0) elab_error with
            | Syn =>
                '(existT _ τ (exist _ nb0 H0)) <- elab nb (hd_env [] TUnit L) Γ Syn ;;
                '(exist _ c' Hc) <- cres (elab c (hd_env [] τ L) Γ (Chk TBool)) ;;
                '(exist _ b' Hb) <- cres (elab body (push_lab (mk_lab x LKWhile [] τ) L) Γ (Chk TUnit)) ;;
                '(exist _ nb' Hn) <- cres (elab nb (hd_env [] τ L) Γ (Chk τ)) ;;
                Ok (existT _ _ (exist _ _ (S_WhileNb E L Γ p x c body nb τ nb0 c' b' nb' H0 Hc Hb Hn)))
            | Chk τ =>
                '(exist _ c' Hc) <- cres (elab c (hd_env [] τ L) Γ (Chk TBool)) ;;
                '(exist _ b' Hb) <- cres (elab body (push_lab (mk_lab x LKWhile [] τ) L) Γ (Chk TUnit)) ;;
                '(exist _ nb' Hn) <- cres (elab nb (hd_env [] τ L) Γ (Chk τ)) ;;
                Okc (exist _ _ (C_WhileNb E L Γ p x c body nb τ c' b' nb' Hc Hb Hn))
            end
        end
    | SFor p x inits oc upds body onb =>
        '(existT _ τs (exist _ es Hi)) <- sinits_dec elab L Γ inits ;;
        let Γ' := List.app (names_ctx (map fst inits) τs) Γ in
        let names := map fst inits in
        (* the loop at type [τ], without [nobreak] *)
        let parts (τ : ty) :=
          '(exist _ c' Hc) <- ochk_dec elab (hd_env τs τ L) Γ' TBool oc ;;
          '(exist _ b' Hb) <- cres (elab body (push_lab (mk_lab x LKForBody [] TUnit) (hd_env τs τ L)) Γ' (Chk TUnit)) ;;
          '(exist _ us Hu) <- supds_dec elab p (hd_env τs τ L) ((None, TUnit) :: Γ') names τs upds ;;
          Ok (exist (fun r : option expr * expr * list (ident * expr) =>
                       let '(c', b', us) := r in
                       Γ' ⊩ᵒ[E;hd_env τs τ L] oc ⇐ TBool ⇝ c' /\
                       Γ' ⊩[E;push_lab (mk_lab x LKForBody [] TUnit) (hd_env τs τ L)] body ⇐ TUnit ⇝ b' /\
                       (None, TUnit) :: Γ' ⊩ᵘ[E;hd_env τs τ L] upds : names ; τs ⇝ us)
                    (c', b', us) (conj Hc (conj Hb Hu))) in
        match onb as o return result (out L Γ (SFor p x inits oc upds body o) m) elab_error with
        | None =>
            let syn_f :=
              '(exist _ (c', b', us) (conj Hc (conj Hb Hu))) <- parts TUnit ;;
              Ok (existT _ _ (exist _ _ (S_For E L Γ p x inits oc upds body τs es c' b' us Hi Hc Hb Hu))) in
            match m as m0 return result (out L Γ (SFor p x inits oc upds body None) m0) elab_error with
            | Syn => syn_f
            | Chk τ =>
                match oc as o return oc = o -> result (out L Γ (SFor p x inits o upds body None) (Chk τ)) elab_error with
                | None => fun _ =>
                    '(exist _ b' Hb) <- cres (elab body (push_lab (mk_lab x LKForBody [] TUnit) (hd_env τs τ L)) Γ' (Chk TUnit)) ;;
                    '(exist _ us Hu) <- supds_dec elab p (hd_env τs τ L) ((None, TUnit) :: Γ') names τs upds ;;
                    Okc (exist _ _ (C_ForInf E L Γ p x inits upds body τs es τ b' us Hi Hb Hu))
                | Some c0 => fun Hoc =>
                    '(exist _ e H) <- cres (fin p L Γ (SFor p x inits oc upds body None) (Chk τ) syn_f) ;;
                    Okc (exist _ e (chk_cast L Γ _ _ τ τ e
                                     (f_equal (fun o' => SFor p x inits o' upds body None) Hoc) eq_refl H))
                end eq_refl
            end
        | Some nb =>
            match m as m0 return result (out L Γ (SFor p x inits oc upds body (Some nb)) m0) elab_error with
            | Syn =>
                '(existT _ τ (exist _ nb0 H0)) <- elab nb (hd_env τs TUnit L) Γ' Syn ;;
                '(exist _ (c', b', us) (conj Hc (conj Hb Hu))) <- parts τ ;;
                '(exist _ nb' Hn) <- cres (elab nb (hd_env τs τ L) Γ' (Chk τ)) ;;
                Ok (existT _ _ (exist _ _ (S_ForNb E L Γ p x inits oc upds body nb τs es τ nb0 c' b' us nb'
                                                   Hi H0 Hc Hb Hu Hn)))
            | Chk τ =>
                '(exist _ (c', b', us) (conj Hc (conj Hb Hu))) <- parts τ ;;
                '(exist _ nb' Hn) <- cres (elab nb (hd_env τs τ L) Γ' (Chk τ)) ;;
                Okc (exist _ _ (C_ForNb E L Γ p x inits oc upds body nb τs es τ c' b' us nb' Hi Hc Hb Hu Hn))
            end
        end
    | SForIn p x pats src inits upds body onb =>
        '(existT _ e1 (existT _ e2 (exist _ it Hs))) <- fsrc_dec elab p L Γ src ;;
        '(existT _ τs (exist _ es Hi)) <- sinits_dec elab L (fo_ctx it Γ) inits ;;
        let names := map fst inits in
        let Γl := fl_ctx it names τs Γ in
        '(existT _ q (existT _ Δ (existT _ scrut (exist _ sty Hp)))) <- fi_pat_dec p it τs pats ;;
        let parts (τ : ty) :=
          '(exist _ b' Hb) <- cres (elab body (fi_body_env x it τs τ L) (List.app Δ Γl) (Chk TUnit)) ;;
          '(exist _ us Hu) <- supds_dec elab p (fi_state_env it τs τ L) ((None, TUnit) :: List.app Δ Γl) names τs upds ;;
          Ok (exist (fun r : expr * list (ident * expr) =>
                       let '(b', us) := r in
                       List.app Δ Γl ⊩[E;fi_body_env x it τs τ L] body ⇐ TUnit ⇝ b' /\
                       (None, TUnit) :: List.app Δ Γl ⊩ᵘ[E;fi_state_env it τs τ L] upds : names ; τs ⇝ us)
                    (b', us) (conj Hb Hu)) in
        match onb as o return result (out L Γ (SForIn p x pats src inits upds body o) m) elab_error with
        | None =>
            fin p L Γ (SForIn p x pats src inits upds body None) m
              ('(exist _ (b', us) (conj Hb Hu)) <- parts TUnit ;;
               Ok (existT _ _ (exist _ _ (S_ForIn E L Γ p x pats src inits upds body e1 e2 it τs es q Δ scrut sty
                                                  b' us Hs Hi Hp Hb Hu))))
        | Some nb =>
            match m as m0 return result (out L Γ (SForIn p x pats src inits upds body (Some nb)) m0) elab_error with
            | Syn =>
                '(existT _ τ (exist _ nb0 H0)) <- elab nb (fi_loop_env it τs TUnit L) Γl Syn ;;
                '(exist _ (b', us) (conj Hb Hu)) <- parts τ ;;
                '(exist _ nb' Hn) <- cres (elab nb (fi_loop_env it τs τ L) Γl (Chk τ)) ;;
                Ok (existT _ _ (exist _ _ (S_ForInNb E L Γ p x pats src inits upds body nb e1 e2 it τs es τ nb0
                                                     q Δ scrut sty b' us nb' Hs Hi H0 Hp Hb Hu Hn)))
            | Chk τ =>
                '(exist _ (b', us) (conj Hb Hu)) <- parts τ ;;
                '(exist _ nb' Hn) <- cres (elab nb (fi_loop_env it τs τ L) Γl (Chk τ)) ;;
                Okc (exist _ _ (C_ForInNb E L Γ p x pats src inits upds body nb e1 e2 it τs es τ
                                         q Δ scrut sty b' us nb' Hs Hi Hp Hb Hu Hn))
            end
        end
    | SBlock p x body =>
        match m as m0 return result (out L Γ (SBlock p x body) m0) elab_error with
        | Syn =>
            '(exist _ b Hb) <- cres (elab body (push_lab (mk_lab (Some x) LKBlock [] TUnit) L) Γ (Chk TUnit)) ;;
            Ok (existT _ _ (exist _ _ (S_Block E L Γ p x body b Hb)))
        | Chk τ =>
            '(exist _ b Hb) <- cres (elab body (push_lab (mk_lab (Some x) LKBlock [] τ) L) Γ (Chk τ)) ;;
            Okc (exist _ _ (C_Block E L Γ p x body τ b Hb))
        end
    | SBreak p x oa =>
        let jmp (τ : ty) : result (cout L Γ (SBreak p x oa) τ) elab_error :=
          '(exist _ (k, τt) Ht) <- of_option (break_target x (ce_labs L) 0) (EE_NoTarget p) ;;
          '(exist _ (ps, r) Hn) <- label_at p L k ;;
          match ty_eq_dec r τt with
          | left Hr =>
              match oa as o return result (cout L Γ (SBreak p x o) τ) elab_error with
              | Some a =>
                  '(exist _ a' Ha) <- cres (elab a L Γ (Chk τt)) ;;
                  Ok (exist _ _ (C_Break E L Γ p x a τ k ps τt a' Ht (lbl_res Hn Hr) Ha))
              | None =>
                  match ty_eq_dec τt TUnit with
                  | left Hu => Ok (exist _ _ (C_Break0 E L Γ p x τ k ps (tgt_res Ht Hu) (lbl_res Hn (eq_trans Hr Hu))))
                  | right _ => Err (EE_Annot p τt TUnit)
                  end
              end
          | right _ => Err (EE_NoTarget p)
          end in
        match m as m0 return result (out L Γ (SBreak p x oa) m0) elab_error with
        | Syn => '(exist _ e H) <- jmp TUnit ;; Ok (existT _ _ (exist _ _ (S_Jump E L Γ (SBreak p x oa) e eq_refl H)))
        | Chk τ => r <- jmp τ ;; Okc r
        end
    | SContinue p x args =>
        let jmp (τ : ty) : result (cout L Γ (SContinue p x args) τ) elab_error :=
          '(exist _ tgt Ht) <- of_option (cont_target_of x (ce_labs L) 0) (EE_NoTarget p) ;;
          match tgt as g, args as a0 return cont_target_of x (ce_labs L) 0 = Some g ->
                                            result (cout L Γ (SContinue p x a0) τ) elab_error with
          | CTWhile k, [] => fun Ht =>
              '(exist _ (ps, r) Hn) <- label_at p L k ;;
              match list_eq_dec ty_eq_dec ps [] with
              | left Hps => Ok (exist _ _ (C_ContWhile E L Γ p x τ k r Ht (lbl_ps Hn Hps)))
              | right _ => Err (EE_NoTarget p)
              end
          | CTWhile _, a0 => fun _ => Err (EE_BadContinue p 0 (List.length a0))
          | CTFor k ps, [] => fun Ht =>
              '(exist _ (pk, r) Hn) <- label_at p L k ;;
              match ty_eq_dec r TUnit with
              | left Hr => Ok (exist _ _ (C_ContFor0 E L Γ p x τ k ps pk Ht (lbl_res Hn Hr)))
              | right _ => Err (EE_NoTarget p)
              end
          | CTFor k ps, a :: a' => fun Ht =>
              _ <- bcheck (Nat.eqb (List.length ps) (List.length (a :: a')))
                          (EE_BadContinue p (List.length ps) (List.length (a :: a'))) ;;
              '(exist _ (ps', r) Hn) <- label_at p L (S k) ;;
              match list_eq_dec ty_eq_dec ps' ps with
              | left Hps =>
                  '(exist _ es Hes) <- chk_list p L Γ (fun s' τ' => cres (elab s' L Γ (Chk τ'))) (a :: a') ps ;;
                  Ok (exist _ _ (C_ContFor E L Γ p x (a :: a') τ k ps r es Ht (cons_not_nil a a') (lbl_ps Hn Hps) Hes))
              | right _ => Err (EE_NoTarget p)
              end
          | CTForIn k ss, [] => fun Ht =>
              '(exist _ (pk, r) Hn) <- label_at p L k ;;
              match ty_eq_dec r TUnit with
              | left Hr => Ok (exist _ _ (C_ContForIn0 E L Γ p x τ k ss pk Ht (lbl_res Hn Hr)))
              | right _ => Err (EE_NoTarget p)
              end
          | CTForIn k ss, a :: a' => fun Ht =>
              _ <- bcheck (Nat.eqb (List.length ss) (List.length (a :: a')))
                          (EE_BadContinue p (List.length ss) (List.length (a :: a'))) ;;
              '(exist _ (pk, r) Hn) <- label_at p L (S k) ;;
              match ty_eq_dec r (TTuple ss) with
              | left Hr =>
                  '(exist _ es Hes) <- chk_list p L Γ (fun s' τ' => cres (elab s' L Γ (Chk τ'))) (a :: a') ss ;;
                  Ok (exist _ _ (C_ContForIn E L Γ p x (a :: a') τ k ss pk es Ht (cons_not_nil a a') (lbl_res Hn Hr) Hes))
              | right _ => Err (EE_NoTarget p)
              end
          end Ht in
        match m as m0 return result (out L Γ (SContinue p x args) m0) elab_error with
        | Syn => '(exist _ e H) <- jmp TUnit ;; Ok (existT _ _ (exist _ _ (S_Jump E L Γ (SContinue p x args) e eq_refl H)))
        | Chk τ => r <- jmp τ ;; Okc r
        end
    | SReturn p oa =>
        let jmp (τ : ty) : result (cout L Γ (SReturn p oa) τ) elab_error :=
          '(exist _ (k, r) Ht) <- of_option (return_target (ce_labs L) 0) (EE_NoTarget p) ;;
          '(exist _ (ps, r') Hn) <- label_at p L k ;;
          match ty_eq_dec r' r with
          | left Hr =>
              match oa as o return result (cout L Γ (SReturn p o) τ) elab_error with
              | Some a =>
                  '(exist _ a' Ha) <- cres (elab a L Γ (Chk r)) ;;
                  Ok (exist _ _ (C_Return E L Γ p a τ k ps r a' Ht (lbl_res Hn Hr) Ha))
              | None =>
                  match ty_eq_dec r TUnit with
                  | left Hu => Ok (exist _ _ (C_Return0 E L Γ p τ k ps (ret_res Ht Hu) (lbl_res Hn (eq_trans Hr Hu))))
                  | right _ => Err (EE_Annot p r TUnit)
                  end
              end
          | right _ => Err (EE_NoTarget p)
          end in
        match m as m0 return result (out L Γ (SReturn p oa) m0) elab_error with
        | Syn => '(exist _ e H) <- jmp TUnit ;; Ok (existT _ _ (exist _ _ (S_Jump E L Γ (SReturn p oa) e eq_refl H)))
        | Chk τ => r <- jmp τ ;; Okc r
        end
    | SField p s0 f =>
        fin p L Γ (SField p s0 f) m
          ('(existT _ τ0 (exist _ e H)) <- elab s0 L Γ Syn ;;
           match τ0 as t return Γ ⊩[E;L] s0 ⇒ t ⇝ e -> result (sout L Γ (SField p s0 f)) elab_error with
           | TData T ts => fun H =>
               '(exist _ names Hn) <- of_option (assoc T (se_sinfo E)) (EE_NotRecord p (TData T ts)) ;;
               '(exist _ i Hi) <- of_option (index_of f names) (EE_UnknownField p f) ;;
               '(exist _ (e', τ) Hf) <- field_proj_dec p T ts i e ;;
               Ok (existT _ τ (exist _ e' (S_Field E L Γ p s0 f T ts e names i e' τ H Hn Hi Hf)))
           | t => fun _ => Err (EE_NotRecord p t)
           end H)
    | SMatch p s0 cases =>
        '(existT _ τs (exist _ e H0)) <- elab s0 L Γ Syn ;;
        match m as m0 return result (out L Γ (SMatch p s0 cases) m0) elab_error with
        | Syn =>
            '(exist _ τ Hpick) <- pick_syn elab p L Γ τs cases ;;
            '(exist _ bs Hbs) <- arms_list elab L Γ τs τ cases ;;
            Ok (existT _ τ (exist _ _ (match_syn L Γ p s0 cases τs τ e bs H0 Hpick Hbs)))
        | Chk τ =>
            '(exist _ bs Hbs) <- arms_list elab L Γ τs τ cases ;;
            Okc (exist _ _ (C_Match E L Γ p s0 cases τs τ e bs H0 Hbs))
        end
    (* ---- trait objects (milestone M5) ---- *)
    | SAs p s0 Tr =>
        fin p L Γ (SAs p s0 Tr) m
          (Hob <- bcheck (existsb (String.eqb Tr) (x_objs (se_x E))) (EE_NotObjectSafe p Tr) ;;
           '(existT _ τ (exist _ e H)) <- elab s0 L Γ Syn ;;
           '(exist _ e' Hc) <- coerce p Γ e τ (TData (obj_name Tr) []) ;;
           Ok (existT _ _ (exist _ _ (S_As E L Γ p s0 Tr τ e e' Hob H Hc))))
    (* ---- errors (milestone M4) ---- *)
    | SRaise p s0 =>
        '(exist _ e H) <- cres (elab s0 L Γ (Chk (ce_exn L))) ;;
        match m as m0 return result (out L Γ (SRaise p s0) m0) elab_error with
        | Syn => Ok (existT _ _ (exist _ _ (S_Raise E L Γ p s0 e H)))
        | Chk τ => Okc (exist _ _ (C_Raise E L Γ p s0 τ e H))
        end
    | STryBang p body =>
        match m as m0 return result (out L Γ (STryBang p body) m0) elab_error with
        | Syn =>
            '(existT _ τ (exist _ b H)) <- elab body (set_exn TError L) Γ Syn ;;
            Ok (existT _ _ (exist _ _ (S_TryBang E L Γ p body τ b H)))
        | Chk τ =>
            '(exist _ b H) <- cres (elab body (set_exn TError L) Γ (Chk τ)) ;;
            Okc (exist _ _ (C_TryBang E L Γ p body τ b H))
        end
    | STry p body cases onr =>
        match onr as o return result (out L Γ (STry p body cases o) m) elab_error with
        | None =>
            match m as m0 return result (out L Γ (STry p body cases None) m0) elab_error with
            | Syn =>
                '(existT _ τe (Ht, existT _ τ (exist _ b Hb))) <- try_pick elab p L Γ cases body Syn ;;
                '(exist _ hbs Hh) <- arms_list elab L ((None, τe) :: Γ) τe τ cases ;;
                Ok (existT _ _ (exist _ _ (S_Try E L Γ p body cases τe τ b hbs Ht Hb Hh)))
            | Chk τ =>
                '(existT _ τe (Ht, existT _ _ (exist _ b Hb))) <- try_pick elab p L Γ cases body (Chk τ) ;;
                '(exist _ hbs Hh) <- arms_list elab L ((None, τe) :: Γ) τe τ cases ;;
                Okc (exist _ _ (C_Try E L Γ p body cases τe τ b hbs Ht (proj2 Hb) Hh))
            end
        | Some ncs =>
            '(existT _ τe (Ht, existT _ τ0 (exist _ b Hb))) <- try_pick elab p L Γ cases body Syn ;;
            match m as m0 return result (out L Γ (STry p body cases (Some ncs)) m0) elab_error with
            | Syn =>
                '(exist _ τ Hpick) <- pick_syn elab p L ((None, τe) :: Γ) τe cases ;;
                '(exist _ hbs Hh) <- arms_list elab L ((None, τe) :: Γ) τe τ cases ;;
                '(exist _ kbs Hk) <- arms_list elab L ((None, τ0) :: Γ) τ0 τ ncs ;;
                Ok (existT _ _ (exist _ _ (trynr_syn L Γ p body cases ncs τe τ0 τ b hbs kbs Ht Hb Hpick Hh Hk)))
            | Chk τ =>
                '(exist _ hbs Hh) <- arms_list elab L ((None, τe) :: Γ) τe τ cases ;;
                '(exist _ kbs Hk) <- arms_list elab L ((None, τ0) :: Γ) τ0 τ ncs ;;
                Okc (exist _ _ (C_TryNr E L Γ p body cases ncs τe τ0 τ b hbs kbs Ht Hb Hh Hk))
            end
        end
    | SDefer p d c body =>
        '(exist _ c' Hc) <- cres (elab c (mk_cenv [] (ce_exn L)) Γ (Chk TUnit)) ;;
        match m as m0 return result (out L Γ (SDefer p d c body) m0) elab_error with
        | Syn =>
            '(existT _ τ (exist _ b H)) <- elab body L Γ Syn ;;
            Ok (existT _ _ (exist _ _ (S_Defer E L Γ p d c body c' τ b Hc H)))
        | Chk τ =>
            '(exist _ b H) <- cres (elab body L Γ (Chk τ)) ;;
            Okc (exist _ _ (C_Defer E L Γ p d c body c' τ b Hc H))
        end
    | _ => Err (EE_Unsupported (sexpr_pos s) "not yet in the certified elaborator")
    end.
End Elaborate.
