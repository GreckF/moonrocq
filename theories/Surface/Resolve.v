(** * Trait instance resolution (milestone M5)

    Traits are elaborated away by dictionary passing (DESIGN.md §11): a
    trait [Tr] becomes a Core data type [Tr[Self]] whose single constructor
    holds the supertrait dictionaries and the methods; an [impl] becomes a
    global function building the dictionary from the dictionaries of its
    own constraints; a bound [T : Tr] becomes a dictionary parameter.  The
    Core language is unchanged, so the soundness results of M1–M4 cover
    trait programs as they are.

    This file is the part of elaboration that decides *which* dictionary a
    constraint [Tr[τ]] uses, following the methodology of the project:
    - [entails]: declarative rules ([Inductive]) for "the constraint
      [Tr[τ]] holds, with dictionary [d]": by an assumption (a bound of the
      enclosing function or one of its supertraits) or by an instance whose
      head matches [τ];
    - [resolve_dict]: a certified resolver (it returns the derivation), and its
      completeness [resolve_complete]: whenever a dictionary exists, it
      finds one; hence [entails_dec];
    - [coherent]: at most one instance per trait and type head, a
      decidable well-formedness condition; it makes resolution unique
      ([entails_unique]);
    - [entails_typed]: the dictionaries are well-typed Core terms, given
      well-typed instance functions and assumptions.

    Instance heads are type constructors applied to distinct type
    parameters ([head]), as in MoonBit: an [impl] for [Array[Int]] next to
    one for [Array[T]] is an overlap. *)

From Stdlib Require Import List Arith Lia.
From MoonRocq.Prelude Require Import Result EqDec Ident ListDec.
From MoonRocq.Core Require Import Syntax Subst Typing.
Import ListNotations.

(** ** Type heads *)

Inductive head : Type :=
| HBase  (b : base_ty)
| HTuple (n : nat)
| HData  (T : ident)
| HRef
| HArray (k : array_kind)
| HError.

Definition head_eq_dec (x y : head) : {x = y} + {x <> y}.
Proof. decide equality; apply eq_dec. Defined.

#[export] Instance EqDec_head : EqDec head := EqDec_of_dec head_eq_dec.

(** The head of a type and its arguments (type variables and function types
    have no instances). *)
Definition head_args (τ : ty) : option (head * list ty) :=
  match τ with
  | TBase b => Some (HBase b, [])
  | TTuple ts => Some (HTuple (length ts), ts)
  | TData T ts => Some (HData T, ts)
  | TRef t => Some (HRef, [t])
  | TArray k t => Some (HArray k, [t])
  | TError => Some (HError, [])
  | TVar _ | TArrow _ _ _ => None
  end.

Definition head_args_sig (τ : ty) : option {p | head_args τ = Some p} :=
  match head_args τ as o return option {p | o = Some p} with
  | Some p => Some (exist _ p eq_refl)
  | None => None
  end.

Lemma head_args_sig_some τ p :
  head_args τ = Some p -> exists E, head_args_sig τ = Some (exist _ p E).
Proof. destruct τ; simpl; intros E; inversion E; subst; eexists; reflexivity. Qed.

(** The head applied to the type parameters [X0 .. Xn-1]. *)
Definition head_ty (h : head) (n : nat) : ty :=
  match h with
  | HBase b => TBase b
  | HTuple _ => TTuple (map TVar (seq 0 n))
  | HData T => TData T (map TVar (seq 0 n))
  | HRef => TRef (TVar 0)
  | HArray k => TArray k (TVar 0)
  | HError => TError
  end.

Lemma map_nth_seq0 (ts : list ty) :
  map (fun x => nth x ts TUnit) (seq 0 (length ts)) = ts.
Proof.
  induction ts as [|a ts IH]; simpl; [reflexivity|].
  f_equal. rewrite <- seq_shift, map_map. exact IH.
Qed.

Lemma map_inst_seq ts : map (tsubst (inst ts)) (map TVar (seq 0 (length ts))) = ts.
Proof. rewrite map_map. exact (map_nth_seq0 ts). Qed.

Lemma head_ty_inst τ h args :
  head_args τ = Some (h, args) -> tsubst (inst args) (head_ty h (length args)) = τ.
Proof.
  destruct τ; simpl; intros E; inversion E; subst; simpl; try reflexivity;
    f_equal; apply map_inst_seq.
Qed.

Lemma head_args_size_lt τ h args i a :
  head_args τ = Some (h, args) -> nth_error args i = Some a -> True.
Proof. auto. Qed.

(** ** Instances and assumptions *)

(** An [impl[X0 .. Xn-1] Tr for H[X0 ..]]: its trait, its head and arity
    [n], the constraints on its type parameters ([(Tr', i)] is [Xi : Tr']),
    and the global function that builds its dictionary from the
    dictionaries of these constraints. *)
Record idef : Type := mk_idef {
  in_trait : ident;
  in_head  : head;
  in_arity : nat;
  in_ctx   : list (ident * nat);
  in_fun   : ident
}.

(** An assumption [(Tr, τ, d)]: the constraint [Tr[τ]] holds with
    dictionary [d] (a bound of the enclosing function, or one of its
    supertraits; the elaborator supplies the expression). *)
Definition assumption : Type := ident * ty * expr.

Fixpoint find_assume (Tr : ident) (τ : ty) (l : list assumption) :
    option {d | In (Tr, τ, d) l} :=
  match l as l' return option {d | In (Tr, τ, d) l'} with
  | [] => None
  | ((Tr', τ'), d') :: l' =>
      match eq_dec (Tr', τ') (Tr, τ) with
      | left E => Some (exist _ d' (or_introl (f_equal (fun k => (k, d')) E)))
      | right _ =>
          match find_assume Tr τ l' with
          | Some (exist _ d H) => Some (exist _ d (or_intror H))
          | None => None
          end
      end
  end.

Lemma find_assume_complete Tr τ d l :
  In (Tr, τ, d) l -> exists p, find_assume Tr τ l = Some p.
Proof.
  induction l as [|[[Tr' τ'] d'] l IH]; simpl; intros H.
  - contradiction.
  - destruct (eq_dec (Tr', τ') (Tr, τ)) as [E|N]; [eauto|].
    destruct H as [H|H]; [inversion H; subst; congruence|].
    destruct (IH H) as [[d0 Hd0] ->]. eauto.
Qed.

Section Entails.
  Variables (I : list idef) (Θ : list assumption).

  (** [entails Tr τ d] : [Tr[τ]] holds, with dictionary [d]. *)
  Inductive entails : ident -> ty -> expr -> Prop :=
  | R_Assume Tr τ d :
      In (Tr, τ, d) Θ ->
      entails Tr τ d
  | R_Inst Tr τ h args id ds :
      head_args τ = Some (h, args) ->
      In id I -> in_trait id = Tr -> in_head id = h -> length args = in_arity id ->
      entails_ctx args (in_ctx id) ds ->
      entails Tr τ (EApp (EGlobal (in_fun id) args) ds)

  (** The constraints of an instance, instantiated with [args]. *)
  with entails_ctx : list ty -> list (ident * nat) -> list expr -> Prop :=
  | RC_nil args :
      entails_ctx args [] []
  | RC_cons args Tr i a ctx d ds :
      nth_error args i = Some a ->
      entails Tr a d ->
      entails_ctx args ctx ds ->
      entails_ctx args ((Tr, i) :: ctx) (d :: ds).

  Scheme entails_mut := Minimality for entails Sort Prop
    with entails_ctx_mut := Minimality for entails_ctx Sort Prop.
  Combined Scheme entails_mutind from entails_mut, entails_ctx_mut.

  (** ** The certified resolver

      Assumptions first, then the instances in order, with backtracking.
      The fuel bounds the depth of the search; [ty_size τ] suffices, since
      the constraints of an instance are on proper subterms of [τ]. *)

  Definition find_assumption (Tr : ident) (τ : ty) : option {d | In (Tr, τ, d) Θ} :=
    find_assume Tr τ Θ.

  Definition opt_sig {A} (o : option A) : option {a | o = Some a} :=
    match o as o' return option {a | o' = Some a} with
    | Some a => Some (exist _ a eq_refl)
    | None => None
    end.

  Lemma opt_sig_some {A} (o : option A) a : o = Some a -> exists E, opt_sig o = Some (exist _ a E).
  Proof. intros ->; eexists; reflexivity. Qed.

  (** The constraints of an instance, given a resolver for the arguments. *)
  Definition resolve_ctx (rs : forall Tr τ, option {d | entails Tr τ d}) (args : list ty) :
      forall ctx, option {ds | entails_ctx args ctx ds} :=
    fix go ctx :=
      match ctx as ctx' return option {ds | entails_ctx args ctx' ds} with
      | [] => Some (exist _ [] (RC_nil args))
      | (Tr', i) :: ctx' =>
          match opt_sig (nth_error args i), go ctx' with
          | Some (exist _ a Ea), Some (exist _ ds Hds) =>
              match rs Tr' a with
              | Some (exist _ d Hd) => Some (exist _ (d :: ds) (RC_cons args Tr' i a ctx' d ds Ea Hd Hds))
              | None => None
              end
          | _, _ => None
          end
      end.

  (** Try the instances of [J] for [Tr[τ]] with head [h] and arguments [args]. *)
  Definition resolve_insts (Tr : ident) (τ : ty) (h : head) (args : list ty)
      (Eh : head_args τ = Some (h, args))
      (rc : forall ctx, option {ds | entails_ctx args ctx ds}) :
      forall J, (forall id, In id J -> In id I) -> option {d | entails Tr τ d} :=
    fix go J :=
      match J as J' return (forall id, In id J' -> In id I) -> option {d | entails Tr τ d} with
      | [] => fun _ => None
      | id :: J' => fun HJ =>
          let rest := go J' (fun x Hx => HJ x (or_intror Hx)) in
          match eq_dec (in_trait id) Tr, eq_dec (in_head id) h,
                Nat.eq_dec (length args) (in_arity id) with
          | left Et, left Eh', left En =>
              match rc (in_ctx id) with
              | Some (exist _ ds Hds) =>
                  Some (exist _ _ (R_Inst Tr τ h args id ds Eh (HJ id (or_introl eq_refl))
                                          Et Eh' En Hds))
              | None => rest
              end
          | _, _, _ => rest
          end
      end.

  Fixpoint resolve_dict (n : nat) (Tr : ident) (τ : ty) {struct n} : option {d | entails Tr τ d} :=
    match find_assumption Tr τ with
    | Some (exist _ d H) => Some (exist _ d (R_Assume Tr τ d H))
    | None =>
        match n with
        | 0 => None
        | S n' =>
            match head_args_sig τ with
            | Some (exist _ (h, args) Eh) =>
                resolve_insts Tr τ h args Eh (resolve_ctx (resolve_dict n') args) I (fun x Hx => Hx)
            | None => None
            end
        end
    end.

  (** ** Completeness *)

  Fixpoint ty_size (t : ty) : nat :=
    match t with
    | TBase _ | TVar _ | TError => 1
    | TTuple ts | TData _ ts => S (list_sum (map ty_size ts))
    | TArrow ps r ε => S (list_sum (map ty_size ps) + ty_size r + ty_size ε)
    | TRef t | TArray _ t => S (ty_size t)
    end.

  Lemma list_sum_nth l i x : nth_error l i = Some x -> x <= list_sum l.
  Proof.
    revert i; induction l as [|y l IH]; intros [|i] E; simpl in *; try discriminate.
    - inversion E; lia.
    - specialize (IH _ E); lia.
  Qed.

  Lemma head_args_size τ h args i a :
    head_args τ = Some (h, args) -> nth_error args i = Some a -> ty_size a < ty_size τ.
  Proof.
    intros E Ea; destruct τ; simpl in E; inversion E; subst; simpl.
    - destruct i; discriminate.
    - assert (H := list_sum_nth (map ty_size args) i (ty_size a)).
      rewrite nth_error_map, Ea in H. specialize (H eq_refl). lia.
    - assert (H := list_sum_nth (map ty_size args) i (ty_size a)).
      rewrite nth_error_map, Ea in H. specialize (H eq_refl). lia.
    - destruct i as [|[]]; simpl in Ea; inversion Ea; subst; lia.
    - destruct i as [|[]]; simpl in Ea; inversion Ea; subst; lia.
    - destruct i; discriminate.
  Qed.

  Lemma find_assumption_complete Tr τ d :
    In (Tr, τ, d) Θ -> exists p, find_assumption Tr τ = Some p.
  Proof. apply find_assume_complete. Qed.

  Lemma resolve_ctx_complete rs args ctx :
    Forall (fun c => exists a, nth_error args (snd c) = Some a /\
                       exists p, rs (fst c) a = Some p) ctx ->
    exists p, resolve_ctx rs args ctx = Some p.
  Proof.
    induction 1 as [|[Tr' i] ctx [a [Ea [p Ep]]] _ [q Eq]]; simpl; [eauto|].
    fold (resolve_ctx rs args ctx). rewrite Eq.
    simpl in Ea. destruct (opt_sig_some _ _ Ea) as [E' ->].
    simpl in Ep. rewrite Ep. destruct p, q. eauto.
  Qed.

  Lemma resolve_insts_complete Tr τ h args Eh rc J HJ id :
    In id J -> in_trait id = Tr -> in_head id = h -> length args = in_arity id ->
    (exists p, rc (in_ctx id) = Some p) ->
    exists p, resolve_insts Tr τ h args Eh rc J HJ = Some p.
  Proof.
    revert HJ; induction J as [|id' J IH]; intros HJ Hin Et Eh' En [pc Epc]; [contradiction|].
    simpl. fold (resolve_insts Tr τ h args Eh rc J).
    destruct Hin as [<-|Hin].
    - destruct (eq_dec (in_trait id') Tr) as [E1|N1]; [|congruence].
      destruct (eq_dec (in_head id') h) as [E2|N2]; [|congruence].
      destruct (Nat.eq_dec (length args) (in_arity id')) as [E3|N3]; [|congruence].
      rewrite Epc. destruct pc. eauto.
    - destruct (eq_dec (in_trait id') Tr), (eq_dec (in_head id') h),
               (Nat.eq_dec (length args) (in_arity id'));
        try (eapply IH; eauto; fail).
      destruct (rc (in_ctx id')) as [[ds Hds]|]; [eauto|]. eapply IH; eauto.
  Qed.

  Lemma resolve_complete_mut :
    (forall Tr τ d, entails Tr τ d ->
       forall n, ty_size τ <= n -> exists p, resolve_dict n Tr τ = Some p) /\
    (forall args ctx ds, entails_ctx args ctx ds ->
       forall n, (forall i a, nth_error args i = Some a -> ty_size a <= n) ->
       Forall (fun c => exists a, nth_error args (snd c) = Some a /\
                          exists p, resolve_dict n (fst c) a = Some p) ctx).
  Proof.
    apply entails_mutind.
    - (* R_Assume *)
      intros Tr τ d Hin n _.
      destruct (find_assumption_complete _ _ _ Hin) as [[d0 H0] E].
      destruct n; simpl; rewrite E; eauto.
    - (* R_Inst *)
      intros Tr τ h args id ds Eh Hid Et Ehd En _ IH n Hn.
      destruct n as [|n].
      { exfalso. destruct τ; simpl in Hn, Eh; try discriminate; lia. }
      simpl. destruct (find_assumption Tr τ) as [[d0 H0]|]; [eauto|].
      destruct (head_args_sig_some _ _ Eh) as [E' ->].
      eapply resolve_insts_complete; eauto.
      apply resolve_ctx_complete. apply IH.
      intros i a Ea. assert (Hs := head_args_size _ _ _ _ _ Eh Ea). lia.
    - (* RC_nil *) intros; constructor.
    - (* RC_cons *)
      intros args Tr i a ctx d ds Ea _ IHd _ IHds n Hn.
      constructor; [|auto].
      exists a; split; [exact Ea | apply IHd, Hn with i; exact Ea].
  Qed.

  Theorem resolve_complete Tr τ d :
    entails Tr τ d -> exists p, resolve_dict (ty_size τ) Tr τ = Some p.
  Proof. intros H; exact (proj1 resolve_complete_mut _ _ _ H _ (le_n _)). Qed.

  Definition entails_dec Tr τ : {d | entails Tr τ d} + {forall d, ~ entails Tr τ d}.
  Proof.
    destruct (resolve_dict (ty_size τ) Tr τ) as [p|] eqn:E; [left; exact p | right].
    intros d H. destruct (resolve_complete _ _ _ H) as [p E']. congruence.
  Defined.

  (** ** Coherence and uniqueness *)

  Definition coherent : Prop := NoDup (map (fun id => (in_trait id, in_head id)) I).

  Lemma NoDup_map_inj {A B} (f : A -> B) l x y :
    NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
  Proof.
    induction l as [|z l IH]; simpl; intros Hn Hx Hy E; [contradiction|].
    inversion Hn as [|? ? Hz Hl]; subst.
    destruct Hx as [<-|Hx], Hy as [<-|Hy]; auto.
    - exfalso; apply Hz. rewrite E. now apply in_map.
    - exfalso; apply Hz. rewrite <- E. now apply in_map.
  Qed.

  Lemma instance_unique id1 id2 :
    coherent -> In id1 I -> In id2 I ->
    in_trait id1 = in_trait id2 -> in_head id1 = in_head id2 -> id1 = id2.
  Proof.
    intros Hc H1 H2 Et Eh. eapply NoDup_map_inj; eauto. simpl; congruence.
  Qed.

  (** Under coherence, with assumptions only on type variables and at most
      one per constraint, a constraint has at most one dictionary: the
      meaning of a program does not depend on how its constraints are
      resolved. *)
  Theorem entails_unique :
    coherent ->
    (forall Tr τ d, In (Tr, τ, d) Θ -> head_args τ = None) ->
    NoDup (map fst Θ) ->
    forall Tr τ d1 d2, entails Tr τ d1 -> entails Tr τ d2 -> d1 = d2.
  Proof.
    intros Hc Hvar Hnd.
    assert (Hmut :
      (forall Tr τ d1, entails Tr τ d1 -> forall d2, entails Tr τ d2 -> d1 = d2) /\
      (forall args ctx ds1, entails_ctx args ctx ds1 ->
         forall ds2, entails_ctx args ctx ds2 -> ds1 = ds2)).
    { apply entails_mutind.
      - intros Tr τ d1 H1 d2 H2. inversion H2; subst.
        + assert (E := NoDup_map_inj fst Θ _ _ Hnd H1 H (eq_refl : fst (Tr, τ, d1) = fst (Tr, τ, d2))).
          congruence.
        + rewrite (Hvar _ _ _ H1) in H. discriminate.
      - intros Tr τ h args id ds Eh Hid Et Ehd En _ IH d2 H2. inversion H2; subst.
        + rewrite (Hvar _ _ _ H) in Eh. discriminate.
        + rewrite Eh in H. inversion H; subst.
          assert (id0 = id) by (eapply instance_unique; eauto; congruence). subst.
          f_equal. apply IH; assumption.
      - intros args ds2 H. inversion H; reflexivity.
      - intros args Tr i a ctx d ds Ea _ IHd _ IHds ds2 H.
        inversion H as [|? ? ? a' ? d' ds' Ea' Hd' Hds']; subst.
        rewrite Ea in Ea'. inversion Ea'; subst. f_equal; auto. }
    intros Tr τ d1 d2 H1 H2. exact (proj1 Hmut _ _ _ H1 _ H2).
  Qed.

  Definition coherent_dec : {coherent} + {~ coherent} :=
    NoDup_dec (map (fun id => (in_trait id, in_head id)) I).

  (** ** Dictionaries are well typed *)

  (** The instance function: [fn[X0 .. Xn-1] f(Tr'[Xi] ..) -> Tr[H[X0 ..]]],
      [noraise]. *)
  Definition inst_ok (ge : genv) (id : idef) : Prop :=
    exists fd, lookup_fn ge (in_fun id) = Some fd /\
      fd_tparams fd = in_arity id /\
      fd_params fd = map (fun c => TData (fst c) [TVar (snd c)]) (in_ctx id) /\
      fd_ret fd = TData (in_trait id) [head_ty (in_head id) (in_arity id)] /\
      fd_eff fd = TNever.

  Theorem entails_typed ge Σ Λ Γ :
    Forall (inst_ok ge) I ->
    (forall Tr τ d, In (Tr, τ, d) Θ -> Γ ⊢[ge;Σ;Λ] d : TData Tr [τ]) ->
    forall Tr τ d, entails Tr τ d -> Γ ⊢[ge;Σ;Λ] d : TData Tr [τ].
  Proof.
    intros HI HΘ.
    assert (Hmut :
      (forall Tr τ d, entails Tr τ d -> Γ ⊢[ge;Σ;Λ] d : TData Tr [τ]) /\
      (forall args ctx ds, entails_ctx args ctx ds ->
         Γ ⊢*[ge;Σ;Λ] ds : map (fun c => tsubst (inst args) (TData (fst c) [TVar (snd c)])) ctx)).
    { apply entails_mutind.
      - intros; auto.
      - intros Tr τ h args id ds Eh Hid Et Ehd En _ IH.
        rewrite Forall_forall in HI.
        destruct (HI id Hid) as (fd & Hfd & Ht & Hp & Hr & He).
        assert (Hg := T_Global ge Σ Λ Γ (in_fun id) args fd Hfd ltac:(congruence)).
        rewrite Hp, Hr, He in Hg. subst Tr h.
        replace (tsubst (inst args) (TData (in_trait id) [head_ty (in_head id) (in_arity id)]))
          with (TData (in_trait id) [τ]) in Hg.
        2:{ simpl. rewrite <- En, (head_ty_inst τ (in_head id) args Eh). reflexivity. }
        eapply T_App; [exact Hg | rewrite map_map; exact IH | left; reflexivity].
      - intros; constructor.
      - intros args Tr i a ctx d ds Ea _ IHd _ IHds. simpl.
        constructor; [|exact IHds].
        unfold inst. rewrite (nth_error_nth _ _ _ Ea). exact IHd. }
    exact (proj1 Hmut).
  Qed.
End Entails.
