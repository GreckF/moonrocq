(** * Surface: programs (milestone M6)

    Elaboration of a whole program: data types, traits, signatures, the
    bodies of functions, methods and default methods (through the
    certified elaborator [Elaborate.v], specified by [fun_body] and proved
    well typed by [body_typed]), and the code generated for instances
    (dictionary functions) and trait objects.  The generated code has no
    surface source and is not specified here: like everything else, it is
    checked again by the Core checker ([check_program]) before a program is
    accepted. *)

From Stdlib Require Import List ZArith NArith String Bool Arith.
From MoonRocq.Prelude Require Import Result EqDec Ident ListDec.
From MoonRocq.Core Require Import Syntax Prim Subst Typing Check.
From MoonRocq.Surface Require Import Syntax Resolve Base ElabSpec ElabTyped Elaborate.
Import ListNotations.

Local Open Scope string_scope.

(** ** Data types and signatures *)

Definition elab_tdef (tys : list (ident * nat)) (st : stype) : result tdef elab_error :=
  let tps := st_tparams st in
  let n := List.length tps in
  match st_body st with
  | SDEnum cs =>
      cds <- mapM (fun c => τs <- mapM (elab_ty tys tps) (snd c) ;; Ok (mk_cdef (fst c) τs)) cs ;;
      Ok (mk_tdef (st_name st) n cds false)
  | SDError cs =>
      cds <- mapM (fun c => τs <- mapM (elab_ty tys tps) (snd c) ;; Ok (mk_cdef (fst c) τs)) cs ;;
      Ok (mk_tdef (st_name st) n cds true)
  | SDStruct fs =>
      (* a [mut] field holds a cell *)
      τs <- mapM (fun (f : ident * bool * sty) => τ <- elab_ty tys tps (snd f) ;;
                           Ok (if snd (fst f) then TRef τ else τ)) fs ;;
      Ok (mk_tdef (st_name st) n [mk_cdef (st_name st) τs] false)
  | SDTupleStruct ts =>
      τs <- mapM (elab_ty tys tps) ts ;;
      Ok (mk_tdef (st_name st) n [mk_cdef (st_name st) τs] false)
  end.

(** Does the type mention the name [x] (used for [raise?])? *)
Fixpoint sty_mentions (x : ident) (t : sty) {struct t} : bool :=
  let fix go (ts : list sty) : bool :=
    match ts with
    | [] => false
    | t :: ts' => (sty_mentions x t || go ts')%bool
    end in
  match t with
  | SName _ n args => (eqb n x || go args)%bool
  | STuple _ ts => go ts
  | SArrow _ ps r eff =>
      (go ps || sty_mentions x r || match eff with Some t => sty_mentions x t | None => false end)%bool
  | SObj _ _ => false
  end.

(** The type parameters of a signature: a [raise?] signature has a hidden
    last one, the error type it raises ([?]). *)
Definition sig_tparams (f : sfun) : list ident :=
  let poly := (existsb (fun xt => sty_mentions "?" (snd xt)) (sf_params f)
               || match sf_eff f with Some t => sty_mentions "?" t | None => false end)%bool in
  if poly then List.app (sf_tparams f) ["?"] else sf_tparams f.

(** The global name of a function or method. *)
Definition fun_name (f : sfun) : ident :=
  match sf_self f with
  | Some T => T ++ "::" ++ sf_name f
  | None => sf_name f
  end.

(** Trait bounds [(X, Tr)] as constraints [(Tr, index of X)]. *)
Definition bound_ctx (p : pos) (tps : list ident) (bs : list (ident * ident)) :
    result (list (ident * nat)) elab_error :=
  mapM (fun b => i <- of_opt (index_of (fst b) tps) (EE_UnknownType p (fst b)) ;; Ok (snd b, i)) bs.

Definition dict_ty (c : ident * nat) : ty := TData (fst c) [TVar (snd c)].

Definition elab_sig (tys : list (ident * nat)) (f : sfun) : result fdef elab_error :=
  let tps := sig_tparams f in
  ctx <- bound_ctx (sf_pos f) tps (sf_bounds f) ;;
  τs <- mapM (fun xt => elab_ty tys tps (snd xt)) (sf_params f) ;;
  τ <- match sf_ret f with
       | Some t => elab_ty tys tps t
       | None => Ok TUnit
       end ;;
  ε <- match sf_eff f with
       | Some t => elab_ty tys tps t
       | None => Ok TNever
       end ;;
  Ok (mk_fdef (fun_name f) (List.length tps) (List.app (map dict_ty ctx) τs) τ ε (ELit LUnit)).

(** ** Definitions

    The body of a definition with trait bounds [ctx] on the type
    parameters [tps]: the dictionary parameters come first, their
    supertrait dictionaries are bound by [let]s around the body, which is
    checked against the result type (as the block that [return] targets).
    The rules are [fun_body]; [body_typed] states that the result is a well
    typed Core function body; [body_dec] is the certified elaborator. *)

Definition dict_ctx (tps : list ident) (ctx : list (ident * nat)) : lctx :=
  map (fun c => (Some (dict_var (fst c) (nth (snd c) tps "")), dict_ty c)) ctx.

Definition body_lets (E : senv) (tps : list ident) (ctx : list (ident * nat)) :
    list (ident * ident * nat * ident * nat) :=
  super_lets (trs E) (List.length (trs E) * S (List.length ctx)) []
             (map (fun c => (fst c, nth (snd c) tps "", snd c)) ctx).

Definition body_asm (E : senv) (tps : list ident) (ctx : list (ident * nat)) : list (ident * ty * ident) :=
  List.app (map (fun c => (fst c, TVar (snd c), dict_var (fst c) (nth (snd c) tps ""))) ctx)
           (map (fun l => let '(Sn, X, i, _, _) := l in (Sn, TVar i, dict_var Sn X)) (body_lets E tps ctx)).

(** The environment of a body: its type parameters and assumptions. *)
Definition with_asm (E : senv) (tps : list ident) (asm : list (ident * ty * ident)) : senv :=
  let X := se_x E in
  mk_senv (se_tys E) (se_hdr E) (se_sinfo E) tps
          (mk_xenv (x_traits X) (x_insts X) (x_bounds X) (x_meths X) (x_objs X) asm).

(** The supertrait dictionary [Sn] of [X] is field [j] of its dictionary
    [T] of [X]. *)
Inductive sup_lets (E : senv) : lctx -> list (ident * ident * nat * ident * nat) -> list expr -> lctx -> Prop :=
| SL_nil Γ :
    sup_lets E Γ [] [] Γ
| SL_cons Γ Sn X i T j ls k e es Γ' :
    lookup_local (dict_var T X) Γ = Some k ->
    nth_error (ctx_of Γ) k = Some (TData T [TVar i]) ->
    field_proj E T [TVar i] j (EVar k) = Some (e, TData Sn [TVar i]) ->
    sup_lets E ((Some (dict_var Sn X), TData Sn [TVar i]) :: Γ) ls es Γ' ->
    sup_lets E Γ ((Sn, X, i, T, j) :: ls) (e :: es) Γ'.

Inductive fun_body (E : senv) (tps : list ident) (ctx : list (ident * nat)) (Γp : lctx) (r ε : ty)
    (body : sexpr) : expr -> Prop :=
| FB es Γ b :
    sup_lets E (List.app (dict_ctx tps ctx) Γp) (body_lets E tps ctx) es Γ ->
    Γ ⊩[with_asm E tps (body_asm E tps ctx); fun_env r ε] body ⇐ r ⇝ b ->
    fun_body E tps ctx Γp r ε body (fold_right ELet (eblock r b) es).

Lemma sup_lets_typed E Λ Γ ls es Γ' b r :
  sup_lets E Γ ls es Γ' ->
  ctx_of Γ' ⊢[se_hdr E;[];Λ] b : r -> ctx_of Γ ⊢[se_hdr E;[];Λ] fold_right ELet b es : r.
Proof.
  induction 1 as [|Γ Sn X i T j ls k e es Γ' Hk Hn Hp _ IH]; simpl; intros Hb; auto.
  eapply T_Let; [|exact (IH Hb)].
  eapply field_proj_typed; [constructor; exact Hn|exact Hp].
Qed.

Lemma dict_ctx_ctx tps ctx : ctx_of (dict_ctx tps ctx) = map dict_ty ctx.
Proof. unfold ctx_of, dict_ctx; rewrite map_map; reflexivity. Qed.

(** A body is well typed in Core, with the dictionaries and then the
    parameters as its parameters. *)
Theorem body_typed E tps ctx Γp r ε body b :
  Forall (inst_ok (se_hdr E)) (x_insts (se_x E)) ->
  fun_body E tps ctx Γp r ε body b ->
  List.app (map dict_ty ctx) (ctx_of Γp) ⊢[se_hdr E;[];mk_cctx [] ε] b : r.
Proof.
  intros HI [es Γ b0 Hl Hb].
  rewrite <- (dict_ctx_ctx tps ctx), <- ctx_of_app.
  eapply sup_lets_typed; [exact Hl|].
  apply (eblock_typed (with_asm E tps (body_asm E tps ctx))).
  exact (proj1 (proj2 (elab_typed (with_asm E tps (body_asm E tps ctx)) HI)) _ _ _ _ _ Hb).
Qed.

Fixpoint sup_lets_dec (E : senv) (ls : list (ident * ident * nat * ident * nat)) (Γ : lctx) :
    result {es : list expr & {Γ' : lctx | sup_lets E Γ ls es Γ'}} elab_error :=
  match ls as l return result {es : list expr & {Γ' : lctx | sup_lets E Γ l es Γ'}} elab_error with
  | [] => Ok (existT _ [] (exist _ Γ (SL_nil E Γ)))
  | (Sn, X, i, T, j) :: ls' =>
      let p0 := mk_pos 0%N 0%N in
      '(exist _ k Hk) <- of_option (lookup_local (dict_var T X) Γ) (EE_Unbound p0 (dict_var T X)) ;;
      '(exist _ t Ht) <- of_option (nth_error (ctx_of Γ) k) (EE_Unbound p0 (dict_var T X)) ;;
      match ty_eq_dec t (TData T [TVar i]) with
      | left Heq =>
          '(exist _ (e, u) Hp) <- field_proj_dec E p0 T [TVar i] j (EVar k) ;;
          match ty_eq_dec u (TData Sn [TVar i]) with
          | left Hu =>
              '(existT _ es (exist _ Γ' Hl)) <-
                sup_lets_dec E ls' ((Some (dict_var Sn X), TData Sn [TVar i]) :: Γ) ;;
              Ok (existT _ (e :: es) (exist _ Γ'
                    (SL_cons E Γ Sn X i T j ls' k e es Γ' Hk (eq_trans Ht (f_equal Some Heq))
                             (eq_trans Hp (f_equal (fun w => Some (e, w)) Hu)) Hl)))
          | right _ => Err (EE_NoInstance p0 Sn (TVar i))
          end
      | right _ => Err (EE_NoInstance p0 T (TVar i))
      end
  end.

Definition body_dec (E : senv) (tps : list ident) (ctx : list (ident * nat)) (Γp : lctx) (r ε : ty)
    (body : sexpr) : result {b | fun_body E tps ctx Γp r ε body b} elab_error :=
  '(existT _ es (exist _ Γ Hl)) <- sup_lets_dec E (body_lets E tps ctx) (List.app (dict_ctx tps ctx) Γp) ;;
  '(exist _ b Hb) <- cres _ (elab (with_asm E tps (body_asm E tps ctx)) body (fun_env r ε) Γ (Chk r)) ;;
  Ok (exist _ _ (FB E tps ctx Γp r ε body es Γ b Hl Hb)).

Definition elab_body (E : senv) (tps : list ident) (ctx : list (ident * nat)) (Γp : lctx) (r ε : ty)
    (body : sexpr) : result expr elab_error :=
  '(exist _ b _) <- body_dec E tps ctx Γp r ε body ;; Ok b.

Definition elab_fun (E : senv) (f : sfun) (sig : fdef) : result fdef elab_error :=
  let tps := sig_tparams f in
  ctx <- bound_ctx (sf_pos f) tps (sf_bounds f) ;;
  let Γp := combine (map (fun xt => Some (fst xt)) (sf_params f))
                    (skipn (List.length ctx) (fd_params sig)) in
  b <- elab_body E tps ctx Γp (fd_ret sig) (fd_eff sig) (sf_body f) ;;
  Ok (mk_fdef (fd_name sig) (fd_tparams sig) (fd_params sig) (fd_ret sig) (fd_eff sig) b).

Fixpoint elab_funs (E : senv) (fs : list sfun) (sigs : list fdef) : result (list fdef) elab_error :=
  match fs, sigs with
  | f :: fs', sig :: sigs' =>
      fd <- elab_fun E f sig ;;
      fds <- elab_funs E fs' sigs' ;;
      Ok (fd :: fds)
  | _, _ => Ok []
  end.

(** ** Traits and impls *)

Definition elab_trait (tys : list (ident * nat)) (t : strait) : result trinfo elab_error :=
  ms <- mapM (fun m =>
                ps <- mapM (elab_ty tys ["Self"]) (sm_params m) ;;
                r <- elab_ty tys ["Self"] (sm_ret m) ;;
                ε <- match sm_eff m with
                     | Some t => elab_ty tys ["Self"] t
                     | None => Ok TNever
                     end ;;
                Ok (mk_msig (sm_name m) ps r ε)) (str_methods t) ;;
  Ok (mk_trinfo (str_name t) (str_supers t) ms (map sm_name (filter sm_default (str_methods t)))).

(** The [impl]s of one trait for one type, grouped. *)
Record igroup : Type := mk_igroup {
  ig_pos     : pos;
  ig_trait   : ident;
  ig_head    : ty;
  ig_tparams : list ident;
  ig_bounds  : list (ident * ident);
  ig_methods : list simethod
}.

Fixpoint add_impl (gs : list igroup) (p : pos) (Tr : ident) (τ : ty) (tps : list ident)
    (bs : list (ident * ident)) (m : option simethod) : list igroup :=
  match gs with
  | [] => [mk_igroup p Tr τ tps bs (match m with Some m => [m] | None => [] end)]
  | g :: gs' =>
      if (eqb (ig_trait g) Tr && eqb (ig_head g) τ)%bool
      then mk_igroup (ig_pos g) Tr τ (ig_tparams g) (ig_bounds g)
                     (List.app (ig_methods g) (match m with Some m => [m] | None => [] end)) :: gs'
      else g :: add_impl gs' p Tr τ tps bs m
  end.

Definition inst_name (Tr H : ident) : ident := "inst$" ++ Tr ++ "$" ++ H.
Definition impl_name (Tr H m : ident) : ident := "impl$" ++ Tr ++ "$" ++ H ++ "$" ++ m.
Definition default_name (Tr m : ident) : ident := "default$" ++ Tr ++ "$" ++ m.

(** An instance group, checked: its head, constraints and signatures. *)
Record iinfo : Type := mk_iinfo {
  ii_group : igroup;
  ii_ti    : trinfo;
  ii_name  : ident;                (** the head's type name *)
  ii_ctx   : list (ident * nat);
  ii_idef  : idef
}.

Definition check_group (trs : list trinfo) (g : igroup) : result iinfo elab_error :=
  let p := ig_pos g in
  let n := List.length (ig_tparams g) in
  ti <- of_opt (find_trait trs (ig_trait g)) (EE_UnknownType p (ig_trait g)) ;;
  '(h, args) <- of_opt (head_args (ig_head g)) (EE_Unsupported p "impl for this type") ;;
  _ <- if eqb args (map TVar (seq 0 n)) then Ok tt
       else Err (EE_Unsupported p "impl head (type parameters in order)") ;;
  H <- of_opt (head_name (ig_head g)) (EE_Unsupported p "impl for this type") ;;
  ctx <- bound_ctx p (ig_tparams g) (ig_bounds g) ;;
  (* every method must be implemented, or have a default *)
  _ <- mapM (fun s =>
               if existsb (fun im => eqb (sim_name im) (ms_name s)) (ig_methods g)
                  || existsb (eqb (ms_name s)) (ti_defaults ti)
               then Ok tt else Err (EE_MissingMethod p (ig_trait g) (ms_name s)))
            (ti_methods ti) ;;
  _ <- if NoDup_dec (map sim_name (ig_methods g)) then Ok tt else Err (EE_Overlap p) ;;
  _ <- mapM (fun im => match method_of ti (sim_name im) with
                       | Some _ => Ok tt
                       | None => Err (EE_NoMethod p (sim_name im) (ig_head g))
                       end) (ig_methods g) ;;
  Ok (mk_iinfo g ti H ctx (mk_idef (ig_trait g) h n ctx (inst_name (ig_trait g) H))).

(** The signatures generated for an instance: its methods and its
    dictionary function. *)
Definition group_sigs (ii : iinfo) : list fdef :=
  let g := ii_group ii in
  let σ := tsubst (inst [ig_head g]) in
  let n := List.length (ig_tparams g) in
  let dicts := map dict_ty (ii_ctx ii) in
  mk_fdef (inst_name (ig_trait g) (ii_name ii)) n dicts (TData (ig_trait g) [ig_head g]) TNever (ELit LUnit)
  :: flat_map (fun im => match method_of (ii_ti ii) (sim_name im) with
                         | Some (_, s) =>
                             [mk_fdef (impl_name (ig_trait g) (ii_name ii) (sim_name im)) n
                                      (List.app dicts (map σ (ms_params s))) (σ (ms_ret s))
                                      (σ (ms_eff s)) (ELit LUnit)]
                         | None => []
                         end) (ig_methods g).

(** The dictionary function of an instance. *)
Definition inst_body (insts : list idef) (trs : list trinfo) (defaults : list (ident * ident))
    (ii : iinfo) : result expr elab_error :=
  let g := ii_group ii in
  let ti := ii_ti ii in
  let p := ig_pos g in
  let n := List.length (ig_tparams g) in
  let nc := List.length (ii_ctx ii) in
  let tvars := map TVar (seq 0 n) in
  let τh := ig_head g in
  let σ := tsubst (inst [τh]) in
  let Θ := map (fun jc => (fst (snd jc), TVar (snd (snd jc)), EVar (fst jc)))
               (combine (seq 0 nc) (ii_ctx ii)) in
  sups <- mapM (fun S => match entails_dec insts Θ S τh with
                         | inleft (exist _ d _) => Ok d
                         | inright _ => Err (EE_NoInstance p S τh)
                         end) (ti_supers ti) ;;
  ms <- mapM (fun s =>
                let ps := map σ (ms_params s) in
                let k := List.length ps in
                let lvars := map EVar (seq 0 k) in
                let dvars := map (fun j => EVar (k + j)) (seq 0 nc) in
                if existsb (fun im => eqb (sim_name im) (ms_name s)) (ig_methods g) then
                  Ok (ELam ps (σ (ms_ret s)) (σ (ms_eff s))
                        (EApp (EGlobal (impl_name (ig_trait g) (ii_name ii) (ms_name s)) tvars)
                              (List.app dvars lvars)))
                else
                  let self := EApp (EGlobal (inst_name (ig_trait g) (ii_name ii)) tvars) dvars in
                  Ok (ELam ps (σ (ms_ret s)) (σ (ms_eff s))
                        (EApp (EGlobal (default_name (ig_trait g) (ms_name s)) [τh]) (self :: lvars))))
             (ti_methods ti) ;;
  Ok (EConstr (ig_trait g) (ig_trait g) [τh] (ETuple (List.app sups ms))).

(** The automatic instance of each trait [S] of an object type [&Tr]. *)
Definition obj_insts (trs : list trinfo) (Tr : ident) : list (idef * fdef) :=
  let On := obj_name Tr in
  map (fun Sn => (mk_idef Sn (HData On) 0 [] (inst_name Sn On),
                  mk_fdef (inst_name Sn On) 0 [] (TData Sn [TData On []]) TNever (ELit LUnit)))
      (closure trs Tr).

Definition obj_inst_body (insts : list idef) (trs : list trinfo) (Tr Sn : ident) :
    result expr elab_error :=
  let On := obj_name Tr in
  let τo := TData On [] in
  let fs := obj_fields trs Tr in
  ti <- of_opt (find_trait trs Sn) (EE_UnknownType (mk_pos 0%N 0%N) Sn) ;;
  sups <- mapM (fun S' => match entails_dec insts [] S' τo with
                          | inleft (exist _ d _) => Ok d
                          | inright _ => Err (EE_NoInstance (mk_pos 0%N 0%N) S' τo)
                          end) (ti_supers ti) ;;
  ms <- mapM (fun s =>
                j <- of_opt (index_of (ms_name s) (map (fun sm => ms_name (snd sm)) fs))
                            (EE_NotObjectSafe (mk_pos 0%N 0%N) Tr) ;;
                let ps := tl (ms_params s) in
                let k := List.length ps in
                Ok (ELam (τo :: ps) (ms_ret s) (ms_eff s)
                      (EApp (field_of On (List.length fs) j (EVar 0) (obj_field_ty s))
                            (map EVar (seq 1 k)))))
             (ti_methods ti) ;;
  Ok (EConstr Sn Sn [τo] (ETuple (List.app sups ms))).

(** ** Programs *)

(** The entry expression is the body of [fn main] (checked against [Unit]),
    or [()] when there is none.  [Option], [Ref], [Result] and [Failure]
    are predeclared. *)
Definition elab_prog (sp : sprog) : result (genv * expr) elab_error :=
  let trnames := map str_name (sp_traits sp) in
  let tys := List.app [("Option", 1); ("Ref", 1); ("Result", 2); ("Failure", 0)]
               (List.app (map (fun st => (st_name st, List.length (st_tparams st))) (sp_types sp))
                  (List.app (map (fun n => (n, 1)) trnames)
                            (map (fun n => (obj_name n, 0)) trnames))) in
  let sinfo := ("Ref", ["val"]) :: flat_map (fun st => match st_body st with
                                   | SDStruct fs => [(st_name st, map (fun f => fst (fst f)) fs)]
                                   | _ => []
                                   end) (sp_types sp) in
  trs <- mapM (elab_trait tys) (sp_traits sp) ;;
  let objs := filter (obj_safe trs) trnames in
  tds <- mapM (elab_tdef tys) (sp_types sp) ;;
  let types := List.app [option_tdef; ref_tdef; result_tdef; failure_tdef]
                 (List.app tds (List.app (map dict_tdef trs) (map (obj_tdef trs) objs))) in
  (* impls: grouped by trait and type; default implementations apart *)
  groups <- fold_left
              (fun acc i =>
                 gs <- acc ;;
                 match si_self i with
                 | Some t => τ <- elab_ty tys (si_tparams i) t ;;
                             Ok (add_impl gs (si_pos i) (si_trait i) τ (si_tparams i) (si_bounds i)
                                          (si_method i))
                 | None => Ok gs
                 end) (sp_impls sp) (Ok []) ;;
  iis <- mapM (check_group trs) groups ;;
  let defaults := flat_map (fun i => match si_self i, si_method i with
                                     | None, Some m => [(si_trait i, m)]
                                     | _, _ => []
                                     end) (sp_impls sp) in
  dsigs <- mapM (fun tm =>
                   let '(Tr, im) := tm in
                   ti <- of_opt (find_trait trs Tr) (EE_UnknownType (mk_pos 0%N 0%N) Tr) ;;
                   '(_, s) <- of_opt (method_of ti (sim_name im)) (EE_NoMethod (mk_pos 0%N 0%N) (sim_name im) TUnit) ;;
                   Ok (mk_fdef (default_name Tr (sim_name im)) 1
                               (TData Tr [TVar 0] :: ms_params s) (ms_ret s) (ms_eff s) (ELit LUnit)))
                defaults ;;
  let oinsts := flat_map (obj_insts trs) objs in
  let insts := List.app (map ii_idef iis) (map fst oinsts) in
  _ <- if coherent_dec insts then Ok tt else Err (EE_Overlap (mk_pos 0%N 0%N)) ;;
  (* signatures *)
  sigs <- mapM (elab_sig tys) (sp_funs sp) ;;
  let gsigs := flat_map group_sigs iis in
  let hdr := mk_genv types (List.app sigs (List.app gsigs (List.app dsigs (map snd oinsts)))) in
  let bounds := List.app
    (flat_map (fun f => match bound_ctx (sf_pos f) (sig_tparams f) (sf_bounds f) with
                        | Ok ctx => [(fun_name f, ctx)]
                        | Err _ => []
                        end) (sp_funs sp))
    (List.app
       (flat_map (fun ii => map (fun im => (impl_name (ig_trait (ii_group ii)) (ii_name ii) (sim_name im),
                                            ii_ctx ii))
                                (ig_methods (ii_group ii))) iis)
       (flat_map (fun ii => [(inst_name (ig_trait (ii_group ii)) (ii_name ii), ii_ctx ii)]) iis)) in
  let meths := flat_map (fun f => match sf_self f with Some T => [(T, sf_name f)] | None => [] end)
                        (sp_funs sp) in
  let gx := mk_xenv trs insts bounds meths objs [] in
  let E := mk_senv tys hdr sinfo [] gx in
  (* bodies *)
  funs <- elab_funs E (sp_funs sp) sigs ;;
  imfs <- mapM (fun ii =>
                  let g := ii_group ii in
                  let σ := tsubst (inst [ig_head g]) in
                  mapM (fun im =>
                          '(_, s) <- of_opt (method_of (ii_ti ii) (sim_name im))
                                            (EE_NoMethod (ig_pos g) (sim_name im) TUnit) ;;
                          let ps := map σ (ms_params s) in
                          _ <- if Nat.eqb (List.length (sim_params im)) (List.length ps) then Ok tt
                               else Err (EE_Type (ig_pos g) (E_ArgArity (List.length ps)
                                                                        (List.length (sim_params im)))) ;;
                          let Γp := combine (map (fun x => Some (fst x)) (sim_params im)) ps in
                          b <- elab_body E (ig_tparams g) (ii_ctx ii) Γp
                                         (σ (ms_ret s)) (σ (ms_eff s)) (sim_body im) ;;
                          Ok (mk_fdef (impl_name (ig_trait g) (ii_name ii) (sim_name im))
                                      (List.length (ig_tparams g))
                                      (List.app (map dict_ty (ii_ctx ii)) ps)
                                      (σ (ms_ret s)) (σ (ms_eff s)) b))
                       (ig_methods g)) iis ;;
  ifs <- mapM (fun ii =>
                 let g := ii_group ii in
                 b <- inst_body insts trs [] ii ;;
                 Ok (mk_fdef (inst_name (ig_trait g) (ii_name ii)) (List.length (ig_tparams g))
                             (map dict_ty (ii_ctx ii)) (TData (ig_trait g) [ig_head g]) TNever b)) iis ;;
  dfs <- mapM (fun tm =>
                 let '(Tr, im) := tm in
                 ti <- of_opt (find_trait trs Tr) (EE_UnknownType (mk_pos 0%N 0%N) Tr) ;;
                 '(_, s) <- of_opt (method_of ti (sim_name im)) (EE_NoMethod (mk_pos 0%N 0%N) (sim_name im) TUnit) ;;
                 let Γp := combine (map (fun x => Some (fst x)) (sim_params im)) (ms_params s) in
                 b <- elab_body E ["Self"] [(Tr, 0)] Γp (ms_ret s) (ms_eff s) (sim_body im) ;;
                 Ok (mk_fdef (default_name Tr (sim_name im)) 1 (TData Tr [TVar 0] :: ms_params s)
                             (ms_ret s) (ms_eff s) b)) defaults ;;
  ofs <- mapM (fun Tr =>
                 mapM (fun Sn =>
                         b <- obj_inst_body insts trs Tr Sn ;;
                         Ok (mk_fdef (inst_name Sn (obj_name Tr)) 0 [] (TData Sn [TData (obj_name Tr) []])
                                     TNever b)) (closure trs Tr)) objs ;;
  main <- match sp_main sp with
          | Some e =>
              elab_body E [] [] [] TUnit TNever
                        (SAnnot (sexpr_pos e) e (SName (sexpr_pos e) "Unit" []))
          | None => Ok (ELit LUnit)
          end ;;
  Ok (mk_genv types (List.app funs (List.app (List.concat imfs) (List.app ifs (List.app dfs (List.concat ofs))))),
      main).
