(** * Core IR: small-step semantics (stack machine)

    The semantics is an inductive relation [step ge s s'] on machine
    states.  It exists to state and prove type soundness; it is not meant to
    be executed.  A state is either
    - [SEval K e] : evaluate [e] under the stack [K];
    - [SRet K v]  : return the value [v] to the top frame of [K];
    - [SAbort]    : the program panicked (division by zero, …).

    Explicit frames, rather than evaluation contexts, are chosen so that the
    non-local control flow of later milestones ([return], labelled
    [break]/[continue], [raise], [defer]) becomes "unwind the stack to the
    matching frame" (DESIGN.md §3).  Values are closed expressions;
    application and [let] substitute them into the body. *)

From Stdlib Require Import List.
From MoonRocq.Core Require Import Syntax Prim Subst.
Import ListNotations.

Inductive value : expr -> Prop :=
| V_Lit l : value (ELit l)
| V_Lam ps r b : value (ELam ps r b)
| V_Tuple vs : Forall value vs -> value (ETuple vs).

Inductive frame : Type :=
| FAppFun (args : list expr)                          (** [□(args)] *)
| FAppArg (f : expr) (done rest : list expr)          (** [f(done, □, rest)] *)
| FLet    (e2 : expr)                                 (** [let _ = □ in e2] *)
| FIf     (t e : expr)                                (** [if □ {t} else {e}] *)
| FTuple  (done rest : list expr)                     (** [(done, □, rest)] *)
| FProj   (i : nat)                                   (** [□.i] *)
| FPrim   (op : prim_op) (done rest : list expr).     (** [op(done, □, rest)] *)

Definition stack : Type := list frame.

Inductive state : Type :=
| SEval  (K : stack) (e : expr)
| SRet   (K : stack) (v : expr)
| SAbort.

(** Literal payloads of a list of values, if they are all literals. *)
Fixpoint as_lits (vs : list expr) : option (list lit) :=
  match vs with
  | [] => Some []
  | ELit l :: vs' =>
      match as_lits vs' with
      | Some ls => Some (l :: ls)
      | None => None
      end
  | _ :: _ => None
  end.

Section Step.
  Variable ge : genv.

  Inductive step : state -> state -> Prop :=
  (* ---- evaluation: push a frame or produce a value ---- *)
  | S_Lit K l :
      step (SEval K (ELit l)) (SRet K (ELit l))
  | S_Lam K ps r b :
      step (SEval K (ELam ps r b)) (SRet K (ELam ps r b))
  | S_Global K f ts fd :
      lookup_fn ge f = Some fd ->
      step (SEval K (EGlobal f ts))
           (SRet K (ELam (map (tsubst (inst ts)) (fd_params fd))
                         (tsubst (inst ts) (fd_ret fd))
                         (esubst_ty (inst ts) (fd_body fd))))
  | S_App K f args :
      step (SEval K (EApp f args)) (SEval (FAppFun args :: K) f)
  | S_Let K e1 e2 :
      step (SEval K (ELet e1 e2)) (SEval (FLet e2 :: K) e1)
  | S_If K c t e :
      step (SEval K (EIf c t e)) (SEval (FIf t e :: K) c)
  | S_TupleNil K :
      step (SEval K (ETuple [])) (SRet K (ETuple []))
  | S_TupleCons K e es :
      step (SEval K (ETuple (e :: es))) (SEval (FTuple [] es :: K) e)
  | S_Proj K e i :
      step (SEval K (EProj e i)) (SEval (FProj i :: K) e)
  | S_PrimNil K op l :
      prim_eval op [] = PVal l ->
      step (SEval K (EPrim op [])) (SRet K (ELit l))
  | S_PrimNilAbort K op :
      prim_eval op [] = PAbort ->
      step (SEval K (EPrim op [])) SAbort
  | S_PrimCons K op e es :
      step (SEval K (EPrim op (e :: es))) (SEval (FPrim op [] es :: K) e)

  (* ---- return: consume the top frame ---- *)
  | S_AppFunNil K ps r b :
      step (SRet (FAppFun [] :: K) (ELam ps r b)) (SEval K (subst (args_sub []) b))
  | S_AppFunCons K f a args :
      step (SRet (FAppFun (a :: args) :: K) f) (SEval (FAppArg f [] args :: K) a)
  | S_AppArgLast K ps r b done v :
      step (SRet (FAppArg (ELam ps r b) done [] :: K) v)
           (SEval K (subst (args_sub (done ++ [v])) b))
  | S_AppArgNext K f done v a rest :
      step (SRet (FAppArg f done (a :: rest) :: K) v)
           (SEval (FAppArg f (done ++ [v]) rest :: K) a)
  | S_LetRet K e2 v :
      step (SRet (FLet e2 :: K) v) (SEval K (subst (args_sub [v]) e2))
  | S_IfTrue K t e :
      step (SRet (FIf t e :: K) (ELit (LBool true))) (SEval K t)
  | S_IfFalse K t e :
      step (SRet (FIf t e :: K) (ELit (LBool false))) (SEval K e)
  | S_TupleLast K done v :
      step (SRet (FTuple done [] :: K) v) (SRet K (ETuple (done ++ [v])))
  | S_TupleNext K done v e rest :
      step (SRet (FTuple done (e :: rest) :: K) v) (SEval (FTuple (done ++ [v]) rest :: K) e)
  | S_ProjRet K i vs v :
      nth_error vs i = Some v ->
      step (SRet (FProj i :: K) (ETuple vs)) (SRet K v)
  | S_PrimLast K op done v ls l :
      as_lits (done ++ [v]) = Some ls ->
      prim_eval op ls = PVal l ->
      step (SRet (FPrim op done [] :: K) v) (SRet K (ELit l))
  | S_PrimLastAbort K op done v ls :
      as_lits (done ++ [v]) = Some ls ->
      prim_eval op ls = PAbort ->
      step (SRet (FPrim op done [] :: K) v) SAbort
  | S_PrimNext K op done v e rest :
      step (SRet (FPrim op done (e :: rest) :: K) v) (SEval (FPrim op (done ++ [v]) rest :: K) e).

  (** Reflexive-transitive closure. *)
  Inductive star : state -> state -> Prop :=
  | star_refl s : star s s
  | star_step s1 s2 s3 : step s1 s2 -> star s2 s3 -> star s1 s3.
End Step.

(** Terminal states: a value returned to the empty stack, or an abort. *)
Definition final (s : state) : Prop :=
  match s with
  | SRet [] v => value v
  | SAbort => True
  | _ => False
  end.

(** A state that is not terminal and cannot step is stuck: this is what
    type soundness rules out. *)
Definition stuck (ge : genv) (s : state) : Prop :=
  ~ final s /\ ~ exists s', step ge s s'.
