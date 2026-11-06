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

(** ** Notations

    - [⟨K ▷ e⟩]      : [SEval K e], evaluate [e] under stack [K];
    - [⟨K ◁ v⟩]      : [SRet K v], return [v] to the top frame of [K];
    - [s ⟶[ge] s']  : one step ([step ge s s']);
    - [s ⟶*[ge] s'] : any number of steps ([star ge s s']). *)

Notation "⟨ K ▷ e ⟩" := (SEval K e)
  (at level 0, K at level 200, e at level 200, format "⟨ K  ▷  e ⟩").
Notation "⟨ K ◁ v ⟩" := (SRet K v)
  (at level 0, K at level 200, v at level 200, format "⟨ K  ◁  v ⟩").

Reserved Notation "s ⟶[ ge ] s'"
  (at level 70, ge at level 200, no associativity, format "s  ⟶[ ge ]  s'").
Reserved Notation "s ⟶*[ ge ] s'"
  (at level 70, ge at level 200, no associativity, format "s  ⟶*[ ge ]  s'").

Inductive step (ge : genv) : state -> state -> Prop :=
(* ---- evaluation: push a frame or produce a value ---- *)
| S_Lit K l :
    ⟨K ▷ ELit l⟩ ⟶[ge] ⟨K ◁ ELit l⟩
| S_Lam K ps r b :
    ⟨K ▷ ELam ps r b⟩ ⟶[ge] ⟨K ◁ ELam ps r b⟩
| S_Global K f ts fd :
    lookup_fn ge f = Some fd ->
    ⟨K ▷ EGlobal f ts⟩
      ⟶[ge] ⟨K ◁ ELam (map (tsubst (inst ts)) (fd_params fd))
                       (tsubst (inst ts) (fd_ret fd))
                       (esubst_ty (inst ts) (fd_body fd))⟩
| S_App K f args :
    ⟨K ▷ EApp f args⟩ ⟶[ge] ⟨FAppFun args :: K ▷ f⟩
| S_Let K e1 e2 :
    ⟨K ▷ ELet e1 e2⟩ ⟶[ge] ⟨FLet e2 :: K ▷ e1⟩
| S_If K c t e :
    ⟨K ▷ EIf c t e⟩ ⟶[ge] ⟨FIf t e :: K ▷ c⟩
| S_TupleNil K :
    ⟨K ▷ ETuple []⟩ ⟶[ge] ⟨K ◁ ETuple []⟩
| S_TupleCons K e es :
    ⟨K ▷ ETuple (e :: es)⟩ ⟶[ge] ⟨FTuple [] es :: K ▷ e⟩
| S_Proj K e i :
    ⟨K ▷ EProj e i⟩ ⟶[ge] ⟨FProj i :: K ▷ e⟩
| S_PrimNil K op l :
    prim_eval op [] = PVal l ->
    ⟨K ▷ EPrim op []⟩ ⟶[ge] ⟨K ◁ ELit l⟩
| S_PrimNilAbort K op :
    prim_eval op [] = PAbort ->
    ⟨K ▷ EPrim op []⟩ ⟶[ge] SAbort
| S_PrimCons K op e es :
    ⟨K ▷ EPrim op (e :: es)⟩ ⟶[ge] ⟨FPrim op [] es :: K ▷ e⟩

(* ---- return: consume the top frame ---- *)
| S_AppFunNil K ps r b :
    ⟨FAppFun [] :: K ◁ ELam ps r b⟩ ⟶[ge] ⟨K ▷ subst (args_sub []) b⟩
| S_AppFunCons K f a args :
    ⟨FAppFun (a :: args) :: K ◁ f⟩ ⟶[ge] ⟨FAppArg f [] args :: K ▷ a⟩
| S_AppArgLast K ps r b done v :
    ⟨FAppArg (ELam ps r b) done [] :: K ◁ v⟩
      ⟶[ge] ⟨K ▷ subst (args_sub (done ++ [v])) b⟩
| S_AppArgNext K f done v a rest :
    ⟨FAppArg f done (a :: rest) :: K ◁ v⟩
      ⟶[ge] ⟨FAppArg f (done ++ [v]) rest :: K ▷ a⟩
| S_LetRet K e2 v :
    ⟨FLet e2 :: K ◁ v⟩ ⟶[ge] ⟨K ▷ subst (args_sub [v]) e2⟩
| S_IfTrue K t e :
    ⟨FIf t e :: K ◁ ELit (LBool true)⟩ ⟶[ge] ⟨K ▷ t⟩
| S_IfFalse K t e :
    ⟨FIf t e :: K ◁ ELit (LBool false)⟩ ⟶[ge] ⟨K ▷ e⟩
| S_TupleLast K done v :
    ⟨FTuple done [] :: K ◁ v⟩ ⟶[ge] ⟨K ◁ ETuple (done ++ [v])⟩
| S_TupleNext K done v e rest :
    ⟨FTuple done (e :: rest) :: K ◁ v⟩ ⟶[ge] ⟨FTuple (done ++ [v]) rest :: K ▷ e⟩
| S_ProjRet K i vs v :
    nth_error vs i = Some v ->
    ⟨FProj i :: K ◁ ETuple vs⟩ ⟶[ge] ⟨K ◁ v⟩
| S_PrimLast K op done v ls l :
    as_lits (done ++ [v]) = Some ls ->
    prim_eval op ls = PVal l ->
    ⟨FPrim op done [] :: K ◁ v⟩ ⟶[ge] ⟨K ◁ ELit l⟩
| S_PrimLastAbort K op done v ls :
    as_lits (done ++ [v]) = Some ls ->
    prim_eval op ls = PAbort ->
    ⟨FPrim op done [] :: K ◁ v⟩ ⟶[ge] SAbort
| S_PrimNext K op done v e rest :
    ⟨FPrim op done (e :: rest) :: K ◁ v⟩ ⟶[ge] ⟨FPrim op (done ++ [v]) rest :: K ▷ e⟩

where "s ⟶[ ge ] s'" := (step ge s s').

(** Reflexive-transitive closure. *)
Inductive star (ge : genv) : state -> state -> Prop :=
| star_refl s :
    s ⟶*[ge] s
| star_step s1 s2 s3 :
    s1 ⟶[ge] s2 -> s2 ⟶*[ge] s3 -> s1 ⟶*[ge] s3

where "s ⟶*[ ge ] s'" := (star ge s s').

(** Terminal states: a value returned to the empty stack, or an abort. *)
Definition final (s : state) : Prop :=
  match s with
  | ⟨[] ◁ v⟩ => value v
  | SAbort => True
  | _ => False
  end.

(** A state that is not terminal and cannot step is stuck: this is what
    type soundness rules out. *)
Definition stuck (ge : genv) (s : state) : Prop :=
  ~ final s /\ ~ exists s', s ⟶[ge] s'.
