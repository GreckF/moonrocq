(** * Core IR: small-step semantics (stack machine with a store)

    The semantics is an inductive relation [step ge s s'] on machine
    states.  It exists to state and prove type soundness; it is not meant to
    be executed.  A state is either
    - [⟨σ ∣ K ▷ e⟩]     : evaluate [e] under the stack [K] with store [σ];
    - [⟨σ ∣ K ◁ v⟩]     : return the value [v] to the top frame of [K];
    - [⟨σ ∣ K ⇑ c k v⟩] : unwind the stack for a [break] ([c = CBreak]) or
                          [continue] ([c = CCont]) to the [k]-th enclosing
                          loop, carrying [v];
    - [SAbort]          : the program panicked ([panic()], division by zero,
                          index out of bounds, no matching branch, …).

    Explicit frames, rather than evaluation contexts, make non-local
    control flow "unwind the stack to the matching frame" (DESIGN.md §3).
    Values are closed expressions; application, [let], [match] and loops
    substitute them into the body.  Store locations [ELoc l] are values
    that only appear at run time. *)

From Stdlib Require Import List ZArith.
From MoonRocq.Prelude Require Import EqDec Ident.
From MoonRocq.Core Require Import Syntax Prim Subst.
Import ListNotations.

Inductive value : expr -> Prop :=
| V_Lit l : value (ELit l)
| V_Lam ps r b : value (ELam ps r b)
| V_Tuple vs : Forall value vs -> value (ETuple vs)
| V_Constr T c ts v : value v -> value (EConstr T c ts v)
| V_Loc l : value (ELoc l).

(** ** Store *)

Inductive sobj : Type :=
| OCell (v : expr)              (** a mutable cell *)
| OArr  (vs : list expr).       (** an array *)

Definition store : Type := list sobj.

Fixpoint set_nth {A} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | _, [] => []
  | 0, _ :: l' => x :: l'
  | S n', y :: l' => y :: set_nth n' x l'
  end.

(** An [Int] index into a sequence of length [n], if in bounds. *)
Definition index_of (z : Z) (n : nat) : option nat :=
  if ((0 <=? z)%Z && (z <? Z.of_nat n)%Z)%bool then Some (Z.to_nat z) else None.

Inductive mres : Type :=
| MOk (σ : store) (v : expr)    (** new store and result *)
| MAbort.                       (** runtime panic (index out of bounds, …) *)

Definition alloc (σ : store) (o : sobj) : mres := MOk (σ ++ [o]) (ELoc (length σ)).

(** Store operations on fully evaluated arguments.  [None] means the
    arguments have the wrong shape (excluded by typing). *)
Definition mem_eval (op : mem_op) (σ : store) (vs : list expr) : option mres :=
  match op, vs with
  | MRef _, [v] => Some (alloc σ (OCell v))
  | MGet _, [ELoc l] =>
      match nth_error σ l with
      | Some (OCell v) => Some (MOk σ v)
      | _ => None
      end
  | MSet _, [ELoc l; v] =>
      match nth_error σ l with
      | Some (OCell _) => Some (MOk (set_nth l (OCell v) σ) (ELit LUnit))
      | _ => None
      end
  | MArray _ _ _, vs => Some (alloc σ (OArr vs))
  | MMake _ _, [ELit (LInt _ n); v] =>
      if (n <? 0)%Z then Some MAbort else Some (alloc σ (OArr (repeat v (Z.to_nat n))))
  | MIndex _ _, [ELoc l; ELit (LInt _ i)] =>
      match nth_error σ l with
      | Some (OArr ws) =>
          match index_of i (length ws) with
          | Some j =>
              match nth_error ws j with
              | Some w => Some (MOk σ w)
              | None => None
              end
          | None => Some MAbort
          end
      | _ => None
      end
  | MSetIndex _ _, [ELoc l; ELit (LInt _ i); v] =>
      match nth_error σ l with
      | Some (OArr ws) =>
          match index_of i (length ws) with
          | Some j => Some (MOk (set_nth l (OArr (set_nth j v ws)) σ) (ELit LUnit))
          | None => Some MAbort
          end
      | _ => None
      end
  | MLength _ _, [ELoc l] =>
      match nth_error σ l with
      | Some (OArr ws) => Some (MOk σ (ELit (LInt I32 (Z.of_nat (length ws)))))
      | _ => None
      end
  | MPush _, [ELoc l; v] =>
      match nth_error σ l with
      | Some (OArr ws) => Some (MOk (set_nth l (OArr (ws ++ [v])) σ) (ELit LUnit))
      | _ => None
      end
  | _, _ => None
  end.

(** ** Frames and states *)

Inductive frame : Type :=
| FAppFun (args : list expr)                          (** [□(args)] *)
| FAppArg (f : expr) (done rest : list expr)          (** [f(done, □, rest)] *)
| FLet    (e2 : expr)                                 (** [let _ = □ in e2] *)
| FIf     (t e : expr)                                (** [if □ {t} else {e}] *)
| FTuple  (done rest : list expr)                     (** [(done, □, rest)] *)
| FProj   (i : nat)                                   (** [□.i] *)
| FPrim   (op : prim_op) (done rest : list expr)      (** [op(done, □, rest)] *)
| FConstr (T c : ident) (ts : list ty)                (** [T::c(□)] *)
| FMatch  (τ : ty) (bs : list (pat * expr))           (** [match □ { bs }] *)
| FMem    (op : mem_op) (done rest : list expr)       (** [op(done, □, rest)] *)
| FLoopInit (ps : list ty) (τ : ty) (b : expr)        (** [loop □ { b }] *)
| FLoop   (ps : list ty) (τ : ty) (b : expr)          (** a running loop: the target of jumps *)
| FJump   (c : ctl) (k : nat).                        (** [break k □] / [continue k □] *)

Definition stack : Type := list frame.

Inductive state : Type :=
| SEval  (σ : store) (K : stack) (e : expr)
| SRet   (σ : store) (K : stack) (v : expr)
| SJump  (σ : store) (K : stack) (c : ctl) (k : nat) (v : expr)
| SAbort.

(** The loops of a stack (innermost first): the targets of jumps. *)
Fixpoint labels (K : stack) : lblctx :=
  match K with
  | [] => []
  | FLoop ps τ _ :: K' => (ps, τ) :: labels K'
  | _ :: K' => labels K'
  end.

Definition is_loop (F : frame) : bool :=
  match F with
  | FLoop _ _ _ => true
  | _ => false
  end.

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

(** ** Pattern matching

    [pmatch σ p v] returns the values bound by [p] (leftmost first) when
    the value [v] matches; [PRef] reads the store.  [pmatch_list] takes the
    element matcher as an argument so that its properties can be stated
    separately (nested recursion, as for [infer_list] in [Check.v]). *)

Definition pmatch_list (pm : pat -> expr -> option (list expr)) :
    list pat -> list expr -> option (list expr) :=
  fix go ps vs :=
    match ps, vs with
    | [], [] => Some []
    | p :: ps', v :: vs' =>
        match pm p v, go ps' vs' with
        | Some xs, Some ys => Some (xs ++ ys)
        | _, _ => None
        end
    | _, _ => None
    end.

Fixpoint pmatch (σ : store) (p : pat) (v : expr) {struct p} : option (list expr) :=
  match p, v with
  | PWild, _ => Some []
  | PVar, _ => Some [v]
  | PLit l, ELit l' => if eqb l l' then Some [] else None
  | PTuple ps, ETuple vs => pmatch_list (pmatch σ) ps vs
  | PConstr c ps, EConstr _ c' _ (ETuple vs) =>
      if eqb c c' then pmatch_list (pmatch σ) ps vs else None
  | PRef p, ELoc l =>
      match nth_error σ l with
      | Some (OCell w) => pmatch σ p w
      | _ => None
      end
  | _, _ => None
  end.

(** The first branch whose pattern matches, with the bound values. *)
Fixpoint first_match (σ : store) (bs : list (pat * expr)) (v : expr)
    : option (list expr * expr) :=
  match bs with
  | [] => None
  | (p, b) :: bs' =>
      match pmatch σ p v with
      | Some vs => Some (vs, b)
      | None => first_match σ bs' v
      end
  end.

(** ** Notations

    - [⟨σ ∣ K ▷ e⟩], [⟨σ ∣ K ◁ v⟩], [⟨σ ∣ K ⇑ c k v⟩] : the states above;
    - [s ⟶[ge] s']  : one step ([step ge s s']);
    - [s ⟶*[ge] s'] : any number of steps ([star ge s s']). *)

Notation "⟨ σ ∣ K ▷ e ⟩" := (SEval σ K e)
  (at level 0, σ at level 200, K at level 200, e at level 200,
   format "⟨ σ  ∣  K  ▷  e ⟩").
Notation "⟨ σ ∣ K ◁ v ⟩" := (SRet σ K v)
  (at level 0, σ at level 200, K at level 200, v at level 200,
   format "⟨ σ  ∣  K  ◁  v ⟩").
Notation "⟨ σ ∣ K ⇑ c k v ⟩" := (SJump σ K c k v)
  (at level 0, σ at level 200, K at level 200, c at level 0, k at level 0,
   v at level 200, format "⟨ σ  ∣  K  ⇑  c  k  v ⟩").

(** The state reached by a store operation. *)
Definition mres_state (K : stack) (r : mres) : state :=
  match r with
  | MOk σ v => ⟨σ ∣ K ◁ v⟩
  | MAbort => SAbort
  end.

Reserved Notation "s ⟶[ ge ] s'"
  (at level 70, ge at level 200, no associativity, format "s  ⟶[ ge ]  s'").
Reserved Notation "s ⟶*[ ge ] s'"
  (at level 70, ge at level 200, no associativity, format "s  ⟶*[ ge ]  s'").

Inductive step (ge : genv) : state -> state -> Prop :=
(* ---- evaluation: push a frame or produce a value ---- *)
| S_Lit σ K l :
    ⟨σ ∣ K ▷ ELit l⟩ ⟶[ge] ⟨σ ∣ K ◁ ELit l⟩
| S_Lam σ K ps r b :
    ⟨σ ∣ K ▷ ELam ps r b⟩ ⟶[ge] ⟨σ ∣ K ◁ ELam ps r b⟩
| S_Global σ K f ts fd :
    lookup_fn ge f = Some fd ->
    ⟨σ ∣ K ▷ EGlobal f ts⟩
      ⟶[ge] ⟨σ ∣ K ◁ ELam (map (tsubst (inst ts)) (fd_params fd))
                           (tsubst (inst ts) (fd_ret fd))
                           (esubst_ty (inst ts) (fd_body fd))⟩
| S_App σ K f args :
    ⟨σ ∣ K ▷ EApp f args⟩ ⟶[ge] ⟨σ ∣ FAppFun args :: K ▷ f⟩
| S_Let σ K e1 e2 :
    ⟨σ ∣ K ▷ ELet e1 e2⟩ ⟶[ge] ⟨σ ∣ FLet e2 :: K ▷ e1⟩
| S_If σ K c t e :
    ⟨σ ∣ K ▷ EIf c t e⟩ ⟶[ge] ⟨σ ∣ FIf t e :: K ▷ c⟩
| S_TupleNil σ K :
    ⟨σ ∣ K ▷ ETuple []⟩ ⟶[ge] ⟨σ ∣ K ◁ ETuple []⟩
| S_TupleCons σ K e es :
    ⟨σ ∣ K ▷ ETuple (e :: es)⟩ ⟶[ge] ⟨σ ∣ FTuple [] es :: K ▷ e⟩
| S_Proj σ K e i :
    ⟨σ ∣ K ▷ EProj e i⟩ ⟶[ge] ⟨σ ∣ FProj i :: K ▷ e⟩
| S_PrimNil σ K op l :
    prim_eval op [] = PVal l ->
    ⟨σ ∣ K ▷ EPrim op []⟩ ⟶[ge] ⟨σ ∣ K ◁ ELit l⟩
| S_PrimNilAbort σ K op :
    prim_eval op [] = PAbort ->
    ⟨σ ∣ K ▷ EPrim op []⟩ ⟶[ge] SAbort
| S_PrimCons σ K op e es :
    ⟨σ ∣ K ▷ EPrim op (e :: es)⟩ ⟶[ge] ⟨σ ∣ FPrim op [] es :: K ▷ e⟩

(* ---- return: consume the top frame ---- *)
| S_AppFunNil σ K ps r b :
    ⟨σ ∣ FAppFun [] :: K ◁ ELam ps r b⟩ ⟶[ge] ⟨σ ∣ K ▷ subst (args_sub []) b⟩
| S_AppFunCons σ K f a args :
    ⟨σ ∣ FAppFun (a :: args) :: K ◁ f⟩ ⟶[ge] ⟨σ ∣ FAppArg f [] args :: K ▷ a⟩
| S_AppArgLast σ K ps r b done v :
    ⟨σ ∣ FAppArg (ELam ps r b) done [] :: K ◁ v⟩
      ⟶[ge] ⟨σ ∣ K ▷ subst (args_sub (done ++ [v])) b⟩
| S_AppArgNext σ K f done v a rest :
    ⟨σ ∣ FAppArg f done (a :: rest) :: K ◁ v⟩
      ⟶[ge] ⟨σ ∣ FAppArg f (done ++ [v]) rest :: K ▷ a⟩
| S_LetRet σ K e2 v :
    ⟨σ ∣ FLet e2 :: K ◁ v⟩ ⟶[ge] ⟨σ ∣ K ▷ subst (args_sub [v]) e2⟩
| S_IfTrue σ K t e :
    ⟨σ ∣ FIf t e :: K ◁ ELit (LBool true)⟩ ⟶[ge] ⟨σ ∣ K ▷ t⟩
| S_IfFalse σ K t e :
    ⟨σ ∣ FIf t e :: K ◁ ELit (LBool false)⟩ ⟶[ge] ⟨σ ∣ K ▷ e⟩
| S_TupleLast σ K done v :
    ⟨σ ∣ FTuple done [] :: K ◁ v⟩ ⟶[ge] ⟨σ ∣ K ◁ ETuple (done ++ [v])⟩
| S_TupleNext σ K done v e rest :
    ⟨σ ∣ FTuple done (e :: rest) :: K ◁ v⟩ ⟶[ge] ⟨σ ∣ FTuple (done ++ [v]) rest :: K ▷ e⟩
| S_ProjRet σ K i vs v :
    nth_error vs i = Some v ->
    ⟨σ ∣ FProj i :: K ◁ ETuple vs⟩ ⟶[ge] ⟨σ ∣ K ◁ v⟩
| S_PrimLast σ K op done v ls l :
    as_lits (done ++ [v]) = Some ls ->
    prim_eval op ls = PVal l ->
    ⟨σ ∣ FPrim op done [] :: K ◁ v⟩ ⟶[ge] ⟨σ ∣ K ◁ ELit l⟩
| S_PrimLastAbort σ K op done v ls :
    as_lits (done ++ [v]) = Some ls ->
    prim_eval op ls = PAbort ->
    ⟨σ ∣ FPrim op done [] :: K ◁ v⟩ ⟶[ge] SAbort
| S_PrimNext σ K op done v e rest :
    ⟨σ ∣ FPrim op done (e :: rest) :: K ◁ v⟩ ⟶[ge] ⟨σ ∣ FPrim op (done ++ [v]) rest :: K ▷ e⟩

(* ---- data types (milestone M2) ---- *)
| S_Constr σ K T c ts e :
    ⟨σ ∣ K ▷ EConstr T c ts e⟩ ⟶[ge] ⟨σ ∣ FConstr T c ts :: K ▷ e⟩
| S_Match σ K e τ bs :
    ⟨σ ∣ K ▷ EMatch e τ bs⟩ ⟶[ge] ⟨σ ∣ FMatch τ bs :: K ▷ e⟩
| S_ConstrRet σ K T c ts v :
    ⟨σ ∣ FConstr T c ts :: K ◁ v⟩ ⟶[ge] ⟨σ ∣ K ◁ EConstr T c ts v⟩
| S_MatchRet σ K τ bs v vs b :
    first_match σ bs v = Some (vs, b) ->
    ⟨σ ∣ FMatch τ bs :: K ◁ v⟩ ⟶[ge] ⟨σ ∣ K ▷ subst (args_sub vs) b⟩
(** No branch matches: MoonBit panics.  Exhaustiveness is a static
    analysis (milestone M8), not part of type soundness. *)
| S_MatchFail σ K τ bs v :
    first_match σ bs v = None ->
    ⟨σ ∣ FMatch τ bs :: K ◁ v⟩ ⟶[ge] SAbort

(* ---- store (milestone M3) ---- *)
| S_Loc σ K l :
    ⟨σ ∣ K ▷ ELoc l⟩ ⟶[ge] ⟨σ ∣ K ◁ ELoc l⟩
| S_MemNil σ K op r :
    mem_eval op σ [] = Some r ->
    ⟨σ ∣ K ▷ EMem op []⟩ ⟶[ge] mres_state K r
| S_MemCons σ K op e es :
    ⟨σ ∣ K ▷ EMem op (e :: es)⟩ ⟶[ge] ⟨σ ∣ FMem op [] es :: K ▷ e⟩
| S_MemLast σ K op done v r :
    mem_eval op σ (done ++ [v]) = Some r ->
    ⟨σ ∣ FMem op done [] :: K ◁ v⟩ ⟶[ge] mres_state K r
| S_MemNext σ K op done v e rest :
    ⟨σ ∣ FMem op done (e :: rest) :: K ◁ v⟩ ⟶[ge] ⟨σ ∣ FMem op (done ++ [v]) rest :: K ▷ e⟩

(* ---- loops and jumps (milestone M3) ---- *)
| S_Loop σ K e ps τ b :
    ⟨σ ∣ K ▷ ELoop e ps τ b⟩ ⟶[ge] ⟨σ ∣ FLoopInit ps τ b :: K ▷ e⟩
| S_LoopEnter σ K ps τ b vs :
    ⟨σ ∣ FLoopInit ps τ b :: K ◁ ETuple vs⟩ ⟶[ge] ⟨σ ∣ FLoop ps τ b :: K ▷ subst (args_sub vs) b⟩
(** The body finished without jumping: its value is the loop's result. *)
| S_LoopRet σ K ps τ b v :
    ⟨σ ∣ FLoop ps τ b :: K ◁ v⟩ ⟶[ge] ⟨σ ∣ K ◁ v⟩
| S_Jump σ K c k e τ :
    ⟨σ ∣ K ▷ EJump c k e τ⟩ ⟶[ge] ⟨σ ∣ FJump c k :: K ▷ e⟩
| S_JumpRet σ K c k v :
    ⟨σ ∣ FJump c k :: K ◁ v⟩ ⟶[ge] ⟨σ ∣ K ⇑ c k v⟩
(** Unwinding: discard frames up to the target loop. *)
| S_UnwindPop σ F K c k v :
    is_loop F = false ->
    ⟨σ ∣ F :: K ⇑ c k v⟩ ⟶[ge] ⟨σ ∣ K ⇑ c k v⟩
| S_UnwindOuter σ K ps τ b c k v :
    ⟨σ ∣ FLoop ps τ b :: K ⇑ c (S k) v⟩ ⟶[ge] ⟨σ ∣ K ⇑ c k v⟩
| S_Break σ K ps τ b v :
    ⟨σ ∣ FLoop ps τ b :: K ⇑ CBreak 0 v⟩ ⟶[ge] ⟨σ ∣ K ◁ v⟩
| S_Continue σ K ps τ b vs :
    ⟨σ ∣ FLoop ps τ b :: K ⇑ CCont 0 (ETuple vs)⟩
      ⟶[ge] ⟨σ ∣ FLoop ps τ b :: K ▷ subst (args_sub vs) b⟩

(* ---- explicit panic ---- *)
| S_Abort σ K τ :
    ⟨σ ∣ K ▷ EAbort τ⟩ ⟶[ge] SAbort

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
  | ⟨_ ∣ [] ◁ v⟩ => value v
  | SAbort => True
  | _ => False
  end.

(** A state that is not terminal and cannot step is stuck: this is what
    type soundness rules out.  (In particular a jump that reaches the
    empty stack is stuck.) *)
Definition stuck (ge : genv) (s : state) : Prop :=
  ~ final s /\ ~ exists s', s ⟶[ge] s'.
