(* Smoke tests: the certified checker computes inside Rocq. *)
From Stdlib Require Import List String ZArith.
From MoonRocq.Prelude Require Import Result.
From MoonRocq.Core Require Import Syntax Check Theorems.
Import ListNotations.
Open Scope string_scope.

(* fn[T] id(x : T) -> T { x } *)
Definition fd_id : fdef :=
  {| fd_name := "id"; fd_tparams := 1; fd_params := [TVar 0]; fd_ret := TVar 0; fd_eff := TNever;
     fd_body := EVar 0 |}.

(* fn fact(n : Int) -> Int { if n <= 0 { 1 } else { n * fact(n - 1) } } *)
Definition fd_fact : fdef :=
  {| fd_name := "fact"; fd_tparams := 0; fd_params := [TInt I32]; fd_ret := TInt I32; fd_eff := TNever;
     fd_body :=
       EIf (EPrim (PIntCmp CLe I32) [EVar 0; ELit (LInt I32 0)])
           (ELit (LInt I32 1))
           (EPrim (PIntArith AMul I32)
              [EVar 0; EApp (EGlobal "fact" [])
                            [EPrim (PIntArith ASub I32) [EVar 0; ELit (LInt I32 1)]]]) |}.

(* enum List[T] { Nil; Cons(T, List[T]) } *)
Definition td_list : tdef :=
  mk_tdef "List" 1 [mk_cdef "Nil" []; mk_cdef "Cons" [TVar 0; TData "List" [TVar 0]]] false.

(* fn[T] length(l : List[T]) -> Int { match l { Nil => 0; Cons(_, t) => 1 + length(t) } } *)
Definition fd_length : fdef :=
  {| fd_name := "length"; fd_tparams := 1; fd_params := [TData "List" [TVar 0]];
     fd_ret := TInt I32; fd_eff := TNever;
     fd_body :=
       EMatch (EVar 0) (TInt I32)
         [ (PConstr "Nil" [], ELit (LInt I32 0));
           (PConstr "Cons" [PWild; PVar],
            EPrim (PIntArith AAdd I32)
              [ELit (LInt I32 1); EApp (EGlobal "length" [TVar 0]) [EVar 0]]) ] |}.

Definition ge : genv := mk_genv [td_list] [fd_id; fd_fact; fd_length].

Definition nil_int : expr := EConstr "List" "Nil" [TInt I32] (ETuple []).
Definition cons_int (e l : expr) : expr := EConstr "List" "Cons" [TInt I32] (ETuple [e; l]).


Definition type_of (e : expr) : option ty :=
  match check_program ge e with
  | Ok (exist _ τ _) => Some τ
  | Err _ => None
  end.

(* fact(id[Int](5)) : Int *)
Example ex_ok :
  type_of (EApp (EGlobal "fact" []) [EApp (EGlobal "id" [TInt I32]) [ELit (LInt I32 5)]])
  = Some (TInt I32).
Proof. vm_compute. reflexivity. Qed.

(* (id[Bool], fact) : ((Bool) -> Bool, (Int) -> Int) *)
Example ex_tuple :
  type_of (ETuple [EGlobal "id" [TBool]; EGlobal "fact" []])
  = Some (TTuple [TArrow [TBool] TBool TNever; TArrow [TInt I32] (TInt I32) TNever]).
Proof. vm_compute. reflexivity. Qed.

(* if true { 1 } else { "s" } is rejected *)
Example ex_mismatch :
  type_of (EIf (ELit (LBool true)) (ELit (LInt I32 1)) (ELit (LString [])))
  = None.
Proof. vm_compute. reflexivity. Qed.

(* id applied with the wrong number of type arguments is rejected *)
Example ex_targ_arity : type_of (EGlobal "id" []) = None.
Proof. vm_compute. reflexivity. Qed.

(* duplicate global names are rejected *)
Example ex_dup :
  match check_genv (mk_genv [] [fd_id; fd_id]) with Ok _ => false | Err _ => true end = true.
Proof. vm_compute. reflexivity. Qed.

(* length[Int](Cons(1, Nil)) : Int *)
Example ex_data :
  type_of (EApp (EGlobal "length" [TInt I32]) [cons_int (ELit (LInt I32 1)) nil_int])
  = Some (TInt I32).
Proof. vm_compute. reflexivity. Qed.

(* match Cons(1, Nil) { Cons(x, _) => x == 1; _ => false } : Bool *)
Example ex_match :
  type_of (EMatch (cons_int (ELit (LInt I32 1)) nil_int) TBool
             [ (PConstr "Cons" [PVar; PWild], EPrim (PIntCmp CEq I32) [EVar 0; ELit (LInt I32 1)]);
               (PWild, ELit (LBool false)) ])
  = Some TBool.
Proof. vm_compute. reflexivity. Qed.

(* a constructor pattern with the wrong number of fields is rejected *)
Example ex_pat_arity :
  type_of (EMatch nil_int TBool [(PConstr "Cons" [PVar], ELit (LBool true))]) = None.
Proof. vm_compute. reflexivity. Qed.

(* a constructor of another type is rejected *)
Example ex_bad_ctor :
  type_of (EConstr "List" "Some" [TInt I32] (ETuple [])) = None.
Proof. vm_compute. reflexivity. Qed.

(* an empty match has its annotated type *)
Example ex_empty_match :
  type_of (ELam [TData "List" [TBool]] TString TNever (EMatch (EVar 0) TString [])) =
  Some (TArrow [TData "List" [TBool]] TString TNever).
Proof. vm_compute. reflexivity. Qed.

(* signatures must mention only declared types, with the right arity *)
Example ex_ill_formed :
  match check_genv (mk_genv [td_list]
          [{| fd_name := "f"; fd_tparams := 0; fd_params := [TData "List" []];
              fd_ret := TUnit; fd_eff := TNever; fd_body := ELit LUnit |}]) with
  | Ok _ => false | Err _ => true end = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- milestone M3: store and loops ---- *)

Definition int (z : Z) : expr := ELit (LInt I32 z).
Definition get_i (x : nat) : expr := EMem (MGet (TInt I32)) [EVar x].

(* let mut i = 0; while i < 3 { i = i + 1 }; i *)
Example ex_while :
  type_of
    (ELet (EMem (MRef (TInt I32)) [int 0])
      (ELet (ELoop (ETuple []) [] TUnit
               (EIf (EPrim (PIntCmp CLt I32) [get_i 0; int 3])
                    (ELet (EMem (MSet (TInt I32))
                             [EVar 0; EPrim (PIntArith AAdd I32) [get_i 0; int 1]])
                          (EJump CCont 0 (ETuple []) TUnit))
                    (ELit LUnit)))
            (get_i 1)))
  = Some (TInt I32).
Proof. vm_compute. reflexivity. Qed.

(* [1, 2][0] : Int, and [1, 2].length() : Int *)
Example ex_array :
  type_of (ETuple [EMem (MIndex AGrow (TInt I32)) [EMem (MArray AGrow (TInt I32) 2) [int 1; int 2]; int 0];
                   EMem (MLength AGrow (TInt I32)) [EMem (MArray AGrow (TInt I32) 0) []]])
  = Some (TTuple [TInt I32; TInt I32]).
Proof. vm_compute. reflexivity. Qed.

(* push is only defined on growable arrays *)
Example ex_push_fixed :
  type_of (EMem (MPush (TInt I32)) [EMem (MArray AFixed (TInt I32) 0) []; int 1]) = None.
Proof. vm_compute. reflexivity. Qed.

(* a loop whose body breaks with its result: loop (x) { break x + 1 } *)
Example ex_break :
  type_of (ELoop (ETuple [int 1]) [TInt I32] (TInt I32)
             (EJump CBreak 0 (EPrim (PIntArith AAdd I32) [EVar 0; int 1]) (TInt I32)))
  = Some (TInt I32).
Proof. vm_compute. reflexivity. Qed.

(* a break value must have the loop's result type *)
Example ex_break_type :
  type_of (ELoop (ETuple []) [] (TInt I32) (EJump CBreak 0 (ELit (LBool true)) (TInt I32)))
  = None.
Proof. vm_compute. reflexivity. Qed.

(* continue passes the loop arguments *)
Example ex_continue_args :
  type_of (ELoop (ETuple [int 1]) [TInt I32] TUnit
             (EJump CCont 0 (ETuple [ELit (LBool true)]) TUnit))
  = None.
Proof. vm_compute. reflexivity. Qed.

(* no break outside a loop, and none across a function boundary *)
Example ex_no_loop : type_of (EJump CBreak 0 (ELit LUnit) TUnit) = None.
Proof. vm_compute. reflexivity. Qed.

Example ex_lambda_boundary :
  type_of (ELoop (ETuple []) [] TUnit
             (EApp (ELam [] TUnit TNever (EJump CBreak 0 (ELit LUnit) TUnit)) []))
  = None.
Proof. vm_compute. reflexivity. Qed.

(* store locations do not occur in programs *)
Example ex_loc : type_of (ELoc 0) = None.
Proof. vm_compute. reflexivity. Qed.

(* panic() has its annotated type, and may stand for any value *)
Example ex_abort :
  type_of (EIf (ELit (LBool true)) (int 1) (EAbort (TInt I32))) = Some (TInt I32).
Proof. vm_compute. reflexivity. Qed.

(* ---- milestone M4: errors ---- *)

(* suberror E { E(Int) } *)
Definition td_err : tdef := mk_tdef "E" 0 [mk_cdef "E" [TInt I32]] true.
Definition ge_err : genv := mk_genv [td_list; td_err] [fd_id; fd_fact; fd_length].
Definition err_of (z : Z) : expr := EConstr "E" "E" [] (ETuple [int z]).

Definition type_of_err (e : expr) : option ty :=
  match check_program ge_err e with
  | Ok (exist _ τ _) => Some τ
  | Err _ => None
  end.

(* try raise E(1) catch { E(x) => x } : Int *)
Example ex_try :
  type_of_err (ETry (ERaise (err_of 1) (TInt I32)) (TData "E" [])
                    (EMatch (EVar 0) (TInt I32) [(PConstr "E" [PVar], EVar 0)])
                    (EVar 0))
  = Some (TInt I32).
Proof. vm_compute. reflexivity. Qed.

(* main is noraise: an uncaught raise is rejected *)
Example ex_uncaught : type_of_err (ERaise (err_of 1) TUnit) = None.
Proof. vm_compute. reflexivity. Qed.

(* errors are promoted to Error explicitly, and matched with PUp *)
Example ex_up :
  type_of_err (EMatch (EUp "E" (err_of 2)) (TInt I32)
                 [(PUp "E" (PConstr "E" [PVar]), EVar 0); (PWild, int 0)])
  = Some (TInt I32).
Proof. vm_compute. reflexivity. Qed.

(* raising E where Error is caught needs the promotion *)
Example ex_no_subeffect :
  type_of_err (ETry (ERaise (err_of 1) TUnit) TError (ELit LUnit) (EVar 0)) = None.
Proof. vm_compute. reflexivity. Qed.

(* a function raising E may only be called where E may escape *)
Example ex_effect :
  let f := ELam [] TUnit (TData "E" []) (ERaise (err_of 1) TUnit) in
  (type_of_err (EApp f []), type_of_err (ETry (EApp f []) (TData "E" []) (ELit LUnit) (EVar 0)))
  = (None, Some TUnit).
Proof. vm_compute. reflexivity. Qed.

(* defer cleanups may not jump *)
Example ex_defer :
  (type_of_err (EDefer false (ELit LUnit) (int 1)),
   type_of_err (ELoop (ETuple []) [] TUnit
                  (EDefer false (EJump CBreak 0 (ELit LUnit) TUnit) (ELit LUnit))))
  = (Some (TInt I32), None).
Proof. vm_compute. reflexivity. Qed.
