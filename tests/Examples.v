(* Smoke tests: the certified checker computes inside Rocq. *)
From Stdlib Require Import List String ZArith.
From MoonRocq.Prelude Require Import Result.
From MoonRocq.Core Require Import Syntax Check Theorems.
Import ListNotations.
Open Scope string_scope.

(* fn[T] id(x : T) -> T { x } *)
Definition fd_id : fdef :=
  {| fd_name := "id"; fd_tparams := 1; fd_params := [TVar 0]; fd_ret := TVar 0;
     fd_body := EVar 0 |}.

(* fn fact(n : Int) -> Int { if n <= 0 { 1 } else { n * fact(n - 1) } } *)
Definition fd_fact : fdef :=
  {| fd_name := "fact"; fd_tparams := 0; fd_params := [TInt I32]; fd_ret := TInt I32;
     fd_body :=
       EIf (EPrim (PIntCmp CLe I32) [EVar 0; ELit (LInt I32 0)])
           (ELit (LInt I32 1))
           (EPrim (PIntArith AMul I32)
              [EVar 0; EApp (EGlobal "fact" [])
                            [EPrim (PIntArith ASub I32) [EVar 0; ELit (LInt I32 1)]]]) |}.

Definition ge : genv := [fd_id; fd_fact].


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
  = Some (TTuple [TArrow [TBool] TBool; TArrow [TInt I32] (TInt I32)]).
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
  match check_genv [fd_id; fd_id] with Ok _ => false | Err _ => true end = true.
Proof. vm_compute. reflexivity. Qed.
