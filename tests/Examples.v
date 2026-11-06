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

(* enum List[T] { Nil; Cons(T, List[T]) } *)
Definition td_list : tdef :=
  mk_tdef "List" 1 [mk_cdef "Nil" []; mk_cdef "Cons" [TVar 0; TData "List" [TVar 0]]].

(* fn[T] length(l : List[T]) -> Int { match l { Nil => 0; Cons(_, t) => 1 + length(t) } } *)
Definition fd_length : fdef :=
  {| fd_name := "length"; fd_tparams := 1; fd_params := [TData "List" [TVar 0]];
     fd_ret := TInt I32;
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
  type_of (ELam [TData "List" [TBool]] TString (EMatch (EVar 0) TString [])) =
  Some (TArrow [TData "List" [TBool]] TString).
Proof. vm_compute. reflexivity. Qed.

(* signatures must mention only declared types, with the right arity *)
Example ex_ill_formed :
  match check_genv (mk_genv [td_list]
          [{| fd_name := "f"; fd_tparams := 0; fd_params := [TData "List" []];
              fd_ret := TUnit; fd_body := ELit LUnit |}]) with
  | Ok _ => false | Err _ => true end = true.
Proof. vm_compute. reflexivity. Qed.
