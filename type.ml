type exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

type program = exp

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ " ^ ")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty -> match e with
	| CONST n -> [(ty, TyInt)]
	| VAR x -> [(ty, TEnv.find tenv x)]
	| ADD (e1, e2) -> [(ty, TyInt)]@(gen_equations tenv e1 TyInt)@(gen_equations tenv e2 TyInt)
	| SUB (e1, e2) -> [(ty, TyInt)]@(gen_equations tenv e1 TyInt)@(gen_equations tenv e2 TyInt)
	| MUL (e1, e2) -> [(ty, TyInt)]@(gen_equations tenv e1 TyInt)@(gen_equations tenv e2 TyInt)
	| DIV (e1, e2) -> [(ty, TyInt)]@(gen_equations tenv e1 TyInt)@(gen_equations tenv e2 TyInt)
	| ISZERO e1 -> [(ty, TyBool)]@(gen_equations tenv e1 TyInt)
	| IF (e1, e2, e3) -> (gen_equations tenv e1 TyBool)@(gen_equations tenv e2 ty)@(gen_equations tenv e3 ty)
	| LET (x, e1, e2) -> let a = fresh_tyvar () in
			       (gen_equations tenv e1 a)@(gen_equations (TEnv.extend (x, a) tenv) e2 ty)
	| LETREC (f, x, e1, e2) -> let a1 = fresh_tyvar() in
                                     let a2 = fresh_tyvar() in
                                       (gen_equations (TEnv.extend (f, TyFun(a2, a1)) (TEnv.extend (x, a2) tenv)) e1 a1)@(gen_equations (TEnv.extend (f, TyFun(a2, a1)) tenv) e2 ty)
                                       
	| PROC (x, e1) -> let a1 = fresh_tyvar () in
			    let a2 = fresh_tyvar () in
			      [(ty, TyFun(a1, a2))]@(gen_equations (TEnv.extend (x, a1) tenv) e1 a2)
	| CALL (e1, e2) -> let a = fresh_tyvar () in
					     (gen_equations tenv e1 (TyFun(a ,ty)))@(gen_equations tenv e2 a)

	
	
let rec check : var -> typ -> bool
= fun x t -> match t with
	| TyInt -> false
	| TyBool -> false
	| TyVar y -> x = y
	| TyFun (t1, t2) -> check x t1 || check x t2

let rec unify : (typ * typ) -> Subst.t -> Subst.t
=fun eqn st -> match eqn with
	| (TyInt, TyInt) -> st
	| (TyBool, TyBool) -> st
	| (TyVar x, t) -> if check x t then raise TypeError else Subst.extend x t st
	| (t, TyVar x) -> unify (TyVar x, t) st
	| (TyFun (t1, t2), TyFun (t3, t4)) -> let sf = unify (t1, t3) st in
						let t5 = Subst.apply t2 sf in
						  let t6 = Subst.apply t4 sf in
						    unify (t5, t6) sf
	| _ -> raise TypeError
	
let rec unifyall : typ_eqn -> Subst.t -> Subst.t
=fun eqn st -> match eqn with
	| [] -> st
	| (t1, t2) :: tl -> let sf = unify ((Subst.apply t1 st), (Subst.apply t2 st)) st in
			      unifyall tl sf

	
	
let solve : typ_eqn -> Subst.t
=fun eqns -> unifyall eqns Subst.empty

let typeof : exp -> typ (* Do not modify this function *)
=fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns;
          print_endline "" in
  let subst = solve eqns in
  let ty = Subst.apply new_tv subst in
   print_endline "= Substitution = ";
    Subst.print subst;
    print_endline "";
    print_endline ("Type: " ^ string_of_type ty);
    print_endline "";
    ty
