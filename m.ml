exception UndefSemantics

type program = exp
and exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
  | CALLREF of exp * var
  | SET of var * exp
  | SEQ of exp * exp
  | BEGIN of exp
and var = string

type value = 
    Int of int
  | Bool of bool
  | Closure of var * exp * env 
  | RecClosure of var * var * exp * env
and env = var -> loc
and loc = int
and mem = loc -> value

(*********************************)
(* implementation of environment *)
(*********************************)
(* empty env *)
let empty_env = fun x -> raise (Failure "Environment is empty")
(* extend the environment e with the binding (x, l), where x is a varaible and l is a location *)
let extend_env (x,l) e = fun y -> if x = y then l else (e y)
(* look up the environment e for the variable x *)
let apply_env e x = e x

(*********************************)
(* implementation of memory      *)
(*********************************)
let empty_mem = fun _ -> raise (Failure "Memory is empty")
(* extend the memory m with the binding (l, v), where l is a location and v is a value *)
let extend_mem (l,v) m = fun y -> if l = y then v else (m y)
let apply_mem m l = m l

(* NOTE: you don't need to understand how env and mem work *)

let counter = ref 0

(* calling 'new_location' produces a fresh memory location *)
let new_location () = counter:=!counter+1;!counter

let value2str v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Closure (x,e,env) -> "Closure "
  | RecClosure (f,x,e,env) -> "RecClosure "^f


(* TODO: Implement this function *)
let rec eval : exp -> env -> mem -> value * mem
=fun exp env mem -> 
  match exp with
  | CONST n -> (Int n, mem)
  | VAR x -> (apply_mem mem (apply_env env x), mem)
  
  
  | ADD (e1, e2) -> (match (eval e1 env mem) with
		| (Int n1, mem1) -> (match (eval e2 env mem1) with
				| (Int n2, mem2) -> (Int (n1 + n2), mem2)
				)
		| (_, _) -> raise UndefSemantics  
		)
   
  | SUB (e1, e2) -> (match (eval e1 env mem) with
		| (Int n1, mem1) -> (match (eval e2 env mem1) with
				| (Int n2, mem2) -> (Int (n1 - n2), mem2)
				)
		| (_, _) -> raise UndefSemantics  
		) 
		
  | MUL (e1, e2) -> (match (eval e1 env mem) with
		| (Int n1, mem1) -> (match (eval e2 env mem1) with
				| (Int n2, mem2) -> (Int (n1 * n2), mem2)
				)
		| (_, _) -> raise UndefSemantics  
		)
		 
  | DIV (e1, e2) -> (match (eval e1 env mem) with
		| (Int n1, mem1) -> (match (eval e2 env mem1) with
				| (Int n2, mem2) -> (Int (n1 / n2), mem2)
				)
		| (_, _) -> raise UndefSemantics  
		)
		
  | ISZERO e -> (match (eval e env mem) with
		| (Int n, mem1) -> if (n = 0) then (Bool true, mem1) else (Bool false, mem1)
		| (_, _) -> raise UndefSemantics    
		)
  | READ -> (Int (read_int()), mem)
  
  | IF (e1, e2, e3) -> (match (eval e1 env mem) with
		| (Bool b, mem1) -> if b then (eval e2 env mem1) else (eval e3 env mem1)	
		| (_, _) -> raise UndefSemantics   
		)
  
  
  | LET (x, e1, e2) -> (match (eval e1 env mem) with
		| (v1, mem1) -> let l = new_location()
                  in eval e2 (extend_env (x, l) env) (extend_mem (l, v1) mem1)
		)
		
  | LETREC (f, x, e1, e2) -> let l = new_location()
                in eval e2 (extend_env (f, l) env) (extend_mem (l, RecClosure (f, x, e1, env)) mem)

  | PROC (x, e) -> (Closure (x, e, env), mem)

  | CALL (e1, e2) -> (match (eval e1 env mem) with
		| (Closure (x, e, env1), mem1) -> (match (eval e2 env mem1) with
			| (v, mem2) -> let l = new_location() in eval e (extend_env (x, l) env1) (extend_mem (l, v) mem2)
			)
		| (RecClosure (f, x, e, env1), mem1) -> (match (eval e2 env mem1) with
			| (v, mem2) -> let l1 = new_location() in let l2 = new_location()
				in eval e (extend_env (x , l1) (extend_env (f, l2) env1)) (extend_mem (l1, v) (extend_mem (l2, RecClosure(f, x, e, env1)) mem2))
			)


		| (_, _) -> raise UndefSemantics  
		)

  | CALLREF (e1, y) -> (match (eval e1 env mem) with
		| (Closure (x, e, env1), mem1) -> eval e (extend_env (x, apply_env env y) env1) mem1
		| (RecClosure (f, x, e, env1), mem1) -> let l = new_location() in eval e (extend_env (f, l) (extend_env (x, apply_env env y) env1)) (extend_mem (l, RecClosure (f, x, e, env1)) mem1)

		| (_, _) -> raise UndefSemantics 
		)

  | SET (x, e) -> (match (eval e env mem) with
		| (v, mem1) -> (v, (extend_mem(apply_env env x, v) mem1))
		)
  
  | SEQ (e1, e2) -> (match (eval e1 env mem) with
		| (_, mem1) -> eval e2 env mem1  
		)
  
  | BEGIN e -> eval e env mem

let run : program -> value
=fun pgm -> 
  let (v,m) = eval pgm empty_env empty_mem in
    v
