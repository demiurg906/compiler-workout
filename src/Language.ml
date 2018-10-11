(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Ostap.Combinators

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    let int_to_bool i = if (i == 0) then false else true
    let bool_to_int b = if b then 1 else 0

    let eval_binop op left right = match op with
        | "!!" -> bool_to_int(int_to_bool(left) || int_to_bool(right))
        | "&&" -> bool_to_int(int_to_bool(left) && int_to_bool(right))
        | "==" -> bool_to_int(left == right)
        | "!=" -> bool_to_int(left <> right)
        | "<=" -> bool_to_int(left <= right)
        | ">=" -> bool_to_int(left >= right)
        | "<"  -> bool_to_int(left < right)
        | ">"  -> bool_to_int(left > right)
        | "+"  -> left + right
        | "-"  -> left - right
        | "*"  -> left * right
        | "/"  -> left / right
        | "%"  -> left mod right
        | _ -> failwith("Unknown operator")

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
      parse:
	  !(Ostap.Util.expr 
             (fun x -> x)
	     (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
		`Lefta, ["!!"];
		`Lefta, ["&&"];
		`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
		`Lefta, ["+" ; "-"];
		`Lefta, ["*" ; "/"; "%"];
              |] 
	     )
	     primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )
    
  end

let default x opt = match opt with
        | Some v -> v
        | None   -> x

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of Expr.t * t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env ((state, input, output) as config) stmt = 
      match stmt with
        | Read variable ->
          let value :: input' = input in
          let state' = State.update variable value state 
          in (state', input', output)
        
        | Write expr -> 
          let output' = output @ [Expr.eval state expr]
          in (state, input, output')
        
        | Assign (variable, expr) -> 
          let state' = State.update variable (Expr.eval state expr) state 
          in (state', input, output)
        
        | Seq (stmt1, stmt2) -> eval env (eval env config stmt1) stmt2
        
        | Skip -> config
        
        | If (cond, then_block, else_block) -> 
          if (Expr.eval state cond <> 0)
          then eval env config then_block
          else eval env config else_block
        
        | While (cond, block) ->
          if (Expr.eval state cond <> 0)
          then let config' = eval env config block
            in eval env config' (While (cond, block))
          else config
        
        | Repeat (cond, block) ->
          let ((state', input', output') as config') = eval env config block
          in if (Expr.eval state' cond == 0)
              then eval env config' (Repeat (cond, block))
              else config'
        
        | Call (func_name, args) ->
          let args_values = List.map (Expr.eval state) args in
          let (args, local_vars, body) = env#definition func_name in
          let new_state = State.push_scope state (args @ local_vars) in
          let updater = (fun state arg value -> State.update arg value state) in
          let updated_new_state = List.fold_left2 updater new_state args args_values in
          let (state', input', output') = eval env (updated_new_state, input, output) body
          in (State.drop_scope state' state, input', output')

    (* Statement parser *)
    ostap (
      read: -"read" -"(" id:IDENT -")" { Read id };
      write: -"write" -"(" e:!(Expr.parse) -")" { Write e };
      assign: id:IDENT -":=" expr:!(Expr.parse) { Assign (id, expr)};
      skip: -"skip" { Skip };
      
      if_op: 
        -"if" cond:!(Expr.parse) -"then" then_block:parse else_block:else_stmt -"fi" { If (cond, then_block, else_block) }
      | -"if" cond:!(Expr.parse) -"then" then_block:parse -"fi" { If (cond, then_block, Skip) };
      
      else_stmt:
        -"else" block:parse { block }
      | -"elif" cond:!(Expr.parse) -"then" then_block:parse else_block:else_stmt { If (cond, then_block, else_block) };

      for_loop: -"for" start:parse -"," cond:!(Expr.parse) -"," step:parse -"do" block:parse -"od" { Seq (start, While (cond, Seq (block, step))) };

      while_loop: -"while" cond:!(Expr.parse) -"do" block:parse -"od" { While (cond, block) };
      
      repeat_loop: -"repeat" block:parse -"until" cond:!(Expr.parse) { Repeat (cond, block) };      
      
      func_call: func_name:IDENT -"(" args:(!(Util.list)[ostap (!(Expr.parse))])? -")" { Call (func_name, default [] args) };

      statement: read | write | assign | skip | if_op | for_loop | while_loop | repeat_loop | func_call;
      
      parse: <st::sts> :
        !(Util.listBy)
        [ostap (-";")]
        [statement]
        { List.fold_left (fun st1 st2 -> Seq (st1, st2) ) st sts}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (                                      
      parse: -"fun" func_name:IDENT -"(" args:!(Util.list)[ostap (IDENT)]? -")"
             local_vars:(-"local" !(Util.list)[ostap (IDENT)])? -"{" body:!(Stmt.parse) -"}" 
             {(func_name, (default [] args, default [] local_vars, body))}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
