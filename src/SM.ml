open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)

let rec eval env ((call_stack, stack, ((state, input, output) as conf)) as config) prog = match prog with
  | [] -> config
  | inst :: prog -> match inst with
      | JMP label -> eval env config (env#labeled label)
      | CJMP (op, label) -> 
        let var::stack' = stack in 
        let predicate = match op with
          | "z"  -> (==) 0
          | "nz" -> (!=) 0
        in if predicate var
            then eval env config (env#labeled label)
            else eval env config prog
      | CALL func -> eval env ((prog, state)::call_stack, stack, conf) (env#labeled func)
      
      | END -> 
        let (prog, state')::call_stack' = call_stack
        in eval env (call_stack', stack, (State.drop_scope state state', input, output)) prog

      | _ ->
        let config' = begin match inst with
          | BINOP op -> 
            let right::left::stack' = stack
            in (call_stack, (Language.Expr.eval_binop op left right) :: stack', conf)
          | CONST x -> (call_stack, x :: stack, conf)
          | READ ->
            let x :: input' = input
            in (call_stack, x :: stack, (state, input', output))
          | WRITE ->
            let x :: stack' = stack
            in (call_stack, stack', (state, input, output @ [x]))
          | LD var ->
            let value = State.eval state var
            in (call_stack, value :: stack, conf)
          
          | ST var ->
            let x :: stack' = stack
            in (call_stack, stack', (State.update var x state, input, output))
          
          | LABEL label -> config
          
          | BEGIN (p, l) ->
            let new_state = State.push_scope state (p @ l) in
            let (state', stack') = List.fold_right (
                fun p (st, x::stack') -> (State.update p x st, stack')  
              ) p (new_state, stack) 
            in (call_stack, stack, (state', input, output))
        end
        in eval env config' prog

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

class label_manager =
 object (self)
   val mutable label = 0

   method new_label = let last_label = label in
     label <- label + 1; Printf.sprintf "L%d" last_label
end

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile (defs, prog) =
  let rec compile_stmt label_manager =
    let rec expr = function
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
    in
    function
    | Stmt.Seq (s1, s2)  -> compile_stmt label_manager s1 @ compile_stmt label_manager s2
    | Stmt.Read x        -> [READ; ST x]
    | Stmt.Write e       -> expr e @ [WRITE]
    | Stmt.Assign (x, e) -> expr e @ [ST x]
    | Stmt.Skip -> []
    | Stmt.If (cond, then_block, else_block) -> 
      let else_label = label_manager#new_label in
      let end_label  = label_manager#new_label
      in expr cond
        @ [CJMP ("z", else_label)] 
        @ compile_stmt label_manager then_block 
        @ [JMP end_label; LABEL else_label] 
        @ compile_stmt label_manager else_block
        @ [LABEL end_label]
    
    | Stmt.While (cond, block) ->
      let loop_label = label_manager#new_label in
      let end_label  = label_manager#new_label 
      in [LABEL loop_label] 
        @ expr cond
        @ [CJMP ("z", end_label)]
        @ compile_stmt label_manager block
        @ [JMP loop_label; LABEL end_label]
    
    | Stmt.Repeat (cond, block) ->
      let loop_label = label_manager#new_label
      in [LABEL loop_label]
        @ compile_stmt label_manager block
        @ expr cond
        @ [CJMP ("z", loop_label)]
    
    | Stmt.Call (func_name, args) -> List.concat (List.map expr args) @ [CALL func_name]
  in

  let compile_procedure label_manager (func_name, (args, local_vars, body)) =
    [LABEL func_name; BEGIN (args, local_vars)] 
    @ compile_stmt label_manager body
    @ [END]
  in
  
  let label_manager = new label_manager in 
  let main_label = label_manager#new_label
  
  in [JMP main_label]
   @ List.concat (List.map (compile_procedure label_manager) defs)
   @ [LABEL main_label]
   @ compile_stmt label_manager prog
