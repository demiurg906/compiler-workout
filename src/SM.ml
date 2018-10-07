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
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env ((stack, ((state, input, output) as config)) as conf) prog = match prog with
  | [] -> conf
  | inst :: prog -> match inst with
      | JMP label -> eval env conf (env#labeled label)
      | CJMP (op, label) -> 
        let var::stack' = stack in 
        let predicate = match op with
          | "z"  -> (==) 0
          | "nz" -> (!=) 0
        in if predicate var
            then eval env conf (env#labeled label)
            else eval env conf prog
      | _ ->
        let conf' = begin match inst with
          | BINOP op -> 
            let right::left::stack' = stack
            in ((Language.Expr.evalBinop op left right) :: stack', config)
          | CONST x -> (x :: stack, config)
          | READ ->
            let x :: input' = input
            in (x :: stack, (state, input', output))
          | WRITE ->
            let x :: stack' = stack
            in (stack', (state, input, output @ [x]))
          | LD var ->
            let value = state var
            in (value :: stack, config)
          | ST var ->
            let x :: stack' = stack
            in (stack', (Language.Expr.update var x state, input, output))
          | LABEL label -> conf
        end
        in eval env conf' prog


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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

class labelManager =
 object (self)
   val mutable label = 0

   method new_label = let last_label = label in
     label <- label + 1; Printf.sprintf "L%d" last_label
 end

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

let rec compile stmt = 
  let rec compile' labelManager =
    let rec expr = function
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
    in
    function
    | Stmt.Seq (s1, s2)  -> compile' labelManager s1 @ compile' labelManager s2
    | Stmt.Read x        -> [READ; ST x]
    | Stmt.Write e       -> expr e @ [WRITE]
    | Stmt.Assign (x, e) -> expr e @ [ST x]
    | Stmt.Skip -> []
    | Stmt.If (cond, thenBlock, elseBlock) -> 
      let elseLabel = labelManager#new_label in
      let endLabel  = labelManager#new_label
      in expr cond
       @ [CJMP ("z", elseLabel)] 
       @ compile' labelManager thenBlock 
       @ [JMP endLabel; LABEL elseLabel] 
       @ compile' labelManager elseBlock
       @ [LABEL endLabel]
    
    | Stmt.While (cond, block) ->
      let loopLabel = labelManager#new_label in
      let endLabel  = labelManager#new_label 
      in [LABEL loopLabel] 
       @ expr cond
       @ [CJMP ("z", endLabel)]
       @ compile' labelManager block
       @ [JMP loopLabel; LABEL endLabel]
    
    | Stmt.Repeat (cond, block) ->
      let loopLabel = labelManager#new_label
      in [LABEL loopLabel]
       @ compile' labelManager block
       @ expr cond
       @ [CJMP ("z", loopLabel)]
  in compile' (new labelManager) stmt