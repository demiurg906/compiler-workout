open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval (stack, ((state, input, output) as config)) instructions = match instructions with
  | inst :: instructions ->
    let config' = begin match inst with
      | BINOP op -> 
        begin match stack with
          | right :: left :: stack' -> ((Language.Expr.evalBinop op left right) :: stack', config)
          | _ -> failwith("Empty stack 1")
        end
      | CONST x -> (x :: stack, config)
      | READ ->
        begin match input with
          | x :: input' -> (x :: stack, (state, input', output))
          | [] -> failwith("Empty input 2")
        end
      | WRITE ->
        begin match stack with
          | x :: stack' -> (stack', (state, input, output @ [x]))
          | [] -> failwith("Empty stack 3")
        end
      | LD var ->
        let value = state var
        in (value :: stack, config)
      | ST var ->
        begin match stack with
          | x :: stack' -> (stack', (Language.Expr.update var x state, input, output))
          | [] -> failwith("Empty stack 4")
        end
      end
    in eval config' instructions
  | [] -> (stack, config)

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile stmt = 
  let rec compileExpr expr = match expr with
    | Language.Expr.Const x -> [CONST x]
    | Language.Expr.Var var -> [LD var]
    | Language.Expr.Binop (op, left, right) -> compileExpr left @ compileExpr right @ [BINOP op]
  in match stmt with
    | Language.Stmt.Read var -> [READ; ST var]
    | Language.Stmt.Write expr -> compileExpr expr @ [WRITE]
    | Language.Stmt.Assign (var, expr) -> compileExpr expr @ [ST var]
    | Language.Stmt.Seq (stmt1, stmt2) -> compile stmt1 @ compile stmt2