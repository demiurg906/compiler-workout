(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open Ostap

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    let intToBool i = if (i == 0) then false else true
    let boolToInt b = if b then 1 else 0
    
    let evalBinop op left right = match op with
        | "!!" -> boolToInt(intToBool(left) || intToBool(right))
        | "&&" -> boolToInt(intToBool(left) && intToBool(right))
        | "==" -> boolToInt(left == right)
        | "!=" -> boolToInt(left <> right)
        | "<=" -> boolToInt(left <= right)
        | ">=" -> boolToInt(left >= right)
        | "<"  -> boolToInt(left < right)
        | ">"  -> boolToInt(left > right)
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
    let rec eval state expr = 
      match expr with
      | Const value -> value
      | Var variable -> state variable
      | Binop (op, left_expr, right_expr) -> 
        let left = eval state left_expr
        and right = eval state right_expr 
        in evalBinop op left right

    let binop op left right = Binop (op, left, right)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
      expr:
        !(Util.expr
        (fun x -> x)
        [|
          `Lefta, [ostap ("!!"), binop "!!"];
          `Lefta, [ostap ("&&"), binop "&&"];
          `Nona,  [ostap ("<="), binop "<="; ostap ("<"),  binop "<"; ostap (">="),  binop ">="; ostap (">"),  binop ">"];
          `Nona,  [ostap ("=="), binop "=="; ostap ("!="), binop "!="];
          `Lefta, [ostap ("-"),  binop "-"; ostap ("+"),  binop "+" ];
          `Lefta, [ostap ("*"),  binop "*"; ostap ("/"),  binop "/"; ostap ("%"),  binop "%" ];
        |]
        main
        );

      main: id:IDENT { Var id } | value:DECIMAL { Const value } | -"(" expr -")"
    )

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((state, input, output) as config) stmt = 
      match stmt with
        | Read variable -> begin match input with
          | value :: input' -> 
            let state' = Expr.update variable value state 
            in (state', input', output)
          | [] -> failwith("Empty input")
          end
        | Write expr -> 
          let output' = output @ [Expr.eval state expr]
          in (state, input, output')
        | Assign (variable, expr) -> 
          let state' = Expr.update variable (Expr.eval state expr) state 
          in (state', input, output)
        | Seq (stmt1, stmt2) -> eval (eval config stmt1) stmt2

    (* Statement parser *)
    ostap (
      read: -"read" -"(" id:IDENT -")" { Read id};
      write: -"write" -"(" e:!(Expr.expr) -")" { Write e };
      assign: id:IDENT -":=" expr:!(Expr.expr) { Assign (id, expr)};
      statement: read | write | assign;
      parse: <st::sts> :
        !(Util.listBy)
        [ostap (-";")]
        [statement]
        { List.fold_left (fun st1 st2 -> Seq (st1, st2) ) st sts}
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
