(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let default x opt = match opt with
  | Some v -> v
  | None -> x

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
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

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
      | _ -> failwith (Printf.sprintf "Unknown binary operator %s" op) 

    let not expr = Binop ("==", expr, Const 0)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)

    let rec eval env ((state, input, output, return_value) as conf) expr = 
      match expr with
        | Const n -> n, conf
        | Var x -> State.eval state x, conf
        | Binop (op, x, y) -> 
          let left, conf = eval env conf x in
          let right, conf = eval env conf y
          in to_func op left right, conf
        | Call (func, args) -> 
          let helper (conf, list) expr = (
            let value, conf = eval env conf expr
            in conf, list @ [value]
          ) in
          let conf, actual_args = List.fold_left helper (conf, []) args in
          let ((_, _, _, return_value) as conf) = env#definition env func actual_args conf
          in (match return_value with
            | Some x -> x
            | None -> failwith "Call void function"
          ), conf
         
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
        
        call: 
         fn:IDENT "(" args:(!(Util.list0By) [ostap (",")] [parse]) ")" { Call (fn, args) };
         
        primary:
          n:DECIMAL {Const n}
        | fn:IDENT "(" args:(!(Util.list0By) [ostap (",")] [parse]) ")" { Call (fn, args) }
        | x:IDENT   {Var x}
        | -"(" parse -")"
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
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of Expr.t * t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    (* let rec eval env ((st, i, o, r) as conf) k stmt = failwith "Not implemented" *)

    let rec eval env ((state, input, output, return_value) as config) k stmt = 
      let (<*>) s1 s2 = match s1, s2 with
          | Skip, s2 -> s2
          | s1, Skip -> s1
          | s1, s2  -> Seq (s1, s2)
      in match stmt with
        | Read variable ->
          let value :: input' = input in
          let state' = State.update variable value state 
          in eval env (state', input', output, None) Skip k
        
        | Write expr -> 
          let value, (state, input, output, _) = Expr.eval env config expr in
          let output' = output @ [value]
          in eval env (state, input, output', None) Skip k
        
        | Assign (variable, expr) -> 
          let value, (state, input, output, _) = Expr.eval env config expr in
          let state' = State.update variable (value) state 
          in eval env (state', input, output, None) Skip k
        
        | Seq (stmt1, stmt2) -> eval env config (stmt2 <*> k) stmt1
        
        | Skip -> if k = Skip
          then (state, input, output, None)
          else eval env config Skip k
        
        | If (cond, then_block, else_block) -> 
          let value, config = Expr.eval env config cond 
          in if (value <> 0)
              then eval env config k then_block
              else eval env config k else_block
        
        | While (cond, block) ->
          let value, config = Expr.eval env config cond 
          in if (value <> 0)
              then eval env config (stmt <*> k) block
              else eval env config Skip k
        
        | Repeat (cond, block) ->
          eval env config (While (Expr.not cond, block) <*> k) block
        
        | Return return_expr -> begin match return_expr with
          | Some expr -> 
            let value, (state, input, output, _) = Expr.eval env config expr
            in (state, input, output, Some value)
          | None -> (state, input, output, None)
          end

        | Call (func, args) -> 
          let helper (config, list) expr = (
            let value, config = Expr.eval env config expr
            in config, list @ [value]
          ) in
          let config, actual_args = List.fold_left helper (config, []) args in
          let config' = env#definition env func actual_args config
          in eval env config' Skip k

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

      return_stmt: -"return" expr:!(Expr.parse)? { Return expr };

      statement: read | write | assign | skip | if_op | for_loop | while_loop | repeat_loop | func_call | return_stmt;

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
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (* let st'', i', o', r' = Stmt.eval env (st', i, o, r) s in *)
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
