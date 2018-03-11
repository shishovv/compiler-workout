(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t = (* integer constant *) | Const of int
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

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)

    let evalBinOp op l r = 
            let toBool i = i != 0 in
            let toInt  b = if b then 1 else 0 in
            match op with 
            | "+"  -> l + r
            | "-"  -> l - r
            | "*"  -> l * r
            | "/"  -> l / r
            | "%"  -> l mod r
            | "<"  -> toInt (l < r)
            | "<=" -> toInt (l <= r)
            | ">"  -> toInt (l > r)
            | ">=" -> toInt (l >= r)
            | "==" -> toInt (l == r)
            | "!=" -> toInt (l != r)
            | "&&" -> toInt (toBool l && toBool r)
            | "!!" -> toInt (toBool l || toBool r)
            | _    -> failwith "unknown operator"

        let rec eval st e =
        match e with
        | Const c -> c
        | Var x -> st x
        | Binop (op, lop, rop) ->
            let l = eval st lop in
            let r = eval st rop in
            evalBinOp op l r

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    let buildOstapBinOpLst ops = List.map (fun op -> (ostap ($(op)), fun x y -> Binop (op, x, y))) ops

    ostap (
        parse:
            !(Ostap.Util.expr
               (fun x -> x)
               [|
                 `Lefta , buildOstapBinOpLst ["!!"];
                 `Lefta , buildOstapBinOpLst ["&&"];
                 `Nona  , buildOstapBinOpLst [">="; ">"; "<="; "<"; "=="; "!="];
                 `Lefta , buildOstapBinOpLst ["+"; "-"];
                 `Lefta , buildOstapBinOpLst ["*"; "/"; "%"];
               |]
               primary
            );
        primary: x:IDENT {Var x} | x:DECIMAL {Const x} | -"(" parse -")"
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

    let rec eval cfg p =
    let (st, input, output) = cfg in
    match p with
    | Read var -> (
            match input with
            | x::xs -> (Expr.update var x st, xs, output)
            | _ -> failwith "read failed : incorrect input"
    )
    | Write e -> (st, input, output@[(Expr.eval st e)])
    | Assign (var, e) -> (Expr.update var (Expr.eval st e) st, input, output)
    | Seq (e1, e2) -> eval (eval cfg e1) e2

    (* Statement parser *)
    ostap (
        parse:
            !(Ostap.Util.expr
                (fun x -> x)
                [|
                    `Lefta , [ostap(";"), (fun x y -> Seq (x, y))];
                |]
                simple_stmt
            );
        simple_stmt:
          x:IDENT ":=" e:!(Expr.parse) {Assign (x, e)}
        | "read" "(" x:IDENT ")" {Read x}
        | "write" "(" e:!(Expr.parse) ")" {Write e}
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
