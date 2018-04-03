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
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t  with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((st, i, o) as conf) stmt =
      match stmt with
      | Read    x       -> 
              (match i with z::i' -> (Expr.update x z st, i', o) | _ -> failwith "Unexpected end of input")
      | Write e         -> (st, i, o @ [Expr.eval st e])
      | Assign (x, e)   -> (Expr.update x (Expr.eval st e) st, i, o)
      | Seq (s1, s2)    -> eval (eval conf s1) s2
      | Skip            -> conf
      | If (e, s1, s2)  -> if Expr.eval st e != 0 
                           then eval conf s1
                           else eval conf s2
      | While (e, s)    -> if Expr.eval st e != 0
                           then eval (eval conf s) stmt
                           else conf
      | Repeat (s, e)   -> 
              let ((st, i, o) as conf) = eval conf s in
              if Expr.eval st e != 0
              then conf
              else eval conf stmt
                               
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
        | %"skip" {Skip}
        | %"if" e:!(Expr.parse)
          %"then" s1:parse
            elifs:(%"elif" !(Expr.parse) %"then" parse)*
            elseb:(%"else" parse)?
          %"fi" {If (e, s1, List.fold_right (fun (e, s1) s2 -> 
              If (e, s1, s2)) elifs (match elseb with Some x -> x | None -> Skip))}
        | %"while" e:!(Expr.parse) 
            %"do" 
                s:parse 
            %"od" {While (e, s)}
        | %"repeat" 
            s:parse 
            %"until" e:!(Expr.parse) {Repeat (s, e)}
        | %"for" i:parse -"," cond:!(Expr.parse) -"," upd:parse %"do"
            s:parse
            %"od" {Seq (i, While(cond, Seq(s, upd)))}
               
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

(* Top-level parser *)
let parse = Stmt.parse                                                     
