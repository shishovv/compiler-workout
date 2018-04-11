(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty = 
        let uv x = failwith ("undefined variable " ^ x) in
        {g = uv; l = uv; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s = 
        if List.mem x s.scope
        then {s with l = fun y -> if x = y then v else s.l y}
        else {s with g = fun y -> if x = y then v else s.g y}
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = 
        if List.mem x s.scope
        then s.l x
        else s.g x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {g = st.g; l = empty.l; scope = xs}

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
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
    | Var x -> State.eval st x
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env ((st, i, o) as conf) stmt =
		match stmt with
		| Read    x       -> 
			(match i with z::i' -> (State.update x z st, i', o) | _ -> failwith "Unexpected end of input")
		| Write e         -> (st, i, o @ [Expr.eval st e])
		| Assign (x, e)   -> (State.update x (Expr.eval st e) st, i, o)
		| Seq (s1, s2)    -> eval env (eval env conf s1) s2
		| Skip            -> conf
		| If (e, s1, s2)  -> 
				if Expr.eval st e != 0 
				then eval env conf s1
				else eval env conf s2
		| While (e, s)    -> 
				if Expr.eval st e != 0
				then eval env (eval env conf s) stmt
				else conf
		| Repeat (s, e)   -> 
				let ((st, i, o) as conf) = eval env conf s in
				if Expr.eval st e != 0
				then conf
				else eval env conf stmt
		| Call (f, args)  ->
				let (args', vars, body) = env#definition f in
				let evargs = List.map (Expr.eval st) args in
				let enter = State.enter st (args' @ vars) in
				let stf = List.fold_left2 (fun s p v -> State.update p v s) enter args' evargs in
				let (st', i', o') = eval env (stf, i, o) body in
				State.leave st' st, i', o'
                                
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
		| f:IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (f, args)}
            
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
		parse: %"fun" f:IDENT -"(" args:IDENT* -")" locals:(%"local" IDENT*)? -"{" body:!(Stmt.parse) -"}" 
		{(f, (args, (match locals with None -> [] | Some locals -> locals), body)) }
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
    let defm = List.fold_left (fun m (fname, fdef) -> M.add fname fdef m) M.empty defs in
    let env = object method definition f = M.find f defm end in
    let _, _, o = Stmt.eval env (State.empty, i, []) body in
    o
                                   
(* Top-level parser *)
let parse = ostap (
    defs:!(Definition.parse) * body:!(Stmt.parse) {defs, body}
)
