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

let rec eval cfg prg =
    match prg with
    | [] -> cfg
    | instr::instrs ->
            let (stack, stmtCfg) = cfg in
            let (st, input, output) = stmtCfg in
            match instr with
            | BINOP op -> (
                    match stack with
                    | r::l::s -> eval ((Language.Expr.evalBinOp op l r)::s,stmtCfg) instrs
                    | _ -> failwith "binop failed : not enough args"
            )
            | CONST c -> eval (c::stack, stmtCfg) instrs
            | READ -> (
                    match input with
                    | x::xs -> eval (x::stack, (st, xs, output)) instrs
                    | _ -> failwith "read failed : invalid input"
            )
            | WRITE -> (
                    match stack with
                    | x::xs -> eval (xs, (st, input, output@[x])) instrs
                    | _ -> failwith "write failed : not enough args"
            )
            | LD var -> eval ((st var)::stack, stmtCfg) instrs
            | ST var -> (
                    match stack with
                    | x::xs -> eval (xs, (Language.Expr.update var x st, input, output)) instrs
                    | _ -> failwith "st failed : not enough args"
            )

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

let rec compileExpr e =
    match e with
    | Language.Expr.Const c -> [CONST c]
    | Language.Expr.Var var -> [LD var]
    | Language.Expr.Binop (op, l, r) -> (compileExpr l)@(compileExpr r)@[BINOP op]

let rec compile expr =
    match expr with
    | Language.Stmt.Read var -> [READ; ST var]
    | Language.Stmt.Write e -> (compileExpr e)@[WRITE]
    | Language.Stmt.Assign (var, e) -> (compileExpr e)@[ST var]
    | Language.Stmt.Seq (e1, e2) -> (compile e1)@(compile e2)
