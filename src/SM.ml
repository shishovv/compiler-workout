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
let rec eval env cfg prg = 
    match prg with
    | [] -> cfg
    | instr::instrs ->
            let (stack, stmtCfg) = cfg in
            let (st, input, output) = stmtCfg in
            match instr with
            | BINOP op -> (
                    match stack with
                    | r::l::s -> eval env ((Language.Expr.evalBinOp op l r)::s,stmtCfg) instrs
                    | _ -> failwith "binop failed : not enough args"
            )
            | CONST c -> eval env (c::stack, stmtCfg) instrs
            | READ -> (
                    match input with
                    | x::xs -> eval env (x::stack, (st, xs, output)) instrs
                    | _ -> failwith "read failed : invalid input"
            )
            | WRITE -> (
                    match stack with
                    | x::xs -> eval env (xs, (st, input, output@[x])) instrs
                    | _ -> failwith "write failed : not enough args"
            )
            | LD var -> eval env ((st var)::stack, stmtCfg) instrs
            | ST var -> (
                    match stack with
                    | x::xs -> eval env (xs, (Language.Expr.update var x st, input, output)) instrs
                    | _ -> failwith "st failed : not enough args"
            )
            | LABEL _ -> eval env cfg instrs
            | JMP l -> eval env cfg (env#labeled l)
            | CJMP (flag, l) -> 
                    let (x::xs) = stack in
                    let cond = match flag with
                    | "z"  -> x == 0
                    | "nz" -> x != 0 in
                    eval env (xs, stmtCfg) (if (cond) 
                                            then env#labeled l
                                            else instrs)


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

let env = object
    val mutable cnt = 0
    method next = 
        cnt <- cnt + 1;
        "l_" ^ string_of_int cnt
end

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile = 
    let rec expr = function
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op] 
    in
    function
    | Stmt.Seq (s1, s2)   -> compile s1 @ compile s2
    | Stmt.Read x         -> [READ; ST x]
    | Stmt.Write e        -> expr e @ [WRITE]
    | Stmt.Assign (x, e)  -> expr e @ [ST x]
    | Stmt.Skip           -> []
    | Stmt.If (e, s1, s2) ->
            let els = env#next in
            let fi  = env#next in
            expr e @ 
            [CJMP ("z", els)] @ 
            compile s1 @ 
            [JMP fi; LABEL els] @ 
            compile s2 @ 
            [LABEL fi]
    | Stmt.While (e, s)   ->
            let bdyl = env#next in
            let endl = env#next in
            [LABEL bdyl] @
            expr e @
            [CJMP ("z", endl)] @
            compile s @
            [JMP bdyl; LABEL endl]
    | Stmt.Repeat (s, e) ->
            let bdyl = env#next in
            [LABEL bdyl] @
            compile s @
            expr e @
            [CJMP ("z", bdyl)]


