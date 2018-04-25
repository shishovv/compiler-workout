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
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg = 
    match prg with
    | [] -> conf
    | instr::instrs ->
            match instr with
            | BINOP op -> (
                    match stack with
                    | r::l::s -> eval env (cstack, (Expr.evalBinOp op l r)::s, c) instrs
                    | _ -> failwith "binop failed : not enough args"
            )
            | CONST const -> eval env (cstack, const::stack, c) instrs
            | READ -> (
                    match i with
                    | x::xs -> eval env (cstack, x::stack, (st, xs, o)) instrs
                    | _ -> failwith "read failed : invalid input"
            )
            | WRITE -> (
                    match stack with
                    | x::xs -> eval env (cstack, xs, (st, i, o@[x])) instrs
                    | _ -> failwith "write failed : not enough args"
            )
            | LD var -> eval env (cstack, (State.eval st var)::stack, c) instrs
            | ST var -> (
                    match stack with
                    | x::xs -> eval env (cstack, xs, (State.update var x st, i, o)) instrs
                    | _ -> failwith "st failed : not enough args"
            )
            | LABEL _ -> eval env conf instrs
            | JMP l -> eval env conf (env#labeled l)
            | CJMP (flag, l) ->
                    let (x::xs) = stack in
                    let cond = match flag with
                    | "z"  -> x == 0
                    | "nz" -> x != 0 in
                    eval env (cstack, xs, c) (if (cond)
                                                    then env#labeled l
                                                    else instrs)
            | CALL (f, _, _) ->
                    eval env ((instrs, st) :: cstack, stack, c) (env#labeled f)
            | BEGIN (_, args, locals) ->
                    let rec eargs s = function
                        | arg::args, v::stack ->
                                let s', stack' = eargs s (args, stack) in
                                State.update arg v s', stack'
                        | [], stack -> s, stack in
                    let st', stack' = eargs (State.enter st (args @ locals)) (args, stack) in
                    eval env (cstack, stack', (st', i, o)) instrs
            | END | RET _ ->
                    match cstack with
                    | (ins, s)::xs ->
                            eval env (xs, stack, (State.leave s st, i, o)) ins
                    | [] -> conf

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

let env = object
    val mutable cnt = 0
    method next = 
        cnt <- cnt + 1;
        "l_" ^ string_of_int cnt
end

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = 
    let rec stmt =
        let rec expr = function
        | Expr.Var   x          -> [LD x]
        | Expr.Const n          -> [CONST n]
        | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
        | Expr.Call (f, args)   -> List.concat (List.map expr args) @ [CALL (f, List.length args, true)] in
        function
        | Stmt.Seq (s1, s2)   -> stmt s1 @ stmt s2
        | Stmt.Read x         -> [READ; ST x]
        | Stmt.Write e        -> expr e @ [WRITE]
        | Stmt.Assign (x, e)  -> expr e @ [ST x]
        | Stmt.Skip           -> []
        | Stmt.If (e, s1, s2) ->
                let els = env#next in
                let fi  = env#next in
                expr e @
                [CJMP ("z", els)] @
                stmt s1 @
                [JMP fi; LABEL els] @
                stmt s2 @
                [LABEL fi]
        | Stmt.While (e, s)   ->
                let bdyl = env#next in
                let endl = env#next in
                [LABEL bdyl] @
                expr e @
                [CJMP ("z", endl)] @
                stmt s @
                [JMP bdyl; LABEL endl]
        | Stmt.Repeat (s, e) ->
                let bdyl = env#next in
                [LABEL bdyl] @
                stmt s @
                expr e @
                [CJMP ("z", bdyl)]
        | Stmt.Return r -> (
                match r with
                | Some e -> (expr e) @ [RET true]
                | _ -> [RET false]
        )
        | Stmt.Call (f, args) ->
            List.concat (List.map expr args) @ [CALL (f, List.length args, false)] in
    let def (f, (args, locals, body)) = [LABEL f; BEGIN (f, args, locals)] @ stmt body @ [END] in
    stmt p @ [END] @ List.concat (List.map def defs)
