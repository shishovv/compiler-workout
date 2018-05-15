open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg =
    match prg with
    | [] -> conf
    | instr::instrs ->
            match instr with
            | BINOP op -> (
                    match stack with
                    | r::l::s -> eval env (cstack, (Value.of_int (Expr.evalBinOp op (Value.to_int l) (Value.to_int r)))::s, c) instrs
                    | _ -> failwith "binop failed : not enough args"
            )
            | CONST const -> eval env (cstack, (Value.of_int const)::stack, c) instrs
            | STRING s -> eval env (cstack, (Value.of_string s)::stack, c) instrs
            | LD var -> eval env (cstack, (State.eval st var)::stack, c) instrs
            | ST var -> (
                    match stack with
                    | x::xs -> eval env (cstack, xs, (State.update var x st, i, o)) instrs
                    | _ -> failwith ("st failed : not enough args " ^ var
            ))
            | STA (var, n) -> 
                    let v::is, stack' = split (n + 1) stack in
                    eval env (cstack, stack', (Stmt.update st var v (List.rev is), i, o)) instrs
            | LABEL _ -> eval env conf instrs
            | JMP l -> eval env conf (env#labeled l)
            | CJMP (flag, l) ->
                    let (x::xs) = stack in
                    let cond = match flag with
                    | "z"  -> Value.to_int x == 0
                    | "nz" -> Value.to_int x != 0 in
                    eval env (cstack, xs, c) (if (cond)
                                                    then env#labeled l
                                                    else instrs)
            | CALL (f, n, p) ->
                    if env#is_label f 
                    then eval env ((instrs, st)::cstack, stack, c) (env#labeled f)
                    else eval env (env#builtin conf f n p) instrs
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
                            eval env (xs, stack, (State.leave st s, i, o)) ins
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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let env = object
    val mutable cnt = 0
    method next = 
        cnt <- cnt + 1;
        "l_" ^ string_of_int cnt
end

let compile (defs, p) =
    let rec stmt =
        let rec expr = function
        | Expr.Var   x          -> [LD x]
        | Expr.Const n          -> [CONST n]
        | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
        | Expr.Call (f, args)   -> List.concat (List.map expr (List.rev args)) @ [CALL ("L" ^ f, List.length args, false)] 
        | Expr.String s         -> [STRING s]
        | Expr.Array a          -> List.concat (List.map expr a) @ [CALL ("$array", List.length a, false)]
        | Expr.Elem (a, i)      -> expr a @ expr i @ [CALL ("$elem", 2, false)]
        | Expr.Length a         -> expr a @ [CALL ("$length", 1, false)] in
        function
        | Stmt.Seq (s1, s2) -> stmt s1 @ stmt s2
        | Stmt.Assign (x, [], e) -> expr e @ [ST x]
        | Stmt.Assign (x, is, e) -> List.concat (List.map expr is) @ expr e @ [STA (x, List.length is)]
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
        | Stmt.While (e, s) ->
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
            List.concat (List.map expr args) @ [CALL ("L" ^ f, List.length args, true)] in
    let def (f, (args, locals, body)) = [LABEL ("L" ^ f); BEGIN ("L" ^ f, args, locals)] @ stmt body @ [END] in
    stmt p @ [END] @ List.concat (List.map def defs)
