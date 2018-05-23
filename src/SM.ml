open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
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
                    | r::l::s -> eval env (cstack, (Value.of_int (Expr.to_func op (Value.to_int l) (Value.to_int r)))::s, c) instrs
                    | _ -> failwith "binop failed : not enough args"
            )
            | CONST const -> eval env (cstack, (Value.of_int const)::stack, c) instrs
            | STRING s -> eval env (cstack, (Value.of_string s)::stack, c) instrs
            | SEXP (tag, len) -> (
                let vs, stack' = split len stack in
                eval env (cstack, (Value.sexp tag (List.rev vs)) :: stack', c) instrs
            )
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
            | DROP -> eval env (cstack, List.tl stack, c) instrs
            | DUP -> eval env (cstack, List.hd stack :: stack, c) instrs
            | SWAP -> let a::b::xs = stack in eval env (cstack, b::a::xs, c) instrs
            | TAG s ->
                let x::xs = stack in
                let v = if s = Value.tag_of x then 1 else 0 in
                eval env (cstack, Value.of_int v::xs, c) instrs
            | ENTER xs ->
                let vs, stack' = split (List.length xs) stack in
                let s = List.fold_left2 (fun s x v -> State.bind x v s) State.undefined xs vs in
                eval env (cstack, stack', (State.push st s xs, i, o)) instrs
            | LEAVE -> eval env (cstack, stack, (State.drop st, i, o)) instrs
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
  (* print_prg p; *)
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
let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (label f, List.length args, p)]
  and pattern lfalse = function
    | Stmt.Pattern.Wildcard     -> false, [DROP]
    | Stmt.Pattern.Ident _      -> false, [DROP]
    | Stmt.Pattern.Sexp (t, ps) -> true, [DUP; TAG t; CJMP ("z", lfalse)] 
                                         @ (List.concat 
                                            (List.mapi (fun i p -> [DUP; CONST i; CALL (".elem", 2, false)] @ snd @@ pattern lfalse p) ps))
  and bindings p =
    let rec inner = function
    | Stmt.Pattern.Ident n      -> [SWAP]
    | Stmt.Pattern.Sexp (_, ps) -> (List.flatten (List.mapi (fun i p -> [DUP; CONST i; CALL (".elem", 2, false)] @ inner p) ps)) @ [DROP]
    | Stmt.Pattern.Wildcard     -> [DROP] in
    inner p @ [ENTER (Stmt.Pattern.vars p)]
  and expr = function
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
    | Expr.Call (f, args)   -> List.concat (List.map expr (List.rev args)) @ [CALL ("L" ^ f, List.length args, false)]
    | Expr.String s         -> [STRING s]
    | Expr.Array a          -> List.concat (List.map expr a) @ [CALL ("$array", List.length a, false)]
    | Expr.Elem (a, i)      -> expr a @ expr i @ [CALL ("$elem", 2, false)]
    | Expr.Length a         -> expr a @ [CALL ("$length", 1, false)]
    | Expr.Sexp (t, xs)     -> List.flatten (List.map expr xs) @ [SEXP (t, List.length xs)] in
  let rec compile_stmt l env = function
        | Stmt.Seq (s1, s2) ->
            let l2, env = env#get_label in
            let env, f1, s1 = compile_stmt l2 env s1 in
            let env, f2, s2 = compile_stmt l env s2 in
            env, f2, s1 @ (if f1 then [LABEL l2] else []) @ s2
        | Stmt.Assign (x, [], e) -> env, false, expr e @ [ST x]
        | Stmt.Assign (x, is, e) -> env, false, List.concat (List.map expr is) @ expr e @ [STA (x, List.length is)]
        | Stmt.Skip -> env, false, []
        | Stmt.If (e, s1, s2) ->
                let l2, env = env#get_label in
                let env, f1, s1 = compile_stmt l env s1 in
                let env, f2, s2 = compile_stmt l env s2 in
                env, f2, 
                expr e @
                [CJMP ("z", l2)] @
                s1 @
                (if f1 then [] else [JMP l]) @
                [LABEL l2] @
                s2 @
                (if f2 then [] else [JMP l])
        | Stmt.While (e, s) ->
                let condl, env = env#get_label in
                let loopl, env = env#get_label in
                let env, f, s = compile_stmt condl env s in
                env, false, 
                [JMP condl; LABEL loopl] @
                s @
                [LABEL condl] @
                expr e @
                [CJMP ("nz", loopl)]
        | Stmt.Repeat (s, e) ->
                let loop, env = env#get_label in
                let env, f, s = compile_stmt loop env s in
                env, false,
                [LABEL loop] @ 
                s @ 
                expr e @ 
                [CJMP ("z", loop)]
        | Stmt.Return r ->
                env, false, (match r with Some e -> (expr e) @ [RET true] | _ -> [RET false])
        | Stmt.Call (f, args) ->
                env, false, call f args true
        | Stmt.Case (e, bs) ->
            let n = List.length bs - 1 in
            let env, _, _, c =
                List.fold_left
                    (fun (env, lab, i, c) (p, s) ->
                        let (lfalse, env), jmp = if i = n then (l, env), [] else env#get_label, [JMP l] in
                        let _, pc = pattern lfalse p in
                        let env, _, sc = compile_stmt l env (Stmt.Seq (s, Stmt.Leave)) in
                        (env, Some lfalse, i + 1, ((match lab with None -> [] | Some l -> [LABEL l]) @ pc @ bindings p @ sc @ jmp) :: c))
                        (env, None, 0, []) bs in
            env, true, expr e @ List.concat @@ List.rev c in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code) 

