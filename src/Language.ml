(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = Utils.list_init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
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
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval env ((st, i, o, r) as conf) expr =
        match expr with
        | Const c -> st, i, o, Some (Value.of_int c)
        | Var x -> st, i, o, Some (State.eval st x)
        | Binop (op, lop, rop) ->
                let (_, _, _, Some l)  = eval env conf lop in
                let (st, i, o, Some r) = eval env conf rop in
                st, i, o, Some (Value.of_int (to_func op (Value.to_int l) (Value.to_int r)))
        | Call (f, args) ->
                let (st, i, o, args') as conf' = eval_list env conf args in
                env#definition env f args' (st, i, o, None)
        | Array a ->
                let (st, i, o, a') = eval_list env conf a in
                env#definition env "$array" a' (st, i, o, None)
        | String s -> st, i, o, Some (Value.of_string s)
        | Elem (e, ei) ->
                let (st, i, o, a) = eval_list env conf [e; ei] in
                env#definition env "$elem" a (st, i, o, None)
        | Length e ->
                let (st, i, o, Some v) = eval env conf e in
                env#definition env "$length" [v] (st, i, o, None)
        | Sexp (s, xs) ->
                let (st, i, o, a) = eval_list env conf xs in
                (st, i, o, Some (Value.sexp s a))
        | _ -> failwith "not implemented yet"
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
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
                 `Lefta , buildOstapBinOpLst ["+"; "-"]; `Lefta , buildOstapBinOpLst ["*"; "/"; "%"];
               |]
               primary
            );
        primary: b:base is:(-"[" i:parse -"]" {`Elem i} | "." %"length" {`Len})*
        {List.fold_left (fun x -> function `Elem i -> Elem(x, i) | `Len -> Length x) b is};

        base:
          x:IDENT e:("(" args:!(Util.list0)[parse] ")" {Call (x, args)} | empty {Var x}) {e}
        | n:DECIMAL {Const n}
        | c:CHAR {Const (Char.code c)}
        | "[" es:!(Util.list0)[parse] "]" {Array es}
        | s:STRING {String (String.sub s 1 (String.length s - 2))}
        | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse:
            %"_" {Wildcard}
          | "`" x:IDENT "(" s:!(Util.list parse) ")" {Sexp (x, s)}
          | "`" x:IDENT {Sexp (x, [])}
          | x:IDENT {Ident x}
        )
        
        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env ((st, i, o, r) as conf) k stmt =
        let m s1 s2 = match s2 with Skip -> s1 | _ -> Seq(s1, s2) in
        match stmt with
		| Assign (x, is, e) -> (
                let (st, i, o, Some v) = Expr.eval env conf e in
                let (st, i, o, is) = Expr.eval_list env (st, i, o, None) is in
                eval env (update st x v is, i, o, None) Skip k
        )
		| Seq (s1, s2) -> eval env conf (m s2 k) s1
        | Skip -> (
            match k with Skip -> conf | _ -> eval env conf Skip k
        )
		| If (e, s1, s2) -> (
                let (st', i', o', Some v) = Expr.eval env conf e in
                eval env (st', i', o', r) k (if Value.to_int v != 0 then s1 else s2)
        )
		| While (e, s) -> (
                let (st', i', o', Some v) = Expr.eval env conf e in
                let conf' = (st', i', o', r) in
                if Value.to_int v != 0
                then eval env conf' (m stmt k) s
                else eval env conf' Skip k
        )
        | Repeat (s, e) -> eval env conf (m (While (Expr.Binop ("==", e, Expr.Const 0), s)) k) s
		| Call (f, args) -> (
                eval env (Expr.eval env conf (Expr.Call (f, args))) k Skip
        )
        | Case (e, bs) ->
                let (_, _, _, Some v) as conf' = Expr.eval env conf e in
                let rec branch ((st, i, o, _) as conf) = function
                | [] -> failwith "pattern matching failed"
                | (patt, body)::tl ->
                    let rec match_patt pattern v st =
                        let update x v = function
                        | Some s -> Some (State.bind x v s)
                        | None -> None in
                        match patt, v with
                        | Pattern.Ident x, v -> update x v st
                        | Pattern.Wildcard , _ -> st
                        | Pattern.Sexp (t, ps), Value.Sexp (t', vs) when t = t' -> match_list ps vs st
                        | _ -> None
                    and match_list ps vs s = match ps, vs with
                    | [], []       -> s
                    | p::ps, v::vs -> match_list ps vs (match_patt p v s)
                    | _            -> None in
                    match match_patt patt v (Some State.undefined) with
                    | None     -> branch conf tl
                    | Some st' -> eval env (State.push st st' (Pattern.vars patt), i, o, None) k (Seq (body, Leave)) in
                branch conf' bs
        | Return r -> (
                match r with
                | Some e -> Expr.eval env conf e
                | _      -> st, i, o, None
        )
        | Leave -> eval env (State.drop st, i, o, None) Skip k
                                                        
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
          x:IDENT is:(-"[" !(Expr.parse) -"]")* ":=" e:!(Expr.parse) {Assign (x, is, e)}
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
        | %"return" e:!(Expr.parse)? {Return e}
        | %"case" e:!(Expr.parse)
            %"of" bs:!(Util.listBy)[ostap ("|")][ostap (!(Pattern.parse) -"->" parse)]
            %"esac" {Case (e, bs)}
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
