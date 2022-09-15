﻿(*
* TinyML
* Eval.fs: evaluator
*)


//Grosso da fare rimane type inference
module TinyML.Eval

open Ast

//Lexer have to recognize only positive integers, not negative one
let rec eval_expr (env : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Var x ->
        let _, v = List.find (fun (y, _) -> x = y) env
        v


//How do we evaluate a lambda? We produce a closure
    | Lambda (x, _, e) -> Closure (env, x, e)


//How to evaluate application. We evaluate the left, evaluate the right, if v1 is a closure we subsitute that with a triple (beta reducing the lambda)
    | App (e1, e2) ->
        let v1 = eval_expr env e1
        let v2 = eval_expr env e2
        match v1 with
        | Closure (env1, x, e) -> eval_expr ((x, v2) :: env1) e //v2 = lambda parameter added with env1 I evaluate e
        | RecClosure (env1, f, x, e) -> eval_expr ((x, v2) :: (f, v1) :: env1) e //recClosure, additional identifier, environment extend with f bound to v1(recClosure itself)
        | _ -> unexpected_error "eval_expr: non-closure in left side of application: %s" (pretty_value v1)
        

    //e1 is a guard
     //Case without the else
    | IfThenElse (e1, e2, None) ->
        let v1 = eval_expr env e1
        match v1 with
        | VLit (LBool true) -> eval_expr env e2
        | VLit (LBool false) -> VLit LUnit
        | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
        
       //Case with the else
    | IfThenElse (e1, e2, Some e3) ->
        let v1 = eval_expr env e1
        eval_expr env (match v1 with
                       | VLit (LBool true) -> e2
                       | VLit (LBool false) -> e3
                       | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
                       )

    //I evaluate e2 in the context of e1
    | Let (x, _, e1, e2) -> 
        let v1 = eval_expr env e1
        eval_expr ((x, v1) :: env) e2

    // TODO: test this is ok or fix it, don't know where to start, from tests, test a rec func and see
    | LetRec (f, _, e1, e2) -> 
        let v1 = eval_expr env e1
        match v1 with
        | Closure (venv1, x, e) -> RecClosure (venv1, f, x, e)
        | _ -> unexpected_error "eval_expr: expected closure in rec binding but got: %s" (pretty_value v1)
        // TODO finish this implementation


//we us binop op to don't write two times the same code
    | BinOp (e1, "+", e2) -> binop (+) (+) env e1 e2
    | BinOp (e1, "-", e2) -> binop (-) (-) env e1 e2
    | BinOp (e1, "*", e2) -> binop ( * ) ( * ) env e1 e2
    | BinOp (e1, "/", e2) -> binop ( / ) ( / ) env e1 e2
    | BinOp (e1, "%", e2) -> binop ( % ) ( % ) env e1 e2
    | BinOp (e1, "<", e2) -> relop ( < ) ( < ) env e1 e2
    | BinOp (e1, "=", e2) -> relop ( = ) ( = ) env e1 e2
    | BinOp (e1, "<=", e2) -> relop ( <= ) ( <= ) env e1 e2
    | BinOp (e1, ">", e2) -> relop ( > ) ( > ) env e1 e2
    | BinOp (e1, ">=", e2) -> relop ( >= ) ( >= ) env e1 e2
    | BinOp (e1, "<>", e2) -> relop ( <> ) ( <> ) env e1 e2
    | BinOp (e1, "or", e2) -> boolop (||) env e1 e2
    | BinOp (e1, "and", e2) -> boolop (&&) env e1 e2
    | UnOp ("not", e1) -> unop env e1
    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

    //I have only one parameter
and unop env e1 =
    let v1 = eval_expr env e1
    match v1 with
    | VLit (LBool x) -> VLit (LBool (not x))
    | _ -> unexpected_error "eval_expr: illegal operands in not operator: %s" (pretty_value v1)


    //Binary operation (int or float)
and binop op_int op_float env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LInt x), VLit (LInt y) -> VLit (LInt (op_int x y))
    | VLit (LFloat x), VLit (LFloat y) -> VLit (LFloat (op_float x y))
    | VLit (LInt x), VLit (LFloat y) -> VLit (LFloat (op_float (float x) y))
    | VLit (LFloat x), VLit (LInt y) -> VLit (LFloat (op_float x (float y)))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s (+) %s" (pretty_value v1) (pretty_value v2)
   
   //Relational operation, I return a boolean
and relop op_int op_float env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LInt x), VLit (LInt y) -> VLit (LBool (op_int x y))
    | VLit (LFloat x), VLit (LFloat y) -> VLit (LBool (op_float x y))
    | VLit (LInt x), VLit (LFloat y) -> VLit (LBool (op_float (float x) y))
    | VLit (LFloat x), VLit (LInt y) -> VLit (LBool (op_float x (float y)))
    | _ -> unexpected_error "eval_expr: illegal operands in logical operator: %s (<) %s" (pretty_value v1) (pretty_value v2)


    //&& and ||
and boolop op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LBool x) , VLit (LBool y) -> VLit (LBool (op x y))
    | _ -> unexpected_error "eval_expr: illegal operands in logical operator: %s (and) %s" (pretty_value v1) (pretty_value v2)

    //Some converters 
let value_to_int = function (VLit (LInt l)) -> l | c -> unexpected_error "NativeClosure: wrong value, expected VLit but got %s" (pretty_value c)
let value_to_float = function (VLit (LFloat l)) -> l | c -> unexpected_error "NativeClosure: wrong value, expected VLit but got %s" (pretty_value c)
let value_to_bool = function (VLit (LBool l)) -> l | c -> unexpected_error "NativeClosure: wrong value, expected VLit but got %s" (pretty_value c)


//Native closure is a env*string*(value->value)->value, basically given and environment and a string it takes two parameters and apply an operation to them,
//Having a predefined environment like this help me to then apply the rule evaluation for these operations
let delta0 = [
    ("+", NativeClosure(["+", VLit LUnit], "x", fun x -> NativeClosure([], "y", fun y -> VLit (LInt ((+) (value_to_int x) (value_to_int y))))))
    ("-", NativeClosure(["-", VLit LUnit], "x", fun x -> NativeClosure([], "y", fun y -> VLit (LInt ((-) (value_to_int x) (value_to_int y))))))
    ("u-", NativeClosure(["u-", VLit LUnit], "x", fun x -> VLit (LInt (-(value_to_int x)))))
    ("*", NativeClosure(["*", VLit LUnit], "x", fun x -> NativeClosure([], "y", fun y -> VLit (LInt ((*) (value_to_int x) (value_to_int y))))))
    ("/", NativeClosure(["/", VLit LUnit], "x", fun x -> NativeClosure([], "y", fun y -> VLit (LInt ((/) (value_to_int x) (value_to_int y))))))
    ("%", NativeClosure(["%", VLit LUnit], "x", fun x -> NativeClosure([], "y", fun y -> VLit (LInt ((%) (value_to_int x) (value_to_int y))))))
    ("+.", NativeClosure(["+.", VLit LUnit], "x", fun x -> NativeClosure([], "y", fun y -> VLit (LFloat ((+) (value_to_float x) (value_to_float y))))))
    ("-.", NativeClosure(["-.", VLit LUnit], "x", fun x -> NativeClosure([], "y", fun y -> VLit (LFloat ((-) (value_to_float x) (value_to_float y))))))
    ("u-.", NativeClosure(["u-.", VLit LUnit], "x", fun x -> VLit (LFloat (-(value_to_float x)))))
    ("*.", NativeClosure(["*.", VLit LUnit], "x", fun x -> NativeClosure([], "y", fun y -> VLit (LFloat ((*) (value_to_float x) (value_to_float y))))))
    ("/.", NativeClosure(["/.", VLit LUnit], "x", fun x -> NativeClosure([], "y", fun y -> VLit (LFloat ((/) (value_to_float x) (value_to_float y))))))
    ("%.", NativeClosure(["%.", VLit LUnit], "x", fun x -> NativeClosure([], "y", fun y -> VLit (LFloat ((%) (value_to_float x) (value_to_float y))))))
    ("and", NativeClosure(["and", VLit LUnit], "x", fun x -> NativeClosure([], "y", fun y -> VLit (LBool ((&&) (value_to_bool x) (value_to_bool y))))))
    ("or", NativeClosure(["or", VLit LUnit], "x", fun x -> NativeClosure([], "y", fun y -> VLit (LBool ((||) (value_to_bool x) (value_to_bool y))))))
    ("not", NativeClosure(["not", VLit LUnit], "x", fun x -> VLit (LBool ((not) (value_to_bool x)))))
]