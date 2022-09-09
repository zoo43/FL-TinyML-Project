(*
* TinyML
* Main.fs: main code
*)

module TinyML.Main

open System
open FSharp.Common
open TinyML.Ast

let parse_from_TextReader rd filename parser = Parsing.parse_from_TextReader SyntaxError rd filename (1, 1) parser Lexer.tokenize Parser.tokenTagToTokenId

    //type env and value env
let interpret_expr tenv venv e =
    #if DEBUG
    printfn "AST:\t%A\npretty:\t%s" e (pretty_expr e)
    #endif
    let t = Typing.typecheck_expr tenv e
    #if DEBUG
    printfn "type:\t%s" (pretty_ty t)
    #endif
    let v = Eval.eval_expr venv e
    #if DEBUG
    printfn "value:\t%s\n" (pretty_value v)
    #endif
    t, v

let trap f =
    try f ()
    with SyntaxError (msg, lexbuf) -> printfn "\nsyntax error: %s\nat token: %A\nlocation: %O" msg lexbuf.Lexeme lexbuf.EndPos
       | TypeError msg             -> printfn "\ntype error: %s" msg
       | UnexpectedError msg       -> printfn "\nunexpected error: %s" msg

let main_interpreter filename =
    trap <| fun () ->
        printfn "loading source file '%s'..." filename
        use fstr = new IO.FileStream (filename, IO.FileMode.Open)
        use rd = new IO.StreamReader (fstr)
        let prg = parse_from_TextReader rd filename Parser.program
        let t, v = interpret_expr [] [] prg
        printfn "type:\t%s\nvalue:\t%s" (pretty_ty t) (pretty_value v)


//All have a list of environments, when you start if we pass without an empty list, but with a list we something inside. A small library of symbol
//This is a trick!
//We would like the empty envinroment [] at venv
let main_interactive () =
    printfn "entering interactive mode..."
    let mutable tenv = Typing.gamma0
    let mutable venv = []
    while true do
        trap <| fun () ->
            printf "\n> "
            stdout.Flush ()
            let x, (t, v) =
                match parse_from_TextReader stdin "LINE" Parser.interactive with
                | IExpr e ->
                    "it", interpret_expr tenv venv e

                | IBinding (_, x, _, _ as b) ->
                    let t, v = interpret_expr tenv venv (LetIn (b, Var x)) // TRICK: put the variable itself as body after the in
                    // update global environments
                    tenv <- (x, t) :: tenv
                    venv <- (x, v) :: venv
                    x, (t, v)

            printfn "val %s : %s = %s" x (pretty_ty t) (pretty_value v)

                (*
let rec map(f,l) =
    match l with
    | [] -> []
    | x :: xs ->
        match l2 with
        | [] -> x::xs
        | y :: ys -> f x y :: map(f,xs,ys)

let rec map f l =
    match l with
    | [] -> []
    | x :: xs -> f x :: map f xs*)

let prova x c =
    x+c

let rec sum list =
   match list with
   | head :: tail -> head + sum tail
   | [] -> 0

let rec fold f z l =
    match l with
    | [] -> z
    | x :: xs -> f (fold f z xs) x

[<EntryPoint>]
let main argv =
    (*let r =
        try 
            if argv.Length < 1 then main_interactive ()
            else main_interpreter argv.[0]
            0
        with e -> printfn "\nexception caught: %O" e; 1
    Console.ReadLine () |> ignore
    r*)     
    let l = [1;2;3]
    let res = List.map(fun x -> (x,0)) l 

    printf "%O" res
   // main_interpreter argv.[0]
    
    //let c = if 5>4 && 5>6 then 10 else 0 in printf "%d" c
   // let rec iter_new_form = fun f -> fun l -> match l with | [] -> () | x :: xs -> f x; iter_new_form f xs in let g = iter_new_form (fun x -> printf "%d" x) in g [1;2;3]
  //  main_interactive ()
    
    Console.ReadLine () |> ignore
    0
