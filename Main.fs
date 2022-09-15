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
    let t,s = Typing.typeinfer_expr tenv e
    #if DEBUG
    printfn "type:\t%s subs : %O" (pretty_ty t) (s)
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
//We would like the empty envinroment [] at venv
let main_interactive () =
    printfn "entering interactive mode..."
    let mutable tenv = Typing.gamma0 //Environmet for typing
    //let mutable tenv = []
    let mutable venv = Eval.delta0 //Environment for evaluation
    //let mutable venv = []
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
                    // tenv <-q (x, t) :: tenv
                    let dummy_scheme = Forall ([], t)
                    tenv <- (x, dummy_scheme) :: tenv
                    venv <- (x, v) :: venv
                    x, (t, v)

            printfn "val %s : %s = %s" x (pretty_ty t) (pretty_value v)


[<EntryPoint>]
let main argv =
    let c = fun x -> fun y -> x+y
    let k = c 8 9
    printf("%O") k
    main_interactive ()

    
    Console.ReadLine () |> ignore
    0
