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

// Questo è praticamente un fold
let rec map =
    fun f -> 
        fun l ->
            fun m ->
        match l with
        | [] -> m
        | x::xs -> map f xs (f x m)

let rec filter f l =
    match l with
    | [] -> []
    | x :: xs -> if f x then x:: filter f xs else filter f xs

let check x y = if x > y then x else y


type tree = Leaf of int | Node of tree * tree * int 

let rec print_tree t =
    match t with
    | Leaf (v) -> printfn("%O") v
    | Node (t1,t2,v) ->
        print_tree t1
        print_tree t2
        printfn("%O") v

let rec print_tree_max t m =
    match t with
    | Leaf (v) -> check v m
    | Node (t1,t2,v) ->
        check (print_tree_max t2 m) (check (print_tree_max t1 m) v)

let rec print_tree_sum t m =
    match t with
    | Leaf (v) -> 
        let s = m+v
        s
    | Node (t1,t2,v) ->
        (print_tree_sum t1 m + print_tree_sum t2 m)+v


let rec foldR f z l =
    match l with
    | [] -> z
    | x :: xs -> f (foldR f z xs) x 


// foldL : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b
let rec foldL f z l =
    match l with
    | [] -> z
    | x :: xs -> foldL f (f z x) xs





[<EntryPoint>]
let main argv =
    //let c = fun x -> fun y -> x+y
    //let k = c 8 9
    let l = [2;5;7;13;64;127;32]
    let g = map (fun x -> fun y -> 
            if x>y 
            then if x%2=0 then x else y 
            else y) l 0

    let g2 = filter (fun x -> if x%2 = 0 then true else false) l
    let g2 = map (fun x y -> if x > y then x else y) g2 0
    
    let treeO = Node (Node (Node (Leaf 1, Leaf 2,10), Leaf 3, 7), Leaf 4, 1)
    
    let s1 = foldL (+) "" ["a"; "b"; "c"]  
    let s2 = foldR (+) "" ["a"; "b"; "c"] 
    printfn("%O") s1
    printfn("%O") s2
    //let tree1, tree2 = divide_list l
   // print_tree tree1
    main_interactive ()
   // main_interpreter "test.tml"
    
    Console.ReadLine () |> ignore
    0
