(*
* TinyML
* Typing.fs: typing algorithms
*)

//Immaginare i test, come testo questo? 


// f x + 1 , applica f con x e poi fa più 1
// f (x + 1) applica f con (x+1)

//UNEXPECTED ERROR, MEANS FOR THE DEVELOPER, you forgot to support something
//Type error, for the user

//Quando tipi una lambda butti dentro l'env una fresh variable che ha il quantificatore senza quantificazione
//Gli do un type scheme e non gli assegno il tipo subito sennò poi non potrei toccarlo

//Se mi porto dietro equazione e basta non ho direzione, (con sostituzione ce l'ho) (forse è solo roba formale questa)

//Produrre un type variable e legarla a un arrow type (magari torna utile sta roba)
//Mettendo un tipo libero dentro l'env permette di non quantificarlo e fare in modo che in futuro qualcuno possa unificarla. E' uno schema in verità a->b qualcuno potrà unificarlo più avanti
//let rec va inferito da cosa torna e da cosa prende

//Grosso da fare qui, destrezza!
module TinyML.Typing

open Ast


//Define new variable for floats and an active pattern for that


let type_error fmt = throw_formatted TypeError fmt

//What a substitution is? (subs rule), always type variables on the left and type on the right. On the left I have only type variables (I want to substitute the type variables)
//It is an environment where instead having identifier I have type variables and instead of having values on the right I have types
//Substition is a list of couples like above
//When you apply substitution on tyvar, I apply substitution to all!
type subst = (tyvar * ty) list

(*
Example of substitution:
let f x y = (x,y) in
let g x = f x x
in ()

final type is unit
We can collect all the let binding and all the substitution will have some type variables durign the execution of the program, printing typing env at the end will print the let bindings

Apply substitution incrementally (type inference produce a type and a substitution), and I compose with the subterm (if there is some) else, I return.
That type and subs can be return without applying the subs to the type, or returns the variable substituted
Tupla ogni pezzo produce un tipo e una sub, poi fai composizione perchè un pezzo ti può servire per le altre 
e la prima la applichi già al risultato della seconda invece che inferire tutto e POI fare la composizione. La composizione delle subs deve poter dare errori:
Devono avere domini disgiunti

Esempio operatori aritmetici monomorfi:
let f = fun x -> (x + 1, x +. 1.2)
faccio unificare x a int e quello dopo a float (abbiamo due sub alfa che va a float e a int, devo verificare che i domini siano disgiunti, non posso inferire due cose diverse per 
la stessa type variable.
Quando componi non devi produrre ambiguità, altrimenti dovrebbe produrre type error

let f = fun x -> (x + 1, if x then 1 else 2), qua dovrebbe dare errore! non può essere sia int che bool. Erorr reporting diverso
Se sostituisco subito, la prima inferisce x come int, applico sub all'ambiente e poi da errore quando cerco di unificare int e bool
Se inferisco tutto e poi compongo ho errore al tempo della composizione

*)
    
//TyName , TyArrow , TyVar = 'a , TyTuple

let mutable tyvar_cont = 0

let add_tyvar =
    let v = TyVar(tyvar_cont)
    tyvar_cont <- tyvar_cont + 1
    v

//DEVO FARE IL PATTERN MATCH, SE SONO ENTRAMBI TYPENAME ALLORA O ERRORE SE SONO TIPI DIVERSI O SOSTITUZIONE VUOTA,
//POI I CASI CON I TYVAR che sono le variabili libere p.5/5 pagina 3
let rec unify (t1 : ty) (t2 : ty) : subst = //empty list, empty substitution
    match (t1 , t2) with
    | (TyName t1, TyName t2) -> 
        match t1 with
        | t2 when t1 = t2 -> [] //empty subs, no need to subs two var of the same type
        | _ -> unexpected_error "Type inference error: you're trying to substitute two variables with different types"
    | (TyVar t1, t2) -> [(t1,t2)] 
    | (t1, TyVar t2) -> [(t2,t1)] 
    | (TyArrow(a,b) , TyArrow(c,d)) -> unify a b @ unify c d
    //| (TyArrow(_,_)),(TyVar _)  -> []
    | _ -> unexpected_error "You're trying to unify something that can't be unified"
    //I think that subst is a list of tyvar and if this tyvar is the same type of tyName? Not sure of that, I apply subs!
  //  | (TyArrow t1, TyArrow t2) -> [] //In that case is compose subs, what does it mean? Idk
    


    //Ripensato: se t è uguale a tyvar nella lista di sub allora t diventa il tipo! Se c==a allora t=b
let rec map(f,l) c =
    match l with
    | [] -> []
    | x :: xs -> f x c :: map (f,xs) c 

let find_subs (a,b) t = 
    if t = TyVar(a) then b else t
    
let apply_subst (t : ty) (s : subst) : ty = 
    let res = map (find_subs, s) t
    printf "%O" res
    t //I think that this is good ... ?
    
let compose_subst (s1 : subst) (s2 : subst) : subst =   //With 2 subs I have to apply composition
     let res = List.distinct (s1@s2)
     res
    //Non so


//Generalization, operation we perform after having typed the right part of the let binded, If there are type variables left, you quantify that, We need a way to quantify that
//Free variables are the occurences of the type variables. An algorithm to calculate the occurences of a type variable. Variables not binded by let
//We match the type. 
let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2) //We merge the two types on the arrow
    | TyVar tv -> Set.singleton tv //I produce a list with that tyvar
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts //We start with the empty set and we're folding ts.
    //How fold works (parameters): function applying each stage(accumulator, each element) initial state of accumulator, list we are foldin. t is our accumulator that starts empty


    //We find All free vars of the type, and then we substract from the list of tyvar
    //The element of the set is polymorphic, the hierarchy is not polymorphic. We have to use a library if we want a polymorphic set
let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)

// type inference
//

//List of pairs
//Just a definition, when you call the type inference in the main, you're basic environment tenv won't be empty but will be gamma0
let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))

]

// TODO for exam
let rec compose list =
   match list with
   | head :: tail ->compose_subst head (compose tail)
   | [] -> []

let split_elements l x =
    l::x
   
let set_to_list s = Set.fold (fun l se -> se::l) [] s //l is the accumulator, we add every pieces of the set in a list

//let prova scheme =
  //  let (scheme s) = scheme
   // ()

//Probably we don't want to have operator like operators, but implemented natively
//Man mano che ho i tipi giusti li applico all'ambiente
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
   // | App (e1, e2) -> //We already have the application case (not really)
    | Lit (LInt _) -> (TyInt,[])
    | Lit (LFloat x) -> (TyFloat,[])
    | Lit (LString _) -> (TyString,[])
    | Lit (LChar _) -> (TyChar,[])
    | Lit (LBool _) -> (TyBool,[])
    | Lit LUnit -> (TyUnit,[])
    | Tuple es -> 
    // l is the list given by inferring all the elements of the typle
        let l = (List.map (typeinfer_expr env) es)
    //For every substitution that i have on this list i call compose_subst and i only have one subst with all substitution needed on the tuple (s)
        let s = compose (List.map snd l)
    //List of the types in this tuple (t)
        let t = List.map fst l
        (TyTuple(t),s)
  
    | IfThenElse (e1, e2, e3o) ->
        let t1 = typeinfer_expr env e1
        let s = unify (fst t1) (TyBool) 
        let t2 = typeinfer_expr env  e2
        match e3o with
        | None ->
            let u = unify(fst t2)(TyUnit) 
            (TyUnit,[])
        | Some e3 ->
            let t3 = typeinfer_expr env e3
            let s2 = unify (fst t2) (fst t3)
            (fst t2 , compose_subst(s)(s2))
            
    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typeinfer_expr env e1
        let t2 = typeinfer_expr env e2
        (fst t1 , unify(fst t1) (fst t2))

    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typeinfer_expr env e1
        let t2 = typeinfer_expr env e2
        (TyBool , unify(fst t1) (fst t2))

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typeinfer_expr env e1
        let t2 = typeinfer_expr env e2
        let s1 = unify (fst t1) (TyBool)
        let s2 = unify (fst t2) (TyBool)
        (TyBool , compose_subst(s1)(s2))

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not" , e) ->
        let t = typeinfer_expr env e
        let s = unify (fst t)(TyBool)
        (TyBool,s)
    
    | UnOp ("-", e) ->
        let t = typeinfer_expr env e
        let s = match (fst(t)) with
                | TyInt -> unify (fst t)(TyInt)
                | TyFloat -> unify (fst t)(TyFloat)
                | _ -> unexpected_error "Unco rrect use of operan -, type that can use that operator are int and float, given:  %s" (pretty_ty (fst t))
        ((fst t),s)

        //I search if the var is present on the env, yes means that I have to return that type, no means that I have to sign in the env that it's a tyVar
    | Var x ->
        let res  = List.find (fun (y, _) -> x = y) env    //tryFind
        let k = freevars_scheme(snd(res))
        let tv_list = set_to_list(k)
        let sub = List.map(fun x -> (x,add_tyvar)) tv_list  
        let (Forall(_,t)) = snd(res)
        (t,sub)
        //How do I find the type?
        //With that I have to refresh the quantified vars, and we have the subs.
        //match res with
        //| Some -> let (Forall (_,t)) = snd(res) in (t,[])
        //| None -> 
        //let c: tyvar list = set_to_list res
        //let env0 = (x, Forall (c,TyVar(c.Head))) :: env
        

    | Lambda (x, Some t, e) ->  
        let s = typeinfer_expr env e
        let u = unify (fst s) (t)
        let final_subs = compose_subst(u)(snd s)
        ((fst s),final_subs)



    | Lambda (x, None, e) ->  
        let v = add_tyvar
        let set = freevars_ty(v)
        let env0 = (x, Forall (set_to_list(set),v)) :: env
        let s = typeinfer_expr env0 e 
        s


        //let x = e1 in e2
    | Let (x, tyo, e1, e2) ->
        let t1 = typeinfer_expr env e1
        let c = List.map fst (snd(t1))
        match tyo with
        | None -> 
            let v = add_tyvar
            let set = freevars_ty(v)
            let env1 = (x, Forall (set_to_list(set),v))::env
            let t2 = typeinfer_expr env1  e2 //add free var alfa to env
            let final_subs = compose_subst(snd t1)(snd t2)
            (fst(t2),final_subs)
            
        | Some tyo -> 
            let env0 = (x, Forall (c,fst(t1)))::env 
            let s = unify(tyo)(fst t1)
            let t2 = typeinfer_expr env0 e2
            let final_subs = compose_subst (compose_subst(snd t1)(snd t2)) (s)
            (fst(t2),final_subs)
           
            
            //infinite n = letrec ns = cons n ns in ns


    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    //| LetRec (f, Some tf, e1, e2) ->
       //Add to env the type of the function (with subs) and... do things...? 
       (* let env0 = (f, tf) :: env
        let t1 = typeinfer_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)*)
           
    //TO DO: Di base final_s = compose_subst(subst per t1)(subst per t2) compose subst con (t1;t2->Beta), poi checckare i tipi?
    | App (e1, e2) ->
        let t1 = typeinfer_expr env e1
        let t2 = typeinfer_expr env e2
        match fst (t1) with
        | TyArrow (l, r) ->
            let s = compose_subst (snd t1)(snd t2)
            let ft1 = fst(t1)
            let ft2 = TyArrow(fst(t2),r)
            let u = unify(ft1)(ft2)
            let final_subs = compose_subst(s)(u)
            (l,final_subs)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty (fst t1))
    | _ -> failwith "not implemented"


//I rebind to this so whenever You call type inference I append the env. Another trick!
//let typeinfer_expr env e = typeinfer_expr (gamma0 @ env) e

// type checker
//
    
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        t

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)
   
    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    //Arithmetic operator
    //It Matches this operator, as means that we can substitute the string with op. we typecheck left and right, if both are the same, it's ok and work, else error
    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
     

    //Logical operator
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e