module TinyML.Typing

open Ast


let type_error fmt = throw_formatted TypeError fmt

//What a substitution is? (subs rule), always type variables on the left and type on the right. On the left I have only type variables (I want to substitute the type variables)
//It is an environment where instead having identifier I have type variables and instead of having values on the right I have types
//Substition is a list of couples like above
//When you apply substitution on tyvar, I apply substitution to all!
type subst = (tyvar * ty) list


//This variable is used to create new tyvariables
let mutable tyvar_cont = 0

let add_tyvar =
    let v = TyVar(tyvar_cont)
    tyvar_cont <- tyvar_cont + 1
    v


//Generalization, operation we perform after having typed the right part of the let binded, If there are type variables left, you quantify that, We need a way to quantify that
//Free variables are the occurences of the type variables. An algorithm to calculate the occurences of a type variable. Variables not binded by let
//We match the type. TyVar not binded
let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2) //We merge the two types on the arrow
    | TyVar tv -> Set.singleton tv //I produce a list with that tyvar
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts //We start with the empty set and we're folding ts.
    //How fold works (parameters): function applying each stage(accumulator, each element) initial state of accumulator, list we are foldin. t is our accumulator that starts empty


let rec unify (t1 : ty) (t2 : ty) : subst = //empty list, empty substitution
    match (t1 , t2) with
    | TyName tn1, TyName tn2 -> if tn1 = tn2 then [] else type_error "unify: cannot unify %s with %s" tn1 tn2
    | TyVar tv1, TyVar tv2 -> if tv1 = tv2 then [] else type_error "unify: cannot unify" //Doesn't work
    | (TyVar tv, tn)  //Check if variables are free, if they are then I can create the substitution, else I can't 
    | (tn, TyVar tv) -> if not (Set.contains tv (freevars_ty tn)) then [(tv, tn)] else type_error "unify: cannot unify %s with %s" (pretty_ty tn) (pretty_ty (TyVar tv))
    | (TyArrow(a,b) , TyArrow(c,d)) -> unify a c @ unify b d
    | _ -> type_error "You're trying to unify something that can't be unified dog"

   //I substitute the tyvar with the type!
let apply_subst (t : ty) (s : subst) : ty = 
    let rec apply_subst_item sub ct =
        let tv, t0 = sub
        match ct with
        | TyName _ -> ct
        | TyVar ttv -> if ttv = tv then t0 else ct
        | TyArrow (t1, t2) -> TyArrow (apply_subst_item sub t1, apply_subst_item sub t2)
        | TyTuple (ts) -> TyTuple (List.map (apply_subst_item sub) ts)
    List.foldBack (apply_subst_item) s t
    
let compose_subst (s1 : subst) (s2 : subst) : subst =   //With 2 subs I have to apply composition
     let res = List.distinct (s1@s2)
     res



    //We find All free vars of the type, and then we substract from the list of tyvar
    //The element of the set is polymorphic, the hierarchy is not polymorphic. We have to use a library if we want a polymorphic set
let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)

    //Given an environment returns a tyvar Set empty in the empty case
    //I obtain the free variables in the environment
let rec freevars_env (env: scheme env) : tyvar Set =
    match env with
    | [] -> Set.empty
    | (_, sc) :: envs -> Set.union (freevars_scheme sc) (freevars_env envs)  

// type inference
//

//List of pairs
//Just a definition, when you call the type inference in the main, you're basic environment tenv won't be empty but will be gamma0
let gamma0 = [
    ("+", Forall ([], TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("-", Forall ([], TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("u-", Forall ([], TyArrow (TyInt, TyInt)))
    ("*", Forall ([], TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("/", Forall ([], TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("%", Forall ([], TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("+.", Forall ([], TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("-.", Forall ([], TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("u-.", Forall ([], TyArrow (TyFloat, TyFloat)))
    ("*.", Forall ([], TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("/.", Forall ([], TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("%.", Forall ([], TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("and", Forall ([], TyArrow (TyBool, TyArrow (TyBool, TyBool))))
    ("or", Forall ([], TyArrow (TyBool, TyArrow (TyBool, TyBool))))
    ("not", Forall ([], TyArrow (TyBool, TyBool)))
]

let rec compose list =
   match list with
   | head :: tail ->compose_subst head (compose tail)
   | [] -> []

   
let set_to_list s = Set.fold (fun l se -> se::l) [] s //l is the accumulator, we add every pieces of the set in a list


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
        let t = TyTuple(List.map fst l)
        (t,s)
  
    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let u = unify (t1) (TyBool) 
        let t2, s2 = typeinfer_expr env  e2
        let sub = compose_subst(compose_subst(s2)(s1))(u)
        let final_subst = 
            match e3o with
                | None -> 
                    let u = unify t2 TyUnit
                    compose_subst sub u
                | Some e3 -> 
                    let t3,s3 = typeinfer_expr env e3
                    let u2 = unify (t2)(t3)
                    compose_subst(compose_subst(u2)(s3))(sub)
        (apply_subst(t2)(final_subst),(final_subst))
        
          

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let s = compose_subst s1 s2
        let t1_s = apply_subst t1 s
        let t2_s = apply_subst t2 s
        let t3, s3 =
            match t1_s, t2_s with
                | TyInt, TyInt -> TyInt, []
                | TyVar tv, TyInt 
                | TyInt, TyVar tv -> TyInt, unify (TyVar tv) TyInt

                | TyFloat, TyFloat -> TyFloat, []

                | TyVar tv, TyFloat 
                | TyFloat, TyVar tv -> TyFloat, unify (TyVar tv) TyFloat

                |TyVar tv1, TyVar tv2 -> TyInt, [tv1, TyInt] @ [tv2, TyInt] 
                | _ -> type_error "binary operator expects two numeric homogenous operands, but got \"%s\" %s \"%s\"" (pretty_ty t1) op (pretty_ty t2)
        let s = compose_subst s1 (compose_subst s2 s3)
        (apply_subst t3 s, s)



    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let s = compose_subst s1 s2
        let t1_s = apply_subst t1 s
        let t2_s = apply_subst t2 s
        let t3, s3 =
            match t1_s, t2_s with
                | TyInt, TyInt
                | TyFloat, TyFloat
                | TyInt, TyFloat
                | TyFloat, TyInt -> TyBool, []

                | TyInt, TyVar tv
                | TyVar tv, TyInt -> TyBool, unify (TyVar tv) TyInt
                | TyFloat, TyVar tv 
                | TyVar tv, TyFloat -> TyBool, unify (TyVar tv) TyFloat

                //| TyVar tv1, TyVar tv2 -> TyBool, [tv2, TyVar tv1] // this should only work if there's a sub from the tyvars to "comparable"... at most i can say they have to be the same type
                | _ -> type_error "binary operator expects two equivalent numeric operands, but got \"%s\" %s \"%s\"" (pretty_ty t1) op (pretty_ty t2)
        let s = compose_subst s1 (compose_subst s2 s3)
        (apply_subst t3 s, s)

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let s3 =
            match t1, t2 with
            | TyBool, TyBool -> []
            | TyBool, TyVar tv
            | TyVar tv, TyBool-> unify (TyVar tv) TyBool
            | TyVar _tv1, TyVar _tv2 -> unexpected_error "Unexpected keyword '%s' in \"%s\"" op (pretty_expr (BinOp (e1, op, e2)))
            | _ -> type_error "binary operator expects two bools operands, but got \"%s\" %s \"%s\"" (pretty_ty t1) op (pretty_ty t2)
        let s = compose_subst s1 (compose_subst s2 s3)
        let t3 = TyBool
        (apply_subst t3 s, s)


    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t, s = typeinfer_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        (apply_subst t s, s)

            
    | UnOp ("-", e) ->
        let t, s = typeinfer_expr env e
        let t1 = 
            match t with
                | TyInt -> TyInt
                | TyFloat -> TyFloat
                | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)
        (apply_subst t1 s, s)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

        //I search if the var is present on the env, yes means that I have to return that type, no means that I have to sign in the env that it's a tyVar and refresh other vars
        //This happen because I trust that the unify will solve that
    | Var x ->
        try
            let instantiate s = 
                let rec refresh vl = 
                    match vl with  //I check if variables are found 
                    | [] -> []
                    | v :: vs ->  //If yes I refresh their values
                        tyvar_cont <- tyvar_cont + 1
                        compose_subst [(v, TyVar (tyvar_cont))] (refresh vs)
                
                
                let vars, t = match s with Forall (_v, _t) -> (_v, _t)
                let refreshed = refresh vars //I refresh all of the tyvars
                (apply_subst t refreshed, refreshed) //Then I apply the subs

            let _, sch = List.find (fun (y, _) -> x = y) env
            instantiate sch
        with :? System.Collections.Generic.KeyNotFoundException -> unexpected_error "Variable %s not bound in the environment\nenv:" x
       

    | Lambda (x, tyo, e) ->  
        let v = add_tyvar
        //I infer the type after I add my new fresh variable in the env
        let t1, s1 = typeinfer_expr ((x, Forall ([], v)) :: env) e
        //Then I check if the notated type is present and, in case, I unify
        let s2 =
            match tyo with
                | Some tyo -> unify t1 tyo
                | None -> []
        let t = TyArrow (v,t1)
        let final_subs = compose_subst s1 s2
        (apply_subst t final_subs,final_subs)


        //let x = e1 in e2
    | Let (x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let u = 
            match tyo with
                | None -> []
                | Some tyo -> unify (t1) (tyo) 
        let not_binded = Forall (set_to_list(Set.difference( freevars_ty t1) (freevars_env env)), t1) //I add to the env the tyvars not already binded
        let t2,s2 = typeinfer_expr ((x,not_binded)::env) e2
        let final_subs = compose_subst(compose_subst (s1)(s2))(u)
        (apply_subst t2 final_subs, s2)

      //First I add v to the env then I evaluate e1
    | LetRec (f, tyo, e1, e2) ->
        let v = add_tyvar //This new variable represent the type of my function
        let env1 = (f, Forall ([],v))::env //I add the name of the function to the e
        let t1,s1 = typeinfer_expr env1 e1           
        //I check if type option is there or not
        match tyo with
        | Some(tyo) -> 
            match tyo with
                | TyArrow(_,TyName _) -> //On let rec optional type must be an arrow type and its codomain has to be a TyName
                    let u = unify(tyo)(t1) //I check that ty option is the same type of t1
                    let t2,s2 = typeinfer_expr env1 e2
                    let final_subs = compose_subst(compose_subst (s1)(s2))(u) 
                    (t2,final_subs)
                | _ -> unexpected_error "on let rec the optional type must be an arrow type where the codomain is a type name, %s given " (pretty_ty tyo) tyo
        | None ->         
            let t2,s2 = typeinfer_expr env1 e2
            let final_subs = compose_subst(s1)(s2)
            (t2,final_subs)
       
    
    | App (e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let v = add_tyvar
        //I add a fresh variables (the right of the arrow type) and I unify t1 and "t2" (t2 = t2->tyvar)
        let final_subs = compose_subst (compose_subst (unify t1 (TyArrow (t2, v))) s1) s2
        (apply_subst v final_subs, final_subs)

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e



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