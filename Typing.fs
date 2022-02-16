(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

// type inference
//

// starting environment with operation
let gamma0 : scheme env = [
    ("+", Forall([],TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("-", Forall([],TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("*", Forall([],TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("/", Forall([],TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("%", Forall([],TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("=", Forall([],TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    ("<", Forall([],TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    ("<=", Forall([],TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    (">", Forall([],TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    ("=>", Forall([],TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    ("<>", Forall([],TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    ("and", Forall([],TyArrow (TyBool, TyArrow (TyBool, TyBool))))
    ("or", Forall([],TyArrow (TyBool, TyArrow (TyBool, TyBool))))
    ("not", Forall([],TyArrow (TyBool, TyBool)))
    ("-", Forall([],TyArrow (TyInt, TyInt)))

    
    ("+.", Forall([],TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("-.", Forall([],TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("*.", Forall([],TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("/.", Forall([],TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("%.", Forall([],TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("=.", Forall([],TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("<.", Forall([],TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("<=.", Forall([],TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    (">.", Forall([],TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("=>.", Forall([],TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("<>.", Forall([],TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("-.", Forall([],TyArrow (TyFloat, TyFloat)))
]

let mutable counter = -1

let generate_fresh_variable () =
    counter <- counter + 1
    counter + int 'a'
        |> char
        |> string

let rec occurs (tv : tyvar) (t : ty) : bool = 
    match t with
    | TyVar t1 -> tv = t1
    | TyArrow (t1,t2) -> occurs tv t1 || occurs tv t2
    | TyName t1 -> false
    | TyTuple tt -> let rec occ_list (tv : tyvar) (t : ty list) : bool =
                        match t with
                        |[] -> false
                        |head::tail -> if occurs tv head
                                       then true
                                       else occ_list tv tail
                    occ_list tv tt

// TODO implement this
let compose_subst (s1 : subst) (s2 : subst) : subst = s1 @ s2

// TODO implement this
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match t1, t2 with
    | TyName n1, TyName n2 -> if n1 <> n2 
                              then type_error "unify: unification between different variables name can't be execute"
                              else []
    | TyVar tv, _ -> if occurs tv t2 
                     then type_error "unify: unification fails because variable %O occurs in %O " tv t2
                     else [(tv , t2)]

    | _ , TyVar tv -> if occurs tv t1 
                      then type_error "unify: unification fails because variable %O occurs in %O " t1 tv
                      else [(tv , t1)]

    | TyArrow (tl1,tr1), TyArrow (tl2,tr2) ->   let u1 = unify tl1 tl2
                                                let u2 = unify tr1 tr2
                                                compose_subst u1 u2

                                                (*let subs1 = unify tl1 tl2
                                                let te1 = apply_subst tr1 subs1 
                                                let te2 = apply_subst tr2 subs1 
                                                let subs2 = unify te1 te2
                                                compose_subst subs1 subs2*)
    | _ -> unexpected_error "unify: unsupported operation"

(* substitute term s for all occurrences of var x in term t *)
let rec subst (s : ty) (x : tyvar) (t : ty) : ty =
  match t with
  | TyVar y -> if x = y then s else t
  | TyArrow (u, v) -> TyArrow (subst s x u, subst s x v)
  | TyName n -> t
  | TyTuple ts -> TyTuple(List.map (subst s x) ts)

// TODO implement this
let apply_subst (t : ty) (s : subst) : ty = 
  List.foldBack (fun (x, e) -> subst e x) s t

let apply_subst_helper s t = apply_subst t s

// Give all tyvar in a type -> FV
let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 

let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)

let rec freevars_env (en: scheme env) : tyvar Set =
    match en with
    | [] -> Set.empty
    | e  -> match e with
            |(_,sc)::tail -> Set.union (freevars_env tail) (freevars_scheme sc)


let generalize (env : scheme env) (typ : ty) : scheme =
    let vars = Set.difference (freevars_ty typ) (freevars_env env)
    Forall (Set.toList vars, typ)

let instantiate (Forall (tvs, typ)) : ty =
    let nvars = List.map (fun _ -> TyVar(generate_fresh_variable()) ) tvs
    let s = Map.ofSeq (Seq.zip tvs nvars) |> Map.toList
    apply_subst typ s

let rec tupleMap l: subst =
    match l with
    |[] -> []
    |head::tail -> 
                   match head with
                   |(_,su) -> compose_subst su (tupleMap tail)

let rec tupleMap2 l: ty list =
    match l with
    |[] -> []
    |head::tail -> 
                   match head with
                   |(typ,_) -> typ::(tupleMap2 tail)
// type inference
//

let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Var x -> 
        let _, t = List.find (fun (y, _) -> x = y) env
        let s = instantiate t
        (s, [])

    | Lit (LInt _) -> (TyInt, [])
    | Lit (LFloat _) -> (TyFloat, [])
    | Lit (LString _) -> (TyString, [])
    | Lit (LChar _) -> (TyChar, [])
    | Lit (LBool _) -> (TyBool, [])
    | Lit LUnit -> (TyUnit, [])

    | App (e1, e2) ->
        let codTy = TyVar(generate_fresh_variable ())
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let s3 = unify t1 (TyArrow (t2,codTy))
        let s32 = compose_subst s3 s2 
        let s321 = compose_subst s32 s1
        (apply_subst codTy s321, s321) 

    | Lambda (x, None, e) ->
        let freshVar = TyVar(generate_fresh_variable())
        let sc1 = Forall([],freshVar) //46:00 lesson 30 november
        let t,s = typeinfer_expr((x, sc1) :: env) e
        let finalType = apply_subst (TyArrow(freshVar,t)) s
        (finalType,s)

    | Lambda (x, Some typ, e) ->
        let sc1 = Forall([],typ)
        let t,s = typeinfer_expr((x, sc1) :: env) e
        let finalType = apply_subst (TyArrow(typ,t)) s
        (finalType,s)

    //monomorphic version
    (*| Let (x, None , e1, e2) -> 
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr ((x,t1) :: env) e2
        let s3 = compose_subst s2 s1
        (t2, s3)*)

    //polimorphic version
    | Let (x, None , e1, e2) -> 
        let t1, s1 = typeinfer_expr env e1
        //Generalize
        let sc1 = generalize env t1
        let t2, s2 = typeinfer_expr ((x,sc1) :: env) e2
        let s3 = compose_subst s2 s1
        let t = apply_subst t2 s3
        (t, s3)

    | LetRec (f, None, e1, e2) ->
        let funTy = TyVar(generate_fresh_variable())
        let env = (f,Forall([],funTy)):: env
        let t1, s1 = typeinfer_expr env e1
        let t1 = apply_subst t1 s1
        let su = unify funTy t1
        let s = compose_subst su s1
        let env = (f,generalize env t1)::env
        let t2,s2 = typeinfer_expr env e2
        let s = compose_subst s2 s
        let t2 = apply_subst t2 s
        (t2,s)

    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let s4 = unify t1 TyBool
        match e3o with
        | None -> let s5 = unify t2 TyUnit
                  let tot = compose_subst (compose_subst (compose_subst s5 s4) s2) s1
                  (apply_subst t2 s5, tot)

        | Some ex -> let t3, s3 = typeinfer_expr env ex
                     let s5 = unify t2 t3
                     let tot = compose_subst (compose_subst (compose_subst (compose_subst s5 s4) s3) s2) s1
                     (apply_subst t2 s5, tot)

    | Tuple es ->
        let t = List.map (typeinfer_expr env) es
        let comp = tupleMap t
        let typL =  tupleMap2 t
        let typ = TyTuple(List.map (apply_subst_helper comp) typL)
        (typ,comp)

    | BinOp(e1, op, e2) ->
        typeinfer_expr env (App (App (Var op, e1), e2))

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op
        
    | UnOp(op, e) ->
        typeinfer_expr env (App (Var op, e))

    | UnOp (op, _) -> unexpected_error "typeinfer_expr: unsupported unary operator (%s)" op

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

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt
        | TyFloat, TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> ()
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
