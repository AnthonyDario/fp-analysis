(* Uses CIL to parse the C AST *)
open GoblintCil
open Tree
open Printing

module E = Errormsg
module F = Frontc
module C = Cil

exception ParseException ;;

let parse_one_file fname = 
    let cabs, cil = F.parse_with_cabs fname () in
    Rmtmps.removeUnusedTemps cil ;
    cil ;;

let transform_const c =
    match c with
    | CReal (f,_,_) ->
        CVal f
    | CInt (i,_,_) ->
        CVal (Float.of_int (Cilint.int_of_cilint i))
    | _ -> 
        E.log "Only numbers supported\n" ;
        raise ParseException

let rec transform_arith_binop op l r =
    let new_l, new_r = (transform_aexp l, transform_aexp r) in
    match op with
    | PlusA ->
        CAdd (new_l, new_r)
    | MinusA ->
        CSub (new_l, new_r)
    | Mult ->
        CMul (new_l, new_r)
    | Div ->
        CDiv (new_l, new_r)
    | _ -> 
        E.log "Expected Arithmetic Binop\n" ; 
        raise ParseException
    
and transform_aexp e =
    match e with
    | Cil.Const c ->
        transform_const c
    | BinOp (op, l, r, _) ->
        transform_arith_binop op l r
    | Lval lv ->
        CVar (transform_lval lv)
    | _ -> 
        E.log "Unknown aexp\n" ;
        raise ParseException
    (* TODO: Support casting from int to float
    *)

(* Gets the name of the variable *)
and transform_lval (lhost, _) =
    match lhost with
    | Var vi -> vi.vname
    | _ -> 
        E.log "lvalues of type [T] not supported\n" ;
        raise ParseException
    ;;

(* TODO: Figure out how true/false is represented, possibly as 1 and 0 consts *)
let rec transform_bexp e =
    match e with
    | BinOp (op, l, r, _) ->
        transform_bool_binop op l r
    | _ -> 
        E.log "Unknown exp\n" ;
        raise ParseException
    
and transform_bool_binop op l r =
    let new_l, new_r = (transform_aexp l, transform_aexp r) in
    match op with
    | Lt ->
        CLt (new_l, new_r)
    | Gt ->
        CGt (new_l, new_r)
    | Le ->
        CLe (new_l, new_r)
    | Ge ->
        CGe (new_l, new_r)
    | Eq ->
        CEq (new_l, new_r)
    | Ne ->
        CNe (new_l, new_r)
    | _ -> 
        E.log "Expected comparison operator\n" ; 
        raise ParseException

let transform_instr i =
    match i with
    | Set (lv, e, _, _) ->
        CAsgn ((transform_lval lv), (transform_aexp e))
    | _ -> 
        E.log "Only assignment instructions supported\n" ;
        raise ParseException
    ;;

let rec transform_stmt s =
    match s.skind with
    | Instr (i1 :: is) ->
        List.fold_left 
            (fun acc i -> CCol (acc, transform_instr i)) 
            (transform_instr i1) 
            is
    | If (c, b1, b2,_,_) -> 
        CIf (transform_bexp c, transform_block b1, transform_block b2)
    | _ ->
        E.log "Unsupported statement\n" ;
        raise ParseException

and transform_block b = 
    (* TODO: Returns could be important. They can contain logic...*)
    let stmts = List.filter 
                    (fun s -> 
                        match s.skind with
                        | Return (_,_) -> false 
                        | _ -> true) 
                    b.bstmts in
    match stmts with
    | s1 :: stmts ->
        List.fold_left (fun acc s -> CCol (acc, transform_stmt s)) 
                       (transform_stmt s1) 
                       stmts
    | _ -> 
        E.log "Empty function declaration\n" ;
        raise ParseException ;;

let transform_fun f =
    let { sformals = formals; slocals = locals; sbody = body } = f in
    transform_block body ;;

let transform_global g =
    match g with
    | GFun (dec,_) ->
        transform_fun dec
    | _ -> 
        E.log "Non-function globals not supported\n" ;
        raise ParseException
    ;;

let transform f = 
    transform_global 
        (List.find (fun g -> 
            match g with
            | GFun (dec,_) -> dec.svar.vname = "main"
            | _ -> false) f.globals ) ;;
