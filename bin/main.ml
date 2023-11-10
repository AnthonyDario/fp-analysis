open Float
open Format
open Tree
open Printing

(* Abstraction *)
(* alpha : CStmt -> AStmt *)
let ulp f = succ f -. f ;;

let abst_flt f = { int = { u = f ; l = f }; err = ulp f } ;;

let rec abst_aexp exp = 
    match exp with
    | CVal v      -> AVal (Eterm (abst_flt v))
    | CVar n      -> AVar n
    | CAdd (l, r) -> AAdd ((abst_aexp l), (abst_aexp r))
    | CSub (l, r) -> ASub ((abst_aexp l), (abst_aexp r))
    | CMul (l, r) -> AMul ((abst_aexp l), (abst_aexp r))
    | CDiv (l, r) -> ADiv ((abst_aexp l), (abst_aexp r)) ;;

let abst_bexp exp =
    match exp with
    | CLt (l, r) -> ALt ((abst_aexp l), (abst_aexp r))
    | CLe (l, r) -> ALe ((abst_aexp l), (abst_aexp r))
    | CEq (l, r) -> AEq ((abst_aexp l), (abst_aexp r))
    | CNe (l, r) -> ANe ((abst_aexp l), (abst_aexp r))
    | CGe (l, r) -> AGe ((abst_aexp l), (abst_aexp r))
    | CGt (l, r) -> AGt ((abst_aexp l), (abst_aexp r)) ;;
    
let rec abst_stmt exp = 
    match exp with
    | CAsgn (n, v)       -> AAsgn (n, (abst_aexp v))
    | CIf   (b, t, e)    -> AIf ((abst_bexp b), (abst_stmt t), (abst_stmt e))
    | CFor  (i, c, b, a) -> 
        AFor ((abst_stmt i), (abst_bexp c), (abst_stmt b), (abst_stmt a))
    | CCol  (f, s)       -> ACol ((abst_stmt f), (abst_stmt s)) ;;

(* Abstract semantics *)

let max_flt l = List.fold_left max neg_infinity l ;;
let min_flt l = List.fold_left min infinity l ;;

(* Interval Operators *)
let intr_add l r = { l = l.l +. r.l ; u = l.u +. r.u } ;;
let intr_sub l r = { l = l.l -. r.l ; u = l.u -. r.u } ;;
let intr_mul l r = 
    { l = min_flt [l.l *. r.l ; l.l *. r.u ; l.u *. r.l ; l.u *. r.l] ; 
      u = max_flt [l.l *. r.l ; l.l *. r.u ; l.u *. r.l ; l.u *. r.l] } ;;
let intr_div l r = 
    { l = min_flt [l.l /. r.l ; l.l /. r.u ; l.u /. r.l ; l.u /. r.l] ; 
      u = max_flt [l.l /. r.l ; l.l /. r.u ; l.u /. r.l ; l.u /. r.l] } ;;

(* Error Propagation *)
let mag_lg i = max_flt [(abs i.l) ; (abs i.u)] ;;
let mag_sm i = min_flt [(abs i.l) ; (abs i.u)] ;;

let ulp_add l r = 0.5 *. ulp ((abs l.int.u) +. (abs r.int.u) +. l.err +. r.err) ;;
let ulp_sub l r = 0.5 *. ulp ((mag_lg l.int) +. (mag_lg r.int) +. l.err +. r.err) ;;
let ulp_mul l r = 
    0.5 *. ulp (((mag_lg l.int) +. l.err) *. ((mag_lg r.int) +. r.err)) ;;
let ulp_div l r = 
    0.5 *. ulp (((mag_lg l.int) +. l.err) /. ((mag_sm r.int) +. r.err)) ;;

let err_add l r = l.err +. r.err +. ulp_add l r ;;

let err_sub l r = abs (l.err +. r.err) +. ulp_sub l r ;;

let err_mul l r =
    let lup = mag_lg l.int in
    let rup = mag_lg r.int in
    lup *. r.err +. rup *. l.err +. l.err *. r.err +. ulp_mul l r ;;

let err_div l r =
    let lup = mag_lg l.int in
    let rup = mag_lg r.int in
    ((rup *. l.err -. lup *. r.err) /. (rup *. rup +. rup *. r.err)) +.
    ulp_div l r ;;

(* eterm operations *)
let eadd le re = 
    match le, re with
    | Eterm l,  Eterm r -> Eterm { int = intr_add l.int r.int ; err = err_add l r }
    | _, _ -> Bot ;;
    
let esub le re = 
    match le, re with
    | Eterm l, Eterm r -> Eterm { int = intr_sub l.int r.int ; err = err_sub l r }
    | _, _ -> Bot ;;

let emul le re = 
    match le, re with
    | Eterm l, Eterm r -> Eterm { int = intr_mul l.int r.int ; err = err_mul l r }
    | _, _ -> Bot ;;

let ediv le re = 
    match le, re with
    | Eterm l, Eterm r -> Eterm { int = intr_div l.int r.int ; err = err_div l r }
    | _, _ -> Bot ;;

(* [[A]] : aaexp -> eterm *)
let rec asem_aexp exp m =
    match exp with
    | AVal e      -> (e, Const)
    | AVar n      -> (m n, Id n)
    | AAdd (l, r) -> (ediv (fst (asem_aexp l m)) (fst (asem_aexp r m)), Const)
    | ASub (l, r) -> (esub (fst (asem_aexp l m)) (fst (asem_aexp r m)), Const)
    | AMul (l, r) -> (emul (fst (asem_aexp l m)) (fst (asem_aexp r m)), Const)
    | ADiv (l, r) -> (ediv (fst (asem_aexp l m)) (fst (asem_aexp r m)), Const) ;;

(* abstract boolean operators *)
(* (eterm * Id) * (eterm * Id) -> (eterm * Id) * (eterm * Id) *)
let alt left right =
    let (ltrm, lid) = left in
    let (rtrm, rid) = right in
    match ltrm, rtrm with
    | Eterm l, Eterm r ->
        let { int = { l = ll ; u = lu } ; err = le} = l in 
        let { int = { l = rl ; u = ru } ; err = re} = r in 
        if ll > ru then 
            ((Bot, lid), (Bot, rid)) 
        else if (rl <= ll) && (ll <= ru) && (ru <= lu) then 
            ((eterm_of ll ru re, lid), (eterm_of ll ru re, rid))
        else if (ll <= rl) && (rl <= ru) && (ru <= lu) then
            ((eterm_of ll ru le, lid), (rtrm, rid))
        else if (rl <= ll) && (ll <= lu) && (lu <= ru) then
            ((ltrm, lid), (eterm_of ll ru re, rid))
        else ((ltrm, lid), (rtrm, rid))
    | _, _ -> ((Bot, lid), (Bot, rid)) ;;

(* [[B]] : amem -> amem *)
let asem_bexp exp m =
    match exp with
    | ALt (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = alt (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r m)
    | ALe (l, r) -> 
    | AEq (l, r) ->
    | ANe (l, r) ->
    | AGe (l, r) ->
    | AGt (l, r) ->

(*
(* [[S]] : astmt -> amem -> amem *)
let rec asem_stmt exp =
*)

(* Testing *)
let test = CCol (CAsgn ("x", CVal 7.2),
                 CIf (CLt (CVar "x", CVal 12.2),
                      CAsgn ("x", CAdd (CVar "x", CVal 5.7)),
                      CAsgn ("x", CMul (CVal 3.1, CVar "x")))) ;;

let abst_test = abst_stmt test ;;
let () = printf "\n\n%s\n\n%s\n" (str_cstmt test) (str_astmt abst_test)

(*
let x = max_flt [1.1; 4.4; 2.2; 3.3] ;;
let y = min_flt [2.3; 1.1; 4.4; 2.2; 3.3] ;;

let () = printf "\n\n%f\n" y 
*)
