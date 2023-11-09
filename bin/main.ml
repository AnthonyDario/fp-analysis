open Float
open Format
open Tree
open Printing

(* Abstraction *)
let ulp f = succ f -. f ;;
let abst_flt f = { int = { u = f ; l = f }; err = ulp f } ;;

let rec abst_aexp exp = 
    match exp with
    | CVal v      -> AVal (abst_flt v)
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

(* Testing utils *)
let test = CCol (CAsgn ("x", CVal 7.2),
                 CIf (CLt (CVar "x", CVal 12.2),
                      CAsgn ("x", CAdd (CVar "x", CVal 5.7)),
                      CAsgn ("x", CMul (CVal 3.1, CVar "x")))) ;;

let abst_test = abst_stmt test ;;

let () = printf "\n\n%s\n\n%s\n" (str_cstmt test) (str_astmt abst_test)
