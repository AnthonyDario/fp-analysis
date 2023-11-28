open Format
open Interp
open Printing
open Tree

(* Testing *)
(* ---------------------- *)
let runtest exp amem =
    let aexp = abst_stmt exp in
    printf "\n\n%s\n" (str_cstmt exp) ;
    printf "\n%s\n" (str_astmt aexp) ;
    printf "\n%s\n" (str_amem (abst_interp aexp amem)) ;
    printf "------------------\n" ;;

let test = CCol (CAsgn ("x", CVal 7.2),
                 CIf (CLt (CVar "x", CVal 12.2),
                      CAsgn ("x", CAdd (CVar "x", CVal 5.7)),
                      CAsgn ("x", CMul (CVal 3.1, CVar "x")))) ;;

(* Testing with parameters *)
let amem_init = 
    amem_update (Id "x") 
                (Eterm { int = { l = 10. ; u = 14. } ; err = 0. }) 
                amem_bot ;;

let test2 = CIf (CGt (CVar "x", CVal 12.2),
                 CAsgn ("x", CAdd (CVar "x", CVal 5.7)),
                 CAsgn ("x", CMul (CVal 3.1, CVar "x"))) ;;

(* Testing widening *)
let test3 = CFor (CAsgn ("i", CVal 0.),
                  CLt (CVar "i", CVal 10.),
                  CAsgn ("i", CAdd (CVar "i", CVal 1.)),
                  CAsgn ("x", CAdd (CVar "x", CVal 1.))) ;;

let runtests =
    runtest test amem_bot ;
    runtest test2 amem_init ;
    runtest test3 amem_init

