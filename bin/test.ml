open List
open Format

open Interp
open Printing
open Tree
open Eterm
open Interr
open Interval
open Util

let test b m = if not b then failwith m ;;
let test_eq a1 a2 m = test (a1 = a2) m ;;

(* Interval Testing *)
(* ---------------------- *)
let i1 = intr_of 2. 4. ;;
let i2 = intr_of 4. 8. ;;
let i3 = intr_of 1. 3. ;;
let i4 = intr_of (-5.) 3. ;;
let i5 = intr_of 1. 5. ;;

let intr_of_test =
    test_eq i1 { l = 2. ; u = 4. }
         "intr_of doesn't construct correct interval" ;
    test_eq (intr_of 2. 1.) intr_bot
         "intr_of doesn't default to bottom" ;;

let intr_contains_test =
    test (contains i1 2.) "contains doesn't capture lower bound" ;
    test (contains i1 3.) "contains doesn't capture inner value" ;
    test (contains i1 4.) "contains doesn't capture upper bound" ;
    test (not (contains i1 5.)) "contains returns true for uncontained value" ;;

let intr_overlap_test =
    test (intr_overlap i1 i3) 
         "intr_overlap doesn't identify overlapping intervals" ;
    test (intr_overlap i1 i2)
         "intr_overlap doesn't identify intervals it same boundary" ;
    test (not (intr_overlap i2 i3))
         "intr_overlap identifies non-overlapping intervals" ;; 

let intr_ops_test =
    test_eq (intr_add i1 i2) (intr_of 6. 12.) "intr_add failed" ;
    test_eq (intr_sub i1 i2) (intr_of (-6.) 0.) "intr_sub failed" ;
    test_eq (intr_mul i1 i2) (intr_of 8. 32.) "intr_mul failed" ;
    test_eq (intr_div i2 i1) (intr_of 1. 4.) "intr_div failed" ;;

let intr_mags_test =
    test_eq (mag_lg i1) 4. "mag_lg failed" ;
    test_eq (mag_lg i4) 5. "mag_lg failed with negative numbers" ;
    test_eq (mag_sm i1) 2. "mag_sm failed" ;
    test_eq (mag_sm i4) 3. "mag_sm failed with negative numbers" ;;

let test_bool input output m = 
    let (in1, in2) = input in
    let (out1, out2) = output in
    test_eq in1 out1 (m ^ " on first operand") ;
    test_eq in2 out2 (m ^ " on second operand") ;;

let intr_lt_test =
    test_bool (intr_lt i3 i1) (i3, i1) "intr_lt failed no-change test" ;
    test_bool (intr_lt i1 i4) (intr_of i1.l (i4.u -. ulp i4.u), 
                               intr_of (i1.l +. ulp i1.l) i4.u)
              "intr_lt failed boundary test" ;
    test_bool (intr_lt i5 i1) (intr_of i5.l (i1.u -. ulp i1.u), i1) 
              "intr_lt failed overlap test" ;; 

let intr_le_test =
    test_bool (intr_le i3 i1) (i3, i1) "intr_le failed no-change test" ;
    test_bool (intr_le i1 i4) (intr_of i1.l i4.u, intr_of i1.l i4.u)
              "intr_le failed boundary test" ;
    test_bool (intr_le i5 i1) (intr_of i5.l i1.u, i1) 
              "intr_le failed overlap test" ;; 

let intr_gt_test =
    test_bool (intr_gt i3 i1) (intr_of (i1.l +. ulp i1.l) i3.u,
                               intr_of i1.l (i3.u -. ulp i3.u))
              "intr_gt failed overlap test" ;
    test_bool (intr_gt i2 i1) (i2, i1) "intr_gt failed no-change test" ;;
    test_bool (intr_gt i5 i1) (intr_of (i1.l +. ulp i1.l) i5.u, i1) 
              "intr_gt failed overlap test" ;;

let intr_ge_test =
    test_bool (intr_ge i3 i1) (intr_of i1.l i3.u, intr_of i1.l i3.u)
              "intr_ge failed overlap test" ;
    test_bool (intr_ge i2 i1) (i2, i1) "intr_ge failed no-change test" ;;
    test_bool (intr_ge i5 i1) (intr_of i1.l i5.u, i1) 
              "intr_ge failed overlap test" ;;

let intr_eq_test = 
    let out = intr_of i1.l i3.u in
    test_bool (intr_eq i1 i3) (out, out) ;;

let intr_neq_test = 
    test_bool (intr_neq i1 i2) (i1, i2) "intr_neq test failed" ;;

let intr_union_test = 
    test_eq (intr_union i1 i2) (intr_of i1.l i2.u) "intr_union test failed" ;
    test_eq (intr_union i5 i1) i5 "intr_union overlap test failed" ;;

let intr_without_test =
    test_eq (intr_without i3 i2) [i3] "intr_without failed no-change test" ;
    (* Perhaps we need to offset by ulp here? *)
    test_eq (intr_without i5 i1) [intr_of 1. 2. ; intr_of 4. 5.] 
        "intr_without failed containing test" ;
    test_eq (intr_without i3 i1) [intr_of 1. 2.] ;;

(* Interpreter Testing *)
(* ---------------------- *)
let runtest exp amem =
    let aexp = abst_stmt exp in
    printf "\n\n%s\n" (str_amem amem) ;
    printf "\n%s\n" (str_cstmt exp) ;
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
                (Eterm []) 
                amem_bot ;;

let test2 = CIf (CGt (CVar "x", CVal 12.2),
                 CAsgn ("x", CAdd (CVar "x", CVal 5.7)),
                 CAsgn ("x", CMul (CVal 3.1, CVar "x"))) ;;

(* Testing widening *)
let test3 = CFor (CAsgn ("i", CVal 9.),
                  CLt (CVar "i", CVal 10.),
                  CAsgn ("i", CAdd (CVar "i", CVal 1.)),
                  CAsgn ("x", CAdd (CVar "x", CVal 1.))) ;;

let runtests =
    runtest test amem_bot ;
    runtest test2 amem_init ; 
    runtest test3 amem_init
