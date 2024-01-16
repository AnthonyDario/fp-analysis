open List
open Format

open Interp
open Printing
open Tree
open Eterm
open Interr
open Interval
open Util

(* Testing functions *)
let test b m = if not b then failwith m ;;
let test_eq a1 a2 m = test (a1 = a2) m ;;

let test_in vals lst =
    (fold_left (fun acc i -> acc && exists (fun x -> i = x) lst)
                      true vals) ;;

let test_lst lst vals m = test (test_in vals lst && test_in lst vals ) m ;;
let test_ets et1 et2 m = test_lst (get_segs et1) (get_segs et2) m ;;

(* Interval Testing *)
(* ---------------------- *)
let i1 = intr_of 2. 4. ;;
let i2 = intr_of 4. 8. ;;
let i3 = intr_of 1. 3. ;;
let i4 = intr_of (-5.) 3. ;;
let i5 = intr_of 1. 5. ;;
let i6 = intr_of 3. 4. ;;

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
    test_bool (intr_eq i1 i3) (out, out) "intr_eq test failed" ;;

let intr_neq_test = 
    test_bool (intr_neq i1 i2) (i1, i2) "intr_neq test failed" ;;

let intr_union_test = 
    test_eq (intr_union i1 i2) (intr_of i1.l i2.u) "intr_union test failed" ;
    test_eq (intr_union i5 i1) i5 "intr_union overlap test failed" ;;


let () = 
    printf "%s\n" (fold_left (fun a x -> a ^ (str_interval x)) "" (intr_without i6 i1)) ;;

let intr_without_test =
    test_eq (intr_without i3 i2) [i3] "intr_without failed no-change test" ;
    (* Perhaps we need to offset by ulp here? *)
    test_eq (intr_without i5 i1) [intr_of 1. 2. ; intr_of 4. 5.] 
        "intr_without failed containing test" ;
    test_eq (intr_without i3 i1) [intr_of 1. 2.] 
        "intr_without failed overlap test" ;
    test_eq (intr_without i1 i5) [] 
        "intr_without failed enveloped test" ;
    test_eq (intr_without i6 i1) [] 
        "intr_without failed boundary test" ;;

(* Interr Testing *)
(* ---------------------- *)
let ie1 = interr_of 2. 4. 0.03;;
let ie2 = interr_of 4. 8. 0.101;;
let ie3 = interr_of 1. 3. 0.004;;
let ie4 = interr_of (-5.) 3. 0.0002 ;;
let ie5 = interr_of 1. 5. 0.00202;;

let interr_of_test = 
    test_eq ie1 { int = { l = 2. ; u = 4. }; err = 0.03 } 
        "interr_of failed test" ;
    test_eq (interr_of 3. 2. 0.0001) interr_bot 
        "interr_of did not produce bottom from negative interval" ;
    test_eq (interr_of 1. 2. (-1.)) interr_bot 
        "interr_of did not produce bottom from negative error" ;;

let interr_overlap_test = 
    test (interr_overlap ie1 ie3)
        "interr_overlap did not identifiy overlapping segments" ;
    test (not (interr_overlap ie2 ie4))
        "interr_overlap misidentified unoverlapping segments" ;;
 
let ie_op_tests =
    test_eq (ie_add ie1 ie2) (interr_of 6. 12. (err_add ie1 ie2)) 
        "ie_add failed" ;
    test_eq (ie_sub ie1 ie2) (interr_of (-6.) 0. (err_sub ie1 ie2))
        "ie_sub failed" ;
    test_eq (ie_mul ie1 ie2) (interr_of 8. 32. (err_mul ie1 ie2))
        "ie_mul failed" ;
    test_eq (ie_div ie2 ie1) (interr_of 1. 4. (err_div ie2 ie1))
        "ie_div failed" ;;

let ie_lt_test =
    test_bool (ie_lt ie3 ie1) (ie3, ie1) "ie_lt failed no-change test" ;
    test_bool (ie_lt ie1 ie4) 
              (interr_of ie1.int.l (ie4.int.u -. ulp ie4.int.u) ie1.err, 
               interr_of (ie1.int.l +. ulp ie1.int.l) ie4.int.u ie4.err)
              "ie_lt failed boundary test" ;
    test_bool (ie_lt ie5 ie1) 
              (interr_of ie5.int.l (ie1.int.u -. ulp ie1.int.u) ie5.err, ie1) 
              "intr_lt failed overlap test" ;; 

let ie_le_test =
    test_bool (ie_le ie3 ie1) (ie3, ie1) "ie_le failed no-change test" ;
    test_bool (ie_le ie1 ie4) (interr_of ie1.int.l ie4.int.u ie1.err,
                               interr_of ie1.int.l ie4.int.u ie4.err)
              "ie_le failed boundary test" ;
    test_bool (ie_le ie5 ie1) (interr_of ie5.int.l ie1.int.u ie5.err, ie1) 
              "ie_le failed overlap test" ;; 

let ie_gt_test =
    test_bool (ie_gt ie3 ie1) (interr_of (ie1.int.l +. ulp ie1.int.l) ie3.int.u ie3.err,
                               interr_of ie1.int.l (ie3.int.u -. ulp ie3.int.u) ie1.err)
              "ie_gt failed overlap test" ;
    test_bool (ie_gt ie2 ie1) (ie2, ie1) "ie_gt failed no-change test" ;;
    test_bool (ie_gt ie5 ie1) 
              (interr_of (ie1.int.l +. ulp ie1.int.l) ie5.int.u ie5.err, ie1) 
              "ie_gt failed overlap test" ;;

let ie_ge_test =
    test_bool (ie_ge ie3 ie1) 
              (interr_of ie1.int.l ie3.int.u ie3.err,
               interr_of ie1.int.l ie3.int.u ie1.err)
              "ie_ge failed overlap test" ;
    test_bool (ie_ge ie2 ie1) (ie2, ie1) "ie_ge failed no-change test" ;;
    test_bool (ie_ge ie5 ie1) (interr_of ie1.int.l ie5.int.u ie5.err, ie1) 
              "ie_ge failed overlap test" ;;

let ie_eq_test = 
    let out1 = interr_of ie1.int.l ie3.int.u ie1.err in
    let out2 = interr_of ie1.int.l ie3.int.u ie3.err in
    test_bool (ie_eq ie1 ie3) (out1, out2) "ie_eq failed test" ;;

let ie_neq_test = 
    test_bool (ie_neq ie1 ie2) (ie1, ie2) "ie_neq test failed" ;;

let ie_without_test =
    test_lst [ ie3 ] (ie_without ie3 ie2) "ie_without failed no-change test" ;
    (* Perhaps we need to offset by ulp here? *)
    test_lst [ interr_of ie5.int.l ie1.int.l ie5.err ; 
              interr_of ie1.int.u ie5.int.u ie5.err ] (ie_without ie5 ie1) 
        "ie_without failed containing test" ;
    test_lst [ interr_of ie3.int.l ie1.int.l ie3.err ] (ie_without ie3 ie1) 
        "ie_without failed overlap test" ;;

let ie_union_test = 
    test_lst [ie1 ; ie2] (ie_union ie1 ie2) "ie_union failed no-change test" ;
    test_lst (ie1 :: (ie_without ie5 ie1)) (ie_union ie5 ie1) 
        "ie_union overlap test failed" ;;


(* Error Testing *)
let ulp_op_test = 
    test_eq (ulp_add ie1 ie2) (0.5 *. ulp (4. +. 8.))
        "ulp_add failed test" ;
    test_eq (ulp_sub ie1 ie2) (0.5 *. ulp (4. +. 8.))
        "ulp_sub failed test" ;
    test_eq (ulp_mul ie1 ie2) (0.5 *. ulp (4. *. 8.))
        "ulp_mul failed test" ;
    test_eq (ulp_div ie1 ie2) (0.5 *. ulp (4. /. 4.))
        "ulp_div failed test" ;;

(*
let () =
    printf "%20.20f = %20.20f\n" 
        (err_div ie2 ie1)
        ((((4. *. 0.101) -. (8. *. 0.03)) /. ((4. *. 4.) +. (4. *. 0.03))) +. 
         (ulp_div ie2 ie1)) ;
    printf "%B\n" (infinity = infinity) ;;
    printf "%s = %s\n" (Float.to_string (ulp_mul ie1 ie2)) 
                       (Float.to_string (0.5 *. ulp (4. *. 8.)) ;;
*)
                       
(* TODO: Look into potentially negative error here? Probably need an absolute value... *)
let err_tests =
    test_eq (err_add ie1 ie2) (ie1.err +. ie2.err +. (ulp_add ie1 ie2)) 
        "err_add failed test" ;
    test_eq (err_add ie1 (interr_of 1. 2. infinity)) infinity 
        "err_add failed infinity test";
    test_eq (err_sub ie1 ie2) (ie1.err +. ie2.err +. (ulp_sub ie1 ie2))
        "err_sub failed test" ;
    test_eq (err_mul ie1 ie2) 
        ((4. *. 0.101) +. (8. *. 0.03) +. (0.03 *. 0.101) +. 
        (ulp_mul ie1 ie2))
        "err_mul failed test" ;
    test_eq (err_div ie2 ie1)
        ((((4. *. 0.101) -. (8. *. 0.03)) /. ((4. *. 4.) +. (4. *. 0.03))) +. 
        (ulp_div ie2 ie1))
        "err_div failed test" ;;

(* Util Testing *)
(* ---------------------- *)

let xs = [ 1 ; 1 ; 2 ; ] ;;
let ys = [ 2 ; 4 ; 8 ; ] ;;
let out = [ 3 ; 5 ; 9 ; 3 ; 5; 9 ; 4 ; 6 ; 10 ];;
let product_map_test =
    test_lst out (product_map (+) xs ys) "product_map failed test" ;;

let extremes_test test = 
    let lst = [ 5. ; 6. ; 1.4; 2.2 ] in
    test_eq 1.4 (min_flt lst) "min_flt failed test" ;
    test_eq 6. (max_flt lst) "max_flt failed test" ;;

(* Eterm Testing *)
(* ---------------------- *)
let x = Eterm [ interr_of 2. 4. 0.02 ; interr_of 4. 8. 0.01 ] ;;
let y = Eterm [ interr_of 1. 3. 0.001 ; interr_of 3. 6. 0.011 ] ;;

let range_tests = 
    test_eq (range x) (intr_of 2. 8.) "range failed happy path test" ;
    test_eq (range Bot) intr_bot "range failed bot test" ;
    test_eq (range_ie x) (interr_of 2. 8. 0.0) "range_ie failed happy path test" ;
    test_eq (range_ie Bot) interr_bot "range_ie failed bot test" ;;

let get_segs_test =
    test_eq (get_segs x) [ interr_of 2. 4. 0.02 ; interr_of 4. 8. 0.01 ] 
        "get_segs happy path failed" ;
    test_eq (get_segs Bot) [] 
        "get_segs bot test failed" ;;

let append_test = 
    let out = Eterm [ interr_of 2. 4. 0.02 ; interr_of 4. 8. 0.01 ; 
                      interr_of 1. 3. 0.001 ; interr_of 3. 6. 0.011 ] in
    test_eq (eterm_append x (get_segs y)) out "eterm_append test failed" ;;


let merge_test =
    let test = eterm_append x (get_segs y) in 
    let happy_test = Eterm [ interr_of 0. 1. 0.1 ; interr_of 1. 2. 0.2 ] in
    test_lst (get_segs (merge happy_test))
            (get_segs happy_test)
            "merge failed no-change test" ;
    test_lst (get_segs (merge test))
            ([ interr_of 1. 2. 0.001 ; interr_of 2. 4. 0.02 ; 
               interr_of 4. 6. 0.011 ; interr_of 6. 8. 0.01 ])
            "merge failed test" ;;

let eterm_arith_tests = 
    let x1, x2 = (interr_of 2. 4. 0.02, interr_of 4. 8. 0.01) in
    let y1, y2 = (interr_of 1. 3. 0.001, interr_of 4. 6. 0.011) in
    test_ets (eadd x y) 
        (merge (Eterm [interr_of 3. 5. (err_add x1 y1) ;
                       interr_of 5. 10. (err_add x1 y2) ;
                       interr_of 5. 12. (err_add x2 y1) ;
                       interr_of 7. 14. (err_add x2 y2)]))
        "eadd failed test" ;
    test_ets (esub x y) 
        (merge (Eterm [interr_of (-1.) 3. (err_sub x1 y1) ;
                       interr_of (-4.) 1. (err_sub x1 y2) ;
                       interr_of 1. 7. (err_sub x2 y1) ;
                       interr_of (-2.) 5. (err_sub x2 y2)]))
        "esub failed test" ;
    test_ets (emul x y) 
        (merge (Eterm [interr_of 2. 12. (err_mul x1 y1) ;
                       interr_of 6. 24. (err_mul x1 y2) ;
                       interr_of 4. 24. (err_mul x2 y1) ;
                       interr_of 12. 48. (err_mul x2 y2)]))
        "emul failed test" ;
    test_ets (ediv x y) 
        (merge (Eterm [interr_of (2. /. 3.) 4. (err_div x1 y1) ;
                       interr_of (2. /. 6.) (4. /. 3.) (err_div x1 y2) ;
                       interr_of (4. /. 3.) 8. (err_div x2 y1) ;
                       interr_of (4. /. 6.) (8. /. 3.) (err_div x2 y2)]))
        "ediv failed test" ;;

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
                (Eterm [{int = {l = 10. ; u = 14. } ; err = 0. }]) 
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
