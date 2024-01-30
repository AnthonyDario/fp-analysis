open List
open Format

open Interp
open Printing
open Tree
open Eterm
open Segment
open Interval
open Util
open Parse

(* Testing functions *)
let test b m = if not b then failwith m ;;
let test_eq a1 a2 m = test (a1 = a2) m ;;

let test_in vals lst =
    (fold_left (fun acc i -> acc && exists (fun x -> i = x) lst)
                      true vals) ;;
                      
let test_tuple input output tst m = 
    let (in1, in2) = input in
    let (out1, out2) = output in
    tst in1 out1 (m ^ " on first operand") ;
    tst in2 out2 (m ^ " on second operand") ;;

let test_bool input output m = test_tuple input output test_eq m ;;

let equal_lsts lst vals = (test_in vals lst && test_in lst vals) ;;
let test_lst lst vals m = test (equal_lsts lst vals) m ;;
let test_tup_lst ins outs = test_tuple ins outs test_lst ;;
let test_ets et1 et2 m = test_lst (get_segs et1) (get_segs et2) m ;;
let test_ets_b input output m = test_tuple input output test_ets m ;;

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
         "intr_overlap identifies non-overlapping intervals" ; 
    test (intr_overlap i1 i5) 
        "intr_overlap doesn't identify containing overlap" ;;

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

(* Segment Testing *)
(* ---------------------- *)
let s1 = seg_of 2. 4. 0.03;;
let s2 = seg_of 4. 8. 0.101;;
let s3 = seg_of 1. 3. 0.004;;
let s4 = seg_of (-5.) 3. 0.0002 ;;
let s5 = seg_of 1. 5. 0.00202;;

let seg_of_test = 
    test_eq s1 { int = { l = 2. ; u = 4. }; err = 0.03 } 
        "seg_of failed test" ;
    test_eq (seg_of 3. 2. 0.0001) seg_bot 
        "seg_of did not produce bottom from negative interval" ;
    test_eq (seg_of 1. 2. (-1.)) seg_bot 
        "seg_of did not produce bottom from negative error" ;;

let seg_overlap_test = 
    test (seg_overlap s1 s3)
        "seg_overlap did not identifiy overlapping segments" ;
    test (not (seg_overlap s2 s4))
        "seg_overlap misidentified unoverlapping segments" ;
    test (seg_overlap s2 (seg_of 3. 12. 0.012)) 
        "seg_overlap misidentified containing overlap" ;;
 
let seg_op_tests =
    test_eq (seg_add s1 s2) (seg_of 6. 12. (err_add s1 s2)) 
        "seg_add failed" ;
    test_eq (seg_sub s1 s2) (seg_of (-6.) 0. (err_sub s1 s2))
        "seg_sub failed" ;
    test_eq (seg_mul s1 s2) (seg_of 8. 32. (err_mul s1 s2))
        "seg_mul failed" ;
    test_eq (seg_div s2 s1) (seg_of 1. 4. (err_div s2 s1))
        "seg_div failed" ;;

let seg_lt_test =
    test_bool (seg_lt s3 s1) (s3, s1) "seg_lt failed no-change test" ;
    test_bool (seg_lt s1 s4) 
              (seg_of s1.int.l (s4.int.u -. ulp s4.int.u) s1.err, 
               seg_of (s1.int.l +. ulp s1.int.l) s4.int.u s4.err)
              "seg_lt failed boundary test" ;
    test_bool (seg_lt s5 s1) 
              (seg_of s5.int.l (s1.int.u -. ulp s1.int.u) s5.err, s1) 
              "intr_lt failed overlap test" ;; 

let seg_le_test =
    test_bool (seg_le s3 s1) (s3, s1) "seg_le failed no-change test" ;
    test_bool (seg_le s1 s4) (seg_of s1.int.l s4.int.u s1.err,
                               seg_of s1.int.l s4.int.u s4.err)
              "seg_le failed boundary test" ;
    test_bool (seg_le s5 s1) (seg_of s5.int.l s1.int.u s5.err, s1) 
              "seg_le failed overlap test" ;; 

let seg_gt_test =
    test_bool (seg_gt s3 s1) (seg_of (s1.int.l +. ulp s1.int.l) s3.int.u s3.err,
                               seg_of s1.int.l (s3.int.u -. ulp s3.int.u) s1.err)
              "range_seg failed overlap test" ;
    test_bool (seg_gt s2 s1) (s2, s1) "seg_gt failed no-change test" ;;
    test_bool (seg_gt s5 s1) 
              (seg_of (s1.int.l +. ulp s1.int.l) s5.int.u s5.err, s1) 
              "seg_gt failed overlap test" ;;

let seg_ge_test =
    test_bool (seg_ge s3 s1) 
              (seg_of s1.int.l s3.int.u s3.err,
               seg_of s1.int.l s3.int.u s1.err)
              "seg_ge failed overlap test" ;
    test_bool (seg_ge s2 s1) (s2, s1) "seg_ge failed no-change test" ;;
    test_bool (seg_ge s5 s1) (seg_of s1.int.l s5.int.u s5.err, s1) 
              "seg_ge failed overlap test" ;;

let seg_eq_test = 
    let out1 = seg_of s1.int.l s3.int.u s1.err in
    let out2 = seg_of s1.int.l s3.int.u s3.err in
    test_bool (seg_eq s1 s3) (out1, out2) "seg_eq failed test" ;;

let seg_neq_test = 
    test_bool (seg_neq s1 s2) (s1, s2) "seg_neq test failed" ;;

let seg_without_test =
    test_lst [ s3 ] (seg_without s3 s2) "seg_without failed no-change test" ;
    (* Perhaps we need to offset by ulp here? *)
    test_lst [ seg_of s5.int.l s1.int.l s5.err ; 
              seg_of s1.int.u s5.int.u s5.err ] (seg_without s5 s1) 
        "seg_without failed containing test" ;
    test_lst [ seg_of s3.int.l s1.int.l s3.err ] (seg_without s3 s1) 
        "seg_without failed overlap test" ;;

let seg_union_test = 
    test_lst [s1 ; s2] (seg_union s1 s2) "seg_union failed no-change test" ;
    test_lst (s1 :: (seg_without s5 s1)) (seg_union s5 s1) 
        "seg_union overlap test failed" ;;


(* Error Testing *)
let ulp_op_test = 
    test_eq (ulp_add s1 s2) (0.5 *. ulp (4. +. 8.))
        "ulp_add failed test" ;
    test_eq (ulp_sub s1 s2) (0.5 *. ulp (4. +. 8.))
        "ulp_sub failed test" ;
    test_eq (ulp_mul s1 s2) (0.5 *. ulp (4. *. 8.))
        "ulp_mul failed test" ;
    test_eq (ulp_div s1 s2) (0.5 *. ulp (4. /. 4.))
        "ulp_div failed test" ;;

(* TODO: Look into potentially negative error here? Probably need an absolute value... *)
let err_tests =
    test_eq (err_add s1 s2) (s1.err +. s2.err +. (ulp_add s1 s2)) 
        "err_add failed test" ;
    test_eq (err_add s1 (seg_of 1. 2. infinity)) infinity 
        "err_add failed infinity test";
    test_eq (err_sub s1 s2) (s1.err +. s2.err +. (ulp_sub s1 s2))
        "err_sub failed test" ;
    test_eq (err_mul s1 s2) 
        ((4. *. 0.101) +. (8. *. 0.03) +. (0.03 *. 0.101) +. 
        (ulp_mul s1 s2))
        "err_mul failed test" ;
    test_eq (err_div s2 s1)
        ((((4. *. 0.101) -. (8. *. 0.03)) /. ((4. *. 4.) +. (4. *. 0.03))) +. 
        (ulp_div s2 s1))
        "err_div failed test" ;;

(* Util Testing *)
(* ---------------------- *)

let xs = [ 1 ; 1 ; 2 ; ] ;;
let ys = [ 2 ; 4 ; 8 ; ] ;;
let out = [ 3 ; 5 ; 9 ; 3 ; 5; 9 ; 4 ; 6 ; 10 ];;
let product_map_test =
    test_lst out (product_map (+) xs ys) "product_map failed test" ;;

let extremes_test = 
    let lst = [ 5. ; 6. ; 1.4; 2.2 ] in
    test_eq 1.4 (min_flt lst) "min_flt failed test" ;
    test_eq 6. (max_flt lst) "max_flt failed test" ;;

let last_test =
    test_eq 1 (last [2 ; 1]) "last failed test" ;;

let remove_last_test = 
    test_eq [1 ; 2 ; 3 ; 4] 
            (remove_last [1; 2; 3; 4; 5]) 
            "remove_last failed test" ;;

(* Eterm Testing *)
(* ---------------------- *)
let x = Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ] ;;
let y = Eterm [ seg_of 1. 3. 0.001 ; seg_of 3. 6. 0.011 ] ;;
let z = Eterm [ seg_of 1. 5. 0.013 ; seg_of 5. 10. 0.017 ] ;;
let t2 = Eterm [ seg_of 1. 2. 0.001 ; seg_of 2. 4. 0.02 ] ;;

let range_tests = 
    test_eq (range x) (intr_of 2. 8.) "range failed happy path test" ;
    test_eq (range Bot) intr_bot "range failed bot test" ;
    test_eq (range_seg x) (seg_of 2. 8. 0.0) "range_seg failed happy path test" ;
    test_eq (range_seg Bot) seg_bot "range_seg failed bot test" ;;

let get_segs_test =
    test_eq (get_segs x) [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ] 
        "get_segs happy path failed" ;
    test_eq (get_segs Bot) [] 
        "get_segs bot test failed" ;;

let append_test = 
    let out = Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ; 
                      seg_of 1. 3. 0.001 ; seg_of 3. 6. 0.011 ] in
    test_eq (eterm_append x (get_segs y)) out "eterm_append test failed" ;;

let merge_test =
    let test = eterm_append x (get_segs y) in 
    let happy_test = Eterm [ seg_of 0. 1. 0.1 ; seg_of 1. 2. 0.2 ] in
    test_lst (get_segs (merge happy_test))
            (get_segs happy_test)
            "merge failed no-change test" ;
    test_lst (get_segs (merge test))
            ([ seg_of 1. 2. 0.001 ; seg_of 2. 4. 0.02 ; 
               seg_of 4. 6. 0.011 ; seg_of 6. 8. 0.01 ])
            "merge failed test" ;;

let eterm_arith_tests = 
    let x1, x2 = (seg_of 2. 4. 0.02, seg_of 4. 8. 0.01) in
    let y1, y2 = (seg_of 1. 3. 0.001, seg_of 4. 6. 0.011) in
    test_ets (eadd x y) 
        (merge (Eterm [seg_of 3. 5. (err_add x1 y1) ;
                       seg_of 5. 10. (err_add x1 y2) ;
                       seg_of 5. 12. (err_add x2 y1) ;
                       seg_of 7. 14. (err_add x2 y2)]))
        "eadd failed test" ;
    test_ets (esub x y) 
        (merge (Eterm [seg_of (-1.) 3. (err_sub x1 y1) ;
                       seg_of (-4.) 1. (err_sub x1 y2) ;
                       seg_of 1. 7. (err_sub x2 y1) ;
                       seg_of (-2.) 5. (err_sub x2 y2)]))
        "esub failed test" ;
    test_ets (emul x y) 
        (merge (Eterm [seg_of 2. 12. (err_mul x1 y1) ;
                       seg_of 6. 24. (err_mul x1 y2) ;
                       seg_of 4. 24. (err_mul x2 y1) ;
                       seg_of 12. 48. (err_mul x2 y2)]))
        "emul failed test" ;
    test_ets (ediv x y) 
        (merge (Eterm [seg_of (2. /. 3.) 4. (err_div x1 y1) ;
                       seg_of (2. /. 6.) (4. /. 3.) (err_div x1 y2) ;
                       seg_of (4. /. 3.) 8. (err_div x2 y1) ;
                       seg_of (4. /. 6.) (8. /. 3.) (err_div x2 y2)]))
        "ediv failed test" ;;

let eterm_lt_test = 
    test_ets_b (eterm_lt x y) 
               (Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. (6. -. ulp 6.) 0.01 ],
                Eterm [ seg_of (2. +. ulp 2.) 3. 0.001 ; seg_of 3. 6. 0.011 ])
               "eterm_lt failed remove top test" ;
    test_ets_b (eterm_lt y x) 
               (Eterm [ seg_of 1. 3. 0.001 ; seg_of 3. 6. 0.011 ],
                Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ])
               "eterm_lt failed no change test" ;
    test_ets_b (eterm_lt z x) 
               (Eterm [ seg_of 1. 5. 0.013 ; seg_of 5. (8. -. ulp 8.) 0.017 ],
                Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ])
               "eterm_lt failed contain test" ;;

let eterm_le_test = 
    test_ets_b (eterm_le x y) 
               (Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 6. 0.01 ],
                Eterm [ seg_of 2. 3. 0.001 ; seg_of 3. 6. 0.011 ])
               "eterm_le failed remove top test" ;
    test_ets_b (eterm_le y x) 
               (Eterm [ seg_of 1. 3. 0.001 ; seg_of 3. 6. 0.011 ],
                Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ])
               "eterm_le failed no change test" ;
    test_ets_b (eterm_le z x) 
               (Eterm [ seg_of 1. 5. 0.013 ; seg_of 5. 8. 0.017 ],
                Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ])
               "eterm_le failed contain test" ;;

let eterm_gt_test = 
    test_ets_b (eterm_gt x y) 
               (Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ],
                Eterm [ seg_of 1. 3. 0.001 ; seg_of 3. 6. 0.011 ])
               "eterm_gt failed no-change top test" ;
    test_ets_b (eterm_gt y x) 
               (Eterm [ seg_of (2. +. ulp 2.) 3. 0.001 ; seg_of 3. 6. 0.011 ],
                Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. (6. -. ulp 6.) 0.01 ])
               "eterm_gt failed remove bottom test" ;
    test_ets_b (eterm_gt z x) 
               (Eterm [ seg_of (2. +. ulp 2.) 5. 0.013 ; seg_of 5. 10. 0.017 ],
                Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ])
               "eterm_gt failed contain test" ;;

let eterm_ge_test = 
    test_ets_b (eterm_ge x y) 
               (Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ],
                Eterm [ seg_of 1. 3. 0.001 ; seg_of 3. 6. 0.011 ])
               "eterm_ge failed no-change top test" ;
    test_ets_b (eterm_ge y x) 
               (Eterm [ seg_of 2. 3. 0.001 ; seg_of 3. 6. 0.011 ],
                Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 6. 0.01 ])
               "eterm_ge failed remove bottom test" ;
    test_ets_b (eterm_ge z x) 
               (Eterm [ seg_of 2. 5. 0.013 ; seg_of 5. 10. 0.017 ],
                Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ])
               "eterm_ge failed contain test" ;;

let eterm_eq_test = 
    test_ets_b (eterm_eq x y) 
               (Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 6. 0.01 ],
                Eterm [ seg_of 2. 3. 0.001 ; seg_of 3. 6. 0.011 ]) 
               "eterm_eq failed overlap test" ;
    test_ets_b (eterm_eq x z)
               (Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ],
                Eterm [ seg_of 2. 5. 0.013 ; seg_of 5. 8. 0.017 ]) 
               "eterm_eq failed contains test" ;;
    
let eterm_neq_test = test_ets_b (eterm_neq x y) (x, y) "eterm_neq failed test" ;;

let partition_overlap_test = 
    test_tup_lst (partition_overlap x (seg_of 5. 9. 0.12))
                 ([seg_of 4. 8. 0.01], [seg_of 2. 4. 0.02])
                 "partition_overlap failed overlap higher segment test" ;
    test_tup_lst (partition_overlap x (seg_of 2. 3. 0.12))
                 ([seg_of 2. 4. 0.02], [seg_of 4. 8. 0.01])
                 "partition_overlap failed overlap lower segment test" ;
    test_tup_lst (partition_overlap x (seg_of 9. 12. 0.12))
                 ([], get_segs x)
                 "partition_overlap failed no-overlap test" ;
    test_tup_lst (partition_overlap x (seg_of 3. 12. 0.12))
                 (get_segs x, [])
                 "partition_overlap failed multiple overlap test" ;
    test_tup_lst (partition_overlap t2 (seg_of 3. 6. 0.11))
                 ([seg_of 2. 4. 0.02], [seg_of 1. 2. 0.001])
                 "partition_overlap failed ... test" ;;

let eterm_seg_union_test = 
    test_ets (eterm_seg_union x (seg_of 4. 7. 0.001)) x
        "eterm_seg_union failed no-change test" ;
    test_ets (eterm_seg_union x (seg_of 4. 7. 0.03))
             (Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 7. 0.03 ; seg_of 7. 8. 0.01 ])
        "eterm_seg_union failed upper-contains test" ;
    test_ets (eterm_seg_union x (seg_of 3. 6. 0.015))
             (Eterm [ seg_of 2. 4. 0.02 ; seg_of 4. 6. 0.015 ; seg_of 6. 8. 0.01 ])
        "eterm_seg_union failed middle union test" ;
    test_ets (eterm_seg_union t2 (seg_of 3. 6. 0.011))
             (Eterm [ seg_of 1. 2. 0.001 ; seg_of 2. 4. 0.02 ; seg_of 4. 6. 0.011])
        "eterm_seg_union failed ... test" ;;


let eterm_union_test =
    test_ets (eterm_union x y)
             (Eterm [ seg_of 1. 2. 0.001 ; seg_of 2. 4. 0.02 ;
                      seg_of 4. 6. 0.011 ; seg_of 6. 8. 0.01 ])
        "eterm_union failed test" ;;

(* Parser Testing *)

let test1 = 
    CCol (
        CCol (
            CAsgn ("x", CVal (CFloat 12.1)),
            CIf (CGe (CVar ("x", FloatTyp), CVal (CInt 12)),
                 CAsgn ("x", CAdd (CVar ("x", FloatTyp), CVal (CFloat 5.7))),
                 CAsgn ("x", CMul (CVal (CFloat 3.1), CVar ("x", FloatTyp))))),
        CRet (CVar ("x", FloatTyp)))
    ;;

let test2 = 
    CCol (
        CCol (
            CAsgn ("x", CVal (CFloat 2.4)),
            CFor (CAsgn ("i", CVal (CInt 0)), 
                  CLt (CVar ("i", IntTyp), CVal (CInt 10)), 
                  CAsgn ("i", CAdd ((CVar ("i", IntTyp) , CVal (CInt 1)))),
                  CAsgn ("x", CAdd ((CVar ("x", FloatTyp), CVal (CFloat 2.1)))))),
        CRet (CVar ("x", FloatTyp)))
    ;;

let parse_test = 
    let t1 = (parse_file "c/test.c") in 
    let t2 = (parse_file "c/test2.c") in 
    test_eq (transform t1 "main") test1 "Parser failed test1" ;
    test_eq (transform t2 "main") test2 "Parser failed test2"  ;;
(* This is functionally the same as test2.  The difference is if the
   initialization statement of the forloop is inside the loop or just before it.
   Really just a presentation problem that seems to be intrinsic to CIL. *)
(*
let test3 = 
    CCol (
        CCol (
            CCol (CAsgn ("x", CVal (CFloat 2.4)),
                  CAsgn ("i", CVal (CInt 0))),
            CFor (CAsgn ("i", CVal (CInt 0)), 
                  CLt (CVar ("i", IntTyp), CVal (CInt 10)), 
                  CAsgn ("i", CAdd ((CVar ("i", IntTyp) , CVal (CInt 1)))),
                  CAsgn ("x", CAdd ((CVar ("x", FloatTyp), CVal (CFloat 2.1)))))),
        CRet (CVar ("x", FloatTyp)))
    ;;
*)

(* Interpreter Testing *)
(* ---------------------- *)
let runtest exp amem =
    let aexp = abst_stmt exp in
    printf "\n\n%s\n" (str_amem amem) ;
    printf "\n%s\n" (str_cstmt exp) ;
    printf "\n%s\n" (str_astmt aexp) ;
    printf "\n%s\n" (str_amem (abst_interp aexp amem)) ;
    printf "------------------\n" ;;

let test = CCol (CAsgn ("x", CVal (CFloat 7.2)),
                 CIf (CLt (CVar ("x", FloatTyp), CVal (CFloat 12.2)),
                      CAsgn ("x", CAdd (CVar ("x", FloatTyp), CVal (CFloat 5.7))),
                      CAsgn ("x", CMul (CVal (CFloat 3.1), CVar ("x", FloatTyp))))) ;;

(* Testing with parameters *)
let amem_init = 
    amem_update (Id "x") 
                (AFloat (Eterm [{int = {l = 10. ; u = 14. } ; err = 0. }]))
                amem_bot ;;

let test2 = CIf (CGt (CVar ("x", FloatTyp), CVal (CFloat 12.2)),
                 CAsgn ("x", CAdd (CVar ("x", FloatTyp), CVal (CFloat 5.7))),
                 CAsgn ("x", CMul (CVal (CFloat 3.1), CVar ("x", FloatTyp)))) ;;

(* Testing widening *)
let test3 = CFor (CAsgn ("i", CVal (CInt 9)),
                  CLt (CVar ("i", IntTyp), CVal (CInt 10)),
                  CAsgn ("i", CAdd (CVar ("i", IntTyp), CVal (CInt 1))),
                  CAsgn ("x", CAdd (CVar ("x", FloatTyp), CVal (CInt 1)))) ;;

let runtests () =
    runtest test amem_bot ;
    runtest test2 amem_init ; 
    runtest test3 amem_init
