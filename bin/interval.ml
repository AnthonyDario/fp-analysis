open Float
open List

open Round
open Util

(* Interval definition *)
type interval = {
    l : float;
    u : float
} ;;

let intr_bot = { l = 1. ; u = -1.} ;;
(* inclusive *)
let intr_of l u = if l > u then intr_bot else {l = l ; u = u} ;;
(* exclusive *)
let intr_of_exc l u = if l >= u then intr_bot else {l = l ; u = u} ;;

(* Useful utils *)
let contains i v = i.l <= v && i.u >= v ;;
let intr_overlap i1 i2 = 
    i1.l <= i2.l && i1.u >= i2.l ||
    i2.l <= i1.l && i2.u >= i1.l ||
    i1.u >= i2.u && i1.l <= i2.u ||
    i2.u >= i1.u && i2.l <= i1.u ;;

(* Arithmetic operators *)
let intr_add l r = { l = add Down l.l r.l ; u = add Up l.u r.u } ;;
let intr_sub l r = { l = sub Down l.l r.u ; u = sub Up l.u r.l } ;;
let intr_mul l r = 
    { l = min_flt [mul Down l.l r.l ; mul Down l.l r.u ;
                   mul Down l.u r.l ; mul Down l.u r.u] ; 
      u = max_flt [mul Up l.l r.l ; mul Up l.l r.u ; 
                   mul Up l.u r.l ; mul Up l.u r.u] } ;;
let intr_div l r = 
    { l = min_flt [div Down l.l r.l ; div Down l.l r.u ;
                   div Down l.u r.l ; div Down l.u r.u] ; 
      u = max_flt [div Up l.l r.l ; div Up l.l r.u ; 
                   div Up l.u r.l ; div Up l.u r.u] } ;;

(* Largest and smallest constraint by magnitude *)
let mag_lg i = max_flt [(abs i.l) ; (abs i.u)] ;;
let mag_sm i = min_flt [(abs i.l) ; (abs i.u)] ;;

(* Boolean Operators *)
(* Returns the new values of the operands *)
let intr_lt l r = 
    let lu = min_flt [l.u ; r.u -. ulp r.u] in
    let rl = max_flt [l.l +. ulp l.l ; r.l] in
    (intr_of l.l lu, intr_of rl r.u) ;;

let intr_le l r =
    let lu = min_flt [l.u ; r.u] in
    let rl = max_flt [l.l ; r.l] in
    (intr_of l.l lu, intr_of rl r.u) ;;

let intr_gt l r = 
    let ll = max_flt [l.l ; r.l +. ulp r.l] in
    let ru = min_flt [r.u ; l.u -. ulp l.u] in
    (intr_of ll l.u, intr_of r.l ru) ;;

let intr_ge l r = 
    let ll = max_flt [l.l ; r.l] in
    let ru = min_flt [l.u ; r.u] in
    (intr_of ll l.u, intr_of r.l ru) ;;

let intr_eq l r = 
    let new_intr = intr_of (max_flt [l.l ; r.l]) (min_flt [l.u ; r.u]) in
    (new_intr, new_intr) ;;

let intr_neq l r = (l, r) ;;

(* Union *)
(* If these don't overlap we include the middle, perhaps we don't want this? *)
let intr_union i1 i2 = 
    let { l = i1l ; u = i1u } = i1 in
    let { l = i2l ; u = i2u } = i2 in
    { l = min_flt [i1l ; i2l]; u = max_flt [i1u ; i2u] } ;;

(* without i6 i1 
   without [ 2 ; 4 ] [ 1 ; 4 ] -> []
*)

(* Remove i2 from i1, produces a list of intervals *)
let intr_without i1 i2 =
    filter (fun x -> x != intr_bot)
           (if i1.l < i2.l
            then [ intr_of_exc i1.l (min_flt [i2.l ; i1.u]) ; intr_of_exc i2.u i1.u ]
            else [ intr_of_exc (max_flt [i2.u ; i1.l]) i1.u ]) ;;
