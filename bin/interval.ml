open Float
open List

open Round
open Util

exception IntervalError of string ;;

(* Interval definitions *)
(* -------------------------- *)

(* Float interval *)
type interval = {
    l : float;
    u : float
} ;;

let intr_bot = { l = 1. ; u = -1.} ;;
(* inclusive *)
let intr_of l u = if l > u then intr_bot else {l = l ; u = u} ;;
(* exclusive *)
let intr_of_exc l u = if l >= u then intr_bot else {l = l ; u = u} ;;

let intr_of_int i = {l = Float.of_int i; u = Float.of_int i} ;;

(* Int interval *)
type iInterval = {
    low : int;
    up : int
}

let iintr_bot = { low = 1 ; up = -1} ;;
let iintr_of l u = if l > u then iintr_bot else {low = l ; up = u} ;;

let intr_to_iintr i = { low = Int.of_float i.l ; up = Int.of_float (i.u +. 0.5) } ;;
let iintr_to_intr i = { l = Float.of_int i.low ; u = Float.of_int i.up } ;;

(* Useful utils *)
(* -------------------------- *)
let contains i v = i.l <= v && i.u >= v ;;
let intr_overlap (i1 : interval) (i2 : interval) : bool = 
    i1.l <= i2.l && i1.u >= i2.l ||
    i2.l <= i1.l && i2.u >= i1.l ||
    i1.u >= i2.u && i1.l <= i2.u ||
    i2.u >= i1.u && i2.l <= i1.u ;;

(* Arithmetic operators *)
(* -------------------------- *)
(* Ints *)
let iintr_add l r = { low = l.low + r.low ; up = l.up + r.up } ;;
let iintr_sub l r = { low = l.low - r.up ; up = l.up + r.low } ;;
let iintr_mul l r = 
    let combos = [l.low * r.low ; l.low * r.up ; l.up * r.low ; l.up * r.up] in 
    { low = min_int combos ; up = max_int combos }
let iintr_div l r = 
    let combos = [l.low / r.low ; l.low / r.up ; l.up / r.low ; l.up / r.up] in 
    { low = min_int combos ; up = max_int combos }

(* Floats *)
let intr_add l r = { l = add Down l.l r.l ; u = add Up l.u r.u } ;;
let intr_sub l r = { l = sub Down l.l r.u ; u = sub Up l.u r.l } ;;
let intr_mul l r = 
    let combos = [mul Down l.l r.l ; mul Down l.l r.u ;
                  mul Down l.u r.l ; mul Down l.u r.u] in
    { l = min_flt combos ; u = max_flt combos } ;;
let intr_div l r = 
    let combos = [div Down l.l r.l ; div Down l.l r.u ;
                  div Down l.u r.l ; div Down l.u r.u] in
    { l = min_flt combos ; u = max_flt combos } ;;

(* Largest and smallest constraint by magnitude *)
let mag_lg i = max_flt [(abs i.l) ; (abs i.u)] ;;
let mag_sm i = min_flt [(abs i.l) ; (abs i.u)] ;;

(* Boolean Operators *)
(* -------------------------- *)
(* Returns the new values of the operands *)
(* Ints *)
let iintr_lt l r = 
    let lu = min_int [l.up ; r.up - 1] in
    let rl = max_int [l.low + 1 ; r.low] in
    (iintr_of l.low lu, iintr_of rl r.up) ;;

let iintr_le l r = 
    let lu = min_int [l.up ; r.up] in
    let rl = max_int [l.low ; r.low] in
    (iintr_of l.low lu, iintr_of rl r.up) ;;

let iintr_gt l r = 
    let ll = max_int [l.low ; r.low + 1] in
    let ru = min_int [r.up ; l.up - 1] in
    (iintr_of ll l.up, iintr_of r.low ru) ;;

let iintr_ge l r = 
    let ll = max_int [l.low ; r.low] in
    let ru = min_int [r.up ; l.up] in
    (iintr_of ll l.up, iintr_of r.low ru) ;;

let iintr_eq l r = 
    let new_iintr = iintr_of (max_int [l.low ; r.low]) (min_int [l.up ; r.up]) in
    (new_iintr, new_iintr) ;;

let iintr_neq l r = (l, r)

(* Floats*)
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
(* -------------------------- *)
(* If these don't overlap we include the middle, perhaps we don't want this? *)

(* Int *)
let iintr_union ii1 ii2 =
    let { low = ii1l ; up = ii1u } = ii1 in
    let { low = ii2l ; up = ii2u } = ii2 in
    { low = min_int [ii1l ; ii2l]; up = max_int [ii1u ; ii2u] } ;;

(* Float *)
let intr_union i1 i2 = 
    let { l = i1l ; u = i1u } = i1 in
    let { l = i2l ; u = i2u } = i2 in
    { l = min_flt [i1l ; i2l]; u = max_flt [i1u ; i2u] } ;;

(* Gets the sections of i1 that don't overlap with i2 *)
let intr_without (i1 : interval) (i2 : interval) : interval list = 
    filter (fun x -> x != intr_bot)
           (if i1.l < i2.l
            then [ intr_of_exc i1.l (min_flt [i2.l ; i1.u]) ; intr_of_exc i2.u i1.u ]
            else [ intr_of_exc (max_flt [i2.u ; i1.l]) i1.u ]) ;;

(* Get the section of i1 that overlap with i2 *)
let intr_with (i1 : interval) (i2 : interval) : interval =
    if i1.l < i2.l
    then intr_of_exc i2.l (min_flt [i1.u ; i2.u])
    else intr_of_exc i1.l (min_flt [i1.u ; i2.u]) ;;

(* First element of return is i1 without any overlap of i2.  Second element is
 * overlapping portion *)
let intr_partition (i1 : interval) (i2 : interval) 
    : (interval list * interval) = 
    (intr_without i1 i2, intr_with i1 i2) ;;

(* Get the intervals which meets the Sterbenz condition for i *)
let rec get_sterbenz_intr (i : interval) : interval = 
    if contains i 0.0 then intr_bot
    else if i.l >= 0. then
        intr_of 
            ((intr_div i (intr_of_int 2)).u)
            ((intr_mul i (intr_of_int 2)).l)
    else if i.u <= 0. then
        intr_of
            ((intr_mul i (intr_of_int 2)).u)
            ((intr_div i (intr_of_int 2)).l)
    else
            raise (IntervalError "missing case when getting sterbenz_intervals") ;;
