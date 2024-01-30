open Float
open List

open Interval
open Util

(* The interval-error terms.  Represents a section of the interval with an
   associated error *)
type segment = {
    int : interval;
    err : float
} ;;

let seg_bot = { int = intr_bot ; err = 0. } ;;
let seg_of l u err = 
    if l > u || err < 0.
    then seg_bot 
    else { int = intr_of l u ; err = err } ;;

let seg_overlap s1 s2 = intr_overlap s1.int s2.int ;;

(* Dealing with error *)
let ulp_add l r = 0.5 *. ulp ((abs l.int.u) +. (abs r.int.u)) ;;
let ulp_sub l r = 0.5 *. ulp ((mag_lg l.int) +. (mag_lg r.int)) ;;
let ulp_mul l r = 
    0.5 *. ulp ((mag_lg l.int) *. (mag_lg r.int)) ;;
let ulp_div l r = 
    0.5 *. ulp ((mag_lg l.int) /. (mag_sm r.int)) ;;

let err_add l r = 
    match l.err, r.err with
    | le, re when not (is_finite le) || not (is_finite re) -> infinity
    | le, re -> le +. re +. ulp_add l r ;;

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

(* Arithmetic operators *)
let seg_add x y = 
    { int = intr_add x.int y.int ; err = err_add x y } ;;

let seg_sub x y = 
    { int = intr_sub x.int y.int ; err = err_sub x y } ;;

let seg_mul x y = 
    { int = intr_mul x.int y.int ; err = err_mul x y } ;;

let seg_div x y = 
    { int = intr_div x.int y.int ; err = err_div x y } ;;

(* Boolean operators *)
(* Return the new values of the operands *)
let seg_lt l r = 
    let (li, ri) = intr_lt l.int r.int in
    (seg_of li.l li.u l.err, seg_of ri.l ri.u r.err) ;;

let seg_le l r = 
    let (li, ri) = intr_le l.int r.int in
    (seg_of li.l li.u l.err, seg_of ri.l ri.u r.err) ;;

let seg_gt l r = 
    let (li, ri) = intr_gt l.int r.int in
    (seg_of li.l li.u l.err, seg_of ri.l ri.u r.err) ;;

let seg_ge l r = 
    let (li, ri) = intr_ge l.int r.int in
    (seg_of li.l li.u l.err, seg_of ri.l ri.u r.err) ;;

let seg_eq l r =
    let (li, ri) = intr_eq l.int r.int in
    (seg_of li.l li.u l.err, seg_of ri.l ri.u r.err) ;;

let seg_neq l r = (l, r) ;;

(* Same as intr without but maintain the error *)
(* Remove seg1 from seg2, produces a list of segments *)
let seg_without seg1 seg2 =
    map (fun i -> seg_of i.l i.u seg1.err) 
        (intr_without seg1.int seg2.int) ;;

(* Union *)
(* This type signature is odd, should probably return an eterm but an import
 * dependency cycle is introduced.  The resulting list has a domain the same
 * size as the union of the two intervals.
 *)
(* seg_union : segment -> segment -> segment list *)
let seg_union (l : segment) (r : segment) : segment list = 
    let (large, small) = if l.err >= r.err then (l, r) else (r, l) in
    let intrs = seg_without small large in
    [large] @ intrs ;;

