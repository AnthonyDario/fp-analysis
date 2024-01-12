open Float
open List

open Interval
open Util

(* The interval-error terms.  Represents a section of the interval with an
   associated error *)
type interr = {
    int : interval;
    err : float
} ;;

let interr_bot = { int = intr_bot ; err = 0. } ;;
let interr_of l u err = 
    if l > u || err < 0.
    then interr_bot 
    else { int = intr_of l u ; err = err } ;;

let interr_overlap ie1 ie2 = intr_overlap ie1.int ie2.int ;;

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
let ie_add x y = 
    { int = intr_add x.int y.int ; err = err_add x y } ;;

let ie_sub x y = 
    { int = intr_sub x.int y.int ; err = err_sub x y } ;;

let ie_mul x y = 
    { int = intr_mul x.int y.int ; err = err_mul x y } ;;

let ie_div x y = 
    { int = intr_div x.int y.int ; err = err_div x y } ;;

(* Boolean operators *)
(* Return the new values of the operands *)
let ie_lt l r = 
    let (li, ri) = intr_lt l.int r.int in
    (interr_of li.l li.u l.err, interr_of ri.l ri.u r.err) ;;

let ie_le l r = 
    let (li, ri) = intr_le l.int r.int in
    (interr_of li.l li.u l.err, interr_of ri.l ri.u r.err) ;;

let ie_gt l r = 
    let (li, ri) = intr_gt l.int r.int in
    (interr_of li.l li.u l.err, interr_of ri.l ri.u r.err) ;;

let ie_ge l r = 
    let (li, ri) = intr_ge l.int r.int in
    (interr_of li.l li.u l.err, interr_of ri.l ri.u r.err) ;;

let ie_eq l r =
    let (li, ri) = intr_eq l.int r.int in
    (interr_of li.l li.u l.err, interr_of ri.l ri.u r.err) ;;

let ie_neq l r = (l, r) ;;

(* Same as intr without but maintain the error *)
(* Remove ie2 from ie1, produces a list of interrors *)
let ie_without ie1 ie2 =
    map (fun i -> interr_of i.l i.u ie1.err) 
        (intr_without ie1.int ie2.int) ;;

(* Union *)
(* This type signature is odd, should probably return an eterm but an import
 * dependency cycle is introduced.  The resulting list has a domain the same
 * size as the union of the two intervals.
 *)
(* ie_union : interr -> interr -> interr list *)
let ie_union l r = 
    let (large, small) = if l.err >= r.err then (l, r) else (r, l) in
    let intrs = ie_without small large in
    [large] @ intrs ;;

