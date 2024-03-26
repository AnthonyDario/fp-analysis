open Float
open List

open Interval
open Util

(* The interval-error terms.  Represents a section of the interval with an
   associated error *)
type segment = {
    int : float intr;
    err : float
} ;;

let seg_bot = { int = IntrBot ; err = 0. } ;;

let seg_of l u err = 
    if l > u || err < 0.
    then seg_bot 
    else { int = intr_of l u ; err = err } ;;

let seg_of_intr i err =
    match i with
    | Intr _ -> { int = i ; err = err } 
    | IntrBot -> { int = i ; err = 0. }
    | IntrErr -> { int = i ; err = nan } ;;

let seg_overlap s1 s2 = intr_overlap s1.int s2.int ;;

let get_segs_range (segs : segment list) : float intr list =
    match segs with
    (* | x :: xs -> fold_left (fun acc s -> intr_union acc s.int) x.int xs *)
    | x :: xs -> fold_left (fun acc s -> 
                                map (fun i -> if intr_overlap i s.int then intr_union i s.int else i) acc) [x.int] xs
    | [] -> [IntrBot] ;;

let lower_bnd (s : segment) : float = lower s.int ;;
let upper_bnd (s : segment) : float = upper s.int ;;


(* Same as intr without but maintain the error *)
(* Remove seg2 from seg1 *)
let seg_without (seg1 : segment) (seg2 : segment) : segment list =
    map (fun i -> seg_of_intr i seg1.err)
        (intr_without seg1.int seg2.int) ;;

let seg_withouts (s1 : segment) (s2 : segment list) : segment list =
    map (fun i -> seg_of_intr i s1.err) (intr_withouts s1.int (get_segs_range s2)) ;;

let seg_withouts_intr (s1 : segment) (is : float intr list) : segment list =
    map (fun i -> seg_of_intr i s1.err) (intr_withouts s1.int is) ;;

(* The portions of s1 that overlap with s2 
 * Note that the error of segment1 is maintained here *)
let seg_with (s1 : segment) (s2 : segment) : segment = 
    let overlap = intr_with s1.int s2.int in
    seg_of_intr overlap s1.err ;;

(* Same as above but works with intervals *)
let seg_with_intr (s : segment) (i : float intr) : segment option =
    let overlap = intr_with s.int i in
    match overlap with
    | Intr i -> Some (seg_of_intr overlap s.err)
    | _ -> None ;;
    

(* First element of return is s1 without any overlap of s2.  Second element is
 * overlapping portion *)
let seg_partition (s1 : segment) (s2 : segment)
    : (segment list * segment) =
    (seg_without s1 s2, seg_with s1 s2) ;;

(* Dealing with error *)
let ulp_add l r = ulp_intr (intr_add_op l r) ;;
let ulp_sub l r = ulp_intr (intr_sub_op l r) ;;
let ulp_mul l r = ulp_intr (intr_mul_op l r) ;;
let ulp_div l r = ulp_intr (intr_div_op l r) ;;

let ulp_op (l : segment) (r : segment) 
           (op : float interval -> float interval -> float) = 
    match l.int, r.int with
    | Intr li, Intr ri -> op li ri
    | IntrBot, _ | _, IntrBot | IntrErr, _ | _, IntrErr-> nan ;;

(* For these error functions, o is the result of the interval operation on l
 * and r *)

let err_add (l : segment) (r : segment) (o : float intr) = 
    l.err +. r.err +. (ulp_intr o) ;;

let err_sub (l : segment) (r : segment) (o : float intr) = 
    (* Format.printf "err_sub\n" ; *)
    l.err +. r.err +. (ulp_intr o) ;;

let err_sbenz (l : segment) (r : segment) (_ : float intr) = 
    l.err +. r.err ;;

let err_mul (l : segment) (r : segment) (o : float intr) =
    let lup = mag_lg_intr l.int in
    let rup = mag_lg_intr r.int in
    lup *. r.err +. rup *. l.err +. l.err *. r.err +. (ulp_intr o) ;;

let err_div (l : segment) (r : segment) (o : float intr) =
    let lup = mag_lg_intr l.int in
    let rdn = mag_sm_intr r.int in
    ((lup *. r.err +. rdn *. l.err) /. (rdn *. rdn -. rdn *. r.err)) +.  
        (ulp_intr o) ;;

(* Sterbenz Lemma *)
(* ---------------------- *)
(* Before subtraction, find sections that meet the condition *)
(* Find Sterbenz stuff *)
let get_sterbenz_seg (seg : segment) : segment =
    let sbenz = get_sterbenz_intr seg.int in
    seg_of_intr sbenz seg.err ;;

(* Arithmetic operators *)
(* ---------------------- *)
let seg_op (x : segment) (y : segment) 
           (intr_op : float intr -> float intr -> float intr)
           (err_op : segment -> segment -> float intr -> float) 
           : segment list =
    let op_out = intr_op x.int y.int in
    let split_result = split_binade op_out in
    map (fun i -> { int = i ; err = err_op x y i }) split_result ;;
    

let seg_add (x : segment) (y : segment) : segment list =
    seg_op x y intr_add err_add

(* No special cases *)
let seg_sub_reg (x : segment) (y : segment) : segment list =
    seg_op x y intr_sub err_sub ;;

(* Sterbenz *)
let seg_sub_sbenz (x : segment) (y : segment) : segment list =
    seg_op x y intr_sub err_sbenz ;;

let seg_sub (x : segment) (y : segment) : segment list = 
    let reg, sbenz = (seg_partition y (get_sterbenz_seg x)) in
    if sbenz = seg_bot 
    then concat_map (seg_sub_reg x) reg  
    else seg_sub_sbenz x sbenz @ concat_map (seg_sub_reg x) reg 

let seg_mul (x : segment) (y : segment) : segment list = 
    seg_op x y intr_mul err_mul ;;

let seg_div (x : segment) (y : segment) : segment list = 
    seg_op x y intr_div err_div ;;


(* Boolean operators *)
(* ---------------------- *)
(* Return the new values of the operands *)
let seg_lt l r = 
    let (li, ri) = intr_lt l.int r.int in
    (seg_of_intr li l.err, seg_of_intr ri r.err) ;;

let seg_le l r = 
    let (li, ri) = intr_le l.int r.int in
    (seg_of_intr li l.err, seg_of_intr ri r.err) ;;

let seg_gt l r = 
    let (li, ri) = intr_gt l.int r.int in
    (seg_of_intr li l.err, seg_of_intr ri r.err) ;;

let seg_ge l r = 
    let (li, ri) = intr_ge l.int r.int in
    (seg_of_intr li l.err, seg_of_intr ri r.err) ;;

let seg_eq l r =
    let (li, ri) = intr_eq l.int r.int in
    (seg_of_intr li l.err, seg_of_intr ri r.err) ;;

let seg_neq l r = (l, r) ;;

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

