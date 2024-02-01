open List
open Util
open Interval
open Segment

(* Models a step function, the interval is the domain and the err is the value
   in that interval *)
type eterm = Bot | Eterm of segment list ;;
let eterm_of l u e = Eterm [seg_of l u e] ;;

(* Utilities *)
(* ------------------------- *)

(* Get the range of the eterm as an interval *)
let range et = 
    match et with
    | Eterm segs -> { l = min_flt (map (fun seg -> seg.int.l) segs) ;
                      u = max_flt (map (fun seg -> seg.int.u) segs) }
    | Bot        -> intr_bot ;;

(* Utility to get the range as a segment datatype *)
let range_seg et = 
    let intr = range et in
    seg_of intr.l intr.u 0.0 ;;

let get_segs et = 
    match et with
    | Eterm segs -> segs
    | Bot -> [] ;;

let eterm_append et segs = 
    match et with
    | Eterm errs -> Eterm (errs @ segs)
    | Bot -> 
        (match segs with
         | [] -> Bot
         | _  -> Eterm segs) ;;


(* Convert to and from an integer interval for casting purposes *)
let eterm_to_iintr et = intr_to_iintr (range et) ;;
let iintr_to_eterm ii = Eterm [seg_of (Float.of_int ii.low) (Float.of_int ii.up) 0.0] ;;


(* Arithmetic operators *)
(* ------------------------- *)
let merge et = 
    let err_first = sort (fun s1 s2 -> Float.compare s2.err s1.err) (get_segs et) in
    match err_first with
    | x :: xs ->
        fold_left (fun acc seg -> eterm_append acc (seg_without seg (range_seg acc))) 
                  (Eterm [x]) xs
    | [] -> Bot ;;

(* eterm -> eterm -> eterm list *)
let eop le re op =
    match le, re with
    | Eterm ls, Eterm rs -> merge (Eterm (product_map op ls rs))
    | _, _ -> Bot ;;

let eadd le re = eop le re seg_add ;;
let esub le re = eop le re seg_sub ;;
let emul le re = eop le re seg_mul ;;
let ediv le re = eop le re seg_div ;;

(* Boolean operators *)
(* Chops based upen segment comparison function passed in *)
let chop eterm range comp =
    match eterm with
    | Eterm segs ->
          let dummy = seg_of range.l range.u 0.0 in
          Eterm (filter (fun x -> x != seg_bot) 
                        (map (fun x -> fst (comp x dummy)) segs))
    | Bot -> Bot ;;

let eterm_lt l r = (chop l (range r) seg_lt, chop r (range l) seg_gt) ;;
let eterm_le l r = (chop l (range r) seg_le, chop r (range l) seg_ge) ;;
let eterm_gt l r = (chop l (range r) seg_gt, chop r (range l) seg_lt) ;;
let eterm_ge l r = (chop l (range r) seg_ge, chop r (range l) seg_le) ;;
let eterm_eq l r = (chop l (range r) seg_eq, chop r (range l) seg_eq) ;; 
let eterm_neq l r = (l, r) ;;

(* Union *)
let eterm_union (l : eterm) (r : eterm) : eterm =
    merge (eterm_append l (get_segs r)) ;;
