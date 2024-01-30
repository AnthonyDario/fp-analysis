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

(* Convert to an integer interval for casting purposes *)
let eterm_to_iintr et = intr_to_iintr (range et) ;;

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
(* Merge an eterm with a single segment *)

(* Partition the segments of et by f *)
let partition_segs (et : eterm) (f : segment -> bool) : (segment list * segment list) = 
    match et with
    | Eterm segs -> partition f segs
    | Bot        -> ([], [])

(* Partition the segments in et by if they overlap with seg *)
let partition_overlap (et : eterm) (seg : segment) = 
    partition_segs et (fun i -> seg_overlap i seg) ;;

(* Union an eterm with a segment *)
let rec eterm_seg_union et seg =
    match et with
    | Eterm _ ->
        let (overlap, nonoverlap) = partition_overlap et seg in
        merge (eterm_append (Eterm nonoverlap) (et_seg_u_inner overlap seg))
    | Bot -> Bot
(* segment list * segment -> segment list *)
and et_seg_u_inner segments s =
    match segments with
    | seg :: segs -> 
        if seg.err < s.err (* if the current segment's error is less than the mergee's *)
        then seg_without seg s @ et_seg_u_inner segs s (* then remove any overlap *)
        (* Don't need to remove overlap here because, there is no overlap in an eterm *)
        else seg :: et_seg_u_inner segs s 
    | [] -> [s] ;;

let eterm_union l r = 
    match l, r with
    | Eterm le, Eterm re -> 
        let segs = sort (fun s1 s2 -> Float.compare s1.int.l s2.int.l) (le @ re) in
        (match segs with
         | hd :: tl -> fold_left (fun acc s -> eterm_seg_union acc s) (Eterm [hd]) tl
         | [] -> Bot)
    | _, _ -> Bot ;;
