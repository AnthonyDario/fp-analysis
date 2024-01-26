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
    | Eterm ies -> { l = min_flt (map (fun ie -> ie.int.l) ies) ;
                     u = max_flt (map (fun ie -> ie.int.u) ies) }
    | Bot       -> intr_bot ;;

(* Utility to get the range as a segment datatype *)
let range_ie et = 
    let intr = range et in
    seg_of intr.l intr.u 0.0 ;;

let get_segs et = 
    match et with
    | Eterm ies -> ies
    | Bot -> [] ;;

let eterm_append et ies = 
    match et with
    | Eterm errs -> Eterm (errs @ ies)
    | Bot -> 
        (match ies with
         | [] -> Bot
         | _  -> Eterm ies) ;;

(* Convert to an integer interval for casting purposes *)
let eterm_to_iintr et = intr_to_iintr (range et) ;;

(* Arithmetic operators *)
(* ------------------------- *)
let merge et = 
    let err_first = sort (fun ie1 ie2 -> Float.compare ie2.err ie1.err) (get_segs et) in
    match err_first with
    | x :: xs ->
        fold_left (fun acc ie -> eterm_append acc (ie_without ie (range_ie acc))) 
                  (Eterm [x]) xs
    | [] -> Bot ;;

(* eterm -> eterm -> eterm list *)
let eop le re op =
    match le, re with
    | Eterm ls, Eterm rs -> merge (Eterm (product_map op ls rs))
    | _, _ -> Bot ;;

let eadd le re = eop le re ie_add ;;
let esub le re = eop le re ie_sub ;;
let emul le re = eop le re ie_mul ;;
let ediv le re = eop le re ie_div ;;

(* Boolean operators *)
(* Chops based upen segment comparison function passed in *)
let chop eterm range comp =
    match eterm with
    | Eterm ies ->
          let dummy = seg_of range.l range.u 0.0 in
          Eterm (filter (fun x -> x != seg_bot) 
                        (map (fun x -> fst (comp x dummy)) ies))
    | Bot -> Bot ;;

let eterm_lt l r = (chop l (range r) ie_lt, chop r (range l) ie_gt) ;;
let eterm_le l r = (chop l (range r) ie_le, chop r (range l) ie_ge) ;;
let eterm_gt l r = (chop l (range r) ie_gt, chop r (range l) ie_lt) ;;
let eterm_ge l r = (chop l (range r) ie_ge, chop r (range l) ie_le) ;;
let eterm_eq l r = (chop l (range r) ie_eq, chop r (range l) ie_eq) ;; 
let eterm_neq l r = (l, r) ;;

(* Union *)
(* Merge an eterm with a single segment *)

let partition_segs et f = 
    match et with
    | Eterm ies -> partition f ies
    | Bot       -> ([], [])

let partition_overlap et ie = partition_segs et (fun i -> seg_overlap i ie) ;;

let rec eterm_seg_union et ie =
    match et with
    | Eterm _ ->
        let (overlap, nonoverlap) = partition_overlap et ie in
        merge (eterm_append (Eterm nonoverlap) (et_ie_u_inner overlap ie))
    | Bot -> Bot
(* segment list * segment -> segment list *)
and et_ie_u_inner segments ie =
    match segments with
    | seg :: segs -> 
        if seg.err < ie.err (* if the current segment's error is less than the mergee's *)
        then ie_without seg ie @ et_ie_u_inner segs ie (* then remove any overlap *)
        (* Don't need to remove overlap here because, there is no overlap in an eterm *)
        else seg :: et_ie_u_inner segs ie 
    | [] -> [ie] ;;

let eterm_union l r = 
    match l, r with
    | Eterm le, Eterm re -> 
        let ies = sort (fun ie1 ie2 -> Float.compare ie1.int.l ie2.int.l) (le @ re) in
        (match ies with
         | hd :: tl -> fold_left (fun acc ie -> eterm_seg_union acc ie) (Eterm [hd]) tl
         | [] -> Bot)
    | _, _ -> Bot ;;
