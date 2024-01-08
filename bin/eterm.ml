open List
open Util
open Interval
open Interr

(* Models a step function, the interval is the domain and the err is the value
   in that interval *)
type eterm = Bot | Eterm of interr list ;;
let eterm_of l u e = Eterm [interr_of l u e] ;;

(* Get the range of the eterm as an interval *)
let range et = 
    match et with
    | Eterm ies -> { l = min_flt (map (fun ie -> ie.int.l) ies) ;
                     u = max_flt (map (fun ie -> ie.int.u) ies) }
    | Bot       -> intr_bot ;;

(* Arithmetic operators *)
(* eterm -> eterm -> eterm list *)
let eop le re op =
    match le, re with
    | Eterm ls, Eterm rs -> Eterm (product_map op ls rs)
    | _, _ -> Bot ;;

let eadd le re = eop le re ie_add ;;
let esub le re = eop le re ie_sub ;;
let emul le re = eop le re ie_mul ;;
let ediv le re = eop le re ie_div ;;

(* Boolean operators *)
(* Chops based open interr comparison function passed in *)
let chop eterm range comp =
    match eterm with
    | Eterm ies ->
          let dummy = interr_of range.l range.u 0.0 in
          Eterm (filter (fun x -> x != interr_bot) 
                        (map (fun x -> fst (comp x dummy)) ies))
    | Bot -> Bot ;;

let eterm_lt l r = (chop l (range r) ie_lt, chop r (range l) ie_ge) ;;
let eterm_le l r = (chop l (range r) ie_le, chop r (range l) ie_gt) ;;
let eterm_gt l r = let (new_r, new_l) = eterm_le r l in (new_l, new_r) ;;
let eterm_ge l r = let (new_r, new_l) = eterm_lt r l in (new_l, new_r) ;;
let eterm_eq l r = (chop l (range r) ie_eq, chop r (range l) ie_eq) ;; 
let eterm_neq l r = (l, r) ;;

(* Union *)
(* Merge an eterm with a single segment *)

let overlapping_segments et ie =
    match et with
    | Eterm ies -> filter (fun i -> interr_overlap i ie) ies
    | Bot       -> [] ;;

let rec eterm_interr_union et ie =
    match et with
    | Eterm ies ->
        let overlap = overlapping_segments et ie in
        Eterm (et_ie_u_inner overlap ie)
    | Bot -> Bot
(* interr list * interr -> interr list *)
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
         | hd :: tl -> fold_left (fun acc ie -> eterm_interr_union acc ie) (Eterm [hd]) tl
         | [] -> Bot)
    | _, _ -> Bot ;;
