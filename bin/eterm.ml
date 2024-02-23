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
    | Eterm segs -> Intr { l = min_flt (map (fun seg -> lower seg.int) segs) ;
                           u = max_flt (map (fun seg -> upper seg.int) segs) }
    | Bot        -> IntrBot ;;

(* Utility to get the range as a segment datatype *)
let range_seg (et : eterm) : segment = 
    let intr = range et in
    seg_of_intr intr 0.0 ;;

let get_segs et = 
    match et with
    | Eterm segs -> segs
    | Bot -> [] ;;

let eterm_append (et : eterm) (segs : segment list) = 
    match et with
    | Eterm errs -> Eterm (segs @ errs)
    | Bot -> 
        (match segs with
         | [] -> Bot
         | _  -> Eterm segs) ;;


(* Convert to and from an integer interval for casting purposes *)
let eterm_to_iintr et = intr_to_iintr (range et) ;;
let iintr_to_eterm (ii : int intr) = 
    match ii with
    | Intr i -> Eterm [seg_of (Float.of_int i.l) (Float.of_int i.u) 0.0]
    | _ -> Bot ;;


(* Arithmetic operators *)
(* ------------------------- *)

(* find overlapping segments *)

let cnt = ref 0;;
let merge et = 
    Format.printf "\neterm merging %d\n" (length (get_segs et)) ;
    Format.print_flush () ;
    let err_first = sort (fun s1 s2 -> Float.compare s2.err s1.err) (get_segs et) in
    Format.printf "sorted\n" ; Format.print_flush() ;
    cnt := 0;
    match err_first with
    | x :: xs ->
        fold_left (fun acc seg -> 
                    cnt := !cnt + 1;
                    Format.printf "\rmerged %d/%d" !cnt (length (get_segs et)); Format.print_flush();
                    eterm_append acc (seg_withouts seg (get_segs acc)
                    ))
                  (Eterm [x]) xs
    | [] -> Bot ;;

(* eterm -> eterm -> eterm list *)
let eop le re op =
    Format.printf "Eop\n\n" ;
    match le, re with
    | Eterm ls, Eterm rs -> merge (Eterm (concat (product_map op ls rs)))
    | _, _ -> Bot ;;

let eadd le re = 
    Format.printf "eadd %d + %d\n" (length (get_segs le)) (length (get_segs re)) ;
    Format.print_flush ();
    eop le re seg_add ;;
let esub le re = 
    Format.printf "esub\n" ;
    eop le re seg_sub ;;
let emul le re = 
    Format.printf "emul\n" ;
    eop le re seg_mul ;;
let ediv le re = 
    Format.printf"ediv\n" ;
    eop le re seg_div ;;

(* Boolean operators *)
(* Chops based upen segment comparison function passed in *)
let chop (eterm : eterm) (range : float intr) 
         (comp : segment -> segment -> (segment * segment)) : eterm =
    match range with
    | Intr r ->
        (match eterm with
         | Eterm segs ->
               let dummy = seg_of_intr range 0.0 in
               Eterm (filter (fun x -> x != seg_bot) 
                             (map (fun x -> fst (comp x dummy)) segs))
         | Bot -> Bot ) 
    | _ -> Bot ;;

let eterm_lt l r = (chop l (range r) seg_lt, chop r (range l) seg_gt) ;;
let eterm_le l r = (chop l (range r) seg_le, chop r (range l) seg_ge) ;;
let eterm_gt l r = (chop l (range r) seg_gt, chop r (range l) seg_lt) ;;
let eterm_ge l r = (chop l (range r) seg_ge, chop r (range l) seg_le) ;;
let eterm_eq l r = (chop l (range r) seg_eq, chop r (range l) seg_eq) ;; 
let eterm_neq l r = (l, r) ;;

(* Union *)
let eterm_union (l : eterm) (r : eterm) : eterm =
    merge (eterm_append l (get_segs r)) ;;
