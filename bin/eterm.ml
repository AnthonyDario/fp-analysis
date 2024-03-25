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

(* Get the range of the eterm as an interval.  If the domain is non-continuous
   this function treats it as continuous *)
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

(* This returns the domain as a list of intervals *)
let dom et =
    let sorted = sort (fun s1 s2 -> Float.compare (lower s1.int) (lower s2.int)) (get_segs et) in
    match sorted with
    | x :: xs ->
        fold_left 
            (fun acc s -> 
                if intr_overlap s.int (hd acc)
                then (intr_union (hd acc) s.int) :: tl acc
                else s.int :: acc)
            [x.int] xs
    | [] -> [] ;;
    

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
let rec combine_segs (segs : segment list) : segment list =
    let total = length segs in
    let curr = ref 0 in
    fold_left (fun acc s -> 
        curr := !curr + 1 ;
        Format.printf "\rcombine %d/%d" !curr total ; Format.print_flush() ;
        combine_elem s acc) [] segs
and combine_elem (s1 : segment) (segs : segment list) =
    match segs with
    | x :: xs -> 
        if s1.err = x.err && seg_overlap s1 x
        then (combine_seg x s1) :: xs 
        else x :: combine_elem s1 xs
    | [] -> [s1] 
and combine_seg (s1 : segment) (s2 : segment) : segment =
    seg_of (min_flt [lower s1.int ; lower s2.int]) 
           (max_flt [upper s1.int ; upper s2.int]) s1.err
;;

(* Compare segments by error, break ties by lower bound *)
let seg_compare (s1 : segment) (s2 : segment) : int =
    let err_cmp = Float.compare s2.err s1.err in
    if err_cmp = 0 
    then Float.compare (lower s2.int) (lower s1.int)
    else err_cmp ;;

let cnt = ref 0;;
let tot = ref 0;;

(* Merge with adjacency comparing *)
let rec merge et =
    (* let err_first = sort seg_compare (get_segs et) in  *)
    let err_first = sort (fun s1 s2 -> Float.compare s2.err s1.err) (get_segs et) in
    tot := length err_first ;
    cnt := 0 ;
    let ret = Eterm (merge_inner [] [] err_first false) in
    Format.printf "\nmerged %d into %d\n" !tot (length (get_segs ret)) ; ret
and merge_inner (dom : float intr list) (acc : segment list) 
                (lst : segment list) (has_nan : bool) : segment list = 
    cnt := !cnt + 1;
    Format.printf "\rmerged %d/%d - dom size = %d - acc size = %d" !cnt !tot (length dom) (length acc); 
    Format.print_flush();
    match lst with
    | x :: xs -> 
        if has_nan && not (is_valid x.int)
        then merge_inner dom acc xs true 
        else (if length acc > 0 &&
                x.err = (hd acc).err && 
                (intr_adjacent x.int (hd acc).int || intr_overlap x.int (hd acc).int)
        then 
             let com = combine_seg x (hd acc) in
             merge_inner (expand_domain dom x.int)
                         (* ((seg_withouts_intr com dom) @ acc) *)
                         (combine_seg x (hd acc) :: tl acc)
                         xs
                         (has_nan || (not (is_valid x.int)))
        else 
            merge_inner (expand_domain dom x.int) 
                         ((seg_withouts_intr x dom) @ acc) 
                         xs
                         (has_nan || (not (is_valid x.int))))
    | [] -> acc
and expand_domain (dom : float intr list) (i : float intr) : float intr list =
    match dom with
    | x :: xs ->
        if intr_overlap i x || intr_adjacent i x
        then expand_domain xs (intr_union x i)
        else x :: expand_domain xs i
    | [] -> [i] ;;

(* eterm -> eterm -> eterm list *)
let eop le re op =
    match le, re with
    (* | Eterm ls, Eterm rs -> merge (Eterm (concat (product_map op ls rs))) *)
    | Eterm ls, Eterm rs ->
        let m = (concat (product_map op ls rs)) in
        (* Format.printf "product_map: \n %s\n\n" (str_eterm (Eterm m)) ; *)
        Format.printf "\ncreated %d segments \n" (length m);
        (let ret = merge (Eterm m) in
        Format.printf "\nmerged : %d * %d = %d into %d\n" 
                      (length (get_segs le)) 
                      (length (get_segs re)) 
                      (length m) 
                      (length (get_segs ret)) ; 
        Format.print_flush();
        ret )
    | _, _ -> Bot ;;

let eadd le re = 
    Format.printf "eadd %d + %d\n" (length (get_segs le)) (length (get_segs re)) ;
    Format.print_flush ();
    eop le re seg_add ;;
let esub le re = 
    Format.printf "esub %d + %d\n" (length (get_segs le)) (length (get_segs re)) ;
    Format.print_flush ();
    eop le re seg_sub ;;
let emul le re = 
    Format.printf "emul %d + %d\n" (length (get_segs le)) (length (get_segs re)) ;
    Format.print_flush ();
    eop le re seg_mul ;;
let ediv le re = 
    Format.printf "ediv %d + %d\n" (length (get_segs le)) (length (get_segs re)) ;
    Format.print_flush ();
    eop le re seg_div ;;

(* Boolean operators *)
(* Get overlapping portion of both step-functions *)
let overlap (e1: eterm) (e2: eterm) : (eterm * eterm) =
    


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
