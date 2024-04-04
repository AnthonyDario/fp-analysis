open List
open Util
open Interval
open Segment

(* Models a step function, the interval is the domain and the err is the value
   in that interval *)
type stepF = Bot | StepF of segment list ;;
let sf_of l u e = StepF [seg_of l u e] ;;

(* Utilities *)
(* ------------------------- *)

(* Get the range of the step function as an interval.  If the domain is
 * non-continuous this function treats it as continuous *)
let range (sf : stepF) : float intr = 
    match sf with
    | StepF segs -> Intr { l = min_flt (map (fun seg -> lower seg.int) segs) ;
                           u = max_flt (map (fun seg -> upper seg.int) segs) }
    | Bot        -> IntrBot ;;


(* Utility to get the range as a segment datatype *)
let range_seg (sf : stepF) : segment = 
    let intr = range sf in
    seg_of_intr intr 0.0 ;;

let get_segs (sf : stepF) : segment list = 
    match sf with
    | StepF segs -> segs
    | Bot -> [] ;;

(* This returns the domain as a list of intervals *)
(* TODO: Where is this used? *)
let dom (sf : stepF) : float intr list =
    let sorted = 
        sort (fun s1 s2 -> Float.compare (lower s1.int) (lower s2.int)) 
             (get_segs sf) in
    match sorted with
    | x :: xs ->
        fold_left 
            (fun acc s -> 
                if intr_overlap s.int (hd acc)
                then (intr_union (hd acc) s.int) :: tl acc
                else s.int :: acc)
            [x.int] xs
    | [] -> [] ;;
    

let sf_append (sf : stepF) (segs : segment list) = 
    match sf with
    | StepF errs -> StepF (segs @ errs)
    | Bot -> 
        (match segs with
         | [] -> Bot
         | _  -> StepF segs) ;;


(* Convert to and from an integer interval for casting purposes *)
let sf_to_iintr (sf : stepF) : int intr = intr_to_iintr (range sf) ;;
let iintr_to_sf (ii : int intr) = 
    match ii with
    | Intr i -> StepF [seg_of (Float.of_int i.l) (Float.of_int i.u) 0.0]
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
let rec merge (sf : stepF) : stepF =
    let err_first = 
        sort (fun s1 s2 -> Float.compare s2.err s1.err) (get_segs sf) in
    tot := length err_first ;
    cnt := 0 ;
    let ret = StepF (merge_inner [] [] err_first false) in
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
             (* let com = combine_seg x (hd acc) in *)
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


(* Trying merging earlier *)
let rec eop (l : stepF) (r : stepF) 
            (op : segment -> segment -> segment list) 
            (prop_err_op : segment -> segment -> float)
            : stepF =
    match l, r with
    | StepF ls, StepF rs ->
        let is = concat 
            (product_map (fun x y -> 
                            let perr = prop_err_op x y in
                            (map (fun s -> {s with err = perr}) 
                                          (op x y))) 
                         ls rs) in
        Format.printf "\ncreated %d segments \n" (length is);
        let ms = merge (StepF is) in
        let ret = concat (map (fun s -> binade_split_seg s) 
                         (get_segs ms)) in 
        Format.printf 
            "\nsplit : %d * %d = %d into %d then %d\n" 
            (length (get_segs l)) 
            (length (get_segs r)) 
            (length is) 
            (length (get_segs ms))
            (length ret) ;
        merge (StepF ret)
    | _, _ -> Bot

(* Binade splitting on segments *)
and binade_split_seg (s : segment) : segment list =
    let is = split_binade s.int in
    map (fun i -> { int = i ; err = s.err +. ulp_intr i }) is ;;

let eadd (l : stepF) (r : stepF) : stepF = 
    Format.printf "eadd %d + %d\n" (length (get_segs l)) (length (get_segs r)) ;
    eop l r seg_add err_add_prop ;;

let esub (l : stepF) (r : stepF) : stepF = 
    Format.printf "esub %d + %d\n" (length (get_segs l)) (length (get_segs r)) ;
    eop l r seg_sub err_sub_prop ;;

let emul (l : stepF) (r : stepF) : stepF = 
    Format.printf "emul %d + %d\n" (length (get_segs l)) (length (get_segs r)) ;
    eop l r seg_mul err_mul_prop ;;

let ediv (l : stepF) (r : stepF) :stepF = 
    Format.printf "ediv %d + %d\n" (length (get_segs l)) (length (get_segs r)) ;
    eop l r seg_div err_div_prop ;;


(* Boolean operators *)
(* Get overlapping portion of both step-functions *)
let overlap (s1: stepF) (s2: stepF) : (stepF * stepF) =
    match s1, s2 with
    | StepF segs1, StepF segs2 ->
        let ov = intr_with (range s1) (range s2) in
        (StepF (filter_map (fun s -> seg_with_intr s ov) segs1),
         StepF (filter_map (fun s -> seg_with_intr s ov) segs2))
    | Bot, _ | _, Bot -> (Bot, Bot) ;;

(* Chops based upen segment comparison function passed in *)
let chop (sf : stepF) (range : float intr) 
         (comp : segment -> segment -> (segment * segment)) : stepF =
    match range with
    | Intr _ ->
        (match sf with
         | StepF segs ->
               let dummy = seg_of_intr range 0.0 in
               StepF (filter (fun x -> x != seg_bot) 
                             (map (fun x -> fst (comp x dummy)) segs))
         | Bot -> Bot ) 
    | _ -> Bot ;;

let sf_lt l r = (chop l (range r) seg_lt, chop r (range l) seg_gt) ;;
let sf_le l r = (chop l (range r) seg_le, chop r (range l) seg_ge) ;;
let sf_gt l r = (chop l (range r) seg_gt, chop r (range l) seg_lt) ;;
let sf_ge l r = (chop l (range r) seg_ge, chop r (range l) seg_le) ;;
let sf_eq l r = (chop l (range r) seg_eq, chop r (range l) seg_eq) ;; 
let sf_neq l r = (l, r) ;;

(* Union *)
let sf_union (l : stepF) (r : stepF) : stepF =
    merge (sf_append l (get_segs r)) ;;
