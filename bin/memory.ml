open List

open Segment
open Stepfunction
open Interval
open Tree

(* Abstract Memory *)
type id = Id of string | ArrElem of string * int intr | Const ;;

module SS = Set.Make(String) ;;

exception UndefinedVariableException of string ;;

(* Memory modeled as a function.  The domain is tracked. *)
type amem = {
    dom : SS.t ;
    lookup : string -> aval option
}

let fail_lookup (x : string) (m : string -> aval option) = 
    match m x with
    | Some v -> v
    | None -> raise (UndefinedVariableException (x ^ " Is not assigned")) ;;

let amem_bot = { dom = SS.empty ; lookup = fun _ -> None } ;;

(* ___________________________________ *)
let str_interval (i : float interval) : string = 
    "[" ^ Format.sprintf "%20.30f" i.l ^ 
    " ; " ^ Format.sprintf "%20.30f" i.u ^ "]" ;;

let str_intr (intr : float intr) : string =
    match intr with
    | Intr i -> str_interval i
    | IntrErr -> "IntrErr"
    | IntrBot -> "_|_" ;;

let str_intrs (is : float intr list) : string =
    fold_left (fun acc i -> acc ^ str_intr i ^ ", ") "{" is ^ "}" ;;

let str_iInterval (i : int interval) : string =
        "[" ^ Int.to_string i.l ^ 
        " ; " ^ Int.to_string i.u ^ "]" ;;

let str_iIntr (intr : int intr) : string =
    match intr with
    | Intr i -> str_iInterval i
    | IntrErr -> "IntrErr"
    | IntrBot -> "_|_" ;;

let str_seg (seg : segment) : string =
    "(" ^ str_intr seg.int ^ ", " ^ Format.sprintf "%20.30f" seg.err ^ ")" ;;

let str_segs (segs : segment list) : string =
    fold_left (fun acc s -> acc ^ str_seg s ^ ", ") "{" segs ^ "}" ;;

let str_sf (trm : stepF) : string = 
    match trm with
    | StepF ies -> str_segs ies
    | Bot       -> "_" ;;

let str_aval (v : aval) : string =
    match v with
    | AInt i      -> str_iIntr i
    | AFloat Bot  -> "_|_"
    | AFloat trm  -> str_sf trm 
    | AArr (_, _) -> "AArr" ;;

let str_id (id : id) : string = 
    match id with
    | Id n -> n
    | Const -> "Const" 
    | ArrElem (n, idxs) -> n ^ "[" ^ str_iIntr idxs ^ "]" ;;

(* ___________________________________ *)

let rec amem_update (n : id) (v : aval) (m : amem) : amem = 
    Format.printf "amem_update %s\n" (str_id n);
    let { dom = mdom ; lookup = look } = m in
    match n with 
    | Id id -> 
        { dom = SS.add id mdom ; 
          lookup = fun x -> if id = x then Some v else look x }
    | ArrElem (id, idxs) -> (
        Format.printf "ArrElem: %s[%s]\n" id (str_iIntr idxs) ;
        match look id with
        | Some (AArr (arr, l)) -> (
            Format.printf "amem_update ArrElem (Some)\n" ;
            Format.print_flush () ;
            let updated = Some (AArr ((arr_update arr idxs v), update_len l idxs)) in
            { dom = SS.add id mdom ; 
              lookup = fun x -> if id = x 
                                then updated
                                else look x }
            )
        | None -> (
            Format.printf "amem_update ArrElem (None)\n" ; 
            Format.print_flush() ;
            let updated = Some (AArr ((arr_update arr_bot idxs v), (upper idxs) + 1)) in
            { dom = SS.add id mdom ;
              lookup = fun x -> if id = x
                                then updated
                                else look x}
                )
        | Some av -> failwith ("Attempting to index a non-array: " ^ str_aval av))
    | Const -> m 

and update_len (l : int) (itr : int intr) : int =
    if l > upper itr + 1 then l else upper itr + 1;;

(* amem_contains : amem -> string -> bool *)
let amem_contains m n = 
    let { dom = _ ; lookup = look } = m in
    match look n with
    | None -> false
    | _   -> true ;;

let amem_eq (m1 : amem) (m2 : amem) : bool =
    m1.dom = m2.dom && 
    fold_left (fun acc x -> acc && (m1.lookup x) = (m2.lookup x))
              true 
              (SS.elements m1.dom) ;;
