open List
open Hashtbl

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
    tbl : (string, aval) Hashtbl.t ;
}

let fail_lookup (x : string) (m : (string, aval) Hashtbl.t) = 
    match Hashtbl.find_opt m x with
    | Some v -> v
    | None -> raise (UndefinedVariableException (x ^ " Is not assigned")) ;;

let amem_bot = { dom = SS.empty ; tbl = Hashtbl.create 5000 }
let lookup (m : amem) (x : string) : aval option = Hashtbl.find_opt m.tbl x ;;

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
    Format.printf "amem_update %s with %s\n" (str_id n) (str_aval v);
    let { dom = mdom ; tbl = tbl } = m in
    match n with 
    | Id id -> 
        Hashtbl.replace tbl id v ;
        { dom = SS.add id mdom ; 
          tbl = tbl }
    | ArrElem (id, idxs) -> (
        Format.printf "ArrElem: %s[%s]\n" id (str_iIntr idxs) ;
        match lookup m id with
        | Some (AArr (arr, l)) -> (
            Format.printf "amem_update ArrElem (Some)\n" ;
            Format.print_flush () ;
            let updated = AArr ((arr_update arr idxs v), update_len l idxs) in
            Hashtbl.replace tbl id updated ;
            { dom = SS.add id mdom ; 
              tbl = tbl }
            )
        | None -> (
            Format.printf "amem_update ArrElem (None)\n" ; 
            Format.print_flush() ;
            let updated = AArr ((arr_update arr_bot idxs v), (upper idxs) + 1) in
            Hashtbl.replace tbl id updated ;
            { dom = SS.add id mdom ;
              tbl = tbl }
                )
        | Some av -> failwith ("Attempting to index a non-array: " ^ str_aval av))
    | Const -> m 

and update_len (l : int) (itr : int intr) : int =
    if l > upper itr + 1 then l else upper itr + 1;;

(* amem_contains : amem -> string -> bool *)
let amem_contains m n = 
    match lookup m n with
    | None -> false
    | _   -> true ;;

let amem_eq (m1 : amem) (m2 : amem) : bool =
    m1.dom = m2.dom && 
    fold_left (fun acc x -> acc && (lookup m1 x) = (lookup m2 x))
              true 
              (SS.elements m1.dom) ;;
