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
    tbl : (string, aval) Hashtbl.t ;
}

let fail_lookup (x : string) (m : (string, aval) Hashtbl.t) = 
    match Hashtbl.find_opt m x with
    | Some v -> v
    | None -> raise (UndefinedVariableException (x ^ " Is not assigned")) ;;

let amem_bot = { dom = SS.empty ; tbl = Hashtbl.create 5000 }
let lookup (m : amem) (x : string) : aval option = Hashtbl.find_opt m.tbl x ;;

let rec amem_update (n : id) (v : aval) (m : amem) : amem = 
    let { dom = mdom ; tbl = tbl } = m in
    let new_tbl = Hashtbl.copy tbl in
    match n with 
    | Id id -> 
        Hashtbl.replace new_tbl id v ;
        { dom = SS.add id mdom ; 
          tbl = new_tbl }
    | ArrElem (id, idxs) -> (
        match lookup m id with
        | Some (AArr (arr, l)) -> (
            let updated = AArr ((arr_update arr idxs v), update_len l idxs) in
            Hashtbl.replace new_tbl id updated ;
            { dom = SS.add id mdom ; 
              tbl = new_tbl })
        | None -> (
            let updated = AArr ((arr_update (arr_bot ()) idxs v), (upper idxs) + 1) in
            Hashtbl.replace new_tbl id updated ;
            { dom = SS.add id mdom ;
              tbl = new_tbl })
        | Some av -> failwith ("Attempting to index a non-array"))
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
