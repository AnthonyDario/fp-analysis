open List

open Interval
open Tree
open Segment
open Stepfunction
open Memory

(* Output ACSL Specifications *)

(* Want an ensures clause that gives output ranges as well as floating point error *)


(* ensures x >= 5.0 && x <= 7.0 && \round_error(x) <= 0.034 *)

(*
/*@
ensures p >= 0.3 && p < 0.7;
behavior p_seg1:
    assumes p >= 0.3 && p < 0.5;
    ensures \roundoff(p) <= 0.0034;
behavior p_seg2:
    assumes p >= 0.5 && p < 0.7;
    ensures \roundoff(p) <= 0.0044;
*/
*)

let acsl_iInterval (n : string) (i : int interval) : string = 
    Format.sprintf "ensures %s >= %i && %s <= %i;\n" n i.l n i.u
;;


let acsl_iIntr (n : string) (intr : int intr) : string = 
    match intr with
    | Intr i  -> acsl_iInterval n i
    | IntrBot -> n ^ " = bot\n"
;;


let acsl_seg_behavior (name : string) (i : float interval) (err : float) (num : int) : string = 
    Format.sprintf 
        "behavior %s_seg%i:\n\tassumes %s >= %20.30e && %s <= %20.30e;\n\tensures \\roundoff(%s) <= %20.30e;\n"
        name num name i.l name i.u name err
;;
    

let acsl_seg (name : string) (seg : segment) (num : int): string =
    match seg.int with
    | Intr i -> acsl_seg_behavior name i seg.err num
    | _      -> name ^ " = bot\n"
;;


let acsl_segs (name : string) (segs : segment list) : string =
    fst (fold_left (fun acc s -> (fst acc ^ acsl_seg name s (snd acc) , (snd acc) + 1)) ("", 0) segs)
;;


let acsl_seg_bounds (name : string) (intr : float intr) : string =
    match intr with
    | Intr i  -> Format.sprintf "ensures %s >= %20.30e && %s <= %20.30e;\n" name i.l name i.u
    | IntrBot -> name ^ " = bottom;\n"


let acsl_sf (name : string) (trm : stepF) : string =
    match trm with
    | StepF segs -> (acsl_seg_bounds name (range trm)) ^ acsl_segs name segs
    | Bot       -> name ^ " = bot\n"
;;

(*
let acsl_arr 
*)


let acsl_aval (n : string) (av : aval) : string =
    match av with
    | AInt ii      -> acsl_iIntr n ii
    | AFloat et    -> acsl_sf n et
    | AArr (ar, l) -> "array\n"
    | ABot         -> n ^ " = bot\n" 
;;


let acsl_avar (n : string) (amem : amem) : string =
    match (lookup amem n) with
    | Some av -> acsl_aval n av
    | None -> n ^ " -> _" ;;


let acsl_amem (amem : amem) : string =
    (fold_left (fun acc x -> acc ^ (acsl_avar x amem) ^ "\n")
              "/*@\n" (SS.elements amem.dom)) ^ "*/" ;;

(* Reference from the CSV printing *)
(*
module SS = Set.Make(String) ;;

(* Memory modeled as a function.  The domain is tracked. *)
type amem = {
    dom : SS.t ;
    tbl : (string, aval) Hashtbl.t ;
}

let csv_amem (amem : amem) : string =
    fold_left (fun acc x -> acc ^ (csv_avar x amem) ^ "\n")
              "var,type,low,high,err\n" (SS.elements amem.dom) ;;
              *)
