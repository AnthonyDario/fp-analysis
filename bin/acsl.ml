open List

open Interval
open Tree
open Segment
open Stepfunction
open Memory
open Util


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
        "behavior %s_seg%i:\n\tassumes %s >= %20.30e && %s <= %20.30e;\n\tensures \\round_error(%s) <= %20.30e;\n"
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


let rec acsl_aval (name : string) (av : aval) : string =
    match av with
    | AInt ii      -> acsl_iIntr name ii
    | AFloat et    -> acsl_sf name et
    | AArr (ar, l) -> acsl_arr name ar l
    | ABot         -> name ^ " = bot\n" 

and acsl_arr (name : string) (ar : (int, aval) Hashtbl.t) (l : int) : string =
    fold_left 
        (fun acc i -> acc ^ (acsl_aval (name ^ "[" ^ Int.to_string i ^ "]") (Hashtbl.find ar i) ^ "\n"))
        ""
        (int_seq l)
;;


let acsl_avar (n : string) (amem : amem) : string =
    match (lookup amem n) with
    | Some av -> acsl_aval n av
    | None -> n ^ " -> _" ;;


(* Output ACSL Specifications *)
let acsl_amem (amem : amem) : string =
    (fold_left (fun acc x -> acc ^ (acsl_avar x amem) ^ "\n")
              "/*@\n" (SS.elements amem.dom)) ^ "*/" ;;
