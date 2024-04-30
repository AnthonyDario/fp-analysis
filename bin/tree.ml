open Interval
open Stepfunction

open Segment
open List
open Util

(* Concrete Domain *)
type ctyp = IntTyp | FloatTyp | ArrTyp of ctyp ;;

type cval =
    | CInt   of int
    | CFloat of float
    | CArr   of (int -> cval) * int ;;
    (*
    | CIntArr   of (int -> int)
    | CFloatArr of (int -> float) ;;
    *)

type caexp =
    | CVal of cval
    | CVar of string * ctyp
    | CAcc of string * caexp option * ctyp (* Array Access *)
    | CAdd of caexp * caexp
    | CSub of caexp * caexp
    | CMul of caexp * caexp
    | CDiv of caexp * caexp ;;

type cbexp =
    | CLt of caexp * caexp
    | CLe of caexp * caexp
    | CEq of caexp * caexp
    | CNe of caexp * caexp
    | CGe of caexp * caexp
    | CGt of caexp * caexp ;;

type cstmt =
    | CAsgn of (string * caexp option) * caexp
    | CIf   of cbexp * cstmt * cstmt
    | CFor  of cstmt * cbexp * cstmt * cstmt
    | CCol  of cstmt * cstmt 
    | CRet  of caexp ;;

(* Abstract Domain *)

(* Abstract AST *)
type atyp = IntrTyp | AStepTyp | AArrTyp of atyp ;;

type aval = 
    | AInt   of int intr
    | AFloat of stepF 
    | AArr   of arr * int
    | ABot

and arr = (int, aval) Hashtbl.t ;;

type aaexp =
    | AVal of aval
    | AVar of string * atyp
    | AAcc of string * aaexp option * atyp (* array access *)
    | AAdd of aaexp * aaexp
    | ASub of aaexp * aaexp
    | AMul of aaexp * aaexp
    | ADiv of aaexp * aaexp ;;

type abexp =
    | ALt of aaexp * aaexp
    | ALe of aaexp * aaexp
    | AEq of aaexp * aaexp
    | ANe of aaexp * aaexp
    | AGe of aaexp * aaexp
    | AGt of aaexp * aaexp ;;

let not_abexp abexp = 
    match abexp with
    | ALt (l, r) -> AGe (l, r)
    | ALe (l, r) -> AGt (l, r)
    | AEq (l, r) -> ANe (l, r)
    | ANe (l, r) -> AEq (l, r)
    | AGe (l, r) -> ALt (l, r)
    | AGt (l, r) -> ALe (l, r) ;;

type astmt = 
    | AAsgn of (string * aaexp option) * aaexp
    | AIf   of abexp * astmt * astmt
    | AFor  of astmt * abexp * astmt * astmt
    | ACol  of astmt * astmt 
    | ARet  of aaexp ;;

(* -------------------------- *)
(* DELETE ME *)
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


let rec str_aval (v : aval) : string =
    match v with
    | AInt i      -> str_iIntr i
    | AFloat Bot  -> "_|_"
    | AFloat trm  -> str_sf trm 
    | AArr (ar, l) -> 
        (fold_left (fun acc i -> acc ^ (Int.to_string i) ^ " : " ^ 
                                 str_aval (Option.get (Hashtbl.find_opt ar i)) ^
                                 ", ")
                   ("[")
                   (int_seq l)) ^ "] (" ^ Int.to_string l ^ ")" 
    | ABot -> "ABot" ;;
(* -------------------------- *)
(* Working with Arrays *)

let arr_bot () : (int, aval) Hashtbl.t = Hashtbl.create 5000 ;;

(* Apply a function piecewise to the elements of a1 and a2 for the length of
   the shorter list.  All elements in the longer list remain unchanged *)
let rec apply (f : aval -> aval -> aval)
              (a1 : arr) (l1 : int)
              (a2 : arr) (l2 : int) : aval =
    Format.printf "apply\n";
              (*
    Format.printf "apply ___ %s \n%s\n\n" (str_aval (AArr (a1,l1))) 
                                          (str_aval (AArr (a2, l2))) ;
                                          *)
    let (long, long_l), (_, short_l) = 
        if l1 < l2 
        then ((Hashtbl.copy a2, l2), (a1, l1))
        else ((Hashtbl.copy a1, l1), (a2, l2)) in
    iter (fun i -> match map2 f (Hashtbl.find_opt a1 i) 
                                (Hashtbl.find_opt a2 i) with
                   | Some av -> Hashtbl.replace long i av
                   | None    -> ())
         (int_seq short_l) ;
    AArr (long, long_l)

and map2 (f : 'a -> 'b -> 'c) (a : 'a option) (b : 'b option) : 'c option =
    match a, b with
    | Some av, Some bv -> Some (f av bv)
    | _, _ -> None ;;


let rec aval_union (av1 : aval) (av2 : aval) : aval = 
    (* Format.printf "aval_union %s %s\n" (str_aval av1) (str_aval av2); *)
    (* Format.printf "aval_union \n"; *)
    Format.print_flush () ;
    (* input_line stdin; *)
    match av1, av2 with
    | AInt ii1, AInt ii2     -> AInt (iintr_union ii1 ii2)
    | AInt ii, AFloat et     -> AInt (iintr_union ii (sf_to_iintr et))
    | AFloat et, AInt ii     -> AInt (iintr_union (sf_to_iintr et) ii)
    | AFloat et1, AFloat et2 -> AFloat (sf_union et1 et2) 
    | AArr (a1, l1), AArr (a2, l2) -> (
        (* Format.printf "aval_union AArrs %s \nU\n %s\n" (str_aval av1) (str_aval av2) ; *)
        Format.printf "aval_union AArrs %d %d\n" l1 l2 ;
        Format.print_flush () ;
        (* input_line stdin ; *)
        apply aval_union a1 l1 a2 l2
        )
    | AArr _, _ | _, AArr _  -> failwith "union of array and number" 
    | ABot, _ -> av2
    | _, ABot -> av1 ;;


let arr_update (a1 : arr) (idxs : int intr) (v : aval) : arr =
    Format.printf "arr_update index %s with %s \n" (str_iIntr idxs) (str_aval v) ;
    Format.print_flush () ;
    (* For each element in the index 
       Update the index with the union if it is there 
       If not then just return the thing *)
    let new_tbl = Hashtbl.copy a1 in
    List.iter (fun i -> match Hashtbl.find_opt new_tbl i with
                        | Some av -> Hashtbl.replace new_tbl i (aval_union v av)
                        | None -> Hashtbl.replace new_tbl i v) 
              (iintr_range idxs);
    new_tbl ;;

