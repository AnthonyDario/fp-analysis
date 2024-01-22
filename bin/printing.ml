open List

open Tree
open Interval
open Segment
open Eterm

(* Concrete Domain *)
let rec str_caexp exp = 
    match exp with
    | CVal v      -> Float.to_string v
    | CVar n      -> n
    | CAdd (l, r) -> str_caexp l ^ " + " ^ str_caexp r
    | CSub (l, r) -> str_caexp l ^ " - " ^ str_caexp r
    | CMul (l, r) -> str_caexp l ^ " * " ^ str_caexp r
    | CDiv (l, r) -> str_caexp l ^ " / " ^ str_caexp r ;;

let str_cbexp exp =
    match exp with
    | CLt (l, r) -> str_caexp l ^ " < "  ^ str_caexp r
    | CLe (l, r) -> str_caexp l ^ " <= " ^ str_caexp r
    | CEq (l, r) -> str_caexp l ^ " = "  ^ str_caexp r
    | CNe (l, r) -> str_caexp l ^ " != " ^ str_caexp r
    | CGe (l, r) -> str_caexp l ^ " >= "  ^ str_caexp r
    | CGt (l, r) -> str_caexp l ^ " > " ^ str_caexp r ;;

let rec str_cstmt stmt = 
    match stmt with
    | CAsgn (n, v)       -> n ^ " = " ^ str_caexp v
    | CIf   (b, t, e)    -> 
        "if " ^ str_cbexp b ^ "\nthen " ^ str_cstmt t ^ "\nelse " ^ str_cstmt e
    | CFor  (i, c, a, b) ->
        "for (" ^ str_cstmt i ^ "; " ^ str_cbexp c ^ "; " ^ str_cstmt a ^ ")\n" ^
        str_cstmt b
    | CCol  (f, s)       -> str_cstmt f ^ ";\n" ^ str_cstmt s ;;

(* Abstract Domain *)
let str_interval i =
    "[" ^ Float.to_string i.l ^ " ; " ^ Float.to_string i.u ^ "]" ;;

let str_seg ie =
    "(" ^ str_interval ie.int ^ ", " ^ Float.to_string ie.err ^ ")" ;;

let str_eterm trm = 
    match trm with
    | Eterm ies -> (fold_left (fun acc s -> acc ^ s ^ ", ") 
                              "{" 
                              (map str_seg ies))
                    ^ "}"
    | Bot       -> "_" ;;

let rec str_aaexp exp = 
    match exp with
    | AVal Bot    -> "@"
    | AVal e      -> str_eterm e
        (* "([" ^ Float.to_string e.int.l ^ " ; " ^ Float.to_string e.int.u ^ 
        "], " ^ Float.to_string e.err ^ ")" *)
    | AVar n      -> n
    | AAdd (l, r) -> str_aaexp l ^ " + " ^ str_aaexp r
    | ASub (l, r) -> str_aaexp l ^ " - " ^ str_aaexp r
    | AMul (l, r) -> str_aaexp l ^ " * " ^ str_aaexp r
    | ADiv (l, r) -> str_aaexp l ^ " / " ^ str_aaexp r ;;

let str_abexp exp =
    match exp with
    | ALt (l, r) -> str_aaexp l ^ " < "  ^ str_aaexp r
    | ALe (l, r) -> str_aaexp l ^ " <= " ^ str_aaexp r
    | AEq (l, r) -> str_aaexp l ^ " = "  ^ str_aaexp r
    | ANe (l, r) -> str_aaexp l ^ " != " ^ str_aaexp r
    | AGe (l, r) -> str_aaexp l ^ " >= "  ^ str_aaexp r
    | AGt (l, r) -> str_aaexp l ^ " > " ^ str_aaexp r ;;

let rec str_astmt stmt = 
    match stmt with
    | AAsgn (n, v)       -> n ^ " = " ^ str_aaexp v
    | AIf   (b, t, e)    -> 
        "if " ^ str_abexp b ^ "\nthen " ^ str_astmt t ^ "\nelse " ^ str_astmt e
    | AFor  (i, c, a, b) ->
        "for (" ^ str_astmt i ^ "; " ^ str_abexp c ^ "; " ^ str_astmt a ^ ")\n" ^
        str_astmt b
    | ACol  (f, s)       -> str_astmt f ^ ";\n" ^ str_astmt s ;;

let str_avar n amem = n ^ " -> " ^ str_eterm (amem.lookup n) 

let str_amem amem =
    fold_left (fun acc x -> acc ^ "\n" ^ (str_avar x amem))
              "" (SS.elements amem.dom) ;;
