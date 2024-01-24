open List
open Util
open Interval
open Segment
open Eterm

(* Concrete Domain *)
type ctyp = IntTyp | FloatTyp ;;

type cval =
    | CInt   of int
    | CFloat of float

type caexp =
    | CVal of cval
    | CVar of string * ctyp
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
    | CAsgn of string * caexp
    | CIf   of cbexp * cstmt * cstmt
    | CFor  of cstmt * cbexp * cstmt * cstmt
    | CCol  of cstmt * cstmt 
    | CRet  of caexp ;;

(* Abstract Domain *)

(* Abstract AST *)
type atyp = IntrTyp | AStepTyp

type aval = 
    | AInt   of iInterval
    | AFloat of eterm ;;

type aaexp =
    | AVal of aval
    | AVar of string * atyp
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
    | AGe (l, r) -> AGe (l, r)
    | AGt (l, r) -> AGt (l, r) ;;

type astmt = 
    | AAsgn of string * aaexp
    | AIf   of abexp * astmt * astmt
    | AFor  of astmt * abexp * astmt * astmt
    | ACol  of astmt * astmt 
    | ARet  of aaexp ;;

type id = Id of string | Const ;;

(* Abstract Memory *)
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

(* amem_update : id -> float -> amem -> amem *)
let amem_update n v m = 
    let { dom = mdom ; lookup = look } = m in
    match n with 
    | Id id -> 
        { dom = SS.add id mdom ; 
          lookup = fun x -> if id == x then Some v else look x }
    | Const -> m ;;

(* amem_contains : amem -> string -> bool *)
let amem_contains m n = 
    let { dom = _ ; lookup = look } = m in
    match look n with
    | None -> false
    | _   -> true ;;

