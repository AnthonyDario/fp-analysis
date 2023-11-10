(* Concrete Domain *)
type caexp =
    | CVal of float
    | CVar of string
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
    | CCol  of cstmt * cstmt ;;

(* Abstract Domain *)
type interval = {
    l : float;
    u : float
} ;;

type interr = {
    int : interval;
    err : float
} ;;

type id = Id of string | Const ;;
type eterm = Bot | Eterm of interr ;;

let eterm_of l u e = Eterm { int = { l = l ; u = u } ; err = e } ;;

(* Abstract Memory *)
type amem = string -> eterm ;;

let amem_bot x = Bot ;;
let amem_update n v m = 
    match n with 
    | Id id -> fun x -> if id == x then v else m x 
    | Const -> m ;;

(* Abstract AST *)
type aaexp =
    | AVal of eterm
    | AVar of string
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

type astmt = 
    | AAsgn of string * aaexp
    | AIf   of abexp * astmt * astmt
    | AFor  of astmt * abexp * astmt * astmt
    | ACol  of astmt * astmt ;;
