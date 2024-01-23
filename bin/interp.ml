open List
open Float

open Util
open Round
open Tree
open Interval
open Segment
open Eterm

(* Abstraction *)
(* alpha : CStmt -> AStmt *)

let abst_flt f = { int = { u = f ; l = f }; err = ulp f } ;;

let rec abst_aexp exp = 
    match exp with
    | CVal v      -> AVal (Eterm [(abst_flt v)])
    | CVar n      -> AVar n
    | CAdd (l, r) -> AAdd ((abst_aexp l), (abst_aexp r))
    | CSub (l, r) -> ASub ((abst_aexp l), (abst_aexp r))
    | CMul (l, r) -> AMul ((abst_aexp l), (abst_aexp r))
    | CDiv (l, r) -> ADiv ((abst_aexp l), (abst_aexp r)) ;;

let abst_bexp exp =
    match exp with
    | CLt (l, r) -> ALt ((abst_aexp l), (abst_aexp r))
    | CLe (l, r) -> ALe ((abst_aexp l), (abst_aexp r))
    | CEq (l, r) -> AEq ((abst_aexp l), (abst_aexp r))
    | CNe (l, r) -> ANe ((abst_aexp l), (abst_aexp r))
    | CGe (l, r) -> AGe ((abst_aexp l), (abst_aexp r))
    | CGt (l, r) -> AGt ((abst_aexp l), (abst_aexp r)) ;;
    
let rec abst_stmt exp = 
    match exp with
    | CAsgn (n, v) -> 
        AAsgn (n, (abst_aexp v))
    | CIf (b, t, e) -> 
        AIf ((abst_bexp b), (abst_stmt t), (abst_stmt e))
    | CFor (i, c, b, a) -> 
        AFor ((abst_stmt i), (abst_bexp c), (abst_stmt b), (abst_stmt a))
    | CCol (f, s) -> 
        ACol ((abst_stmt f), (abst_stmt s)) 
    | CRet aexp ->
        ARet (abst_aexp aexp) 
    ;;

(* Abstract semantics *)

(* [[A]] : aaexp -> eterm *)
let rec asem_aexp exp m =
    match exp with
    | AVal e      -> (e, Const)
    | AVar n      -> (m n, Id n)
    | AAdd (l, r) -> (eadd (fst (asem_aexp l m)) (fst (asem_aexp r m)), Const)
    | ASub (l, r) -> (esub (fst (asem_aexp l m)) (fst (asem_aexp r m)), Const)
    | AMul (l, r) -> (emul (fst (asem_aexp l m)) (fst (asem_aexp r m)), Const)
    | ADiv (l, r) -> (ediv (fst (asem_aexp l m)) (fst (asem_aexp r m)), Const) ;;

(* abstract boolean operators *)

(* "less than" : (eterm * Id) * (eterm * Id) -> (eterm * Id) * (eterm * Id) *)
let abst_op left right op =
    let (ltrm, lid) = left in
    let (rtrm, rid) = right in
    match ltrm, rtrm with
    | Eterm l, Eterm r -> 
        let (new_l, new_r) = op ltrm rtrm in
        ((new_l, lid), (new_r, rid))
    | _, _ -> ((Bot, lid), (Bot, rid)) ;;
    
let abst_lt left right = abst_op left right eterm_lt ;;
let abst_le left right = abst_op left right eterm_le ;;
let abst_gt left right = abst_op left right eterm_gt ;;
let abst_ge left right = abst_op left right eterm_ge ;;
let abst_eq left right = abst_op left right eterm_eq ;;
let abst_neq left right = abst_op left right eterm_neq ;;

(* [[B]] : amem -> amem *)
let asem_bexp exp mem =
    let { dom = _ ; lookup = m } = mem in
    match exp with
    | ALt (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = abst_lt (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r mem)
    | ALe (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = abst_le (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r mem)
    | AEq (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = abst_eq (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r mem)
    | ANe _ -> mem
    | AGe (l, r) ->
        let ((new_l, lid), (new_r, rid)) = abst_ge (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r mem)
    | AGt (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = abst_gt (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r mem)
        
(* [[S]] : astmt -> amem -> amem *)

(* u_mem : amem -> amem -> amem *)
let u_amem mem1 mem2 = 
    let { dom = dom1 ; lookup = m1 } = mem1 in
    let { dom = dom2 ; lookup = m2 } = mem2 in
    let dom3 = SS.union dom1 dom2 in
    { dom = dom3 ;
      lookup = fun x -> eterm_union (m1 x) (m2 x) } ;;

(* For loops require finding a fixpoint *)
(* fixpoint : ('a -> 'a) -> 'a -> 'a *)
let rec fixpoint f i = 
    let next = f i in
    if next = i
    then next
    else fixpoint f next ;;

(*
(* We don't _need_ to widen since we have a lattice of finite height (floating
   points numbers are not infinite), however in practice it is too tall. *)
let w_val i1 i2 =
    match i1, i2 with
    | { l = i1l; u = i1u }, { l = i2l; u = i2u } when i1l > i2l && i1u < i2u ->
        { l = neg_infinity; u = infinity }
    | { l = i1l; u = _ }, { l = i2l; u = i2u } when i1l > i2l ->
        { l = neg_infinity; u = i2u }
    | { l = _; u = i1u }, { l = i2l; u = i2u } when i1u < i2u ->
        { l = i2l; u = infinity }
    | { l = _; u = _ }, { l = i2l; u = i2u } ->
        { l = i2l; u = i2u } ;;

let w_err e1 e2 = if e2 > e1 then infinity else e2 ;;
let w_eterm e1 e2 = 
    match e1, e2 with
    | Eterm i1, Eterm i2 ->
        Eterm { int = w_val i1.int i2.int; err = w_err i1.err i2.err }
    | Eterm _, Bot -> e1  
    | Bot, Eterm _ -> e2
    | Bot, Bot -> Bot ;;

(* TODO: Right now I'm sorta ignoring if x not in one of the memories.  
   Logic is handled in w_eterm, which will probably fall over. *)
(* w_amem : amem -> amem -> amem *)
let w_amem mem1 mem2 =
    let { dom = dom1 ; lookup = m1 } = mem1 in
    let { dom = dom2 ; lookup = m2 } = mem2 in
    let dom3 = SS.union dom1 dom2 in
    { dom = dom3 ;
      lookup = fun x -> w_eterm (m1 x) (m2 x) } ;;

(* OCaml's structural equality here _should_ work *)
let rec abst_iter f m n = 
    if n = 0 then m else
    let next = f m in
    let widened = w_amem m next in
    if widened = m then 
        widened
    else
        abst_iter f widened (n - 1) ;;
*)

let rec abst_iter f m n =
    if n = 0 then m else
    let next = f m in
    let widened = u_amem m next in
    if widened = m then 
        widened
    else
        abst_iter f widened (n - 1) ;;

let comp f g x = f (g x) ;;

let rec asem_stmt exp is m =
    match exp with
    | AAsgn (id, e) -> amem_update (Id id) (fst (asem_aexp e m.lookup)) m 
    | AIf (c, t, e) -> 
        u_amem (asem_stmt t is (asem_bexp c m)) 
               (asem_stmt e is (asem_bexp (not_abexp c) m))
    | AFor (f, c, a, b) -> 
        let body = comp (asem_stmt a is) 
                        (comp (asem_stmt b is) (asem_bexp c)) in
        asem_bexp (not_abexp c) (abst_iter body (asem_stmt f is m) is)
    | ACol (s1, s2) -> asem_stmt s2 is (asem_stmt s1 is m) 
    | ARet x -> m ;;

let abst_interp exp m = asem_stmt exp 20 m ;;
