open List

open Util
open Tree
open Interval
open Segment
open Stepfunction

exception UnassignedVariableException of string ;;

(* Abstraction *)
(* --------------------------------------------------- *)

let abst_flt (f : float) : segment = 
    { int = Intr { u = f ; l = f }; err = ulp f } ;;

let abst_typ (typ : ctyp) : atyp =
    match typ with
    | IntTyp -> IntrTyp
    | FloatTyp -> AStepTyp ;;

let abst_val (v : cval) : aval =
    match v with
    | CInt i -> AInt (Intr { l = i ; u = i })
    | CFloat f -> AFloat (StepF [abst_flt f]) ;;

let rec abst_aexp (exp : caexp) : aaexp = 
    match exp with
    | CVal v      -> AVal (abst_val v)
    | CVar (n, t) -> AVar (n, abst_typ t)
    | CAdd (l, r) -> AAdd ((abst_aexp l), (abst_aexp r))
    | CSub (l, r) -> ASub ((abst_aexp l), (abst_aexp r))
    | CMul (l, r) -> AMul ((abst_aexp l), (abst_aexp r))
    | CDiv (l, r) -> ADiv ((abst_aexp l), (abst_aexp r)) ;;

let abst_bexp (exp : cbexp) : abexp =
    match exp with
    | CLt (l, r) -> ALt ((abst_aexp l), (abst_aexp r))
    | CLe (l, r) -> ALe ((abst_aexp l), (abst_aexp r))
    | CEq (l, r) -> AEq ((abst_aexp l), (abst_aexp r))
    | CNe (l, r) -> ANe ((abst_aexp l), (abst_aexp r))
    | CGe (l, r) -> AGe ((abst_aexp l), (abst_aexp r))
    | CGt (l, r) -> AGt ((abst_aexp l), (abst_aexp r)) ;;
    
let rec abst_stmt (exp : cstmt) : astmt = 
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
(* --------------------------------------------------- *)
let aval_op (l : aval) (r : aval) 
            (iintr_op : intIntr -> intIntr -> intIntr) 
            (sf_op : stepF -> stepF -> stepF) 
            : aval = 
    match l, r with
    | AInt ii1, AInt ii2 -> AInt (iintr_op ii1 ii2)
    | AInt ii, AFloat et | AFloat et, AInt ii -> 
        AInt (iintr_op ii (sf_to_iintr et))
    | AFloat et1, AFloat et2 -> AFloat (sf_op et1 et2) ;;

(* Arithmetic Expressions *)
(* --------------------------------------------------- *)
let rec asem_aexp (exp : aaexp) (mem : amem) : (aval * id) =
    let { dom = _ ; lookup = m } = mem in
    match exp with
    | AVal e      -> (e, Const)
    | AVar (n, _) -> (
        match m n with
        | Some v -> (v, Id n)
        | None -> raise (UnassignedVariableException n))
    | AAdd (l, r) -> 
        (aval_op (fst (asem_aexp l mem)) 
                  (fst (asem_aexp r mem)) 
                  iintr_add eadd, Const)
    | ASub (l, r) -> 
        (aval_op (fst (asem_aexp l mem)) 
                  (fst (asem_aexp r mem)) 
                  iintr_sub esub, Const)
    | AMul (l, r) ->
        (aval_op (fst (asem_aexp l mem)) 
                  (fst (asem_aexp r mem)) 
                  iintr_mul emul, Const)
    | ADiv (l, r) -> 
        (aval_op (fst (asem_aexp l mem)) 
                  (fst (asem_aexp r mem)) 
                  iintr_div ediv, Const) ;;

(* Abstract boolean operators *)
(* --------------------------------------------------- *)
let abst_op (left : stepF) (right : stepF) 
            (op : stepF -> stepF -> (stepF * stepF)) : (stepF * stepF) =
    match left, right with
    | StepF _, StepF _ -> 
        let (new_l, new_r) = op left right in
        (new_l, new_r)
    | _, _ -> (Bot, Bot) ;;
    

(* Need to maintain the types of each side of the operator *)
let abst_bool_op (l : aval * id) (r : aval * id) 
                 (iintr_op : intIntr -> intIntr -> (intIntr * intIntr))
                 (sf_op : stepF -> stepF -> (stepF * stepF))
                 : ((aval * id) * (aval * id)) = 

    let (ltrm, lid), (rtrm, rid) = l, r in

    (* wrap into a tuple *)
    let wrap_int (l, r : intIntr * intIntr) : (aval * id) * (aval * id) = 
        ((AInt l, lid), (AInt r, rid)) in

    let wrap_flt (l, r : stepF * stepF) : (aval * id) * (aval * id) =
        ((AFloat l, lid), (AFloat r, rid)) in

    match ltrm, rtrm with
    | AFloat sf1, AFloat sf2 -> wrap_flt (abst_op sf1 sf2 sf_op)
    | AInt ii1, AInt ii2 -> wrap_int (iintr_op ii1 ii2)
    | AInt ii, AFloat sf -> 
        ((AInt (fst (iintr_op ii (sf_to_iintr sf))), lid), 
         (AFloat (snd (sf_op (iintr_to_sf ii) sf)), rid))
    | AFloat sf, AInt ii -> 
        ((AFloat (fst (sf_op sf (iintr_to_sf ii))), lid),
         (AInt (snd (iintr_op (sf_to_iintr sf) ii)), rid))
    ;;

let abst_lt l r = abst_bool_op l r iintr_lt sf_lt ;;
let abst_le l r = abst_bool_op l r iintr_le sf_le ;;
let abst_gt l r = abst_bool_op l r iintr_gt sf_gt ;;
let abst_ge l r = abst_bool_op l r iintr_ge sf_ge ;;
let abst_eq l r = abst_bool_op l r iintr_eq sf_eq ;;
let abst_neq l r = abst_bool_op l r iintr_neq sf_neq ;;

(* Abstract Semantics of boolean expressions *)
(* --------------------------------------------------- *)
let asem_bexp (exp : abexp) (m : amem) : amem =
    match exp with
    | ALt (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = abst_lt (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r m)
    | ALe (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = abst_le (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r m)
    | AEq (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = abst_eq (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r m)
    | ANe _ -> m
    | AGe (l, r) ->
        let ((new_l, lid), (new_r, rid)) = abst_ge (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r m)
    | AGt (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = abst_gt (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r m)

let aval_union (a1 : aval) (a2 : aval) : aval = 
    match a1, a2 with
    | AInt ii1, AInt ii2 -> AInt (iintr_union ii1 ii2)
    | AInt ii, AFloat et -> AInt (iintr_union ii (sf_to_iintr et))
    | AFloat et, AInt ii -> AInt (iintr_union (sf_to_iintr et) ii)
    | AFloat et1, AFloat et2 -> AFloat (sf_union et1 et2) ;;

(* u_mem : amem -> amem -> amem *)
let u_amem mem1 mem2 = 
    let { dom = dom1 ; lookup = m1 } = mem1 in
    let { dom = dom2 ; lookup = m2 } = mem2 in
    let dom3 = SS.union dom1 dom2 in
    { dom = dom3 ;
      lookup = fun x -> Some (aval_union (fail_lookup x m1) (fail_lookup x m2)) } ;;

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

(* iterate function f on m n times *)
let rec abst_iter (f : amem -> amem) (m : amem) (n : int) : amem =
    if n = 0 then m else
    let next = f m in
    let widened = u_amem m next in
    if widened = m then 
        widened
    else
        abst_iter f widened (n - 1) ;;

let comp f g x = f (g x) ;;

let rec asem_stmt (exp : astmt) (iters : int) (m : amem) : amem =
    match exp with
    | AAsgn (id, e) -> amem_update (Id id) (fst (asem_aexp e m)) m 
    | AIf (c, t, e) -> 
        u_amem
            (u_amem (asem_stmt t iters (asem_bexp c m)) 
                    (asem_stmt e iters (asem_bexp (not_abexp c) m)))
            (unstable_branch c t e iters m)
    | AFor (f, c, a, b) -> 
        let body = comp (asem_stmt a iters) 
                        (comp (asem_stmt b iters) (asem_bexp c)) in
        asem_bexp (not_abexp c) (abst_iter body (asem_stmt f iters m) iters)
    | ACol (s1, s2) -> asem_stmt s2 iters (asem_stmt s1 iters m) 
    | ARet _ -> m

(* Find the unstable region of a condition *)
(* A little bit of a hack since abst_eq computes the overlap *)
and filter_unstable (exp : abexp) (m : amem) : amem =
    match exp with
    | ALt (l, r) | ALe (l, r) | AEq (l, r) | ANe (l, r) | AGe (l, r) | AGt (l, r) ->
        let ((new_l, lid), (new_r, rid)) = abst_eq (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r m)

(* find the error between the branches 
   map each variable to a new interval based on the then branch and other things*)
and unstable_branch (exp : abexp) (t : astmt) (e : astmt) 
                    (i : int) (m : amem) : amem =
    let fu = filter_unstable exp m in
    let m1, m2 = asem_stmt t i fu, asem_stmt e i fu in
    u_amem (fold_left (fun a x -> amem_update (Id x) (unstable_aval x m1 m2) a) amem_bot (SS.elements m1.dom)) (* then branch *)
           (fold_left (fun a x -> amem_update (Id x) (unstable_aval x m2 m1) a) amem_bot (SS.elements m2.dom)) (* else branch *)

(* What is the difference between branch m1 and branch m2? Assuming we took
 * branch m1. *)
and unstable_aval (x: string) (m1 : amem) (m2 : amem) : aval =
    let { dom = _ ; lookup = m1l} = m1 in
    let { dom = _ ; lookup = m2l} = m2 in
    let x1, x2 = m1l x, m2l x in
    match x1, x2 with
    | Some av1, Some av2 -> both_branches av1 av2
    | Some av1, None -> one_branch av1
    | None, Some av2 -> one_branch av2
    | None, None -> raise (UnassignedVariableException "Neither branch assigned?")

(* If both branches have the value then either the error or the difference *)
and both_branches (av1 : aval) (av2 : aval) : aval =
    match av1, av2 with
    | AFloat (StepF sf1), AFloat (StepF sf2) ->
        AFloat (StepF 
            (map (fun seg -> seg_of_intr seg.int (max_flt [seg.err ; diff_intr seg.int (range (StepF sf2))])) sf1))
    | AFloat (StepF sf1), AFloat Bot ->
        AFloat (StepF
            (map (fun seg -> seg_of_intr seg.int infinity) sf1))
    | AFloat (StepF sf1), AInt i -> 
        AFloat (StepF
            (map (fun seg -> seg_of_intr seg.int (max_flt [seg.err ; diff_intr seg.int (iintr_to_intr i)])) sf1))
    | _, _ -> av1

(* if the other branch doesn't have a value then our error is infinite *)
and one_branch (a : aval) : aval =
    match a with
    | AFloat (StepF sf) -> 
        AFloat (StepF (map (fun s -> seg_of_intr s.int infinity) sf))
    | _         -> a ;;

let abst_interp exp m = asem_stmt exp 20 m ;;
