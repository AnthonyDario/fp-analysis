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
            (iintr_op : int intr -> int intr -> int intr) 
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
                 (iintr_op : int intr -> int intr -> (int intr * int intr))
                 (sf_op : stepF -> stepF -> (stepF * stepF))
                 : ((aval * id) * (aval * id)) = 

    let (ltrm, lid), (rtrm, rid) = l, r in

    (* wrap into a tuple *)
    let wrap_int (l, r : int intr * int intr) : (aval * id) * (aval * id) = 
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


(* Widening: Note that the order of the arguments matters. *)
(* Step Functions 
 * widen the ends and widen each segment *)
let rec widen_sf (sf1 : stepF) (sf2 : stepF) : stepF = 
    match sf1, sf2 with
    | StepF i1, StepF i2 ->
        (sf_union
            (sf_union
                (if (lower (range sf2) <= lower (range sf1)) 
                 then StepF [seg_of neg_infinity (lower (range sf1)) infinity]
                 else Bot)
                (if (upper (range sf2) >= upper (range sf1))
                 then StepF [seg_of (upper (range sf1)) infinity infinity]
                 else Bot))
            (StepF (widen_segs sf1 sf2)))
    | StepF _, Bot -> sf1
    | Bot, StepF _ -> sf2
    | Bot, Bot -> Bot

and widen_segs (sf1 : stepF) (sf2 : stepF) : segment list =
        map (fun s1 -> fold_left widen_seg s1 (get_segs sf2)) (get_segs sf1)

and widen_seg (s1 : segment) (s2 : segment) : segment =
    if seg_overlap s1 s2 && s1.err < s2.err
    then seg_of_intr s1.int infinity
    else s1 ;;

let widen_iintr (i1 : int intr) (i2 : int intr) : int intr =
    let low = if (lower i1) > (lower i2) then min_int else (lower i1) in
    let high = if (upper i1) < (upper i2) then max_int else (upper i1) in
    iintr_of low high ;;


let widen_aval (a1 : aval) (a2 : aval) : aval =
    match a1, a2 with
    | AFloat sf1, AFloat sf2 -> AFloat (widen_sf sf1 sf2)
    | AFloat sf1, AInt i2 -> AInt (widen_iintr (sf_to_iintr sf1) i2)
    | AInt i1, AFloat sf2 -> AInt (widen_iintr i1 (sf_to_iintr sf2))
    | AInt i1, AInt i2 -> AInt (widen_iintr i1 i2)
;;

let widen_aval_opt (a1 : aval option) (a2 : aval option) : aval =
    match a1, a2 with
    | Some av1, Some av2 -> widen_aval av1 av2
    | _, _ -> failwith "Variable dissapeared between iterations of widening";;

let widen_amem (mem1 : amem) (mem2 : amem) : amem =
    let { dom = dom1 ; lookup = m1 } = mem1 in
    let { dom = dom2 ; lookup = m2 } = mem2 in
    fold_left (fun acc x -> amem_update (Id x) 
                                        (widen_aval_opt (acc.lookup x) (m2 x)) 
                                        acc)
              mem1 (SS.elements mem2.dom)

(* iterate with widening *)
let rec abst_iter (f : amem -> amem) (m : amem) (n : int) : amem =
    if n = 0 then m else
    let next = f m in
    let widened = widen_amem m next in
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
