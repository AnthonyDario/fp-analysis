open Float
open Round
open Tree

(* Abstraction *)
(* alpha : CStmt -> AStmt *)
let ulp f = succ f -. f ;;

let abst_flt f = { int = { u = f ; l = f }; err = ulp f } ;;

let rec abst_aexp exp = 
    match exp with
    | CVal v      -> AVal (Eterm (abst_flt v))
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
    | CAsgn (n, v)       -> AAsgn (n, (abst_aexp v))
    | CIf   (b, t, e)    -> AIf ((abst_bexp b), (abst_stmt t), (abst_stmt e))
    | CFor  (i, c, b, a) -> 
        AFor ((abst_stmt i), (abst_bexp c), (abst_stmt b), (abst_stmt a))
    | CCol  (f, s)       -> ACol ((abst_stmt f), (abst_stmt s)) ;;

(* Abstract semantics *)

let max_flt l = List.fold_left max neg_infinity l ;;
let min_flt l = List.fold_left min infinity l ;;

(* Interval Operators *)
let intr_add l r = { l = add Down l.l r.l ; u = add Up l.u r.u } ;;
let intr_sub l r = { l = sub Down l.l r.u ; u = sub Up l.u r.l } ;;
let intr_mul l r = 
    { l = min_flt [mul Down l.l r.l ; mul Down l.l r.u ;
                   mul Down l.u r.l ; mul Down l.u r.u] ; 
      u = max_flt [mul Up l.l r.l ; mul Up l.l r.u ; 
                   mul Up l.u r.l ; mul Up l.u r.u] } ;;
let intr_div l r = 
    { l = min_flt [div Down l.l r.l ; div Down l.l r.u ;
                   div Down l.u r.l ; div Down l.u r.u] ; 
      u = max_flt [div Up l.l r.l ; div Up l.l r.u ; 
                   div Up l.u r.l ; div Up l.u r.u] } ;;

(* Error Propagation *)
let mag_lg i = max_flt [(abs i.l) ; (abs i.u)] ;;
let mag_sm i = min_flt [(abs i.l) ; (abs i.u)] ;;

let ulp_add l r = 0.5 *. ulp ((abs l.int.u) +. (abs r.int.u) +. l.err +. r.err) ;;
let ulp_sub l r = 0.5 *. ulp ((mag_lg l.int) +. (mag_lg r.int) +. l.err +. r.err) ;;
let ulp_mul l r = 
    0.5 *. ulp (((mag_lg l.int) +. l.err) *. ((mag_lg r.int) +. r.err)) ;;
let ulp_div l r = 
    0.5 *. ulp (((mag_lg l.int) +. l.err) /. ((mag_sm r.int) +. r.err)) ;;

let err_add l r = 
    match l.err, r.err with
    | le, re when not (is_finite le) || not (is_finite re) -> infinity
    | le, re -> le +. re +. ulp_add l r ;;

let err_sub l r = abs (l.err +. r.err) +. ulp_sub l r ;;

let err_mul l r =
    let lup = mag_lg l.int in
    let rup = mag_lg r.int in
    lup *. r.err +. rup *. l.err +. l.err *. r.err +. ulp_mul l r ;;

let err_div l r =
    let lup = mag_lg l.int in
    let rup = mag_lg r.int in
    ((rup *. l.err -. lup *. r.err) /. (rup *. rup +. rup *. r.err)) +.
    ulp_div l r ;;

(* eterm operations *)
let eadd le re = 
    match le, re with
    | Eterm l,  Eterm r -> 
        Eterm { int = intr_add l.int r.int ; err = err_add l r }
    | _, _ -> Bot ;;
    
let esub le re = 
    match le, re with
    | Eterm l, Eterm r ->
        Eterm { int = intr_sub l.int r.int ; err = err_sub l r }
    | _, _ -> Bot ;;

let emul le re = 
    match le, re with
    | Eterm l, Eterm r ->
        Eterm { int = intr_mul l.int r.int ; err = err_mul l r }
    | _, _ -> Bot ;;

let ediv le re = 
    match le, re with
    | Eterm l, Eterm r ->
        Eterm { int = intr_div l.int r.int ; err = err_div l r }
    | _, _ -> Bot ;;

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
(* TODO: Write functions for the conditions here... *)
(* "a less than" : (eterm * Id) * (eterm * Id) -> (eterm * Id) * (eterm * Id) *)
let alt left right =
    let (ltrm, lid) = left in
    let (rtrm, rid) = right in
    match ltrm, rtrm with
    | Eterm l, Eterm r ->
        let { int = { l = ll ; u = lu } ; err = le} = l in 
        let { int = { l = rl ; u = ru } ; err = re} = r in 
        if ll >= ru then                                    (* l always greater than r *)
            ((Bot, lid), (Bot, rid)) 
        else if (rl <= ll) && (ll <= ru) && (ru <= lu) then (* l sometimes greater than r *)
            ((eterm_of ll (ru -. ulp ru) re, lid), 
             (eterm_of (ll +. ulp ll) ru re, rid))
        else if (ll <= rl) && (rl <= ru) && (ru <= lu) then (* l contains r *)
            ((eterm_of ll (ru -. ulp ru) le, lid), 
             (rtrm, rid))
        else if (rl <= ll) && (ll <= lu) && (lu <= ru) then (* r contains l *)
            ((ltrm, lid), 
             (eterm_of (ll +. ulp ll) ru re, rid))
        else ((ltrm, lid), (rtrm, rid))                     (* l always/sometimes less than r *)
    | _, _ -> ((Bot, lid), (Bot, rid)) ;;

let agt left right = 
    let ((new_r, rid), (new_l, lid)) = alt right left in
    ((new_l, lid), (new_r, rid)) ;;

let ale left right =
    let (ltrm, lid) = left in
    let (rtrm, rid) = right in
    match ltrm, rtrm with
    | Eterm l, Eterm r ->
        let { int = { l = ll ; u = lu } ; err = le} = l in 
        let { int = { l = rl ; u = ru } ; err = re} = r in 
        if ll > ru then                                     (* l always greater than r *)
            ((Bot, lid), (Bot, rid)) 
        else if (rl <= ll) && (ll <= ru) && (ru <= lu) then (* l sometimes greater than r *)
            ((eterm_of ll ru re, lid), 
             (eterm_of ll ru re, rid))
        else if (ll <= rl) && (rl <= ru) && (ru <= lu) then (* l contains r *)
            ((eterm_of ll ru le, lid), (rtrm, rid))
        else if (rl <= ll) && (ll <= lu) && (lu <= ru) then (* r contains l *)
            ((ltrm, lid), (eterm_of ll ru re, rid))
        else ((ltrm, lid), (rtrm, rid))                     (* l always/sometimes less than r *)
    | _, _ -> ((Bot, lid), (Bot, rid)) ;;

let age left right =
    let ((new_r, rid), (new_l, lid)) = ale right left in
    ((new_l, lid), (new_r, rid)) ;;

(* For equality operators we are looking for the overlap of the intervals *)
let aeq left right =
    let (ltrm, lid) = left in
    let (rtrm, rid) = right in
    match ltrm, rtrm with
    | Eterm l, Eterm r ->
        let { int = { l = ll ; u = lu } ; err = le} = l in 
        let { int = { l = rl ; u = ru } ; err = re} = r in 
        if (ll > ru) || (rl > lu) then                      (* No overlap *)
            ((Bot, lid), (Bot, rid)) 
        else if (rl <= ll) && (ll <= ru) && (ru <= lu) then (* l sometimes greater than r *)
            ((eterm_of ll ru le, lid), 
             (eterm_of ll ru re, rid))
        else if (ll <= rl) && (rl <= lu) && (lu <= ru) then (* r sometimes greater than l *)
            ((eterm_of rl lu le, lid),
             (eterm_of rl lu re, rid))
        else if (ll <= rl) && (rl <= ru) && (ru <= lu) then (* l contains r *)
            ((eterm_of rl ru le, lid), 
             (eterm_of rl ru re, rid))
        else if (rl <= ll) && (ll <= lu) && (lu <= ru) then (* r contains l *)
            ((eterm_of ll lu le, lid), 
             (eterm_of ll lu re, rid))
        else raise (Failure "You didn't cover all the cases of intervals")
    | _, _ -> ((Bot, lid), (Bot, rid)) ;;

(* [[B]] : amem -> amem *)
let asem_bexp exp mem =
    let { dom = _ ; lookup = m } = mem in
    match exp with
    | ALt (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = alt (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r mem)
    | ALe (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = ale (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r mem)
    | AEq (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = aeq (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r mem)
    | ANe _ -> mem
    | AGe (l, r) ->
        let ((new_l, lid), (new_r, rid)) = age (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r mem)
    | AGt (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = agt (asem_aexp l m) (asem_aexp r m) in
        amem_update lid new_l (amem_update rid new_r mem)
        
(* [[S]] : astmt -> amem -> amem *)

(* Define union *)
(* u_val : interval -> interval -> interval *)
let u_val i1 i2 = 
    let { l = i1l ; u = i1u } = i1 in
    let { l = i2l ; u = i2u } = i2 in
    { l = min_flt [i1l ; i2l]; u = max_flt [i1u ; i2u] } ;;

let u_eterm e1 e2 = 
    match e1, e2 with
    | Eterm i1, Eterm i2 -> 
        Eterm { int = (u_val (i1.int) (i2.int));
                err = max_flt [i1.err ; i2.err] }
    | Eterm _,  Bot      -> e1
    | Bot,      Eterm _  -> e2 
    | Bot,      Bot      -> 
        raise (Failure "attempting to introduce a new variable during union
                       operation") ;;

(* u_mem : amem -> amem -> amem *)
let u_amem mem1 mem2 = 
    let { dom = dom1 ; lookup = m1 } = mem1 in
    let { dom = dom2 ; lookup = m2 } = mem2 in
    let dom3 = SS.union dom1 dom2 in
    { dom = dom3 ;
      lookup = fun x -> u_eterm (m1 x) (m2 x) } ;;

(* For loops require finding a fixpoint *)
(* fixpoint : ('a -> 'a) -> 'a -> 'a *)
let rec fixpoint f i = 
    let next = f i in
    if next = i
    then next
    else fixpoint f next ;;

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
    | ACol (s1, s2) -> asem_stmt s2 is (asem_stmt s1 is m) ;;

let abst_interp exp m = asem_stmt exp 20 m ;;
