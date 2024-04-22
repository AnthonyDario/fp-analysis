open List

(* product_map f [a1; ...; an] [b1; ...; bm] = 
   [f a1 b1; f a1 b2; ... f a2 b1 ; f a2 b2 ; ... ; f an bm] *)
let product_map (f : 'a -> 'b -> 'c) (xs : 'a list) (ys : 'b list) : 'c list = 
    (* let tot = (length xs) in *)
    let i = ref 0 in 
    let ret = concat_map (fun x -> 
        i := !i + 1;
        map (fun y -> f x y) ys) xs in
    ret ;;

let min_ints l = List.fold_left Int.min Int.max_int l ;;
let max_ints l = List.fold_left Int.max Int.min_int l ;;

let min_flt l = List.fold_left Float.min infinity l ;;
let max_flt l = List.fold_left Float.max neg_infinity l ;;

(* Ulp function *)
let ulp f = Float.succ f -. f ;;

(* Get the smallest divisor of a number that does not produce infinity *)
let smallest_finite_divisor (f : float) : float =
    f /. Float.max_float ;;

let fail_unwrap op =
    match op with
    | Some v -> v
    | None -> failwith "Unwrapped empty option" 
    ;;

let last lst = nth lst ((length lst) - 1) ;;
let rec remove_last lst = 
    match lst with
    | [] -> []
    | _ :: [] -> []
    | x :: xs -> x :: (remove_last xs) ;;
