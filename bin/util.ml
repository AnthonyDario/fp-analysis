open List

(* product_map f [a1; ...; an] [b1; ...; bm] = 
   [f a1 b1; f a1 b2; ... f a2 b1 ; f a2 b2 ; ... ; f an bm] *)
(* 'a -> 'b -> 'c -> 'a list -> 'b list -> 'c list *)
let product_map f xs ys = concat_map (fun x -> map (fun y -> f x y) ys) xs;;

let min_int l = List.fold_left Int.min Int.max_int l ;;
let max_int l = List.fold_left Int.max Int.min_int l ;;

let min_flt l = List.fold_left Float.min infinity l ;;
let max_flt l = List.fold_left Float.max neg_infinity l ;;

(* Ulp function *)
let ulp f = Float.succ f -. f ;;

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
