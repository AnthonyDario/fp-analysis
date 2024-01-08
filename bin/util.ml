open Float
open List

(* product_map f [a1; ...; an] [b1; ...; bm] = [f a1 b1; f a1 b2; ...; f an bm] *)
(* 'a -> 'b -> 'c -> 'a list -> 'b list -> 'c list *)
let product_map f xs ys = concat_map (fun x -> map (fun y -> f x y) ys) xs;;

let max_flt l = List.fold_left max neg_infinity l ;;
let min_flt l = List.fold_left min infinity l ;;

(* Ulp function *)
let ulp f = succ f -. f ;;
