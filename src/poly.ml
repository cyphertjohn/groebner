open Sigs

let var_power_to_string (Exp(x, e)) = if e > 1 then x ^ "^" ^ (string_of_int e) else x

let get_deg (Exp (v, e)) = e 

let cmp_var (Exp(x, e1)) (Exp(y, e2)) = if compare x y = 0 then compare e1 e2 else -1 * (compare x y)

let sort_monic_mon (Prod l) = 
  let remove_one = List.filter (fun (Exp(_, e)) -> e <> 0) l in
  Prod (List.rev (List.sort cmp_var remove_one))

let mult_var_mon (Exp (var, e)) (Prod l) = 
  if (List.exists (fun (Exp (s, _)) -> var = s) l) then
    Prod (List.map (fun (Exp (s, e2)) -> if (s = var) then Exp (s, e + e2) else Exp (s, e2)) l)
  else sort_monic_mon (Prod ((Exp(var,e)) :: l))

let monic_mon_to_string m = String.concat "" (List.map var_power_to_string (match (sort_monic_mon m) with | Prod l -> l))

let rec lex_ord a b = 
  match (sort_monic_mon a, sort_monic_mon b) with
  | (Prod [], Prod []) -> 0
  | (Prod [], _) -> -1
  | (_, Prod []) -> 1
  | (Prod (x :: xs), Prod (y :: ys)) -> if cmp_var x y = 0 then lex_ord (Prod xs) (Prod ys)
                          else cmp_var x y

let total_deg (Prod m) = List.fold_left (+) 0 (List.map get_deg m)

let grlex_ord a b =
  if compare (total_deg a) (total_deg b) = 0 then lex_ord a b
  else compare (total_deg a) (total_deg b)

(*let grevlex_ord a b = 
  if compare (total_deg a) (total_deg b) = 0 then (
    let (Prod a_sort, Prod b_sort) = (sort_monic_mon a, sort_monic_mon b) in
    let rec aux alist blist =
      match (alist, blist) with
      | (((Exp (x, e1)) :: rest_a), ((Exp (y, e2)):: rest_b)) -> 
        if x = y && e1 = e2 then aux rest_a rest_b
        else if x = y then (-1) * (e1 - e2)
        else compare y x
      | (x :: xs, []) -> 1
      | ([], x :: xs) -> -1
      | _ -> 0
    in
    aux (List.rev a_sort) (List.rev b_sort)
  )
  else compare (total_deg a) (total_deg b) *)

let sort_monomial (coef, mon) = (coef, sort_monic_mon mon)

let monomial_to_string (Coef c, Prod m) = if m = [] then string_of_float c else if c <> 1. then (string_of_float c) ^ (monic_mon_to_string (Prod m)) else (monic_mon_to_string (Prod m))

let get_monic_mon (Coef c, mon) = mon

let get_coef (Coef c, Prod mon) = c
 
let mult_mon a b = 
  let new_coef = (get_coef a) *. (get_coef b) in
  if (new_coef = 0.) then (Coef 0., Prod [])
  else 
    let (Prod l1, Prod l2) = (get_monic_mon a, get_monic_mon b) in
    match (l1, l2) with
    | ([], _) -> sort_monomial (Coef new_coef, Prod l2)
    | (_, []) -> sort_monomial (Coef new_coef, Prod l1)
    | _ -> 
      let new_monic = List.fold_left (fun acc y-> mult_var_mon y acc) (Prod l1) l2 in
      (Coef new_coef, new_monic)

let divide_mon a b = 
  let new_coef = (get_coef a) /. (get_coef b) in
  let (Prod vars) = get_monic_mon b in
  if vars = [] then Some (Coef new_coef, get_monic_mon a)
  else 
    let (Prod alist) = get_monic_mon a in
    let var_divide acc (Exp (bvar, be)) = 
      let (Exp (avari, ae)) = List.find (fun (Exp (avar, _)) -> avar = bvar) acc in
      if ae >= be then List.map (fun (Exp (v, e)) -> if v = bvar then Exp (v, e - be) else Exp (v, e)) acc
      else raise Not_found
    in
    try
      Some (sort_monomial (Coef new_coef, Prod (List.fold_left var_divide alist vars)))
    with Not_found -> None

let lcm (Prod a) (Prod b) = 
  let rec aux x y acc =
    match (x, y) with
    | ([], _) -> y @ acc
    | (_, []) -> x @ acc
    | (Exp(xvar, e1) :: xs, Exp(yvar, e2) :: ys) -> 
      if xvar = yvar then Exp(xvar, max e1 e2) :: (aux xs ys acc)
      else if xvar < yvar then Exp(xvar, e1) :: (aux xs y acc)
      else Exp(yvar, e2) :: (aux ys x acc)
  in
  sort_monic_mon (Prod (aux a b []))

module Make () = struct

  let ord = ref lex_ord

  let set_ord order = ord := order

  type polynomial = Sigs.polynomial

  let mon_ord (Coef c1, m1) (Coef c2, m2) = if !ord m1 m2 = 0 then compare c1 c2 else !ord m1 m2

  let sort_poly (Sum poly) = 
    let remove_zero = List.filter (fun (Coef c, _) -> c <> 0.) (List.map sort_monomial poly) in
    if remove_zero = [] then (Sum [(Coef 0., Prod [])])
    else Sum (List.rev (List.sort mon_ord remove_zero))

  let lt poly = let (Sum sorted) = sort_poly poly in List.hd sorted 

  let lm poly = get_monic_mon (lt poly)

  let lc poly = let (Coef c, _) = lt poly in c

  let add_mon (Coef c1, m) (Sum a) =
    if a = [] then Sum [(Coef c1, m)]
    else if (List.exists (fun (Coef _, m2) -> !ord m m2 = 0) a) then
      Sum (List.map (fun (Coef c2, m2) -> if !ord m m2 = 0 then (Coef (c1 +. c2), m) else (Coef c2, m2)) a)
    else Sum ((Coef c1, m) :: a)

  let add (Sum p1) p2 = 
    sort_poly (List.fold_left (fun acc x -> add_mon x acc) p2 p1)

  let mult_mon_poly mon (Sum p2) = Sum (List.map (fun x -> mult_mon mon x) p2)

  let mult (Sum p1) p2 = 
    sort_poly (List.fold_left (fun acc x -> add (mult_mon_poly x p2) acc) (Sum []) p1)
  
  let to_string (Sum p) = 
    String.concat " + " (List.map monomial_to_string p)

  let is_zero p = (Sum [(Coef 0., Prod [])]) = sort_poly p

  let compare p1 p2 = 
    let rec aux (Sum a) (Sum b) = 
      match (a, b) with 
      | ([], []) -> 0
      | ([], _) -> -1
      | (_, []) -> 1
      | (x :: xs, y :: ys) -> if mon_ord x y = 0 then aux (Sum xs) (Sum ys) else mon_ord x y
    in
    aux (sort_poly p1) (sort_poly p2)

  let from_string s = 
    sort_poly (PolyParse.main PolyLexer.token (Lexing.from_string s))

  let minus_1 = Sum [(Coef (-1.), Prod [])]

  let division divisors f =
    let r = ref (sort_poly (Sum [])) in
    let mults = ref (List.map (fun _ -> sort_poly (Sum [])) divisors) in
    let s = List.length divisors in
    let p = ref f in
    while (!p <> (Sum [(Coef 0., Prod [])])) do (
      let i = ref 1 in
      let division_occurred = ref false in
      while (!i <= s && not (!division_occurred)) do (
        let fi = List.nth divisors (!i - 1) in
        match divide_mon (lt !p) (lt fi) with
        | None -> i := !i + 1
        | Some new_mon -> (
          mults := List.mapi (fun j a -> if j= (!i-1) then add a (Sum [new_mon]) else a) !mults;
          p := add !p (mult minus_1 (mult (Sum [new_mon]) fi));
          division_occurred := true)
      )
      done;
      if not (!division_occurred) then (
        r := add !r (Sum [lt !p]);
        p := add !p (mult (Sum [(lt !p)]) minus_1))
    )
    done;
    (!mults, !r)

  let s_poly f g =
    let lcmlm = lcm (lm f) (lm g) in
    let f_m = divide_mon (Coef 1., lcmlm) (lt f) in
    let g_m = divide_mon (Coef 1., lcmlm) (lt g) in
    match (f_m, g_m) with
    | (Some f_t, Some g_t) ->
      add (mult (Sum [f_t]) f) (mult minus_1 (mult (Sum [g_t]) g))
    | _ -> failwith "shouldn't happen"

  let buchberger (fs : polynomial list) = 
    let g = ref fs in
    let g_p = ref [] in
    while (!g <> !g_p) do
      g_p := !g;
      let get_pairs l = List.filter (fun (x, y) -> x<>y) (fst(List.fold_left (fun (acc, l1) x -> (acc @ (List.map (fun y -> (x, y)) l1),List.tl l1)) ([],l) l)) in
      let pairs = get_pairs !g_p in
      List.iter (fun (x, y) ->
        let s = snd (division !g_p (s_poly x y)) in
        if not (is_zero s) then g := s :: !g
      ) pairs
    done;
    !g

  let improved_buchberger (fs : polynomial list) = 
    let rec aux worklist g fss=
      match worklist with
      | [] -> g
      | (fi, fj) :: rest ->
        let lcmlt = lcm (lm fi) (lm fj) in (* lt or lm? *)
        let prod = get_monic_mon (mult_mon (lt fi) (lt fj)) in
        if lcmlt = prod then aux rest g fss (* criterion *)
        else (
          let s = snd (division g (s_poly fi fj)) in
          print_endline (to_string s);
          if is_zero s then aux rest g fss
          else (
            aux (worklist @ (List.map (fun f -> (f, s)) fss)) (s :: g) (fss @ [s])
          )
        )
    in
    let get_pairs l = List.filter (fun (x, y) -> x<>y) (fst(List.fold_left (fun (acc, l1) x -> (acc @ (List.map (fun y -> (x, y)) l1),List.tl l1)) ([],l) l)) in
    aux (get_pairs fs) fs fs

  let minimal_grobner fs = 
    let grobner_basis = improved_buchberger fs in
    let monic_grobner = List.map 
      (fun poly -> 
        let lc = lc poly in
        mult (Sum [(Coef (1. /. lc), Prod [])]) poly
      ) grobner_basis in
    let is_need poly l = 
      let others = List.filter (fun p -> p <> poly) l in
      let divides x = match divide_mon (lt poly) (lt x) with | Some _ -> true | None -> false in
      not (List.exists divides others)
    in
    let rec filter candidates =
      match List.find_opt (fun x -> not (is_need x candidates)) candidates with
      | None -> candidates
      | Some poly -> filter (List.filter (fun x -> x <> poly) candidates)
    in
    filter monic_grobner

end

module Polynomial = Make ()

module Eliminate = struct

  let order = ref (let default = ref [] in let () = String.iter (fun c -> default := (Char.escaped c):: !default) "zyxwvutsrqponmlkjihgfedcba" in !default)

  let compare_var_s s1 s2 = 
    if (s1 = s2) then 0
    else if (List.find (fun v -> v = s1 || v = s2) !order) = s1 then (-1)
    else 1

  let compare_var (Exp (s1, e1)) (Exp (s2, e2)) = 
    if (s1 = s2) then compare e1 e2
    else compare_var_s s1 s2
  
  let multi_deg (Prod a) =
    let find_deg v = 
      match List.find_opt (fun (Exp (x, _)) -> x = v) a with
      | None -> 0
      | Some (Exp (_, c)) -> c
    in
    List.map find_deg !order

  let grevlex_ord a b = 
    let (adeg, bdeg) = (multi_deg a, multi_deg b) in
    let (tota, totb) = (List.fold_left (+) 0 adeg, List.fold_left (+) 0 bdeg) in
    if tota = totb then (
      try (-1) * (List.find ((<>) 0) (List.rev (List.map2 (-) adeg bdeg)))
      with Not_found -> 0)
    else compare tota totb
    
  let weight_order a b weight ord =
    let (adeg, bdeg) = (multi_deg a, multi_deg b) in
    let (ares, bres) = (List.fold_left2 (fun acc x y -> acc + (x * y)) 0 weight adeg, List.fold_left2 (fun acc x y -> acc + (x * y)) 0 weight bdeg) in
    if ares = bres then ord a b
    else compare ares bres
    
  let elimination_order vars_to_remove a b = 
    let weight = List.map (fun x -> if (List.exists ((=) x) vars_to_remove) then 1 else 0) !order in
    weight_order a b weight grevlex_ord

  let get_vars_m (_, Prod mon) = 
    List.map (fun (Exp (v, _)) -> v) mon

  let set_var_order polys vars =
    let get_vars (Sum poly) = List.concat (List.map get_vars_m poly) in
    let variables = List.concat (List.map get_vars polys) in
    let rec remove_dupes vs acc =
      match vs with
      | [] -> acc
      | v :: rest ->
        match (List.find_opt ((=) v) vars, List.find_opt ((=) v) acc)  with
        | (None, None) -> remove_dupes rest (v :: acc)
        | _ -> remove_dupes rest acc
    in
    order := (List.sort compare vars) @ (List.sort compare (remove_dupes variables []))

  let mon_cont_var v (_, Prod mon) = List.exists (fun (Exp (x, _)) -> x = v) mon

  let poly_cont_var v (Sum poly) = List.exists (mon_cont_var v) poly

  let eliminate polys remove =
    set_var_order polys remove;
    Polynomial.set_ord (elimination_order remove);
    let g = Polynomial.minimal_grobner polys in
    List.filter (fun poly -> not (List.exists (fun v -> poly_cont_var v poly) remove)) g

end


let p1 = Sum [(Coef 1., Prod[Exp("x",2);Exp("y",1)]); (Coef (-1.), Prod[])];;

let p2 = Sum [(Coef 1., Prod[Exp("x",1);Exp("y",2)]); (Coef (-1.), Prod[Exp("x",1)])];;

let p3 = Sum [(Coef 1., Prod [Exp ("x", 3)]); (Coef (-2.), Prod [Exp ("x", 1); Exp ("y", 1)])];;

let p4 = Sum [(Coef 1., Prod [Exp ("x", 2); Exp("y", 1)]); (Coef (-2.), Prod [Exp ("y", 2)]); (Coef (1.), Prod [Exp ("x", 1)])];;

let f1 = Polynomial.from_string "t^2+x^2+y^2+z^2";;
let f2 = Polynomial.from_string "t^2+2x^2-xy-z^2";;
let f3 = Polynomial.from_string "t+y^3-z^3";;

let print_list l = List.iter (fun poly -> print_endline (Polynomial.to_string poly)) l;;

let m1 = Sigs.Prod [Exp("x", 2)];;
let m2 = Sigs.Prod [Exp("x", 1);Exp("y",1)];;
let m3 = Sigs.Prod [Exp("y", 2)];;
let m4 = Sigs.Prod [Exp("x", 1);Exp("z",1)];;
let m5 = Sigs.Prod [Exp("y", 1);Exp("z",1)];;
let m6 = Sigs.Prod [Exp("z", 2)];;