open Sigs

module Coefficient = Poly.C
(*module Coefficient = struct 
  type coef = float 
  let addc = (+.) 
  let mulc = ( *. ) 
  let divc = (/.) 
  let is_zero = ((=) 0.) 
  let is_one = ((=) 1.) 
  let to_string_c = string_of_float 
  let from_string_c = float_of_string 
  let cmp = compare 
end*)

let mat_mult a b =
  let m = Array.length a in
  let n = Array.length a.(0) in
  let p = Array.length b in
  let q = Array.length b.(0) in
  if p = n then (
    let res = Array.make_matrix m q (Coefficient.from_string_c "0") in
    for i = 0 to (m-1) do
      for j = 0 to (q-1) do
        let colj = Array.make n (Coefficient.from_string_c "0") in
        for k = 0 to (n-1) do
          colj.(k) <- b.(k).(j)
        done;
        res.(i).(j) <- Array.fold_left (Coefficient.addc) (Coefficient.from_string_c "0") (Array.map2 (fun x y -> Coefficient.mulc x y) a.(i) colj)
      done
    done;
    res
  )
  else failwith "incompatible matrix dimensions"

let mat_mult_v a v =
  Array.map (fun row -> Array.fold_left Coefficient.addc (Coefficient.from_string_c "0") (Array.map2 Coefficient.mulc row v)) a
  
let rref b = 
  let get_pivot mat curr_c curr_r = 
    let matList = Array.to_list mat in
    let pivot_test k row = if not (Coefficient.is_zero row.(curr_c)) && k >= curr_r then k else -1 in
    match (List.find_opt ((<=) 0) (List.mapi pivot_test matList)) with
    | None -> -1
    | Some v -> v
  in 
  let swap l p mat = 
    let temp = mat.(l) in
    mat.(l) <- mat.(p);
    mat.(p) <- temp
  in
  let mult_const c row = Array.map (Coefficient.mulc c) row in
  let add_rows = Array.map2 Coefficient.addc in
  let a = Array.copy b in
  let m = Array.length a in
  let n = Array.length a.(0) in
  let t = Array.make_matrix m m (Coefficient.from_string_c "0") in
  let p = Array.make_matrix m m (Coefficient.from_string_c "0") in
  for j = 0 to m-1 do
    t.(j).(j) <- Coefficient.from_string_c "1";
    p.(j).(j) <- Coefficient.from_string_c "1"
  done;
  let curr_row = ref 0 in
  let curr_col = ref 0 in
  while !curr_row < m && !curr_col < n do
    let pivot = get_pivot a !curr_col !curr_row in
    if pivot >= 0 then (
      if pivot <> !curr_row then (swap pivot !curr_row a; swap pivot !curr_row t; swap pivot !curr_row p);
      let head_value = a.(!curr_row).(!curr_col) in
      a.(!curr_row) <- mult_const (Coefficient.divc (Coefficient.from_string_c "1") head_value) a.(!curr_row);
      t.(!curr_row) <- mult_const (Coefficient.divc (Coefficient.from_string_c "1") head_value) t.(!curr_row);
      for curr = 0 to m - 1 do
        if not (Coefficient.is_zero a.(curr).(!curr_col)) && curr <> !curr_row then (
          let neg_coef = Coefficient.mulc (Coefficient.from_string_c "-1") a.(curr).(!curr_col) in
          let new_row = add_rows (mult_const neg_coef (a.(!curr_row))) (a.(curr)) in
          let new_row_t = add_rows (mult_const neg_coef (t.(!curr_row))) (t.(curr)) in
          t.(curr) <- new_row_t;
          a.(curr) <- new_row)
      done;
      curr_row := !curr_row + 1;);
    curr_col := !curr_col + 1;
  done;
  (a, t, p)

let transpose mat m n = 
  let res = Array.make_matrix n m mat.(0).(0) in
  for i = 0 to (n-1) do
    for j = 0 to (m-1) do
      res.(i).(j) <- mat.(j).(i)
    done
  done;
  res

let trans mat = 
  let m = Array.length mat in
  let n = Array.length mat.(0) in
  transpose mat m n


let left_non_zero row = Array.fold_left (fun acc ind -> if acc < 0 && ind >= 0 then ind else acc) (-1) (Array.mapi (fun k value -> if Coefficient.is_zero value then -1 else k) row)

let invert_matrix mat = 
  let size = Array.length mat in
  if Array.length (mat.(0)) <> size then failwith "Non Square matrix"
  else
    let ident = Array.mapi (fun i _ -> Array.mapi (fun j _ -> if i = j then Coefficient.from_string_c "1" else Coefficient.from_string_c "0") mat) mat in
    let (r, _, _) = rref (Array.mapi (fun i _ -> Array.append mat.(i) ident.(i)) mat) in
    if Array.for_all (fun b -> b) (Array.mapi (fun i row -> Coefficient.is_one row.(i)) r) then
      Array.map (fun row -> Array.sub row size size) r
    else failwith "Matrix is singular"
    
let lu b = 
  let get_pivot mat curr_c curr_r = 
    let matList = Array.to_list mat in
    let pivot_test k row = if not (Coefficient.is_zero row.(curr_c)) && k >= curr_r then k else -1 in
    match (List.find_opt ((<=) 0) (List.mapi pivot_test matList)) with
    | None -> -1
    | Some v -> v
  in 
  let swap l p mat = 
    let temp = mat.(l) in
    mat.(l) <- mat.(p);
    mat.(p) <- temp
  in
  let mult_const c row = Array.map (Coefficient.mulc c) row in
  let add_rows = Array.map2 Coefficient.addc in
  let a = Array.copy b in
  let m = Array.length a in
  let n = Array.length a.(0) in
  let p = Array.make_matrix m m (Coefficient.from_string_c "0") in
  let l = Array.make_matrix m m (Coefficient.from_string_c "0") in
  for j = 0 to m-1 do
    p.(j).(j) <- Coefficient.from_string_c "1";
    l.(j).(j) <- Coefficient.from_string_c "1"
  done;
  let curr_row = ref 0 in
  let curr_col = ref 0 in
  while !curr_row < m && !curr_col < n do
    let pivot = get_pivot a !curr_col !curr_row in
    if pivot >= 0 then (
      if pivot <> !curr_row then (swap pivot !curr_row a; swap pivot !curr_row p);
      for curr = !curr_row + 1 to m - 1 do
        if not (Coefficient.is_zero a.(curr).(!curr_col)) then (
          let piv_val = a.(!curr_row).(!curr_col) in
          let coe_to_clear = a.(curr).(!curr_col) in
          let multiplier = Coefficient.mulc (Coefficient.from_string_c "-1") (Coefficient.divc piv_val coe_to_clear) in
          let new_row = add_rows (mult_const multiplier (a.(!curr_row))) (a.(curr)) in
          let new_row_t = add_rows (mult_const multiplier (l.(!curr_row))) (l.(curr)) in
          l.(curr) <- new_row_t;
          a.(curr) <- new_row)
      done;
      curr_row := !curr_row + 1;);
    curr_col := !curr_col + 1;
  done;
  (a, invert_matrix l, l, p);;


let max_project a b =
  let at = trans a in
  let bt = Array.map (Array.map (Coefficient.mulc (Coefficient.from_string_c "-1"))) (trans b) in
  let s = Array.map2 (fun arow brow -> Array.append arow brow) at bt in
  let iden = Array.mapi (fun i _ -> 
    let res = Array.make (Array.length s.(0)) (Coefficient.from_string_c "0") in 
    res.(i) <- Coefficient.from_string_c "1";
    res) (Array.make (Array.length s.(0)) "") in
  let sid = Array.append s iden in
  let sidt = trans sid in
  let (r, _, _) = rref sidt in
  let rlist = Array.to_list r in
  let basrows = List.filter (fun row -> Array.for_all Coefficient.is_zero (Array.sub row 0 (Array.length s))) rlist in
  let basis = ref (Array.of_list (List.map (fun row -> Array.sub row (Array.length s) ((Array.length (row)) - (Array.length s))) basrows)) in
  for j = 1 to Array.length a do
    let num_nonzero_rows = Array.fold_left (fun acc v -> if Coefficient.is_zero v.(0) then acc else acc+1) 0 !basis in
    if num_nonzero_rows <= 1 then
      basis := Array.map (fun row -> Array.sub row 1 ((Array.length row) - 1)) !basis
    else
      let (new_basis, _, _) = rref !basis in
      basis := new_basis
  done;
  let (rp, _, _) = rref !basis in
  Array.of_list (List.filter (fun x -> not (Array.for_all Coefficient.is_zero x)) (Array.to_list rp))


let mat_div d a =
  let x = Array.length d in
  let z = Array.length d.(0) in
  let y = Array.length a in
  if (Array.length a.(0) = z) then
    let res = Array.make_matrix x y (Coefficient.from_string_c "0") in
    let is_zero v = Array.for_all Coefficient.is_zero v in
    let vec_sub = Array.map2 (fun i j -> Coefficient.addc i (Coefficient.mulc j (Coefficient.from_string_c "-1"))) in
    let dot f g = Array.fold_left (fun acc v -> Coefficient.addc acc v) (Coefficient.from_string_c "0") (Array.map2 Coefficient.mulc f g) in
    let alistrow = List.filter (fun (_,c) -> not (is_zero c)) (Array.to_list (Array.mapi (fun i row -> (i, row)) a)) in
    let outer i current =
      let ord k (_, rowu) (_, rowv) =
        let uind = left_non_zero rowu in
        let vind = left_non_zero rowv in
          if uind <k && vind < k || uind>=k && vind>=k then
            compare uind vind
          else if uind <=k then
            1
          else 
            -1
      in
      let red_order = List.sort (ord (left_non_zero current)) alistrow in
      let reduced = 
        List.fold_left 
          (fun curr (index, arow) -> 
            let multiplier = Coefficient.divc (dot curr arow) (dot arow arow) in
            res.(i).(index) <- multiplier;
            vec_sub curr (Array.map (Coefficient.mulc multiplier) arow)
          )
          (Array.copy current)
          red_order
      in
      if not (is_zero reduced) then false
      else true
    in
    let succ = Array.mapi outer d in
    (res, succ)
  else failwith "Incompatible matrix dimensions"


let zass a b =
  let n = Array.length a in
  let m = Array.length a.(0) in
  let k = Array.length b in
  if Array.length b.(0) = m then
    let s = Array.mapi 
      (fun i row ->
        if i < n then Array.append a.(i) a.(i)
        else Array.append b.(i-n) (Array.make m (Coefficient.from_string_c "0"))
        ) (Array.make (n+k) (""))
      in
    let (r, _, _) = rref s in
    let start = 
      (Array.fold_left
        (fun acc v -> max acc v) 
        (-1)
        (Array.mapi 
          (fun i row -> 
            if Coefficient.is_zero row.(m-1) then
              -1
            else i
          ) r)) + 1
    in
    let temp = Array.sub (Array.map (fun row -> Array.sub row m m) r) start (n+k - start) in
    let non_zero_rows = Array.fold_left (fun acc row -> if Array.for_all Coefficient.is_zero row then acc else acc+1) 0 temp in
    Array.sub temp 0 non_zero_rows
  else failwith "Incompatible dimensions"


module AffineT = struct

  type coef = Coefficient.coef
  let coef_from_string : string -> coef = Coefficient.from_string_c

  let get_sim_strings vars sim = 
    let temp = Array.map 
      (fun row ->
        String.concat ""
          (List.map2 
            (fun co v -> 
              if Coefficient.is_zero co then ""
              else if Coefficient.is_one co then "+" ^ v
              else if Coefficient.cmp co (Coefficient.from_string_c "-1") = 0 then "-" ^ v
              else if Coefficient.cmp co (Coefficient.from_string_c "0") < 0 then
                  (Coefficient.to_string_c co) ^ v
              else
                "+" ^ (Coefficient.to_string_c co) ^ v
            )
            (Array.to_list row)
            vars
            )) sim
    in
    let temp_p = Array.map 
      (fun row ->
        String.concat ""
          (List.map2 
            (fun co v -> 
              if Coefficient.is_zero co then ""
              else if Coefficient.is_one co then "+" ^ v ^ "'"
              else if Coefficient.cmp co (Coefficient.from_string_c "-1") = 0 then "-" ^ v ^ "'"
              else if Coefficient.cmp co (Coefficient.from_string_c "0") < 0 then
                  (Coefficient.to_string_c co) ^ v ^ "'"
              else
                "+" ^ (Coefficient.to_string_c co) ^ v ^ "'"
            )
            (Array.to_list row)
            vars
            )) sim
    in
    let temp = Array.map (fun s -> if String.get s 0 = '+' then String.sub s 1 ((String.length s)-1) else s) temp in
    let temp_p = Array.map (fun s -> if String.get s 0 = '+' then String.sub s 1 ((String.length s)-1) else s) temp_p in
    let max_width = Array.fold_left (fun acc s -> if String.length s > acc then String.length s else acc) (-1) temp in
    let max_width_p = Array.fold_left (fun acc s -> if String.length s > acc then String.length s else acc) (-1) temp_p in
    (Array.map (fun s -> let spaces = String.make (max_width - (String.length s)) ' ' in s^spaces) temp,
    Array.map (fun s -> let spaces = String.make (max_width_p - (String.length s)) ' ' in s^spaces) temp_p)

  let get_mat_widths mat = 
    let n = Array.length mat.(0) in
    Array.fold_left (fun acc row -> Array.map2 (fun x y -> max x y) acc row) (Array.make n (-1)) (Array.map (fun row -> Array.map (fun v -> String.length (Coefficient.to_string_c v)) row) mat) 

  let mat_row_to_string row widths = 
    let el_to_string i v = 
      let val_str = Coefficient.to_string_c v in
      let val_len = String.length val_str in
      let spaces = String.make (widths.(i) - val_len) ' ' in
      if i = 0 then spaces ^ val_str
      else " " ^ spaces ^ val_str
    in
    "|" ^ (String.concat " " (Array.to_list (Array.mapi el_to_string row))) ^ "|" 

  let affine_to_string a b c =
    let aw = get_mat_widths a in
    let bw = get_mat_widths b in
    let cmat = Array.mapi (fun i _ -> Array.make 1 c.(i)) a in
    let cw = get_mat_widths cmat in
    let row i = 
      if i = (Array.length a) / 2 then (mat_row_to_string a.(i) aw) ^ " = " ^ (mat_row_to_string b.(i) bw) ^ " + " ^ (mat_row_to_string cmat.(i) cw)
      else (mat_row_to_string a.(i) aw) ^ "   " ^ (mat_row_to_string b.(i) bw)^ "   " ^ (mat_row_to_string cmat.(i) cw)
    in
    String.concat "\n" (Array.to_list (Array.mapi (fun r _ -> row r) a))

  let alg_to_affine polys pre_post = 
    let lin_polys = Poly.Eliminate.affine_hull polys in
    let a = Array.make_matrix (List.length lin_polys) (List.length pre_post) (coef_from_string "0") in
    let b = Array.make_matrix (List.length lin_polys) (List.length pre_post) (coef_from_string "0") in
    let c = Array.make (List.length lin_polys) (coef_from_string "0") in
    List.iteri (fun i (Sum lin_term) ->
      List.iter (fun m ->
        let coefic = Poly.Mon.get_coef m in
        match (Poly.Eliminate.get_vars_m m) with
        | [] -> c.(i) <- Coefficient.mulc (Coefficient.from_string_c "-1") coefic
        | var :: [] ->
          let (j, is_post) = 
            List.find (fun (k, _) -> k>= 0)
              (List.mapi (fun l (pre, post) -> 
                if var = pre then (l, false)
                else if var = post then (l, true)
                else (-1, false)
             ) pre_post)
            in
          if is_post then a.(i).(j) <- coefic
          else b.(i).(j) <- Coefficient.mulc (Coefficient.from_string_c "-1") coefic
        | _ -> failwith "Nonlinear monomial"
      ) lin_term
    ) lin_polys;
    let s = Array.mapi (fun i _ -> Array.append (Array.append a.(i) b.(i)) ([|c.(i)|])) a in
    let (r, _, p) = rref s in
    (*let make_leading_coef_pos i _ =
      let leading_non_zero = 
        let temp = Array.fold_left 
          (fun acc v -> 
            if Coefficient.is_zero v || not (Coefficient.is_zero acc) then acc 
            else v)
          (Coefficient.from_string_c "0")
          a.(i)
        in
        if Coefficient.is_zero temp then
          Array.fold_left 
          (fun acc v -> 
            if Coefficient.is_zero v || not (Coefficient.is_zero acc) then acc 
            else v)
          (Coefficient.from_string_c "0")
          b.(i)
        else temp
      in
      if (Coefficient.cmp leading_non_zero (Coefficient.from_string_c "0"))>= 0 then ()
      else
        let newrowa = Array.map (fun v -> Coefficient.mulc (Coefficient.from_string_c "-1") v) a.(i) in
        let newrowb = Array.map (fun v -> Coefficient.mulc (Coefficient.from_string_c "-1") v) b.(i) in
        let newc = Coefficient.mulc (Coefficient.from_string_c "-1") c.(i) in
        a.(i) <- newrowa;
        b.(i) <- newrowb;
        c.(i) <- newc
    in
    Array.iteri make_leading_coef_pos a;*)
    let width = Array.length r.(0) in
    let awidth = Array.length a.(0) in
    let extract_matrices row = 
      let ab = Array.sub row 0 (width - 1) in
      if (Array.for_all Coefficient.is_zero ab) then
        if Coefficient.is_zero row.(width - 1) then
          failwith "Linear Dependency. Should have been handled by Grob"
        else failwith ""
      else
      (Array.sub row 0 awidth, Array.sub row awidth awidth, row.(width - 1))
    in
    let rlistsplit = List.map extract_matrices (Array.to_list r) in
    let (ualist, ublist, uclist) = List.fold_left (fun (acca, accb, accc) (ar, br, cr) -> (ar :: acca, br :: accb, cr :: accc)) ([],[],[]) rlistsplit in
    let (ua, ub, uc) = (Array.of_list (List.rev ualist), Array.of_list (List.rev ublist), Array.of_list (List.rev uclist)) in
    (mat_mult p ua, mat_mult p ub, mat_mult_v p uc, List.map fst pre_post)
  
  let tats_to_string a m c =
    let aw = get_mat_widths a in
    let mw = get_mat_widths m in
    let cmat = Array.mapi (fun i _ -> Array.make 1 c.(i)) a in
    let cw = get_mat_widths cmat in
    let row i = 
      if i = (Array.length a) / 2 then (mat_row_to_string a.(i) aw) ^ " = " ^ (mat_row_to_string m.(i) mw)^(mat_row_to_string a.(i) aw) ^ " + " ^ (mat_row_to_string cmat.(i) cw)
      else (mat_row_to_string a.(i) aw) ^ "   " ^ (mat_row_to_string m.(i) mw) ^(mat_row_to_string a.(i) aw)^ "   " ^ (mat_row_to_string cmat.(i) cw)
    in
    String.concat "\n" (Array.to_list (Array.mapi (fun r _ -> row r) a))

  let dats_to_string t little_t d little_d vars sim =
    let tw = get_mat_widths t in
    let dw = get_mat_widths d in
    let dize = Array.length d in
    let blankdrow = String.make (String.length (mat_row_to_string d.(0) dw)) ' ' in
    let ltmat = Array.mapi (fun i _ -> Array.make 1 little_t.(i)) little_t in
    let ldmat = Array.mapi (fun i _ -> Array.make 1 little_d.(i)) little_d in
    let ltw = get_mat_widths ltmat in
    let ldw = get_mat_widths ldmat in
    let (var_string, var_string_p) = get_sim_strings vars sim in
    let row i = 
      if i = (Array.length t) / 2 && i < dize then 
        "|" ^ (var_string_p.(i)) ^ "| = " ^ (mat_row_to_string t.(i) tw) ^ "|" ^ (var_string.(i)) ^ "|" ^ " + " ^ (mat_row_to_string ltmat.(i) ltw) ^ 
        "  /\\  " ^ (mat_row_to_string d.(i) dw) ^ "|" ^ (var_string.(i)) ^ "| = " ^ (mat_row_to_string ldmat.(i) ldw)
      else if i = (Array.length t) / 2 then 
        "|" ^ (var_string_p.(i)) ^ "| = " ^ (mat_row_to_string t.(i) tw) ^ "|" ^ (var_string.(i)) ^ "|" ^ " + " ^ (mat_row_to_string ltmat.(i) ltw) ^ 
        "  /\\  " ^ blankdrow ^ "|" ^ (var_string.(i)) ^ "| = "
      else if i < dize then
        "|" ^ (var_string_p.(i)) ^ "|   " ^ (mat_row_to_string t.(i) tw) ^ "|" ^ (var_string.(i)) ^ "|" ^ "   " ^ (mat_row_to_string ltmat.(i) ltw) ^ 
        "      " ^ (mat_row_to_string d.(i) dw) ^ "|" ^ (var_string.(i)) ^ "|   " ^ (mat_row_to_string ldmat.(i) ldw)
      else
        "|" ^ (var_string_p.(i)) ^ "|   " ^ (mat_row_to_string t.(i) tw) ^ "|" ^ (var_string.(i)) ^ "|" ^ "   " ^ (mat_row_to_string ltmat.(i) ltw) ^ 
        "      " ^ blankdrow ^ "|" ^ (var_string.(i)) ^ "|"
    in
    String.concat "\n" (Array.to_list (Array.mapi (fun r _ -> row r) t))

  let affine_to_dats init_a init_b init_c vars =
    let rec aux curr_a curr_b curr_c curr_t = 
      let (dyn, divsuc) = mat_div curr_b curr_a in
      (*if Array.for_all (fun x -> x) divsuc then (curr_a, dyn, curr_c, curr_t)*)
      if Array.for_all (fun x -> x) divsuc then (curr_a, curr_b, curr_c, curr_t)
      else
        let tnew = max_project curr_a curr_b in
        aux (mat_mult tnew curr_a) (mat_mult tnew curr_b) (mat_mult_v tnew curr_c) tnew
    in
    (*let (a, m, c, sim) = aux init_a init_b init_c (Array.make_matrix 1 1 (Coefficient.from_string_c "0")) in*)
    let (a, b, c, sim) = aux init_a init_b init_c (Array.make_matrix 1 1 (Coefficient.from_string_c "0")) in
    let (u, l, li, p) = lu a in
    let (l, li) = (mat_mult p l, mat_mult li p) in
    let zero_rows = Array.fold_left (fun acc row -> if Array.for_all Coefficient.is_zero row then acc + 1 else acc) 0 u in
    let total_rows = Array.length u in

    let (dyn_mat, _) = mat_div (mat_mult li b) (Array.sub u 0 (total_rows - zero_rows)) in

    (*let dyn_mat = mat_mult (mat_mult li m) l in*)
    let add_mat = mat_mult_v li c in
    if zero_rows = 0 then
      (dyn_mat, add_mat, Array.make_matrix 1 (Array.length dyn_mat.(0)) (Coefficient.from_string_c "0"), Array.make 1 (Coefficient.from_string_c "0"), u)
    else
      (*let t = Array.sub (Array.map (fun row -> Array.sub row 0 (total_rows-zero_rows)) dyn_mat) 0 (total_rows-zero_rows) in
      let d = Array.sub (Array.map (fun row -> Array.sub row 0 (total_rows-zero_rows)) dyn_mat) (total_rows - zero_rows) zero_rows in*)

      let t = Array.sub dyn_mat 0 (total_rows-zero_rows) in
      let d = Array.sub dyn_mat (total_rows - zero_rows) zero_rows in

      let little_t = Array.sub add_mat 0 (total_rows - zero_rows) in
      let little_d = Array.map (Coefficient.mulc (Coefficient.from_string_c "-1")) (Array.sub add_mat (total_rows-zero_rows) zero_rows) in
      let s = Array.sub u 0 (total_rows-zero_rows) in
      let diag mat = 
        Array.mapi
          (fun ind m_row ->
            let temp = Array.make (Array.length mat) (Coefficient.from_string_c "0") in
            let left_c = left_non_zero m_row in
            (if left_c < 0 then
              temp.(ind) <- Coefficient.from_string_c "1"
            else if Coefficient.cmp m_row.(left_non_zero m_row) (Coefficient.from_string_c "0") < 0 then
              temp.(ind) <- Coefficient.from_string_c "-1"
            else
              temp.(ind) <- Coefficient.from_string_c "1");
            temp
            )
           mat
      in
      let s_unit_norm = diag s in
      let new_sim = mat_mult s_unit_norm s in
      let new_little_t = mat_mult_v s_unit_norm little_t in
      let temp_d = mat_mult d s_unit_norm in
      let d_unit_norm = diag temp_d in
      let new_d = mat_mult d_unit_norm temp_d in
      let new_little_d = mat_mult_v d_unit_norm little_d in
      (t, new_little_t, new_d, new_little_d, new_sim)

  let alg_to_dats polys pre_post = 
    let (a, b, c, vars) = alg_to_affine polys pre_post in
    let (t, little_t, d, little_d, s) = affine_to_dats a b c vars in
    (t, little_t, d, little_d, s, vars)

end 

let p1 = Poly.Polynomial.from_string "x'-y'-x+y-2";;
let p2 = Poly.Polynomial.from_string "z'-z-x^2+2xy-y^2";;
let p3 = Poly.Polynomial.from_string "x-3";;
let p4 = Poly.Polynomial.from_string "y";;
let p5 = Poly.Polynomial.from_string "z+3";;
let p6 = Poly.Polynomial.from_string "x'-x - 5";;
let (t, litte_t, d, little_d, sim, vars) = AffineT.alg_to_dats [p1;p2;p3;p4;p5;p6] [("x", "x'"); ("y", "y'"); ("z","z'")];;
print_endline (AffineT.dats_to_string t litte_t d little_d vars sim)
