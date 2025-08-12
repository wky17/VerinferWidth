open Extraction
open Hifirrtl_lang
open Useocamlscc
open Printf
open Transhiast
open Mlir_lang
open Extraction.Constraints
open Extraction.Extract_cswithmin

let split2_tailrec l =
  let rec aux acc = function
    | [] -> acc
    | (_, y)::tl -> aux (Stdlib.List.append y acc) tl
  in
  aux [] l

let tr_map f lst =
  let rec aux acc = function
    | [] -> Stdlib.List.rev acc  (* 保持原顺序 *)
    | h :: t -> aux (f h :: acc) t
  in
  aux [] lst

let my_solve_helper c1map cs2 =
  let cs1 = (*Stdlib.List.concat (snd (Stdlib.List.split (HiFirrtl.PVM.elements c1map))*)
            split2_tailrec (HiFirrtl.PVM.elements c1map) in
  let dpdcg = build_graph_from_constraints cs1 in
  let res = SCC.scc_list dpdcg in
  let res' = tr_map (fun l -> tr_map (fun v-> nat_to_pair (G.V.label v)) l) res in
  InferWidths.solve_alg_check res' c1map cs2

let my_solve_fun c tmap =
  let ut0 = (Unix.times()).tms_utime in 
  match extract_constraints_c c tmap with
  | Some (c1maps, cs2) -> let ut1 = (Unix.times()).tms_utime in 
    printf "extraction time : %f\n" (Float.sub ut1 ut0);
    Stdlib.List.fold_left (fun res c1map ->
      match res with
      | Some old_values -> let ut2 = (Unix.times()).tms_utime in 
        (match my_solve_helper c1map cs2 with
         | Some new_values -> let ut3 = (Unix.times()).tms_utime in 
            printf "single solution : %f\n" (Float.sub ut3 ut2);
            Some (Branch_and_bound.smaller_valuation old_values new_values)
         | None -> res)
      | None -> my_solve_helper c1map cs2) None c1maps
  | None -> None

let my_coq_InferWidths_transps ps tmap =
  let rec loop ps acc =
    match ps with
    | [] -> Some (Stdlib.List.rev acc)  (* 反转累加器以保持原始顺序 *)
    | p :: tl ->
        match InferWidths.coq_InferWidths_transp p tmap with
        | None -> None  (* 提前终止 *)
        | Some n -> loop tl (n :: acc)  (* 尾递归调用 *)
  in
  loop ps []  (* 初始调用 *)

let rec revhfstmts sts res = 
  match sts with 
  | HiFirrtl.Qnil -> res
  | HiFirrtl.Qcons (h, tl) -> revhfstmts tl (revhfstmt h res)
    
and revhfstmt st res =
  match st with
  | HiFirrtl.Swhen (c, s1, s2) -> HiFirrtl.Qcons ((HiFirrtl.Swhen (c, revhfstmts s1 HiFirrtl.Qnil, revhfstmts s2 HiFirrtl.Qnil)), res)
  | _ -> HiFirrtl.Qcons (st, res)

let rec my_coq_InferWidths_transs s tmap res =
  match s with
  | HiFirrtl.Swire (v, t0) ->
    if HiEnv.ftype_not_implicit t0
    then Some (HiFirrtl.Qcons (s, res))
    else (match HiFirrtl.VM.find v tmap with
          | Some p -> let (ft, _) = p in Some (HiFirrtl.Qcons (Swire (v, ft), res))
          | None -> None)
  | Sreg (v, r) ->
    if HiEnv.ftype_not_implicit r.coq_type
    then Some (HiFirrtl.Qcons (s, res))
    else (match HiFirrtl.VM.find v tmap with
          | Some p ->
            let (ft, _) = p in
            Some (HiFirrtl.Qcons (Sreg (v, { coq_type = ft; clock = r.clock; reset =
            r.reset }), res))
          | None -> None)
  | Swhen (c, s1, s2) ->
    (match my_coq_InferWidths_transss s1 tmap HiFirrtl.Qnil with
     | Some n1 ->
       (match my_coq_InferWidths_transss s2 tmap HiFirrtl.Qnil with
        | Some n2 -> Some (HiFirrtl.Qcons (Swhen (c, n1, n2), res))
        | None -> None)
     | None -> None)
  | _ -> Some (HiFirrtl.Qcons (s, res))

and my_coq_InferWidths_transss sts tmap res =
  match sts with
  | HiFirrtl.Qnil -> Some res
  | HiFirrtl.Qcons (s, ss) ->
    (match my_coq_InferWidths_transs s tmap res with
    | Some n ->
      my_coq_InferWidths_transss ss tmap n
    | None -> None)

let my_coq_InferWidths_fun c =
  match HiFirrtl.circuit_tmap c with
  | Some tmap ->
    let Fcircuit (cv, l) = c in
    let h = Stdlib.List.hd l in
      (match h with
        | FInmod (mv, ps, ss) ->
          let ut0 = (Unix.times()).tms_utime in 
             (match my_solve_fun c tmap with
              | Some solution ->
                let ut1 = (Unix.times()).tms_utime in 
                let elements = HiFirrtl.PVM.elements solution in
                printf "total time : %f\n" (Float.sub ut1 ut0);
                (match InferWidths.update_tmap tmap elements with
                 | Some newtm -> printf "components amount : %d\n" (Stdlib.List.length elements);
                   (match my_coq_InferWidths_transps ps newtm with
                    | Some nps ->
                      (match my_coq_InferWidths_transss ss newtm HiFirrtl.Qnil with
                       | Some nss ->
                         Some (HiFirrtl.Fcircuit (cv, ((FInmod (mv, nps, revhfstmts nss HiFirrtl.Qnil)) :: [])), newtm)
                       | None -> None)
                    | None -> None) 
                 | None -> None)
              | None -> None)
        | FExmod (_, _, _) -> None)
  | None -> None

let print_iw_mlir in_file hif_ast = 
  let flatten_cir = Inline.inline_cir stdout hif_ast in
  (*let oc_fir = open_out (process_string in_file "_iw.fir") in*)
  match flatten_cir with
  | Ast.Fcircuit (v, ml) ->
    let ((map0, flag), tmap_ast) = mapcir flatten_cir in 
    let fcir = trans_cir flatten_cir map0 flag tmap_ast in 

    (*let mfile = convert_path in_file in
    let mlirf = Mparser.mlirparse mfile in 
    let inlined = Mast.inline_cir mlirf in 
    let mlirmap = Mast.mapcir inlined in*)

    (match my_coq_InferWidths_fun fcir with
    | Some (newc, newtm) -> (*Printfir.pp_fcircuit_fir oc_fir v newc; close_out oc_fir;*) 
      printf "%s\n" in_file;

      (*StringMap.iter (fun key value -> 
        match HiFirrtl.VM.find (Obj.magic (Stdlib.List.hd (Stdlib.List.rev (StringMap.find key map0)))) newtm with
        | Some (ft, _) -> 
          if (fir_mlir_ty_eq value ft) then printf "" else (
              printf "%s\n%s : " in_file key; Printmlir.pp_ftype_mlir stdout ft; printf "<->"; Mast.pp_type stdout value; printf "\n")
        | _ -> printf "%s not find\n" key
        ) mlirmap;*)

    | _ -> output_string stdout ("no inferred\n"))

let rec length_ss ss =
  match ss with
| HiFirrtl.Qnil -> 0
| Qcons (s, st) -> 1 + length_ss st

let rec nth_hfstmt_seq seq n =
  if n < 0 then raise (Invalid_argument "nth_hfstmt_seq: negative index") else
  match seq with
  | HiFirrtl.Qnil -> raise (Invalid_argument "nth_hfstmt_seq: index out of bounds")
  | Qcons (stmt, rest) ->
      if n = 0 then stmt
      else nth_hfstmt_seq rest (n - 1)

let take n lst =
  let rec aux acc n = function
    | _ when n <= 0 -> HiFirrtl.coq_Qrev acc
    | HiFirrtl.Qnil -> HiFirrtl.coq_Qrev acc
    | Qcons (h,t) -> aux (Qcons (h, acc)) (n - 1) t
  in
  aux Qnil n lst

let flat_map_tailrec f lst =
  let rec prepend_sublist sublist acc = 
    match sublist with
    | [] -> acc
    | h :: t -> prepend_sublist t (h :: acc)
  in
  let rec loop acc = function
    | [] -> Stdlib.List.rev acc
    | x :: xs ->
        loop (prepend_sublist (f x) acc) xs
  in
  loop [] lst

let min2cs2_tailrec minl =
  let el = flat_map_tailrec (fun min0 -> list_min_rhs min0 []) minl in
  Stdlib.List.map (fun e -> { lhs_const2_new = (1 - e.regular_const);
    rhs_terms2_new = e.regular_terms; rhs_power2_new = e.regular_power }) el

let find_segmentation_fault in_file hif_ast = 
  let flatten_cir = Inline.inline_cir stdout hif_ast in 
  let oc_fir = open_out (process_string in_file "_cons.txt") in
  (*let oc_res_num = open_out (process_string in_file "_res_num.txt") in*)

  (*Ast.pp_fcircuit oc_fir flatten_cir;*)
  match flatten_cir with
  | Ast.Fcircuit (v, ml) ->
    let ((map0, flag), tmap_ast) = mapcir flatten_cir in 
    (*StringMap.iter (fun key value -> output_string oc_fir (key^": ["); Stdlib.List.iter (fprintf oc_fir "%d;") value; output_string oc_fir "]\n") map0;*)
    let c = trans_cir flatten_cir map0 flag tmap_ast in 

    (match HiFirrtl.circuit_tmap c, c with
    | Some tmap, HiFirrtl.Fcircuit (_, [m]) -> output_string stdout ("numbered\n");
      (match Extract_cswithmin.extract_constraint_m m tmap with
      | Some ((c1map, cs2), cs_min) -> 
        let cs1 = split2_tailrec (HiFirrtl.PVM.elements c1map) in

        (*
        let dpdcg = build_graph_from_constraints cs1 in 
        let res = SCC.scc_list dpdcg in 
        let res' = tr_map (fun l -> tr_map (fun v-> nat_to_pair (G.V.label v)) l) res in *)

        (match my_solve_fun c tmap with
        | Some solution ->
          Stdlib.List.iter (fun c -> pp_cstrt1 oc_fir (remove_power1 solution c)) cs1;
          Stdlib.List.iter (fun c -> pp_cstrt_min oc_fir (remove_power_min solution c)) cs_min;
          Stdlib.List.iter (fun c -> pp_cstrt2 oc_fir (remove_power_min_rhs solution c)) cs2;
        | None -> output_string stdout ("unsolved\n"))
        (*match InferWidths.solve_alg res' initial_valuation c1map with
        | Some valuation -> 
          (*
          Stdlib.List.iter (fun (var, value) -> fprintf oc_res_num "x(%d,%d) : %d\n" (fst (Obj.magic var)) (snd (Obj.magic var)) value) (HiFirrtl.PVM.elements valuation);
          close_out oc_fir; close_out oc_res_num*) output_string stdout ("solved\n");
        | None -> output_string stdout ("unsolved\n")*)

      | _ -> output_string stdout ("no extract\n"))
        
    | _, _ -> output_string stdout ("no inferred\n"))

let take_list n l =
  if n < 0 then invalid_arg "List.take"
  else
    let rec aux n = function
      | _ when n = 0 -> []       (* 取够数量时终止 *)
      | [] -> []                 (* 列表取空时终止 *)
      | hd::tl -> hd :: aux (n-1) tl  (* 递归构建新列表 *)
    in
    aux n l
