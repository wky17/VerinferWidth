open Extraction
open Hifirrtl_lang
open Useocamlscc
open Printf
open Transhiast
open Mlir_lang

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
  Solve_fun.solve_alg_check res' c1map cs2

let my_solve_fun c tmap =
  let ut0 = (Unix.times()).tms_utime in 
  match Extract_cswithmin.extract_constraints_c c tmap with
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
                printf "total time : %f\n" (Float.sub ut1 ut0);
                (match Solve_fun.update_tmap tmap (HiFirrtl.PVM.elements solution) with
                 | Some newtm ->
                   (match Solve_fun.coq_InferWidths_transps ps newtm with
                    | Some nps ->
                      (match Solve_fun.coq_InferWidths_transss ss newtm with
                       | Some nss ->
                         Some (HiFirrtl.Fcircuit (cv, ((FInmod (mv, nps, nss)) :: [])), newtm)
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
    (* If you want to test the type equivalence against firtool, uncomment this *)
    (*let mfile = convert_path in_file in
    let mlirf = Mparser.mlirparse mfile in 
    let inlined = Mast.inline_cir mlirf in 
    let mlirmap = Mast.mapcir inlined in*)

    (match my_coq_InferWidths_fun fcir with
    | Some (newc, newtm) -> (*Printfir.pp_fcircuit_fir oc_fir v newc; close_out oc_fir;*) 
      printf "%s processed\n" in_file;
    (* If you want to test the type equivalence against firtool, uncomment this *)
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

let find_segmentation_fault in_file hif_ast = 
  let flatten_cir = Inline.inline_cir stdout hif_ast in 
  let oc_fir = open_out (process_string in_file "_cons1.txt") in
  (*Ast.pp_fcircuit oc_fir flatten_cir;*)
  match flatten_cir with
  | Ast.Fcircuit (v, ml) ->
    let ((map0, flag), tmap_ast) = mapcir flatten_cir in 
    (*StringMap.iter (fun key value -> output_string oc_fir (key^": ["); Stdlib.List.iter (fprintf oc_fir "%d;") value; output_string oc_fir "]\n") map0;*)
    let c = trans_cir flatten_cir map0 flag tmap_ast in 

    (match HiFirrtl.circuit_tmap c with
    | Some tmap ->
      (*match c, HiFirrtl.pv2ref (101761,59) tmap with
      | HiFirrtl.Fcircuit (_, [(FInmod (_, _, ss))]), Some ref -> 
        (*let (ss', _) = Extract_cswithmin.expandwhens ss (HiFirrtl.Qnil, []) in *)
  
      | _, _ -> printf "0\n"*)
      (match Extract_cswithmin.extract_constraints_c c tmap with
      | Some (c1map0 :: [c1map1], cs2) -> 
        let cs1 = Stdlib.List.concat (snd (Stdlib.List.split (HiFirrtl.PVM.elements c1map1))) in
        let cs2' = Extract_cswithmin.min2cs2 cs2 in
        let power_vars = Stdlib.List.append (flat_map_tailrec Extract_cswithmin.collect_power1_vars cs1) 
                          (flat_map_tailrec Extract_cswithmin.collect_power2_vars cs2') in
        (*Stdlib.List.iter (pp_cstrt1 oc_fir) cs1;
        Stdlib.List.iter (pp_cstrt2_new oc_fir) cs2';*)
        printf "%d\n" (Stdlib.List.length power_vars);
        

        (*match my_solve_helper c1map0 [] with
        | Some new_values -> output_string stdout ("solved0\n")
        | _ -> output_string stdout ("unsolved\n")
        *)
        
        let cs1 = split2_tailrec (HiFirrtl.PVM.elements c1map1) in 
        let dpdcg = build_graph_from_constraints cs1 in 
        let res = SCC.scc_list dpdcg in 
        let res' = tr_map (fun l -> tr_map (fun v-> nat_to_pair (G.V.label v)) l) res in 
        Stdlib.List.iter (fun component ->
          if (Stdlib.List.length component > 1) then
            (if (Stdlib.List.exists (fun x -> Stdlib.List.mem x power_vars) component) then 
            printf "power in cycle\n")
        ) res';
        (*match Solve_fun.solve_alg res' [] Constraints.initial_valuation c1map0 with
        | Some value -> output_string stdout ("solved0\n")
        | None -> output_string stdout ("unsolved\n"))*)

      | _ -> output_string stdout ("no extract\n"))
    | None -> output_string stdout ("no inferred\n"))
