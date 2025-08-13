open Extraction
open Hifirrtl_lang
open Useocamlscc
open Printf
open Transhiast
open Mlir_lang
open Extraction.Constraints
open Extraction.Extract_cswithmin
open Min_solver

let store_cons_res in_file hif_ast = 
  let flatten_cir = Inline.inline_cir stdout hif_ast in 
  let oc_cons = open_out (process_string in_file "_cons.txt") in
  let oc_res_num = open_out (process_string in_file "_res_num.txt") in
  match flatten_cir with
  | Ast.Fcircuit (v, ml) ->
    let ((map0, flag), tmap_ast) = mapcir flatten_cir in 
    let c = trans_cir flatten_cir map0 flag tmap_ast in 

    (match HiFirrtl.circuit_tmap c, c with
    | Some tmap, HiFirrtl.Fcircuit (_, [m]) -> 
      (match Extract_cswithmin.extract_constraint_m m tmap with
      | Some ((c1map, cs2), cs_min) -> 
        let cs1 = split2_tailrec (HiFirrtl.PVM.elements c1map) in

        (match my_solve_fun c tmap with
        | Some solution ->
          Stdlib.List.iter (fun c -> pp_cstrt1 oc_cons (remove_power1 solution c)) cs1;
          Stdlib.List.iter (fun c -> pp_cstrt_min oc_cons (remove_power_min solution c)) cs_min;
          Stdlib.List.iter (fun c -> pp_cstrt2 oc_cons (remove_power_min_rhs solution c)) cs2;
          Stdlib.List.iter (fun (var, value) -> fprintf oc_res_num "x(%d,%d) : %d\n" (fst (Obj.magic var)) (snd (Obj.magic var)) value) (HiFirrtl.PVM.elements solution);
          close_out oc_cons; close_out oc_res_num; 
          printf "constraints are stored in %s\n" (process_string in_file "_cons.txt");
          printf "results are stored in %s\n" (process_string in_file "_res_num.txt");

        | None -> output_string stdout ("cannot be inferred\n"))
      | _ -> output_string stdout ("constraint extraction is broken\n"))
    | _, _ -> output_string stdout ("bad type definition in the circuit\n"))
