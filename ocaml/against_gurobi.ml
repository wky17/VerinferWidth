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
  Ast.pp_fcircuit stdout hif_ast;
  let ((modmap, _), map) = Transhiast_without_inline.mapcir hif_ast in
  let fcir = Transhiast_without_inline.trans_cir hif_ast modmap map in 
  let oc_cons = open_out (process_string in_file "_cons.txt") in
  let oc_res_num = open_out (process_string in_file "_res_num.txt") in

  (match Extract_cs_multimod.circuit_tmap fcir, fcir with
    | Some tmap, HiFirrtl.Fcircuit (_, ml) -> 
      (match Extract_cs_multimod.extract_constraint_ml ml tmap HiFirrtl.PVM.empty [] [] with
      | Some ((c1map, cs2), cs_min) -> 
        let cs1 = split2_tailrec (HiFirrtl.PVM.elements c1map) in

        (match my_solve_fun fcir tmap with
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
