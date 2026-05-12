open Extraction
open Hifirrtl_lang
open Useocamlscc
open Printf
open Transhiast
open Mlir_lang
open Extraction.Constraints
open Extraction.Extract_cs_multimod
open Extraction.InferWidths_multimod
open Min_solver

let pp_cstrt1 out c1 = fprintf out "x(%d,(%d,%d)) >= " (Obj.magic (fst c1.lhs_var1)) (Obj.magic (fst (snd c1.lhs_var1))) (Obj.magic (snd (snd c1.lhs_var1)));
    Stdlib.List.iter (fun (coe, var) -> fprintf out "%d * x(%d,(%d,%d)) + " coe (Obj.magic (fst var)) (Obj.magic (fst (snd var))) (Obj.magic (snd (snd var)))) c1.rhs_terms1;
    Stdlib.List.iter (fun (_, var) -> fprintf out "2 ^ x(%d,(%d,%d)) + " (Obj.magic (fst var)) (Obj.magic (fst (snd var))) (Obj.magic (snd (snd var)))) c1.rhs_power;
    fprintf out "%d\n" c1.rhs_const1

let rec pp_min_rhs out r =
  match r with
  | Expr e ->
    Stdlib.List.iter (fun (coe, var) ->
      fprintf out "%d * x(%d,(%d,%d)) + " coe
        (Obj.magic (fst var))
        (Obj.magic (fst (snd var)))
        (Obj.magic (snd (snd var)))
    ) e.regular_terms;
    Stdlib.List.iter (fun (_, var) ->
      fprintf out "2 ^ x(%d,(%d,%d)) + "
        (Obj.magic (fst var))
        (Obj.magic (fst (snd var)))
        (Obj.magic (snd (snd var)))
    ) e.regular_power;
    fprintf out "%d" e.regular_const
  | Min (min1, min2) ->
    fprintf out "min(";
    pp_min_rhs out min1;
    fprintf out ",";
    pp_min_rhs out min2;
    fprintf out ")"

let pp_cstrt_min out c1 =
  fprintf out "x(%d,(%d,%d)) >= "
    (Obj.magic (fst c1.lhs_var_min))
    (Obj.magic (fst (snd c1.lhs_var_min)))
    (Obj.magic (snd (snd c1.lhs_var_min)));
  pp_min_rhs out c1.rhs_expr_min;
  fprintf out "\n"

let pp_cstrt2 out c2 =
  fprintf out "1 >= ";
  pp_min_rhs out c2;
  fprintf out "\n"

let store_cons_res in_file hif_ast = 
  (*Ast.pp_fcircuit stdout hif_ast;*)
  let ((modmap, _), map) = Transhiast_without_inline.mapcir hif_ast in
  let fcir = Transhiast_without_inline.trans_cir hif_ast modmap map in 
  let oc_cons = open_out (process_string in_file "_cons.txt") in
  let oc_res_num = open_out (process_string in_file "_res_num.txt") in

  (match circuit_tmap fcir, fcir with
    | Some tmap, HiFirrtl.Fcircuit (_, ml) -> 
      let ut0 = (Unix.times()).tms_utime in 
      (match extract_constraint_ml ml tmap TVM.empty [] [] with
      | Some ((c1map, cs2), cs_min) -> 
        let ut1 = (Unix.times()).tms_utime in 
        printf "extraction time : %f\n" (Float.sub ut1 ut0);
        let cs1 = split2_tailrec (TVM.elements c1map) in
        (match my_solve_fun fcir tmap with
        | Some solution ->
          Stdlib.List.iter (fun c -> pp_cstrt1 oc_cons (remove_power1 solution c)) cs1;
          Stdlib.List.iter (fun c -> pp_cstrt_min oc_cons (remove_power_min solution c)) cs_min;
          Stdlib.List.iter (fun c -> pp_cstrt2 oc_cons (remove_power_min_rhs solution c)) cs2;
          Stdlib.List.iter (fun (var, value) -> fprintf oc_res_num "x(%d,(%d,%d)) : %d\n" (fst (Obj.magic var)) (fst (snd (Obj.magic var))) (snd (snd (Obj.magic var))) value) (TVM.elements solution);
          close_out oc_cons; close_out oc_res_num; 
          printf "constraints are stored in %s\n" (process_string in_file "_cons.txt");
          printf "results are stored in %s\n" (process_string in_file "_res_num.txt");

        | None -> output_string stdout ("cannot be inferred\n"))
      | _ -> output_string stdout ("constraint extraction is broken\n"))
    | _, _ -> output_string stdout ("bad type definition in the circuit\n"))
