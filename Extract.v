From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrOcamlIntConv ExtrOcamlNatInt ExtrOcamlZInt.
From Coq Require Import Arith List.
From mathcomp Require Import all_ssreflect.
Require Import Solver.HiFirrtl Solver.constraints Solver.floyd_sc Solver.scc Solver.branch_and_bound
Solver.TopoSort Solver.extract_cs Solver.inferWidths_exp Solver.extract_cs_multimod Solver.inferWidths_multimod.
From mathcomp.tarjan Require Import kosaraju.

Extraction Language OCaml.
Cd "ocaml/extraction".
Extraction Inline ssrbool.predT ssrbool.pred_of_argType.
Separate Extraction
         HiFirrtl.Qrev extract_cswithmin.extract_constraints_c extract_cs.expandwhens
         inferWidths_exp.InferWidths_fun HiFirrtl.pv2ref HiFirrtl.href_eqn extract_cswithmin.min2cs2 
         extract_cswithmin.collect_power1_vars extract_cswithmin.collect_power2_vars extract_cswithmin.remove_power1 extract_cswithmin.remove_power2 extract_cswithmin.remove_power_min
         constraints.split_constraints' inferWidths.solve_alg_check
         extract_cs_multimod.extract_constraints_c extract_cs_multimod.update_tmap extract_cs_multimod.InferWidths_trans_c extract_cs_multimod.circuit_tmap
         inferWidths_multimod.extract_constraints_c inferWidths_multimod.solve_alg_check inferWidths_multimod.smaller_valuation inferWidths_multimod.update_tmap inferWidths_multimod.InferWidths_trans_c.
Cd "../..".