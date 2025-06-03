From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrOcamlIntConv ExtrOcamlNatInt ExtrOcamlZInt.
From Coq Require Import Arith List.
From mathcomp Require Import all_ssreflect.
Require Import Solver.HiFirrtl Solver.constraints (*Solver.seperate*) Solver.floyd_sc Solver.scc Solver.branch_and_bound
Solver.TopoSort Solver.extract_cs Solver.solve_fun.
From mathcomp.tarjan Require Import kosaraju.

Extraction Language OCaml.
Cd "ocaml/extraction".
Extraction Inline ssrbool.predT ssrbool.pred_of_argType.
Separate Extraction
         (*constraints.solve_acyclic'
         seperate.res_r seperate.res seperate.V (*fintype.enum*)
         simple_cycle.bl0 simple_cycle.res0 simple_cycle.solved_sc0
         simple_cycle.cs1 simple_cycle.cs2 simple_cycle.cs3 simple_cycle.cs4
         simple_cycle.v2' simple_cycle.v3' (*scc.res scc.res1 scc.res2 scc.ub3 scc.ub3'*)
         branch_and_bound.res 
         branch_and_bound.res0 branch_and_bound.res1 branch_and_bound.res2 branch_and_bound.res0'
         branch_and_bound.smaller_solution1 branch_and_bound.smaller_solution2 branch_and_bound.smaller_solution3*)
         mathcomp.tarjan.kosaraju.kosaraju HiFirrtl.Qrev extract_cs.extract_constraints_c extract_cs.expandwhens
         (*seperate.extract_constraints_c graph.build_dependency_graph seperate.solve *)
         solve_fun.InferWidths_fun HiFirrtl.pv2ref HiFirrtl.href_eqn extract_cswithmin.min2cs2 extract_cswithmin.collect_power1_vars extract_cswithmin.collect_power2_vars
         (*HiFirrtl.pmap0 HiFirrtl.tmap0' HiFirrtl.tmap0 graph.res graph.res_r
         simple_cycle.s0 simple_cycle.solve_sc0 simple_cycle.nv
         extract_cs.constraints extract_cs.nv0 extract_cs.nv extract_cs.nv' extract_cs.nv2 extract_cs.nv3
         extract_cs.cs1 extract_cs.val extract_cs.nv3' extract_cs.nval*)
         constraints.split_constraints' (*seperate.inferwidths_fun*)
         .
Cd "../..".