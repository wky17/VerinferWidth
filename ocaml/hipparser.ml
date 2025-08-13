open Arg
open Hifirrtl_lang

let args = [
  ]

let usage = "Usage: hipparse FILE\n"

let anon file =
  let f = (Parser.hiparse file) in 
  let _ = Against_firtool.compare_with_mlir (*Against_gurobi.store_cons_res*) (*Min_solver.print_iw_fir*) file f in
  ()

let _ = parse args anon usage
