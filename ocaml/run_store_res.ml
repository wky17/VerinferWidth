open Arg
open Hifirrtl_lang

let args = [
  ]

let usage = "Usage: Compare with Gurobi FILE\n"

let anon file =
  let f = (Parser.hiparse file) in 
  let _ = Against_gurobi.store_cons_res file f in
  ()

let _ = parse args anon usage
