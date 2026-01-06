open Arg
open Hifirrtl_lang

let args = [
  ]

let usage = "Usage: OCaml inferWidths FILE\n"

let anon file =
  let f = (Parser.hiparse file) in 
  let _ = Min_solver.print_iw_fir file f in
  ()

let _ = parse args anon usage
