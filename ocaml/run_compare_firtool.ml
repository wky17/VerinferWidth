open Arg
open Hifirrtl_lang

let args = [
  ]

let usage = "Usage: Compare with firtool FILE\n"

let anon file =
  let f = (Parser.hiparse file) in 
  let _ = Against_firtool.compare_with_mlir file f in
  ()

let _ = parse args anon usage
