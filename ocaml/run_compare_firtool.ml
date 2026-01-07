open Arg
open Hifirrtl_lang

let args = [
  ]

let usage = "Usage: Compare with firtool FILE\n"

let file1_ref = ref ""
let file2_ref = ref ""

let anon filename =
  if !file1_ref = "" then
    file1_ref := filename 
  else if !file2_ref = "" then
    file2_ref := filename 
  else
    raise (Arg.Bad "Too many anonymous arguments")

let () =
  parse args anon usage;
  if !file1_ref = "" || !file2_ref = "" then
    raise (Arg.Bad "Requires exactly two input files");
  let f = Parser.hiparse !file1_ref in 
  Against_firtool.compare_with_mlir !file1_ref f !file2_ref