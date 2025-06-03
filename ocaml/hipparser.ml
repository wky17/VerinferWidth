open Arg
open Hifirrtl_lang

let args = [
  ]

let usage = "Usage: hipparse FILE\n"

let anon file =
  (*let gc = Gc.get () in
  Printf.printf "All GC settings:\n%!";
  (Gc.print_stat stdout);
  Printf.printf "%s\n" file;*)
  let f = (Parser.hiparse file) in 
  let _ = Min_solver.print_iw_mlir (*Ast.pp_file*) (*Transhiast.inline_transf*) (*find_segmentation_fault*) (*Inline.inline_cir*) file f in
  ()

let _ = parse args anon usage
