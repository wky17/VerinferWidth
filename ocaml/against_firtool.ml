open Extraction
open Hifirrtl_lang
open Useocamlscc
open Printf
open Transhiast
open Mlir_lang
open Extraction.Constraints
open Extraction.Extract_cswithmin
open Min_solver

let fir_to_mlir filename =
  if Filename.check_suffix filename ".fir" then
    let len = String.length filename - 4 in  (* 4 = ".fir" 的长度 *)
    String.sub filename 0 len ^ ".mlir"
  else
    filename  (* 如果不是 .fir 文件，返回原文件名 *)

let compare_with_mlir in_file hif_ast = 
  let flatten_cir = Inline.inline_cir stdout hif_ast in
  match flatten_cir with
  | Ast.Fcircuit (v, ml) ->
    let ((map0, flag), tmap_ast) = mapcir flatten_cir in 
    let fcir = trans_cir flatten_cir map0 flag tmap_ast in 

    (match my_coq_InferWidths_fun fcir with
    | Some (newc, newtm) -> 
      let mfile = fir_to_mlir in_file in
      let mlirf = Mparser.mlirparse mfile in 
      let inlined = Mast.inline_cir mlirf in 
      let mlirmap = Mast.mapcir inlined in

      StringMap.iter (fun key value -> 
        match HiFirrtl.VM.find (Obj.magic (Stdlib.List.hd (Stdlib.List.rev (StringMap.find key map0)))) newtm with
        | Some (ft, _) -> 
          if (fir_mlir_ty_eq value ft) then printf "" else (
            printf "%s has type " key; Printmlir.pp_ftype_mlir stdout ft; printf "by firtool\nwhile we say it's of type"; Mast.pp_type stdout value; printf "\n")
        | _ -> printf "%s not find\n" key
        ) mlirmap;
      printf "%s check finished\n" in_file

    | _ -> output_string stdout ("no inferred\n"))
