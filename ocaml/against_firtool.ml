open Extraction
open Hifirrtl_lang
open Useocamlscc
open Printf
open Transhiast
open Mlir_lang
open Extraction.Constraints
open Extraction.Extract_cs_multimod
open Min_solver

let fir_to_mlir filename =
  if Filename.check_suffix filename ".fir" then
    let len = String.length filename - 4 in 
    String.sub filename 0 len ^ ".mlir"
  else
    filename 

let compare_with_mlir in_file hif_ast mfile = 
  Ast.pp_fcircuit stdout hif_ast;
  let ((modmap, _), map) = Transhiast_without_inline.mapcir hif_ast in
  let fcir = Transhiast_without_inline.trans_cir hif_ast modmap map in 

  (match my_coq_InferWidths_fun fcir with
  | Some (newc, newtm) -> 
    (*let mfile = fir_to_mlir in_file in*)
    let mlirf = Mparser.mlirparse mfile in 
    let mlirmap = Mast.mapcir mlirf in

    (* 逐modul比较 *)
    StringMap.iter (fun modname mod_tmap -> 
      let modnum = StringMap.find modname modmap in
      let (map0,_) = StringMap.find modname map in
      match HiFirrtl.VM.find (Obj.magic modnum) newtm with
      | Some ocaml_tmap ->
        StringMap.iter (fun key value -> 
          match HiFirrtl.VM.find (Obj.magic (Stdlib.List.hd (Stdlib.List.rev (StringMap.find key map0)))) ocaml_tmap with
          | Some (ft, _) -> 
            if (fir_mlir_ty_eq value ft) then (printf "%s has type " key; Printmlir.pp_ftype_mlir stdout ft; printf " in both file\n") else (
              printf "%s has type " key; Printmlir.pp_ftype_mlir stdout ft; printf "by firtool\nwhile we say it's of type"; Mast.pp_type stdout value; printf "\n")
          | _ -> printf "%s not find\n" key
        ) mod_tmap
      | None -> printf "find module %d ocaml tmap failed\n" (Obj.magic modnum)
    ) mlirmap;
    printf "%s type check finished.\n" in_file

  | _ -> output_string stdout ("no inferred\n"))
