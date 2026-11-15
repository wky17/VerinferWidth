open Arg
open Hifirrtl_lang
open Mlir_lang
open Transhiast
open Printf
open Min_solver_hash
open Extraction
open Printmlir

let () =
  (* 调整 GC 参数，减小 Major GC 频率，提高性能 *)
  let open Gc in
  let c = get () in
  set { c with
    minor_heap_size = 64 * 1024 * 1024;  (* minor heap 大小，默认 256KB，增大到 4MB *)
    major_heap_increment = 256;         (* major heap 每次增长量，默认 128，增大到 256 *)
    space_overhead = 180;               (* 允许的空间开销百分比，默认 80，适当放宽 *)
    max_overhead = 500;
    allocation_policy = 2;   (* First-fit 分配策略 *)}

let args = [
  ]

let usage = "Usage: OCaml FIRRTL compiler FILE\n"

let typecheck_against_firtool modmap map newtm mfile = 
  printf "start compare with firtool\n";
  let mlirf = Mparser.mlirparse mfile in 
  let mlirmap = Mast.mapcir mlirf in

  (* 逐module比较 *)
  (*StringMap.iter (fun modname mod_tmap -> 
    let modnum = StringMap.find modname modmap in
    let (map0,_) = StringMap.find modname map in
    match HiFirrtl.VM.find (Obj.magic modnum) newtm with
    | Some ocaml_tmap ->
      StringMap.iter (fun key value -> 
        match HiFirrtl.VM.find (Obj.magic (Stdlib.List.hd (Stdlib.List.rev (StringMap.find key map0)))) ocaml_tmap with
        | Some (ft, _) -> 
          if (fir_mlir_ty_eq value ft) then (printf "%s has type " key; pp_ftype_mlir stdout ft; printf " in both file\n") else (
            printf "%s has type " key; pp_ftype_mlir stdout ft; printf "by firtool\nwhile we say it's of type"; Mast.pp_type stdout value; printf "\n")
        | _ -> printf "%s not find\n" key
      ) mod_tmap
    | None -> printf "find module %d ocaml tmap failed\n" (Obj.magic modnum)
  ) mlirmap;*)
  printf "type check finished.\n"


let anon in_file =
  let hif_ast = Parser.hiparse in_file in 
  (*let oc_fir = open_out (process_string in_file "_iw.fir") in 
  Ast.pp_fcircuit stdout hif_ast;*)
  let (((modmap, modmap_rev), _), map) = Transhiast_without_inline.mapcir hif_ast in 
  let hif_without_inline = Transhiast_without_inline.trans_cir hif_ast modmap map in
  (*output_string oc_fir "\norigin\n";
  Printfir.pp_fcircuit_fir oc_fir hif_without_inline;*)
  let ut0 = (Unix.times()).tms_utime in 

  (match my_coq_InferWidths_fun hif_without_inline with
  | Some (c_iw, newtm_iw) -> 
    printf "%s width inference is finished\n" in_file;
    Printfir.pp_fcircuit_fir stdout c_iw;
    (match InferResets.coq_InferResets_fun c_iw with
    | Some (c_ir, newtm_ir) -> 
      printf "%s reset inference is finished\n" in_file;
      Printfir.pp_fcircuit_fir stdout c_ir;

  (*match ExpandConnects_inst.preprocess_subaccess c_ir with
    | Some fcir -> let ut1 = (Unix.times()).tms_utime in 
      (match ExpandConnects_inst.expandconnects fcir with
      | Some c_lowertypes -> let ut2 = (Unix.times()).tms_utime in 
        printf "after lowerTypes :\n";
        Printfir_pair.pp_fcircuit_fir stdout c_lowertypes;
        printf "lowerTypes time : %fs\n" (Float.sub ut2 ut1); 
        printf "\nafter expandWhens :\n";
        (match ExpandWhens_inst.expandWhens c_lowertypes with
        | Some ((c_expandwhens, conn_map), pvlist) -> let ut3 = (Unix.times()).tms_utime in 
          Printfir_pair.pp_fcircuit_fir stdout c_expandwhens;
          printf "expandWhens time : %fs\n" (Float.sub ut3 ut2); 
          printf "total time : %fs\n\n" (Float.sub ut3 ut0); 
          let string_cir = Transfast_string.trans_cir c_expandwhens modmap_rev map in 
          Ast.pp_fcircuit stdout string_cir;
          (*Ast.pp_fcircuit oc_fir string_cir; close_out oc_fir*)
        | None -> output_string stdout "error expandwhens\n")
      | None -> output_string stdout "error lowertypes\n") 
  | None -> output_string stdout "error subaccess preprocess\n"*)
      
    | _ -> output_string stdout ("inferResets failed\n"))
  | _ -> output_string stdout ("inferWidths failed\n"))

let _ = parse args anon usage
