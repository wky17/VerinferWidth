open Extraction
open Hifirrtl_lang
open Useocamlscc
open Printf
open Transhiast
open Mlir_lang
open Extraction.Constraints
open Extraction.Extract_cswithmin

let split2_tailrec l =
  let rec aux acc = function
    | [] -> acc
    | (_, y)::tl -> aux (Stdlib.List.append y acc) tl
  in
  aux [] l

let tr_map f lst =
  let rec aux acc = function
    | [] -> Stdlib.List.rev acc  (* 保持原顺序 *)
    | h :: t -> aux (f h :: acc) t
  in
  aux [] lst

let my_solve_helper c1map cs2 =
  let cs1 = split2_tailrec (HiFirrtl.PVM.elements c1map) in
  let dpdcg = build_graph_from_constraints cs1 in
  let res = SCC.scc_list dpdcg in
  let res' = tr_map (fun l -> tr_map (fun v-> nat_to_pair (G.V.label v)) l) res in
  InferWidths.solve_alg_check res' c1map cs2

let my_solve_fun c tmap =
  let ut0 = (Unix.times()).tms_utime in 
    match extract_constraints_c c tmap with
    | Some (c1maps, cs2) -> let ut1 = (Unix.times()).tms_utime in 
      let solution = Stdlib.List.fold_left (fun res c1map ->
        match res with
        | Some old_values -> 
          (match my_solve_helper c1map cs2 with
           | Some new_values -> 
              Some (Branch_and_bound.smaller_valuation old_values new_values)
           | None -> res)
        | None -> my_solve_helper c1map cs2) None c1maps in
      let ut2 = (Unix.times()).tms_utime in 
      printf "extraction time : %f\ncomputation time : %f\n" (Float.sub ut1 ut0) (Float.sub ut2 ut1); solution
    | None -> None

let my_coq_InferWidths_transps ps tmap =
  let rec loop ps acc =
    match ps with
    | [] -> Some (Stdlib.List.rev acc)  (* 反转累加器以保持原始顺序 *)
    | p :: tl ->
        match InferWidths.coq_InferWidths_transp p tmap with
        | None -> None  (* 提前终止 *)
        | Some n -> loop tl (n :: acc)  (* 尾递归调用 *)
  in
  loop ps []  (* 初始调用 *)

let rec revhfstmts sts res = 
  match sts with 
  | HiFirrtl.Qnil -> res
  | HiFirrtl.Qcons (h, tl) -> revhfstmts tl (revhfstmt h res)
    
and revhfstmt st res =
  match st with
  | HiFirrtl.Swhen (c, s1, s2) -> HiFirrtl.Qcons ((HiFirrtl.Swhen (c, revhfstmts s1 HiFirrtl.Qnil, revhfstmts s2 HiFirrtl.Qnil)), res)
  | _ -> HiFirrtl.Qcons (st, res)

let rec my_coq_InferWidths_transs s tmap res =
  match s with
  | HiFirrtl.Swire (v, t0) ->
    if HiEnv.ftype_not_implicit t0
    then Some (HiFirrtl.Qcons (s, res))
    else (match HiFirrtl.VM.find v tmap with
          | Some p -> let (ft, _) = p in Some (HiFirrtl.Qcons (Swire (v, ft), res))
          | None -> None)
  | Sreg (v, r) ->
    if HiEnv.ftype_not_implicit r.coq_type
    then Some (HiFirrtl.Qcons (s, res))
    else (match HiFirrtl.VM.find v tmap with
          | Some p ->
            let (ft, _) = p in
            Some (HiFirrtl.Qcons (Sreg (v, { coq_type = ft; clock = r.clock; reset =
            r.reset }), res))
          | None -> None)
  | Swhen (c, s1, s2) ->
    (match my_coq_InferWidths_transss s1 tmap HiFirrtl.Qnil with
     | Some n1 ->
       (match my_coq_InferWidths_transss s2 tmap HiFirrtl.Qnil with
        | Some n2 -> Some (HiFirrtl.Qcons (Swhen (c, n1, n2), res))
        | None -> None)
     | None -> None)
  | _ -> Some (HiFirrtl.Qcons (s, res))

and my_coq_InferWidths_transss sts tmap res =
  match sts with
  | HiFirrtl.Qnil -> Some res
  | HiFirrtl.Qcons (s, ss) ->
    (match my_coq_InferWidths_transs s tmap res with
    | Some n ->
      my_coq_InferWidths_transss ss tmap n
    | None -> None)

let my_coq_InferWidths_fun c =
  match HiFirrtl.circuit_tmap c with
  | Some tmap ->
    let Fcircuit (cv, l) = c in
    let h = Stdlib.List.hd l in
      (match h with
        | FInmod (mv, ps, ss) ->
          let ut0 = (Unix.times()).tms_utime in 
             (match my_solve_fun c tmap with
              | Some solution ->
                let ut1 = (Unix.times()).tms_utime in 
                let elements = HiFirrtl.PVM.elements solution in
                printf "total time : %f\n" (Float.sub ut1 ut0);
                (match InferWidths.update_tmap tmap elements with
                 | Some newtm -> printf "components amount : %d\n" (Stdlib.List.length elements);
                   (match my_coq_InferWidths_transps ps newtm with
                    | Some nps ->
                      (match my_coq_InferWidths_transss ss newtm HiFirrtl.Qnil with
                       | Some nss ->
                         Some (HiFirrtl.Fcircuit (cv, ((FInmod (mv, nps, revhfstmts nss HiFirrtl.Qnil)) :: [])), newtm)
                       | None -> None)
                    | None -> None) 
                 | None -> None)
              | None -> None)
        | FExmod (_, _, _) -> None)
  | None -> None

let print_iw_fir in_file hif_ast = 
  let flatten_cir = Inline.inline_cir stdout hif_ast in
  let oc_fir = open_out (process_string in_file "_iw.fir") in
  match flatten_cir with
  | Ast.Fcircuit (v, ml) ->
    let ((map0, flag), tmap_ast) = mapcir flatten_cir in 
    let fcir = trans_cir flatten_cir map0 flag tmap_ast in 
    (match my_coq_InferWidths_fun fcir with
    | Some (newc, newtm) -> Printfir.pp_fcircuit_fir oc_fir v newc; Printfir.pp_fcircuit_fir stdout v newc; close_out oc_fir;
      printf "%s width inference is finished\n" in_file
    | _ -> output_string stdout ("cannot be inferred\n"))
