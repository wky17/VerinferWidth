open Hifirrtl_lang
open Extraction

let trans_fgtyp ty nty = 
  match ty, nty with
  | Ast.Fuint_implicit _, Env.Fuint s -> Ast.Fuint s
  | Ast.Fsint_implicit _, Env.Fsint s -> Ast.Fsint s
  | _, _ -> ty

let rec trans_ftype ty nty = 
  match ty, nty with
  | Ast.Gtyp gt, HiEnv.Gtyp ngt -> Ast.Gtyp (trans_fgtyp gt ngt)
  | Ast.Atyp (atyp, n), HiEnv.Atyp (natyp, _) -> Ast.Atyp (trans_ftype atyp natyp, n)
  | Ast.Btyp btyp, HiEnv.Btyp nbtyp -> Ast.Btyp (trans_btyp btyp nbtyp)

and trans_btyp btyp nbtyp =
  match btyp, nbtyp with
  | Ast.Fnil, _ -> Ast.Fnil
  | Ast.Fflips (fv, fl, ft, ff), HiEnv.Fflips (_, _, nft, nff) -> 
    Ast.Fflips (fv, fl, trans_ftype ft nft, trans_btyp ff nff)

let trans_port p map tmap = 
  match p with
  | Ast.Finput (v, ty) -> let num = Obj.magic (Stdlib.List.hd (Transhiast.StringMap.find v map)) in
    (match HiFirrtl.VM.find num tmap with
    | Some (nty, _) -> Ast.Finput(v, trans_ftype ty nty)
    | _ -> p)
  | Ast.Foutput (v, ty) -> let num = Obj.magic (Stdlib.List.hd (Transhiast.StringMap.find v map)) in
    (match HiFirrtl.VM.find num tmap with
    | Some (nty, _) -> Ast.Foutput(v, trans_ftype ty nty)
    | _ -> p)

let rec trans_stmt s map tmap res = 
  match s with
  | Ast.Swire (v, ty) -> let num = Obj.magic (Stdlib.List.hd (Transhiast.StringMap.find v map)) in
    (match HiFirrtl.VM.find num tmap with
    | Some (nty, _) -> let ns = Ast.Swire(v, trans_ftype ty nty) in
                  Ast.Qcons (ns, res)
    | _ -> Ast.Qcons (s, res))
  | Ast.Sreg (v, r) -> let num = Obj.magic (Stdlib.List.hd (Transhiast.StringMap.find v map)) in
    (match HiFirrtl.VM.find num tmap with
    | Some (nty, _) -> let nty' = trans_ftype r.coq_type nty in
                  let ns = Ast.Sreg(v, Ast.mk_freg_r nty' r.clock r.reset) in
                  Ast.Qcons (ns, res)
    | _ -> Ast.Qcons (s, res))
  | Ast.Swhen (c, s1, s2) -> 
    let ns = Ast.Swhen (c, trans_stmts s1 map tmap Ast.Qnil, trans_stmts s2 map tmap Ast.Qnil) in
             Ast.Qcons (ns, res)
  | _ -> Qcons (s, res)

and trans_stmts ss map tmap res =
  match ss with
  | Ast.Qnil -> res
  | Ast.Qcons (s, st) -> trans_stmts st map tmap (trans_stmt s map tmap res)

let rec revstmts sts res = 
  match sts with 
  | Ast.Qnil -> res
  | Ast.Qcons (h, tl) -> revstmts tl (revstmt h res)
    
and revstmt st res =
  match st with
  | Ast.Swhen (c, s1, s2) -> Ast.Qcons ((Ast.Swhen (c, revstmts s1 Ast.Qnil, revstmts s2 Ast.Qnil)), res)
  | _ -> Ast.Qcons (st, res)

let trans_mod m modmap map tmap = 
  match m with
  | Ast.FInmod (mv, pl, sl) -> 
    let mv_num = Transhiast.StringMap.find mv modmap in
    let (hd_map, _) = Transhiast.StringMap.find mv map in
    (match HiFirrtl.VM.find (Obj.magic mv_num) tmap with
    | Some mod_tmap ->
      let newports = List.map (fun a -> trans_port a hd_map mod_tmap) pl in
      let newstmts = trans_stmts sl hd_map mod_tmap Ast.Qnil in
      Ast.FInmod(mv, newports, revstmts newstmts Ast.Qnil)
    | _ -> m)
  | Ast.FExmod _ -> m

let rec trans_modl ml modmap map tmap =
  match ml with
  | [] -> []
  | hd :: tl -> 
    let m = trans_mod hd modmap map tmap in
    m :: (trans_modl tl modmap map tmap)

let trans_cir cir modmap map tmap =
  match cir with
  | Ast.Fcircuit (cv, ml) ->
    Ast.Fcircuit (cv, (trans_modl ml modmap map tmap))