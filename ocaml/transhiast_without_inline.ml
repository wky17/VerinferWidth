open Hifirrtl_lang
open Printf
open Nodehelper
open Extraction
open Big_int_Z

module StringMap = Map.Make(String)
let initmap_s = StringMap.empty
module IntMap = Map.Make(Stdlib.Int)
let initmap_i = IntMap.empty

let rec pl2btyp pl = 
  match pl with
  | [] -> Ast.Fnil
  | (Ast.Finput (v, ty)) :: tl -> Ast.Fflips (v, Ast.Nflip, ty, pl2btyp tl)
  | (Ast.Foutput (v, ty)) :: tl -> Ast.Fflips (v, Ast.Flipped, ty, pl2btyp tl)

let rec mapstmt modplmap (((map, map_i), flag), tmap) stmt = 
  match stmt with
  | Ast.Swire (v, ty) -> let (map0, flag0) = Transhiast.mapftype v (map, flag) ty in 
                        (((map0, IntMap.add flag v map_i), flag0), StringMap.add v ty tmap)
  | Ast.Sreg (v, r) -> let (map0, flag0) = Transhiast.mapftype v (map, flag) r.coq_type in 
                        (((map0, IntMap.add flag v map_i), flag0), StringMap.add v r.coq_type tmap)
  | Ast.Smem (v, ty, n) -> let (map0, flag0) = Transhiast.mapftype v (map, flag) (Ast.Atyp (ty, n)) in 
                        (((map0, IntMap.add flag v map_i), flag0), StringMap.add v (Ast.Atyp (ty, n)) tmap)
  | Ast.Snode (v, e) -> (match Nodehelper.type_of_hfexpr e tmap with
                      | Some ty -> let (map0, flag0) = Transhiast.mapftype v (map, flag) ty in 
                          (((map0, IntMap.add flag v map_i), flag0), StringMap.add v ty tmap)
                      | None -> printf "%s wrong expr type\n" v; Ast.pp_expr stdout e; (((map, map_i), flag), tmap))
  | Ast.Sinst (v, mv) -> let pl = StringMap.find mv modplmap in
    let ty = Ast.Btyp (pl2btyp pl) in 
    let (map0, flag0) = Transhiast.mapftype v (map, flag) ty in 
    (((map0, IntMap.add flag v map_i), flag0), StringMap.add v ty tmap)
  | Ast.Swhen (_, s1, s2) -> mapstmts modplmap (mapstmts modplmap (((map, map_i), flag), tmap) s1) s2
  | _ -> (((map, map_i), flag), tmap)

and mapstmts modplmap (((map, map_i), flag), tmap) stmts = 
  match stmts with
  | Ast.Qnil -> (((map, map_i), flag), tmap)
  | Ast.Qcons (s, ss) -> mapstmts modplmap (mapstmt modplmap (((map, map_i), flag), tmap) s) ss

let mapmod m modplmap =  
  match m with 
  | Ast.FInmod (mv, pl, sl) -> 
    let (((map0, map0_i), flag0), tmap0) = Stdlib.List.fold_left Transhiast.mapport (((initmap_s, initmap_i), 0), initmap_s) pl in
    let (((map1, map1_i), _), tmap1) = mapstmts modplmap (((map0, map0_i), flag0), tmap0) sl in (((mv, map1), map1_i), tmap1)
  | FExmod (mv, _, _) -> (((mv, initmap_s), initmap_i), initmap_s)

let rec mapmodl (((modmap, modmap_rev), flag), map) modplmap ml =
  match ml with
  | [] -> (((modmap, modmap_rev), flag), map)
  | hd :: tl -> let (((hd_v, hd_map), hd_map_i), hd_tmap) = mapmod hd modplmap in
    mapmodl (((StringMap.add hd_v flag modmap, IntMap.add flag hd_v modmap_rev), flag + 1), StringMap.add hd_v ((hd_map, hd_map_i), hd_tmap) map) modplmap tl

let mapcir cir = 
  match cir with
  | Ast.Fcircuit (_, ml) -> let modplmap = Stdlib.List.fold_left (fun acc m -> 
      match m with
      | Ast.FInmod (mv, pl, _) -> StringMap.add mv pl acc
      | FExmod (mv, pl, _) -> StringMap.add mv pl acc) initmap_s ml in
    mapmodl (((initmap_s, initmap_i), 0), initmap_s) modplmap ml 

(* transast *)

let rec trans_stmt s map res tmap modmap = 
  match s with
  | Ast.Sskip -> HiFirrtl.Qcons (HiFirrtl.Sskip, res)
  | Ast.Swire (v, ty) -> 
                let ns = HiFirrtl.Swire(Obj.magic (Stdlib.List.hd (StringMap.find v map)), Transhiast.trans_ftype v ty map) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Sfcnct (ref, e) -> 
                let new_ref = Transhiast.trans_ref ref map in 
                let ns = HiFirrtl.Sfcnct((Transhiast.trans_ref ref map), Transhiast.trans_expr e map) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Sinvalid ref -> 
                let ns = HiFirrtl.Sinvalid ((Transhiast.trans_ref ref map)) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Snode (v, e) -> 
                let ns = HiFirrtl.Snode(Obj.magic (Stdlib.List.hd (StringMap.find v map)), Transhiast.trans_expr e map) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Sreg (v, r) -> 
                let ns = HiFirrtl.Sreg (Obj.magic (Stdlib.List.hd (StringMap.find v map)), 
                    Transhiast.mk_freg (Transhiast.trans_ftype v r.coq_type map) (Transhiast.trans_expr r.clock map) (Transhiast.trans_rst r.reset map)) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Smem _ -> res
  | Ast.Sinst (v, modv) -> 
                let ns = HiFirrtl.Sinst (Obj.magic (Stdlib.List.hd (StringMap.find v map)), Obj.magic (StringMap.find modv modmap)) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Swhen (c, s1, s2) -> let ns = HiFirrtl.Swhen (Transhiast.trans_expr c map, trans_stmts s1 map HiFirrtl.Qnil tmap modmap, trans_stmts s2 map HiFirrtl.Qnil tmap modmap) in
                HiFirrtl.Qcons (ns, res)


and trans_stmts ss map res tmap modmap =
  match ss with
  | Ast.Qnil -> res
  | Ast.Qcons (s, st) -> trans_stmts st map (trans_stmt s map res tmap modmap) tmap modmap

let trans_mod m modmap map = 
  match m with
  | Ast.FInmod (mv, pl, sl) -> 
    let flag = StringMap.find mv modmap in
    let ((hd_map, _), hd_tmap) = StringMap.find mv map in
    let newstmts = trans_stmts sl hd_map HiFirrtl.Qnil hd_tmap modmap in
    HiFirrtl.FInmod(Obj.magic flag, List.map (fun a -> Transhiast.trans_port a hd_map) pl, Transhiast.revstmts newstmts HiFirrtl.Qnil)
  | Ast.FExmod (mv, _, _) -> 
    let flag = StringMap.find mv modmap in
    HiFirrtl.FExmod(Obj.magic flag, [], HiFirrtl.Qnil)

let rec trans_modl ml modmap map = 
  match ml with
  | [] -> []
  | hd :: tl -> 
    let fmod = trans_mod hd modmap map in
    fmod :: (trans_modl tl modmap map)

let trans_cir cir modmap map = 
  match cir with
  | Ast.Fcircuit (cv, ml) -> 
    HiFirrtl.Fcircuit ((Obj.magic (StringMap.find cv modmap)), 
    (trans_modl ml modmap map))
