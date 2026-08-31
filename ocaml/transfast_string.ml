open Hifirrtl_lang
open Extraction

let rec trans_ports pp map tmap res = 
  match pp with
  | [] -> res
  | HiFirrtl.Finput (v, HiEnv.Gtyp ty) :: pp' -> (match Pair2string.pair_to_string (Obj.magic v) map tmap with
                              | Some nv ->
                                let nty = Pair2string.fgtyp_pair_to_string ty in
                                trans_ports pp' map tmap ((Ast.Finput (nv, Ast.Gtyp nty)) :: res)
                              | _ -> trans_ports pp' map tmap res)
  | HiFirrtl.Foutput (v, HiEnv.Gtyp ty) :: pp' -> (match Pair2string.pair_to_string (Obj.magic v) map tmap with
                              | Some nv ->
                                let nty = Pair2string.fgtyp_pair_to_string ty in
                                trans_ports pp' map tmap ((Ast.Foutput (nv, Ast.Gtyp nty)) :: res)
                              | _ -> trans_ports pp' map tmap res)

let trans_rst rst map tmap = 
  match rst with
  | HiFirrtl.NRst -> Some Ast.NRst
  | HiFirrtl.Rst (e1, e2) -> (match Pair2string.expr_pair_to_string e1 map tmap, Pair2string.expr_pair_to_string e2 map tmap with
                              | Some str_e1, Some str_e2 ->  Some (Ast.Rst (str_e1, str_e2))
                              | _, _ -> None)
    
let rec trans_stmt s map tmap res = 
  match s with
  | HiFirrtl.Swire (v, HiEnv.Gtyp ty) -> (match Pair2string.pair_to_string (Obj.magic v) map tmap with
                              | Some nv -> 
                                let nty = Pair2string.fgtyp_pair_to_string ty in
                                let ns = Ast.Swire (nv, Ast.Gtyp nty) in
                                Ast.Qcons (ns, res)
                              | _ -> res)
  | HiFirrtl.Sfcnct (Eid v, e) -> (match Pair2string.pair_to_string (Obj.magic v) map tmap, Pair2string.expr_pair_to_string e map tmap with
                              | Some nv, Some ne ->
                                let ns = Ast.Sfcnct (Eid nv, ne) in
                                Ast.Qcons (ns, res)
                              | _, _ -> res)
  | HiFirrtl.Sinvalid (Eid v) -> (match Pair2string.pair_to_string (Obj.magic v) map tmap with
                              | Some nv ->
                                let ns = Ast.Sinvalid (Eid nv) in
                                Ast.Qcons (ns, res)
                              | _ -> res)
  | HiFirrtl.Snode (v, e) -> (match Pair2string.pair_to_string (Obj.magic v) map tmap, Pair2string.expr_pair_to_string e map tmap with
                              | Some nv, Some ne ->
                                let ns = Ast.Snode (nv, ne) in
                                Ast.Qcons (ns, res)
                              | _, _ -> res)
  | HiFirrtl.Sreg (v, r) -> (match Pair2string.pair_to_string (Obj.magic v) map tmap, r.coq_type with
                              | Some nv, HiEnv.Gtyp ty ->
                                let nty = Pair2string.fgtyp_pair_to_string ty in
                                (match Pair2string.expr_pair_to_string r.clock map tmap, trans_rst r.reset map tmap with
                                | Some nclock, Some nrst -> 
                                  let ns = Ast.Sreg (nv, Ast.mk_freg_r (Ast.Gtyp nty) nclock nrst) in
                                  Ast.Qcons (ns, res)
                                | _, _ -> res)
                              | _ -> res)
  | HiFirrtl.Sinst (v, modv) -> (match Pair2string.pair_to_string (Obj.magic v) map tmap, Pair2string.pair_to_string (Obj.magic modv) map tmap with
                              | Some nv, Some nmodv -> 
                                let ns = Ast.Sinst (nv, nmodv) in
                                Ast.Qcons (ns, res)
                              | _, _ -> res)
  | HiFirrtl.Swhen (c, s1, s2) -> (match Pair2string.expr_pair_to_string c map tmap with
                              | Some nc ->
                                let ns1 = trans_stmts s1 map tmap Ast.Qnil in
                                let ns2 = trans_stmts s2 map tmap Ast.Qnil in
                                let ns = Ast.Swhen (nc, ns1, ns2) in
                                Ast.Qcons (ns, res)
                              | _ -> res)
  | _ -> res 

and trans_stmts ss map tmap res =
  match ss with
  | HiFirrtl.Qnil -> res
  | HiFirrtl.Qcons (s, st) -> trans_stmts st map tmap (trans_stmt s map tmap res)

let rec revstmts sts res = 
  match sts with 
  | Ast.Qnil -> res
  | Ast.Qcons (h, tl) -> revstmts tl (revstmt h res)
    
and revstmt st res =
  match st with
  | Ast.Swhen (c, s1, s2) -> Ast.Qcons ((Ast.Swhen (c, revstmts s1 Ast.Qnil, revstmts s2 Ast.Qnil)), res)
  | _ -> Ast.Qcons (st, res)

let trans_mod m modmap map = 
  match m with
  | HiFirrtl.FInmod (mv, pl, sl) -> 
    let mv_string = Transhiast.IntMap.find (fst (Obj.magic mv)) modmap in
    let ((map0, map1), tmap) = Transhiast.StringMap.find mv_string map in
    let newports = trans_ports pl map1 tmap [] in
    let newstmts = trans_stmts sl map1 tmap Ast.Qnil in
    Ast.FInmod(mv_string, newports, revstmts newstmts Ast.Qnil)
  | HiFirrtl.FExmod (mv, _, _) -> 
    let mv_string = Transhiast.IntMap.find (fst (Obj.magic mv)) modmap in
    Ast.FExmod(mv_string,[],Ast.Qnil)

let rec trans_modl ml modmap map =
  match ml with
  | [] -> []
  | hd :: tl -> 
    let m = trans_mod hd modmap map in
    m :: (trans_modl tl modmap map)

let trans_cir cir modmap map = 
  match cir with
  | HiFirrtl.Fcircuit (cv, ml) -> 
    Ast.Fcircuit (Transhiast.IntMap.find (fst (Obj.magic cv)) modmap, 
    (trans_modl ml modmap map))