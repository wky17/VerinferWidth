open Hifirrtl_lang
open Printf
open Nodehelper
open Extraction
open Extraction.Constraints
open Extraction.Extract_cswithmin
(*open Extraction.TopoSort*)
open Useocamlscc
open Big_int_Z
open Mlir_lang

module StringMap = Map.Make(String)
let initmap_s = StringMap.empty
module IntMap = Map.Make(Stdlib.Int)
let initmap_i = IntMap.empty

let rec mapbtyp_helper v (map, flag, flag') ft = (* 这里flag是list，flag'是int *)
  match ft with
  | Ast.Gtyp _ -> (StringMap.add v (flag' :: flag) map, flag' + 1)
  | Ast.Atyp (atyp, _) -> (*mapbtyp_helper (v^"[0]") (StringMap.add v (flag' :: flag) map, flag, flag' + 1) atyp*)
                            mapbtyp_helper v (map, flag, flag') atyp
  | Ast.Btyp btyp -> let map0 = StringMap.add v (flag' :: flag) map in
                     let (map1, _, flag'0) = mapbtyp v (map0, (flag' :: flag), 0) btyp in (map1, flag' + 1)
  and mapbtyp v (map, flag, flag') btyp =
  match btyp with 
  | Ast.Fnil -> (map, flag, flag')
  | Ast.Fflips (fv, _, ft, ff) -> let map0 = StringMap.add (v^"."^fv) (flag' :: flag) map in
                                  let (map1, flag'0) = mapbtyp_helper (v^"."^fv) (map0, flag, flag') ft in
                                  mapbtyp v (map1, flag, flag'0) ff

let rec mapftype v (map, flag) ft = (* 这里flag是int *)
match ft with
| Ast.Gtyp _ -> ((StringMap.add v [flag] map), flag+1)
| Ast.Atyp (atyp, _) -> (*mapftype (v^"[0]") (StringMap.add v [flag] map, flag + 1) atyp*)mapftype v (map, flag) atyp
| Ast.Btyp btyp -> let (map0, _, _) = mapbtyp v (StringMap.add v [flag] map, [flag], 0) btyp in
                   (map0, flag + 1)
  
let mapport ((map, flag), tmap) p = 
  match p with
  | Ast.Finput (v, ty) -> (mapftype v (map, flag) ty, StringMap.add v ty tmap)
  | Ast.Foutput (v, ty) -> (mapftype v (map, flag) ty, StringMap.add v ty tmap)

let rec mapstmt ((map, flag), tmap) stmt = 
  match stmt with
  | Ast.Swire (v, ty) -> (mapftype v (map, flag) ty, StringMap.add v ty tmap)
  | Ast.Sreg (v, r) -> (mapftype v (map, flag) r.coq_type, StringMap.add v r.coq_type tmap)
  | Ast.Smem (v, _) -> ((StringMap.add v [flag] map, flag + 1), tmap)
  | Ast.Snode (v, e) -> (match type_of_hfexpr e tmap with
                      | Some ty -> (mapftype v (map, flag) ty, StringMap.add v ty tmap)
                      | None -> printf "%s wrong expr type\n" v; Ast.pp_expr stdout e; ((map, flag), tmap))
  | Ast.Sinst (v, _) -> ((StringMap.add v [flag] map, flag + 1), tmap)
  | Ast.Sinferport (v, r, _) -> (match type_of_ref r tmap with
                      | Some ty -> (mapftype v (map, flag) ty, StringMap.add v ty tmap)
                      | None -> ((map, flag), tmap))
  | Ast.Swhen (_, s1, s2) -> mapstmts (mapstmts ((map, flag), tmap) s1) s2
  | _ -> ((map,flag), tmap)

 and mapstmts ((map, flag), tmap) stmts = 
  match stmts with
  | Ast.Qnil -> ((map, flag), tmap)
  | Ast.Qcons (s, ss) -> mapstmts (mapstmt ((map, flag), tmap) s) ss

let mapmod ((map, flag), tmap) m =  
  match m with 
  | Ast.FInmod (_, pl, sl) -> let ((map0, flag0), tmap0) = List.fold_left mapport pl ((map, flag), tmap) in
                              mapstmts ((map0, flag0),tmap0) sl 
  | _ -> ((map, flag), tmap)

let mapcir cir = 
  match cir with
  | Ast.Fcircuit (_, ml) -> mapmod ((initmap_s, 0), initmap_s) (Stdlib.List.hd ml)

(*transast*)

let trans_fgtyp ty = 
  match ty with
  | Ast.Fuint s -> Env.Fuint s
  | Ast.Fsint s -> Env.Fsint s
  | Ast.Fuint_implicit s -> Env.Fuint_implicit s
  | Ast.Fsint_implicit s -> Env.Fsint_implicit s
  | Ast.Fclock -> Env.Fclock
  | Ast.Freset -> Env.Freset
  | Ast.Fasyncreset -> Env.Fasyncreset

let trans_flip f = 
  match f with
  | Ast.Flipped -> HiEnv.Flipped
  | Ast.Nflip -> HiEnv.Nflip

let trans_ucast a_ucast = 
  match a_ucast with
  | Ast.AsUInt -> LoFirrtl.AsUInt
  | Ast.AsSInt -> LoFirrtl.AsSInt
  | Ast.AsClock -> LoFirrtl.AsClock
  | Ast.AsAsync -> LoFirrtl.AsAsync

let trans_eunop a_eunop = 
  match a_eunop with
  | Ast.Upad s -> LoFirrtl.Upad s
  | Ast.Ushl s -> LoFirrtl.Ushl s
  | Ast.Ushr s -> LoFirrtl.Ushr s
  | Ast.Ucvt -> LoFirrtl.Ucvt
  | Ast.Uneg -> LoFirrtl.Uneg
  | Ast.Unot -> LoFirrtl.Unot
  | Ast.Uandr -> LoFirrtl.Uandr
  | Ast.Uorr -> LoFirrtl.Uorr
  | Ast.Uxorr -> LoFirrtl.Uxorr
  | Ast.Uextr (s1, s2) -> LoFirrtl.Uextr (s1, s2)
  | Ast.Uhead s -> LoFirrtl.Uhead s
  | Ast.Utail s -> LoFirrtl.Utail s

let trans_cmp a_cmp = 
  match a_cmp with
  | Ast.Blt -> LoFirrtl.Blt
  | Ast.Bleq -> LoFirrtl.Bleq
  | Ast.Bgt -> LoFirrtl.Bgt
  | Ast.Bgeq -> LoFirrtl.Bgeq
  | Ast.Beq -> LoFirrtl.Beq
  | Ast.Bneq -> LoFirrtl.Bneq

let trans_ebinop a_ebinop = 
  match a_ebinop with
  | Ast.Badd -> LoFirrtl.Badd
  | Ast.Bsub -> LoFirrtl.Bsub
  | Ast.Bmul -> LoFirrtl.Bmul
  | Ast.Bdiv -> LoFirrtl.Bdiv
  | Ast.Brem -> LoFirrtl.Brem
  | Ast.Bcomp s -> LoFirrtl.Bcomp (trans_cmp s)
  | Ast.Bdshl -> LoFirrtl.Bdshl
  | Ast.Bdshr -> LoFirrtl.Bdshr
  | Ast.Band -> LoFirrtl.Band
  | Ast.Bor -> LoFirrtl.Bor
  | Ast.Bxor -> LoFirrtl.Bxor
  | Ast.Bcat -> LoFirrtl.Bcat

(*let bits_of_z (size : int) (z : Z.t) =
    let binstr =
      if z >= Z.zero then
        Z.format ("%0" ^ (string_of_int size) ^ "b") z
      else
        Z.format ("%0" ^ (string_of_int size) ^ "b")
          (Z.add (Z.pow (Z.of_int 2) size) z) in
    let rec helper i max str res =
      if i >= max then res
      else match String.get str i with
      | '0' -> helper (succ i) max str (false::res)
      | '1' -> helper (succ i) max str (true::res)
      | _ -> assert false in
    helper 0 (String.length binstr) binstr []*)

(* 定义函数，计算二进制表示的长度 *)
let binary_length (signed : bool) (n: Z.t) : int =
  if n = Z.zero then 1  (* 特殊情况：0 的补码表示为 "0"，长度为 1 *)
  else let bits = Z.numbits (Z.abs n) in
    if signed then
      if n > Z.zero then
        bits + 1
      else if (Z.popcount (Z.abs n)) = 1 then bits
        else bits + 1
    else bits

(* 辅助函数：将整数转换为布尔列表表示的二进制数 *)
let rec int_to_bool_list n bits_remaining =
  if bits_remaining = 0 then []
  else
    let bit = Z.testbit n (bits_remaining - 1) in
    bit :: int_to_bool_list n (bits_remaining - 1)

(* 主函数：将整数转换为指定位长的二进制补码表示，并用 bool list 表示 *)
let bits_of_z (n: Z.t) (bit_length: int) : bool list =
  (* 计算 2^bit_length 的值 *)
  let two_power_bit_length = Z.shift_left Z.one bit_length in
  (* 计算补码表示 *)
  let twos_complement =
    if n >= Z.zero then
      Z.rem n two_power_bit_length
    else
      Z.add two_power_bit_length (Z.rem n two_power_bit_length)
  in
  (* 将补码表示转换为布尔列表 *)
  int_to_bool_list twos_complement bit_length

let rec trans_ftype v ty map = 
  match ty with
  | Ast.Gtyp gt -> HiEnv.Gtyp (trans_fgtyp gt)
  | Ast.Atyp (atyp, n) -> HiEnv.Atyp (trans_ftype v atyp map, n)
  | Ast.Btyp btyp -> HiEnv.Btyp (trans_btyp v btyp map)

and trans_btyp v btyp map =
  match btyp with
  | Ast.Fnil -> HiEnv.Fnil
  | Ast.Fflips (fv, fl, ft, ff) -> (*printf "%s\n" (v^"."^fv);*) HiEnv.Fflips (Obj.magic (Stdlib.List.hd (StringMap.find (v^"."^fv) map)), trans_flip fl, trans_ftype (v^"."^fv) ft map, (trans_btyp v ff map))

let rec find_nat4v ref =
  match ref with
  | Ast.Eid v -> v
  | Ast.Esubfield (ref1, v) -> (find_nat4v ref1)^"."^v
  | Ast.Esubindex (ref1, _) -> (find_nat4v ref1) (*"["^(Stdlib.Int.to_string n)^"]"*)
  | Ast.Esubaccess (ref1, _) -> (find_nat4v ref1)

let rec trans_ref ref map = 
  match ref with
  | Ast.Eid v -> (*printf "%s\n" v;*) HiFirrtl.Eid (Obj.magic (Stdlib.List.hd (StringMap.find v map)))
  | Ast.Esubfield (r, _) -> (*printf "%s\n" (find_nat4v ref);*) HiFirrtl.Esubfield (trans_ref r map, Obj.magic (Stdlib.List.hd (StringMap.find (find_nat4v ref) map)))
  | Ast.Esubindex (r, n) -> HiFirrtl.Esubindex (trans_ref r map, n)
  | Ast.Esubaccess (r, _) -> (trans_ref r map)

let rec trans_expr e map = 
  match e with
  | Ast.Econst (ty, s) -> (match ty with
    | Ast.Fuint_implicit _ -> HiFirrtl.Econst (trans_fgtyp (Ast.Fuint (binary_length false s)), bits_of_z s (binary_length false s))
    | Ast.Fsint_implicit _ -> HiFirrtl.Econst (trans_fgtyp (Ast.Fsint (binary_length true s)), bits_of_z s (binary_length true s))
    | _ -> HiFirrtl.Econst (trans_fgtyp ty, bits_of_z s (Env.sizeof_fgtyp (trans_fgtyp ty))))
  | Ast.Eref v -> HiFirrtl.Eref (trans_ref v map)
  | Ast.Eprim_unop (op, e1) -> HiFirrtl.Eprim_unop(trans_eunop op, trans_expr e1 map)
  | Ast.Eprim_binop (bop, e1, e2) -> HiFirrtl.Eprim_binop(trans_ebinop bop, trans_expr e1 map, trans_expr e2 map)
  | Ast.Emux (e1,e2,e3) -> HiFirrtl.Emux(trans_expr e1 map, trans_expr e2 map, trans_expr e3 map)
  (*| Ast.Evalidif (e1,e2) -> HiFirrtl.Evalidif(trans_expr e1 map,trans_expr e2 map)*)
  | Ast.Ecast (s, e) -> HiFirrtl.Ecast(trans_ucast s, trans_expr e map)
  
let trans_ruw r = 
  match r with
  | Ast.Coq_old -> LoFirrtl.Coq_old
  | Ast.Coq_new -> LoFirrtl.Coq_new
  | Ast.Coq_undefined -> LoFirrtl.Coq_undefined

let trans_rst rst map = 
  match rst with
  | Ast.NRst -> HiFirrtl.NRst
  | Ast.Rst (e1, e2) -> HiFirrtl.Rst(trans_expr e1 map, trans_expr e2 map)

let mk_freg t c r = { HiFirrtl.coq_type = t; clock = c; reset = r}

let rec trans_stmt s map res tmap = 
  match s with
  | Ast.Sskip -> HiFirrtl.Qcons (HiFirrtl.Sskip, res)
  | Ast.Swire (v, ty) -> (*printf "%s\n" v;*) 
                let ns = HiFirrtl.Swire(Obj.magic (Stdlib.List.hd (StringMap.find v map)), trans_ftype v ty map) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Sfcnct (ref, e) -> let ns = HiFirrtl.Sfcnct((trans_ref ref map), trans_expr e map) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Sinvalid ref -> let ns = HiFirrtl.Sinvalid ((trans_ref ref map)) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Snode (v, e) -> (*printf "%s\n" v;*) 
                let ns = HiFirrtl.Snode(Obj.magic (Stdlib.List.hd (StringMap.find v map)), trans_expr e map) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Sreg (v, r) -> (*printf "%s\n" v;*) 
                let ns = HiFirrtl.Sreg (Obj.magic (Stdlib.List.hd (StringMap.find v map)), mk_freg (trans_ftype v r.coq_type map) (trans_expr r.clock map) (trans_rst r.reset map)) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Sinferport (v, r, e_clock) -> (match type_of_ref r tmap with
                  | Some ty -> let fv = Obj.magic (Stdlib.List.hd (StringMap.find v map)) in
                               let s1 = HiFirrtl.Sreg (fv, mk_freg (trans_ftype v ty map) (trans_expr e_clock map) HiFirrtl.NRst) in
                               let s2 = HiFirrtl.Sfcnct(Eid fv, Eref (trans_ref r map)) in
                               let s3 = HiFirrtl.Sfcnct(trans_ref r map, HiFirrtl.Eref (Eid fv)) in
                    HiFirrtl.Qcons (s3, Qcons (s2, Qcons (s1, res)))
                  | None -> res)
  | Ast.Smem _ -> res
  | Ast.Sinst _ -> res
  | Ast.Swhen (c, s1, s2) -> let ns = HiFirrtl.Swhen (trans_expr c map, trans_stmts s1 map HiFirrtl.Qnil tmap, trans_stmts s2 map HiFirrtl.Qnil tmap) in
                    HiFirrtl.Qcons (ns, res)


and trans_stmts ss map res tmap =
  match ss with
  | Ast.Qnil -> res
  | Ast.Qcons (s, st) -> trans_stmts st map (trans_stmt s map res tmap) tmap

let trans_port p map = 
  match p with
  | Ast.Finput (v, ty) -> (*printf "%s\n" v;*) HiFirrtl.Finput(Obj.magic (Stdlib.List.hd (StringMap.find v map)), trans_ftype v ty map)
  | Ast.Foutput (v, ty) -> (*printf "%s\n" v;*) HiFirrtl.Foutput(Obj.magic (Stdlib.List.hd (StringMap.find v map)), trans_ftype v ty map)

let rec revstmts sts res = 
  match sts with 
  | HiFirrtl.Qnil -> res
  | Qcons (h, tl) -> revstmts tl (revstmt h res)
    
and revstmt st res =
  match st with
  | HiFirrtl.Swhen (c, s1, s2) -> HiFirrtl.Qcons ((HiFirrtl.Swhen (c, revstmts s1 HiFirrtl.Qnil, revstmts s2 HiFirrtl.Qnil)), res)
  | _ -> Qcons (st, res)

let trans_mod m map flag tmap = 
  match m with
  | Ast.FInmod (_, pl, sl) -> let newstmts = trans_stmts sl map HiFirrtl.Qnil tmap in
                              HiFirrtl.FInmod(Obj.magic flag, List.map (fun a -> trans_port a map) pl, revstmts newstmts HiFirrtl.Qnil)
  | Ast.FExmod (_, pl, sl) -> let newstmts = trans_stmts sl map HiFirrtl.Qnil tmap in
                              HiFirrtl.FExmod(Obj.magic flag, List.map (fun a -> trans_port a map) pl, revstmts newstmts HiFirrtl.Qnil)

let trans_cir cir map flag tmap = 
  match cir with
  | Ast.Fcircuit (_, ml) -> HiFirrtl.Fcircuit ((Obj.magic flag), (trans_mod (Stdlib.List.hd ml) map (flag + 1) tmap) :: [])

let hiparse f =
  let lexbuf = Lexing.from_channel (open_in f) in
  FirrtlParser.file FirrtlLexer.token lexbuf

let pp_gtyp out ty =
  match ty with
  | Env.Fuint s -> output_string out "(Fuint "; output_string out (Stdlib.Int.to_string s); output_string out ")"
  | Fsint s -> output_string out "(Fsint "; output_string out (Stdlib.Int.to_string s); output_string out ")"
  | Fuint_implicit s -> output_string out "Fuint_implicit"
  | Fsint_implicit s -> output_string out "Fsint_implicit"
  | Freset -> output_string out "Freset"
  | Fasyncreset -> output_string out "Fasyncreset"
  | Fclock -> output_string out "Fclock"
 
let pp_flip out fl = 
  match fl with
  | HiEnv.Flipped -> output_string out "flip "
  | Nflip -> output_string out ""

let rec pp_ftype out ty = 
  match ty with
  | HiEnv.Gtyp gt -> output_string out "(Gtyp "; pp_gtyp out gt; output_string out ")"
  | Atyp (atyp, n) -> output_string out "(Atyp "; pp_ftype out atyp; output_string out ("["^(Stdlib.Int.to_string n)^"]")
  | Btyp btyp -> output_string out "({"; pp_fbtyp out btyp; output_string out "})";
 
and pp_fbtyp out ty = 
  match ty with
  | Fnil -> output_string out "Fnil"
  | Fflips (v, fl, ft, ff) -> pp_flip out fl; output_string out ((Stdlib.Int.to_string v)^" : "); pp_ftype out ft; output_string out "; "; pp_fbtyp out ff; output_string out ")"

let rec pp_expr out e =
 match e with
 | HiFirrtl.Econst (ty, s) -> output_string out "(econst "; pp_gtyp out ty; output_string out " [::b?])"
 | Eref v -> output_string out "(eref "; pp_ref out v; output_string out ")"
 | Eprim_unop (op, e1) -> output_string out "(eprim_unop ?"; pp_expr out e1; output_string out ")"
 | Eprim_binop (bop, e1, e2) -> output_string out "(eprim_binop ?"; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")"
 | Emux (e1,e2,e3)  -> output_string out "(emux "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out " "; pp_expr out e3; output_string out " "; output_string out ")"
 (*| Evalidif (e1,e2)  -> output_string out "(evalidif "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")"*)
 | Ecast (s, e) -> output_string out "(ecast ?"; output_string out " "; pp_expr out e; output_string out ")";

and pp_ref out ref = 
 match ref with
 | Eid v -> output_string out (Stdlib.Int.to_string v)
 | Esubfield (ref1, v) -> pp_ref out ref1; output_string out "."; output_string out (Stdlib.Int.to_string v)
 | Esubindex (ref1, n) -> pp_ref out ref1; output_string out "["; output_string out ((Stdlib.Int.to_string n)^"]")
 | Esubaccess (ref1, e) -> pp_ref out ref1; output_string out "."; pp_expr out e

let rec pp_stmts out sl = 
  match sl with
  | HiFirrtl.Qnil -> output_string out ""
  | Qcons (s, ss) -> pp_stmt out s; pp_stmts out ss
                             
and pp_stmt out s =
  match s with
  | Sskip -> output_string out "sskip\n"
  | Swire (v, ty) -> output_string out "swire "; output_string out ((Stdlib.Int.to_string v)^" : "); pp_ftype out ty; output_string out "\n"
  | Smem (v, m) -> output_string out "smem\n"
  | Sfcnct (e1, e2) -> pp_ref out e1; output_string out " <= "; pp_expr out e2; output_string out "\n"
  | Sinvalid v -> output_string out "sinvalid\n"
  | Sreg (v, r) -> output_string out "sreg \n" ; output_string out ((Stdlib.Int.to_string v)^" : ")
  | Snode (v, e) -> output_string out "snode\n"
  | Sinst (v, e) -> output_string out "sinst\n"
  | Swhen (c, s1, s2) -> output_string out "swhen cond :"; output_string out "\nthen [::"; pp_stmts out s1; output_string out "]\nelse \n [::"; pp_stmts out s2; output_string out "])\n"
  
let pp_cstrt1 out c1 = fprintf out "x(%d,%d) >= " (fst (Obj.magic c1.lhs_var1)) (snd (Obj.magic c1.lhs_var1));
    Stdlib.List.iter (fun (coe, var) -> fprintf out "%d * x(%d,%d) + " coe (fst (Obj.magic var)) (snd (Obj.magic var))) c1.rhs_terms1;
    Stdlib.List.iter (fun (_, var) -> fprintf out "2 ^ x(%d,%d) + " (fst (Obj.magic var)) (snd (Obj.magic var))) c1.rhs_power;
    fprintf out "%d\n" c1.rhs_const1

let rec pp_min_rhs out r =
  match r with
  | Extract_cswithmin.Expr e ->
    Stdlib.List.iter (fun (coe, var) -> fprintf out "%d * x(%d,%d) + " coe (fst (Obj.magic var)) (snd (Obj.magic var))) e.regular_terms;
    Stdlib.List.iter (fun (_, var) -> fprintf out "2 ^ x(%d,%d) + " (fst (Obj.magic var)) (snd (Obj.magic var))) e.regular_power;
    fprintf out "%d" e.regular_const
  | Min (min1, min2) -> fprintf out "min("; pp_min_rhs out min1; fprintf out ","; pp_min_rhs out min2; fprintf out ")"

let pp_cstrt_min out c1 = fprintf out "x(%d,%d) >= " (fst (Obj.magic c1.lhs_var_min)) (snd (Obj.magic c1.lhs_var_min));
  pp_min_rhs out c1.rhs_expr_min; fprintf out "\n"
    
let pp_cstrt2 out c2 = fprintf out "1 >= "; pp_min_rhs out c2; fprintf out "\n"

let pp_cstrt2_new out c2 = fprintf out "%d >= " c2.lhs_const2_new;
Stdlib.List.iter (fun (coe, var) -> fprintf out "%d * x(%d,%d) + " coe (fst (Obj.magic var)) (snd (Obj.magic var))) c2.rhs_terms2_new; fprintf out "0\n"

(*let pp_cstrt out c =
  match c with
  | Constraints.Phi1 c1 -> pp_cstrt1 out c1
  | Phi2 c2 -> pp_cstrt2_new out c2


let my_solve c =
  match Extract_cs.extract_constraints_c c with
  | Some p ->
    let (c1map, cs2) = p in
    let cs1 = Stdlib.List.concat (snd (Stdlib.List.split (HiFirrtl.PVM.elements c1map))) in
    let dpdcg = build_graph_from_constraints cs1 in
    let res = SCC.scc_list dpdcg in
    let res' = Stdlib.List.map (fun l -> Stdlib.List.map (fun v-> nat_to_pair (G.V.label v)) l) res in
    Solve_fun.solve_alg_check res' c1map cs2
  | None -> None

let my_coq_InferWidths_fun c =
  match HiFirrtl.circuit_tmap c with
    | Some tmap ->
      (match my_solve c with
      | Some solution ->
        let Fcircuit (cv, l) = c in
        (match l with
          | [] -> None
          | h :: l0 ->
            (match h with
            | FInmod (mv, ps, ss) ->
              (match l0 with
                | [] ->
                  (match Solve_fun.update_tmap tmap (HiFirrtl.PVM.elements solution) with
                  | Some newtm ->
                    (match Solve_fun.coq_InferWidths_transps ps newtm with
                      | Some nps ->
                        (match Solve_fun.coq_InferWidths_transss ss newtm with
                        | Some nss ->
                          Some (HiFirrtl.Fcircuit (cv, ((FInmod (mv, nps, nss)) :: [])), newtm)
                        | None -> None)
                      | None -> None)
                  | None -> None)
                | _ :: _ -> None)
            | FExmod (_, _, _) -> None))
      | None -> None)
    | None -> None
*)
let pp_bits bs = Stdlib.List.iter (printf "%b;") bs; printf "\n"

let fir_mlir_gt_eq mlir_gt fir_gt =
  match mlir_gt, fir_gt with
  | Mast.Fuint n0, Env.Fuint n1 
  | Fuint n0, Fuint_implicit n1
  | Fuint_implicit n0, Fuint n1
  | Fuint_implicit n0, Fuint_implicit n1
  | Fsint n0, Fsint n1 
  | Fsint n0, Fsint_implicit n1
  | Fsint_implicit n0, Fsint n1
  | Fsint_implicit n0, Fsint_implicit n1 -> n0 = n1
  | Fclock, Fclock
  | Fasyncreset, Fasyncreset
  | Freset, Freset -> true
  | _, _ -> false

let rec fir_mlir_ty_eq mlir_ty fir_ty = 
  match mlir_ty, fir_ty with
  | Mast.Gtyp gt0, HiEnv.Gtyp gt1 -> fir_mlir_gt_eq gt0 gt1
  | Atyp (ft0, n0), Atyp (ft1, n1) -> (fir_mlir_ty_eq ft0 ft1) && (n0 = n1)
  | Btyp ft0, Btyp ft1 -> fir_mlir_bty_eq ft0 ft1
  | _, _ -> false
and fir_mlir_bty_eq mlir_bty fir_bty =
  match mlir_bty, fir_bty with
  | Mast.Fnil, HiEnv.Fnil -> true
  | Fflips (_, Mast.Nflip, ft0, ff0), Fflips (_, HiEnv.Nflip, ft1, ff1) -> (fir_mlir_ty_eq ft0 ft1) && (fir_mlir_bty_eq ff0 ff1)
  | Fflips (_, Mast.Flipped, ft0, ff0), Fflips (_, Flipped, ft1, ff1) -> (fir_mlir_ty_eq ft0 ft1) && (fir_mlir_bty_eq ff0 ff1)
  | _, _ -> false

let process_string str suffix =
  let len = String.length str in
  if len >= 4 && String.sub str (len - 4) 4 = ".fir" then
    String.sub str 0 (len - 4) ^ suffix
  else
    str 

open Str
let convert_path path =
  Str.global_replace (Str.regexp "\\(.*/\\)preprowhen/\\(.*\\)\\.fir$") "\\1mlir/\\2.mlir" path

(*let inline_transf in_file hif_ast = 
  let flatten_cir = Inline.inline_cir stdout hif_ast in 
  output_string stdout ("flattened\n"); 

  match flatten_cir with
  | Ast.Fcircuit (v, ml) -> 
    (* generate numbering *)
    let ((map0, flag), tmap_ast) = mapcir flatten_cir in 
    (*StringMap.iter (fun key value -> output_string stdout (key^": ["); Stdlib.List.iter (printf "%d;") value; output_string stdout "]\n") map0;*)

    (* generate firrtl circuit *)
    let fcir = trans_cir flatten_cir map0 flag tmap_ast in 
    match HiFirrtl.circuit_tmap fcir with
    | Some tmap ->(
    
    (*let oc_fir = open_out (process_string in_file "_iw.fir") in
    let oc_cons = open_out (process_string in_file "_cons.txt") in
    let oc_res_num = open_out (process_string in_file "_res_num.txt") in
    let oc_res_str = open_out (process_string in_file "_res_str.txt") in*)
    (*let mfile = convert_path in_file in
    let mlirf = Mparser.mlirparse mfile in 
    let inlined = Mast.inline_cir mlirf in 
    let mlirmap = Mast.mapcir inlined in*)

    (* extract constraint *)
    let ut0 = (Unix.times()).tms_utime in 
    match Extract_cs.extract_constraints_c fcir tmap with
    | Some c1map_cs2 -> let (c1map, cs2) = Stdlib.List.hd c1map_cs2 in
                let ut1 = (Unix.times()).tms_utime in 
                let cs1 = Stdlib.List.concat (snd (Stdlib.List.split (HiFirrtl.PVM.elements c1map))) in
                (*output_string out ("constraint1 length : "^(Stdlib.Int.to_string (Stdlib.List.length cs1))^"\n");
                output_string out ("constraint2 length : "^(Stdlib.Int.to_string (Stdlib.List.length cs2))^"\n");*)
                Stdlib.List.iter (pp_cstrt1 stdout) cs1;
                Stdlib.List.iter (pp_cstrt2 stdout) cs2;

    let ut2 = (Unix.times()).tms_utime in 
    let g = build_graph_from_constraints cs1 in
    output_string stdout ("depandency graph built\n");

    let ut3 = (Unix.times()).tms_utime in 
    let scc_list = SCC.scc_list g in
    output_string stdout ("compute scc\n");
    let ut4 = (Unix.times()).tms_utime in 
    let res = Stdlib.List.map (fun l -> Stdlib.List.map (fun v-> nat_to_pair (G.V.label v)) l) scc_list in
    
    (*Stdlib.List.iteri (fun i component ->
      Printf.printf "SCC %d: [ " (i + 1);
      Stdlib.List.iter (fun v -> Printf.printf "(%d,%d) " (fst v) (snd v)) component;
      Printf.printf "]\n"
    ) res;

    Stdlib.List.iter (fun component ->
      if (Stdlib.List.length component > 1) then
        (Stdlib.List.iter (fun v -> Printf.printf "(%d,%d) " (fst v) (snd v)) component;
        printf "\nis simple_cycle : %b\n" (Solve_fun.is_simple_cycle component cs1);)
    ) res;

    let hd = [(5,0);(4,0);(3,0)] in
    let cs = (Extract_cs.extract_cs hd c1map) in
    let m = Floyd_sc.floyd_loop_map hd cs in
    let init = Floyd_sc.init_dist_map hd cs in
    let m' = Floyd_sc.floyd_update (3,0) (5,0) (Stdlib.List.map (fun p -> Floyd_sc.Node p) [(5,0);(4,0);(3,0)]) init in

    Stdlib.List.iter (fun (v, value) -> printf "(%d,%d) : " (fst v) (snd v);
      Stdlib.List.iter (fun (v', w) -> match v' with
        | Floyd_sc.Zero -> printf "-> 0 : %d; " w 
        | Floyd_sc.Node node -> printf "-> (%d,%d) : %d; " (fst node) (snd node) w) (Floyd_sc.NVM.elements value);
      printf "\n")
         (HiFirrtl.PVM.elements m');

    Stdlib.List.iter (pp_cstrt1 stdout) cs;
    let hd_cs = Stdlib.List.nth cs 0 in
    pp_cstrt1 stdout hd_cs;
    
    (match Simple_cycle.simplify_constraint (4,0) 2 1 1 hd_cs cs initial_valuation with
    | Some value -> printf "%d\n" value
    | _ -> printf "no value\n");

    match Simple_cycle.solve_simple_cycle' 3 (4,0) (Extract_cs.extract_cs hd c1map) initial_valuation with
    | Some _ -> printf "solved\n";
    | _ -> printf "wrong\n";);
    match Scc.solve_ubs hd hd (Extract_cs.extract_cs hd c1map) with
             | Some nv -> printf "solved";
             | _ -> printf "wrong ubs\n";);
    match Scc.solve_ub (2,0) hd (Extract_cs.extract_cs hd c1map) with
    | Some ub -> printf "%d\n" ub;
    | _ -> printf "wrong ub\n";);
    Stdlib.List.iter (pp_cstrt1 stdout) (Scc.substitute_vs [(3,0);(4,0)] (Extract_cs.extract_cs hd c1map));
    *)
    

    let ut5 = (Unix.times()).tms_utime in 
                (match Solve_fun.solve_alg res [] initial_valuation c1map with
                | Some values -> 
                  let ut6 = (Unix.times()).tms_utime in 
                  (*output_string stdout ("solved\n");*)
                  
                  (* update and print result *)
                  (match Solve_fun.update_tmap tmap (HiFirrtl.PVM.elements values) with
                  | Some newtm ->
                    Stdlib.List.iter (fun (var, value) -> printf (*oc_res_num*) "x(%d,%d) : %d\n" (fst (Obj.magic var)) (snd (Obj.magic var)) value) (HiFirrtl.PVM.elements values);
                    (*match my_coq_InferWidths_fun fcir with
                    | Some (newc, _) -> Printfir.pp_fcircuit_fir oc_fir v newc
                    | _ -> output_string stdout ("no inferred circuit\n"));*)

                    (*output_string stdout ("mlir tmap:\n");
                    StringMap.iter (fun key value -> 
                      (*output_string stdout (key^": "); Mast.pp_type stdout value; output_string stdout "\n";*)
                      match HiFirrtl.VM.find (Obj.magic (Stdlib.List.hd (Stdlib.List.rev (StringMap.find key map0)))) newtm with
                      | Some (ft, _) -> 
                        if (fir_mlir_ty_eq value ft) then printf "" else (
                            printf "%s\n%s : " in_file key; Printmlir.pp_ftype_mlir stdout ft; printf "<->"; Mast.pp_type stdout value; printf "\n")
                      | _ -> printf "%s not find\n" key
                      ) mlirmap;*)

                    (*output_string stdout ("coq inferred tmap:\n");
                    StringMap.iter (fun key value -> if (Stdlib.List.length value = 1) then 
                      (printf "%s : " key; 
                      match HiFirrtl.VM.find (Obj.magic (Stdlib.List.hd (Stdlib.List.rev (value)))) newtm with
                      | Some (ft, _) -> Printmlir.pp_ftype_mlir stdout ft; printf "\n";
                      | _ -> printf "wrong infer\n")) map0;*)

                    (* scale and time *)
                    (*printf "amount of implicit gtyp components : %d\n" (Stdlib.List.length (HiFirrtl.PVM.elements values));
                    printf "extract constraints : %f\ndraw graph : %f\ntarjan : %f\niw : %f\n"
                      (Float.sub ut1 ut0) (Float.sub ut3 ut2) (Float.sub ut4 ut3) (Float.sub ut6 ut5);*)
                  | _ -> printf "update error\n");

                | _ -> printf "solve error\n";);
    (*close_out oc_cons; close_out oc_fir; close_out oc_res_num; close_out oc_res_str*)

    | None -> output_string stdout "error extracting constraints\n");
    | _ -> output_string stdout "no circuit_map\n"*)


let try_mlir_parse f =
  let mlirf = Mparser.mlirparse f in 
  let inlined = Mast.inline_cir mlirf in 
  let mlirmap = Mast.mapcir inlined in
  (*Mast.pp_fcircuit stdout inlined;*)
  StringMap.iter (fun key value -> output_string stdout (key^": "); Mast.pp_type stdout value; output_string stdout "\n") mlirmap

let try_fir_parse f =
  output_string stdout f; output_string stdout "\n";
  let firf = Parser.hiparse f in 
  Ast.pp_fcircuit stdout firf
