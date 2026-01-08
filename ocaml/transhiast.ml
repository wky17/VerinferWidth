open Hifirrtl_lang
open Printf
open Nodehelper
open Extraction
open Extraction.Constraints
open Extraction.Extract_cswithmin
open Useocamlscc
open Big_int_Z
open Mlir_lang

module StringMap = Map.Make(String)
let initmap_s = StringMap.empty
module IntMap = Map.Make(Stdlib.Int)
let initmap_i = IntMap.empty

let rec mapbtyp_helper v (map, flag, flag') ft = 
  match ft with
  | Ast.Gtyp _ -> (StringMap.add v (flag' :: flag) map, flag' + 1)
  | Ast.Atyp (atyp, _) -> mapbtyp_helper v (map, flag, flag') atyp
  | Ast.Btyp btyp -> let map0 = StringMap.add v (flag' :: flag) map in
                     let (map1, _, flag'0) = mapbtyp v (map0, (flag' :: flag), 0) btyp in (map1, flag' + 1)
  and mapbtyp v (map, flag, flag') btyp =
  match btyp with 
  | Ast.Fnil -> (map, flag, flag')
  | Ast.Fflips (fv, _, ft, ff) -> let map0 = StringMap.add (v^"."^fv) (flag' :: flag) map in
                                  let (map1, flag'0) = mapbtyp_helper (v^"."^fv) (map0, flag, flag') ft in
                                  mapbtyp v (map1, flag, flag'0) ff

let rec mapftype v (map, flag) ft = 
match ft with
| Ast.Gtyp _ -> ((StringMap.add v [flag] map), flag+1)
| Ast.Atyp (atyp, _) -> mapftype v (map, flag) atyp
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

let binary_length (signed : bool) (n: Z.t) : int =
  if n = Z.zero then 1  
  else let bits = Z.numbits (Z.abs n) in
    if signed then
      if n > Z.zero then
        bits + 1
      else if (Z.popcount (Z.abs n)) = 1 then bits
        else bits + 1
    else bits

let rec int_to_bool_list n bits_remaining =
  if bits_remaining = 0 then []
  else
    let bit = Z.testbit n (bits_remaining - 1) in
    bit :: int_to_bool_list n (bits_remaining - 1)

let bits_of_z (n: Z.t) (bit_length: int) : bool list =
  let two_power_bit_length = Z.shift_left Z.one bit_length in
  let twos_complement =
    if n >= Z.zero then
      Z.rem n two_power_bit_length
    else
      Z.add two_power_bit_length (Z.rem n two_power_bit_length)
  in
  int_to_bool_list twos_complement bit_length

let rec trans_ftype v ty map = 
  match ty with
  | Ast.Gtyp gt -> HiEnv.Gtyp (trans_fgtyp gt)
  | Ast.Atyp (atyp, n) -> HiEnv.Atyp (trans_ftype v atyp map, n)
  | Ast.Btyp btyp -> HiEnv.Btyp (trans_btyp v btyp map)

and trans_btyp v btyp map =
  match btyp with
  | Ast.Fnil -> HiEnv.Fnil
  | Ast.Fflips (fv, fl, ft, ff) -> HiEnv.Fflips (Obj.magic (Stdlib.List.hd (StringMap.find (v^"."^fv) map)), trans_flip fl, trans_ftype (v^"."^fv) ft map, (trans_btyp v ff map))

let rec find_nat4v ref =
  match ref with
  | Ast.Eid v -> v
  | Ast.Esubfield (ref1, v) -> (find_nat4v ref1)^"."^v
  | Ast.Esubindex (ref1, _) -> (find_nat4v ref1)
  | Ast.Esubaccess (ref1, _) -> (find_nat4v ref1)

let rec trans_ref ref map = 
  match ref with
  | Ast.Eid v -> HiFirrtl.Eid (Obj.magic (Stdlib.List.hd (StringMap.find v map)))
  | Ast.Esubfield (r, _) ->  HiFirrtl.Esubfield (trans_ref r map, Obj.magic (Stdlib.List.hd (StringMap.find (find_nat4v ref) map)))
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
  | Ast.Swire (v, ty) -> 
                let ns = HiFirrtl.Swire(Obj.magic (Stdlib.List.hd (StringMap.find v map)), trans_ftype v ty map) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Sfcnct (ref, e) -> let ns = HiFirrtl.Sfcnct((trans_ref ref map), trans_expr e map) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Sinvalid ref -> let ns = HiFirrtl.Sinvalid ((trans_ref ref map)) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Snode (v, e) -> 
                let ns = HiFirrtl.Snode(Obj.magic (Stdlib.List.hd (StringMap.find v map)), trans_expr e map) in
                HiFirrtl.Qcons (ns, res)
  | Ast.Sreg (v, r) -> 
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
  | Ast.Finput (v, ty) -> HiFirrtl.Finput(Obj.magic (Stdlib.List.hd (StringMap.find v map)), trans_ftype v ty map)
  | Ast.Foutput (v, ty) -> HiFirrtl.Foutput(Obj.magic (Stdlib.List.hd (StringMap.find v map)), trans_ftype v ty map)

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
