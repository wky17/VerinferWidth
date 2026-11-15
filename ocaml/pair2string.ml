open Hifirrtl_lang
open Extraction
(* reflect a pair of natural number to its string name, according to its type. *)

let rec size_of_ftype = function
| Ast.Gtyp _ -> Stdlib.Int.succ 0
| Atyp (t0, n) -> (size_of_ftype t0) * n
| Btyp b -> size_of_fields b

and size_of_fields = function
| Fnil -> 0
| Fflips (_, _, t0, fs) -> (size_of_ftype t0) + (size_of_fields fs)

let rec offset_to_string base_id offset = function
| Ast.Gtyp gt ->
  if offset = 0 then base_id else "wrong name"
| Atyp (atyp, n) ->
  let index = offset / (size_of_ftype atyp) in
  let offset_new = offset mod (size_of_ftype atyp) in
  offset_to_string (base_id^"_"^(string_of_int index)) offset_new atyp
| Btyp ff -> offset_to_string_b base_id offset ff

and offset_to_string_b base_id offset = function
| Ast.Fnil -> base_id
| Fflips (v0, fl, ft, ff') ->
  if offset < (size_of_ftype ft)
    then offset_to_string (base_id^"_"^v0) offset ft
  else offset_to_string_b base_id (offset - (size_of_ftype ft)) ff'

let pair_to_string pv nummap tmap =
  match Transhiast.IntMap.find_opt (fst pv) nummap with
  | None -> None
  | Some base_id ->
      match Transhiast.StringMap.find_opt base_id tmap with
      | None -> None
      | Some ftype ->
          Some (offset_to_string base_id (snd pv) ftype)

let fgtyp_pair_to_string gt = 
  match gt with
  | Env.Fuint s -> Ast.Fuint s
  | Env.Fsint s -> Ast.Fsint s
  | Env.Fclock -> Ast.Fclock
  | Env.Freset -> Ast.Freset
  | Env.Fasyncreset -> Ast.Fasyncreset

let cast_pair_to_string ucast = 
  match ucast with
  | LoFirrtl.AsUInt -> Ast.AsUInt
  | LoFirrtl.AsSInt -> Ast.AsSInt
  | LoFirrtl.AsClock -> Ast.AsClock
  | LoFirrtl.AsAsync -> Ast.AsAsync

let eunop_pair_to_string eunop = 
  match eunop with
  | LoFirrtl.Upad s -> Ast.Upad s
  | LoFirrtl.Ushl s -> Ast.Ushl s
  | LoFirrtl.Ushr s -> Ast.Ushr s 
  | LoFirrtl.Ucvt -> Ast.Ucvt
  | LoFirrtl.Uneg -> Ast.Uneg
  | LoFirrtl.Unot -> Ast.Unot
  | LoFirrtl.Uandr -> Ast.Uandr
  | LoFirrtl.Uorr -> Ast.Uorr
  | LoFirrtl.Uxorr -> Ast.Uxorr
  | LoFirrtl.Uextr (s1, s2) -> Ast.Uextr (s1, s2)
  | LoFirrtl.Uhead s -> Ast.Uhead s
  | LoFirrtl.Utail s -> Ast.Utail s

let cmp_pair_to_string cmp = 
  match cmp with
  | LoFirrtl.Blt -> Ast.Blt 
  | LoFirrtl.Bleq -> Ast.Bleq
  | LoFirrtl.Bgt -> Ast.Bgt
  | LoFirrtl.Bgeq -> Ast.Bgeq
  | LoFirrtl.Beq -> Ast.Beq
  | LoFirrtl.Bneq -> Ast.Bneq

let binop_pair_to_string binop = 
  match binop with
  | LoFirrtl.Badd -> Ast.Badd
  | LoFirrtl.Bsub -> Ast.Bsub
  | LoFirrtl.Bmul -> Ast.Bmul
  | LoFirrtl.Bdiv -> Ast.Bdiv
  | LoFirrtl.Brem -> Ast.Brem
  | LoFirrtl.Bcomp s -> Ast.Bcomp (cmp_pair_to_string s)
  | LoFirrtl.Bdshl -> Ast.Bdshl
  | LoFirrtl.Bdshr -> Ast.Bdshr
  | LoFirrtl.Band -> Ast.Band
  | LoFirrtl.Bor -> Ast.Bor
  | LoFirrtl.Bxor -> Ast.Bxor
  | LoFirrtl.Bcat -> Ast.Bcat

let rec expr_pair_to_string e nummap tmap = 
  match e with
  | HiFirrtl.Econst (gt, bs) -> Some (match gt with
                          | Env.Fuint n -> Ast.Econst (fgtyp_pair_to_string gt, Printfir.nat_of_bits bs)
                          | Env.Fsint n -> Econst (fgtyp_pair_to_string gt, Printfir.z_of_bits bs)
                          | _ -> Econst (fgtyp_pair_to_string gt, Z.of_int 0))
  | HiFirrtl.Eref (Eid v) -> (match pair_to_string (Obj.magic v) nummap tmap with
                          | Some str -> Some (Eref (Eid str))
                          | _ -> None)
  | HiFirrtl.Eprim_unop (op, e) -> (match expr_pair_to_string e nummap tmap with
                          | Some str_e -> Some (Eprim_unop (eunop_pair_to_string op, str_e))
                          | _ -> None)
  | HiFirrtl.Eprim_binop (op, e1, e2) -> (match expr_pair_to_string e1 nummap tmap, expr_pair_to_string e2 nummap tmap with
                          | Some str_e1, Some str_e2 -> Some (Eprim_binop (binop_pair_to_string op, str_e1, str_e2))
                          | _, _ -> None)
  | HiFirrtl.Emux (e1,e2,e3) -> (match expr_pair_to_string e1 nummap tmap, expr_pair_to_string e2 nummap tmap, expr_pair_to_string e3 nummap tmap with
                          | Some str_e1, Some str_e2, Some str_e3 -> Some (Emux (str_e1, str_e2, str_e3))
                          | _, _, _ -> None)
  | HiFirrtl.Ecast (s, e) -> (match expr_pair_to_string e nummap tmap with
                          | Some str_e -> Some (Ecast(cast_pair_to_string s, str_e))
                          | _ -> None)
