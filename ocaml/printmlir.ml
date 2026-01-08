open Hifirrtl_lang
open Big_int_Z
open Printf
open Extraction
open HiFirrtl

let pp_fgtyp_mlir out gt =
  match gt with
  | Env.Fuint n -> fprintf out "uint<%d>" n
  | Env.Fsint n -> fprintf out "sint<%d>" n
  | Env.Fclock -> fprintf out "clock"
  | Env.Fasyncreset -> fprintf out "asyncreset"
  | Env.Fuint_implicit n -> fprintf out "uint<%d>" n
  | Env.Fsint_implicit n -> fprintf out "sint<%d>" n
  | Env.Freset -> fprintf out "reset"

let rec pp_ftype_mlir out ft = 
  match ft with
  | HiEnv.Gtyp gt -> pp_fgtyp_mlir out gt
  (*| HiEnv.Atyp _ -> fprintf out "array type\n"
  | HiEnv.Btyp _ -> fprintf out "bundle type\n"*)
  | HiEnv.Atyp (atyp, n) -> fprintf out "vector<"; pp_ftype_mlir out atyp; fprintf out ", %d>" n
  | HiEnv.Btyp btyp -> fprintf out "bundle<"; pp_fbtyp_mlir out btyp; fprintf out ">"

and pp_fbtyp_mlir out btyp =
  match btyp with
  | HiEnv.Fnil -> fprintf out ""
  | HiEnv.Fflips (fv, HiEnv.Nflip, ft, Fnil) -> fprintf out "f%d : " fv; pp_ftype_mlir out ft
  | HiEnv.Fflips (fv, HiEnv.Flipped, ft, Fnil) -> fprintf out "f%d flip : " fv; pp_ftype_mlir out ft
  | HiEnv.Fflips (fv, HiEnv.Nflip, ft, ff) -> fprintf out "f%d : " fv; pp_ftype_mlir out ft; fprintf out ", "; pp_fbtyp_mlir out ff
  | HiEnv.Fflips (fv, HiEnv.Flipped, ft, ff) -> fprintf out "f%d flip : " fv; pp_ftype_mlir out ft; fprintf out ", "; pp_fbtyp_mlir out ff

let rec pp_ref_mlir out eflag ft ref =
  match ft, ref with
  | _, HiFirrtl.Eid v -> ("%"^Stdlib.Int.to_string (Obj.magic v), eflag)
  | HiEnv.Atyp (f, _), Esubindex (r, n) -> let (eflag0, eflag1) = pp_ref_mlir out eflag ft r in
    fprintf out "%%e%d = firrtl.subindex %s[%d] : !firrtl." eflag1 eflag0 n; pp_ftype_mlir out ft; fprintf out "\n";
    ("%e"^Stdlib.Int.to_string eflag1, eflag1 + 1)
  | HiEnv.Btyp ff, Esubfield (r, v) -> let (eflag0, eflag1) = pp_ref_mlir out eflag ft r in
    fprintf out "%%e%d = firrtl.subfield %s[f%d] : !firrtl." eflag1 eflag0 (Obj.magic v); pp_ftype_mlir out ft; fprintf out "\n";
    ("%e"^Stdlib.Int.to_string eflag1, eflag1 + 1)
  | _, _ -> ("abc", eflag)

let rec expand_ref ref = 
  match ref with
  | HiFirrtl.Eid v -> "%"^Stdlib.Int.to_string (Obj.magic v)
  | Esubindex (r, n) -> (expand_ref r)^"["^(Stdlib.Int.to_string n)^"]"
  | Esubfield (r, v) -> (expand_ref r)^"[f"^(Stdlib.Int.to_string (Obj.magic v))^"]"
  | _ -> ""

let pp_port_mlir out p =
  match p with 
  | HiFirrtl.Finput (v, ft) -> fprintf out "in %%%d: !firrtl." (Obj.magic v); pp_ftype_mlir out ft
  | HiFirrtl.Foutput (v, ft) -> fprintf out "out %%%d: !firrtl." (Obj.magic v); pp_ftype_mlir out ft

let rec pp_ports_mlir out pl =
  match pl with
  | [] -> fprintf out ""
  | p :: [] -> pp_port_mlir out p
  | p :: tl -> pp_port_mlir out p; fprintf out ", "; pp_ports_mlir out tl

let sizeof_ftype ft =
  match ft with
  | HiEnv.Gtyp gt -> Env.sizeof_fgtyp gt
  | _ -> 0

let nat_of_bits bv = 
  let rec helper i max lst res =
    if i >= max then res
    else match Stdlib.List.nth bv i with
    | false -> helper (succ i) max lst res
    | true -> helper (succ i) max lst (add_big_int (power_int_positive_int (2) i) res) in
  helper 0 (Stdlib.List.length bv) bv zero_big_int

let z_of_bits bv = 
  let (v,sign) = (Stdlib.List.tl bv, Stdlib.List.hd bv) in
  if sign then (sub_big_int (nat_of_bits v) (power_int_positive_int (2) ((Stdlib.List.length bv)-1)))
  else
    nat_of_bits v

(*let infer_cst signed bs =
  if signed then
    if (z_of_bits bs) == zero_big_int then 0 else (Stdlib.List.length bs + 1)
  else (Stdlib.List.length bs*)

let rec pp_expr_mlir out eflag tmap e = 
  match e with
  | HiFirrtl.Econst (gt, bs) -> (match gt with
                          | Env.Fuint _ -> fprintf out "%%e%d = firrtl.constant %s : !firrtl." eflag (string_of_big_int (nat_of_bits bs)); pp_fgtyp_mlir out gt; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag), eflag + 1)
                          | Env.Fsint _ -> fprintf out "%%e%d = firrtl.constant %s : !firrtl." eflag (string_of_big_int (z_of_bits bs)); pp_fgtyp_mlir out gt; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag), eflag + 1)
                          (*| Env.Fuint_implicit _ -> fprintf out "%%e%d = firrtl.constant %s : !firrtl." eflag (string_of_big_int (nat_of_bits bs)); pp_fgtyp_mlir out (Env.Fuint (Stdlib.List.length bs)); fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag), eflag + 1)
                          | Env.Fsint_implicit _ -> fprintf out "%%e%d = firrtl.constant %s : !firrtl." eflag (string_of_big_int (z_of_bits bs)); pp_fgtyp_mlir out (Env.Fsint (Stdlib.List.length bs)); fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag), eflag + 1*)
                          | _ -> printf "error const expression\n"; ("error const expression", eflag))
  | HiFirrtl.Ecast (c, e0) -> (let (eflag0, eflag1) = pp_expr_mlir out eflag tmap e0 in match c with
                          | LoFirrtl.AsUInt -> fprintf out "%%e%d = firrtl.asUInt %s : (!firrtl." eflag1 eflag0; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.AsSInt -> fprintf out "%%e%d = firrtl.asSInt %s : (!firrtl." eflag1 eflag0; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.AsClock -> fprintf out "%%e%d = firrtl.asClock %s : (!firrtl." eflag1 eflag0; (match HiFirrtl.type_of_hfexpr e0 tmap with
                                                                                                                | Some te0 -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl.clock"; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.AsAsync -> fprintf out "%%e%d = firrtl.asAsyncReset %s : (!firrtl." eflag1 eflag0; (match HiFirrtl.type_of_hfexpr e0 tmap with
                                                                                                                | Some te0 -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl.asyncreset"; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          (*| LoFirrtl.AsReset -> fprintf out "wrong expression asreset"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)*))
  | HiFirrtl.Eprim_unop (op, e0) -> (let (eflag0, eflag1) = pp_expr_mlir out eflag tmap e0 in match op with
                          | LoFirrtl.Upad s -> fprintf out "%%e%d = firrtl.pad %s, %d : (!firrtl." eflag1 eflag0 s; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.Ushl s -> fprintf out "%%e%d = firrtl.shl %s, %d : (!firrtl." eflag1 eflag0 s; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.Ushr s -> fprintf out "%%e%d = firrtl.shr %s, %d : (!firrtl." eflag1 eflag0 s; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.Ucvt -> fprintf out "%%e%d = firrtl.cvt %s : (!firrtl." eflag1 eflag0; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.Uneg -> fprintf out "%%e%d = firrtl.neg %s : (!firrtl." eflag1 eflag0; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.Unot -> fprintf out "%%e%d = firrtl.not %s : (!firrtl." eflag1 eflag0; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.Uandr -> fprintf out "%%e%d = firrtl.andr %s : (!firrtl." eflag1 eflag0; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.Uorr -> fprintf out "%%e%d = firrtl.orr %s : (!firrtl." eflag1 eflag0; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.Uxorr -> fprintf out "%%e%d = firrtl.xorr %s : (!firrtl." eflag1 eflag0; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.Uextr (s1, s2) -> fprintf out "%%e%d = firrtl.bits (%s,%d ,%d) : (!firrtl." eflag1 eflag0 s1 s2; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.Uhead s -> fprintf out "%%e%d = firrtl.head %s, %d : (!firrtl." eflag1 eflag0 s; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1))
                          | LoFirrtl.Utail s -> fprintf out "%%e%d = firrtl.tail %s, %d : (!firrtl." eflag1 eflag0 s; (match HiFirrtl.type_of_hfexpr e0 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag1), eflag1 + 1)))
  | HiFirrtl.Eprim_binop (op, e1, e2) -> (let (eflag0, eflag1) = pp_expr_mlir out eflag tmap e1 in
                          let (eflag2, eflag3) = pp_expr_mlir out eflag1 tmap e2 in match op with
                          | LoFirrtl.Badd -> fprintf out "%%e%d = firrtl.add %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                          | LoFirrtl.Bsub -> fprintf out "%%e%d = firrtl.sub %s, %s : (!firrtl." eflag3 eflag0 eflag2;
                                          (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                          | LoFirrtl.Bmul -> fprintf out "%%e%d = firrtl.mul %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                          | LoFirrtl.Bdiv -> fprintf out "%%e%d = firrtl.div %s, %s : (!firrtl." eflag3 eflag0 eflag2;
                                          (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                          | LoFirrtl.Brem -> fprintf out "%%e%d = firrtl.rem %s, %s : (!firrtl." eflag3 eflag0 eflag2;
                                          (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                          | LoFirrtl.Bcomp s -> (match s with
                                              | LoFirrtl.Blt -> fprintf out "%%e%d = firrtl.lt %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                                              (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                              | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                                              | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                                              | LoFirrtl.Bleq -> fprintf out "%%e%d = firrtl.leq %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                                              (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                              | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                                              | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                                              | LoFirrtl.Bgt -> fprintf out "%%e%d = firrtl.gt %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                                              (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                              | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                                              | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                                              | LoFirrtl.Bgeq -> fprintf out "%%e%d = firrtl.geq %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                                              (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                              | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                                              | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                                              | LoFirrtl.Beq -> fprintf out "%%e%d = firrtl.eq %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                                              (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                              | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                                              | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                                              | LoFirrtl.Bneq -> fprintf out "%%e%d = firrtl.neq %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                                              (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                                              | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                                              | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)))
                          | LoFirrtl.Bdshl -> fprintf out "%%e%d = firrtl.dshl %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                          | LoFirrtl.Bdshr -> fprintf out "%%e%d = firrtl.dshr %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                          | LoFirrtl.Band -> fprintf out "%%e%d = firrtl.and %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                          | LoFirrtl.Bor -> fprintf out "%%e%d = firrtl.or %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                          | LoFirrtl.Bxor -> fprintf out "%%e%d = firrtl.xor %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1))
                          | LoFirrtl.Bcat -> fprintf out "%%e%d = firrtl.cat %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag3), eflag3 + 1)))
  | HiFirrtl.Emux (c, e1, e2) -> let (eflag0, eflag1) = pp_expr_mlir out eflag tmap c in
                                 let (eflag2, eflag3) = pp_expr_mlir out eflag1 tmap e1 in 
                                 let (eflag4, eflag5) = pp_expr_mlir out eflag3 tmap e2 in 
                                 fprintf out "%%e%d = firrtl.mux(%s, %s, %s) : (!firrtl." eflag5 eflag0 eflag2 eflag4;
                                 (match HiFirrtl.type_of_hfexpr c tmap, HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap, HiFirrtl.type_of_hfexpr e tmap with
                                 | Some tc, Some te1, Some te2, Some te -> pp_ftype_mlir out tc; fprintf out ", !firrtl."; pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; ("%e"^(Stdlib.Int.to_string eflag5), eflag5 + 1)
                                 | _, _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Stdlib.Int.to_string eflag5), eflag5 + 1))
  | HiFirrtl.Eref (Eid r) -> ("%"^(Stdlib.Int.to_string (Obj.magic r)), eflag) 
  | Eref r -> let base_var = HiFirrtl.base_id r in
              (match VM.find base_var tmap with
              | Some (ft, _) -> pp_ref_mlir out eflag ft r
              | _ -> ("wrong ref", eflag))

(*let rec pp_ftype_cnct v0 v1 f0 f1 =
  match f0, f1 with
  | HiEnv.Gtyp gt0, HiEnv.Gtyp gt1 -> fprintf out "firrtl.connect %s, %s : !firrtl." v0 v1; pp_ftype_mlir out f0; fprintf out ", !firrtl."; pp_ftype_mlir out f1; fprintf out "\n"
  | HiEnv.Atyp _ -> fprintf out "array type\n"
  | HiEnv.Btyp btyp0, HiEnv.Btyp btyp1 -> pp_fbtyp_cnct v0 v1 btyp0 btyp1

and pp_fbtyp_cnct v0 v1 f0 f1 =
  match f0, f1 with
  | HiEnv.Fnil -> fprintf out ""
  | HiEnv.Fflips (fv0, HiEnv.Nflip, ft0, Fnil), HiEnv.Fflips (fv1, HiEnv.Nflip, ft1, Fnil) -> pp_ftype_cnct v0^fv0 v1^fv1 ft0 ft1
  | HiEnv.Fflips (fv0, HiEnv.Flipped, ft0, Fnil), HiEnv.Fflips (fv1, HiEnv.Flipped, ft1, Fnil) -> pp_ftype_cnct v0^fv0 v1^fv1 ft0 ft1
  | HiEnv.Fflips (fv0, HiEnv.Nflip, ft0, ff0), HiEnv.Fflips (fv1, HiEnv.Nflip, ft1, ff1) -> pp_ftype_cnct v0^fv0 v1^fv1 ft0 ft1; pp_fbtyp_cnct v0 v1 ff0 ff1
  | HiEnv.Fflips (fv0, HiEnv.Flipped, ft0, ff0), HiEnv.Fflips (fv1, HiEnv.Flipped, ft1, ff1) -> pp_ftype_cnct v0^fv0 v1^fv1 ft0 ft1; pp_fbtyp_cnct v0 v1 ff0 ff1*)

let rec pp_stmt_mlir out eflag tmap s =
  match s with
  | HiFirrtl.Sskip -> fprintf out ""; eflag
  | HiFirrtl.Swire (v, ty) -> fprintf out "%%%d = firrtl.wire : !firrtl." (Obj.magic v); pp_ftype_mlir out ty; eflag
  | HiFirrtl.Smem _ -> fprintf out "memory"; eflag
  (*match VM.find v tmap with
             | Some (Gtyp gt, _) -> match e with
                                | Eref (Eid rhs) -> (match VM.find rhs tmap with
                                      | Some (te, _) -> fprintf out "firrtl.connect %%%d, %%%d : !firrtl." (Obj.magic v) (Obj.magic rhs); pp_ftype_mlir out (Gtyp gt); fprintf out ", !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; eflag                                      
                                      | _ -> fprintf out "wrong variable name\n"; eflag)
                                | _ -> let (eflag0, eflag1) = pp_expr_mlir out eflag tmap e in 
                                      (match HiFirrtl.type_of_hfexpr e tmap with
                                      | Some (te, _) -> fprintf out "firrtl.connect %%%d, %s : !firrtl." (Obj.magic v) eflag0; pp_ftype_mlir out (Gtyp gt); fprintf out ", !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; eflag1
                                      | _ -> fprintf out "wrong variable name\n"; eflag1)
             | Some (Atyp tv n, _) -> fprintf out "array type\n"
             | Some (Btyp ff, _) -> match e with
                                | Eref (Eid rhs) -> (match VM.find rhs tmap with
                                      | Some (Btyp ff', _) -> pp_btyp_cnct v rhs ff ff'; eflag
                                      | _ -> fprintf out "wrong variable name\n"; eflag)
                                | _ -> let (eflag0, eflag1) = pp_expr_mlir out eflag tmap e in 
                                      (match HiFirrtl.type_of_hfexpr e tmap with
                                      | Some (Btyp ff', _) -> pp_btyp_cnct v rhs ff ff'; eflag1
                                      | _ -> fprintf out "wrong variable name\n"; eflag1*)

  | HiFirrtl.Sfcnct (v, Eref r) -> (match HiFirrtl.type_of_ref v tmap, HiFirrtl.type_of_ref r tmap, 
                                          VM.find (HiFirrtl.base_id v) tmap, VM.find (HiFirrtl.base_id r) tmap with
                                  | Some tv, Some te, Some (base_tv, _), Some (base_te, _) -> 
                                                    let (eflag_v, eflag1) = pp_ref_mlir out eflag base_tv v in
                                                    let (eflag_r, eflag2) = pp_ref_mlir out eflag1 base_te r in
                                         fprintf out "firrtl.connect %s, %s : !firrtl." eflag_v eflag_r; pp_ftype_mlir out tv; fprintf out ", !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; eflag2
                                  | _, _, _, _ -> fprintf out "wrong variable name\n"; eflag)
  | HiFirrtl.Sfcnct (v, e) -> let (eflag_e, eflag1) = pp_expr_mlir out eflag tmap e in 
                                  (match HiFirrtl.type_of_ref v tmap, HiFirrtl.type_of_hfexpr e tmap, VM.find (HiFirrtl.base_id v) tmap with
                                  | Some tv, Some te, Some (base_tv, _) -> 
                                    let (eflag_v, eflag2) = pp_ref_mlir out eflag1 base_tv v in
                                    fprintf out "firrtl.connect %s, %s : !firrtl." eflag_v eflag_e; pp_ftype_mlir out tv; fprintf out ", !firrtl."; pp_ftype_mlir out te; fprintf out "\n"; eflag2
                                  | _, _, _ -> fprintf out "wrong variable name\n"; eflag1)
  | HiFirrtl.Sinvalid v -> fprintf out "%%e%d = firrtl.invalidvalue : !firrtl." eflag; 
                                  (match HiFirrtl.type_of_ref v tmap, VM.find (HiFirrtl.base_id v) tmap with
                                  | Some tv, Some (base_tv, _) -> pp_ftype_mlir out tv; fprintf out "\n"; 
                                               let (eflag_v, eflag1) = pp_ref_mlir out eflag base_tv v in
                                               fprintf out "firrtl.connect %s, %%e%d : !firrtl." eflag_v eflag; pp_ftype_mlir out tv; fprintf out "\n"; eflag1
                                  | _, _ -> fprintf out "wrong variable name\n"; eflag + 1)
  | HiFirrtl.Snode (v, e) -> let (eflag0, eflag1) = pp_expr_mlir out eflag tmap e in 
                                  (match VM.find v tmap with
                                  | Some (tv, _) -> fprintf out "\n%%%d = firrtl.node %s : !firrtl." (Obj.magic v) eflag0; pp_ftype_mlir out tv; eflag1
                                  | _ -> fprintf out "wrong variable name\n"; eflag1)
  | HiFirrtl.Sreg (v, r) ->
     (match r.reset with
     | HiFirrtl.NRst -> let (eflag0, eflag1) = pp_expr_mlir out eflag tmap r.clock in
       fprintf out "%%%d = firrtl.reg %s : !firrtl.clock, !firrtl." (Obj.magic v) eflag0; pp_ftype_mlir out r.coq_type; eflag1
     | HiFirrtl.Rst (e1, e2) -> (let (eflag0, eflag1) = pp_expr_mlir out eflag tmap r.clock in
       let (eflag2, eflag3) = pp_expr_mlir out eflag1 tmap e1 in
       let (eflag4, eflag5) = pp_expr_mlir out eflag3 tmap e2 in
       match HiFirrtl.type_of_hfexpr e1 tmap, HiFirrtl.type_of_hfexpr e2 tmap with
       | Some te1, Some te2 -> fprintf out "%%%d = firrtl.regreset %s, %s, %s : !firrtl.clock, !firrtl." (Obj.magic v) eflag0 eflag2 eflag4; 
         pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ", !firrtl."; pp_ftype_mlir out r.coq_type; eflag5
       | _, _ -> fprintf out "wrong expression type"; eflag5))
  | HiFirrtl.Sinst _ -> fprintf out "inst"; eflag
  | HiFirrtl.Swhen (cond, ss_true, ss_false) -> let (eflag0, eflag1) = pp_expr_mlir out eflag tmap cond in
                    (match HiFirrtl.type_of_hfexpr cond tmap with
                    | Some te -> fprintf out "firrtl.when %s : !firrtl." eflag0; pp_ftype_mlir out te; fprintf out "{\n";
                                 let eflag2 = pp_stmts_mlir out ss_true eflag1 tmap in fprintf out "} else {";
                                 let eflag3 = pp_stmts_mlir out ss_false eflag2 tmap in fprintf out "}"; eflag3
                    | _ -> fprintf out "wrong when condition"; eflag1)
  | _ -> fprintf out "wrong id"; eflag

and pp_stmts_mlir out sl eflag tmap =
  match sl with
  | HiFirrtl.Qnil -> fprintf out ""; eflag
  | HiFirrtl.Qcons (s, ss) -> let eflag0 = pp_stmt_mlir out eflag tmap s in 
                           fprintf out "\n"; pp_stmts_mlir out ss eflag0 tmap

let pp_module_mlir out cn tmap fmod = 
  match fmod with
  | HiFirrtl.FInmod (_, pl, sl) ->
                                   fprintf out "firrtl.module @"; fprintf out "%s(" cn; 
    pp_ports_mlir out pl; fprintf out (") {\n"); let _ = pp_stmts_mlir out sl 0 tmap in fprintf out "}\n"
  | HiFirrtl.FExmod _ -> fprintf out "extmod .. \n"
          
let pp_modules_mlir out cn tmap fmod = Stdlib.List.iter (fun c -> pp_module_mlir out cn tmap c) fmod 

let pp_fcircuit_mlir out cn tmap fc = 
  match fc with
  | HiFirrtl.Fcircuit (_, fmod) -> fprintf out "firrtl.circuit \""; fprintf out "%s\"{\n" cn; pp_modules_mlir out cn tmap fmod; fprintf out "}\n"
