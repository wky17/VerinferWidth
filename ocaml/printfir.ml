open Hifirrtl_lang
open Big_int_Z
open Printf
open Extraction

let repeat_string n =
  if n <= 0 then ""
  else
    let buf = Buffer.create (2 * n) in
    for _ = 1 to n do
      Buffer.add_string buf "  "
    done;
    Buffer.contents buf

let pp_indent_fir out n =
  output_string out (repeat_string n)

let pp_fgtyp_fir out gt =
  match gt with
  | Env.Fuint s -> output_string out ("UInt<"^(Stdlib.Int.to_string s)^">")
  | Fsint s -> output_string out ("SInt<"^(Stdlib.Int.to_string s)^">")
  | Fuint_implicit s -> output_string out "error : uninferred widths\n"
  | Fsint_implicit s -> output_string out "error : uninferred widths\n"
  | Freset -> output_string out "Reset"
  | Fasyncreset -> output_string out "Asyncreset"
  | Fclock -> output_string out "Clock"
 
let rec pp_ftype_fir out ft = 
  match ft with
  | HiEnv.Gtyp gt -> pp_fgtyp_fir out gt
  | Atyp (atyp, n) -> pp_ftype_fir out atyp; output_string out ("["^(Stdlib.Int.to_string n)^"]")
  | Btyp btyp -> output_string out "{"; pp_fbtyp_fir out btyp; output_string out "}"
 
and pp_fbtyp_fir out ty = 
  match ty with
  | HiEnv.Fnil -> fprintf out ""
  | HiEnv.Fflips (fv, HiEnv.Nflip, ft, Fnil) -> fprintf out "%d : " fv; pp_ftype_fir out ft
  | HiEnv.Fflips (fv, HiEnv.Flipped, ft, Fnil) -> fprintf out " flip %d : " fv; pp_ftype_fir out ft
  | HiEnv.Fflips (fv, HiEnv.Nflip, ft, ff) -> fprintf out "%d : " fv; pp_ftype_fir out ft; fprintf out ", "; pp_fbtyp_fir out ff
  | HiEnv.Fflips (fv, HiEnv.Flipped, ft, ff) -> fprintf out " flip %d : " fv; pp_ftype_fir out ft; fprintf out ", "; pp_fbtyp_fir out ff
       
let nat_of_bits_rev bv = 
  let rec helper i max lst res =
    if i >= max then res
    else match Stdlib.List.nth bv i with
    | false -> helper (succ i) max lst res
    | true -> helper (succ i) max lst (add_big_int (power_int_positive_int (2) i) res) in
  helper 0 (Stdlib.List.length bv) bv zero_big_int

let z_of_bits bv = 
  let (v,sign) = (Stdlib.List.tl bv, Stdlib.List.hd bv) in
  if sign then (sub_big_int (nat_of_bits_rev v) (power_int_positive_int (2) ((Stdlib.List.length bv)-1))) (*最高位true，负数*)
  else
    nat_of_bits_rev v

let nat_of_bits bv = nat_of_bits_rev (Stdlib.List.rev bv)

let rec pp_ref_fir out ref = 
  match ref with
  | HiFirrtl.Eid v -> fprintf out "_%d" (Obj.magic v)
  | Esubfield (ref1, v) -> pp_ref_fir out ref1; fprintf out ".%d" (Obj.magic v)
  | Esubindex (ref1, n) -> pp_ref_fir out ref1; fprintf out "[%d]" n
  | Esubaccess (ref1, e) -> fprintf out "subaccess"(*pp_ref_fir out ref1; output_string out "["; pp_expr_fir out e; output_string out "]"*)

let rec pp_expr_fir out e =
  match e with
  | HiFirrtl.Econst (gt, bs) -> (match gt with
                          | Env.Fuint n -> pp_fgtyp_fir out gt; fprintf out "(%s)" (string_of_big_int  (nat_of_bits bs))
                          | Env.Fsint n -> pp_fgtyp_fir out gt; fprintf out "(%s)" (string_of_big_int  (z_of_bits bs))
                          | _ -> printf "error const expression\n")
  | HiFirrtl.Ecast (c, e0) -> (match c with
                          | LoFirrtl.AsUInt -> fprintf out "asUInt("; pp_expr_fir out e0; fprintf out ")"
                          | LoFirrtl.AsSInt -> fprintf out "asSInt("; pp_expr_fir out e0; fprintf out ")"
                          | LoFirrtl.AsClock -> fprintf out "asClock("; pp_expr_fir out e0; fprintf out ")"
                          | LoFirrtl.AsAsync -> fprintf out "asAsyncReset("; pp_expr_fir out e0; fprintf out ")")
  | HiFirrtl.Eprim_unop (op, e0) -> (match op with
                          | LoFirrtl.Upad s -> fprintf out "pad("; pp_expr_fir out e0; fprintf out ", %d)" s
                          | LoFirrtl.Ushl s -> fprintf out "shl("; pp_expr_fir out e0; fprintf out ", %d)" s
                          | LoFirrtl.Ushr s -> fprintf out "shr("; pp_expr_fir out e0; fprintf out ", %d)" s
                          | LoFirrtl.Uhead s -> fprintf out "head("; pp_expr_fir out e0; fprintf out ", %d)" s
                          | LoFirrtl.Utail s -> fprintf out "tail("; pp_expr_fir out e0; fprintf out ", %d)" s
                          | LoFirrtl.Uextr (s1, s2) -> fprintf out "bits("; pp_expr_fir out e0; fprintf out ", %d, %d)" s1 s2
                          | LoFirrtl.Ucvt -> fprintf out "cvt("; pp_expr_fir out e0; fprintf out ")"
                          | LoFirrtl.Uneg -> fprintf out "neg("; pp_expr_fir out e0; fprintf out ")"
                          | LoFirrtl.Unot -> fprintf out "not("; pp_expr_fir out e0; fprintf out ")"
                          | LoFirrtl.Uandr -> fprintf out "andr("; pp_expr_fir out e0; fprintf out ")"
                          | LoFirrtl.Uorr -> fprintf out "orr("; pp_expr_fir out e0; fprintf out ")"
                          | LoFirrtl.Uxorr -> fprintf out "xorr("; pp_expr_fir out e0; fprintf out ")")
  | HiFirrtl.Eprim_binop (op, e1, e2) -> (match op with
                          | LoFirrtl.Badd -> fprintf out "add("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                          | LoFirrtl.Bsub -> fprintf out "sub("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                          | LoFirrtl.Bmul -> fprintf out "mul("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                          | LoFirrtl.Bdiv -> fprintf out "div("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                          | LoFirrtl.Brem -> fprintf out "rem("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                          | LoFirrtl.Bdshl -> fprintf out "dshl("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                          | LoFirrtl.Bdshr -> fprintf out "dshr("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                          | LoFirrtl.Band -> fprintf out "and("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                          | LoFirrtl.Bor -> fprintf out "or("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                          | LoFirrtl.Bxor -> fprintf out "xor("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                          | LoFirrtl.Bcat -> fprintf out "cat("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                          | LoFirrtl.Bcomp s -> (match s with
                                              | LoFirrtl.Blt -> fprintf out "lt("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                                              | LoFirrtl.Bleq -> fprintf out "leq("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                                              | LoFirrtl.Bgt -> fprintf out "gt("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                                              | LoFirrtl.Bgeq -> fprintf out "geq("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                                              | LoFirrtl.Beq -> fprintf out "eq("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
                                              | LoFirrtl.Bneq -> fprintf out "neq("; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"))
  | HiFirrtl.Emux (c, e1, e2) -> fprintf out "mux("; pp_expr_fir out c; fprintf out ", "; pp_expr_fir out e1; fprintf out ", "; pp_expr_fir out e2; fprintf out ")"
  | HiFirrtl.Eref r -> pp_ref_fir out r

let pp_port_fir out p =
  match p with
  | HiFirrtl.Finput (v, ty) -> fprintf out "    input _%d : " (Obj.magic v); pp_ftype_fir out ty; output_string out "\n"
  | Foutput (v, ty) -> fprintf out "    output _%d : " (Obj.magic v); pp_ftype_fir out ty; output_string out "\n"

let rec pp_ports_fir out pl = Stdlib.List.iter (pp_port_fir out) pl
                      
let rec pp_statements_fir out indent sl = 
  match sl with
  | HiFirrtl.Qnil -> output_string out ""
  | Qcons (s, ss) -> pp_indent_fir out indent; pp_statement_fir out indent s; pp_statements_fir out indent ss
                              
and pp_statement_fir out indent s =
  match s with
  | HiFirrtl.Sskip -> output_string out "skip\n"
  | Swire (v, ty) -> fprintf out "wire _%d : " (Obj.magic v); pp_ftype_fir out ty; output_string out "\n"
  | Smem (v, m) -> fprintf out "wire _%d : " (Obj.magic v); pp_ftype_fir out m.data_type; fprintf out "[%d]\n" m.depth 
  | Sfcnct (v, e) -> pp_ref_fir out v; output_string out " <= "; pp_expr_fir out e; output_string out "\n"
  | Sinvalid v -> (*output_string out "invalidate "; *)pp_ref_fir out v; output_string out " is invalid\n"
  | Sreg (v, r) ->
    (match r.reset with
    | NRst -> fprintf out "reg _%d : " (Obj.magic v); pp_ftype_fir out (r.coq_type); output_string out ", "; pp_expr_fir out r.clock; output_string out "\n"
    | Rst (e1, e2) ->
      fprintf out "regreset _%d : " (Obj.magic v); pp_ftype_fir out (r.coq_type); output_string out ", "; pp_expr_fir out r.clock; output_string out ", "; pp_expr_fir out e1; output_string out ", "; pp_expr_fir out e2; output_string out "\n")
  | Snode (v, e) -> fprintf out "node _%d = " (Obj.magic v); pp_expr_fir out e; output_string out "\n"
  | Sinst (v, e) -> output_string out "inst of \n"
  | Swhen (c, s1, s2) -> 
    (match s2 with
    | Qnil -> output_string out "when "; pp_expr_fir out c; output_string out " : \n"; pp_statements_fir out (indent +1) s1
    | _ -> output_string out "when "; pp_expr_fir out c; output_string out " : \n"; pp_statements_fir out (indent +1) s1; pp_indent_fir out indent; output_string out "else : \n"; pp_statements_fir out (indent +1) s2)
           
let pp_module_fir out v fmod =
  match fmod with
  | HiFirrtl.FInmod (_, pl, sl) -> fprintf out "  module %s : \n" v; pp_ports_fir out pl; pp_statements_fir out 2 sl
  | FExmod _ -> output_string out "extmodule\n"
           
let pp_modules_fir out v fmod = Stdlib.List.iter (pp_module_fir out v) fmod
 
let pp_fcircuit_fir out v fc =
  match fc with
  | HiFirrtl.Fcircuit (_, fmod) -> fprintf out "circuit %s : \n" v; pp_modules_fir out v fmod
