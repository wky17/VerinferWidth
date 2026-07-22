type var = string

type fgtyp =
| Fuint of int
| Fsint of int
| Fuint_implicit of int
| Fsint_implicit of int
| Fclock
| Freset
| Fasyncreset

type fflip =
| Flipped
| Nflip

type ftype =
| Gtyp of fgtyp
| Atyp of ftype * int
| Btyp of ffield
and ffield =
| Fnil
| Fflips of var * fflip * ftype * ffield

type ucast =
| AsUInt
| AsSInt
| AsClock
| AsAsync

type eunop =
| Upad of int
| Ushl of int
| Ushr of int
| Ucvt
| Uneg
| Unot
| Uandr
| Uorr
| Uxorr
| Uextr of int * int
| Uhead of int
| Utail of int

type bcmp =
| Blt
| Bleq
| Bgt
| Bgeq
| Beq
| Bneq

type ebinop =
| Badd
| Bsub
| Bmul
| Bdiv
| Brem
| Bcomp of bcmp
| Bdshl
| Bdshr
| Band
| Bor
| Bxor
| Bcat

type hfexpr =
| Econst of fgtyp * Z.t
| Ecast of ucast * hfexpr
| Eprim_unop of eunop * hfexpr
| Eprim_binop of ebinop * hfexpr * hfexpr
| Emux of hfexpr * hfexpr * hfexpr
(*| Evalidif of hfexpr * hfexpr*)
| Eref of href
and href =
| Eid of var
| Esubfield of href * var
| Esubindex of href * int
| Esubaccess of href * hfexpr

type mem_port = { id : var; addr : var;
                  en : var; clk : var;
                  mask : var }

type ruw =
| Coq_old
| Coq_new
| Coq_undefined

type hfmem = { data_type : ftype; depth : int; reader : mem_port list;
               writer : mem_port list; read_latency : int;
               write_latency : int; read_write : ruw }

type rst =
| NRst
| Rst of hfexpr * hfexpr

type hfreg = { coq_type : ftype; clock : hfexpr; reset : rst }

let mk_freg t c e1 e2 = { coq_type = t; clock = c; reset = Rst(e1,e2) }
let mk_freg_non t c = { coq_type = t; clock = c; reset = NRst}
let mk_freg_r t c r = { coq_type = t; clock = c; reset = r}
let mk_fmem e z1 z2 z3 vl1 vl2 r = { data_type = e; depth = z1;  read_latency = z2; write_latency = z3; reader = vl1; writer = vl2; read_write = r }
let mk_fmem_non e z1 z2 z3 r = { data_type = e; depth = z1;  read_latency = z2; write_latency = z3; reader = []; writer = []; read_write = r }
let mk_fmem_r e z1 z2 z3 vl r = { data_type = e; depth = z1;  read_latency = z2; write_latency = z3; reader = vl; writer = []; read_write = r }

type hfstmt =
| Sskip
| Swire of var * ftype
| Sreg of var * hfreg
| Smem of var * ftype * int 
| Sinst of var * var
| Snode of var * hfexpr
| Sfcnct of href * hfexpr
| Spcnct of href * hfexpr
| Sinvalid of href
| Sinferport of var * href * hfexpr
| Sreadport of var * href * hfexpr
| Swriteport of var * href * hfexpr
| Swhen of hfexpr * hfstmt_seq * hfstmt_seq
and hfstmt_seq =
| Qnil
| Qcons of hfstmt * hfstmt_seq

let rec qcat s1 s2 =
  match s1 with
  | Qnil -> s2
  | Qcons (h1, tl1) -> Qcons (h1, (qcat tl1 s2))

type hfport =
| Finput of var * ftype
| Foutput of var * ftype

type hfmodule =
| FInmod of var * hfport list * hfstmt_seq
| FExmod of var * hfport list * hfstmt_seq

type hfcircuit =
| Fcircuit of var * hfmodule list

type file = hfcircuit

(** pretty printer **)
open Printf

let pp_gtyp out ty =
 match ty with
 | Fuint s -> output_string out "UInt<"; output_string out (Int.to_string s); output_string out ">"
 | Fsint s -> output_string out "SInt<"; output_string out (Int.to_string s); output_string out ">"
 | Fuint_implicit s -> output_string out "UInt"
 | Fsint_implicit s -> output_string out "SInt"
 | Freset -> output_string out "Reset"
 | Fasyncreset -> output_string out "AsyncReset"
 | Fclock -> output_string out "Clock"

let rec pp_type out ty = 
  match ty with
  | Gtyp gt -> pp_gtyp out gt
  | Atyp (atyp, n) -> pp_type out atyp; output_string out ("["^(Int.to_string n)^"]")
  | Btyp btyp -> output_string out "{"; pp_btyp out btyp; output_string out "}";

and pp_btyp out ty = 
  match ty with
  | Fnil -> output_string out ""
  | Fflips (fv, Nflip, ft, Fnil) -> fprintf out "%s : " fv; pp_type out ft
  | Fflips (fv, Flipped, ft, Fnil) -> fprintf out " flip %s : " fv; pp_type out ft
  | Fflips (fv, Nflip, ft, ff) -> fprintf out "%s : " fv; pp_type out ft; fprintf out ", "; pp_btyp out ff
  | Fflips (fv, Flipped, ft, ff) -> fprintf out " flip %s : " fv; pp_type out ft; fprintf out ", "; pp_btyp out ff

let rec pp_expr out e =
 match e with
 | Econst (gt, bs) -> (match gt with
                          | Fuint n -> pp_gtyp out gt; fprintf out "(%s)" (Z.to_string bs)
                          | Fsint n -> pp_gtyp out gt; fprintf out "(%s)" (Z.to_string bs)
                          | _ -> printf "error const expression\n")
 | Eref v -> pp_ref out v
 | Eprim_unop (op, e0) -> (match op with
                          | Upad s -> fprintf out "pad("; pp_expr out e0; fprintf out ", %d)" s
                          | Ushl s -> fprintf out "shl("; pp_expr out e0; fprintf out ", %d)" s
                          | Ushr s -> fprintf out "shr("; pp_expr out e0; fprintf out ", %d)" s
                          | Uhead s -> fprintf out "ahead("; pp_expr out e0; fprintf out ", %d)" s(* ahead *)
                          | Utail s -> fprintf out "tail("; pp_expr out e0; fprintf out ", %d)" s
                          | Uextr (s1, s2) -> fprintf out "bits("; pp_expr out e0; fprintf out ", %d, %d)" s1 s2
                          | Ucvt -> fprintf out "cvt("; pp_expr out e0; fprintf out ")"
                          | Uneg -> fprintf out "neg("; pp_expr out e0; fprintf out ")"
                          | Unot -> fprintf out "not("; pp_expr out e0; fprintf out ")"
                          | Uandr -> fprintf out "andr("; pp_expr out e0; fprintf out ")"
                          | Uorr -> fprintf out "orr("; pp_expr out e0; fprintf out ")"
                          | Uxorr -> fprintf out "xorr("; pp_expr out e0; fprintf out ")")
 | Eprim_binop (op, e1, e2) -> (match op with
                          | Badd -> fprintf out "add("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                          | Bsub -> fprintf out "sub("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                          | Bmul -> fprintf out "mul("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                          | Bdiv -> fprintf out "div("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                          | Brem -> fprintf out "rem("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                          | Bdshl -> fprintf out "dshl("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                          | Bdshr -> fprintf out "dshr("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                          | Band -> fprintf out "and("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                          | Bor -> fprintf out "or("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                          | Bxor -> fprintf out "xor("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                          | Bcat -> fprintf out "cat("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                          | Bcomp s -> (match s with
                                              | Blt -> fprintf out "lt("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                                              | Bleq -> fprintf out "leq("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                                              | Bgt -> fprintf out "gt("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                                              | Bgeq -> fprintf out "geq("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                                              | Beq -> fprintf out "eq("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"
                                              | Bneq -> fprintf out "neq("; pp_expr out e1; fprintf out ", "; pp_expr out e2; fprintf out ")"))
 | Emux (e1,e2,e3)  -> output_string out "mux("; pp_expr out e1; output_string out ", "; pp_expr out e2; output_string out ", "; pp_expr out e3; output_string out ")"
 | Ecast (c, e0) -> (match c with
                          | AsUInt -> fprintf out "asUInt("; pp_expr out e0; fprintf out ")"
                          | AsSInt -> fprintf out "asSInt("; pp_expr out e0; fprintf out ")"
                          | AsClock -> fprintf out "asClock("; pp_expr out e0; fprintf out ")"
                          | AsAsync -> fprintf out "asAsyncReset("; pp_expr out e0; fprintf out ")")

and pp_ref out ref = 
 match ref with
 | Eid v -> output_string out v
 | Esubfield (ref1, v) -> pp_ref out ref1; output_string out "."; output_string out v
 | Esubindex (ref1, n) -> pp_ref out ref1; output_string out "["; output_string out ((Int.to_string n)^"]")
 | Esubaccess (ref1, e) -> pp_ref out ref1; output_string out "["; pp_expr out e; output_string out "]"

 let pp_ruw out e = 
 match e with
 | Coq_old -> output_string out "old"
 | Coq_new -> output_string out "new"
 | Coq_undefined -> output_string out "undefined"

let rec pp_ports out pl = List.iter (fun c -> pp_port out c) pl
                     
and pp_port out p =
  match p with
  | Finput (v, ty) -> output_string out ("    input "^v^" : "); pp_type out ty; output_string out "\n"
  | Foutput (v, ty) -> output_string out ("    output "^v^" : "); pp_type out ty; output_string out "\n"                 

let repeat_string n =
  if n <= 0 then ""
  else
    let buf = Buffer.create (2 * n) in
    for _ = 1 to n do
      Buffer.add_string buf "  "
    done;
    Buffer.contents buf

let pp_indent out n =
  output_string out (repeat_string n)
          
let rec pp_statements out indent sl = 
  match sl with
  | Qnil -> output_string out ""
  | Qcons (s, ss) -> pp_indent out indent; pp_statement out indent s; pp_statements out indent ss

and pp_statement out indent s =
  match s with
  | Sskip -> output_string out "skip\n"
  | Swire (v, ty) -> output_string out ("wire "^v^" : "); pp_type out ty; output_string out "\n"
  | Smem (v, ty, n) -> output_string out ("cmem "^v^" : "); pp_type out ty; fprintf out "[%d]\n" n
  | Sfcnct (e1, e2) -> pp_ref out e1; output_string out " <= "; pp_expr out e2; output_string out "\n"
                       (*output_string out "connect "; pp_ref out e1; output_string out ", "; pp_expr out e2; output_string out "\n"*)
  | Spcnct (e1, e2) -> pp_ref out e1; output_string out " <- "; pp_expr out e2; output_string out "\n"
  | Sinvalid v -> pp_ref out v; output_string out " is invalid\n"
                  (*output_string out "invalidate "; pp_ref out v; output_string out "\n"*)
  | Sreg (v, r) ->
     (match r.reset with
     | NRst -> output_string out ("reg "^v^" : "); pp_type out (r.coq_type); output_string out ", "; pp_expr out r.clock; output_string out " \n"
     | Rst (e1, e2) ->
        (*output_string out ("regreset "^v^" : "); pp_type out (r.coq_type); output_string out ", "; pp_expr out r.clock; output_string out ", "; pp_expr out e1; output_string out ", "; pp_expr out e2; output_string out "\n")*)
        output_string out ("reg "^v^" : "); pp_type out (r.coq_type); output_string out ", "; pp_expr out r.clock; 
        output_string out " with : (reset => ("; pp_expr out e1; output_string out ", "; pp_expr out e2; output_string out "))"; output_string out " \n")
  | Snode (v, e) -> output_string out ("node "^v^" = "); pp_expr out e; output_string out "\n"
  | Sinst (v, e) -> output_string out ("inst "^v^" aof "^e^"\n")(* aof *)
  | Swhen (c, s1, s2) -> 
    (match s1, s2 with
    | Qnil, Qnil -> output_string out "when "; pp_expr out c; output_string out " : \n{\n"(*" : \n"*); pp_indent out (indent+1); pp_statement out (indent +1) Sskip; output_string out "}\n"
    | Qnil, _ ->  output_string out "when "; pp_expr out c; output_string out " : \n{\n"(*" : \n"*); pp_indent out (indent+1); pp_statement out (indent +1) Sskip; output_string out "}\n";
           pp_indent out indent; output_string out "else : \n{\n"(*"else : \n"*); pp_statements out (indent +1) s2; output_string out "}\n"
    | _, Qnil -> output_string out "when "; pp_expr out c; output_string out " : \n{\n"(*" : \n"*); pp_statements out (indent +1) s1; output_string out "}\n"
    | _, _ -> output_string out "when "; pp_expr out c; output_string out " : \n{\n"(*" : \n"*); pp_statements out (indent +1) s1; output_string out "}\n";
           pp_indent out indent; output_string out "else : \n{\n"(*"else : \n"*); pp_statements out (indent +1) s2; output_string out "}\n")
  | Sinferport (v, ref, e) -> output_string out ("infer mport "^v^" = "); pp_ref out ref; output_string out ", "; pp_expr out e; output_string out " \n"
  | Sreadport (v, ref, e) -> output_string out ("read mport "^v^" = "); pp_ref out ref; output_string out ", "; pp_expr out e; output_string out " \n"
  | Swriteport (v, ref, e) -> output_string out ("write mport "^v^" = "); pp_ref out ref; output_string out ", "; pp_expr out e; output_string out " \n"

let pp_module out fmod =
  match fmod with
  | FInmod (v, pl, sl) -> output_string out ("  module "^v^" : \n"); pp_ports out pl; pp_statements out 2 sl
  | FExmod _ -> output_string out "  extmodule\n"

let pp_modules out fmod = List.iter (fun c -> pp_module out c) fmod

let pp_fcircuit out fc =
  match fc with
  | Fcircuit (v, fmod) -> output_string out ("FIRRTL version 2.0.0\ncircuit "^v^" : \n"); pp_modules out fmod
  
let pp_file out fc = pp_fcircuit out fc
