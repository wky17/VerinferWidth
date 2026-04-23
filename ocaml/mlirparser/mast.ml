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

type hfport =
| Finput of var * ftype
| Foutput of var * ftype

type hfstmt =
| Swire of var * ftype
| Sreg of var * ftype
| Snode of var * ftype
| Sinst of var * var
and hfstmt_seq =
| Qnil
| Qcons of hfstmt * hfstmt_seq

type hfmodule =
| FInmod of var * hfport list * hfstmt_seq
| FExmod of var * hfport list * hfstmt_seq

type hfcircuit =
| Fcircuit of var * hfmodule list

type file = hfcircuit


let pp_gtyp out ty =
  match ty with
  | Fuint s -> output_string out "(Fuint "; output_string out (Int.to_string s); output_string out ")"
  | Fsint s -> output_string out "(Fsint "; output_string out (Int.to_string s); output_string out ")"
  | Fuint_implicit s -> output_string out "Fuint_implicit"
  | Fsint_implicit s -> output_string out "Fsint_implicit"
  | Freset -> output_string out "Freset"
  | Fasyncreset -> output_string out "Fasyncreset"
  | Fclock -> output_string out "Fclock"
 
 let pp_flip out fl = 
   match fl with
   | Flipped -> output_string out "flip "
   | Nflip -> output_string out ""
 
 let rec pp_type out ty = 
   match ty with
   | Gtyp gt -> output_string out "(Gtyp "; pp_gtyp out gt; output_string out ")"
   | Atyp (atyp, n) -> output_string out "(Atyp "; pp_type out atyp; output_string out ("["^(Int.to_string n)^"]")
   | Btyp btyp -> output_string out "({"; pp_btyp out btyp; output_string out "})";
 
 and pp_btyp out ty = 
   match ty with
   | Fnil -> output_string out "Fnil"
   | Fflips (v, fl, ft, ff) -> pp_flip out fl; output_string out (v^" : "); pp_type out ft; output_string out "; "; pp_btyp out ff; output_string out ")"
 
let rec pp_ports out pl = output_string out "["; List.iter (fun c -> pp_port out c; output_string out ",\n") pl;  output_string out "]\n";
                     
and pp_port out p =
  match p with
  | Finput (v, ty) -> output_string out "Finput "; output_string out (v^" : "); pp_type out ty
  | Foutput (v, ty) -> output_string out "Foutput "; output_string out (v^" : "); pp_type out ty               
                       
let rec pp_statements out sl = 
  match sl with
  | Qnil -> output_string out ""
  | Qcons (s, ss) -> pp_statement out s; pp_statements out ss
                             
and pp_statement out s =
  match s with
  | Swire (v, ty) -> output_string out "wire "; output_string out (v^" : "); pp_type out ty; output_string out "\n"
  | Sreg (v, r) -> output_string out "wire "; output_string out (v^" : "); pp_type out r; output_string out "\n"
  | Snode (v, e) -> output_string out "node "; output_string out (v^" : "); pp_type out e; output_string out "\n"
  | Sinst (v, var) -> output_string out "inst "; output_string out (v^" : "^var); output_string out "\n"
          
let pp_module out fmod =
  match fmod with
  | FInmod (v, pl, sl) -> output_string out "FInmod "; output_string out (v^" : \n"); pp_ports out pl; pp_statements out sl; output_string out "\n"
  | FExmod (v, pl, sl) -> output_string out "FExmod "; output_string out (v^" : \n"); pp_ports out pl; pp_statements out sl; output_string out "\n"
          
let pp_modules out fmod = List.iter (fun c -> pp_module out c; output_string out "") fmod

let pp_fcircuit out fc =
  match fc with
  | Fcircuit (v, fmod) -> output_string out "FCircuit "; output_string out (v^" : \n"); pp_modules out fmod; output_string out "\n"


module StringMap = Map.Make(String)
let initmap_s = StringMap.empty

let mapport tmap p = 
  match p with
  | Finput (v, ty) -> StringMap.add v ty tmap
  | Foutput (v, ty) -> StringMap.add v ty tmap

let rec mapstmt tmap stmt = 
  match stmt with
  | Swire (v, ty) -> StringMap.add v ty tmap
  | Sreg (v, r) -> StringMap.add v r tmap
  | Snode (v, e) -> StringMap.add v e tmap
  | Sinst _ -> tmap

 and mapstmts tmap stmts = 
  match stmts with
  | Qnil -> tmap
  | Qcons (s, ss) -> mapstmts (mapstmt tmap s) ss

let mapmod m =  
  match m with 
  | FInmod (_, pl, sl) -> let map0 = List.fold_left mapport initmap_s pl in
                              mapstmts map0 sl 
  | _ -> initmap_s

let rec mapmodl ml tmap = 
  match ml with
  | [] -> tmap
  | (FInmod (mv, pl, sl)) :: tl -> mapmodl tl (StringMap.add mv (mapmod (FInmod (mv, pl, sl))) tmap)
  | _ -> output_string stdout "There is a extmodule\n"; tmap


let mapcir cir = 
  match cir with
  | Fcircuit (_, ml) -> mapmodl ml initmap_s
