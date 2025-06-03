open Hifirrtl_lang
open Printf
open Extraction
open Big_int_Z

module StringMap = Map.Make(String)
let initmap_s = StringMap.empty
module IntMap = Map.Make(Stdlib.Int)
let initmap_i = IntMap.empty

(*lec collect_insts sts = 
  match sts with
  | Ast.Qnil -> []
  | Qcons (s, st) -> Stdlib.List.append (collect_inst s) (collect_insts st)

and collect_inst s =
  match s with
  | Ast.Sinst (v, _) -> [v]
  | Ast.Swhen (_, s1, s2) -> Stdlib.List.append (collect_insts s1) (collect_insts s2)
  | _ -> []*)

let collect_insts sts =
  let rec loop sts acc =
    match sts with
    | Ast.Qnil -> acc
    | Ast.Qcons (s, st) -> loop st (collect_inst_acc s acc)
  and collect_inst_acc s acc =
    match s with
    | Ast.Sinst (v, _) -> v :: acc
    | Ast.Swhen (_, s1, s2) ->
        let acc = loop s1 acc in
        let acc = loop s2 acc in
        acc
    | _ -> acc
  in
  Stdlib.List.rev (loop sts [])

let rec catrev s1 s2 =
  match s1 with
  | Ast.Qnil -> s2
  | Qcons (h1, tl1) -> catrev tl1 (Ast.Qcons (h1, s2))
let rev s =
  catrev s Qnil

let generate_fmodmap a_cir = 
  match a_cir with
  | Ast.Fcircuit (cv, fml) -> let modmap = List.fold_left (fun map fm -> match fm with 
                                | Ast.FInmod (mv, _, _) -> StringMap.add mv fm map
                                | _ -> map) fml initmap_s in
                              let instmap = List.fold_left (fun map fm -> match fm with 
                                | Ast.FInmod (mv, _, sl) -> let insts = collect_insts sl in StringMap.add mv insts map
                                | _ -> map) fml initmap_s in
    (modmap, cv, instmap)

let rec addpre_e e insts current_pre = 
  match e with
  | Ast.Econst _ -> e
  | Ast.Eref r -> Ast.Eref (addpre_ref r insts current_pre)
  | Ast.Eprim_unop (op, e1) -> Ast.Eprim_unop (op, addpre_e e1 insts current_pre)
  | Ast.Eprim_binop (bop, e1, e2) -> Ast.Eprim_binop (bop, addpre_e e1 insts current_pre, addpre_e e2 insts current_pre)
  | Ast.Emux (e1,e2,e3)  -> Ast.Emux (addpre_e e1 insts current_pre, addpre_e e2 insts current_pre, addpre_e e3 insts current_pre)
  (*| Ast.Evalidif (r,e)  -> Ast.Evalidif (addpre_ref r current_pre, addpre_e e curret_pre)*)
  | Ast.Ecast (s, e) -> Ast.Ecast (s, addpre_e e insts current_pre)

and addpre_ref r insts current_pre =
match r with
| Ast.Eid v -> Ast.Eid (current_pre^v)
| Ast.Esubfield (Ast.Eid ref1, v) -> if (Stdlib.List.mem ref1 insts) then Eid (current_pre^ref1^"."^v) else Ast.Esubfield (Ast.Eid (current_pre^ref1), v)
| Ast.Esubfield (ref1, v) -> Ast.Esubfield (addpre_ref ref1 insts current_pre, v)
| Ast.Esubindex (ref1, n) -> Ast.Esubindex (addpre_ref ref1 insts current_pre, n)
| Ast.Esubaccess (ref1, e) -> Ast.Esubaccess (addpre_ref ref1 insts current_pre, addpre_e e insts current_pre)

let rec flatstmts fmodmap sts insts instmap current_pre res = 
  match sts with 
  | Ast.Qnil -> res
  | Ast.Qcons (h, tl) -> let sts0 = flatstmt fmodmap h insts instmap current_pre res in
                         flatstmts fmodmap tl insts instmap current_pre sts0
    
and flatstmt fmodmap st insts instmap current_pre res =
  match st with
  | Ast.Sskip -> Ast.Qcons (Ast.Sskip, res)
  | Ast.Swire (v, ty) -> Qcons (Ast.Swire ((current_pre^v), ty), res)
  | Ast.Sreg (v, r) -> (match r.reset with
                | NRst -> Qcons (Ast.Sreg (current_pre^v, (Ast.mk_freg_non r.coq_type (addpre_e r.clock insts current_pre))), res)
                | Rst (e1, e2) -> Qcons (Ast.Sreg (current_pre^v, (Ast.mk_freg r.coq_type 
                  (addpre_e r.clock insts current_pre) (addpre_e e1 insts current_pre) (addpre_e e2 insts current_pre))), res))
  | Ast.Smem _ -> Qcons (Ast.Sskip, res) (* ignore *)
  | Ast.Sinst (v1, e) -> let new_pre = if current_pre = "" then v1^"." else current_pre^v1^"." in
                        (match StringMap.find e fmodmap, StringMap.find e instmap with
                        | Ast.FInmod (_, pl, sl), ninsts -> (* expand inst 内部语句 *)
                          let instpl = List.fold_left (fun templ p -> match p with
                                                        | Ast.Finput (v, ty) -> Ast.Qcons (Ast.Swire ((new_pre^v), ty), templ)
                                                        | Ast.Foutput (v, ty) -> Qcons (Ast.Swire ((new_pre^v), ty), templ)) pl res in 
                          flatstmts fmodmap sl ninsts instmap new_pre instpl
                        | _, _ -> res)
  | Ast.Snode (v, e) -> Qcons (Ast.Snode ((current_pre^v), addpre_e e insts current_pre), res)
  | Ast.Sinferport (v, r, e) -> Qcons (Ast.Sinferport ((current_pre^v), addpre_ref r insts current_pre, addpre_e e insts current_pre), res)
  | Ast.Sfcnct (r, e) -> Qcons (Ast.Sfcnct (addpre_ref r insts current_pre, addpre_e e insts current_pre), res)
  | Ast.Sinvalid r -> Qcons (Ast.Sinvalid (addpre_ref r insts current_pre), res)
  | Ast.Swhen (c, s1, s2) -> Qcons (Ast.Swhen ((addpre_e c insts current_pre), (flatstmts fmodmap s1 insts instmap current_pre Qnil), (flatstmts fmodmap s2 insts instmap current_pre Qnil)), res)

let rec revstmts sts res = 
  match sts with 
  | Ast.Qnil -> res
  | Ast.Qcons (h, tl) -> revstmts tl (revstmt h res)
    
and revstmt st res =
  match st with
  | Ast.Swhen (c, s1, s2) -> Ast.Qcons ((Ast.Swhen (c, revstmts s1 Ast.Qnil, revstmts s2 Ast.Qnil)), res)
  | _ -> Ast.Qcons (st, res)

let inline_cir out hif_ast =
  let (fmodmap ,cv, instmap) = generate_fmodmap hif_ast in (* string -> fmod, circuit string name, module string name -> inst string names *)
  match StringMap.find cv fmodmap, StringMap.find cv instmap with (* find main module *)
  | Ast.FInmod (_, pl, sl), insts -> let flattensl = flatstmts fmodmap sl insts instmap "" Qnil in
                              let flattenmain = Ast.FInmod (cv, pl, revstmts flattensl Ast.Qnil) in
                              (*Ast.pp_module out flattenmain; *)
                              Ast.Fcircuit (cv, [flattenmain])

                            