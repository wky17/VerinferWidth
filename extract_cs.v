From HB Require Import structures.
From Coq Require Import ZArith Arith List Ascii String Lia FMaps.
From mathcomp Require Import all_ssreflect.
From Solver Require Import Env LoFirrtl HiEnv HiFirrtl constraints.
Import ListNotations.

Section Extract_Constraints_better.

Fixpoint extract_constraint_expr (e : hfexpr) (tmap : VM.t (ftype * forient)) : option (list ((list (list term * list term * Z.t)) * (list Constraint2))) :=
  match e with
  | Eref r => match type_of_ref r tmap, ref2pv r tmap with
                            | Some (Gtyp (Fuint_implicit _)), Some pv 
                            | Some (Gtyp (Fsint_implicit _)), Some pv => Some [([([(1, pv)], nil, 0%Z)], nil)]
                            | Some (Gtyp gt), _ => Some [([(nil, nil, (Z.of_nat (sizeof_fgtyp gt)))], nil)]
                            | _, _ => None
                            end
  | Econst t bs => match t with
                            | Fuint_implicit _ 
                            | Fsint_implicit _ => Some [([(nil, nil, (Z.of_nat (size bs)))], nil)]
                            | t => Some [([(nil, nil, (Z.of_nat (sizeof_fgtyp t)))], nil)]
                            end
  | Ecast AsUInt e1 
  | Ecast AsSInt e1 => match type_of_hfexpr e1 tmap with
                            | Some (exist (Gtyp _) _) => extract_constraint_expr e1 tmap
                            | _ => None
                            end
  | Eprim_unop Unot e1 => match type_of_hfexpr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _)
                            | Some (exist (Gtyp (Fuint w)) _) => extract_constraint_expr e1 tmap
                            | _ => None
                            end
  | Ecast AsClock e1 
  | Ecast AsAsync e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp _) _), Some ((_, cs)::_) => Some [([(nil, nil, 1%Z)], cs)]
                            | _, _ => None
                            end
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some el_cs 
                            | Some (exist (Gtyp (Fuint w)) _), Some el_cs => Some (map (fun '(el, cs) => ((nil, nil, Z.of_nat n) :: el, cs)) el_cs)
                            | _, _ => None
                            end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some el_cs 
                            | Some (exist (Gtyp (Fuint w)) _), Some el_cs => Some (map (fun '(el, cs) => (map (fun '(terms, terms', cst) => (terms, terms', Z.add cst (Z.of_nat n))) el, cs)) el_cs) 
                            | _, _ => None
                            end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some el_cs  => 
                                Some (map (fun '(el, cs) => 
                                  let nexp := map (fun '(terms, terms', cst) => (terms, terms', Z.sub cst (Z.of_nat n))) el in
                                  ((nil, nil, 1%Z) :: nexp, cs)) el_cs) 
                            | Some (exist (Gtyp (Fuint w)) _), Some el_cs => 
                                Some (map (fun '(el, cs) =>
                                  (map (fun '(terms, terms', cst) => (terms, terms', Z.sub cst (Z.of_nat n))) el, cs)) el_cs)
                            | _, _ => None
                            end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some el_cs => Some el_cs
                            | Some (exist (Gtyp (Fuint _)) _), Some el_cs => 
                                Some (map (fun '(el, cs) => (map (fun '(terms, terms', cst) => (terms, terms', Z.add cst 1%Z)) el, cs)) el_cs) 
                            | _, _ => None
                            end
  | Eprim_unop Uneg e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some el_cs 
                            | Some (exist (Gtyp (Fuint _)) _), Some el_cs => Some (map (fun '(el, cs) => (map (fun '(terms, terms', cst) => (terms, terms', Z.add cst 1%Z)) el, cs)) el_cs) 
                            | _, _ => None
                            end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some el_cs
                            | Some (exist (Gtyp (Fuint w)) _), Some el_cs => (*if (n2 <= n1) && (n1 < w) then *)
                                Some (map (fun '(el, cs) => ([(nil, nil, Z.of_nat (n1 - n2 + 1))], cs)) el_cs) (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some el_cs
                            | Some (exist (Gtyp (Fuint w)) _), Some el_cs => (*if n <= w then *)
                                Some (map (fun '(el, cs) => ([(nil, nil, Z.of_nat n)], cs)) el_cs) (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some el_cs
                            | Some (exist (Gtyp (Fuint w)) _), Some el_cs => (*if n <= w then *)
                                Some (map (fun '(el, cs) => (map (fun '(terms, terms', cst) => (terms, terms', Z.sub cst (Z.of_nat n))) el, cs)) el_cs) 
                              (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop _ e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some el_cs
                            | Some (exist (Gtyp (Fuint _)) _), Some el_cs => 
                              Some (map (fun '(el, cs) => ([(nil, nil, 1%Z)], cs)) el_cs) 
                            | _, _ => None
                            end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _), Some el1_cs1, Some el2_cs2
                            | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _), Some el1_cs1, Some el2_cs2 => 
                                Some (flat_map (fun '(el1, cs1) => map (fun '(el2, cs2) =>
                                ([(nil, nil, 1%Z)], cs1 ++ cs2)) el2_cs2) el1_cs1) 
                            | _, _, _, _ => None
                            end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some el1_cs1, Some el2_cs2 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some el1_cs1, Some el2_cs2 => 
                              Some (flat_map (fun '(el1, cs1) => map (fun '(el2, cs2) => 
                                let nexp1 := map (fun '(terms, terms', cst) => (terms, terms', Z.add cst 1%Z)) el1 in
                                let nexp2 := map (fun '(terms, terms', cst) => (terms, terms', Z.add cst 1%Z)) el2 in
                                (nexp1 ++ nexp2, cs1 ++ cs2)
                              ) el2_cs2) el1_cs1)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some el1_cs1, Some el2_cs2 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some el1_cs1, Some el2_cs2 => 
                              Some (flat_map (fun '(el1, cs1) => map (fun '(el2, cs2) => 
                                (flat_map (fun x => map (combine_terms x) el2) el1, cs1 ++ cs2)) el2_cs2) el1_cs1) 
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some el1_cs1, Some el2_cs2 => 
                              Some (flat_map (fun '(el1, cs1) => map (fun '(el2, cs2) => (el1, cs1 ++ cs2)) el2_cs2) el1_cs1) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some el1_cs1, Some el2_cs2 => 
                              Some (flat_map (fun '(el1, cs1) => map (fun '(el2, cs2) => 
                                (map (fun '(terms, terms', cst) => (terms, terms', Z.sub cst 1%Z)) el1, cs1 ++ cs2)) el2_cs2) el1_cs1) 
                            | _, _, _, _ => None
                            end
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some el1_cs1, Some el2_cs2 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some el1_cs1, Some el2_cs2 => 
                              Some (flat_map (fun '(el1, cs1) => map (fun '(el2, cs2) => (el1, cs1 ++ cs2)) el2_cs2) el1_cs1 ++ 
                                    flat_map (fun '(el2, cs2) => map (fun '(el1, cs1) => (el2, cs1 ++ cs2)) el1_cs1) el2_cs2)
                            | _, _, _, _ => None 
                            end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some el1_cs1 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some el1_cs1 =>
                                match e2 with
                                | Eref r => match type_of_ref r tmap, ref2pv r tmap with
                                          | Some (Gtyp (Fuint_implicit _)), Some pv => Some (map (fun '(el1, cs1) => (map (fun '(terms, _, cst) => (terms, [(1, pv)], Z.sub cst 1)) el1, cs1)) el1_cs1)
                                          | Some (Gtyp (Fuint w)), _ => 
                                            Some (map (fun '(el1, cs1) => (map (fun '(terms, terms', cst) => (terms, terms', Z.sub (Z.add cst (Z.pow 2 (Z.of_nat w))) 1)) el1, cs1)) el1_cs1) 
                                          | _, _ => None
                                          end
                                | Econst t bs => match t with
                                          | Fuint_implicit _ 
                                          | Fsint_implicit _ => Some (map (fun '(el1, cs1) => (map (fun '(terms, terms', cst) => (terms, terms', Z.sub (Z.add cst (Z.pow 2 (Z.of_nat (size bs)))) 1)) el1, cs1)) el1_cs1) 
                                          | t => Some (map (fun '(el1, cs1) => (map (fun '(terms, terms', cst) => (terms, terms', Z.sub (Z.add cst (Z.pow 2 (Z.of_nat (sizeof_fgtyp t)))) 1)) el1, cs1)) el1_cs1) 
                                          end
                                | _ => None
                                end
                            | _, _, _ => None
                            end
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some el1_cs1, Some el2_cs2
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some el1_cs1, Some el2_cs2 => 
                              Some (flat_map (fun '(el1, cs1) => map (fun '(el2, cs2) => (el1, cs1 ++ cs2)) el2_cs2) el1_cs1)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some el1_cs1, Some el2_cs2 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some el1_cs1, Some el2_cs2 => 
                                Some (flat_map (fun '(el1, cs1) => map (fun '(el2, cs2) => (flat_map (fun x => map (combine_terms x) el2) el1, cs1 ++ cs2)) el2_cs2) el1_cs1) 
                            | _, _, _, _ => None
                            end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some el1_cs1, Some el2_cs2 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some el1_cs1, Some el2_cs2 => 
                              Some (flat_map (fun '(el1, cs1) => map (fun '(el2, cs2) => (el1 ++ el2, cs1 ++ cs2)) el2_cs2) el1_cs1) 
                            | _, _, _, _ => None
                            end
  | Emux c e1 e2 => match type_of_hfexpr c tmap, extract_constraint_expr c tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint _)) _), Some ec_cs0, Some el1_cs1, Some el2_cs2 => 
                              Some (flat_map (fun '(ec, cs0) => flat_map (fun '(el1, cs1) => map (fun '(el2, cs2) => 
                              let ncs := map (fun '(terms, _, cst) => {|
                                lhs_const2 := 1 - (Z.to_nat cst);
                                rhs_terms2 := terms
                              |}) ec in (el1 ++ el2, ncs ++ cs0 ++ cs1 ++ cs2)) el2_cs2) el1_cs1) ec_cs0)
                            | _, _, _, _ => None
                            end 
end.

(*Compute (combine_terms ([(1,(1%num,0%num))], 4%Z) ([(1,(1%num,0%num))], 0%Z)).
Compute (flat_map (fun x => map (combine_terms x) [([(1,(1%num,0%num))], 4%Z)]) [([(1,(1%num,0%num))], 0%Z)]).*)

Fixpoint expand_mux (e : hfexpr) (tmap : VM.t (ftype * forient)) : option (list (list href * list Constraint2)) := 
  match e with
  | Eref r => Some [([r], nil)]
  | Emux c e1 e2 => match type_of_hfexpr c tmap, extract_constraint_expr c tmap, 
                          expand_mux e1 tmap, expand_mux e2 tmap with
                  | Some (exist (Gtyp (Fuint _)) _), Some ec_cs0, Some r1_cs1, Some r2_cs2 => 
                    Some (flat_map (fun '(ec, cs0) => flat_map (fun '(r1, cs1) => map (fun '(r2, cs2) =>
                      let ncs := map (fun '(terms, terms', cst) => {|
                      lhs_const2 := 1 - (Z.to_nat cst);
                      rhs_terms2 := terms
                      |}) ec in (r1 ++ r2, ncs ++ cs0 ++ cs1 ++ cs2)) r2_cs2) r1_cs1) ec_cs0)  
                  | _, _, _, _ => None
                  end
  | _ => None
  end.

Fixpoint extract_constraint_passive (ft ft_ref : ftype) (pv pvar : ProdVar.t) (c1map : PVM.t (list Constraint1)) : PVM.t (list Constraint1) :=
  match ft, ft_ref with 
  | Gtyp (Fuint_implicit _), Gtyp (Fuint_implicit _)
  | Gtyp (Fsint_implicit _), Gtyp (Fsint_implicit _) => 
                                let nc := {|
                                 lhs_var1 := pv;
                                 rhs_const1 := 0;
                                 rhs_power := nil;
                                 rhs_terms1 := [(1, pvar)]
                               |} in
                               match PVM.find pv c1map with
                               | Some cs1 => PVM.add pv (nc :: cs1) c1map
                               | _ => PVM.add pv [nc] c1map
                               end
  | Gtyp (Fuint_implicit _), Gtyp (Fuint w)
  | Gtyp (Fsint_implicit _), Gtyp (Fsint w) => 
                                let nc := {|
                                 lhs_var1 := pv;
                                 rhs_const1 := Z.of_nat w;
                                 rhs_power := nil;
                                 rhs_terms1 := []
                               |} in
                               match PVM.find pv c1map with
                               | Some cs1 => PVM.add pv (nc :: cs1) c1map
                               | _ => PVM.add pv [nc] c1map
                               end
  | Atyp atyp _, Atyp atyp_ref _ => extract_constraint_passive atyp atyp_ref pv pvar c1map
  | Btyp ff, Btyp ff_ref => extract_constraint_passive_f ff ff_ref pv pvar c1map
  | _, _ => c1map
  end
with extract_constraint_passive_f (ff ff_ref : ffield) (pv pvar : ProdVar.t) (c1map : PVM.t (list Constraint1)) : PVM.t (list Constraint1) :=
  match ff, ff_ref with
  | Fnil, Fnil => c1map
  | Fflips _ Nflip t fs, Fflips _ Nflip t_ref fs_ref => let nmap := extract_constraint_passive t t_ref pv pvar c1map in 
                           extract_constraint_passive_f fs fs_ref (pv.1, N.add pv.2 (N.of_nat (size_of_ftype t))) (pvar.1, N.add pvar.2 (N.of_nat (size_of_ftype t))) nmap
  | _, _ => c1map
  end.

Fixpoint extract_constraint_non_passive (ft ft_ref : ftype) (pv pvar : ProdVar.t) (c1map : PVM.t (list Constraint1)) : PVM.t (list Constraint1) :=
  match ft, ft_ref with 
  | Gtyp (Fuint_implicit _), Gtyp (Fuint_implicit _)
  | Gtyp (Fsint_implicit _), Gtyp (Fsint_implicit _) => 
                                let nc := {|
                                 lhs_var1 := pv;
                                 rhs_power := nil;
                                 rhs_const1 := 0;
                                 rhs_terms1 := [(1, pvar)]
                               |} in
                               match PVM.find pv c1map with
                               | Some cs1 => PVM.add pv (nc :: cs1) c1map
                               | _ => PVM.add pv [nc] c1map
                               end
  | Gtyp (Fuint_implicit _), Gtyp (Fuint w)
  | Gtyp (Fsint_implicit _), Gtyp (Fsint w) => 
                                let nc := {|
                                 lhs_var1 := pv;
                                 rhs_const1 := Z.of_nat w;
                                 rhs_power := nil;
                                 rhs_terms1 := []
                               |} in
                               match PVM.find pv c1map with
                               | Some cs1 => PVM.add pv (nc :: cs1) c1map
                               | _ => PVM.add pv [nc] c1map
                               end
  | Atyp atyp _, Atyp atyp_ref _ => extract_constraint_non_passive atyp atyp_ref pv pvar c1map
  | Btyp ff, Btyp ff_ref => extract_constraint_non_passive_f ff ff_ref pv pvar c1map
  | _, _ => c1map
  end
with extract_constraint_non_passive_f (ff ff_ref : ffield) (pv pvar : ProdVar.t) (c1map : PVM.t (list Constraint1)) : PVM.t (list Constraint1) :=
  match ff, ff_ref with
  | Fnil, Fnil => c1map
  | Fflips _ Nflip t fs, Fflips _ Nflip t_ref fs_ref => let nmap := extract_constraint_non_passive t t_ref pv pvar c1map in 
                           extract_constraint_non_passive_f fs fs_ref (pv.1, N.add pv.2 (N.of_nat (size_of_ftype t))) (pvar.1, N.add pvar.2 (N.of_nat (size_of_ftype t))) nmap
  | Fflips _ Flipped t fs, Fflips _ Flipped t_ref fs_ref => let nmap := extract_constraint_non_passive t t_ref pvar pv c1map in
                           extract_constraint_non_passive_f fs fs_ref (pv.1, N.add pv.2 (N.of_nat (size_of_ftype t))) (pvar.1, N.add pvar.2 (N.of_nat (size_of_ftype t))) nmap
  | _, _ => c1map
  end.

Fixpoint extract_constraint (s : hfstmt) (tmap : VM.t (ftype * forient)) (c1map : PVM.t (list Constraint1)) : option (list (PVM.t (list Constraint1) * list Constraint2)) :=
  match s with
  | Sskip => Some [(c1map, nil)]
  | Sfcnct r expr => match type_of_ref r tmap with
                    | Some (Gtyp gt) => if not_implicit gt then Some [(c1map, nil)]
                        else match ref2pv r tmap, extract_constraint_expr expr tmap with
                            | Some pv, Some exprs_cs2 => Some (map (fun '(exprs, cs2) => 
                              let ncs1 := map (fun '(terms, terms', cst) => {|
                                  lhs_var1 := pv;
                                  rhs_const1 := cst;
                                  rhs_power := terms';
                                  rhs_terms1 := terms
                                |}) exprs in
                                let nmap := match PVM.find pv c1map with
                                  | Some cs1 => PVM.add pv (ncs1 ++ cs1) c1map
                                  | _ => PVM.add pv ncs1 c1map
                                end in (nmap, cs2)) exprs_cs2)
                            | _, _ => None
                            end
                    | Some ft => match expr with
                            | Eref ref => match ref2pv r tmap, ref2pv ref tmap, type_of_ref ref tmap with
                                        | Some pv, Some pvar, Some ft_ref => let nmap := extract_constraint_non_passive ft ft_ref pv pvar c1map in Some [(nmap, nil)]
                                        | _, _, _ => None
                                        end
                            | Emux c e0 e1 => match ref2pv r tmap, expand_mux expr tmap with
                                        | Some pv, Some rhsl_cs2 => Some (map (fun '(rhsl, cs2) => 
                                            let nmap := fold_left (fun temp_map ref0 => 
                                                match ref2pv ref0 tmap, type_of_ref ref0 tmap with
                                                | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref pv pvar temp_map
                                                | _, _ => temp_map
                                                end) rhsl c1map in (nmap, cs2)) rhsl_cs2)
                                        | _, _ => None
                                        end
                            | _ => None
                            end
                    | _ => None
                    end
  | Sinvalid _ => Some [(c1map, nil)]
  | Swire _ _ => Some [(c1map, nil)]
  | Sreg v reg => match type reg with
                | Gtyp gt => if not_implicit gt then Some [(c1map, nil)]
                    else match reset reg with
                    | NRst => Some [(c1map, nil)]
                    | Rst _ rst_val => match extract_constraint_expr rst_val tmap with
                                      | Some exprs_cs2 => 
                                        Some (map (fun '(exprs, cs2) => 
                                        let ncs1 := map (fun '(terms, terms', cst) => {|
                                          lhs_var1 := (v, N0);
                                          rhs_const1 := cst;
                                          rhs_terms1 := terms;
                                          rhs_power := terms'
                                        |}) exprs in
                                        let nmap := match PVM.find (v, N0) c1map with
                                          | Some cs1 => PVM.add (v, N0) (ncs1 ++ cs1) c1map
                                          | _ => PVM.add (v, N0) ncs1 c1map
                                        end in (nmap, cs2)) exprs_cs2)  
                                      | _ => None
                                      end
                    end
                | ft => match reset reg with
                        | NRst => Some [(c1map, nil)]
                        | Rst _ rst_val => match rst_val with
                                      | Eref ref => match ref2pv ref tmap, type_of_ref ref tmap with
                                                  | Some pvar, Some ft_ref => let nmap := extract_constraint_passive ft ft_ref (v, N0) pvar c1map in Some [(nmap, nil)]
                                                  | _, _ => None
                                                  end
                                      | Emux c e0 e1 => match expand_mux rst_val tmap with
                                                  | Some rhsl_cs2 => Some (map (fun '(rhsl, cs2) => 
                                                      let nmap := fold_left (fun temp_map ref0 => 
                                                          match ref2pv ref0 tmap, type_of_ref ref0 tmap with
                                                          | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref (v, N0) pvar temp_map
                                                          | _, _ => temp_map
                                                          end) rhsl c1map in (nmap, cs2)) rhsl_cs2)
                                                  | _ => None
                                                  end
                                      | _ => None
                                      end
                        end
                end
  | Snode v e => match type_of_ref (Eid v) tmap with
                | Some (Gtyp gt) => match extract_constraint_expr e tmap with
                                  | Some exprs_cs2 => Some (map (fun '(exprs, cs2) => 
                                      let ncs1 := map (fun '(terms, terms', cst) => {|
                                      lhs_var1 := (v, N0);
                                      rhs_const1 := cst;
                                      rhs_terms1 := terms;
                                      rhs_power := terms'
                                    |}) exprs in
                                    let nmap := match PVM.find (v, N0) c1map with
                                      | Some cs1 => PVM.add (v, N0) (ncs1 ++ cs1) c1map
                                      | _ => PVM.add (v, N0) ncs1 c1map
                                    end in (nmap, cs2)) exprs_cs2)
                                  | _ => None
                                  end
                | Some ft => match e with
                            | Eref ref => match ref2pv ref tmap, type_of_ref ref tmap with
                                        | Some pvar, Some ft_ref => let nmap := extract_constraint_passive ft ft_ref (v, N0) pvar c1map in Some [(nmap, nil)]
                                        | _, _ => None
                                        end
                            | Emux c e0 e1 => match expand_mux e tmap with
                                        | Some rhsl_cs2 => Some (map (fun '(rhsl, cs2) =>
                                          let nmap := fold_left (fun temp_map ref0 => 
                                                          match ref2pv ref0 tmap, type_of_ref ref0 tmap with
                                                          | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref (v, N0) pvar temp_map
                                                          | _, _ => temp_map
                                                          end) rhsl c1map in (nmap, cs2)) rhsl_cs2)
                                        | _ => None
                                        end
                            | _ => None
                            end
                | _ => None
                end
  | Smem _ _ => Some [(c1map, nil)]
  | Sinst _ _ => Some [(c1map, nil)]
  | Swhen c ss_true ss_false =>
    match type_of_hfexpr c tmap, extract_constraint_expr c tmap, 
          extract_constraints ss_true tmap c1map with
    | Some (exist (Gtyp (Fuint _)) _), Some ec_cs2, Some c1map_true_cs2_true => 
      fold_left (fun res '(c1map_true, cs2_true) =>
        fold_left (fun temp_res '(ec, cs2) => 
                      let ncs2 := map (fun '(terms, _, cst) => {|
                        lhs_const2 := 1 - (Z.to_nat cst);
                        rhs_terms2 := terms
                        |}) ec in
                      match temp_res, extract_constraints ss_false tmap c1map_true with
                      | Some ls, Some c1map_false_cs2_false => Some (map (fun '(c1map_false, cs2_false) =>
                        (c1map_false, ncs2 ++ cs2 ++ cs2_true ++ cs2_false)) c1map_false_cs2_false ++ ls) 
                      | _, _ => None
                      end) ec_cs2 res) c1map_true_cs2_true (Some nil)
    | _, _, _ => None
    end 
  end
with extract_constraints (ss : hfstmt_seq) (tmap : VM.t (ftype * forient)) (c1map : PVM.t (list Constraint1)) : option (list (PVM.t (list Constraint1) * list Constraint2)) :=
  match ss with
  | Qnil => Some [(c1map, nil)]
  | Qcons s st => 
    match extract_constraint s tmap c1map with
    | Some nmap_c2 => fold_left (fun res '(nmap, c2) => 
        match res, extract_constraints st tmap nmap with
        | Some ls, Some nmap'_cs2 =>  Some (map (fun '(nmap', cs2) => (nmap', c2 ++ cs2)) nmap'_cs2 ++ ls) 
        | _, _ => None
        end) nmap_c2 (Some nil)
    | _ => None
    end
  end.

Definition extract_constraint_tailrec (s : hfstmt) (tmap : VM.t (ftype * forient)) (c1map : PVM.t (list Constraint1)) : option (list (PVM.t (list Constraint1) * list Constraint2)) :=
  match s with
  | Sskip => Some [(c1map, nil)]
  | Sfcnct r expr => match type_of_ref r tmap with
                    | Some (Gtyp gt) => if not_implicit gt then Some [(c1map, nil)]
                        else match ref2pv r tmap, extract_constraint_expr expr tmap with
                            | Some pv, Some exprs_cs2 => Some (map (fun '(exprs, cs2) => 
                              let ncs1 := map (fun '(terms, terms', cst) => {|
                                  lhs_var1 := pv;
                                  rhs_const1 := cst;
                                  rhs_power := terms';
                                  rhs_terms1 := terms
                                |}) exprs in
                                let nmap := match PVM.find pv c1map with
                                  | Some cs1 => PVM.add pv (ncs1 ++ cs1) c1map
                                  | _ => PVM.add pv ncs1 c1map
                                end in (nmap, cs2)) exprs_cs2)
                            | _, _ => None
                            end
                    | Some ft => match expr with
                            | Eref ref => match ref2pv r tmap, ref2pv ref tmap, type_of_ref ref tmap with
                                        | Some pv, Some pvar, Some ft_ref => let nmap := extract_constraint_non_passive ft ft_ref pv pvar c1map in Some [(nmap, nil)]
                                        | _, _, _ => None
                                        end
                            | Emux c e0 e1 => match ref2pv r tmap, expand_mux expr tmap with
                                        | Some pv, Some rhsl_cs2 => Some (map (fun '(rhsl, cs2) => 
                                            let nmap := fold_left (fun temp_map ref0 => 
                                                match ref2pv ref0 tmap, type_of_ref ref0 tmap with
                                                | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref pv pvar temp_map
                                                | _, _ => temp_map
                                                end) rhsl c1map in (nmap, cs2)) rhsl_cs2)
                                        | _, _ => None
                                        end
                            | _ => None
                            end
                    | _ => None
                    end
  | Sinvalid _ => Some [(c1map, nil)]
  | Swire _ _ => Some [(c1map, nil)]
  | Sreg v reg => match type reg with
                | Gtyp gt => if not_implicit gt then Some [(c1map, nil)]
                    else match reset reg with
                    | NRst => Some [(c1map, nil)]
                    | Rst _ rst_val => match extract_constraint_expr rst_val tmap with
                                      | Some exprs_cs2 => 
                                        Some (map (fun '(exprs, cs2) => 
                                        let ncs1 := map (fun '(terms, terms', cst) => {|
                                          lhs_var1 := (v, N0);
                                          rhs_const1 := cst;
                                          rhs_terms1 := terms;
                                          rhs_power := terms'
                                        |}) exprs in
                                        let nmap := match PVM.find (v, N0) c1map with
                                          | Some cs1 => PVM.add (v, N0) (ncs1 ++ cs1) c1map
                                          | _ => PVM.add (v, N0) ncs1 c1map
                                        end in (nmap, cs2)) exprs_cs2)  
                                      | _ => None
                                      end
                    end
                | ft => match reset reg with
                        | NRst => Some [(c1map, nil)]
                        | Rst _ rst_val => match rst_val with
                                      | Eref ref => match ref2pv ref tmap, type_of_ref ref tmap with
                                                  | Some pvar, Some ft_ref => let nmap := extract_constraint_passive ft ft_ref (v, N0) pvar c1map in Some [(nmap, nil)]
                                                  | _, _ => None
                                                  end
                                      | Emux c e0 e1 => match expand_mux rst_val tmap with
                                                  | Some rhsl_cs2 => Some (map (fun '(rhsl, cs2) => 
                                                      let nmap := fold_left (fun temp_map ref0 => 
                                                          match ref2pv ref0 tmap, type_of_ref ref0 tmap with
                                                          | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref (v, N0) pvar temp_map
                                                          | _, _ => temp_map
                                                          end) rhsl c1map in (nmap, cs2)) rhsl_cs2)
                                                  | _ => None
                                                  end
                                      | _ => None
                                      end
                        end
                end
  | Snode v e => match type_of_ref (Eid v) tmap with
                | Some (Gtyp gt) => match extract_constraint_expr e tmap with
                                  | Some exprs_cs2 => Some (map (fun '(exprs, cs2) => 
                                      let ncs1 := map (fun '(terms, terms', cst) => {|
                                      lhs_var1 := (v, N0);
                                      rhs_const1 := cst;
                                      rhs_terms1 := terms;
                                      rhs_power := terms'
                                    |}) exprs in
                                    let nmap := match PVM.find (v, N0) c1map with
                                      | Some cs1 => PVM.add (v, N0) (ncs1 ++ cs1) c1map
                                      | _ => PVM.add (v, N0) ncs1 c1map
                                    end in (nmap, cs2)) exprs_cs2)
                                  | _ => None
                                  end
                | Some ft => match e with
                            | Eref ref => match ref2pv ref tmap, type_of_ref ref tmap with
                                        | Some pvar, Some ft_ref => let nmap := extract_constraint_passive ft ft_ref (v, N0) pvar c1map in Some [(nmap, nil)]
                                        | _, _ => None
                                        end
                            | Emux c e0 e1 => match expand_mux e tmap with
                                        | Some rhsl_cs2 => Some (map (fun '(rhsl, cs2) =>
                                          let nmap := fold_left (fun temp_map ref0 => 
                                                          match ref2pv ref0 tmap, type_of_ref ref0 tmap with
                                                          | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref (v, N0) pvar temp_map
                                                          | _, _ => temp_map
                                                          end) rhsl c1map in (nmap, cs2)) rhsl_cs2)
                                        | _ => None
                                        end
                            | _ => None
                            end
                | _ => None
                end
  | Smem _ _ => Some [(c1map, nil)]
  | Sinst _ _ => Some [(c1map, nil)]
  | Swhen _ _ _ => None
  end.

Fixpoint extract_constraints_tailrec (ss : hfstmt_seq) (tmap : VM.t (ftype * forient)) (res : list (PVM.t (list Constraint1) * list Constraint2)) 
          : option (list (PVM.t (list Constraint1) * list Constraint2)) :=
  match ss with
  | Qnil => Some res
  | Qcons s st => let res' := fold_left (fun ls '(c1map, cs2) => 
    match ls, extract_constraint_tailrec s tmap c1map with
    | Some ls', Some nmap_c2 => Some (nmap_c2 ++ ls')
    | _, _ => None
    end) res (Some nil) in 
    match res' with
    | Some res'' => extract_constraints_tailrec st tmap res''
    | _ => None
    end
  end.

Fixpoint expandwhen (s : hfstmt) (res : hfstmt_seq * (list hfexpr)) : hfstmt_seq * (list hfexpr) :=
  match s with
  | Swhen c s1 s2 => let res' := expandwhens s1 res in 
                     let (s2', c2') := expandwhens s2 res' in (s2', c :: c2') 
  | _ => (Qcons s res.1, res.2)
  end
with expandwhens (ss : hfstmt_seq) (res : hfstmt_seq * (list hfexpr)) : hfstmt_seq * (list hfexpr) :=
  match ss with
  | Qnil => res
  | Qcons s st => expandwhens st (expandwhen s res)
  end.

Definition extract_constraint_m (m : hfmodule) (tmap : VM.t (ftype * forient)) (c1map : PVM.t (list Constraint1)) : option (list (PVM.t (list Constraint1) * list Constraint2)) :=
  match m with
  | FInmod _ _ ss => let (ss', _) := expandwhens ss (Qnil, []) in
                     extract_constraints ss' tmap c1map
  | _ => None
  end.

Definition extract_constraints_c (c : hfcircuit) (tmap : (VM.t (ftype * forient))) : option (list (PVM.t (list Constraint1) * list Constraint2)) :=
  match c with
  | Fcircuit _ [m] => extract_constraint_m m tmap (PVM.empty (list Constraint1))
  | _ => None
  end.

Fixpoint extract_cs (ls : list ProdVar.t) (cs1 : PVM.t (list Constraint1)) : list Constraint1 := 
  match ls with
  | nil => []
  | hd :: tl => match PVM.find hd cs1 with
      | Some c => c ++ (extract_cs tl cs1)
      | _ => extract_cs tl cs1
      end
  end.

Lemma extract_cs_app c1map : forall l0 l1, extract_cs (l0 ++ l1) c1map = extract_cs l0 c1map ++ extract_cs l1 c1map.
Proof.
  intros l0 l1.
  induction l0 as [|hd tl IH].
  - (* Base case: l0 = nil *)
    simpl. reflexivity.
  - (* Inductive step: l0 = hd :: tl *)
    simpl. destruct (PVM.find hd c1map) eqn:Hfind.
    + (* Case: Some c *)
      rewrite IH. rewrite catA //.
    + (* Case: None *)
      rewrite IH. reflexivity.
Qed.

Lemma extract_cs_lhs_in c1map : forall a (c : Constraint1), 
  (forall var, List.In var a -> exists cs, PVM.find var c1map = Some cs /\
    forallb (fun c : Constraint1 => lhs_var1 c == var) cs) ->
  List.In c (extract_cs a c1map) -> List.In (lhs_var1 c) a.
Proof.
  elim. simpl; intros; done.
  simpl; intros. destruct (H0 a) as [cs [Hfind Hlhs]]. left; done.  
  rewrite Hfind in H1. apply in_app_or in H1. destruct H1.
  - left; symmetry. apply (elimT eqP). move : c H1. apply forallb_forall. done.
  - right; apply H; try done. intros; apply H0. right; done.
Qed.

Fixpoint remove_solved (values : Valuation) (terms : list term) : list term * Z.t :=
match terms with
| nil => (nil, 0%Z)
| (coe, var) :: tl => match PVM.find var values, remove_solved values tl with
  | Some val, (terms', cst) => (terms', Z.add cst (Z.of_nat (coe * val)))
  | _, (terms', cst) => ((coe, var) :: terms', cst)
  end
end.

Definition remove_solved_c (values : Valuation) (c : Constraint1) : Constraint1 :=
  let '(new_terms, new_cst) := remove_solved values (rhs_terms1 c) in
  match rhs_power c with
  | nil => 
      {| lhs_var1 := lhs_var1 c;
        rhs_const1 := Z.add (rhs_const1 c) new_cst;
        rhs_power := nil;
        rhs_terms1 := new_terms |}
  | (_, var) :: _ =>
    match PVM.find var values with
    | Some val => 
      {| lhs_var1 := lhs_var1 c;
        rhs_const1 := Z.add (Z.add (rhs_const1 c) new_cst) (Z.pow 2 (Z.of_nat val));
        rhs_power := nil;
        rhs_terms1 := new_terms |}
    | None => 
      {| lhs_var1 := lhs_var1 c;
        rhs_const1 := Z.add (rhs_const1 c) new_cst;
        rhs_power := rhs_power c;
        rhs_terms1 := new_terms |}
    end
  end.

Fixpoint remove_solveds (values : Valuation) (cs : list Constraint1) : list Constraint1 :=
match cs with
| nil => nil
| c :: cs' => remove_solved_c values c :: remove_solveds values cs'
end.

Fixpoint merge_solution (tbsolved : list ProdVar.t) (initial solution_of_tbsolved : Valuation) : option Valuation := 
match tbsolved with
| nil => Some initial
| hd :: tl => match PVM.find hd solution_of_tbsolved with
  | Some val => merge_solution tl (PVM.add hd val initial) solution_of_tbsolved
  | _ => None
  end
end.

End Extract_Constraints_better.