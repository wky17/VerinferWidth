From HB Require Import structures.
From Coq Require Import ZArith Arith List Ascii String Lia FMaps.
From mathcomp Require Import all_ssreflect.
From Solver Require Import Env LoFirrtl HiEnv HiFirrtl constraints extract_cs extract_cswithmin inferWidths.
Import ListNotations.

Section Extract_Constraints_for_multimod.

(* 定义配对函数: nat * nat -> nat *)
Definition cantor_pairing (p : nat * nat) : nat :=
  let (m, n) := p in
  let s := m + n in
  (s * (s + 1)) / 2 + n.

(* 辅助函数：计算最大的 w *)
Definition find_w (z : nat) : nat :=
  (Nat.sqrt (8 * z + 1) - 1) / 2.
  
(* 定义逆映射: nat -> nat * nat *)
Definition cantor_unpairing (z : nat) : nat * nat :=
  let w := find_w z in
  let t := (w * (w + 1)) / 2 in
  let n := z - t in
  let m := w - n in
  (m, n).

Compute(cantor_pairing (1,7)).
Compute(cantor_unpairing 43).

Fixpoint find_ref_inside (instv : VM.key) (r : href) : option href :=
  match r with
  | Eid v => None
  | Esubfield (Eid instv) v => Some (Eid v)
  | Esubfield ref v => match find_ref_inside instv ref with
                      | Some subref => Some (Esubfield subref v)
                      | _ => None
                      end
  | Esubindex ref n => match find_ref_inside instv ref with
                      | Some subref => Some (Esubindex subref n)
                      | _ => None
                      end
  | Esubaccess ref e => match find_ref_inside instv ref with
                      | Some subref => Some (Esubaccess subref e)
                      | _ => None
                      end
  end.

Compute (find_ref_inside (N.of_nat 4) (Esubfield (Eid (N.of_nat 4)) (N.of_nat 1))).
Compute (find_ref_inside (N.of_nat 4) (Esubfield (Esubfield (Eid (N.of_nat 4)) (N.of_nat 0)) (N.of_nat 1))).

Definition ref2pv_mod (r : href) (mv : VM.key) (instmap : VM.t VM.key)(* mapping known instance name to module name *) 
  (tmap : VM.t (VM.t (ftype * forient))) : option ProdVar.t :=
  let base_ref := base_id r in
  match VM.find base_ref instmap with
  | Some inst_mv => (* base_ref 是inst名，inst_mv 是对应module名 *)
      match find_ref_inside base_ref r, VM.find inst_mv tmap with
      | Some inst_ref, Some inst_tmap => match ref2pv inst_ref inst_tmap with
          | Some pv => Some (inst_mv, N.of_nat (cantor_pairing (N.to_nat (fst pv), N.to_nat (snd pv))))
          | _ => None
          end
      | _, _ => None
      end
  | _ => (* r是本mod中的普通cmpnt *)
      match VM.find mv tmap with
      | Some mod_tmap => match ref2pv r mod_tmap with
          | Some pv => Some (mv, N.of_nat (cantor_pairing (N.to_nat (fst pv), N.to_nat (snd pv))))
          | _ => None
          end
      | _ => None
      end
  end.

(*Definition type_of_ref_mod (r : href) (mv : VM.key) (instmap : VM.t VM.key)
  (tmap : VM.t (VM.t (ftype * forient))) : option ftype :=
  let base_ref := base_id r in 
  match VM.find base_ref instmap with
  | Some inst_mv => (* base_ref 是inst名，inst_mv 是对应module名 *)
      match find_ref_inside base_ref r, VM.find inst_mv tmap with
      | Some inst_ref, Some inst_tmap => type_of_ref inst_ref inst_tmap
      | _, _ => None
      end
  | _ => match VM.find mv tmap with
      | Some mod_tmap => type_of_ref r mod_tmap
      | _ => None
      end
  end.

Fixpoint type_of_hfexpr_mod (mv : VM.key) (instmap : VM.t VM.key) (e : hfexpr) (tmap: VM.t (VM.t (ftype * forient))) : option ftype_explicit := 
  match e with
  | Econst t bs => match t with
                  | Fuint_implicit _ => Some (exist ftype_not_implicit_width (Gtyp (Fuint (size bs))) I)
                  | Fsint_implicit _ => Some (exist ftype_not_implicit_width (Gtyp (Fsint (size bs))) I)
                  | t => Some (exist ftype_not_implicit_width (Gtyp t) I)
                  end
  | Eref r => match type_of_ref_mod r mv instmap tmap with
            | Some ft => Some (make_ftype_explicit ft)
            | _ => None
            end
  | Ecast AsUInt e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                        | Some (exist (Gtyp (Fsint w)) _)
                        | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                        | Some (exist (Gtyp Fclock) _)
                        | Some (exist (Gtyp Freset) _)
                        | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                        | _ => None
                        end
  | Ecast AsSInt e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                        | Some (exist (Gtyp (Fsint w)) _)
                        | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                        | Some (exist (Gtyp Fclock) _)
                        | Some (exist (Gtyp Freset) _)
                        | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint 1)) I)
                        | _ => None
                        end
  | Ecast AsClock e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                        | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fclock) I)
                        | _ => None
                        end
  | Ecast AsAsync e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                        | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fasyncreset) I)
                        | _ => None
                        end
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                              | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w n))) I)
                              | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w n))) I)
                              | _ => None
                              end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                              | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + n))) I)
                              | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w + n))) I)
                              | _ => None
                              end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                              | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn (w - n) 1))) I)
                              | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn (w - n) 0))) I)
                              | _ => None
                              end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                          | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                          | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                          | _ => None
                          end
  | Eprim_unop Uneg e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                          | Some (exist (Gtyp (Fsint w)) _)
                          | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                          | _ => None
                          end
  | Eprim_unop Unot e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                          | Some (exist (Gtyp (Fsint w)) _)
                          | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                          | _ => None
                          end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                                    | Some (exist (Gtyp (Fsint w)) _)
                                    | Some (exist (Gtyp (Fuint w)) _) =>
                                        (*if (n2 <= n1) && (n1 < w) then*) Some (exist ftype_not_implicit_width (Gtyp (Fuint (n1 - n2 + 1))) I)
                                                                  (*else None*)
                                    | _ => None
                                    end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _)
                                | Some (exist (Gtyp (Fuint w)) _) =>
                                    (*if n <= w then*) Some (exist ftype_not_implicit_width (Gtyp (Fuint n)) I)
                                              (*else None*)
                                | _ => None
                                end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _)
                                | Some (exist (Gtyp (Fuint w)) _) =>
                                    (*if n <= w then*) Some (exist ftype_not_implicit_width (Gtyp (Fuint (w - n))) I)
                                              (*else None*)
                                | _ => None
                                end
  | Eprim_unop _ e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                        | Some (exist (Gtyp (Fsint _)) _)
                        | Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                        | _ => None
                        end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap with
                                    | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _)
                                    | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                                    | _, _ => None
                                    end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap with
                              | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2 + 1))) I)
                              | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w1 w2 + 1))) I)
                              | _, _ => None
                              end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap with
                              | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                              | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + w2))) I)
                              | _, _ => None
                              end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + 1))) I)
                                | _, _ => None
                                end
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (minn w1 w2))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (minn w1 w2))) I)
                                | _, _ => None
                                end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (2 ^ w2 + w1 - 1))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (2 ^ w2 + w1 - 1))) I)
                                | _, _ => None
                                end
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w1)) I)
                                | _, _ => None
                                end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap with
                              | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                              | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                              | _, _ => None
                              end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap with
                              | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                              | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2))) I)
                              | _, _ => None
                              end
  | Emux c e1 e2 => match type_of_hfexpr_mod mv instmap c tmap, type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap with
                    | Some (exist (Gtyp (Fuint _)) _), Some t1, Some t2 => ftype_mux t1 t2
                    | _, _, _ => None
                    end
  end.

Fixpoint extract_constraint_expr_mod (mv : VM.key) (e : hfexpr) (tmap : VM.t (VM.t (ftype * forient))) (instmap : VM.t VM.key) 
  : option ((list min_rhs) * (list min_rhs)) :=
  (* min_rhs 的 Expr case 是一条phi1约束的一次项，指数项和常数项。rem产生min_rhs 中的 Min case
     mux 直接生成 list of min_rhs
     constraint2 来自 mux的condition*)
  match e with
  | Eref r => match type_of_ref_mod r mv instmap tmap, ref2pv_mod r mv instmap tmap with
                            | Some (Gtyp (Fuint_implicit _)), Some pv 
                            | Some (Gtyp (Fsint_implicit _)), Some pv => Some ([Expr (make_rhs [(1, pv)] nil 0%Z)], nil)
                            | Some (Gtyp gt), _ => Some ([Expr (make_rhs nil nil (Z.of_nat (sizeof_fgtyp gt)))], nil)
                            | _, _ => None
                            end
  | Econst t bs => match t with
                            | Fuint_implicit _ 
                            | Fsint_implicit _ => Some ([Expr (make_rhs nil nil (Z.of_nat (size bs)))], nil)
                            | t => Some ([Expr (make_rhs nil nil (Z.of_nat (sizeof_fgtyp t)))], nil)
                            end
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap,
                            extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (map (fun '(a,b) => Min a b) (cartesian el1 el2), cs1 ++ cs2)
                            | _, _, _, _ => None 
                            end
  | Ecast AsUInt e1 
  | Ecast AsSInt e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                            | Some (exist (Gtyp _) _) => extract_constraint_expr_mod mv e1 tmap instmap
                            | _ => None
                            end
  | Eprim_unop Unot e1 => match type_of_hfexpr_mod mv instmap e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _)
                            | Some (exist (Gtyp (Fuint w)) _) => extract_constraint_expr_mod mv e1 tmap instmap
                            | _ => None
                            end
  | Ecast AsClock e1 
  | Ecast AsAsync e1 => match type_of_hfexpr_mod mv instmap e1 tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp _) _), Some (_, cs) => Some ([Expr (make_rhs nil nil 1%Z)], cs)
                            | _, _ => None
                            end
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr_mod mv instmap e1 tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => Some (Expr (make_rhs nil nil (Z.of_nat n)) :: el, cs)
                            | _, _ => None
                            end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr_mod mv instmap e1 tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs) 
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.of_nat n)) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr_mod mv instmap e1 tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs) => 
                              let nexp := map (fun temp_e => min_rhs_add_cst temp_e (Z.opp (Z.of_nat n))) el in
                                Some (Expr (make_rhs nil nil 1%Z) :: nexp, cs) 
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => 
                                Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.opp (Z.of_nat n))) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr_mod mv instmap e1 tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (el, cs) => Some (el, cs)
                            | Some (exist (Gtyp (Fuint _)) _), Some (el, cs) => 
                                Some (map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop Uneg e1 => match type_of_hfexpr_mod mv instmap e1 tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (el, cs) 
                            | Some (exist (Gtyp (Fuint _)) _), Some (el, cs) => 
                                Some (map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr_mod mv instmap e1 tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => (*if (n2 <= n1) && (n1 < w) then *)
                                Some ([Expr (make_rhs nil nil (Z.of_nat (n1 - n2 + 1)))], cs) (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr_mod mv instmap e1 tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => (*if n <= w then *)
                                Some ([Expr (make_rhs nil nil (Z.of_nat n))], cs) (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr_mod mv instmap e1 tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => (*if n <= w then *)
                                Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.opp (Z.of_nat n))) el, cs)
                              (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop _ e1 => match type_of_hfexpr_mod mv instmap e1 tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint _)) _), Some (el, cs) => 
                              Some ([Expr (make_rhs nil nil 1%Z)], cs)
                            | _, _ => None
                            end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _), Some (el1, cs1), Some (el2, cs2)
                            | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _), Some (el1, cs1), Some (el2, cs2) => 
                                Some ([Expr (make_rhs nil nil 1%Z)], cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                                let nexp1 := map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el1 in
                                let nexp2 := map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el2 in
                                Some (nexp1 ++ nexp2, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (map (fun '(e1, e2) => combine_min_rhs e1 e2) (cartesian el1 el2), cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1, cs1 ++ cs2)
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.opp 1%Z)) el1, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1) =>
                                match e2 with
                                | Eref r => match type_of_ref_mod r mv instmap tmap, ref2pv_mod r mv instmap tmap with
                                          | Some (Gtyp (Fuint_implicit _)), Some pv => Some (map (fun temp_e => min_rhs_add_power temp_e pv) el1, cs1)
                                          | Some (Gtyp (Fuint w)), _ => 
                                            Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.sub (Z.pow 2 (Z.of_nat w)) 1)) el1, cs1)
                                          | _, _ => None
                                          end
                                | Econst t bs => match t with
                                          | Fuint_implicit _ 
                                          | Fsint_implicit _ => Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.sub (Z.pow 2 (Z.of_nat (size bs))) 1)) el1, cs1)
                                          | t => Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.sub (Z.pow 2 (Z.of_nat (sizeof_fgtyp t))) 1)) el1, cs1)
                                          end
                                | _ => None
                                end
                            | _, _, _ => None
                            end
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2)
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                                Some (map (fun '(e1, e2) => combine_min_rhs e1 e2) (cartesian el1 el2), cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr_mod mv instmap e1 tmap, type_of_hfexpr_mod mv instmap e2 tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1 ++ el2, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Emux c e1 e2 => match type_of_hfexpr_mod mv instmap c tmap, extract_constraint_expr_mod mv c tmap instmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint _)) _), Some (ec, cs0), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1 ++ el2, ec ++ cs0 ++ cs1 ++ cs2)
                            | _, _, _, _ => None
                            end (* condition c 只能是 0/1位宽 *)
end.*)

Fixpoint extract_constraint_expr_mod (mv : VM.key) (e : hfexpr) (tmap : VM.t (VM.t (ftype * forient))) (instmap : VM.t VM.key) 
  : option ((list min_rhs) * (list min_rhs)) :=
  (* min_rhs 的 Expr case 是一条phi1约束的一次项，指数项和常数项。rem产生min_rhs 中的 Min case
     mux 直接生成 list of min_rhs
     constraint2 来自 mux的condition*)
match VM.find mv tmap with
| Some mod_tmap => 
  match e with
  | Eref r => match type_of_ref r mod_tmap, ref2pv_mod r mv instmap tmap with
                            | Some (Gtyp (Fuint_implicit _)), Some pv 
                            | Some (Gtyp (Fsint_implicit _)), Some pv => Some ([Expr (make_rhs [(1, pv)] nil 0%Z)], nil)
                            | Some (Gtyp gt), _ => Some ([Expr (make_rhs nil nil (Z.of_nat (sizeof_fgtyp gt)))], nil)
                            | _, _ => None
                            end
  | Econst t bs => match t with
                            | Fuint_implicit _ 
                            | Fsint_implicit _ => Some ([Expr (make_rhs nil nil (Z.of_nat (size bs)))], nil)
                            | t => Some ([Expr (make_rhs nil nil (Z.of_nat (sizeof_fgtyp t)))], nil)
                            end
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                            extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (map (fun '(a,b) => Min a b) (cartesian el1 el2), cs1 ++ cs2)
                            | _, _, _, _ => None 
                            end
  | Ecast AsUInt e1 
  | Ecast AsSInt e1 => match type_of_hfexpr e1 mod_tmap with
                            | Some (exist (Gtyp _) _) => extract_constraint_expr_mod mv e1 tmap instmap
                            | _ => None
                            end
  | Eprim_unop Unot e1 => match type_of_hfexpr e1 mod_tmap with
                            | Some (exist (Gtyp (Fsint w)) _)
                            | Some (exist (Gtyp (Fuint w)) _) => extract_constraint_expr_mod mv e1 tmap instmap
                            | _ => None
                            end
  | Ecast AsClock e1 
  | Ecast AsAsync e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp _) _), Some (_, cs) => Some ([Expr (make_rhs nil nil 1%Z)], cs)
                            | _, _ => None
                            end
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => Some (Expr (make_rhs nil nil (Z.of_nat n)) :: el, cs)
                            | _, _ => None
                            end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs) 
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.of_nat n)) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs) => 
                              let nexp := map (fun temp_e => min_rhs_add_cst temp_e (Z.opp (Z.of_nat n))) el in
                                Some (Expr (make_rhs nil nil 1%Z) :: nexp, cs) 
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => 
                                Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.opp (Z.of_nat n))) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (el, cs) => Some (el, cs)
                            | Some (exist (Gtyp (Fuint _)) _), Some (el, cs) => 
                                Some (map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop Uneg e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (el, cs) 
                            | Some (exist (Gtyp (Fuint _)) _), Some (el, cs) => 
                                Some (map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => (*if (n2 <= n1) && (n1 < w) then *)
                                Some ([Expr (make_rhs nil nil (Z.of_nat (n1 - n2 + 1)))], cs) (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => (*if n <= w then *)
                                Some ([Expr (make_rhs nil nil (Z.of_nat n))], cs) (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => (*if n <= w then *)
                                Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.opp (Z.of_nat n))) el, cs)
                              (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop _ e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint _)) _), Some (el, cs) => 
                              Some ([Expr (make_rhs nil nil 1%Z)], cs)
                            | _, _ => None
                            end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _), Some (el1, cs1), Some (el2, cs2)
                            | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _), Some (el1, cs1), Some (el2, cs2) => 
                                Some ([Expr (make_rhs nil nil 1%Z)], cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                                let nexp1 := map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el1 in
                                let nexp2 := map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el2 in
                                Some (nexp1 ++ nexp2, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (map (fun '(e1, e2) => combine_min_rhs e1 e2) (cartesian el1 el2), cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1, cs1 ++ cs2)
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.opp 1%Z)) el1, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1) =>
                                match e2 with
                                | Eref r => match type_of_ref r mod_tmap, ref2pv_mod r mv instmap tmap with
                                          | Some (Gtyp (Fuint_implicit _)), Some pv => Some (map (fun temp_e => min_rhs_add_power temp_e pv) el1, cs1)
                                          | Some (Gtyp (Fuint w)), _ => 
                                            Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.sub (Z.pow 2 (Z.of_nat w)) 1)) el1, cs1)
                                          | _, _ => None
                                          end
                                | Econst t bs => match t with
                                          | Fuint_implicit _ 
                                          | Fsint_implicit _ => Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.sub (Z.pow 2 (Z.of_nat (size bs))) 1)) el1, cs1)
                                          | t => Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.sub (Z.pow 2 (Z.of_nat (sizeof_fgtyp t))) 1)) el1, cs1)
                                          end
                                | _ => None
                                end
                            | _, _, _ => None
                            end
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2)
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                                Some (map (fun '(e1, e2) => combine_min_rhs e1 e2) (cartesian el1 el2), cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1 ++ el2, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Emux c e1 e2 => match type_of_hfexpr c mod_tmap, extract_constraint_expr_mod mv c tmap instmap,
                                    extract_constraint_expr_mod mv e1 tmap instmap, extract_constraint_expr_mod mv e2 tmap instmap with
                            | Some (exist (Gtyp (Fuint _)) _), Some (ec, cs0), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1 ++ el2, ec ++ cs0 ++ cs1 ++ cs2)
                            | _, _, _, _ => None
                            end (* condition c 只能是 0/1位宽 *)
  end
| None => None
end.

Fixpoint extract_mux_mod (mv : VM.key) (instmap : VM.t VM.key) (e : hfexpr) (tmap : VM.t (VM.t (ftype * forient))) : option (list href * list min_rhs) := 
match VM.find mv tmap with
| Some mod_tmap => 
  match e with
  | Eref r => Some ([r], nil)
  | Emux c e1 e2 => match type_of_hfexpr c mod_tmap, extract_constraint_expr_mod mv c tmap instmap, 
                          extract_mux_mod mv instmap e1 tmap, extract_mux_mod mv instmap e2 tmap with
                  | Some (exist (Gtyp (Fuint _)) _), Some (ec, cs0), Some (r1, cs1), Some (r2, cs2) => 
                    Some (r1 ++ r2, ec ++ cs0 ++ cs1 ++ cs2)
                  | _, _, _, _ => None
                  end
  | _ => None
  end
| _ => None
end.

Fixpoint extract_constraint_ss (mv : VM.key) (ss : hfstmt_seq) (tmap : VM.t (VM.t (ftype * forient))) (c1map : PVM.t (list Constraint1)) 
  (cs2 : list min_rhs) (cs_min : list Constraint_Min) (instmap : VM.t VM.key) 
  : option (PVM.t (list Constraint1) * list min_rhs * list Constraint_Min * VM.t VM.key) :=
  match ss with
  | Qnil => Some (c1map, cs2, cs_min, instmap)
  | Qcons s st => 
    match extract_constraint_s mv s tmap c1map cs2 cs_min instmap with
    | Some (c1map', cs2', cs_min', instmap') => extract_constraint_ss mv st tmap c1map' cs2' cs_min' instmap'
    | _ => None
    end
  end
with extract_constraint_s (mv : VM.key) (s : hfstmt) (tmap : VM.t (VM.t (ftype * forient))) (c1map : PVM.t (list Constraint1)) 
  (cs2 : list min_rhs) (cs_min : list Constraint_Min) (instmap : VM.t VM.key) 
  : option (PVM.t (list Constraint1) * list min_rhs * list Constraint_Min * VM.t VM.key) :=
match VM.find mv tmap with
| Some mod_tmap => 
  match s with
  | Sinst inst_v inst_mv => Some (c1map, cs2, cs_min, VM.add inst_v inst_mv instmap)
  | Sfcnct r expr => match type_of_ref r mod_tmap with
                    | Some (Gtyp gt) => if not_implicit gt then Some (c1map, cs2, cs_min, instmap)
                        else match ref2pv_mod r mv instmap tmap, extract_constraint_expr_mod mv expr tmap instmap with
                            | Some pv, Some (exprs, cs2') =>
                              let (regular_cs, cs_min') := seperate_min pv exprs (nil, nil) in
                              let nmap := match PVM.find pv c1map with
                                | Some cs1 => PVM.add pv (regular_cs ++ cs1) c1map
                                | _ => PVM.add pv regular_cs c1map
                                end
                              in Some (nmap, cs2 ++ cs2', cs_min ++ cs_min', instmap)
                            | _, _ => None
                            end
                    | Some ft => match expr with
                            | Eref ref => match ref2pv_mod r mv instmap tmap, ref2pv_mod ref mv instmap tmap, 
                                                type_of_ref ref mod_tmap with
                                        | Some pv, Some pvar, Some ft_ref => 
                                          let nmap := extract_constraint_non_passive ft ft_ref false pv pvar c1map in 
                                          Some (nmap, cs2, cs_min, instmap)
                                        | _, _, _ => None
                                        end
                            | Emux c e0 e1 => match ref2pv_mod r mv instmap tmap, extract_mux_mod mv instmap expr tmap with
                                        | Some pv, Some (rhsl, cs2') => 
                                            let nmap := fold_left (fun temp_map ref0 => 
                                                match ref2pv_mod ref0 mv instmap tmap, type_of_ref ref0 mod_tmap with
                                                | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref pv pvar temp_map
                                                | _, _ => temp_map
                                                end) rhsl c1map in Some (nmap, cs2 ++ cs2', cs_min, instmap)
                                        | _, _ => None
                                        end
                            | _ => None
                            end
                    | _ => None
                    end
  | Sreg v reg => let pv_reg := (mv, N.of_nat (cantor_pairing (N.to_nat v, 0))) in
                match type reg with
                | Gtyp gt => if not_implicit gt then Some (c1map, cs2, cs_min, instmap)
                    else match reset reg with
                    | NRst => Some (c1map, cs2, cs_min, instmap)
                    | Rst _ rst_val => match extract_constraint_expr_mod mv rst_val tmap instmap with
                                      | Some (exprs, cs2') => 
                                        let (regular_cs, cs_min') := seperate_min pv_reg exprs (nil, nil) in
                                        let nmap := match PVM.find pv_reg c1map with
                                          | Some cs1 => PVM.add pv_reg (regular_cs ++ cs1) c1map
                                          | _ => PVM.add pv_reg regular_cs c1map
                                          end
                                        in Some (nmap, cs2 ++ cs2', cs_min ++ cs_min', instmap)
                                      | _ => None
                                      end
                    end
                | ft => (* reg 只能passive *)
                        match reset reg with
                        | NRst => Some (c1map, cs2, cs_min, instmap)
                        | Rst _ rst_val => match rst_val with
                                      | Eref ref => match ref2pv_mod ref mv instmap tmap, type_of_ref ref mod_tmap with
                                                  | Some pvar, Some ft_ref => 
                                                    let nmap := extract_constraint_passive ft ft_ref pv_reg pvar c1map in 
                                                    Some (nmap, cs2, cs_min, instmap)
                                                  | _, _ => None
                                                  end
                                      | Emux c e0 e1 => match extract_mux_mod mv instmap rst_val tmap with
                                                  | Some (rhsl, cs2') => 
                                                      let nmap := fold_left (fun temp_map ref0 => 
                                                          match ref2pv_mod ref0 mv instmap tmap, type_of_ref ref0 mod_tmap with
                                                          | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref pv_reg pvar temp_map
                                                          | _, _ => temp_map
                                                          end) rhsl c1map in Some (nmap, cs2 ++ cs2', cs_min, instmap)
                                                  | _ => None
                                                  end
                                      | _ => None
                                      end
                        end
                end
  | Snode v e => let pv_node := (mv, N.of_nat (cantor_pairing (N.to_nat v, 0))) in 
                match VM.find mv tmap with
                | Some mod_tmap => match VM.find v mod_tmap with
                    | Some (Gtyp gt, _) => match extract_constraint_expr_mod mv e tmap instmap with
                                  | Some (exprs, cs2') => 
                                      let (regular_cs, cs_min') := seperate_min pv_node exprs (nil, nil) in
                                      let nmap := match PVM.find pv_node c1map with
                                        | Some cs1 => PVM.add pv_node (regular_cs ++ cs1) c1map
                                        | _ => PVM.add pv_node regular_cs c1map
                                        end
                                      in Some (nmap, cs2 ++ cs2', cs_min ++ cs_min', instmap)
                                  | _ => None
                                  end
                    | Some (ft, _) => match e with
                            | Eref ref => match ref2pv_mod ref mv instmap tmap, type_of_ref ref mod_tmap with
                                        | Some pvar, Some ft_ref => 
                                          let nmap := extract_constraint_passive ft ft_ref pv_node pvar c1map in 
                                          Some (nmap, cs2, cs_min, instmap)
                                        | _, _ => None
                                        end
                            | Emux c e0 e1 => match extract_mux_mod mv instmap e tmap with
                                        | Some (rhsl, cs2') => 
                                            let nmap := fold_left (fun temp_map ref0 => 
                                                        match ref2pv_mod ref0 mv instmap tmap, type_of_ref ref0 mod_tmap with
                                                        | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref pv_node pvar temp_map
                                                        | _, _ => temp_map
                                                        end) rhsl c1map in Some (nmap, cs2 ++ cs2', cs_min, instmap)
                                        | _ => None
                                        end
                            | _ => None
                            end
                    | _ => None
                    end
                | _ => None
                end
  | Smem _ _ 
  | Sinvalid _ 
  | Swire _ _ 
  | Sskip => Some (c1map, cs2, cs_min, instmap)
  | Swhen c ss_true ss_false => match extract_constraint_expr_mod mv c tmap instmap with
                | Some (ce0, ce1) => match extract_constraint_ss mv ss_true tmap c1map (cs2 ++ ce0 ++ ce1) cs_min instmap with
                    | Some (c1map', cs2', cs_min', instmap') => extract_constraint_ss mv ss_false tmap c1map' cs2' cs_min' instmap'
                    | _ => None
                    end
                | _ => None
                end
  end
| _ => None
end.

Fixpoint extract_constraint_ml ml (tmap : VM.t (VM.t (ftype * forient))) (c1map : PVM.t (list Constraint1)) (cs2 : list min_rhs) 
  (cs_min : list Constraint_Min) : option (PVM.t (list Constraint1) * list min_rhs * list Constraint_Min) :=
  match ml with
  | nil => Some (c1map, cs2, cs_min)
  | FInmod mv _ ss :: tl => match extract_constraint_ss mv ss tmap c1map cs2 cs_min (VM.empty VM.key) with
      | Some (c1map', cs2', cs_min', _) => extract_constraint_ml tl tmap c1map' cs2' cs_min'
      | _ => None
      end
  | _ :: tl => extract_constraint_ml tl tmap c1map cs2 cs_min
  end.

Definition extract_constraints_c (c : hfcircuit) (tmap : VM.t (VM.t (ftype * forient))) : option (list (PVM.t (list Constraint1)) * list min_rhs) :=
  match c with
  | Fcircuit _ ml => match extract_constraint_ml ml tmap (PVM.empty (list Constraint1)) nil nil with
                    | Some (c1map, cs2, cs_min) => let group_of_mins := map list_Constraint_Min cs_min in
                      let group_of_cs1 := cartesian_product group_of_mins in
                      match group_of_cs1 with
                      | nil => Some ([c1map], cs2) (* 不存在min *)
                      | _ => Some (map (fun new_cs1 => add_cs1_2_c1map new_cs1 c1map) group_of_cs1, cs2)
                      end
                    | _ => None
                    end
  end.



Fixpoint update_tmap (tmap : VM.t (VM.t (ftype * forient))) (new_widths : list (ProdVar.t * nat)) : option (VM.t (VM.t (ftype * forient))) :=
  match new_widths with
  | nil => Some tmap
  | (pv, w) :: tl => match VM.find pv.1 tmap with (* 找到对应moule的tmap *)
                    | Some mod_tmap => let pvar := cantor_unpairing (N.to_nat pv.2) in 
                        match VM.find (N.of_nat pvar.1) mod_tmap with
                        | Some (ft, ori) => match update_ftype pvar.2 w ft with 
                                | Some nft => update_tmap (VM.add pv.1 (VM.add (N.of_nat pvar.1) (nft, ori) mod_tmap) tmap) tl
                                | _ => None
                                end
                        | _ => None
                        end
                    | _ => None
                    end
  end.

Definition InferWidths_trans_m m (tmap : VM.t (VM.t (ftype * forient))) : option hfmodule :=
  match m with
  | FInmod mv ps ss => match VM.find mv tmap with
          | Some mod_tmap => match InferWidths_transps ps mod_tmap, InferWidths_transss ss mod_tmap with
                  | Some nps, Some nss => Some (FInmod mv nps nss)
                  | _, _ => None
                  end
          | _ => None
          end
  | FExmod _ _ _ => Some m 
  end.

Fixpoint InferWidths_trans_ml ml (tmap : VM.t (VM.t (ftype * forient))) : option (seq hfmodule) :=
  match ml with
  | nil => Some nil
  | hd :: tl => match InferWidths_trans_m hd tmap, InferWidths_trans_ml tl tmap with
      | Some nhd, Some ntl => Some (nhd :: ntl)
      | _, _ => None
      end
  end.

Definition InferWidths_trans_c c (tmap : VM.t (VM.t (ftype * forient))) : option hfcircuit :=
  match c with
  | Fcircuit c ml => match InferWidths_trans_ml ml tmap with
      | Some nml => Some (Fcircuit c nml)
      | _ => None
      end
  end.


Fixpoint pl2btyp (pl : seq hfport) : ffield := 
  match pl with
  | nil => Fnil
  | Finput v t :: tl => Fflips v Nflip t (pl2btyp tl)
  | Foutput v t :: tl => Fflips v Flipped t (pl2btyp tl)
  end.

(* functions used to record ftype and component type *)
Fixpoint stmts_tmap (modplmap : VM.t (seq hfport)) (tmap : VM.t (ftype * forient)) (ss : hfstmt_seq): option (VM.t (ftype * forient)) :=
  match ss with
  | Qnil => Some tmap
  | Qcons s ss' => match stmt_tmap modplmap tmap s with
      | Some tmap' => stmts_tmap modplmap tmap' ss'
      | None => None
      end
  end
with stmt_tmap (modplmap : VM.t (seq hfport)) (tmap : VM.t (ftype * forient)) (s : hfstmt) : option (VM.t (ftype * forient)) :=
  match s with
  | Sskip => Some tmap
  | Sfcnct _ _ => Some tmap
  | Sinvalid _ => Some tmap
  | Smem v m => Some (VM.add v (data_type m, Duplex) tmap)
  | Sinst v mv => match VM.find mv modplmap with
      | Some pl => let t := Btyp (pl2btyp pl) in
                  Some (VM.add v (t, Duplex) tmap)
      | _ => None
      end
  | Swire v t => match VM.find v tmap with
      | None => Some (VM.add v (t, Duplex) tmap)
      | _ => None
      end
  | Sreg v reg => match VM.find v tmap, type_of_hfexpr (clock reg) tmap with
      | None, Some _ => Some (VM.add v ((type reg), Duplex) tmap)
      | _, _ => None
      end
  | Snode v expr => match VM.find v tmap, type_of_hfexpr expr tmap with
                  | None, Some (exist newt _) => Some (VM.add v (make_ftype_implicit newt, Source) tmap)
                  | _, _ => None
                  end
  | Swhen cond ss_true ss_false =>
      match type_of_hfexpr cond tmap, stmts_tmap modplmap tmap ss_true with
      | Some (exist (Gtyp (Fuint 1)) _), Some tmap_true => stmts_tmap modplmap tmap_true ss_false 
      | _, _ => None
      end
  end.

Fixpoint modules_tmap (modplmap : VM.t (seq hfport)) (tmap : VM.t (VM.t (ftype * forient))) (ml : seq hfmodule) : option (VM.t (VM.t (ftype * forient))) :=
  match ml with
  | nil => Some tmap
  | FInmod mv ps ss :: tl => match ports_tmap' (VM.empty (ftype * forient)) ps with
              | Some pmap => match stmts_tmap modplmap pmap ss with
                  | Some tmap' => modules_tmap modplmap (VM.add mv tmap' tmap) tl
                  | None => None
                  end
              | None => None
              end 
  | _ :: tl => modules_tmap modplmap tmap tl
  end.

Definition circuit_tmap (c : hfcircuit) : option (VM.t (VM.t (ftype * forient))) :=
  match c with
  | Fcircuit v ml => let modplmap := List.fold_left (fun acc m => 
      match m with
      | FInmod mv ps _ => VM.add mv ps acc
      | FExmod mv ps _ => VM.add mv ps acc
      end) ml (VM.empty (seq hfport)) in
    modules_tmap modplmap (VM.empty (VM.t (ftype * forient))) ml
  end.

End Extract_Constraints_for_multimod.
