From HB Require Import structures.
From Coq Require Import ZArith Arith List Ascii String Lia FMaps.
From mathcomp Require Import all_ssreflect.
From Solver Require Import Env LoFirrtl HiEnv HiFirrtl constraints extract_cs.
Import ListNotations.

Section Extract_Constraints_with_min.

Record regular_rhs : Type := {
  regular_const : Z.t;(* 右侧常数项 *)
  regular_terms : list (nat * ProdVar.t); (* 右侧线性组合项，列表形式 (系数, 变量) *)
  regular_power : list (nat * ProdVar.t) (* 右侧2的幂项 *)
}.

Definition make_rhs a b c : regular_rhs :=
  {|regular_const := c;
    regular_terms := a;
    regular_power := b|}.

Definition split_rhs a : list term * list term * Z.t :=
  (regular_terms a, regular_power a, regular_const a).

(*Definition a : regular_rhs := make_rhs nil nil 0%Z.*)

Inductive min_rhs : Type :=
  | Expr : regular_rhs -> min_rhs
  | Min : min_rhs -> min_rhs -> min_rhs.

Fixpoint min_rhs_value (v : Valuation) (rhs : min_rhs) : Z.t :=
  match rhs with
  | Expr r => terms_value v (regular_terms r) (regular_const r) + power_value v (regular_power r)
  | Min e1 e2 => Z.min (min_rhs_value v e1) (min_rhs_value v e2)
  end.
  
(* inequality of form: lhs_ >= min(fr1_ + const1_, fr2_ + const2_)
This is introduced to indicate the "rem" operation
  e.g. z <= rem(x,y) indicates lhs_(w_z), fr1_(w_x), const1_(0), fr2_(w_y),
  const2_(0)
The use of "const" here is to take into account the case where the expression
is a constant. However, it is not actually utilized because in MLIR,
constants are also declared with variable names. *)
Record Constraint_Min : Type := {
  lhs_var_min : ProdVar.t;
  rhs_expr_min : min_rhs
}.

Definition default_min : min_rhs := Expr {|regular_const := 0%Z;
  regular_terms := nil;
  regular_power := nil|}.

Fixpoint add_pairs {A B : Type} (x : A) (ys : list B) (acc : list (A * B)) : list (A * B) :=
  match ys with
  | nil => acc
  | y :: ys' => add_pairs x ys' ((x, y) :: acc)
  end.

Fixpoint cartesian_tail {A B : Type} (xs : list A) (ys : list B) (acc : list (A * B)) : list (A * B) :=
  match xs with
  | nil => rev acc
  | x :: xs' => cartesian_tail xs' ys (add_pairs x ys acc)
  end.

Definition cartesian {A B : Type} (xs : list A) (ys : list B) : list (A * B) :=
  cartesian_tail xs ys [].

Fixpoint min_rhs_add_cst (temp_e : min_rhs) (cst : Z.t) :=
  match temp_e with
  | Expr e => Expr (make_rhs (regular_terms e) (regular_power e) (Z.add (regular_const e) cst))
  | Min e1 e2 => Min (min_rhs_add_cst e1 cst) (min_rhs_add_cst e2 cst)
  end.

Fixpoint min_rhs_add_power (temp_e : min_rhs) (pv : ProdVar.t) :=
  match temp_e with
  | Expr e => Expr (make_rhs (regular_terms e) [(1, pv)] (Z.sub (regular_const e) 1%Z))
  | Min e1 e2 => Min (min_rhs_add_power e1 pv) (min_rhs_add_power e2 pv)
  end.

Fixpoint list_min_rhs (temp_e : min_rhs) res : list regular_rhs :=
  match temp_e with
  | Expr e => e :: res
  | Min e1 e2 => list_min_rhs e2 (list_min_rhs e1 res)
  end.

Definition min2cs2 (minl : list min_rhs) : list Constraint2_new :=
  let el := flat_map (fun min => list_min_rhs min nil) minl in
  map (fun e => {|
    lhs_const2_new := Z.sub 1%Z (regular_const e);
    rhs_terms2_new := regular_terms e;
    rhs_power2_new := regular_power e
  |}) el.

Fixpoint regulars2min (el : list regular_rhs) : min_rhs :=
  match el with
  | nil => default_min
  | [hd] => Expr hd
  | hd :: tl => Min (Expr hd) (regulars2min tl)
  end.

Definition combine_min_rhs (e1 e2 : min_rhs) : min_rhs :=
  let el1 := list_min_rhs e1 [] in
  let el2 := list_min_rhs e2 [] in
  let nel := map (fun '(temp_e1, temp_e2) => let '(a, b, c) := combine_terms (split_rhs temp_e1) (split_rhs temp_e2) in
                                  make_rhs a b c) (cartesian el1 el2) in 
  regulars2min nel.

Fixpoint extract_constraint_expr (e : hfexpr) (tmap : VM.t (ftype * forient)) : option ((list min_rhs) * (list min_rhs)) :=
  (* min_rhs 的 Expr case 是一条phi1约束的一次项，指数项和常数项。rem产生min_rhs 中的 Min case
     mux 直接生成 list of min_rhs
     constraint2 来自 mux的condition*)
  match e with
  | Eref r => match type_of_ref r tmap, ref2pv r tmap with
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
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                            extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                    | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                    | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                      Some (map (fun '(a,b) => Min a b) (cartesian el1 el2), cs1 ++ cs2)
                    | _, _, _, _ => None 
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
                            | Some (exist (Gtyp _) _), Some (_, cs) => Some ([Expr (make_rhs nil nil 1%Z)], cs)
                            | _, _ => None
                            end
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => Some (Expr (make_rhs nil nil (Z.of_nat n)) :: el, cs)
                            | _, _ => None
                            end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs) 
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.of_nat n)) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs) => 
                              let nexp := map (fun temp_e => min_rhs_add_cst temp_e (Z.opp (Z.of_nat n))) el in
                                Some (Expr (make_rhs nil nil 1%Z) :: nexp, cs) 
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => 
                                Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.opp (Z.of_nat n))) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (el, cs) => Some (el, cs)
                            | Some (exist (Gtyp (Fuint _)) _), Some (el, cs) => 
                                Some (map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop Uneg e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (el, cs) 
                            | Some (exist (Gtyp (Fuint _)) _), Some (el, cs) => 
                                Some (map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => (*if (n2 <= n1) && (n1 < w) then *)
                                Some ([Expr (make_rhs nil nil (Z.of_nat (n1 - n2 + 1)))], cs) (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => (*if n <= w then *)
                                Some ([Expr (make_rhs nil nil (Z.of_nat n))], cs) (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => (*if n <= w then *)
                                Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.opp (Z.of_nat n))) el, cs)
                              (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop _ e1 => match type_of_hfexpr e1 tmap, extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint _)) _), Some (el, cs) => 
                              Some ([Expr (make_rhs nil nil 1%Z)], cs)
                            | _, _ => None
                            end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _), Some (el1, cs1), Some (el2, cs2)
                            | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _), Some (el1, cs1), Some (el2, cs2) => 
                                Some ([Expr (make_rhs nil nil 1%Z)], cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                                let nexp1 := map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el1 in
                                let nexp2 := map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el2 in
                                Some (nexp1 ++ nexp2, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (map (fun '(e1, e2) => combine_min_rhs e1 e2) (cartesian el1 el2), cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1, cs1 ++ cs2)
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.opp 1%Z)) el1, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1) =>
                                match e2 with
                                | Eref r => match type_of_ref r tmap, ref2pv r tmap with
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
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2)
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                                Some (map (fun '(e1, e2) => combine_min_rhs e1 e2) (cartesian el1 el2), cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1 ++ el2, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Emux c e1 e2 => match type_of_hfexpr c tmap, extract_constraint_expr c tmap,
                                    extract_constraint_expr e1 tmap, extract_constraint_expr e2 tmap with
                            | Some (exist (Gtyp (Fuint _)) _), Some (ec, cs0), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1 ++ el2, ec ++ cs0 ++ cs1 ++ cs2)
                            | _, _, _, _ => None
                            end (* condition c 只能是 0/1位宽 *)
end.

(*Compute (combine_terms ([(1,(1%num,0%num))], 4%Z) ([(1,(1%num,0%num))], 0%Z)).
Compute (flat_map (fun x => map (combine_terms x) [([(1,(1%num,0%num))], 4%Z)]) [([(1,(1%num,0%num))], 0%Z)]).*)

Fixpoint expand_mux (e : hfexpr) (tmap : VM.t (ftype * forient)) : option (list href * list min_rhs) := 
  (* 同时记录mux的condition产生的约束 *)
  match e with
  | Eref r => Some ([r], nil)
  | Emux c e1 e2 => match type_of_hfexpr c tmap, extract_constraint_expr c tmap, 
                          expand_mux e1 tmap, expand_mux e2 tmap with
                  | Some (exist (Gtyp (Fuint _)) _), Some (ec, cs0), Some (r1, cs1), Some (r2, cs2) => 
                    Some (r1 ++ r2, ec ++ cs0 ++ cs1 ++ cs2)
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

Fixpoint extract_constraint_non_passive (ft ft_ref : ftype) (flip : bool) (pv pvar : ProdVar.t) (c1map : PVM.t (list Constraint1)): PVM.t (list Constraint1) :=
  match ft, ft_ref with 
  | Gtyp (Fuint_implicit _), Gtyp (Fuint_implicit _)
  | Gtyp (Fsint_implicit _), Gtyp (Fsint_implicit _) => if flip == false then
                                let nc := {|
                                 lhs_var1 := pv;
                                 rhs_power := nil;
                                 rhs_const1 := 0;
                                 rhs_terms1 := [(1, pvar)]
                               |} in
                               match PVM.find pv c1map with
                               | Some cs1 => PVM.add pv (nc :: cs1) c1map
                               | _ => PVM.add pv [nc] c1map
                               end else 
                               let nc := {|
                                 lhs_var1 := pvar;
                                 rhs_power := nil;
                                 rhs_const1 := 0;
                                 rhs_terms1 := [(1, pv)]
                               |} in
                               match PVM.find pvar c1map with
                               | Some cs1 => PVM.add pvar (nc :: cs1) c1map
                               | _ => PVM.add pvar [nc] c1map
                               end
  | Gtyp (Fuint_implicit _), Gtyp (Fuint w)
  | Gtyp (Fsint_implicit _), Gtyp (Fsint w) => if flip == false then
                                let nc := {|
                                 lhs_var1 := pv;
                                 rhs_const1 := Z.of_nat w;
                                 rhs_power := nil;
                                 rhs_terms1 := []
                               |} in
                               match PVM.find pv c1map with
                               | Some cs1 => PVM.add pv (nc :: cs1) c1map
                               | _ => PVM.add pv [nc] c1map
                               end else c1map
  | Gtyp (Fuint w), Gtyp (Fuint_implicit _)
  | Gtyp (Fsint w), Gtyp (Fsint_implicit _) => if flip == false then c1map else
                                let nc := {|
                                 lhs_var1 := pvar;
                                 rhs_const1 := Z.of_nat w;
                                 rhs_power := nil;
                                 rhs_terms1 := []
                               |} in
                               match PVM.find pvar c1map with
                               | Some cs1 => PVM.add pvar (nc :: cs1) c1map
                               | _ => PVM.add pvar [nc] c1map
                               end
  | Atyp atyp _, Atyp atyp_ref _ => extract_constraint_non_passive atyp atyp_ref flip pv pvar c1map
  | Btyp ff, Btyp ff_ref => extract_constraint_non_passive_f ff ff_ref flip pv pvar c1map
  | _, _ => c1map
  end
with extract_constraint_non_passive_f (ff ff_ref : ffield) (flip : bool) (pv pvar : ProdVar.t) (c1map : PVM.t (list Constraint1)) : PVM.t (list Constraint1) :=
  match ff, ff_ref with
  | Fnil, Fnil => c1map
  | Fflips _ Nflip t fs, Fflips _ Nflip t_ref fs_ref => let nmap := extract_constraint_non_passive t t_ref flip pv pvar c1map in 
                           extract_constraint_non_passive_f fs fs_ref flip (pv.1, N.add pv.2 (N.of_nat (size_of_ftype t))) (pvar.1, N.add pvar.2 (N.of_nat (size_of_ftype t))) nmap
  | Fflips _ Flipped t fs, Fflips _ Flipped t_ref fs_ref => let nmap := extract_constraint_non_passive t t_ref (~~flip) pv pvar c1map in
                           extract_constraint_non_passive_f fs fs_ref flip (pv.1, N.add pv.2 (N.of_nat (size_of_ftype t))) (pvar.1, N.add pvar.2 (N.of_nat (size_of_ftype t))) nmap
  | _, _ => c1map
  end.

Fixpoint seperate_min (pv : ProdVar.t) (el : list min_rhs) (res : list Constraint1 * list Constraint_Min) : list Constraint1 * list Constraint_Min :=
  match el with
  | nil => res
  | Expr e :: tl => let '(a, b, c) := split_rhs e in
                    let nc := {|
                      lhs_var1 := pv;
                      rhs_const1 := c;
                      rhs_power := b;
                      rhs_terms1 := a
                    |} in
                    seperate_min pv tl (nc :: res.1, res.2)
  | hd :: tl => let nc := {|
                      lhs_var_min := pv;
                      rhs_expr_min := hd
                    |} in
                    seperate_min pv tl (res.1, nc :: res.2)
  end.

Definition extract_constraint (s : hfstmt) (tmap : VM.t (ftype * forient)) (c1map : PVM.t (list Constraint1)) (res2 : list min_rhs) (resmin : list Constraint_Min) : option (PVM.t (list Constraint1) * list min_rhs * list Constraint_Min) :=
  match s with
  | Sfcnct r expr => match type_of_ref r tmap with
                    | Some (Gtyp gt) => if not_implicit gt then Some (c1map, res2, resmin)
                        else match ref2pv r tmap, extract_constraint_expr expr tmap with
                            | Some pv, Some (exprs, cs2) =>
                              let (regular_cs, min_cs) := seperate_min pv exprs (nil, nil) in
                              let nmap := match PVM.find pv c1map with
                                | Some cs1 => PVM.add pv (regular_cs ++ cs1) c1map
                                | _ => PVM.add pv regular_cs c1map
                                end
                              in Some (nmap, cs2 ++ res2, min_cs ++ resmin)
                            | _, _ => None
                            end
                    | Some ft => match expr with
                            | Eref ref => match ref2pv r tmap, ref2pv ref tmap, type_of_ref ref tmap with
                                        | Some pv, Some pvar, Some ft_ref => let nmap := extract_constraint_non_passive ft ft_ref false pv pvar c1map in Some (nmap, res2, resmin)
                                        | _, _, _ => None
                                        end
                            | Emux c e0 e1 => match ref2pv r tmap, expand_mux expr tmap with
                                        | Some pv, Some (rhsl, cs2) => 
                                            let nmap := fold_left (fun temp_map ref0 => 
                                                match ref2pv ref0 tmap, type_of_ref ref0 tmap with
                                                | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref pv pvar temp_map
                                                | _, _ => temp_map
                                                end) rhsl c1map in Some (nmap, cs2 ++ res2, resmin)
                                        | _, _ => None
                                        end
                            | _ => None
                            end
                    | _ => None
                    end

  | Sreg v reg => match type reg with
                | Gtyp gt => if not_implicit gt then Some (c1map, res2, resmin)
                    else match reset reg with
                    | NRst => Some (c1map, res2, resmin)
                    | Rst _ rst_val => match extract_constraint_expr rst_val tmap with
                                      | Some (exprs, cs2) => 
                                        let (regular_cs, min_cs) := seperate_min (v, N0) exprs (nil, nil) in
                                        let nmap := match PVM.find (v, N0) c1map with
                                          | Some cs1 => PVM.add (v, N0) (regular_cs ++ cs1) c1map
                                          | _ => PVM.add (v, N0) regular_cs c1map
                                          end
                                        in Some (nmap, cs2 ++ res2, min_cs ++ resmin)
                                      | _ => None
                                      end
                    end
                | ft => (* reg 只能passive *)
                        match reset reg with
                        | NRst => Some (c1map, res2, resmin)
                        | Rst _ rst_val => match rst_val with
                                      | Eref ref => match ref2pv ref tmap, type_of_ref ref tmap with
                                                  | Some pvar, Some ft_ref => let nmap := extract_constraint_passive ft ft_ref (v, N0) pvar c1map in Some (nmap, res2, resmin)
                                                  | _, _ => None
                                                  end
                                      | Emux c e0 e1 => match expand_mux rst_val tmap with
                                                  | Some (rhsl, cs2) => 
                                                      let nmap := fold_left (fun temp_map ref0 => 
                                                          match ref2pv ref0 tmap, type_of_ref ref0 tmap with
                                                          | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref (v, N0) pvar temp_map
                                                          | _, _ => temp_map
                                                          end) rhsl c1map in Some (nmap, cs2 ++ res2, resmin)
                                                  | _ => None
                                                  end
                                      | _ => None
                                      end
                        end
                end
  | Snode v e => match type_of_ref (Eid v) tmap with
                | Some (Gtyp gt) => match extract_constraint_expr e tmap with
                                  | Some (exprs, cs2) => 
                                      let (regular_cs, min_cs) := seperate_min (v, N0) exprs (nil, nil) in
                                      let nmap := match PVM.find (v, N0) c1map with
                                        | Some cs1 => PVM.add (v, N0) (regular_cs ++ cs1) c1map
                                        | _ => PVM.add (v, N0) regular_cs c1map
                                        end
                                      in Some (nmap, cs2 ++ res2, min_cs ++ resmin)
                                  | _ => None
                                  end
                | Some ft => match e with
                            | Eref ref => match ref2pv ref tmap, type_of_ref ref tmap with
                                        | Some pvar, Some ft_ref => let nmap := extract_constraint_passive ft ft_ref (v, N0) pvar c1map in Some (nmap, res2, resmin)
                                        | _, _ => None
                                        end
                            | Emux c e0 e1 => match expand_mux e tmap with
                                        | Some (rhsl, cs2) => 
                                            let nmap := fold_left (fun temp_map ref0 => 
                                                        match ref2pv ref0 tmap, type_of_ref ref0 tmap with
                                                        | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref (v, N0) pvar temp_map
                                                        | _, _ => temp_map
                                                        end) rhsl c1map in Some (nmap, cs2 ++ res2, resmin)
                                        | _ => None
                                        end
                            | _ => None
                            end
                | _ => None
                end
  | Smem _ _ 
  | Sinst _ _ 
  | Sinvalid _ 
  | Swire _ _ 
  | Sskip => Some (c1map, res2, resmin)
  | Swhen _ _ _ => None
  end.

Fixpoint extract_constraints (ss : hfstmt_seq) (tmap : VM.t (ftype * forient)) (c1map : PVM.t (list Constraint1)) (res2 : list min_rhs) (resmin : list Constraint_Min) : option (PVM.t (list Constraint1) * list min_rhs * list Constraint_Min) :=
  match ss with
  | Qnil => Some (c1map, res2, resmin)
  | Qcons s st => 
    match extract_constraint s tmap c1map res2 resmin with
    | Some (nmap, cs2, csmin) => extract_constraints st tmap nmap cs2 csmin
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

Fixpoint make_cs2 (el : list hfexpr) (tmap : VM.t (ftype * forient)) res : option (list min_rhs) :=
  match el with
  | nil => Some res
  | hd :: tl => match extract_constraint_expr hd tmap with
              | Some (a, b) => make_cs2 tl tmap (res ++ a ++ b)
              | _ => None
              end
  end.

Definition extract_constraint_m (m : hfmodule) (tmap : VM.t (ftype * forient)) : option (PVM.t (list Constraint1) * list min_rhs * list Constraint_Min) :=
  match m with
  | FInmod _ _ ss => let (ss', conds) := expandwhens ss (Qnil, []) in
                     match extract_constraints ss' tmap (PVM.empty (list Constraint1)) nil nil, make_cs2 conds tmap nil with
                     | Some (c1map, cs2, cs_min), Some cs2' => Some (c1map, cs2 ++ cs2', cs_min)
                     | _, _ => None
                     end
  | _ => None
  end.

Definition list_Constraint_Min (minc : Constraint_Min) : list Constraint1 :=
  let rhs_ls := list_min_rhs (rhs_expr_min minc) nil in
  map (fun r => let '(a,b,c) := split_rhs r in
                {|lhs_var1 := lhs_var_min minc;
                  rhs_terms1 := a;
                  rhs_power := b;
                  rhs_const1 := c|}) rhs_ls.

Fixpoint cartesian_product {A : Type} (l : list (list A)) : list (list A) :=
  match l with
  | [] => [[]]  (* 空列表的笛卡尔积是包含一个空列表的列表 *)
  | x :: xs =>
      let cp := cartesian_product xs in
      flat_map (fun a => map (fun b => a :: b) cp) x
  end.

Fixpoint add_cs1_2_c1map (cs : list Constraint1) (c1map : PVM.t (list Constraint1)) : PVM.t (list Constraint1) :=
  match cs with
  | nil => c1map
  | hd :: tl => let nmap := match PVM.find (lhs_var1 hd) c1map with
                            | Some cs1 => PVM.add (lhs_var1 hd) (hd :: cs1) c1map
                            | _ => PVM.add (lhs_var1 hd) [hd] c1map
                            end
                          in add_cs1_2_c1map tl nmap
  end.

Definition extract_constraints_c (c : hfcircuit) (tmap : (VM.t (ftype * forient))) : option (list (PVM.t (list Constraint1)) * list min_rhs) :=
  match c with
  | Fcircuit _ [m] => match extract_constraint_m m tmap with
                    | Some (c1map, cs2, cs_min) => let group_of_mins := map list_Constraint_Min cs_min in
                      let group_of_cs1 := cartesian_product group_of_mins in
                      match group_of_cs1 with
                      | nil => Some ([c1map], cs2) (* 不存在min *)
                      | _ => Some (map (fun new_cs1 => add_cs1_2_c1map new_cs1 c1map) group_of_cs1, cs2)
                      end
                    | _ => None
                    end
  | _ => None
  end.

Definition collect_power1_vars (c : Constraint1) : list ProdVar.t :=
  if (rhs_power c) == nil then nil else (lhs_var1 c) :: (List.split (rhs_power c)).2.
Definition collect_power2_vars (c : Constraint2_new) : list ProdVar.t :=
  if (rhs_power2_new c) == nil then nil else (List.split (rhs_power2_new c)).2.
  
Definition remove_power_regular (value : Valuation) (r : regular_rhs) : regular_rhs :=
  {|
    regular_terms := regular_terms r;
    regular_power := nil;
    regular_const := Z.add (regular_const r) (power_value value (regular_power r))
  |}.

Definition remove_power1 (value : Valuation) (c : Constraint1) : Constraint1 :=
  {|
    lhs_var1 := lhs_var1 c;
    rhs_terms1 := rhs_terms1 c;
    rhs_power := nil;
    rhs_const1 := Z.add (rhs_const1 c) (power_value value (rhs_power c))
  |}.

Definition remove_power2 (value : Valuation) (c : Constraint2_new) : Constraint2_new :=
  {|
    lhs_const2_new := Z.sub (lhs_const2_new c) (power_value value (rhs_power2_new c));
    rhs_terms2_new := rhs_terms2_new c;
    rhs_power2_new := nil
  |}.

Fixpoint remove_power_min_rhs (value : Valuation) (rhs : min_rhs) : min_rhs :=
  match rhs with
  | Expr r => Expr (remove_power_regular value r)
  | Min min1 min2 => Min (remove_power_min_rhs value min1) (remove_power_min_rhs value min2)
  end.

Definition remove_power_min (value : Valuation) (c : Constraint_Min) : Constraint_Min :=
  {|
    lhs_var_min := lhs_var_min c;
    rhs_expr_min := remove_power_min_rhs value (rhs_expr_min c)
  |}.

End Extract_Constraints_with_min.