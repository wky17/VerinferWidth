From mathcomp Require Import all_ssreflect.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From Solver Require Import Env LoFirrtl HiEnv HiFirrtl constraints graph.
Require Import Coq.Bool.Bool.
From Coq Require Import ZArith Arith List Ascii String Lia FMaps.
Import ListNotations.
(* Import recursive definitions *)
(* From Equations Require Import Equations. *)

Set Implicit Arguments.
(*Unset Strict Implicit.*) 
Import Prenex Implicits.

(* ------------ solve sccs ------------ *)

Section scc.

Definition substitute_constraint (c : Constraint1) (v : ProdVar.t) (terms : list (nat * ProdVar.t)) (cst : Z.t) : Constraint1 :=
  match find (fun p : term => snd p == v) (rhs_terms1 c) with
  | Some (coe, _) =>
    let new_terms := 
        fold_right (fun '(coe', var) (acc : list term) =>
            (* 检查 acc 是否已经包含 var *)
            match find (fun p : term => snd p == var) acc with
            | None => (coe * coe', var) :: acc  (* 添加新的项 *)
            | Some (existing_coef, _) =>
                (* 合并项 *)
                (existing_coef + coe * coe', var) :: (List.remove term_dec (existing_coef, var) acc)
            end
        ) (List.remove term_dec (coe, v) (rhs_terms1 c)) terms in
      (* 返回替换的约束 *)
      {| lhs_var1 := lhs_var1 c;
        rhs_const1 := Z.add (rhs_const1 c) ((Z.of_nat coe) * cst);
        rhs_power := nil;
        rhs_terms1 := new_terms |}
  | None => c
  end.

Definition preprocess_tbreplace1 (hd : ProdVar.t) (cs_hd : list Constraint1) : list Constraint1 :=
  (* 处理第一种情况 存在某条 不等式右侧只有hd 的约束 *)
  match find (fun c => (List.length (rhs_terms1 c) == 1) &&
                      ((List.hd (0,(N0,N0)) (rhs_terms1 c)).2 == hd)) cs_hd with
  | Some temp_c => match rhs_terms1 temp_c with
    | [(1, hd)] => if (Z.leb (rhs_const1 temp_c) 0) then cs_hd else nil
    | [(n, hd)] => if n > 1 then 
                     map (fun c => substitute_constraint temp_c hd (rhs_terms1 c) (rhs_const1 c)) cs_hd
                     else nil
    | _ => nil
    end
  | _ => cs_hd
  end.
  
Definition preprocess_tbreplace2 (hd : ProdVar.t) (cs_hd : list Constraint1) : list Constraint1 :=
  (* 检查是否特殊情况: 不等式右边有x, 并且除x外有其他项 *)
  match find (fun c => (List.length (rhs_terms1 c) > 1) &&
                      (in_bool hd (List.split (rhs_terms1 c)).2)) cs_hd with
  | Some temp_c => let new_c := substitute_constraint temp_c hd (rhs_terms1 temp_c) (rhs_const1 temp_c) in
                    new_c :: cs_hd
  | _ => cs_hd
  end.

Definition preprocess_tbreplace (hd : ProdVar.t) (cs_hd : list Constraint1) : list Constraint1 :=
  preprocess_tbreplace2 hd (preprocess_tbreplace1 hd cs_hd).

Fixpoint substitute_vs (vl : list ProdVar.t) (constraints : list Constraint1) : list Constraint1 :=
  match vl with
  | [] => constraints
  (*| [:: hd] => (* 处理特殊情况 *)
    let cs_hd := find_constraint1s hd constraints in
    let cs_tl := filter (fun c => (hd != (lhs_var1 c))) constraints in
    let ncs := flat_map (fun c => 
      map (fun temp_c => substitute_constraint temp_c hd (rhs_terms1 c) (rhs_const1 c)) cs_tl 
      ) cs_hd in
      (* 若替换后的约束，存在rhs中，lhs的系数大于1，则代入结束 *)
    if (existsb (fun c => match find (fun p : term => snd p == (lhs_var1 c)) (rhs_terms1 c) with
                        | Some (coe,_) => coe > 1
                        | _ => false
                        end) ncs) then ncs
    else (* 未解出上界，则再带入一次hd *)
    flat_map (fun c => 
      map (fun temp_c => substitute_constraint temp_c hd (rhs_terms1 c) (rhs_const1 c)) ncs
      ) cs_hd*)
  | hd :: tl => (* 用所有lhs为hd约束，消去所有约束中rhs中的hd *)
    let (cs_hd, cs_tl) := List.partition (fun c => (hd == (lhs_var1 c))) constraints in

(* 在这里添加一步对将要消去的 hd 的相关约束的操作
1、对存在形如: x >= 2x + cst, 是 不等式右侧只有x, 并且其系数大于1
  一定存在其他 x >= x' + cst' 的约束，先用 x' + cst' 去替换 2x + cst 中的 x，得到新的一系列约束。
  作为后续带入的 x >= ...
2、对存在形如: x >= x + x' + cst, 是 不等式右边有x, 并且除x外只有一项, 且这项的系数为1
  用其自身带入rhs的x，得到这条预处理后的约束 *)

    let cs_hd' := preprocess_tbreplace hd cs_hd in
    let ncs := flat_map (fun c => 
        map (fun temp_c => substitute_constraint temp_c hd (rhs_terms1 c) (rhs_const1 c)) cs_tl 
        (* 用c的rhs替换constraints中的所有hd，并合并化简 *)
        ) cs_hd' in
      substitute_vs tl ncs
end.

(*Definition c0 : Constraint1 :=
  {|
    lhs_var1 := (2%num, N0);
    rhs_const1 := 2;
    rhs_terms1 := [(1, (4%num, N0))];
    rhs_power := []
  |}.

Definition c1 : Constraint1 :=
  {|
    lhs_var1 := (2%num, N0);
    rhs_const1 := -1;
    rhs_terms1 := [(1, (4%num, N0)); (1, (2%num, N0))];
    rhs_power := []
  |}.
Definition hd := (4%num, N0).
Definition term_hd := [(1, (4%num, N0)); (1, (2%num, N0))].
Definition cst := (-3)%Z.

Definition subed_c0 := substitute_constraint c1 hd term_hd cst. 

Definition c2 : Constraint1 :=
  {|
    lhs_var1 := hd;
    rhs_const1 := cst;
    rhs_terms1 := term_hd;
    rhs_power := []
  |}.
Definition subed_c1 := substitute_vs [hd] [c0;c2]. *)

Definition solve_ub (v : ProdVar.t) (scc : list ProdVar.t) (constraints : list Constraint1) : option Z.t :=
  let vl := filter (fun (p : ProdVar.t) => p != v) scc in 
  let res := substitute_vs vl constraints in (* 依次消掉constraints中的其他变量 *)
  (* 如果有常数项大于0则无解 *)
  if (existsb (fun (c : Constraint1) => Z.gtb (rhs_const1 c) 0%Z) res) then None
  else fold_left (fun (ub : option Z.t) (c : Constraint1) => 
    match find (fun (p : term) => snd p == v) (rhs_terms1 c), ub with
    | None, _ => ub
    | Some (1, _), _ => ub
    | Some (coe, _), None => Some (Z.add (Z.div (Z.abs (rhs_const1 c)) (Z.of_nat (coe - 1))) 1)
    | Some (coe, _), Some n => Some (Z.min n (Z.add (Z.div (Z.abs (rhs_const1 c)) (Z.of_nat (coe - 1))) 1))
    end) res None.

Fixpoint solve_ubs (ls scc : list ProdVar.t) (constraints : list Constraint1) : option Valuation :=
  match ls with
  | [] => Some (initial_valuation)
  | hd :: tl => match solve_ub hd scc constraints, solve_ubs tl scc constraints with
    | Some n, Some nv => Some (add_valuation hd (Z.to_nat n) nv)
    | _, _ => None
    end
  end.

End scc.

(*Section old_version_of_substitute_terms.

Fixpoint min_list (l : list (option nat)) : option nat :=
  match l with
  | [] => None
  | None :: tl => None
  | [Some hd] => Some hd
  | Some hd :: tl => match min_list tl with
    | Some v => Some (min hd v)
    | None => None
    end
  end.

Fixpoint sum_cartesian_product (l1 l2 : list (nat * Z.t)) : list (nat * Z.t) :=
  match l1 with
  | [] => [] (* 如果第一个列表为空，返回空列表 *)
  | x :: xs =>
      let sums_with_x := map (fun y => (x.1 + y.1, Z.add x.2 y.2)) l2 in
      sums_with_x ++ sum_cartesian_product xs l2 (* 进行拼接 *)
  end.

Definition pair0 := (1, 2%Z).
Definition pair1 := (3, (-4)%Z).
Definition pair2 := (5, 6%Z).
Definition pair3 := (7, (-8)%Z).
Compute (sum_cartesian_product [pair0; pair1] [pair2; pair3]).

(*Definition helper' (v : ProdVar.t) (visited : list ProdVar.t) (cs : list Constraint1) : nat :=
  let cs1 := filter (fun c => (eq_op (lhs_var1 ProdVar.t c) v) && (constraint1_exclusive_set ProdVar.t visited c)) cs in
  length cs1.

Fixpoint helper (terms : list (nat * ProdVar.t)) (visited : list ProdVar.t) (cs : list Constraint1) : nat :=
  match terms with
  | nil => 0
  | (_, hd) :: tl => helper' hd visited cs + helper tl visited cs
  end.*)

(* 对多个 (nat, Z) 对进行替换 
Definition replace_x_pairs (terms: list (nat * ProdVar.t)) (cst : Z.t) (x v: ProdVar.t) (nz_pairs: list (nat * Z)) : list (list (nat * ProdVar.t) * Z.t) :=
  map (replace_x terms cst x v) nz_pairs.

(* 对所有约束进行替换 *)
Definition replace_x_cs (constraints: list Constraint1) (x v: ProdVar.t) 
                             (nz_pairs: list (nat * Z)) : list Constraint1 :=
  flat_map (fun c => 
    let new_terms_cst := replace_x_pairs (rhs_terms1 c) (rhs_const1 c) x v nz_pairs in
    map (fun '(new_terms, new_cst) => {| lhs_var1 := lhs_var1 c; rhs_const1 := new_cst; rhs_terms1 := new_terms |}) new_terms_cst
    ) constraints.

Lemma replace_correct0 : forall nz_pairs x v var constraints,
  x \in (unique_vars
  (filter [eta constraint1_exclusive_v var]
    (replace_x_cs constraints var v nz_pairs))) -> 
  x \in (unique_vars constraints).
Proof.
Admitted.

Lemma replace_correct1 : forall nz_pairs v var constraints,
  var \notin (unique_vars (filter [eta constraint1_exclusive_v var]
    (replace_x_cs constraints var v nz_pairs))).
Proof.
Admitted.

Lemma helper4replace : forall nz_pairs constraints var v,
(size
  (unique_vars
    (filter [eta constraint1_exclusive_v var]
        (replace_x_cs constraints var v nz_pairs))) < size (unique_vars constraints))%coq_nat.
Proof.
Admitted.

Program Fixpoint
  substitute_terms (v : ProdVar.t) (terms : list (nat * ProdVar.t)) (constraints : list Constraint1) 
  {measure (size (unique_vars constraints))} 
  : list (nat * Z.t) :=
  match terms with
  | [] => [(0, 0%Z)] (* list到头 *)
  | (coe, var) :: tl => 
          let var_v := (if (v == var) then [::(1, 0%Z)] else 

            let cs := find_constraint1s var constraints in (* 化简lhs为x的约束到只关于v *)
            let cs' := filter (fun c => constraint1_exclusive_v var c) constraints in (* 用于代入化简的约束不能含有x *)
            flat_map (fun c =>
              map (fun p => (p.1, Z.add p.2 (rhs_const1 c))) (substitute_terms v (rhs_terms1 c) cs')
              ) cs

          ) in (* 用v表示var: v >= nat * v + Z.t *)
          let res0 :=
           map (fun '(coe', cst') => (coe * coe', Z.mul (Z.of_nat coe) cst')) var_v in (* 乘以var的系数 *)

          let cs := replace_x_cs constraints var v var_v in (* 用v替换constraints中的所有var *)
          let cs' := filter (fun c => constraint1_exclusive_v var c) cs in (* 忽略lhs为var的约束 *)
          let res1 := substitute_terms v tl cs' in
          sum_cartesian_product res0 res1
  end.
Next Obligation.
  assert (H : var \in unique_vars constraints) by admit.

  specialize exclusive_v_correct0 with (var := var) (constraints := constraints); intro.
  specialize exclusive_v_correct1 with (var := var) (constraints := constraints); intro.
Admitted.
Next Obligation.
  apply helper4replace.
Admitted.
Next Obligation.
Admitted.

(*Program Fixpoint
  substitute_terms (v : ProdVar.t) (terms : list (nat * ProdVar.t)) (constraints : list Constraint1) 
  {measure (length (unique_vars ProdVar.t constraints))} 
  : list (nat * Z.t) :=

  let fix substitute_v (v x: ProdVar.t) (constraints : list Constraint1) 
  : list (nat * Z.t) :=
  (* 对于关心的v，化简出x之于它的关系式，即把x表示为 a*v+b，由于x可能有多个约束，所以是 list of a*v+b *)
    let cs := find_constraint1s ProdVar.t x constraints in (* 化简lhs为x的约束到只关于v *)
    let cs' := filter (fun c => constraint1_exclusive_v ProdVar.t x c) constraints in (* 用于代入化简的约束不能含有x *)
    flat_map (fun c =>
      map (fun p => (p.1, Z.add p.2 (rhs_const1 ProdVar.t c))) (substitute_terms v (rhs_terms1 ProdVar.t c) cs')
      ) cs
  in

    (* 对于terms，ai*xi，化简出它之于v的关系式。由于每个ai*xi有一系列的v约束，每次对于每个term任选其一 *)
  match  terms with
  | [] => [] (* list到头 *)
  | (coe, var) :: tl => 
          let var_v := (if (v == var) then [::(1, 0%Z)] else 
           substitute_v v var constraints) in (* 用v表示var: v >= nat * v + Z.t *)
          let res0 :=
           map (fun '(coe', cst') => (coe * coe', Z.mul (Z.of_nat coe) cst')) var_v in (* 乘以var的系数 *)

          let cs := replace_x_cs constraints var v var_v in (* 用v替换constraints中的所有var *)
          let cs' := filter (fun c => constraint1_exclusive_v ProdVar.t var c) cs in (* 忽略lhs为var的约束 *)
          let res1 := substitute_terms v tl cs' in
          sum_cartesian_product res0 res1
  end.
Next Obligation.
Admitted.
Next Obligation.
Admitted.*)

Check substitute_terms.

(* 对scc中的某个点v，解出v的上界 *)
Definition solve_ub (v : ProdVar.t) (constraints : list Constraint1) : option nat :=
  let cs := find_constraint1s v constraints in
  let res := flat_map (fun c =>
    map (fun p => (p.1, Z.add p.2 (rhs_const1 c))) (substitute_terms v (rhs_terms1 c) constraints) 
    ) cs in (* 一组 x>= ax+b,进行求解 *) (* a应大于1，b应小于0 *)
  if (existsb (fun '(_, cst) => Z.gtb cst 0%Z) res) then None
    else let res' := filter (fun '(coe, _) => coe > 1) res in
  let ubs := map (fun '(coe, cst) => Z.to_nat (Z.div (Z.abs cst) (Z.of_nat (coe - 1)))) res in 
  Some (min_list ubs).

Fixpoint solve_ubs (scc : list ProdVar.t) (constraints : list Constraint1) : option ProdVar.taluation :=
  match scc with
  | [] => Some (initial_valuation)
  | hd :: tl => match solve_ub hd constraints, solve_ubs tl constraints with
    | Some n, Some nv => Some (add_valuation nv hd n)
    | _, _ => None
    end
  end.*)

End old_version_of_substitute_terms.*)

(*Section test_scc.

Definition c0 : Constraint1 :=
  {|
    lhs_var1 := (11%num,N0);
    rhs_const1 := 1;
    rhs_terms1 := [(1, (8%num,N0))]
  |}.

Definition c1 : Constraint1 :=
  {|
    lhs_var1 := (11%num,N0);
    rhs_const1 := 1;
    rhs_terms1 := [(1, (9%num,N0))]
  |}.

Definition c2 : Constraint1 :=
  {|
    lhs_var1 := (12%num,N0);
    rhs_const1 := -1;
    rhs_terms1 := [(1, (11%num,N0))]
  |}.

Definition c3 : Constraint1 :=
  {|
    lhs_var1 := (8%num,N0);
    rhs_const1 := 0;
    rhs_terms1 := [(1, (12%num,N0))]
  |}.

Definition c4 : Constraint1 :=
  {|
    lhs_var1 := (15%num,N0);
    rhs_const1 := 1;
    rhs_terms1 := [(1, (9%num,N0))]
  |}.

Definition c5 : Constraint1 :=
  {|
    lhs_var1 := (15%num,N0);
    rhs_const1 := 1;
    rhs_terms1 := [(1, (8%num,N0))]
  |}.

Definition c6 : Constraint1 :=
  {|
    lhs_var1 := (16%num,N0);
    rhs_const1 := -1;
    rhs_terms1 := [(1, (15%num,N0))]
  |}.

Definition c7 : Constraint1 :=
  {|
    lhs_var1 := (9%num,N0);
    rhs_const1 := 0;
    rhs_terms1 := [(1, (16%num,N0))]
  |}.

Definition constraints := [c0;c1;c2;c3;c4;c5;c6;c7].
Definition ls := [(15%num,N0);(16%num,N0);(9%num,N0);(11%num,N0);(12%num,N0);(8%num,N0)].

Compute (is_simple_cycle ls (map (fun c => Phi1 c) constraints)).
Definition ubs0 := solve_ubs ls ls constraints.
Definition ub1 := solve_ub (15%num,N0) ls constraints.
Definition vl := filter (fun p => p != (15%num,N0)) ls.
Definition res0 := substitute_vs vl constraints.
Compute res0.

(*Definition res := substitute_terms (n_V 3) (rhs_terms1 c0) [c1; c2].
Definition res1 := substitute_terms (n_V 3) [(1, n_V 0); (2, n_V 1); (3, n_V 2)] constraints.*)

Definition c4 : Constraint1 :=
  {|
    lhs_var1 := n_V 2;
    rhs_const1 := 0;
    rhs_terms1 := [(1, n_V 0); (1, n_V 1)]
  |}.

(*Definition res2 := substitute_terms (n_V 3) [(1, n_V 0); (2, n_V 1); (3, n_V 2)] (c4 :: constraints).*)

Definition c5 : Constraint1 :=
  {|
    lhs_var1 := (n_V 0);
    rhs_const1 := -3;
    rhs_terms1 := [(2, (n_V 1)); (1, (n_V 2))]
  |}.

Definition c6 : Constraint1 :=
  {|
    lhs_var1 := n_V 1;
    rhs_const1 := -1;
    rhs_terms1 := [(1, n_V 2)]
  |}.

Definition c7 : Constraint1 :=
  {|
    lhs_var1 := n_V 2;
    rhs_const1 := 1;
    rhs_terms1 := [(1, n_V 0)]
  |}.

Definition ub3 := solve_ub (n_V 1) [(n_V 0); (n_V 1); (n_V 2)] [c5; c6; c7].
Compute ub3.
Definition ub3' := solve_ubs [(n_V 0); (n_V 1); (n_V 2)] [(n_V 0); (n_V 1); (n_V 2)] [c5; c6; c7].
Compute ub3'.


Compute (substitute_vs [(n_V 0); (n_V 2)] [c5; c6; c7]).
Compute (substitute_constraint c7 (n_V 0) [(2, (n_V 1)); (1, (n_V 2))] (-3)%Z).
Definition cs1 := substitute_vs [(n_V 0)] [c5; c6; c7].
Compute (substitute_vs [(n_V 2)] cs1).
Compute (substitute_vs [(n_V 0); (n_V 2)] [c5; c6; c7]).

End test_scc.*)

Section SccCorrectness.

Definition good_terms (terms : list term) : Prop :=
  (forall coe var, List.In (coe, var) terms -> coe <> 0)
  /\ NoDup (List.split terms).2
  (* terms中没有相同的两项var *).

Lemma good_terms_NoDup : forall (terms : list term),
  good_terms terms -> NoDup terms.
Proof.
  intros terms [H1 H2].  (* 分解good_terms为两个假设H1和H2 *)
  induction terms as [|[coe var] ts IH].  (* 对terms进行结构归纳 *)
  - apply NoDup_nil.  (* 空列表的情况，直接应用NoDup_nil *)
  - apply NoDup_cons.  (* 非空列表的情况，应用NoDup_cons构造子 *)
    + intro H.  (* 假设t在ts中出现，导出矛盾 *)
      (* 分解H2：split (t::ts).2是NoDup的 *)
      destruct (List.split ts) as [coes vars] eqn : Hsplit.
      simpl in H2. rewrite Hsplit in H2; simpl in H2.
      apply in_split_r in H; rewrite Hsplit in H; simpl in H. apply NoDup_cons_iff in H2. intuition.
    + apply IH.  (* 应用归纳假设，需证明good_terms ts *)
      * intros; apply (H1 _ var0). right; done.
      * destruct (List.split ts) as [coes vars] eqn : Hsplit.
        simpl in H2. rewrite Hsplit in H2; simpl in H2. simpl. apply (NoDup_remove_1 nil vars var); simpl; done.
Qed.

Definition strict_smaller_valuation (v0 v1 : Valuation) : Prop :=
  (forall (var : ProdVar.t), PVM.mem var v0 -> 
  (exists value0 value1, PVM.find var v0 = Some value0 /\ PVM.find var v1 = Some value1 /\ value0 <= value1))
  /\ (exists (var : ProdVar.t), PVM.mem var v0 /\
  (exists value0 value1, PVM.find var v0 = Some value0 /\ PVM.find var v1 = Some value1 /\ value0 < value1))
  /\ (forall var, PVM.mem var v0 <-> PVM.mem var v1).

(*Definition satisfies_constraint1 (v: Valuation) (c: Constraint1) : bool :=
  match PVM.find c.(lhs_var1) v with
  | Some val => Z.leb (rhs_value1 v c) (Z.of_nat val)
  | None => Z.leb (rhs_value1 v c) 0%Z
  end.*)

Definition goodubs (cs1 : list Constraint1) (ubs : Valuation) : Prop :=
  (* 任何大于ub的取值都将不满足，只包含这些已求变量的约束 *)
  (*let cs := List.filter (fun c => forallb (fun v => PVM.mem v ubs) (constraint1_vars c)) cs1 in*)
  forall temp_ub, strict_smaller_valuation ubs temp_ub -> 
    exists c, List.In c cs1 /\ ((satisfies_constraint1 temp_ub c = false)).


Lemma reduce_constraints1_helper (hd : ProdVar.t) (res : Z.t) : forall cl optionub, forallb (fun c : Constraint1 => (lhs_var1 c == hd)) cl ->
  (forall c : Constraint1, List.In c cl -> good_terms (rhs_terms1 c)) ->
  fold_left
      (fun (ub : option Z.t) (c : Constraint1) =>
        match List.find (fun p : term => p.2 == hd) (rhs_terms1 c) with
        | Some t =>
            let (coe, _) := t in
            match coe with
            | 0 =>
                match ub with
                | Some n =>
                    Some (Z.min n (Z.abs (rhs_const1 c) / Z.of_nat (coe - 1) + 1))
                | None => Some (Z.abs (rhs_const1 c) / Z.of_nat (coe - 1) + 1)%Z
                end
            | n0.+1 =>
                match n0 with
                | 0 => ub
                | _.+1 =>
                    match ub with
                    | Some n =>
                        Some (Z.min n (Z.abs (rhs_const1 c) / Z.of_nat (coe - 1) + 1))
                    | None => Some (Z.abs (rhs_const1 c) / Z.of_nat (coe - 1) + 1)%Z
                    end
                end
            end
        | None => ub
        end) cl optionub = Some res ->
  match optionub with
  | Some ub => ub = res \/ (exists c, List.In c cl /\ (exists coe, List.find (fun p : term => p.2 == hd) (rhs_terms1 c) = Some (coe, hd) /\ coe > 1 /\
    (Z.add (Z.div (Z.abs (rhs_const1 c)) (Z.of_nat (coe - 1))) 1 = res)))
  | None => exists c, List.In c cl /\ (exists coe, List.find (fun p : term => p.2 == hd) (rhs_terms1 c) = Some (coe, hd) /\ coe > 1 /\
    (Z.add (Z.div (Z.abs (rhs_const1 c)) (Z.of_nat (coe - 1))) 1 = res))
  end.
Proof.
    elim.
    - simpl; intros.
      rewrite H1; left; done.
    - simpl; intros a l H optionub H0 Hterm; intros.
      move /andP : H0 => [Heq Hforall].
      apply H in H1; try done; clear H.
      move /eqP : Heq => Heq; subst.
      case Hfind : (List.find (fun p : term => p.2 == lhs_var1 a) (rhs_terms1 a)) => [[coe hd]|]; rewrite Hfind in H1.
      - case Hcoe : coe => [|coe']; subst.
        apply find_some in Hfind. assert (a=a\/List.In a l) by (left; done). apply Hterm in H; clear Hterm. rewrite /good_terms in H. 
        move : H => [H _]; move : Hfind => [Hfind _]. apply H in Hfind; done. (* 不存在coe为0 *)
        case Hcoe : coe' => [|coe]; subst.
        - (* coe = 1 *)
          case Hoptionub : optionub => [ub|]; rewrite Hoptionub in H1; try done.
          (* Some *)
          destruct H1.
          left; done.
          destruct H as [c [Hin H]].
          right; exists c; split; try done.
          right; done.
          (* None *)
          destruct H1 as [c [Hin H]].
          exists c; split; try done.
          right; done.
        - (* coe >1 *)
          case Hoptionub : optionub => [ub|]; rewrite Hoptionub in H1; try done.
          (* Some *)
          destruct H1.
          - (* res = min ub a *)
            specialize (Z.min_spec ub (Z.abs (rhs_const1 a) / Z.of_nat (coe.+2 - 1) + 1)); intro Hmin.
            destruct Hmin.
            * (* res = ub *)
              move : H0 => [Hlt Hmin].
              rewrite Hmin in H; left; done.
            * (* res = a *)
              move : H0 => [Hlt Hmin].
              rewrite Hmin in H.
              right; exists a. 
              split; try left; try done.
              exists (coe.+2); split; try done.
              generalize Hfind; apply find_some in Hfind as [Hin Hlhs]; intros Hfind.
              move /eqP : Hlhs => Hlhs; simpl in Hlhs; subst; done.
          - (* res in l *)
            destruct H as [c [Hin H]].
            right; exists c; split; try right; try done.
          (* None *)
          destruct H1.
          - (* res = a *)
            exists a. 
            split; try left; try done.
            exists (coe.+2); split; try done.
            generalize Hfind; apply find_some in Hfind as [Hin Hlhs]; intros Hfind.
            move /eqP : Hlhs => Hlhs; simpl in Hlhs; subst; done.
          - (* res in l *)
            destruct H as [c [Hin H]].
            exists c; split; try right; try done.

      - case Hoptionub : optionub => [ub|]; rewrite Hoptionub in H1; try done.
        (* Some *)
        destruct H1.
        left; done.
        destruct H as [c [Hin H]].
        right; exists c; split; try done.
        right; done.
        (* None *)
        destruct H1 as [c [Hin H]].
        exists c; split; try done.
        right; done.
        intros; apply Hterm; right; done.
Qed.

Lemma reduce_constraints1 valuation : forall cl (hd : ProdVar.t), forallb (fun c => lhs_var1 c == hd) cl ->
  (forall c, List.In c cl -> good_terms (rhs_terms1 c) /\ Z.le (rhs_const1 c) 0 /\ (rhs_power c) = nil) -> 
  match fold_left (fun (ub : option Z.t) (c : Constraint1) => 
    match List.find (fun (p : term) => snd p == hd) (rhs_terms1 c), ub with
    | None, _ => ub
    | Some (1, _), _ => ub
    | Some (coe, _), None => Some (Z.add (Z.div (Z.abs (rhs_const1 c)) (Z.of_nat (coe - 1))) 1)
    | Some (coe, _), Some n => Some (Z.min n (Z.add (Z.div (Z.abs (rhs_const1 c)) (Z.of_nat (coe - 1))) 1))
    end) cl None with 
  | Some res => forall m, Z.lt res m -> PVM.find hd valuation = Some (Z.to_nat m) -> exists c, List.In c cl /\ List.existsb (fun (p : term) => snd p == hd) (rhs_terms1 c) /\
    satisfies_constraint1 valuation c = false
  | None => true
  end.
Proof.
  intros cl hd Hcl Hterm.
  case Hres : (fold_left
    (fun (ub : option Z.t) (c : Constraint1) =>
    match List.find (fun p : term => p.2 == hd) (rhs_terms1 c) with
    | Some t =>
        let (coe, _) := t in
        match coe with
        | 0 =>
            match ub with
            | Some n =>
                Some (Z.min n (Z.abs (rhs_const1 c) / Z.of_nat (coe - 1)+1))
            | None => Some (Z.abs (rhs_const1 c) / Z.of_nat (coe - 1)+1)%Z
            end
        | n0.+1 =>
            match n0 with
            | 0 => ub
            | _.+1 =>
                match ub with
                | Some n =>
                    Some
                      (Z.min n (Z.abs (rhs_const1 c) / Z.of_nat (coe - 1)+1))
                | None => Some (Z.abs (rhs_const1 c) / Z.of_nat (coe - 1)+1)%Z
                end
            end
        end
    | None => ub
    end) cl None) => [res|]; try done.
  
  apply (reduce_constraints1_helper _ _) in Hres; try done; simpl in Hres.

  destruct Hres as [c [Hin [coe [Hfind [Hcoe Hres]]]]].
  intros m H Hfindhd; exists c; split; try done.
  split.
  apply existsb_exists;
  apply find_some in Hfind;
  exists (coe, hd); done.
  assert (lhs_var1 c == hd) by
    (move : Hcl Hin;
    clear;
    intro H; move : c; apply forallb_forall; done).
  clear Hcl. 
  move /eqP : H0 => H0; subst. 
  unfold satisfies_constraint1, rhs_value1, terms_value.

  assert (Hm : (0 <= m)%Z).
  move : H Hcoe; clear; intros.
    specialize (Z_div_ge0 (Z.abs (rhs_const1 c)) (Z.of_nat (coe - 1))); intro.
    specialize (Z.abs_nonneg (rhs_const1 c)); intro.
    apply Z.le_ge in H1.
    apply H0 in H1; clear H0.
    apply Z.ge_le in H1.
    specialize (Z.lt_add_pos_r 1 (Z.abs (rhs_const1 c) / Z.of_nat (coe - 1))%Z); intro.
    assert ((0 < Z.abs (rhs_const1 c) / Z.of_nat (coe - 1) + 1)%Z).
      apply (Z.le_lt_trans _ _ _ H1).
      apply H0; try done.
    specialize (Z.lt_trans _ _ _ H2 H); intros.
    lia.
    rewrite -Nat2Z.inj_0.
    apply inj_gt.
    apply Arith_prebase.gt_S_n_stt.
    rewrite subn1 Nat.succ_pred_pos.
    apply (elimT leP); done.
    apply Nat.le_lt_trans with (m := 1).
    - apply le_0_n.  (* 证明0 <= 1 *)
    - apply (elimT leP); done.

  rewrite Hfindhd Z2Nat.id; try done.
  assert (Hpower : (rhs_power c) = nil) by (apply Hterm in Hin; clear Hterm; exact Hin.2.2).
  assert (Hcst : Z.le (rhs_const1 c) 0) by (apply Hterm in Hin; clear Hterm; exact Hin.2.1).
  rewrite Hpower; clear Hpower; simpl. clear Hin.
  apply Z.leb_gt.
  rewrite Z.add_0_r.
  assert ((((rhs_const1 c) + (Z.of_nat (coe * (Z.to_nat m)))) <= fold_left
    (fun (acc : Z) (ax : nat * PVM.key) =>
    acc +
    Z.of_nat
      (ax.1 *
        match
          PVM.find (elt:=nat) ax.2 valuation
        with
        | Some val => val
        | None => 0
        end)) (rhs_terms1 c) (rhs_const1 c))%Z).
    clear H Hcoe.
    assert (exists pre post, pre ++ (coe, lhs_var1 c) :: post = (rhs_terms1 c)).
      assert (Hin : List.In (coe, lhs_var1 c) (rhs_terms1 c)) by
        (apply find_some in Hfind; move : Hfind => [Hfind _]; done). 
      destruct (List.In_split _ _ Hin) as [pre [post Hsplit]].
      exists pre, post. symmetry. apply Hsplit.
    destruct H as [pre [post H]].
    rewrite -H; clear H.
    rewrite fold_left_app.
    remember ((fold_left
      (fun (acc : Z) (ax : nat * PVM.key) =>
      acc +
      Z.of_nat
        (ax.1 *
          match
            PVM.find (elt:=nat) ax.2 valuation
          with
          | Some val => val
          | None => 0
          end)) pre (rhs_const1 c))%Z) as res0.
    simpl.
    rewrite Hfindhd.
    assert (forall init ls lhs, Z.le lhs init -> Z.le lhs (fold_left
      (fun (acc : Z) (ax : nat * PVM.key) =>
      (acc +
        Z.of_nat
          (ax.1 *
          match
            PVM.find (elt:=nat) ax.2 valuation
          with
          | Some val => val
          | None => 0
          end))%Z) ls init)).
      clear.
      intros init ls; move : ls init.
      elim.
      - simpl; intros; done.
      - simpl; intros.
        apply H; clear H.
        assert ((init <= init + Z.of_nat (a.1 *
            match PVM.find (elt:=nat) a.2 valuation with
            | Some val => val
            | None => 0
            end))%Z) by lia.
        move : H0 H; apply Z.le_trans.
    specialize (H (rhs_const1 c) pre (rhs_const1 c)) as H0; rewrite -Heqres0 in H0.
    apply (H ((res0 + Z.of_nat (coe * Z.to_nat m))%Z) post ((rhs_const1 c + Z.of_nat (coe * Z.to_nat m))%Z)); clear H.
    apply Zplus_le_compat_r.
    apply H0. lia.

  assert ((m < rhs_const1 c + Z.of_nat (coe * Z.to_nat m))%Z).
    clear H0 Hfind.
    assert (Hcoe' : (0 < Z.of_nat (coe - 1))%Z).
      rewrite -Nat2Z.inj_0.
      apply inj_lt.
      apply Arith_prebase.lt_S_n_stt.
      rewrite subn1 Nat.succ_pred_pos.
      apply (elimT leP); done.
      apply Nat.le_lt_trans with (m := 1).
      - apply le_0_n.  (* 证明0 <= 1 *)
      - apply (elimT leP); done.
    apply Z.abs_neq in Hcst.
    rewrite Hcst in H; clear Hcst.
    apply (Zmult_lt_compat_r _ _ _ Hcoe') in H.
    apply Z.lt_sub_lt_add_l.
    rewrite -Z.add_opp_l.
    apply Z.lt_add_lt_sub_r.
    rewrite Nat2Z.inj_mul Z2Nat.id.
    rewrite -{2}(Z.mul_1_l m) -Z.mul_sub_distr_r Z.mul_comm.
    rewrite {1}Z.mul_comm in H.
    rewrite (Z_div_mod_eq_full (- rhs_const1 c) (Z.of_nat (coe - 1))).
    rewrite Z.mul_add_distr_l Z.mul_1_r in H.
    rewrite {4}Nat2Z.inj_sub in H. simpl in H.
    move : H; apply Z.lt_trans.
    apply Zplus_lt_compat_l.
    apply (Z.mod_pos_bound (- rhs_const1 c)%Z) in Hcoe'.
    move : Hcoe' => [_ Hcoe']; done.
    apply (elimT leP).
    apply ltnW; done.
    done.

  move : H1 H0; apply Z.lt_le_trans.
  intros; apply Hterm in H; exact H.1.
Qed.

Lemma good_terms_tl : forall a l, good_terms (a :: l) -> good_terms l.
Proof.
  unfold good_terms; intros [coe var]; intros. move : H => [H0 H1]. split. intros; apply (H0 _ var0); simpl; right; done.
  destruct (List.split l) as [coes vars] eqn : Hsplit. simpl in H1; rewrite Hsplit in H1; simpl in H1. simpl. apply NoDup_cons_iff in H1. exact H1.2.
Qed.

Lemma good_terms_remove : forall a l, good_terms l -> good_terms (List.remove term_dec a l).
Proof.
  unfold good_terms; intros [coe var]; intros. move : H => [H0 H1]. split. intros; apply (H0 _ var0). apply in_remove in H. exact H.1.
  clear H0; move : l H1. elim. 
  - simpl; intros; apply NoDup_nil.
  - simpl; intros [coe' var']; intros.
    destruct (List.split l) as [coes vars] eqn : Hsplit. simpl in H1; simpl in H. 
    case Hdec : (term_dec (coe, var) (coe', var')) => [left|right]. apply H. apply NoDup_cons_iff in H1. exact H1.2.
    destruct (List.split (remove term_dec (coe, var) l)) as [coes' vars'] eqn : Hsplit'. simpl; rewrite Hsplit'; simpl. simpl in H. 
    apply NoDup_cons_iff in H1. move : H1 => [H1 Hvars]. apply NoDup_cons. apply split_combine in Hsplit. rewrite -Hsplit in Hsplit'.
    apply (in_split_remove _ _ _ _ Hsplit'); done.
    apply H; done.
Qed.

Lemma substitute_good_terms coe : forall l1 l0, good_terms l0 -> good_terms l1 -> coe <> 0 -> good_terms (fold_right
    (fun '(coe', var) (acc : list term) =>
    match List.find (fun p : term => p.2 == var) acc with
    | Some t =>
        let (existing_coef0, _) := t in
        (existing_coef0 + coe * coe', var) :: remove term_dec (existing_coef0, var) acc
    | None => (coe * coe', var) :: acc
    end) l0 l1).
Proof.
  elim. 
  - simpl; intros; done. 
  - simpl; intros [coe' var]; intros.
    remember ((fold_right
      (fun '(coe'0, var0) (acc : list term) =>
      match List.find (fun p : term => p.2 == var0) acc with
      | Some t =>
          let (existing_coef0, _) := t in
          (existing_coef0 + coe * coe'0, var0)
          :: remove term_dec (existing_coef0, var0) acc
      | None => (coe * coe'0, var0) :: acc
      end) l0 l)) as tl. rewrite -Heqtl.
    assert (Hgoodl : good_terms l) by (apply (good_terms_tl H1)).
    assert (Hgoodtl : good_terms tl) by (rewrite Heqtl; apply H; try done).
    case Hfind : (List.find (fun p : term => p.2 == var) tl) => [[existing_coef var']|].
    * rewrite /good_terms. split.
      + simpl; intros. destruct H3. inversion H3; subst; clear H3.
        remember (fold_right
          (fun '(coe'0, var0) (acc : list term) =>
          match List.find (fun p : term => p.2 == var0) acc with
          | Some t =>
              let (existing_coef0, _) := t in
              (existing_coef0 + coe * coe'0, var0) :: remove term_dec (existing_coef0, var0) acc
          | None => (coe * coe'0, var0) :: acc
          end) l0 l) as tl.
        assert (existing_coef <> 0). rewrite /good_terms in Hgoodtl; move : Hgoodtl => [Hgoodtl _]. specialize (find_some _ _ Hfind); intro.
        move : H3.1; apply Hgoodtl.
        intro Heq. assert (existing_coef + coe * coe' == 0) by (rewrite Heq; apply eq_refl). clear Heq; rewrite addn_eq0 in H4.
        move /andP : H4 => [H4 _]. move /eqP : H4 => H4; done. 
        apply in_remove in H3. move : H3.1. rewrite /good_terms in Hgoodtl. apply Hgoodtl.1.
        
        simpl. destruct (List.split (remove term_dec (existing_coef, var) tl)) as [coes vars] eqn : Hsplit; simpl. 
        rewrite /good_terms in Hgoodtl. move : Hgoodtl => [_ Htl].
        destruct (List.split tl) as [coes' vars'] eqn : Hsplit'; simpl in Htl. apply split_combine in Hsplit'. rewrite -Hsplit' in Hsplit.
        apply NoDup_cons.
        - move :  Hsplit; apply (NoDup_remove_notin _ _ _ Htl). apply find_some in Hfind; move : Hfind => [Hin Heq].
          move /eqP : Heq => Heq. simpl in Heq; subst var'. rewrite -Hsplit' in Hin; done. 
        - apply (remove_NoDup _ _ Hsplit); done.

    * rewrite /good_terms. split.
      + simpl; intros. destruct H3. inversion H3; subst; clear H3.
        rewrite /good_terms in H1. move : H1 => [H1 _].
        intro Heq. assert (coe * coe' == 0) by (rewrite Heq; apply eq_refl). clear Heq; rewrite muln_eq0 in H3.
        destruct (coe == 0) eqn : Heq; move /eqP : Heq => Heq; try done. rewrite orb_false_l in H3. move /eqP : H3 => H3.
        assert (List.In  (coe', var0) ((coe', var0) :: l)) by (simpl; left; done). apply H1 in H4; try done.
        assert (good_terms tl) by (rewrite Heqtl; apply H; try done).
        rewrite /good_terms in H4. apply H4.1 in H3; done.

        simpl. destruct (List.split tl) as [coes vars] eqn : Hsplit. 
        apply NoDup_cons. specialize (find_none _ _ Hfind); intro. 
        apply combine_notin in H3. rewrite Hsplit in H3; done.

        rewrite /good_terms in Hgoodtl. rewrite Hsplit in Hgoodtl; simpl in Hgoodtl; exact Hgoodtl.2.
Qed.

Lemma substitute_constraint_rhs valuation (hd : ProdVar.t) hd_val coe : forall (terms_hd terms_tl : list term) cst_hd cst_tl,
  good_terms terms_tl -> good_terms terms_hd ->
  List.find (fun p : term => snd p == hd) terms_tl = Some (coe, hd) ->
  PVM.find hd valuation = Some hd_val -> 
  terms_value valuation
    (fold_right
      (fun '(coe', var) (acc : list term) =>
        match List.find (fun p : term => p.2 == var) acc with
        | Some t =>
            let (existing_coef, _) := t in
            (existing_coef + coe * coe', var) :: (List.remove term_dec (existing_coef, var) acc)
        | None => (coe * coe', var) :: acc
        end) (remove term_dec (coe, hd) terms_tl)
      terms_hd)
    (cst_tl + Z.of_nat coe * cst_hd) =
  (terms_value valuation terms_tl cst_tl -
  Z.of_nat (coe * hd_val) +
  Z.of_nat coe *
  terms_value valuation terms_hd cst_hd)%Z.
Proof.
  elim.
  - simpl; intros terms_tl cst_hd cst_tl Hnodup_tl Hnodup_hd; intros.
    specialize terms_value_remove with (hd_val := hd_val); intros.
    rewrite H1; try done; clear H1.
    rewrite terms_value_cst_add Nat2Z.inj_mul.
    apply Z.add_sub_swap. apply (good_terms_NoDup Hnodup_tl). (* NoDup *) rewrite H0 //.
  - simpl; intros [coe_hd var_hd] terms_hd' H terms_tl cst_hd cst_tl Hnodup_tl Hnodup_hd; intros.
    simpl; simpl in H.
    rewrite (terms_value_cst_add _ _ cst_hd (Z.of_nat
      (coe_hd *
       match PVM.find (elt:=nat) var_hd valuation with
       | Some val => val
       | None => 0
       end))).
    remember (fold_right
      (fun '(coe', var) (acc : list term) =>
      match List.find (fun p : term => p.2 == var) acc with
      | Some t => let (existing_coef, _) := t in (existing_coef + coe * coe', var) :: (List.remove term_dec (existing_coef, var) acc)
      | None => (coe * coe', var) :: acc
      end) (remove term_dec (coe, hd) terms_tl) terms_hd') as combined_hd'.
    rewrite -Heqcombined_hd'.
    case Hfind : (List.find (fun p : term => p.2 == var_hd) combined_hd') => [[existing_coef var_hd']|]; try done.
    - (* 代入hd'后，存在var_hd *)
      (* 整理右 *)
      rewrite Z.mul_add_distr_l Z.add_assoc.
      (* 整理左 *)
      assert ((existing_coef + coe * coe_hd, var_hd) :: remove term_dec (existing_coef, var_hd) combined_hd' 
        = [(existing_coef + coe * coe_hd, var_hd)] ++ remove term_dec (existing_coef, var_hd) combined_hd') by (simpl; done).
      rewrite H2. rewrite (terms_value_app (cst_tl + Z.of_nat coe * cst_hd)%Z valuation [(existing_coef + coe * coe_hd, var_hd)] 
        (remove term_dec (existing_coef, var_hd) combined_hd')). clear H2; simpl.
      rewrite Z.add_comm. 
      rewrite -> mult_plus_distr_r.
      rewrite Nat2Z.inj_add.
      (* 化简消去 *)
      rewrite (Nat2Z.inj_mul (coe * coe_hd) (match PVM.find (elt:=nat) var_hd valuation with
        | Some val => val
        | None => 0
        end)).
      rewrite (Nat2Z.inj_mul coe coe_hd).
      rewrite (Nat2Z.inj_mul coe_hd (match PVM.find (elt:=nat) var_hd valuation with
        | Some val => val
        | None => 0
        end)) Z.mul_assoc.
      rewrite Z.add_assoc.
      (* 化简 *)
      apply Z.add_cancel_r.
      specialize terms_value_remove with (hd_val := (match PVM.find (elt:=nat) var_hd valuation with
        | Some val => val
        | None => 0
        end)); intros.
      rewrite H2; try done; clear H2.
      rewrite Z.sub_add.
      rewrite Heqcombined_hd'; apply H; try done.
      (* NoDup start *)
      move : Hnodup_hd; clear. unfold good_terms in *; intros. move : Hnodup_hd => [H0 H1]. split. intros. 
      assert (List.In  (coe, var) ((coe_hd, var_hd) :: terms_hd')) by (simpl; right; done). clear H; apply H0 in H2; try done.
      destruct (List.split terms_hd') as [coes vars] eqn : Hsplit; simpl. simpl in H1; rewrite Hsplit in H1; simpl in H1.
      apply NoDup_cons_iff in H1; exact H1.2.
      apply good_terms_NoDup. rewrite Heqcombined_hd'; apply substitute_good_terms; try done.
      apply good_terms_remove; done. move : Hnodup_hd; apply good_terms_tl.

      rewrite /good_terms in Hnodup_tl. apply (Hnodup_tl.1 _ hd). apply find_some in H0. exact H0.1.
      generalize Hfind; apply find_some in Hfind; simpl in Hfind; intros. move : Hfind => [Hin Heq]; move /eqP : Heq => Heq. rewrite Heq in Hfind0; done.

    - (* 不存在var_hd *)
      (* 整理左 *)
      assert ((coe * coe_hd, var_hd) :: combined_hd' = [(coe * coe_hd, var_hd)] ++ combined_hd') by (simpl; done).
      rewrite H2. rewrite (terms_value_app (cst_tl + Z.of_nat coe * cst_hd)%Z valuation [(coe * coe_hd, var_hd)] (combined_hd')). clear H2; simpl.
      rewrite Z.add_comm.
      (* 整理右 *)
      rewrite Z.mul_add_distr_l Z.add_assoc.
      rewrite Nat2Z.inj_mul.
      rewrite Nat2Z.inj_mul.
      rewrite (Nat2Z.inj_mul coe_hd (match PVM.find (elt:=nat) var_hd valuation with
        | Some val => val
        | None => 0
        end)) Z.mul_assoc.
      (* 化简 *)
      apply Z.add_cancel_r.
      rewrite Heqcombined_hd'; apply H; try done.
      (* NoDup start *)
      move : Hnodup_hd; apply good_terms_tl.
      (* Nodup end*)
Qed.

Lemma substitute_hd_2_c valuation hd c_hd c_tl : 
  (satisfies_constraint1 valuation (substitute_constraint c_tl hd (rhs_terms1 c_hd) (rhs_const1 c_hd)) = false) -> 
  lhs_var1 c_hd = hd -> rhs_power c_hd = nil -> rhs_power c_tl = nil -> good_terms (rhs_terms1 c_hd) -> good_terms (rhs_terms1 c_tl) ->
  (satisfies_constraint1 valuation c_hd = false) \/ (satisfies_constraint1 valuation c_tl = false).
Proof.
  intros H Hhdlhs Hhd_power Htl_power Hhd_term Htl_term.
  rewrite /satisfies_constraint1 in H; simpl in H.
  rewrite {1}/substitute_constraint in H; simpl in H.
  case Hfind : (List.find (fun p : term => snd p == hd) (rhs_terms1 c_tl)) => [[coe hd']|]; rewrite Hfind in H; simpl in H.
  - (* some hd term in c_tl *)
    case Hlhs : (PVM.find (elt:=nat) (lhs_var1 c_tl) valuation) => [tl_val|]; rewrite Hlhs in H; try done.
    + destruct (satisfies_constraint1 valuation c_hd) eqn : Hc_hd; try intuition.
      (* hd >= ... 成立 *)
      right.
      unfold satisfies_constraint1 in *; rewrite Hlhs.
      case Hhd : (PVM.find (elt:=nat) (lhs_var1 c_hd) valuation) => [hd_val|]; rewrite Hhd in Hc_hd; try discriminate.
      apply Zle_bool_imp_le in Hc_hd.
      apply Z.leb_gt.
      apply Z.leb_gt in H.
      assert ((rhs_value1 valuation (substitute_constraint c_tl hd (rhs_terms1 c_hd) (rhs_const1 c_hd)) <= 
        rhs_value1 valuation c_tl)%Z).
        clear H. 
        rewrite /substitute_constraint Hfind /rhs_value1; simpl; rewrite Z.add_0_r.
        assert ((terms_value valuation
          (fold_right
            (fun '(coe', var) (acc : list term) =>
              match List.find (fun p : term => p.2 == var) acc with
              | Some t =>
                  let (existing_coef, _) := t in
                  ((existing_coef + coe * coe')%nat, var) :: remove term_dec (existing_coef, var) acc
              | None => ((coe * coe')%nat, var) :: acc
              end) (remove term_dec (coe, hd) (rhs_terms1 c_tl))
            (rhs_terms1 c_hd))
          (rhs_const1 c_tl + Z.of_nat coe * rhs_const1 c_hd) 
          = terms_value valuation (rhs_terms1 c_tl) (rhs_const1 c_tl) - Z.of_nat (coe * hd_val)
            + Z.of_nat coe * (terms_value valuation (rhs_terms1 c_hd) (rhs_const1 c_hd)))%Z).
          apply substitute_constraint_rhs; try done.
          apply find_some in Hfind as Heq. 
          move /eqP : Heq.2 => Heq'; clear Heq. 
          simpl in Heq'; rewrite Heq' in Hfind; done.
          rewrite -Hhdlhs //.
        rewrite H; clear H. 
        rewrite Nat2Z.inj_mul -Z.sub_sub_distr -Zmult_minus_distr_l.
        rewrite Htl_power; simpl; rewrite Z.add_0_r.
        apply (Zplus_le_reg_r _ _ (Z.of_nat coe *
          (Z.of_nat hd_val -
          terms_value valuation (rhs_terms1 c_hd) (rhs_const1 c_hd)))%Z).
        rewrite Z.sub_add.
        apply (Z.sub_le_mono_r _ _ (terms_value valuation (rhs_terms1 c_tl) (rhs_const1 c_tl))).
        rewrite Z.sub_diag Z.add_simpl_l.
        apply Ztac.mul_le; try intuition.
        apply Zle_minus_le_0.
        rewrite /rhs_value1 in Hc_hd.
        rewrite Hhd_power in Hc_hd; simpl in Hc_hd; rewrite Z.add_0_r in Hc_hd; done.

      move : H H0; apply Z.lt_le_trans.
    + (* no lhs value *)
      right; rewrite /satisfies_constraint1 Hlhs //.
  - (* no hd term in c_tl *)
    rewrite /substitute_constraint Hfind in H; intuition.
Qed.

Lemma substitute_hd_2_cs valuation hd c_hd: forall cs_tl, lhs_var1 c_hd = hd -> rhs_power c_hd = [] -> (forall c, List.In c cs_tl -> rhs_power c = []) ->
  good_terms (rhs_terms1 c_hd) -> (forall c, List.In c cs_tl -> good_terms (rhs_terms1 c)) -> 
  (exists (c : Constraint1), List.In c (List.map
    (fun temp_c : Constraint1 =>
      substitute_constraint temp_c hd (rhs_terms1 c_hd) (rhs_const1 c_hd)) cs_tl) /\ 
  satisfies_constraint1 valuation c = false) -> 
  (satisfies_constraint1 valuation c_hd = false) \/ (exists c, List.In c cs_tl /\ satisfies_constraint1 valuation c = false).
Proof.
  elim. 
  - simpl; intros; try done.
    intuition.
  - simpl; intros c_tl cs_tl' H Hhdlhs Hhd_power Htl_power Hhd_term Htl_term. intros.
    destruct H0 as [c [Hin Hunsat]].
    destruct Hin.
    - (* is c_tl or c_hd *)
      clear H. 
      rewrite -H0 in Hunsat.
      apply substitute_hd_2_c in Hunsat; try done.
      destruct Hunsat.
      - (* is c_hd *)
        left; done.
      - (* is c_tl *)
        right; exists c_tl; split; try left; try done.
      apply Htl_power; left; done.
      apply Htl_term; left; done.
    - (* in cs_tl' or c_hd *)
      assert (Hcs_tl' : exists c : Constraint1,
        List.In c
          (List.map
            (fun temp_c : Constraint1 =>
              substitute_constraint temp_c hd 
                (rhs_terms1 c_hd) (rhs_const1 c_hd)) cs_tl') /\
        satisfies_constraint1 valuation c = false) by (exists c; done).
      clear H0.
      apply H in Hcs_tl'; clear H; try done.
      destruct Hcs_tl'.
      - (* is c_hd *)
        left; done.
      - (* in cs_tl' *)
        right.
        destruct H as [c0 [Hin0 Hunsat0]].
        exists c0; split; try right; try done.
      intros; apply Htl_power; right; done.
      intros; apply Htl_term; right; done.
Qed.

Lemma substitute_hds_2_c valuation hd c_hd: forall cs_tl, 
  (forall c, List.In c cs_tl -> lhs_var1 c = hd) -> 
  rhs_power c_hd = [] -> (forall c, List.In c cs_tl -> rhs_power c = []) ->
  good_terms (rhs_terms1 c_hd) -> (forall c, List.In c cs_tl -> good_terms (rhs_terms1 c)) -> 
  (exists (c : Constraint1), List.In c (List.map
    (fun temp_c : Constraint1 =>
      substitute_constraint c_hd hd (rhs_terms1 temp_c) (rhs_const1 temp_c)) cs_tl) /\ 
  satisfies_constraint1 valuation c = false) -> 
  (satisfies_constraint1 valuation c_hd = false) \/ (exists c, List.In c cs_tl /\ satisfies_constraint1 valuation c = false).
Proof.
  elim. 
  - simpl; intros; try done.
    intuition.
  - simpl; intros c_tl cs_tl' H Hhdlhs Hhd_power Htl_power Hhd_term Htl_term. intros.
    destruct H0 as [c [Hin Hunsat]].
    destruct Hin.
    - (* is c_tl or c_hd *)
      clear H. 
      rewrite -H0 in Hunsat.
      apply substitute_hd_2_c in Hunsat; try done.
      destruct Hunsat.
      - (* is c_tl *)
        right; exists c_tl; split; try left; try done.
      - (* is c_hd *)
        left; done.
      apply Hhdlhs; left; done.
      apply Htl_power; left; done.
      apply Htl_term; left; done.
    - (* in cs_tl' or c_hd *)
      assert (Hcs_tl' : exists c : Constraint1,
        List.In c
          (List.map
            (fun temp_c : Constraint1 =>
              substitute_constraint c_hd hd 
                (rhs_terms1 temp_c) (rhs_const1 temp_c)) cs_tl') /\
        satisfies_constraint1 valuation c = false) by (exists c; done).
      clear H0.
      apply H in Hcs_tl'; clear H; try done.
      destruct Hcs_tl'.
      - (* is c_hd *)
        left; done.
      - (* in cs_tl' *)
        right.
        destruct H as [c0 [Hin0 Hunsat0]].
        exists c0; split; try right; try done.
      intros; apply Hhdlhs; right; done.
      intros; apply Htl_power; right; done.
      intros; apply Htl_term; right; done.
Qed.

Lemma substitute_hds_2_cs valuation hd : forall cs_hd cs_tl, 
  (forall c, List.In c cs_hd -> lhs_var1 c = hd) ->
  (forall c, List.In c cs_hd -> rhs_power c = []) ->
  (forall c, List.In c cs_tl -> rhs_power c = []) ->
  (forall c, List.In c cs_hd -> good_terms (rhs_terms1 c)) -> 
  (forall c, List.In c cs_tl -> good_terms (rhs_terms1 c)) -> 
  (exists (c : Constraint1), List.In c (flat_map (fun c0 : Constraint1 => List.map
    (fun temp_c : Constraint1 =>
      substitute_constraint temp_c hd (rhs_terms1 c0) (rhs_const1 c0)) cs_tl) cs_hd) /\ 
  satisfies_constraint1 valuation c = false) -> forallb (fun c0 => (hd == (lhs_var1 c0))) cs_hd -> forallb (fun c0 : Constraint1 => hd != lhs_var1 c0) cs_tl ->
  (exists c, List.In c cs_hd /\ satisfies_constraint1 valuation c = false) \/ (exists c, List.In c cs_tl /\ satisfies_constraint1 valuation c = false).
Proof.
  elim. 
  - simpl; intros; try done.
    intuition.
  - simpl; intros c_hd cs_hd' H cs_tl Hhdlhs Hhd_power Htl_power Hhd_term Htl_term. intros.
    destruct H0 as [c [Hin Hunsat]].
    apply in_app_or in Hin. 
    destruct Hin. 
    - (* in c_hd or cs_tl *)
      clear H.
      assert (Hc_hd : exists (c : Constraint1), List.In c (List.map
        (fun temp_c : Constraint1 =>
          substitute_constraint temp_c hd (rhs_terms1 c_hd) (rhs_const1 c_hd)) cs_tl) /\ 
      satisfies_constraint1 valuation c = false) by (exists c; intuition).
      clear H0 Hunsat.
      apply substitute_hd_2_cs in Hc_hd; try done.
      destruct Hc_hd.
      - (* is c_hd *)
        left; exists c_hd; split; try left; try done.
      - (* in cs_tl *)
        right; done.
      move /andP : H1 => [H1 _].
      move /eqP : H1 => H1; symmetry; done.
      apply Hhd_power; left; done.
      apply Hhd_term; left; done.

    - (* in cs_hd' or cs_tl *)
      move /andP : H1 => [_ H1].
      apply (H cs_tl) in H2; try done.
      destruct H2.
      - (* in cs_hd'*)
        destruct H2 as [c0 [Hin0 Hunsat0]].
        left; exists c0; split; try right; try done.
      - (* in cs_tl*)
        destruct H2 as [c0 H2].
        right; exists c0; try done.
      intros; apply Hhdlhs; right; done.
      intros; apply Hhd_power; right; done.
      intros; apply Hhd_term; right; done.
      exists c; try done.
Qed.

Lemma substitute_v_good_terms (a : ProdVar.t) (cl cl' res : list Constraint1) : 
  (forall c : Constraint1, List.In c cl -> good_terms (rhs_terms1 c)) ->
  (forall c : Constraint1, List.In c cl' -> good_terms (rhs_terms1 c)) ->
    res =
  flat_map
    (fun c0 : Constraint1 =>
    List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a (rhs_terms1 c0) (rhs_const1 c0))
      cl') cl ->
  (forall c : Constraint1, List.In c res -> good_terms (rhs_terms1 c)).
Proof.
  intros Hterm1 Hterm2 Heqres; intros; rewrite flat_map_concat_map in Heqres.  
  rewrite Heqres in H; clear Heqres.
  apply in_concat in H.
  destruct H as [cl0 [Hin0 Hin]].
  apply in_map_iff in Hin0.
  destruct Hin0 as [c0 [Hin1 Hsub]].
  rewrite -Hin1 in Hin; clear Hin1.
  apply in_map_iff in Hin.
  destruct Hin as [c1 [Hsub0 Hin1]].
  rewrite -Hsub0 /substitute_constraint; simpl.
  case Hfind : (List.find (fun p : term => p.2 == a) (rhs_terms1 c1)) => [[coe var]|]; try done.
  * simpl. apply substitute_good_terms; try done. apply good_terms_remove. move : Hin1; apply Hterm2. move : Hsub; apply Hterm1.
    apply Hterm2 in Hin1. rewrite /good_terms in Hin1. apply find_some in Hfind. move : Hfind.1. apply Hin1.1.
  * apply Hterm2; done.
Qed.

Lemma substitute_v_power (a : ProdVar.t) (cl cl' res : list Constraint1) : 
  (forall c : Constraint1, List.In c cl' -> rhs_power c = []) -> 
  res =
  flat_map
    (fun c0 : Constraint1 =>
    List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a (rhs_terms1 c0) (rhs_const1 c0))
      cl') cl ->
  (forall c : Constraint1, List.In c res -> rhs_power c = []).
Proof.
  intros Hpower1 Heqres; rewrite flat_map_concat_map in Heqres.
  intros; rewrite Heqres in H; clear Heqres.
  apply in_concat in H.
  destruct H as [cl0 [Hin0 Hin]].
  apply in_map_iff in Hin0.
  destruct Hin0 as [c0 [Hin1 Hsub]].
  rewrite -Hin1 in Hin; clear Hin1.
  apply in_map_iff in Hin.
  destruct Hin as [c1 [Hsub0 Hin1]].
  rewrite -Hsub0.
  assert (forall c v terms cst, rhs_power c = [] -> rhs_power (substitute_constraint c v terms cst) = []).
    intros; rewrite /substitute_constraint.
    case Hfind : (List.find (fun p : term => p.2 == v) (rhs_terms1 c2)) => [[coe v']|]; simpl; try done.
  apply H. apply Hpower1; done.
Qed.

Lemma substitute_v_no_hd (a a0 : ProdVar.t) (cl cl' res : list Constraint1) : 
  (forall c : Constraint1, List.In c cl' -> a != lhs_var1 c) -> 
  res =
  flat_map
    (fun c0 : Constraint1 =>
    List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a0 (rhs_terms1 c0) (rhs_const1 c0))
      cl') cl ->
  forallb (fun c0 : Constraint1 => a != lhs_var1 c0) res.
Proof.
  intros Hnotin Heqres. rewrite flat_map_concat_map in Heqres.
  apply forallb_forall; intros; rewrite Heqres in H; clear Heqres.
  apply in_concat in H;
  destruct H as [cl0 [Hin0 Hin]];
  apply in_map_iff in Hin0;
  destruct Hin0 as [c0 [Hin1 Hsub]];
  rewrite -Hin1 in Hin; clear Hin1;
  apply in_map_iff in Hin;
  destruct Hin as [c1 [Hsub0 Hin1]];
  rewrite -Hsub0.
  rewrite /substitute_constraint.
  case Hfind : (List.find (fun p : term => p.2 == a0) (rhs_terms1 c1)) => [[coe var]|]; simpl.
  1,2 : apply Hnotin; done.
Qed.

Lemma preprocess_tbreplace1_good_terms (a : ProdVar.t) : forall cs1 (c : Constraint1),
  (forall c0 : Constraint1, List.In c0 cs1 -> good_terms (rhs_terms1 c0)) ->
  In c (preprocess_tbreplace1 a cs1) -> good_terms (rhs_terms1 c).
Proof.
  rewrite /preprocess_tbreplace1; intros cs1 c Hterm H.
  case Hfind : (find
    (fun c : Constraint1 =>
    (Datatypes.length (rhs_terms1 c) == 1) &&
    ((hd (0, (0%N, 0%N)) (rhs_terms1 c)).2 == a)) cs1) => [temp_c|]; rewrite Hfind in H. 
  case H1 : (rhs_terms1 temp_c) => [|[n hd] l]; rewrite H1 in H; try done.
  case H2 : n => [|n0]; rewrite H2 in H; simpl in H; try done.
  case H3 : l; rewrite H3 in H; try done.
  case H3 : n0 => [|n1]; rewrite H3 in H; simpl in H; try done.
  case H4 : l; rewrite H4 in H; try done.
  case H5 : (rhs_const1 temp_c <=? 0)%Z; rewrite H5 in H; try done.
  move : H; apply Hterm.
  case H4 : l; rewrite H4 in H; try done.
  apply in_map_iff in H.
  destruct H as [c0 [Hsub Hin]].
  rewrite -Hsub /substitute_constraint; simpl.
  case Hfind0 : (List.find (fun p : term => p.2 == hd) (rhs_terms1 temp_c)) => [[coe var]|]; try done.
  * simpl. apply substitute_good_terms; try done. apply good_terms_remove. apply find_some in Hfind. move : Hfind.1. apply Hterm.
    move : Hin; apply Hterm. rewrite /good_terms in Hterm. apply find_some in Hfind0. move : Hfind0.1. 
    apply find_some in Hfind. move : Hfind => [Hfind _]. apply Hterm in Hfind. apply Hfind.1.
  * apply find_some in Hfind. move : Hfind.1. apply Hterm.
    move : H; apply Hterm.
Qed.

Lemma preprocess_tbreplace2_good_terms (a : ProdVar.t) : forall cs1 (c : Constraint1),
  (forall c0 : Constraint1, List.In c0 cs1 -> good_terms (rhs_terms1 c0)) ->
  In c (preprocess_tbreplace2 a cs1) -> good_terms (rhs_terms1 c).
Proof.
  rewrite /preprocess_tbreplace2; intros cs1 c Hterm H.
  case Hfind : (find
    (fun c : Constraint1 =>
    (1 < Datatypes.length (rhs_terms1 c)) &&
    in_bool a (split (rhs_terms1 c)).2) cs1) => [temp_c|]; rewrite Hfind in H.
  simpl in H. destruct H. 
  * rewrite -H /substitute_constraint; simpl.
    case Hfind0 : (List.find (fun p : term => p.2 == a) (rhs_terms1 temp_c)) => [[coe var]|]; try done.
    - simpl. apply substitute_good_terms; try done. apply good_terms_remove. apply find_some in Hfind. move : Hfind.1. apply Hterm.
      apply find_some in Hfind. move : Hfind.1; apply Hterm.
      rewrite /good_terms in Hterm. apply find_some in Hfind0. move : Hfind0.1. apply find_some in Hfind. 
      move : Hfind => [Hfind _]. apply Hterm in Hfind. apply Hfind.1.
    - apply find_some in Hfind. move : Hfind.1. apply Hterm.
      move : H; apply Hterm.
      move : H; apply Hterm.
Qed.

Lemma preprocess_tbreplace_good_terms (a : ProdVar.t) : forall cs1 (c : Constraint1),
  (forall c0 : Constraint1, List.In c0 cs1 -> good_terms (rhs_terms1 c0)) ->
  In c (preprocess_tbreplace a cs1) -> good_terms (rhs_terms1 c).
Proof.
  rewrite /preprocess_tbreplace.
  intros. move : H0; apply preprocess_tbreplace2_good_terms.
  intro c0. apply preprocess_tbreplace1_good_terms; done.
Qed.

Lemma preprocess_tbreplace1_lhs (a : ProdVar.t) : forall cs1 (c : Constraint1),
  (forall c0 : Constraint1, List.In c0 cs1 -> lhs_var1 c0 = a) ->
  In c (preprocess_tbreplace1 a cs1) -> lhs_var1 c = a.
Proof.
  rewrite /preprocess_tbreplace1; intros.
  case Hfind : (find
    (fun c : Constraint1 =>
    (Datatypes.length (rhs_terms1 c) == 1) &&
    ((hd (0, (0%N, 0%N)) (rhs_terms1 c)).2 == a)) cs1) => [temp_c|]; rewrite Hfind in H0. 
  case H1 : (rhs_terms1 temp_c) => [|[n hd] l]; rewrite H1 in H0; try done.
  case H2 : n => [|n0]; rewrite H2 in H0; simpl in H0; try done.
  case H3 : l; rewrite H3 in H0; try done.
  case H3 : n0 => [|n1]; rewrite H3 in H0; simpl in H0; try done.
  case H4 : l; rewrite H4 in H0; try done.
  case H5 : (rhs_const1 temp_c <=? 0)%Z; rewrite H5 in H0; try done.
  move : H0; apply H.
  case H4 : l; rewrite H4 in H0; try done.
  apply in_map_iff in H0.
  destruct H0 as [c0 [Hsub Hin]].
  rewrite -Hsub /substitute_constraint; simpl.
  case Hfind0 : (List.find (fun p : term => p.2 == hd) (rhs_terms1 temp_c)) => [[coe var]|]; simpl; try done.
  1,2 : apply find_some in Hfind; move : Hfind.1; apply H.
  move : H0; apply H.
Qed.

Lemma preprocess_tbreplace2_lhs (a : ProdVar.t) : forall cs1 (c : Constraint1),
  (forall c0 : Constraint1, List.In c0 cs1 -> lhs_var1 c0 = a) ->
  In c (preprocess_tbreplace2 a cs1) -> lhs_var1 c = a.
Proof.
  rewrite /preprocess_tbreplace2; intros.
  case Hfind : (find
    (fun c : Constraint1 =>
    (1 < Datatypes.length (rhs_terms1 c)) &&
    in_bool a (split (rhs_terms1 c)).2) cs1) => [temp_c|]; rewrite Hfind in H0.
  simpl in H0. destruct H0. 
  * rewrite -H0 /substitute_constraint; simpl.
    case Hfind0 : (List.find (fun p : term => p.2 == a) (rhs_terms1 temp_c)) => [[coe var]|]; simpl; try done.
  1,2 : apply find_some in Hfind; move : Hfind.1; apply H.
  1,2 : move : H0; apply H.
Qed.

Lemma preprocess_tbreplace_lhs (a : ProdVar.t) : forall cs1 (c : Constraint1),
  (forall c0 : Constraint1, List.In c0 cs1 -> lhs_var1 c0 = a) ->
  In c (preprocess_tbreplace a cs1) -> lhs_var1 c = a.
Proof.
  rewrite /preprocess_tbreplace.
  intros. move : H0; apply preprocess_tbreplace2_lhs.
  intro c0. apply preprocess_tbreplace1_lhs; done.
Qed.

Lemma preprocess_tbreplace1_power (a : ProdVar.t) : forall cs1 (c : Constraint1),
  (forall c0 : Constraint1, List.In c0 cs1 -> rhs_power c0 = []) ->
  In c (preprocess_tbreplace1 a cs1) -> rhs_power c = [].
Proof.
  rewrite /preprocess_tbreplace1; intros.
  case Hfind : (find
    (fun c : Constraint1 =>
    (Datatypes.length (rhs_terms1 c) == 1) &&
    ((hd (0, (0%N, 0%N)) (rhs_terms1 c)).2 == a)) cs1) => [temp_c|]; rewrite Hfind in H0. 
  case H1 : (rhs_terms1 temp_c) => [|[n hd] l]; rewrite H1 in H0; try done.
  case H2 : n => [|n0]; rewrite H2 in H0; simpl in H0; try done.
  case H3 : l; rewrite H3 in H0; try done.
  case H3 : n0 => [|n1]; rewrite H3 in H0; simpl in H0; try done.
  case H4 : l; rewrite H4 in H0; try done.
  case H5 : (rhs_const1 temp_c <=? 0)%Z; rewrite H5 in H0; try done.
  move : H0; apply H.
  case H4 : l; rewrite H4 in H0; try done.
  apply in_map_iff in H0.
  destruct H0 as [c0 [Hsub Hin]].
  rewrite -Hsub /substitute_constraint; simpl.
  case Hfind0 : (List.find (fun p : term => p.2 == hd) (rhs_terms1 temp_c)) => [[coe var]|]; simpl; try done.
  apply find_some in Hfind; move : Hfind.1; apply H.
  move : H0; apply H.
Qed.

Lemma preprocess_tbreplace2_power (a : ProdVar.t) : forall cs1 (c : Constraint1),
  (forall c0 : Constraint1, List.In c0 cs1 -> rhs_power c0 = []) ->
  In c (preprocess_tbreplace2 a cs1) -> rhs_power c = [].
Proof.
  rewrite /preprocess_tbreplace2; intros.
  case Hfind : (find
    (fun c : Constraint1 =>
    (1 < Datatypes.length (rhs_terms1 c)) &&
    in_bool a (split (rhs_terms1 c)).2) cs1) => [temp_c|]; rewrite Hfind in H0.
  simpl in H0. destruct H0. 
  * rewrite -H0 /substitute_constraint; simpl.
    case Hfind0 : (List.find (fun p : term => p.2 == a) (rhs_terms1 temp_c)) => [[coe var]|]; simpl; try done.
  apply find_some in Hfind; move : Hfind.1; apply H.
  1,2 : move : H0; apply H.
Qed.

Lemma preprocess_tbreplace_power (a : ProdVar.t) : forall cs1 (c : Constraint1),
  (forall c0 : Constraint1, List.In c0 cs1 -> rhs_power c0 = []) ->
  In c (preprocess_tbreplace a cs1) -> rhs_power c = [].
Proof.
  rewrite /preprocess_tbreplace.
  intros. move : H0; apply preprocess_tbreplace2_power.
  intro c0. apply preprocess_tbreplace1_power; done.
Qed.

Lemma preprocess_tbreplace1_correctness valuation : forall a cs, 
  (forall c : Constraint1, In c cs -> lhs_var1 c = a) ->
  (forall c : Constraint1, In c cs -> rhs_power c = []) ->
  (forall c : Constraint1, In c cs -> good_terms (rhs_terms1 c)) ->
  (exists c : Constraint1, In c (preprocess_tbreplace1 a cs) /\ satisfies_constraint1 valuation c = false) -> 
  (exists c : Constraint1, In c cs /\ satisfies_constraint1 valuation c = false).
Proof.
  intros a cs Hlhs Hpower Hterm; intros. rewrite /preprocess_tbreplace1 in H. 
  case Hfind : (find
    (fun c0 : Constraint1 =>
    (Datatypes.length (rhs_terms1 c0) == 1) &&
    ((hd (0, (0%N, 0%N)) (rhs_terms1 c0)).2 == a)) cs) => [temp_c|]; rewrite Hfind in H; try done.
  case H1 : (rhs_terms1 temp_c) => [|[n hd] l]; rewrite H1 in H; try done. destruct H as [c [Hin _]]; try done.
  case H2 : n => [|n0]; rewrite H2 in H; simpl in H; try done.
  case H3 : l; rewrite H3 in H; destruct H as [c [Hin _]]; try done.
  case H3 : n0 => [|n1]; rewrite H3 in H; simpl in H; try done.
  case H4 : l; rewrite H4 in H; try done.
  case H5 : (rhs_const1 temp_c <=? 0)%Z; rewrite H5 in H; try done. destruct H as [c [Hin _]]; try done. destruct H as [c [Hin _]]; try done.
  case H4 : l; rewrite H4 in H; try done. 2 : destruct H as [c [Hin _]]; try done.
  apply substitute_hds_2_c in H; try done. destruct H; try done.
  - apply find_some in Hfind. exists temp_c; split; try done. exact Hfind.1.
  apply find_some in Hfind. move : Hfind => [Hin Hlength]. move /andP : Hlength => [Hlength Hhd].
  rewrite H1 in Hhd; simpl in Hhd. move /eqP : Hhd => Hhd; subst. done.
  apply find_some in Hfind. move : Hfind.1. apply Hpower.
  apply find_some in Hfind. move : Hfind.1. apply Hterm.
Qed.

Lemma preprocess_tbreplace2_correctness valuation : forall a cs, 
  (forall c : Constraint1, In c cs -> lhs_var1 c = a) ->
  (forall c : Constraint1, In c cs -> rhs_power c = []) ->
  (forall c : Constraint1, In c cs -> good_terms (rhs_terms1 c)) ->
  (exists c : Constraint1, In c (preprocess_tbreplace2 a cs) /\ satisfies_constraint1 valuation c = false) -> 
  (exists c : Constraint1, In c cs /\ satisfies_constraint1 valuation c = false).
Proof.
  intros a cs Hlhs Hpower Hterm; intros. rewrite /preprocess_tbreplace2 in H. 
  case Hfind : (find
    (fun c0 : Constraint1 =>
    (1 < Datatypes.length (rhs_terms1 c0)) &&
    in_bool a (split (rhs_terms1 c0)).2) cs) => [temp_c|]; rewrite Hfind in H; try done.
  destruct H as [c [Hin Hsub]]; simpl in Hin. destruct Hin; try done. 2: exists c; split; try done.
  rewrite -H in Hsub.
  apply substitute_hd_2_c in Hsub; try done. destruct Hsub.
  1,2 : apply find_some in Hfind. 1,2 : exists temp_c; split; try done. 1,2 :  exact Hfind.1.
  apply find_some in Hfind. move : Hfind.1. apply Hlhs.
  1,2 : apply find_some in Hfind; move : Hfind.1; apply Hpower.
  1,2 : apply find_some in Hfind; move : Hfind.1; apply Hterm.
Qed.

Lemma preprocess_tbreplace_correctness valuation : forall a cs, 
  (forall c : Constraint1, In c cs -> lhs_var1 c = a) ->
  (forall c : Constraint1, In c cs -> rhs_power c = []) ->
  (forall c : Constraint1, In c cs -> good_terms (rhs_terms1 c)) ->
  (exists c : Constraint1, In c (preprocess_tbreplace a cs) /\ satisfies_constraint1 valuation c = false) -> 
  (exists c : Constraint1, In c cs /\ satisfies_constraint1 valuation c = false).
Proof.
  intros. rewrite /preprocess_tbreplace in H. apply preprocess_tbreplace2_correctness in H2; try done.
  move : H2; apply preprocess_tbreplace1_correctness; try done.
  intro c; apply (preprocess_tbreplace1_lhs _ _ H).
  intro c; apply (preprocess_tbreplace1_power _ _ _ H0).
  intro c; apply (preprocess_tbreplace1_good_terms _ _ _ H1).
Qed.

Lemma substitute_correctness valuation : forall cl vl,
  (forall c, List.In c cl -> rhs_power c = []) ->
  (forall c, List.In c cl -> good_terms (rhs_terms1 c)) -> 
  (exists c, List.In c (substitute_vs vl cl) /\ satisfies_constraint1 valuation c = false) ->
  exists c', List.In c' cl /\ satisfies_constraint1 valuation c' = false.
Proof.
  intros cl vl; move : vl cl. 
  elim. 
  - simpl; intros; done.
  - simpl; intros a l H cl Hpower Hterm H0.
    destruct (partition (fun c0 : Constraint1 => a == lhs_var1 c0) cl) as [cs_hd cs_tl] eqn : Hpart.
    remember ((flat_map
        (fun c0 : Constraint1 =>
          List.map
            (fun temp_c : Constraint1 =>
            substitute_constraint temp_c a (rhs_terms1 c0) (rhs_const1 c0))
            cs_tl) (preprocess_tbreplace a cs_hd))) as res.

    assert (Htl_power : forall c : Constraint1, List.In c (List.filter (fun c1 : Constraint1 => a != lhs_var1 c1) cl) -> rhs_power c = []) by (intros; apply Hpower; apply filter_In in H1; exact H1.1).
    assert (Hhd_power : forall c : Constraint1, List.In c (find_constraint1s a cl) -> rhs_power c = []) by (rewrite /find_constraint1s; intros; apply Hpower; apply filter_In in H1; exact H1.1).
    assert (Htl_term : forall c : Constraint1, List.In c (List.filter (fun c1 : Constraint1 => a != lhs_var1 c1) cl) -> good_terms (rhs_terms1 c)) by (intros; apply Hterm; apply filter_In in H1; exact H1.1).
    assert (Hhd_term : forall c : Constraint1, List.In c (find_constraint1s a cl) -> good_terms (rhs_terms1 c)) by (rewrite /find_constraint1s; intros; apply Hterm; apply filter_In in H1; exact H1.1).
    assert (Hres_power : forall c : Constraint1, List.In c res -> rhs_power c = []) by
      (rewrite partition_as_filter in Hpart; inversion Hpart; rewrite -H3 in Heqres; apply (substitute_v_power a (preprocess_tbreplace a cs_hd) _ Htl_power Heqres)).
    assert (Hres_term : forall c : Constraint1, List.In c res -> good_terms (rhs_terms1 c)).
      move : Heqres; apply substitute_v_good_terms. intro c; apply preprocess_tbreplace_good_terms.
      1, 2 : intros; apply Hterm. 1,2 : rewrite partition_as_filter in Hpart; inversion Hpart. 
      rewrite -H3 in H1; apply filter_In in H1; exact H1.1.
      rewrite -H4 in H1; apply filter_In in H1; exact H1.1.

    (*case Hl : l => [|l0 l1]; rewrite Hl in H0.
    * (* l = [] *)
      case Hgt1 : (List.existsb
        (fun c0 : Constraint1 =>
        match List.find (fun p : term => p.2 == lhs_var1 c0) (rhs_terms1 c0) with
        | Some t => let (coe, _) := t in 1 < coe
        | None => false
        end) res); rewrite Hgt1 in H0.
      + (* 不需要再次代入 *)
        rewrite Hl in H; clear Hl l. 
        simpl in H. 
        apply H in H0; clear H; try done.
        rewrite Heqres in H0.
        apply substitute_hds_2_cs in H0.
        destruct H0.
        - (* in hd_cs *)
          destruct H as [c [Hin Hunsat]].
          rewrite /find_constraint1s in Hin. 
          apply filter_In in Hin. 
          intuition.
          exists c; try done.
        - (* in tl_cs *)
          destruct H as [c [Hin Hunsat]].
          apply filter_In in Hin. 
          intuition.
          exists c; try done.
        rewrite /find_constraint1s; intros.
        apply filter_In in H; move /eqP : H.2 => H'; rewrite H' //.
        1,2 : intros; apply filter_In in H; move : H.1; apply Hpower. 
        1,2 : intros; apply filter_In in H; move : H.1; apply Hterm.
        1,2 : rewrite /find_constraint1s; apply forallb_forall; intros.
        1,2 : intros; apply filter_In in H; apply H.2.

      + rewrite Hl in H; clear Hl l. 
        simpl in H. 
        remember ((flat_map
          (fun c0 : Constraint1 =>
            List.map
              (fun temp_c : Constraint1 =>
              substitute_constraint temp_c a (rhs_terms1 c0) (rhs_const1 c0)) res)
          (find_constraint1s a cl))) as res'.
        apply H in H0; try done.
        rewrite Heqres' in H0.
        apply substitute_hds_2_cs in H0; try done.
        destruct H0.
        - (* in hd_cs *)
          destruct H0 as [c [Hin Hunsat]].
          rewrite /find_constraint1s in Hin. 
          apply filter_In in Hin. 
          intuition.
          exists c; try done.
        - (* in tl_cs' *)
          apply H in H0; clear H; try done.
          rewrite Heqres in H0.
          apply substitute_hds_2_cs in H0.
          destruct H0.
          * destruct H as [c [Hin Hunsat]].
            rewrite /find_constraint1s in Hin. 
            apply filter_In in Hin. 
            intuition.
            exists c; try done.
          * destruct H as [c [Hin Hunsat]].
            apply filter_In in Hin. 
            intuition.
            exists c; try done.
          rewrite /find_constraint1s; intros.
          apply filter_In in H; move /eqP : H.2 => H'; rewrite H' //.
          1,2 : intros; apply filter_In in H; move : H.1; apply Hpower.
          1,2 : intros; apply filter_In in H; move : H.1; apply Hterm.
          1,2 : rewrite /find_constraint1s; apply forallb_forall; intros.
          1,2 : intros; apply filter_In in H; apply H.2.

        clear H.
        rewrite /find_constraint1s; intros.
        apply filter_In in H; move /eqP : H.2 => H'; rewrite H' //.
        clear H; rewrite /find_constraint1s; apply forallb_forall; intros.
        intros; apply filter_In in H; apply H.2.
        (* no lhs after substitute *)
        move : Heqres; apply substitute_v_no_hd. intros; apply filter_In in H1; exact H1.2.
        (* res' power *)
        move : Heqres'; apply substitute_v_power; try done.
        (* res' good_terms *)
        move : Heqres'; apply substitute_v_good_terms; try done.

    * (* l <> [] *)
      rewrite -Hl in H0; clear Hl l0 l1.*)
      rewrite partition_as_filter in Hpart. inversion Hpart; clear Hpart.
      apply H in H0; clear H; try done.
      rewrite Heqres in H0.
      apply substitute_hds_2_cs in H0.
      destruct H0.
      - (* in hd_cs *)
        (*destruct H as [c [Hin Hunsat]].
        rewrite /find_constraint1s in Hin. 
        apply filter_In in Hin. 
        intuition.
        exists c; try done.*) 
        apply preprocess_tbreplace_correctness in H; try done.
        + destruct H as [c [Hin Hunsat]]. rewrite -H2 in Hin; apply filter_In in Hin. exists c; split; try done. exact Hin.1.
        + intros. rewrite -H2 in H0; apply filter_In in H0. move /eqP : H0.2 => H1. rewrite H1 //.
        + intros. apply Hpower. rewrite -H2 in H0; apply filter_In in H0. exact H0.1.
        + intros. apply Hterm. rewrite -H2 in H0; apply filter_In in H0. exact H0.1.
      - (* in tl_cs *)
        destruct H as [c [Hin Hunsat]].
        rewrite -H3 in Hin; apply filter_In in Hin. 
        intuition.
        exists c; try done.

      move : H2; clear; intros; rewrite /preprocess_tbreplace /preprocess_tbreplace2 in H.
        case Hfind : (find
          (fun c : Constraint1 =>
          (1 < Datatypes.length (rhs_terms1 c)) &&
          in_bool a (split (rhs_terms1 c)).2)
          (preprocess_tbreplace1 a cs_hd)) => [temp_c|]; rewrite Hfind in H. simpl in H. destruct H.
        + rewrite -H /substitute_constraint.
          case Hfind0 : (find (fun p : term => p.2 == a) (rhs_terms1 temp_c)) => [[coe var]|]; simpl.
          1,2 : apply find_some in Hfind; move : Hfind.1; apply preprocess_tbreplace1_lhs; intros; rewrite -H2 in H0; apply filter_In in H0; move /eqP : H0.2 => H1; rewrite H1 //.
          1,2 : move : H; apply preprocess_tbreplace1_lhs; intros; rewrite -H2 in H; apply filter_In in H; move /eqP : H.2 => H1; rewrite H1 //.
        + intro c; apply preprocess_tbreplace_power. 1,2 : intros; apply Hpower.
          rewrite -H2 in H; apply filter_In in H; exact H.1.
          rewrite -H3 in H; apply filter_In in H; exact H.1.
        + intro c; apply preprocess_tbreplace_good_terms. 1,2 : intros; apply Hterm.
          rewrite -H2 in H; apply filter_In in H; exact H.1.
          rewrite -H3 in H; apply filter_In in H; exact H.1.
        + 1,2 : apply forallb_forall. intros; apply (introT eqP). symmetry; move : H; apply preprocess_tbreplace_lhs. intros. rewrite -H2 in H; apply filter_In in H. move /eqP : H.2 => H1. rewrite H1 //.
        + intros; rewrite -H3 in H. apply filter_In in H. exact H.2.
      (*rewrite /find_constraint1s; intros.
      apply filter_In in H; move /eqP : H.2 => H'; rewrite H' //.
      1,2 : intros; apply filter_In in H; move : H.1; apply Hpower.
      1,2 : intros; apply filter_In in H; move : H.1; apply Hterm.
      1,2 : rewrite /find_constraint1s; apply forallb_forall; intros.
      1,2 : intros; apply filter_In in H; apply H.2.*)
Qed.

(*Lemma solve_ubs_in_cs cs1 ls : forall tbsolved ubs, solve_ubs tbsolved ls cs1 = Some ubs ->
  forall var, List.In var (constraints1_vars cs1) -> PVM.mem var ubs.
Proof.
  (* TBD *)
Admitted.*)

Lemma solve_ubs_tbsolved_in cs1 ls : forall tbsolved ubs, solve_ubs tbsolved ls cs1 = Some ubs ->
  forall var, List.In var tbsolved <-> PVM.mem var ubs.
Proof.
  elim. simpl; intros. inversion H; rewrite /initial_valuation. split; try done.
  simpl; intros. split.
  - intros. case Hub : (solve_ub a ls cs1) => [n|]; rewrite Hub in H0; try discriminate.
    case Hubs : (solve_ubs l ls cs1) => [nv|]; rewrite Hubs in H0; try discriminate. inversion H0. destruct H1.
    * subst. rewrite /add_valuation. apply add_mem.
    * specialize (H _ Hubs). apply H in H1. move : H1; apply mem_add.
  - intros. case Hub : (solve_ub a ls cs1) => [n|]; rewrite Hub in H0; try discriminate.
    case Hubs : (solve_ubs l ls cs1) => [nv|]; rewrite Hubs in H0; try discriminate. inversion H0.
    specialize (H _ Hubs). rewrite -H3 /add_valuation in H1. apply mem_add_or in H1. destruct H1.
    * right; move : H1; apply H; done.
    * left. move /eqP : H1 => H1. rewrite H1 //.
Qed.

Lemma substitute_vs_no_hd (a : ProdVar.t) : forall l cl, forallb (fun c0 : Constraint1 => a != lhs_var1 c0) cl -> (forall c, List.In c (substitute_vs l cl) -> a != lhs_var1 c).
Proof.
  elim.
  - simpl; intros. move : c H0; apply forallb_forall. done.
  - simpl; intros. (*case Hl : l => [|x y]; rewrite Hl in H1.
    * remember (flat_map
        (fun c : Constraint1 =>
        map
          (fun temp_c : Constraint1 =>
          substitute_constraint temp_c a0 (rhs_terms1 c) (rhs_const1 c))
          cs_tl) (preprocess_tbreplace a0 cs_hd)) as res.
      case Hagain : (List.existsb
        (fun c : Constraint1 =>
        match List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c) with
        | Some t => let (coe, _) := t in 1 < coe
        | None => false
        end) res); rewrite Hagain in H1. apply (substitute_v_no_hd a) in Heqres.
      move : Heqres H1; clear. intro H; move : c. apply forallb_forall; done.
      intros; apply filter_In in H2. move : H0 H2.1; clear. intro H; move : c0; apply forallb_forall; done.
      remember (flat_map
        (fun c : Constraint1 =>
        List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a0 (rhs_terms1 c) (rhs_const1 c))
          res) (find_constraint1s a0 cl)) as res'. apply (substitute_v_no_hd a) in Heqres'.
      move : Heqres' H1; clear. intro H; move : c. apply forallb_forall; done.
      apply (substitute_v_no_hd a) in Heqres. apply forallb_forall; done.
      intros; apply filter_In in H2. move : H0 H2.1; clear. intro H; move : c0; apply forallb_forall; done.*)
    * destruct (partition (fun c : Constraint1 => a0 == lhs_var1 c) cl) as [cs_hd cs_tl] eqn : Hpart.
      move : H1; apply H.
      apply forallb_forall. intros.
      remember (flat_map
        (fun c0 : Constraint1 =>
        map
          (fun temp_c : Constraint1 =>
            substitute_constraint temp_c a0 (rhs_terms1 c0) (rhs_const1 c0))
          cs_tl) (preprocess_tbreplace a0 cs_hd)) as res.
      apply (substitute_v_no_hd a) in Heqres.
      move : Heqres H1; clear. intro H; move : x. apply forallb_forall; done.
      rewrite partition_as_filter in Hpart. inversion Hpart. move : H0; clear. intros. apply filter_In in H. move : H.1. clear H; move : c. apply forallb_forall; done.
Qed.

Lemma substitute_v_in_vl a vl (cl cl' res : list Constraint1) : 
  (forall c : Constraint1, List.In c cl' -> List.In (lhs_var1 c) vl) ->
    res =
  flat_map
    (fun c0 : Constraint1 =>
    List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a (rhs_terms1 c0) (rhs_const1 c0))
      cl') cl ->
  (forall c : Constraint1, List.In c res -> List.In (lhs_var1 c) vl).
Proof.
  intros Hinvl Heqres; intros; rewrite flat_map_concat_map in Heqres.  
  rewrite Heqres in H; clear Heqres.
  apply in_concat in H.
  destruct H as [cl0 [Hin0 Hin]].
  apply in_map_iff in Hin0.
  destruct Hin0 as [c0 [Hin1 Hsub]].
  rewrite -Hin1 in Hin; clear Hin1.
  apply in_map_iff in Hin.
  destruct Hin as [c1 [Hsub0 Hin1]].
  rewrite -Hsub0 /substitute_constraint; simpl.
  case Hfind : (List.find (fun p : term => p.2 == a) (rhs_terms1 c1)) => [[coe var]|]; try done.
  * simpl. apply Hinvl; done.
  * simpl. apply Hinvl; done.
Qed.

Lemma substitute_vs_in_vl vl : forall l cl, vl <> [] ->
  (forall c : Constraint1, List.In c cl -> List.In (lhs_var1 c) vl) ->
  (forall c, List.In c (substitute_vs l cl) -> List.In (lhs_var1 c) vl).
Proof.
  elim.
  - simpl; intros; apply H0; done.
  - simpl; intros a l H cl H2; intros. (*case Hl : l => [|x y]; rewrite Hl in H1.
    * destruct (partition (fun c : Constraint1 => a == lhs_var1 c) cl) as [cs_hd cs_tl] eqn : Hpart.
      remember (flat_map
        (fun c : Constraint1 =>
        map
          (fun temp_c : Constraint1 =>
            substitute_constraint temp_c a (rhs_terms1 c) (rhs_const1 c))
          cs_tl) (preprocess_tbreplace a cs_hd)) as res.
      case Hagain : (List.existsb
        (fun c : Constraint1 =>
        match List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c) with
        | Some t => let (coe, _) := t in 1 < coe
        | None => false
        end) res); rewrite Hagain in H1. specialize (substitute_v_in_vl a vl (find_constraint1s a cl) (List.filter (fun c0 : Constraint1 => a != lhs_var1 c0) cl) res); intro.
      move : c H1. apply H3; try done. 
      intros; apply filter_In in H1. apply H0; exact H1.1.
      remember (flat_map
        (fun c : Constraint1 =>
        List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a (rhs_terms1 c) (rhs_const1 c))
          res) (find_constraint1s a cl)) as res'. apply (substitute_v_in_vl a vl _ _ res') with (c := c) in Heqres'; try done.
      intros; apply (substitute_v_in_vl a vl _ _ res) with (c := c0) in Heqres; try done.
      intros; apply filter_In in H4. apply H0; exact H4.1.
    * rewrite -Hl in H1. move : H1; apply H; try done. intros.
      remember (flat_map
        (fun c : Constraint1 =>
        List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a (rhs_terms1 c) (rhs_const1 c))
          (List.filter (fun c0 : Constraint1 => a != lhs_var1 c0) cl)) (find_constraint1s a cl)) as res.*)
    destruct (partition (fun c : Constraint1 => a == lhs_var1 c) cl) as [cs_hd cs_tl] eqn : Hpart.
    remember (flat_map
      (fun c : Constraint1 =>
      map
        (fun temp_c : Constraint1 =>
          substitute_constraint temp_c a (rhs_terms1 c) (rhs_const1 c))
        cs_tl) (preprocess_tbreplace a cs_hd)) as res.
    move : H1; apply H; try done.
    move : Heqres; apply substitute_v_in_vl.
    intros; apply H0. rewrite partition_as_filter in Hpart. inversion Hpart. rewrite -H5 in H1.
    apply filter_In in H1. exact H1.1.
Qed.

Lemma substitute_vs_no_vl : forall (vl : list ProdVar.t) cs1, 
  (forall c : Constraint1, List.In c (substitute_vs vl cs1) -> ~List.In (lhs_var1 c) vl).
Proof.
  elim. 
  - simpl; intros; done.
  - simpl; intros a l IH cs1 c H0. intro Hin. destruct Hin as [H1|H1].
    * (*case Hv : l => [|x y]; rewrite Hv in H0.
      + (* to the end : special case *) 
        remember (flat_map
          (fun c : Constraint1 =>
          List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a (rhs_terms1 c) (rhs_const1 c))
            (List.filter (fun c0 : Constraint1 => a != lhs_var1 c0) cs1)) (find_constraint1s a cs1)) as cl.
        case Hagain : (List.existsb
          (fun c : Constraint1 =>
          match List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c) with
          | Some t => let (coe, _) := t in 1 < coe
          | None => false
          end) cl); rewrite Hagain in H0. 
        apply (substitute_v_no_hd a) in Heqcl; try done.
        assert (forall c : Constraint1, List.In c cl -> a != lhs_var1 c) by (apply forallb_forall; apply Heqcl). apply H in H0. rewrite H1 in H0. move /eqP : H0 => H0; done.
        intros. apply filter_In in H. exact H.2. 
        remember (flat_map
          (fun c : Constraint1 =>
          List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a (rhs_terms1 c) (rhs_const1 c)) cl)
          (find_constraint1s a cs1)) as cl'.
        apply (substitute_v_no_hd a) in Heqcl; try done.
        apply (substitute_v_no_hd a) in Heqcl'; try done.
        assert (forall c : Constraint1, List.In c cl' -> a != lhs_var1 c) by (apply forallb_forall; apply Heqcl'). apply H in H0. rewrite H1 in H0. move /eqP : H0 => H0; done.
        apply forallb_forall; done. intros. apply filter_In in H. exact H.2. *)
      + destruct (partition (fun c : Constraint1 => a == lhs_var1 c) cs1) as [cs_hd cs_tl] eqn : Hpart.
        remember (flat_map
          (fun c : Constraint1 =>
          map
            (fun temp_c : Constraint1 =>
              substitute_constraint temp_c a (rhs_terms1 c) (rhs_const1 c))
            cs_tl) (preprocess_tbreplace a cs_hd)) as cl.
        apply (substitute_v_no_hd a) in Heqcl. apply (substitute_vs_no_hd _ _ _ Heqcl) in H0. rewrite H1 in H0. move /eqP : H0 => H0; done.
        intros. rewrite partition_as_filter in Hpart. inversion Hpart. rewrite -H4 in H. apply filter_In in H. exact H.2.
    * destruct (partition (fun c : Constraint1 => a == lhs_var1 c) cs1) as [cs_hd cs_tl] eqn : Hpart.
      apply IH in H0. done.
Qed.

(*Lemma substitute_vs_is_hd (hd : ProdVar.t) : forall (vl : list ProdVar.t) cs1, 
  vl <> [] ->
  (forall c : Constraint1, List.In c cs1 -> List.In (lhs_var1 c) vl) ->
  forallb (fun c : Constraint1 => lhs_var1 c == hd) (substitute_vs (List.filter (fun p : ProdVar.t => p != hd) vl) cs1).
Proof.
  intros vl cs1 H2; intros; apply forallb_forall; intros. specialize (substitute_vs_no_vl (List.filter (fun p : ProdVar.t => p != hd) vl) _ x H0); intro. 
  apply (substitute_vs_in_vl _ _ H2 H) in H0.
  destruct (lhs_var1 x == hd) eqn : Heq; auto.
  exfalso.
  apply H1.
  apply filter_In.
  split; auto. 
Admitted.*)

Lemma substitute_vs_good_terms (hd : ProdVar.t) : forall (vl : list ProdVar.t) (c : Constraint1) cs1,
  (forall c : Constraint1, List.In c cs1 -> good_terms (rhs_terms1 c)) ->
  List.In c (substitute_vs (List.filter (fun p : ProdVar.t => p != hd) vl) cs1) -> good_terms (rhs_terms1 c).
Proof.
  elim. 
  - simpl; intros. move : H0; apply H. 
  - simpl; intros. case Heq : (a != hd); rewrite Heq in H1. move /eqP : Heq => Heq. 
    * simpl in H1. (*case Hv : (List.filter (fun p : ProdVar.t => p != hd) l) => [|x y]; rewrite Hv in H1.
      + (* to the end : special case *) clear H.
        remember (flat_map
          (fun c : Constraint1 =>
          List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a (rhs_terms1 c) (rhs_const1 c))
            (List.filter (fun c0 : Constraint1 => a != lhs_var1 c0) cs1)) (find_constraint1s a cs1)) as cl.
        case Hagain : (List.existsb
          (fun c : Constraint1 =>
          match List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c) with
          | Some t => let (coe, _) := t in 1 < coe
          | None => false
          end) cl); rewrite Hagain in H1. move : Heqcl c H1; apply substitute_v_good_terms.
          rewrite /find_constraint1s. 1,2 : intros; apply H0; apply filter_In in H; exact H.1.
        remember (flat_map
          (fun c : Constraint1 =>
          List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a (rhs_terms1 c) (rhs_const1 c)) cl)
          (find_constraint1s a cs1)) as cl'.
        move : Heqcl' c H1; apply substitute_v_good_terms.
        rewrite /find_constraint1s; intros; apply H0; apply filter_In in H; exact H.1.
        move : Heqcl; apply substitute_v_good_terms. rewrite /find_constraint1s. 1,2 : intros; apply H0; apply filter_In in H; exact H.1.
      + rewrite -Hv in H1; clear Hv x y.*)
      destruct (partition (fun c : Constraint1 => a == lhs_var1 c) cs1) as [cs_hd cs_tl] eqn : Hpart.
      remember (flat_map
        (fun c : Constraint1 =>
        map
          (fun temp_c : Constraint1 =>
            substitute_constraint temp_c a (rhs_terms1 c) (rhs_const1 c))
          cs_tl) (preprocess_tbreplace a cs_hd)) as cl.
      move: H1; apply H.
      move : Heqcl; apply substitute_v_good_terms.
      intro c0; apply preprocess_tbreplace_good_terms. clear c0.
      1,2 : intros; apply H0. 1,2 : rewrite partition_as_filter in Hpart. 1,2 : inversion Hpart; clear Hpart.
      rewrite -H3 in H1; apply filter_In in H1; exact H1.1.
      rewrite -H4 in H1; apply filter_In in H1; exact H1.1.
    * move : H0 H1; apply H.
Qed.

Lemma substitute_vs_no_power (hd : ProdVar.t) : forall (vl : list ProdVar.t) (c : Constraint1) cs1,
  (forall c : Constraint1, List.In c cs1 -> rhs_power c = []) ->
  List.In c (substitute_vs (List.filter (fun p : ProdVar.t => p != hd) vl) cs1) -> rhs_power c = nil.
Proof.
  elim. 
  - simpl; intros. move : H0; apply H. 
  - simpl; intros. case Heq : (a != hd); rewrite Heq in H1. move /eqP : Heq => Heq. 
    * simpl in H1. (*case Hv : (List.filter (fun p : ProdVar.t => p != hd) l) => [|x y]; rewrite Hv in H1.
      + (* to the end : special case *) clear H.
        remember (flat_map
          (fun c : Constraint1 =>
          List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a (rhs_terms1 c) (rhs_const1 c))
            (List.filter (fun c0 : Constraint1 => a != lhs_var1 c0) cs1)) (find_constraint1s a cs1)) as cl.
        case Hagain : (List.existsb
          (fun c : Constraint1 =>
          match List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c) with
          | Some t => let (coe, _) := t in 1 < coe
          | None => false
          end) cl); rewrite Hagain in H1. move : Heqcl c H1; apply substitute_v_power.
          intros; apply H0; apply filter_In in H; exact H.1.
        remember (flat_map
          (fun c : Constraint1 =>
          List.map (fun temp_c : Constraint1 => substitute_constraint temp_c a (rhs_terms1 c) (rhs_const1 c)) cl)
          (find_constraint1s a cs1)) as cl'.
        move : Heqcl' c H1; apply substitute_v_power.
        move : Heqcl; apply substitute_v_power. intros; apply H0; apply filter_In in H; exact H.1.
      + rewrite -Hv in H1; clear Hv x y.*)
      destruct (partition (fun c : Constraint1 => a == lhs_var1 c) cs1) as [cs_hd cs_tl] eqn : Hpart.
      move : H1; apply H. clear H.
      remember (flat_map
          (fun c1 : Constraint1 =>
          map
            (fun temp_c : Constraint1 =>
            substitute_constraint temp_c a (rhs_terms1 c1) (rhs_const1 c1)) cs_tl)
        (preprocess_tbreplace a cs_hd)) as cl.
      move : Heqcl; apply substitute_v_power. intros; apply H0.
      rewrite partition_as_filter in Hpart. inversion Hpart. rewrite -H3 in H. apply filter_In in H; exact H.1.
    * move : H0 H1; apply H.
Qed.

Lemma find_tbsolved_ubs cs1 ls : forall tbsolved ubs, NoDup tbsolved -> solve_ubs tbsolved ls cs1 = Some ubs ->
  forall var, List.In var tbsolved -> exists n, solve_ub var ls cs1 = Some n /\ PVM.find var ubs = Some (Z.to_nat n).
Proof.
  elim. simpl; intros; done.
  simpl; intros a l H ubs Hnodup; intros. destruct H1.
  - subst. clear H. case Hub : (solve_ub var ls cs1) => [n|]; rewrite Hub in H0; try discriminate.
    case Hubs : (solve_ubs l ls cs1) => [nv|]; rewrite Hubs in H0; try discriminate. exists n.
    split; try done. inversion H0. rewrite /add_valuation find_add_eq //.
  - case Hub : (solve_ub a ls cs1) => [n|]; rewrite Hub in H0; try discriminate.
    case Hubs : (solve_ubs l ls cs1) => [nv|]; rewrite Hubs in H0; try discriminate.
    inversion H0. rewrite find_add_neq. apply H; try done.
    apply NoDup_cons_iff in Hnodup; exact Hnodup.2. intro Heq; subst; apply NoDup_cons_iff in Hnodup. move : Hnodup => [Hnotin _].
    done.
Qed.

(*Lemma is_goodubs cs1 : forall tbsolved ubs, NoDup tbsolved -> tbsolved <> [] -> 
  (forall var : ProdVar.t, List.In var (constraints1_vars cs1) -> List.In var tbsolved) ->
  (forall c : Constraint1, List.In c cs1 -> rhs_power c = []) -> 
  (forall c : Constraint1, List.In c cs1 -> good_terms (rhs_terms1 c)) -> 
  solve_ubs tbsolved tbsolved cs1 = Some ubs -> goodubs cs1 ubs.
Proof.
  intros tbsolved ubs Hnodup Hnotempty Hinvl Hpower Hterm. rewrite /goodubs. intros.
  rewrite /strict_smaller_valuation in H0. destruct H0 as [H1 [H2 _]].
  destruct H2 as [var [Hmem [value0 [value1 [Hfind0 [Hfind1 Hlt]]]]]].
  specialize (solve_ubs_tbsolved_in _ _ _ H); intro Hmemeq. apply Hmemeq in Hmem. 
  specialize (find_tbsolved_ubs _ _ Hnodup H _ Hmem); intro Hub. destruct Hub as [n [Hub Hfind']].
  rewrite Hfind0 in Hfind'; inversion Hfind'; clear Hfind'. rewrite H2 in Hfind0 Hlt; clear H2 value0.
  rewrite /solve_ub in Hub.
  case Hcstgt0 : (List.existsb (fun c : Constraint1 => (rhs_const1 c >? 0)%Z)
    (substitute_vs
      (List.filter (fun p : ProdVar.t => p != var) tbsolved) cs1)); rewrite Hcstgt0 in Hub; try discriminate.
  assert (Hgt0 : (0 <= n)%Z).
    apply (reduce_constraints1_helper _ _ _) in Hub; simpl in Hub; try done.
    move : Hub; clear; intros. destruct Hub as [c [Hin [coe [Hfind [Hcoe Heq]]]]]. rewrite -Heq; clear Heq.
    assert (H: (0 <= Z.abs (rhs_const1 c) / Z.of_nat (coe - 1))%Z). apply Z_div_nonneg_nonneg; try lia. lia. 
    apply substitute_vs_is_hd; try done.
    intros; apply Hinvl. apply (constraint1_vars2constraints1_vars _ H0).
    rewrite /constraint1_vars; simpl; left; done.
    intro c; apply substitute_vs_good_terms; try done.
  specialize (reduce_constraints1 temp_ub (substitute_vs (List.filter (fun p : ProdVar.t => p != var) tbsolved) cs1) var); intro Hreduce.
  rewrite Hub in Hreduce; clear Hub. rewrite -(Nat2Z.id value1) in Hfind1.
  apply Hreduce in Hfind1; try done; clear Hreduce. 
  specialize (substitute_correctness temp_ub cs1 (List.filter (fun p : ProdVar.t => p != var) tbsolved) Hpower Hterm); intros Hsub.
  apply Hsub. destruct Hfind1 as [c [Hin [Hexists Hunsat]]]. exists c; split; try done.

  apply substitute_vs_is_hd; try done. intros. 
  apply Hinvl. apply (constraint1_vars2constraints1_vars _ H0).
  rewrite /constraint1_vars; simpl; left; done.
 
  intros; split. move : H0; apply substitute_vs_good_terms; try done. split. 
    specialize (List.In_nth _ _ c H0); intros. destruct H2 as [k [Hle Hnth]].
    apply (existsb_nth _ _ c Hle) in Hcstgt0. rewrite Hnth in Hcstgt0. lia.
  move : H0; apply substitute_vs_no_power; try done. 

  rewrite -(Z2Nat.id n); try done. apply inj_lt. apply (elimT ltP); done.

Qed.*)

Definition isGoodbound (solved tbsolved : list ProdVar.t) (cs : list Constraint)
  (initial ubs : Valuation) : Prop :=
  (* initial 满足cs中rhs全为solved的约束，并且保证最小 *)
  is_good_initialized_smallest solved tbsolved cs initial /\
  (* 只有待求解变量有 ub, 满足任何大于ub的取值都将不满足约束 *)
  let tbsolved := map fst (PVM.elements ubs) in
  let ub_cs := filter (constraint1_in_set tbsolved) (split_constraints cs).1 in
  forall temp_ub, smaller_valuation ubs temp_ub -> ~~ forallb (satisfies_constraint1 temp_ub) ub_cs.


Definition G := PVM.t (list ProdVar.t).
Definition Adj := PVM.t (PVM.t (list Constraint1)).

Definition find_adj_matrix (from to : ProdVar.t) (m : Adj) : option (list Constraint1) :=
  match PVM.find from m with
  | Some m' => PVM.find to m'
  | None => None
  end.

Definition add_edge graph adj_matrix (from to : ProdVar.t) (c : Constraint1) : G * Adj :=
  let new_graph := match PVM.find from graph with
    | Some children => PVM.add from (to :: children) graph
    | _ => PVM.add from [::to] graph
  end in
  let new_adj := match PVM.find from adj_matrix with
    | Some adj' => match PVM.find to adj' with
                  | Some cs1 => PVM.add from (PVM.add to (c :: cs1) adj') adj_matrix
                  | None => PVM.add from (PVM.add to [::c] adj') adj_matrix
                  end
    | _ => PVM.add from (PVM.add to [::c] (PVM.empty (list Constraint1))) adj_matrix
  end in (new_graph, new_adj).

Fixpoint build_graph (constraints : list Constraint1) : G * Adj :=
  match constraints with
  | [] => (PVM.empty (list ProdVar.t), PVM.empty (PVM.t (list Constraint1)))
  | c0 :: cs =>
      fold_left (fun '(graph, adj_matrix) (xi : ProdVar.t) =>
                   add_edge graph adj_matrix xi (lhs_var1 c0) c0)
                (List.split (rhs_terms1 c0)).2 (build_graph cs)
  end. (* from 为rhs, to lhs *)

Fixpoint find_path (g : G) (y : ProdVar.t) n (v : list ProdVar.t) (x : ProdVar.t) res : option (list ProdVar.t) :=
  match res with
  | Some p => res
  | None =>
  if x == y then Some (y :: v) else
  if n is n'.+1 then match PVM.find x g with
    | Some children =>
    foldl (fun r child => match r with
      | Some p => res 
      | None => find_path g y n' (x :: v) child None
      end) res children
    | None => None
    end else None
  end. (* from x to y, res 为 y, ..., x *)

Fixpoint find_constraints_of_path (adj : Adj) (p_hd : ProdVar.t) (p_tl : list ProdVar.t) : option (list Constraint1) :=
  match p_tl with
  | [] => Some nil
  | hd :: tl => match find_adj_matrix hd p_hd adj, find_constraints_of_path adj hd tl with
              | Some (c :: _), Some cs => Some (c :: cs)
              | _, _ => None
              end
  end.

Definition substitute_c (c1 c2 : Constraint1) : Constraint1 :=
  substitute_constraint c1 (lhs_var1 c2) (rhs_terms1 c2) (rhs_const1 c2).

Fixpoint substitute_cs (cs : list Constraint1) : option Constraint1 :=
  match cs with
  | [] => None
  | hd :: tl => match substitute_cs tl with
                | Some c => Some (substitute_c hd c)
                | None => Some hd
                end
  end.

Definition compute_ub (c : Constraint1) : option nat :=
  match find (fun (p : term) => snd p == (lhs_var1 c)) (rhs_terms1 c) with
  | None => None
  | Some (coe, _) => if coe > 1 then Some (Z.to_nat (Z.div (Z.abs (rhs_const1 c)) (Z.of_nat (coe - 1)))) else None
  end.

Definition solve_ub_case1 (x : ProdVar.t) (c : Constraint1) (var : ProdVar.t) (g : G) (adj : Adj) (n : nat) : option nat :=
  (* c : lhs >= coe * var + ... + cst c *) 
  (* 找 x >= ? * lhs + ... 和 var >= ? * x + ... *)
  match find_path g x n nil (lhs_var1 c) None, find_path g var n nil x None with
  | Some (p0_hd :: p0_tl), Some (p1_hd :: p1_tl) => 
          match find_constraints_of_path adj p0_hd p0_tl, find_constraints_of_path adj p1_hd p1_tl with
          | Some cs0, Some cs1 => let new_c := match substitute_cs cs0, substitute_cs cs1 with
                                | Some c0, Some c1 => substitute_c c0 (substitute_c c c1)
                                | None, Some c1 => substitute_c c c1
                                | Some c0, None => substitute_c c0 c
                                | None, None => c end in
                                  compute_ub new_c 
          | _, _ => None
          end
  | _, _ => None
  end.

Fixpoint solve_ubs_case1 (tbsolved : list ProdVar.t) (c : Constraint1) (var : ProdVar.t) (g : G) (adj : Adj) (n : nat) (v : Valuation) : option Valuation :=
  match tbsolved with
  | [] => Some v
  | hd :: tl => match solve_ub_case1 hd c var g adj n with
              | Some ub => solve_ubs_case1 tl c var g adj n (PVM.add hd ub v)
              | _ => None
              end
  end.

Definition solve_ub_case2 (x : ProdVar.t) (c : Constraint1) (var0 var1 : ProdVar.t) (g : G) (adj : Adj) (n : nat) : option nat :=
  (* c : lhs >= coe0 * var0 + coe1 * var1 + ... + cst c *) 
  (* 找 x >= ? * lhs + ... 和 var0 >= ? * x + ... 和 var1 >= ? * x + ... *)
  match find_path g x n nil (lhs_var1 c) None, find_path g var0 n nil x None, find_path g var1 n nil x None with
  | Some (p0_hd :: p0_tl), Some (p1_hd :: p1_tl), Some (p2_hd :: p2_tl) => 
        match find_constraints_of_path adj p0_hd p0_tl, find_constraints_of_path adj p1_hd p1_tl, find_constraints_of_path adj p2_hd p2_tl with
        | Some cs0, Some cs1, Some cs2 => let new_c := match substitute_cs cs0, substitute_cs cs1, substitute_cs cs2 with
                                | Some c0, Some c1, Some c2 => substitute_c c0 (substitute_c (substitute_c c c1) c2)
                                | None, Some c1, Some c2 => substitute_c (substitute_c c c1) c2
                                | Some c0, None, Some c2 => substitute_c c0 (substitute_c c c2)
                                | None, None, Some c2 => substitute_c c c2
                                | Some c0, Some c1, None => substitute_c c0 (substitute_c c c1)
                                | None, Some c1, None => substitute_c c c1
                                | Some c0, None, None => substitute_c c0 c
                                | None, None, None => c end in
                                  compute_ub new_c 
        | _, _, _ => None
        end
| _, _, _ => None
end.

Fixpoint solve_ubs_case2 (tbsolved : list ProdVar.t) (c : Constraint1) (var0 var1 : ProdVar.t) (g : G) (adj : Adj) (n : nat) (v : Valuation) : option Valuation :=
  match tbsolved with
  | [] => Some v
  | hd :: tl => match solve_ub_case2 hd c var0 var1 g adj n with
              | Some ub => solve_ubs_case2 tl c var0 var1 g adj n (PVM.add hd ub v)
              | _ => None
              end
  end.

Definition solve_ubs_aux (tbsolved : list ProdVar.t) (cs1 : list Constraint1) : option Valuation :=
  let (g, adj) := build_graph cs1 in
  let n := List.length tbsolved in
  match List.find (fun c => existsb (fun t => t.1 > 1) (rhs_terms1 c)) cs1 with
  | Some c => (* lhs >= coe * var + ... + cst c *) 
              match List.find (fun t => t.1 > 1) (rhs_terms1 c) with
              | Some (_, var) => solve_ubs_case1 tbsolved c var g adj n initial_valuation
              | _ => None
              end
  | None => match List.find (fun c => List.length (rhs_terms1 c) > 1) cs1 with
            | Some c => (* lhs >= coe0 * var0 + coe1 * var1 + ... + cst c *)
                        match rhs_terms1 c with
                        | (_, var0) :: (_, var1) :: _ => solve_ubs_case2 tbsolved c var0 var1 g adj n initial_valuation
                        | _ => None
                        end
            | None => None
            end
  end.

Fixpoint add_bs (ls : list (ProdVar.t * nat)) (bs : PVM.t (nat * nat)) : PVM.t (nat * nat) :=
  match ls with
  | nil => bs
  | (hd, ub) :: tl => add_bs tl (PVM.add hd (0, ub) bs)
  end.

Definition mergeBounds (v2 : Valuation) : PVM.t (nat * nat) :=
  let eles := PVM.elements v2 in
  add_bs eles (PVM.empty (nat * nat)).

End SccCorrectness.
