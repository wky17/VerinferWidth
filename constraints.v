From mathcomp Require Import all_ssreflect.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
From HB Require Import structures.
From Solver Require Import Env HiEnv LoFirrtl HiFirrtl.
Import ListNotations.

Set Implicit Arguments.
(*Unset Strict Implicit.*) 
Import Prenex Implicits.

Section constraint.

Definition term : Type := nat * ProdVar.t.

Lemma eq_from_prodvar_eq : forall p1 p2 : ProdVar.t, ProdVar.eq p1 p2 <-> p1 = p2.
Proof.
  split; move : p1 p2.
  intros [x1 y1] [x2 y2] [H1 H2].
  simpl in H1; simpl in H2.
  move /eqP : H1 => H1.
  move /eqP : H2 => H2.
  rewrite H1 H2. (* 替换 x1, y1 *)
  reflexivity. (* 结束证明 *)
  intros [x1 y1] [x2 y2] Heq.
  injection Heq; intros.
  subst.
  split; (apply ProdVar.eq_refl).
Qed.

Lemma term_dec : forall (x y : term), { eq x y } + { ~ eq x y }.
Proof. 
  intros [n1 p1] [n2 p2].
  destruct (Nat.eq_dec n1 n2) as [Hn | Hn].
  destruct (ProdVar.eq_dec p1 p2) as [Hp | Hp].
  - left.
    + (* p1 = p2，则 x = y *)
      apply eq_from_prodvar_eq in Hp.
      rewrite Hn.
      rewrite Hp.
      reflexivity.
    + (* p1 <> p2，证明 d(x,y) 不等 *)
      right.
      unfold not.
      intros H.
      injection H; intros.
      apply eq_from_prodvar_eq in H0.
      unfold not in Hp; apply Hp in H0.
      done.
  - (* n1 <> n2，直接得到不等 *)
    right.
    unfold not.
    intros H.
    injection H; intros; subst.
    done.
Qed.

Definition term_eqn (x y : term) : bool :=
  (x.1 == y.1) && (x.2 == y.2).
Lemma term_eqP : Equality.axiom term_eqn.
Proof.
  unfold Equality.axiom, term_eqn.
  destruct x as [coe0 var0];
  destruct y as [coe1 var1]; simpl.
  destruct (coe0 == coe1) eqn: Hc ; move /eqP : Hc => Hc ;
        last by (apply ReflectF ; contradict Hc ; injection Hc ; done).
  rewrite Hc andTb.
  destruct (var0 == var1) eqn: Hv ; move /eqP : Hv => Hv ;
        last by (apply ReflectF ; contradict Hv ; injection Hv ; done).
  rewrite Hv. apply ReflectT; done.
Qed.

HB.instance Definition _ := hasDecEq.Build term term_eqP.

Definition terms := list term.
Fixpoint terms_eqn (x y : terms) : bool :=
  match x,y with
  | nil, nil => true
  | t0 :: tl0, t1 :: tl1 => (t0 == t1) && (terms_eqn tl0 tl1)
  | _, _ => false
  end.

Lemma terms_eqP : Equality.axiom terms_eqn.
Proof.
  unfold Equality.axiom.
  move=> x y.
  elim: x y => [|x xs IHx] y /=.
  - (* x = nil 的情况 *)
    case: y => [|y ys] /=.
    + (* y = nil *)
      apply ReflectT; reflexivity.
    + (* y = y::ys *)
      apply ReflectF; discriminate.
  
  - (* x = x::xs 的情况 *)
    case: y => [|y ys] /=.
    + (* y = nil *)
      apply ReflectF; discriminate.
    + (* y = y::ys *)
      (* 比较头部元素 *)
      move: (term_eqP x y) => [Hxy_eq|Hxy_neq].
      * (* x == y *)
        rewrite Hxy_eq /=.
        move: (IHx ys) => [Hxsys_eq|Hxsys_neq].
        -- (* xs 和 ys 相等 *)
          rewrite Hxsys_eq eq_refl. apply ReflectT. done.
        -- (* xs 和 ys 不相等 *)
          rewrite eq_refl. simpl. apply ReflectF.
          contradict Hxsys_neq. inversion Hxsys_neq. done.
      * (* x != y *)
        assert ((x==y)=false). apply not_true_iff_false. intro. move /eqP : H => H; subst x; done. rewrite H. simpl. apply ReflectF.
        contradict Hxy_neq. inversion Hxy_neq. done.
Qed.

HB.instance Definition _ := hasDecEq.Build terms terms_eqP.

(* 定义ϕ1类型的约束结构 *)
(*Record Constraint1 : Type := {
  lhs_var1 : ProdVar.t;  (* 左侧变量 *)
  rhs_const1 : Z.t;(* 右侧常数项 *)
  rhs_terms1 : list (nat * ProdVar.t) (* 右侧线性组合项，列表形式 (系数, 变量) *)
}.*)

Record Constraint1 : Type := {
  lhs_var1 : ProdVar.t;  (* 左侧变量 *)
  rhs_const1 : Z.t;(* 右侧常数项 *)
  rhs_terms1 : terms; (* 右侧线性组合项，列表形式 (系数, 变量) *)
  rhs_power : terms (* 右侧2的幂项 *)
}.

Definition constraint1_eqn (x y : Constraint1) : bool :=
  (lhs_var1 x == lhs_var1 y) &&
  (Z.eqb (rhs_const1 x) (rhs_const1 y)) &&
  (rhs_terms1 x == rhs_terms1 y) &&
  (rhs_power x == rhs_power y).

Lemma constraint1_eqP : Equality.axiom constraint1_eqn.
Proof.
  unfold Equality.axiom, constraint1_eqn.
  destruct x as [x_lhs x_const x_terms x_power];
  destruct y as [y_lhs y_const y_terms y_power]; simpl.
  destruct (x_lhs == y_lhs) eqn: Hlhs ; move /eqP : Hlhs => Hlhs ;
        last by (apply ReflectF ; contradict Hlhs ; injection Hlhs ; done).
  rewrite Hlhs andTb.
  (* 比较常数项 *)
  case Hconst: (x_const =? y_const)%Z; [move/Z.eqb_eq in Hconst | move/Z.eqb_neq in Hconst]; simpl; 
        last by (apply ReflectF ; contradict Hlhs ; injection Hlhs ; done).
  rewrite Hconst.
 (* 比较线性组合项 *)
  destruct (x_terms == y_terms) eqn: Hterms ; move /eqP : Hterms => Hterms ;  
        last by (apply ReflectF ; contradict Hterms ; injection Hterms ; done).
  rewrite Hterms andTb.
  (* 比较2的幂项 *)
  destruct (x_power == y_power) eqn: Hp ; move /eqP : Hp => Hp ;  
        last by (apply ReflectF ; contradict Hp ; injection Hp ; done).
  rewrite Hp.
  apply ReflectT. done. 
Qed.

HB.instance Definition _ := hasDecEq.Build Constraint1 constraint1_eqP.

(* 定义ϕ2类型的约束结构 *)
Record Constraint2 : Type := {
  lhs_const2 : nat; (* 左侧常数项 *)
  rhs_terms2 : terms (* 右侧线性组合项，列表形式 (系数, 变量) *)
}.

Definition constraint2_eqn (x y : Constraint2) : bool :=
  ((lhs_const2 x) == (lhs_const2 y)) &&
  (rhs_terms2 x == rhs_terms2 y).

Lemma constraint2_eqP : Equality.axiom constraint2_eqn.
Proof.
  unfold Equality.axiom, constraint2_eqn.
  destruct x as [x_lhs x_terms];
  destruct y as [y_lhs y_terms]; simpl.
  destruct (x_lhs == y_lhs) eqn: Hlhs ; move /eqP : Hlhs => Hlhs ;
        last by (apply ReflectF ; contradict Hlhs ; injection Hlhs ; done).
  rewrite Hlhs andTb.
  (* 比较线性组合项 *)
  destruct (x_terms == y_terms) eqn: Hterms ; move /eqP : Hterms => Hterms ;  
        last by (apply ReflectF ; contradict Hterms ; injection Hterms ; done).
  rewrite Hterms.
  apply ReflectT. done. 
Qed.

HB.instance Definition _ := hasDecEq.Build Constraint2 constraint2_eqP.

(* 定义统一的约束类型 *)
Inductive Constraint : Type :=
  | Phi1 : Constraint1 -> Constraint (* ϕ1类型的约束 *)
  | Phi2 : Constraint2 -> Constraint (* ϕ2类型的约束 *)
.

Definition constraint_eqn (x y : Constraint) : bool :=
  match x,y with
  | Phi1 c1, Phi1 c2
  | Phi2 c1, Phi2 c2 => c1 == c2
  | _, _ => false
  end.

Lemma constraint_eqP : Equality.axiom constraint_eqn.
Proof.
  unfold Equality.axiom, constraint_eqn ; intros.
  destruct x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
  destruct (c == c0) eqn: Hlhs ; move /eqP : Hlhs => Hlhs ;
        last by (apply ReflectF ; contradict Hlhs ; injection Hlhs ; done).
  rewrite Hlhs. apply ReflectT. done. 
  destruct (c == c0) eqn: Hlhs ; move /eqP : Hlhs => Hlhs ;
        last by (apply ReflectF ; contradict Hlhs ; injection Hlhs ; done).
  rewrite Hlhs. apply ReflectT. done.
Qed.

HB.instance Definition _ := hasDecEq.Build Constraint constraint_eqP.

Record Constraint2_new : Type := {
  lhs_const2_new : Z.t;
  rhs_terms2_new : list (nat * ProdVar.t);
  rhs_power2_new : list (nat * ProdVar.t)
}.

(* 定义变量值的映射 *)
(* old version 
Definition Valuation := ProdVar.t -> nat.

(* 假设初始值都为0 *)
Definition initial_valuation : Valuation := fun _ => 0.
Definition add_valuation (s : ProdVar.t -> nat) (x : ProdVar.t) (v : nat) :=
  fun n => if n == x then v else s n. *)

Definition combine_term (t1 : term) (t2 : list term) : list term := 
  match List.find (fun p : term => snd p == t1.2) t2 with
  | None => t1 :: t2  (* 添加新的项 *)
  | Some t =>
      (* 合并项 *)
      (t.1 + t1.1, t1.2) :: (List.remove term_dec t t2)
  end.

Definition combine_terms (t1 t2 : (list term * list term * Z.t)) : list term * list term * Z.t := 
  (* 不考虑幂项 *)
  let '(terms1, _, cst1) := t1 in
  let '(terms2, _, cst2) := t2 in
  let new_terms := fold_left (fun acc term =>
    combine_term term acc) terms2 terms1 in
  (new_terms, nil, Z.add cst1 cst2). 

Definition Valuation := PVM.t nat.
Definition initial_valuation := PVM.empty nat.
Definition add_valuation := PVM.add.

(* 检查ϕ1类型的约束是否满足 *)
Definition terms_value (v : Valuation) (terms : list (nat * ProdVar.t)) (init : Z.t) : Z.t :=
  fold_left (fun acc ax => 
                            let vi := match PVM.find ax.2 v with
                            | Some val => val
                            | None => 0
                            end in
                            Z.add acc (Z.of_nat (ax.1 * vi))) terms init.

Definition power_value (v : Valuation) (terms : list (nat * ProdVar.t)) : Z.t :=
  match terms with
  | nil => 0
  | _ => let n := terms_value v terms 0 in Z.pow 2 n
  end.

Definition rhs_value1 (v: Valuation) (c : Constraint1) : Z.t :=
  terms_value v c.(rhs_terms1) c.(rhs_const1) + power_value v c.(rhs_power).

Definition rhs_vars (c : Constraint1) : list ProdVar.t :=
  map snd (rhs_terms1 c) ++ map snd (rhs_power c).

Definition satisfies_constraint1 (v: Valuation) (c: Constraint1) : bool :=
  match PVM.find c.(lhs_var1) v with
  | Some val => Z.leb (rhs_value1 v c) (Z.of_nat val)
  | None => false
  end.

(* 检查ϕ2类型的约束是否满足 *)
Definition satisfies_constraint2 (v: Valuation) (c: Constraint2) : bool :=
  let total := fold_left (fun acc '(bi, xi) => 
                            let vi := match PVM.find xi v with
                            | Some val => val
                            | None => 0 
                            end in
                            acc + (bi * vi)) 
                         c.(rhs_terms2) 0
  in total <=? c.(lhs_const2).

(* 检查约束是否满足 *)
Definition satisfies_constraint (v: Valuation) (c: Constraint) : bool :=
  match c with
  | Phi1 c1 => satisfies_constraint1 v c1
  | Phi2 c2 => satisfies_constraint2 v c2
  end.

(* 检查约束集是否满足 *)
Definition satisfies_all (v: Valuation) (cs: list Constraint) : bool :=
  forallb (satisfies_constraint v) cs.

(* 项合并 
Definition unite_terms (terms1 terms2 : list (nat * ProdVar.t)) (cst1 cst2 : Z.t) : (list (nat * ProdVar.t) * Z.t) :=
  let new_terms := fold_left (fun '(coe1, var1) =>
  ) terms1 in (new_terms, Z.add cst1 cst2).*)


(* ------ seperate subset from constraints ------ *)

(* 判断一个变量是否在集合中 *)
Definition in_set (s : list ProdVar.t) (v : ProdVar.t) : bool :=
  existsb (eq_op v) s.

(* 判断一个约束是否只涉及集合中的变量 *)
Definition constraint1_in_set (s : list ProdVar.t) (c : Constraint1) : bool :=
  let vars_in_rhs := map snd (rhs_terms1 c) ++ map snd (rhs_power c) in
  let all_vars := lhs_var1 c :: vars_in_rhs in
  forallb (in_set s) all_vars.

(* 判断一个约束rhs是否只涉及集合中的变量 
Definition constraintrhs_in_set (s : list ProdVar.t) (c : Constraint) : bool :=
  match c with
  | Phi1 c1 => forallb (in_set s) (map snd (rhs_terms1 c1))
  | Phi2 c1 => forallb (in_set s) (map snd (rhs_terms2 c1))
  end.*)

Definition constraint2_in_set (s : list ProdVar.t) (c : Constraint2) : bool :=
  let all_vars := map snd (rhs_terms2 c) in
  forallb (in_set s) all_vars.

Definition constraint_in_set (s : list ProdVar.t) (c : Constraint) : bool :=
  match c with
  | Phi1 c1 => constraint1_in_set s c1
  | Phi2 c1 => constraint2_in_set s c1
  end.

(* 判断一个约束 不包含任何 变量s *)
(*Definition constraint1_exclusive_v (s : ProdVar.t) (c : Constraint1) : bool :=
  let vars_in_rhs := map snd (rhs_terms1 c) in
  s \notin ((lhs_var1 c) :: vars_in_rhs).

(* 判断一个约束 不包含任何 集合中的变量 *)
Definition constraint1_exclusive_set (s : list ProdVar.t) (c : Constraint1) : bool :=
  let vars_in_rhs := map snd (rhs_terms1 c) in
  ~~ (existsb (in_set s) ((lhs_var1 c) :: vars_in_rhs)).

(* 判断一个约束rhs 不包含任何 集合中的变量 *)
Definition constraint1rhs_exclusive_set (s : list ProdVar.t) (c : Constraint1) : bool :=
  let vars_in_rhs := map snd (rhs_terms1 c) in
  ~~ (existsb (in_set s) (vars_in_rhs)).*)

(* 根据集合筛选出相关约束 *)
Fixpoint filter_constraints1 (s : list ProdVar.t) (constraints : list Constraint) : list Constraint1 :=
  match constraints with
  | nil => nil
  | (Phi1 c) :: cs => let ls := filter_constraints1 s cs in
                      if (constraint1_in_set s c) then c :: ls else ls
  | _ :: cs => filter_constraints1 s cs
  end.

Fixpoint filter_constraints2 (s : list ProdVar.t) (constraints : list Constraint) : list Constraint2 :=
  match constraints with
  | nil => nil
  | (Phi2 c) :: cs => let ls := filter_constraints2 s cs in
                      if (constraint2_in_set s c) then c :: ls else ls
  | _ :: cs => filter_constraints2 s cs
  end.

Fixpoint filter_constraints (s : list ProdVar.t) (constraints : list Constraint) : list Constraint :=
  match constraints with
  | nil => nil
  | (Phi1 c) :: cs => let ls := filter_constraints s cs in
                      if (constraint1_in_set s c) then (Phi1 c) :: ls else ls
  | (Phi2 c) :: cs => let ls := filter_constraints s cs in
                      if (constraint2_in_set s c) then (Phi2 c) :: ls else ls
  end.

Fixpoint split_constraints (l : list Constraint) : list Constraint1 * list Constraint2 :=
  match l with
  | [] => ([], [])
  | c :: cs =>
      match c with
      | Phi1 c1 => (c1 :: (split_constraints cs).1, (split_constraints cs).2)
      | Phi2 c2 => ((split_constraints cs).1, c2 :: (split_constraints cs).2)
      end
  end.

Fixpoint split_constraints' (l : list Constraint) : list Constraint1 * list Constraint2 :=
  match l with
  | [] => ([], [])
  | c :: cs =>
      let (cs1, cs2) := split_constraints' cs in
      match c with
      | Phi1 c1 => (c1 :: cs1, cs2)
      | Phi2 c2 => (cs1, c2 :: cs2)
      end
  end.

Lemma split_constraints_eq : forall l, split_constraints l = split_constraints' l.
Proof.
  elim. 
  - simpl; done.
  - intros c cs IH; simpl.
    destruct c as [c1 | c2]; rewrite IH; clear IH;
    destruct (split_constraints' cs) as [cs1 cs2];
    simpl; done.
Qed.

(* 在约束列表中找到指定左变量的约束 *)
Definition find_constraint1s (v : ProdVar.t) (constraints : list Constraint1) : list Constraint1 :=
  filter (fun c => (v == (lhs_var1 c))) constraints.

Definition smaller_valuation0 (v0 v1 : Valuation) : Prop :=
  let vars := (List.split (PVM.elements v0)).1 in
  forall (var : ProdVar.t), var \in vars -> 
  (exists value0 value1, PVM.find var v0 = Some value0 /\ PVM.find var v1 = Some value1 /\ value0 <= value1).

(*Definition is_good_smallest (solved : list ProdVar.t) (cs : list Constraint) (initial : Valuation) : Prop :=
  (* claim : initial中变量的取值，满足cs中rhs全为solved的约束，并且是所有满足约束的取值中最小的 *)
  let solved_cs := filter (constraint_in_set solved) cs in (* 关心所有仅包含solved变量的约束 *)
  (satisfies_all initial solved_cs) /\ 
  (forall temp_s, satisfies_all temp_s solved_cs -> (*PVM.equal leq*) smaller_valuation0 initial temp_s).
*)
Definition is_good_initialized (var : ProdVar.t) (solved : list ProdVar.t) (cs : list Constraint) (values : Valuation) : Prop :=
  let cs' := (split_constraints cs).1 in
  let cs'' := filter (fun c => forallb (in_set solved) (map snd (rhs_terms1 c))) cs' in
  let tbsolved_cs := filter (fun c => (lhs_var1 c) == var) cs'' in
  forallb (satisfies_constraint1 values) tbsolved_cs.

Definition is_good_initialized_smallest (solved tbsolved : list ProdVar.t) (cs : list Constraint) (initial : Valuation) : Prop :=
  (* 在is_good_smallest的基础上，tbsolved被正确地初始化，是满足条件的最小 *)
  let solved_cs := filter (constraint_in_set solved) cs in 
  (satisfies_all initial solved_cs) /\ 
  (forall (var : ProdVar.t), var \in tbsolved -> is_good_initialized var solved cs initial) /\
  (forall (temp_s : Valuation), satisfies_all temp_s solved_cs /\
    (forall (var : ProdVar.t), var \in tbsolved -> is_good_initialized var solved cs temp_s) 
    -> (*PVM.equal leq*) smaller_valuation0 initial temp_s).

(* 提取一个 Constraint1 中的所有变量 *)
Definition constraint1_vars (c : Constraint1) : list ProdVar.t :=
  lhs_var1 c :: map snd (rhs_terms1 c) ++ map snd (rhs_power c).

Fixpoint constraints1_vars (c : list Constraint1) : list ProdVar.t :=
  match c with
  | nil => nil
  | c1 :: tl => constraint1_vars c1 ++ (constraints1_vars tl)
  end.

(*Fixpoint unique_ls (vars : list ProdVar.t) : list ProdVar.t :=
  match vars with
  | nil => nil
  | hd :: tl => if hd \notin (unique_ls tl) then hd :: (unique_ls tl)
    else unique_ls tl
  end.

Theorem unique_ls_correst : forall ls, uniq (unique_ls ls).
Proof.
  elim.
  simpl; done.
  intros; simpl.
  case Ha : (a \notin unique_ls l); try done.
  simpl; rewrite Ha H; done.
Qed.

Check undup.
Search uniq.
Search NoDup.

(* 合并所有约束中的变量并去重 *)
Fixpoint unique_var (vars rest_vars : list ProdVar.t) : list ProdVar.t :=
  match vars with
  | nil => rest_vars
  | hd :: tl => if hd \notin ((unique_var tl rest_vars) ++ rest_vars) 
    then hd :: (unique_var tl rest_vars)
    else unique_var tl rest_vars
  end.

Fixpoint unique_vars (constraints : list Constraint1) : list ProdVar.t :=
  match constraints with
  | [] => []
  | c :: cs =>
      let rest_vars := unique_vars cs in
      let vars := constraint_vars c in
      let exclude_vars := unique_var vars rest_vars in
      exclude_vars ++ rest_vars
  end.

Definition unique_vars (constraints : list Constraint1) : list ProdVar.t :=
  undup (flat_map constraint_vars constraints).

Lemma exclusive_v_correct0 : forall v var constraints,
  v \in (unique_vars
      (filter [eta constraint1_exclusive_v var] constraints)) -> 
  v \in (unique_vars constraints).
Proof.
  intros v var constraints.
  rewrite /unique_vars.
  move : constraints; elim; try (simpl; done).
  intros hd tl H; simpl.
  case Hhd : (constraint1_exclusive_v var hd); intros.
  assert (hd :: filter [eta constraint1_exclusive_v var] tl = [::hd] ++ filter [eta constraint1_exclusive_v var] tl) by (simpl; done).
  rewrite H1 in H0; clear H1.
  rewrite flat_map_app in H0. rewrite -> undup_cat in H0.
  rewrite mem_cat in H0.
  case H1 : (v
    \in [seq x <- undup (flat_map constraint_vars [hd])
         | x
             \notin flat_map constraint_vars
                      (filter [eta constraint1_exclusive_v var]
                         tl)]); rewrite H1 in H0.
  - clear H0; simpl in H1.
    assert (rhs_vars (rhs_terms1 hd) ++ [] = rhs_vars (rhs_terms1 hd)) by (rewrite app_nil_r //).
    rewrite H0 in H1; clear H0.
    assert ((lhs_var1 hd) \notin (rhs_vars (rhs_terms1 hd))) by admit.
    unfold "\notin" in H0.
    apply negb_true_iff in H0.
    rewrite H0 in H1; clear H0.
    rewrite mem_filter in H1.
    move /andP : H1 => [_ H1].
    case H0 : (lhs_var1 hd
      \in rhs_vars (rhs_terms1 hd) ++ flat_map constraint_vars tl).
    + rewrite seq.in_cons in H1.
      case H2 : (v == lhs_var1 hd); rewrite H2 in H1.
      * clear H1; move /eqP : H2 => H2; subst.
        specialize (mem_undup (rhs_vars (rhs_terms1 hd) ++
        flat_map constraint_vars tl)) as H1.
        (*specialize (mem_subseq (undup_subseq (rhs_vars (rhs_terms1 hd) ++
        flat_map constraint_vars tl))) as H1.
        unfold "{ 'et' A <= B }" in H1.*)
        (*et_eqP*)
        unfold "A =i B" in H1.
        specialize H1 with (x := (lhs_var1 hd)); rewrite H0 in H1; done.
      * rewrite orb_false_l in H1.
        rewrite (mem_undup (rhs_vars (rhs_terms1 hd))) in H1.
        rewrite (mem_undup (rhs_vars (rhs_terms1 hd) ++ flat_map constraint_vars tl)) mem_cat H1
          orb_true_l //.
    + rewrite seq.in_cons; rewrite seq.in_cons in H1.
      case H2 : (v == lhs_var1 hd); rewrite H2 in H1; try (apply orb_true_l; done).
      rewrite orb_false_l in H1; rewrite orb_false_l.
      rewrite (mem_undup (rhs_vars (rhs_terms1 hd))) in H1.
      rewrite (mem_undup (rhs_vars (rhs_terms1 hd) ++ flat_map constraint_vars tl)) mem_cat H1 orb_true_l //.
  - rewrite orb_false_l in H0.
    assert ({subset (flat_map constraint_vars (filter [eta constraint1_exclusive_v var] tl))
      <= (flat_map constraint_vars tl)}) by admit.
    unfold "{ 'subset' A <= B }" in H2.
    rewrite (mem_undup (flat_map constraint_vars (filter [eta constraint1_exclusive_v var] tl))) in H0.
    apply H2 in H0; clear H2.
    case : (lhs_var1 hd \in rhs_vars (rhs_terms1 hd) ++ flat_map constraint_vars tl).
    + rewrite (mem_undup (rhs_vars (rhs_terms1 hd) ++ flat_map constraint_vars tl)) mem_cat H0 orb_true_r //.
    + rewrite seq.in_cons (mem_undup (rhs_vars (rhs_terms1 hd) ++ flat_map constraint_vars tl)) mem_cat H0 orb_true_r orb_true_r //.
  apply H in H0; clear H.
  rewrite (mem_undup (flat_map constraint_vars tl)) in H0.
  case : (lhs_var1 hd \in rhs_vars (rhs_terms1 hd) ++ flat_map constraint_vars tl).
  + rewrite (mem_undup (rhs_vars (rhs_terms1 hd) ++ flat_map constraint_vars tl)) mem_cat H0 orb_true_r //.
  + rewrite seq.in_cons (mem_undup (rhs_vars (rhs_terms1 hd) ++ flat_map constraint_vars tl)) mem_cat H0 orb_true_r orb_true_r //.
Admitted.

Lemma notin_filtered_seq (var : ProdVar.t) (ls ls' : list ProdVar.t) :
  var \notin ls ->
  var \notin [seq x <- ls | x \notin ls'].
Proof.
  move=> Hnotin.
  rewrite /= mem_filter.
  unfold "\notin" in Hnotin.
  apply negb_true_iff in Hnotin; rewrite Hnotin.
  rewrite andb_false_r //.
Qed.

Lemma exclusive_v_correct1 : forall var constraints,
  var \notin (unique_vars (filter [eta constraint1_exclusive_v var] constraints)).
Proof.
  intros var constraints.
  rewrite /unique_vars.
  move : constraints; elim; try (simpl; done).
  intros hd tl H; simpl.
  case Hhd : (constraint1_exclusive_v var hd); try done.
  assert (hd :: filter [eta constraint1_exclusive_v var] tl
      = [::hd] ++ filter [eta constraint1_exclusive_v var] tl) by (simpl; done).
  rewrite H0; clear H0; rewrite flat_map_app.
  rewrite -> undup_cat.
  rewrite mem_cat negb_or H andb_true_r; clear H.
  simpl; rewrite /constraint1_exclusive_v in Hhd.
  assert (rhs_vars (rhs_terms1 hd) ++ [] = rhs_vars (rhs_terms1 hd)) by (rewrite app_nil_r //).
  rewrite H; clear H.
  assert ((lhs_var1 hd) \notin (rhs_vars (rhs_terms1 hd))) by admit.
  unfold "\notin" in H.
  apply negb_true_iff in H.
  rewrite H; clear H.
  assert (undup (rhs_vars (rhs_terms1 hd)) = rhs_vars (rhs_terms1 hd)) by admit.
  rewrite H; clear H; rewrite /rhs_vars.
  apply notin_filtered_seq; done.
Admitted.*)

(*Definition max_of_list_fold_left (l : list Z) : option Z :=
  match l with
  | [] => None
  | x :: xs => Some (fold_left Z.max xs x)
  end.

Definition solve_acyclic' (v : ProdVar.t) (constraints : list Constraint1) (values : Valuation) : Valuation :=
  let cs := filter (fun c => eq_op (lhs_var1 c) v) constraints in
  let vals := map (rhs_value1 values) cs in 
  match max_of_list_fold_left vals with
  | Some new_value => PVM.add v (Z.to_nat new_value) values
  | None => values
  end.*)


Lemma filter_empty : forall [A : Type] (f : A -> bool) (nl : list A),
(forall n : A, In n nl -> f n = false) -> 
List.filter f nl = [].
Proof.
intros A f nl H.                   (* 引入函数f、列表nl和前提H *)
induction nl as [|n nl' IHnl].     (* 对列表进行归纳 *)
- (* 基本情况：空列表 *)
  simpl. reflexivity.              (* filter f [] 自动化简为 [] *)
- (* 归纳步骤：n :: nl *)
  simpl. rewrite H. apply IHnl.
  intros; apply H. move : H0; apply List.in_cons.
  apply in_eq.
Qed.

Lemma filter_full : forall [A : Type] (f : A -> bool) (nl : list A),
(forall n : A, In n nl -> f n = true) -> 
List.filter f nl = nl.
Proof.
intros A f nl H.                 
induction nl as [|n nl' IHnl].   
- (* 基本情况：空列表 *)
  simpl. reflexivity.         
- (* 归纳步骤：n :: nl *)
  simpl. rewrite H. rewrite IHnl //.
  intros; apply H. move : H0; apply List.in_cons.
  apply in_eq.
Qed.

Lemma find_add_neq : forall [A : Type] (v a : ProdVar.t) (val : A) (valuation : PVM.t A), v <> a -> PVM.find v (PVM.add a val valuation) = PVM.find v valuation.
Proof.
  intros; apply HiFirrtl.find_add_neq; done.
Qed.

Lemma find_add_eq : forall [A : Type] (a : ProdVar.t) (val : A) (valuation : PVM.t A), PVM.find a (PVM.add a val valuation) = Some val.
Proof.
  intros; apply HiFirrtl.find_add_eq; done.
Qed.

Lemma find_mem : forall [A : Type] (a : ProdVar.t) (valuation : PVM.t A), (exists val, PVM.find a valuation = Some val) <-> PVM.mem a valuation.
Proof.
Admitted.

Lemma find_remove_eq : forall [A : Type] (a : ProdVar.t) (valuation : PVM.t A), PVM.find a (PVM.remove a valuation) = None.
Proof.
Admitted.

Lemma find_remove_neq : forall [A : Type] (v a : ProdVar.t) (valuation : PVM.t A), v <> a -> PVM.find v (PVM.remove a valuation) = PVM.find v valuation.
Proof.
Admitted.

Lemma add_mem : forall [A : Type] (a : ProdVar.t) (val : A) (valuation : PVM.t A), PVM.mem a (PVM.add a val valuation).
Proof.
  intros; apply find_mem. exists val; apply find_add_eq.
Qed.

Lemma mem_add : forall [A : Type] (a hd : ProdVar.t) (val : A) (valuation : PVM.t A), PVM.mem a valuation -> PVM.mem a (PVM.add hd val valuation).
Proof.
  intros. apply find_mem in H. destruct H as [val0 Hfind]. apply find_mem.
  destruct (a == hd) eqn : Heq; move /eqP : Heq => Heq.
  - subst a. exists val; apply find_add_eq.
  - exists val0; rewrite -Hfind; apply find_add_neq; done.
Qed.

Lemma mem_add_or : forall [A : Type] (a hd : ProdVar.t) (val : A) (valuation : PVM.t A), PVM.mem a valuation \/ a == hd <-> PVM.mem a (PVM.add hd val valuation).
Proof.
  split.
  - intros. destruct H. move : H; apply mem_add.
    move /eqP : H => H; subst a. apply find_mem. exists val; apply find_add_eq.
  - intros. apply find_mem in H. destruct H as [val0 Hfind]. destruct (a == hd) eqn : Heq; move /eqP : Heq => Heq; try (right; done).
    left. rewrite find_add_neq in Hfind; try done. apply find_mem. exists val0; done.
Qed.

Lemma find_remove_add : forall [A : Type] (a : ProdVar.t) (val : A) (valuation : PVM.t A), PVM.find a valuation = Some val -> PVM.add a val (PVM.remove a valuation) = valuation.
Proof.
Admitted.

Lemma mem_find_none : forall [A : Type] (a : ProdVar.t) (m : PVM.t A), ~ PVM.mem a m -> PVM.find a m = None.
Proof.
  intros. destruct (PVM.find a m) as [val|] eqn : Hfind; try done.
  assert (exists val, PVM.find a m = Some val) by (exists val; done). apply find_mem in H0. done.
Qed.

Lemma partition_as_filter [A : Type] (f : A -> bool) (l : list A) : List.partition f l = (filter f l, filter (fun x => negb (f x)) l).
Proof.
  induction l as [|x xs IH].
  - (* 基础情况: 空列表 *)
    simpl. reflexivity.
  - (* 归纳步骤: x::xs *)
    simpl. (* 展开 partition 和 filter 定义 *)
    destruct (List.partition f xs) as [trues falses] eqn:Hpart.
    (* 根据 f x 的值分情况证明 *)
    case (f x) eqn:Hfx.
    + (* f x = true 的情况 *)
      simpl. inversion IH. done.
    + (* f x = false 的情况 *)
      simpl. inversion IH. done.
Qed.

Lemma in_split_r_exists_in [A B : Type] (b : B) (l : list (A * B)) : List.In b (List.split l).2 -> exists a, List.In (a, b) l.
Proof.
  intros HIn.
  (* 对列表 l 进行归纳 *)
  induction l as [| (a', b') l IH]; simpl in *.
  - (* 基本情况：空列表 *)
    contradiction.  (* 空列表的 split 返回空列表 *)
  - (* 归纳步骤：非空列表 *)
    destruct (List.split l) as [xs ys] eqn:HSplit.
    simpl in HIn.
    destruct HIn as [Heq | HIn'].
    + (* 情况1: b 等于当前元素的第二个分量 *)
      exists a'.
      left.
      congruence.  (* 自动处理等式 *)
    + (* 情况2: b 在尾部分量列表中 *)
      apply IH in HIn'.
      destruct HIn' as [a'' HIn''].
      exists a''.
      right; assumption.
Qed.

Lemma split2_eq_mapsnd : forall [A B : Type] (l : list (A * B)), (List.split l).2 = List.map snd l.
Proof.
  intros A B. elim. simpl; done. simpl; intros [a b] tl H.
  destruct (List.split tl) as [left right]. simpl. rewrite -H; done.
Qed.

Lemma in_split_remove : forall a coes vars coes' vars' var, List.split (remove term_dec a (combine coes vars)) = (coes', vars') -> ~ In var vars -> ~ In var vars'.
Proof.
  intros a coes vars coes' vars' var Hsplit Hnin Hcont.
  assert (vars' = (split (remove term_dec a (combine coes vars))).2) by (rewrite Hsplit; simpl; done). rewrite H in Hcont.
  apply in_split_r_exists_in in Hcont. destruct Hcont as [a0 Hcont]. apply in_remove in Hcont; move : Hcont => [Hin _].
  apply in_split_r in Hin. simpl in Hin. 
  assert (In var vars). move : Hin; clear. move : coes vars. elim. simpl; intros; done. intros coe_hd coe_tl IH. elim. simpl; intros; done.
    intros var_hd var_tl; intros. simpl in Hin. destruct (split (combine coe_tl var_tl)) as [left right] eqn : Hsplit. simpl in Hin. destruct Hin. 
    simpl; left; done. clear H. specialize (IH var_tl). simpl; right. apply IH. rewrite Hsplit; simpl; done.
  done.
Qed.

Lemma term_dec_refl a : term_dec a a.
Proof.
  destruct a as [coe var].
  case Hdec : (term_dec (coe, var) (coe, var)) => [left|right]; done.
Qed.

Lemma NoDup_remove_notin coe var : forall l1 l2 coes' vars', NoDup l2 -> List.In (coe, var) (combine l1 l2) -> List.split (remove term_dec (coe, var) (combine l1 l2)) = (coes', vars') -> ~ In var vars'.
Proof.
  elim. simpl; intros. inversion H0; done. intros coe_hd coe_tl IH. elim. simpl; intros. inversion H0; done.
  intros var_hd var_tl. intros. clear H. simpl in H1. destruct H1.
  - clear IH. inversion H; subst coe_hd var_hd; clear H. simpl in H2. 
    destruct (term_dec (coe, var) (coe, var)) eqn : Heq; try done. clear e Heq. apply NoDup_cons_iff in H0.
    move : H2 H0.1. apply in_split_remove.
  - simpl in H2. 
    destruct (term_dec (coe, var) (coe_hd, var_hd)) eqn : Heq; try done.
    * inversion e; subst coe_hd var_hd. clear Heq e. 
      apply in_combine_r in H. apply NoDup_cons_iff in H0. move : H0 => [H0 _]. done.
    * simpl in H2. destruct (split (remove term_dec (coe, var) (combine coe_tl var_tl))) as [left right] eqn : Hsplit.
      inversion H2; subst coes' vars'; clear H2. apply IH in Hsplit as H'; try done. 
      intro. simpl in H1. destruct H1; try done.
      subst var_hd. apply in_combine_r in H. apply NoDup_cons_iff in H0. move : H0 => [H0 _]. done.
      apply NoDup_cons_iff in H0. exact H0.2.
Qed.

Lemma remove_NoDup a : forall coes vars coes' vars', List.split (remove term_dec a (combine coes vars)) = (coes', vars') -> NoDup vars -> NoDup vars'.
Proof.
  elim. simpl; intros. inversion H; subst vars'; apply NoDup_nil. intros coe_hd coe_tl IH. elim. simpl; intros. inversion H; subst vars'; apply NoDup_nil.
  intros var_hd var_tl _. intros. simpl in H. destruct (term_dec a (coe_hd, var_hd)).
  - apply IH in H; try done. apply NoDup_cons_iff in H0. exact H0.2.
  - simpl in H. destruct (split (remove term_dec a (combine coe_tl var_tl))) as [left right] eqn : Hsplit.
    inversion H; subst coes' vars'; clear H. apply NoDup_cons_iff. split.
    apply (in_split_remove _ _ _ _ Hsplit). apply NoDup_cons_iff in H0. exact H0.1.
    apply IH in Hsplit; try done. apply NoDup_cons_iff in H0. exact H0.2.
Qed.

Lemma combine_notin (v : ProdVar.t) : forall l, (forall x : term, In x l -> (x.2 == v) = false) -> ~ In v (split l).2.
Proof.
  elim. simpl; intros; done. intros [coe var] tl IH. simpl; intros. destruct (split tl) as [left right] eqn : Hsplit. simpl; intro.
  destruct H0. subst v. assert ((coe, var) = (coe, var) \/ In (coe, var) tl) by (left; done). apply H in H0. rewrite eq_refl in H0. discriminate.
  move : H0; apply IH. intros; apply H. right; done.
Qed.

Lemma add_cover [A : Type] (a : ProdVar.t) (val val' : A) values : PVM.add a val values = PVM.add a val (PVM.add a val' values).
Proof.
Admitted.

Lemma NoDup_app_remove_l [A : Type] (l l' : list A) : NoDup (l++l') -> NoDup l'.
Proof.
  induction l. simpl; done. intro. simpl in H. apply NoDup_cons_iff in H; move : H => [_ H]. apply IHl; done. 
Qed.

Lemma NoDup_app_remove_r [A : Type] (l l' : list A) : NoDup (l++l') -> NoDup l.
Proof.
  move : l. elim. intro; apply NoDup_nil. intros. apply NoDup_cons_iff. simpl in H0. apply NoDup_cons_iff in H0; move : H0 => [H0 H1].
  split. intro. apply (contra_not (in_or_app l l' a)) in H0. intuition.
  move : H1; apply H.
Qed.

Lemma NoDup_app_notin_r [A : Type] : forall (l0 l1 : list A), NoDup (l0 ++ l1) -> forall var, List.In var l0 -> ~List.In var l1.
Proof.
  elim. simpl; intros; done. simpl; intros. destruct H1. subst a. apply NoDup_cons_iff in H0; move : H0 => [H0 _]. apply (contra_not (in_or_app l l1 var)) in H0. intuition. 
  move : H1; apply H. apply NoDup_cons_iff in H0. exact H0.2.
Qed.

Lemma elements_add [A : Type] bounds : forall v (a b : A), PVM.find v bounds = Some a -> 
  exists l0 l1, l0 ++ (v, a) :: l1 = PVM.elements bounds /\ l0 ++ (v, b) :: l1 = PVM.elements (PVM.add v b bounds).
Proof.
Admitted.

Lemma elements_add' [A : Type] bounds : forall v (a : A), PVM.find v bounds = None -> 
  exists l0 l1, l0 ++ l1 = PVM.elements bounds /\ l0 ++ (v, a) :: l1 = PVM.elements (PVM.add v a bounds).
Proof.
Admitted.

Lemma eq_dec : forall x y : ProdVar.t, { eq x y } + { ~ eq x y }.
Proof.
  intros [x1 x2] [y1 y2].
  specialize (ProdVar.eq_dec (x1,x2) (y1,y2)); intro. destruct H. apply eq_from_prodvar_eq in e. left; done.
  right; intro. apply eq_from_prodvar_eq in H. done.
Qed.

Lemma elements_map [A : Type] : forall (f : A -> A) (bounds : PVM.t A), PVM.elements (PVM.map f bounds) = List.map (fun '(key, value) => (key, f value)) (PVM.elements bounds).
Proof.
Admitted.

Lemma find_in_elements [A : Type] : forall x a (bounds : PVM.t A), PVM.find x bounds = Some a <-> List.In (x, a) (PVM.elements bounds).
Proof.
Admitted.

Lemma mem_in_elements [A : Type] : forall x (bounds : PVM.t A), PVM.mem x bounds <-> exists a, List.In (x, a) (PVM.elements bounds).
Proof.
  split; intros.
  - apply find_mem in H. destruct H as [val H]. apply find_in_elements in H. exists val; done.
  - apply find_mem. destruct H as [val H]. apply find_in_elements in H. exists val; done.
Qed.

Fixpoint in_bool (a : ProdVar.t) (l : list ProdVar.t) : bool :=
  match l with
  | [] => false
  | hd :: tl => (hd == a) || in_bool a tl
  end.

Lemma In_in_bool : forall a l, in_bool a l <-> In a l.
Proof.
  intros a l.
  split.
  (* 证明左到右: in_bool a l -> In a l *)
  - (* 进行归纳法 *)
    induction l as [| hd tl IH].
    + (* 基础情况: l = [] *)
      simpl. intros H. discriminate H.
    + (* 递归情况: l = hd :: tl *)
      simpl. intros H.
      (* 通过布尔运算的定义进行分析 *)
      destruct (hd == a) eqn:Heq.
      * (* 如果 hd == a 为真 *)
        move /eqP : Heq => Heq. subst. left. reflexivity.
      * (* 如果 hd == a 为假 *)
        right. apply IH. rewrite orb_false_l in H. done.

  (* 证明右到左: In a l -> in_bool a l *)
  - (* 进行归纳法 *)
    induction l as [| hd tl IH].
    + (* 基础情况: l = [] *)
      simpl. intros H. contradiction.
    + (* 递归情况: l = hd :: tl *)
      simpl. intros H.
      destruct H as [H1 | H2].
      * (* H1: a = hd *)
        rewrite H1 eq_refl orb_true_l //.
      * (* H2: In a tl *)
        apply IH in H2. rewrite H2 orb_true_r //.
Qed.

(************************     Lemmas on constraints       *************************)

Lemma terms_value_eq :
  forall (terms : list term) (init : Z.t) (v0 v1 : Valuation),
    (forall var, In var (map snd terms) -> PVM.find var v0 = PVM.find var v1) ->
    terms_value v0 terms init = terms_value v1 terms init.
Proof.
  intro terms. induction terms as [|(n, var) terms IH]; intros init v0 v1 Hvars; simpl.
  - reflexivity.
  - rewrite Hvars.
    apply IH.
    intros; apply Hvars.
    simpl; right; done.
    simpl; left; done.
Qed.

Lemma power_value_eq :
  forall (terms : list term) (v0 v1 : Valuation),
    (forall var, In var (map snd terms) -> PVM.find var v0 = PVM.find var v1) ->
    power_value v0 terms = power_value v1 terms.
Proof.
  intros terms v0 v1 Hvars.
  unfold power_value.
  destruct terms as [|(n, var) terms]; auto.
  f_equal.
  apply terms_value_eq; done.
Qed.

Lemma satisfies1_on_constrainedvars : forall (c : Constraint1) (v0 v1 : Valuation), (forall (var : ProdVar.t), In var (constraint1_vars c) -> PVM.find var v0 = PVM.find var v1) ->
  satisfies_constraint1 v0 c -> satisfies_constraint1 v1 c.
Proof.
  intros c v0 v1 Hvars Hsat.
  unfold satisfies_constraint1 in *.
  destruct (PVM.find (lhs_var1 c) v0) eqn:Heq_lhs0; [|discriminate].
  rewrite -(Hvars (lhs_var1 c)). rewrite Heq_lhs0.
  unfold rhs_value1 in *.
  rewrite -(terms_value_eq _ _ v0).
  rewrite -(power_value_eq _ v0) //.
  intros; apply Hvars;
  rewrite /constraint1_vars;
  apply List.in_cons;
  apply in_or_app;
  right; done.
  intros; apply Hvars;
  rewrite /constraint1_vars;
  apply List.in_cons;
  apply in_or_app;
  left; done.
  rewrite /constraint1_vars.
  apply in_eq.
Qed. 

Lemma satisfies1_exists_value : forall (a : ProdVar.t) cs values, forallb (satisfies_constraint1 values) cs ->
  (exists c, In c cs /\ lhs_var1 c == a) ->
  exists value, PVM.find a values = Some value.
Proof.
  intros.
  assert (forall x, In x cs -> satisfies_constraint1 values x = true).
  apply forallb_forall; rewrite H //.
  clear H.
  destruct H0 as [c [H0 H]].
  move /eqP : H => H; subst.
  apply H1 in H0; clear H1.
  rewrite /satisfies_constraint1 in H0.
  case H1 : (PVM.find (lhs_var1 c) values) => [val|]; rewrite H1 in H0; try discriminate.
  exists val; reflexivity.
Qed.

Lemma satisfies2le : forall (values : Valuation) (cs : list Constraint1), forallb (satisfies_constraint1 values) cs 
  -> forall (hd : ProdVar.t) (c : Constraint1), In c cs /\ (lhs_var1 c == hd) ->
  match PVM.find hd values with
  | Some val => Z.leb (rhs_value1 values c) (Z.of_nat val)
  | None => false
  end.
Proof.
  intros values cs H hd c Hc.
  assert (forall x, In x cs -> satisfies_constraint1 values x = true).
  apply forallb_forall; try done. clear H.
  move : Hc => [Hc Hc'].
  move /eqP : Hc' => Hc'; subst.
  apply H0 in Hc; clear H0.
  unfold satisfies_constraint1 in Hc.
  destruct (PVM.find (lhs_var1 c) values) eqn:Heq.
  - (* Case: Some val *)
    done.
  - (* Case: None *)
    discriminate.
Qed.

Definition smaller_valuation (v0 v1 : Valuation) : Prop :=
  forall (var : ProdVar.t), PVM.mem var v0 -> 
  (exists value0 value1, PVM.find var v0 = Some value0 /\ PVM.find var v1 = Some value1 /\ value0 <= value1).

Definition le (v0 v1 : Valuation) : Prop :=
  forall (var : ProdVar.t) (value0 : nat),
    PVM.find var v0 = Some value0 ->
    (exists value1, PVM.find var v1 = Some value1 /\ value0 <= value1).

Lemma le_refl : forall (v : Valuation), le v v.
Proof.
  rewrite /le => v x n Hfind. by exists n.
Qed.

Lemma le_trans : forall (v u w : Valuation), le v u -> le u w -> le v w.
Proof.
  rewrite /le => v u w Hv Hu x nv Hfxv.
  move: (Hv _ _ Hfxv) => [nu [Hfxu /leP Hnvnu]].
  move: (Hu _ _ Hfxu) => [nw [Hfxw /leP Hnunw]].
  exists nw. split; first done. apply /leP. by apply (Nat.le_trans _ nu).
Qed.

Lemma smaller_valuation_le_equiv : forall (v0 v1 : Valuation), smaller_valuation v0 v1 <-> le v0 v1.
Proof.
  move => v0 v1. split; rewrite /smaller_valuation /le => H.
  - move => var n Hfind.
    have He : (exists val : nat, PVM.find var v0 = Some val) by (exists n).
    rewrite find_mem in He. case : (H _ He) => value0. case => value1 [Hf0 Hf1].
    rewrite Hfind in Hf0. case: Hf0 => Heq. rewrite Heq; by (exists value1).
  - move => var Hmem. rewrite -find_mem in Hmem.
    case: Hmem => value0 Hf0.
    case: (H _ _ Hf0) => value1 Hv1. by (exists value0; exists value1).
Qed.

Lemma terms_value_le : forall values temp_s, smaller_valuation values temp_s ->
  forall (terms : list term) (init0 init1 : Z.t), Z.leb init0 init1 ->
    (forall var, In var (map snd terms) -> PVM.mem var values) ->
    Z.leb (terms_value values terms init0) (terms_value temp_s terms init1).
Proof.
  intros values temp_s Hsmall.
  elim.
  - simpl; intros; done.
  - simpl; intros.
    apply H.
    apply Zle_bool_plus_mono; try done.
    apply Zle_imp_le_bool.
    apply inj_le.
    apply (elimT leP).
    apply leq_mul; try done.
    destruct (PVM.find a.2 values) eqn : Hfind; rewrite Hfind.
    - rewrite /smaller_valuation in Hsmall.
      assert (exists val, PVM.find a.2 values = Some val) by (exists n; done).
      apply find_mem in H2.
      apply Hsmall in H2; clear Hsmall.
      destruct H2 as [value0 [value1 [H2 [H3 H4]]]].
      rewrite Hfind in H2; inversion H2; subst.
      clear H2.
      rewrite H3; done.
    - destruct (PVM.find a.2 temp_s) eqn : Hfind'; rewrite Hfind'; try done.
    intros; apply H1.
    right; done.
Qed.

Lemma power_value_le : forall values temp_s, smaller_valuation values temp_s ->
  forall (terms : list term),
    (forall var, In var (map snd terms) -> PVM.mem var values) ->
    Z.leb (power_value values terms) (power_value temp_s terms).
Proof.
  intros v0 v1 Hvars terms.
  unfold power_value.
  destruct terms as [|(n, var) terms]; auto.
  intros.
  specialize (terms_value_le Hvars ((n, var) :: terms) 0 0 (Z.leb_refl 0) H); intro.
  apply Zle_imp_le_bool.
  apply Z.pow_le_mono_r; try done.
  apply Zle_bool_imp_le; done.
Qed.

Lemma smaller_rhs_value : forall values temp_s, smaller_valuation values temp_s ->
  forall c, (*forallb (in_set solved) (map snd (rhs_terms1 c)) ->
  forall temp_s, satisfies_all temp_s (filter (constraint_in_set solved) cs) -> *)
  (forall var, In var (rhs_vars c) -> PVM.mem var values) ->
  Z.leb (rhs_value1 values c)(rhs_value1 temp_s c).
Proof.
  intros.
  unfold rhs_value1 in *.
  specialize (terms_value_le H (rhs_terms1 c) (rhs_const1 c) (rhs_const1 c)); intro.
  specialize (power_value_le H (rhs_power c)); intro.
  apply Zle_bool_plus_mono.
  - apply H1.
    apply Z.leb_refl.
    intros.
    apply H0; rewrite /rhs_vars.
    apply in_or_app; left; done.
  - apply H2.
    intros.
    apply H0; rewrite /rhs_vars.
    apply in_or_app; right; done.
Qed.

Definition strict_smaller_valuation (v0 v1 : Valuation) : Prop :=
  (forall (var : ProdVar.t), PVM.mem var v0 -> 
  (exists value0 value1, PVM.find var v0 = Some value0 /\ PVM.find var v1 = Some value1 /\ value0 <= value1))
  /\ (exists (var : ProdVar.t), PVM.mem var v0 -> 
  (exists value0 value1, PVM.find var v0 = Some value0 /\ PVM.find var v1 = Some value1 /\ value0 < value1)).

Lemma split_app : forall A B (l1 l2 : list (A * B)),
  List.split (l1 ++ l2) = (fst (List.split l1) ++ fst (List.split l2), snd (List.split l1) ++ snd (List.split l2)).
Proof.
  induction l1 as [| [x y] l1 IH]; simpl; intros.
  - destruct (List.split l2) as [a b]; simpl; done.
  - rewrite IH. destruct (List.split l1). reflexivity.
Qed.

Lemma forallb_neg_neg : forall A (f: A -> bool) (x: list A),
  (exists y, In y x /\ f y = false) <-> ~ (forallb f x = true).
Proof.
  split.
  - intros [y [Hin Hf]].
    rewrite forallb_forall.
    intro H; apply H in Hin.
    congruence.
  - (* 右推左：非全真 → 存在反例 *)
    intros Hnot. induction x as [|a x' IH].
    + (* 空列表情况 *)
      exfalso. apply Hnot. reflexivity.             (* forallb [] = true *)
    + (* 非空列表情况 *)
      simpl in *. apply not_true_iff_false in Hnot. apply andb_false_iff in Hnot.          (* 分解合取式 *)
      destruct Hnot as [Hf|Hforall].
      * (* 头部元素为假 *)
        exists a. split; auto.
      * (* 尾部存在假元素 *)
        apply not_true_iff_false in Hforall. destruct (IH Hforall) as [y [Hin Hfalse]].
        exists y. split; auto.
Qed.

Lemma terms_value_app cst valuation : forall terms0 terms1, (terms_value valuation (terms0 ++ terms1) cst 
  = terms_value valuation terms0 0 + terms_value valuation terms1 cst)%Z.
Proof.
  intros terms0 terms1.
  unfold terms_value.
  rewrite fold_left_app.
  rewrite Z.add_comm.

  assert (forall l a, fold_left 
    (fun acc ax => Z.add acc (Z.of_nat (fst ax * 
      match PVM.find (snd ax) valuation with
      | Some val => val
      | None => 0
      end))) l a = Z.add a (fold_left (fun acc ax => Z.add acc (Z.of_nat (fst ax * 
      match PVM.find (snd ax) valuation with
      | Some val => val
      | None => 0
      end))) l 0%Z)).
    clear.
    elim. 
    - simpl; intros; rewrite Z.add_0_r //.
    - simpl; intros.
      rewrite H.
      rewrite (H (Z.of_nat
        (a.1 *
        match PVM.find (elt:=nat) a.2 valuation with
        | Some val => val
        | None => 0
        end))).
      rewrite Z.add_assoc //.

  rewrite H.
  rewrite H.
  rewrite (H terms1 cst).
  rewrite -Z.add_assoc (Z.add_comm (fold_left
  (fun (acc : Z) (ax : nat * PVM.key) =>
   acc +
   Z.of_nat
     (ax.1 *
      match PVM.find (elt:=nat) ax.2 valuation with
      | Some val => val
      | None => 0
      end)) terms0 0)%Z (fold_left
      (fun (acc : Z) (ax : nat * PVM.key) =>
       acc +
       Z.of_nat
         (ax.1 *
          match PVM.find (elt:=nat) ax.2 valuation with
          | Some val => val
          | None => 0
          end)) terms1 0)%Z) Z.add_assoc //.
Qed.

Lemma terms_value_cst_add valuation : forall terms cst cst0, 
  (terms_value valuation terms (cst + cst0) = terms_value valuation terms cst + cst0)%Z.
Proof.
  elim. 
  - simpl; intros; intuition.
  - simpl; intros.
    rewrite Z.add_shuffle0.
    apply H.
Qed.

Lemma terms_value_remove cst (hd : ProdVar.t) valuation : forall terms coe hd_val, 
  NoDup terms ->
  List.find (fun p : term => p.2 == hd) terms = Some (coe, hd) ->
  hd_val = match PVM.find (elt:=nat) hd valuation with
    | Some val => val
    | None => 0
    end ->
  (terms_value valuation (List.remove term_dec (coe, hd) terms) cst
  = terms_value valuation terms cst - Z.of_nat (coe * hd_val))%Z.
Proof.
  elim.
  - simpl; intros; discriminate.
  - simpl; intros [coe' hd'] terms'; intros H coe hd_val Hnodup; intros.
    simpl in H0.
    destruct (hd' == hd) eqn : Heq; move /eqP : Heq => Heq.
    - subst.
      inversion H0; subst; clear H0.
      case : (term_dec (coe, hd) (coe, hd)); try done.
      intros; clear a.
      simpl.
      apply NoDup_cons_iff in Hnodup; move : Hnodup => [Hnotin _].
      rewrite notin_remove; try done.
      rewrite terms_value_cst_add Z.add_simpl_r //.
    - simpl.
      case : (term_dec (coe, hd) (coe', hd')); try done.
      intros.
      inversion a; rewrite H4 in Heq; intuition.
      intros.
      simpl.
      rewrite terms_value_cst_add terms_value_cst_add (H _ (match PVM.find (elt:=nat) hd valuation with
        | Some val => val
        | None => 0
        end)); try done.
      rewrite -H1 Z.add_sub_swap //.
      apply (NoDup_remove_1 [] terms' (coe', hd')) in Hnodup. simpl in Hnodup; done.
Qed.

Lemma constraint1_vars2constraints1_vars : forall cs x var, In x cs -> In var (constraint1_vars x) -> In var (constraints1_vars cs).
Proof.
  intros cs. induction cs as [|c1 tl IHcs]; intros x var HIn1 HIn2.
  - (* 基础情况：cs = nil *)
    inversion HIn1. (* HIn1 不成立，因为 nil 中没有元素 *)
  - (* 归纳步骤：cs = c1 :: tl *)
    simpl in *. (* 展开 constraints1_vars 的定义 *)
    destruct HIn1 as [Hc1 | HIn_tl].
    + (* 情况1：x = c1 *)
      subst x. (* 替换 x 为 c1 *)
      destruct HIn2. left; done.
      right; apply in_or_app. left. assumption.
    + (* 情况2：x 在 tl 中 *)
      right; apply in_or_app.
      right; apply IHcs with (x := x); assumption.
Qed.

Lemma constraints1_vars_app : forall l0 l1, constraints1_vars (l0 ++ l1) = constraints1_vars l0 ++ constraints1_vars l1.
Proof.
  induction l0 as [| c1 tl IH].
  - (* 基础情况：l0 = nil *)
    simpl. reflexivity.
  - (* 归纳步骤：假设 l0 = c1 :: tl *)
    intros; simpl.
    rewrite IH.
    rewrite -{1}cat1s. rewrite -(cat1s (lhs_var1 c1) ((((map snd (rhs_terms1 c1) ++ map snd (rhs_power c1)) ++ constraints1_vars tl)%SEQ ++ constraints1_vars l1)%list)).
    apply app_inv_head_iff.
    remember ((map snd (rhs_terms1 c1) ++ map snd (rhs_power c1)))%SEQ as l0.
    intuition.
Qed.

Lemma find_some_sat_ctr1 : forall (v : Valuation) (cs : list Constraint1) (c : Constraint1),
    find (fun c1 : Constraint1 => negb (satisfies_constraint1 v c1)) cs = Some c ->
    negb (satisfies_constraint1 v c).
Proof.
  move => v cs c H. move: (find_some _ _ H) => [Hin Hsat]. exact: Hsat.
Qed.

Lemma find_some_sat_ctr2 : forall (v : Valuation) (cs : list Constraint2) (c : Constraint2),
    find (fun c2 : Constraint2 => negb (satisfies_constraint2 v c2)) cs = Some c ->
    negb (satisfies_constraint2 v c).
Proof.
  move => v cs c H. move: (find_some _ _ H) => [Hin Hsat]. exact: Hsat.
Qed.

Lemma find_some_in_ctr1 : forall (v : Valuation) (cs : list Constraint1) (c : Constraint1),
    find (fun c1 : Constraint1 => negb (satisfies_constraint1 v c1)) cs = Some c ->
    List.In c cs.
Proof.
  move => v cs c H. move: (find_some _ _ H) => [Hin Hsat]. exact: Hin.
Qed.

Lemma find_some_in_ctr2 : forall (v : Valuation) (cs : list Constraint2) (c : Constraint2),
    find (fun c2 : Constraint2 => negb (satisfies_constraint2 v c2)) cs = Some c ->
    List.In c cs.
Proof.
  move => v cs c H. move: (find_some _ _ H) => [Hin Hsat]. exact: Hin.
Qed.

Lemma sat_ctr1_eq : forall (c : Constraint1) (v v' : Valuation),
    PVM.find (lhs_var1 c) v = PVM.find (lhs_var1 c) v' ->
    (forall x : ProdVar.t, List.In x (rhs_vars c) -> PVM.find x v = PVM.find x v') ->
    satisfies_constraint1 v c = satisfies_constraint1 v' c.
Proof.
  move => c v1 v2 Hleq Hreq. apply eq_iff_eq_true.
  have H : (forall x : ProdVar.t, List.In x (constraint1_vars c) ->
                                  PVM.find x v1 = PVM.find x v2).
  {
    move => x. rewrite /constraint1_vars => Hin.
    move: (in_inv Hin) => [<- | Hinr]; first done.
    by apply Hreq.
  }
  split.
  - by (apply satisfies1_on_constrainedvars).
  - apply satisfies1_on_constrainedvars => x Hin. rewrite (H x Hin) //=.
Qed.  

Lemma rhs_value1_eq : forall (c : Constraint1) (v v' : Valuation),
    (forall x : ProdVar.t, List.In x (rhs_vars c) -> PVM.find x v = PVM.find x v') ->
    rhs_value1 v c = rhs_value1 v' c.
Proof.
  rewrite /rhs_value1 /rhs_vars => c v1 v2 H. 
  have H1 : forall x : ProdVar.t,
      List.In x (map snd (rhs_terms1 c)) -> PVM.find x v1 = PVM.find x v2.
  { move => x Hin. apply H. apply in_or_app. by left. }
  have H2 : forall x : ProdVar.t,
      List.In x (map snd (rhs_power c)) -> PVM.find x v1 = PVM.find x v2.
  { move => x Hin. apply H. apply in_or_app. by right. }
  rewrite (terms_value_eq _ _ _ _ H1) (power_value_eq _ _ _ H2) //=.
Qed.  

Lemma unsat_ctr1_le : forall (c : Constraint1) (v v' : Valuation) (n n' : nat),
    (forall x : ProdVar.t, List.In x (rhs_vars c) -> PVM.find x v = PVM.find x v') ->
    PVM.find (lhs_var1 c) v = Some n ->
    PVM.find (lhs_var1 c) v' = Some n' ->
    n <= n' ->
    ~~ satisfies_constraint1 v' c ->
    ~~ satisfies_constraint1 v c.
Proof.
  rewrite /satisfies_constraint1 => c v1 v2 n1 n2 Hreq -> -> Hle.
  rewrite (rhs_value1_eq _ _ _ Hreq).
  apply contra => Hrhsn1. move: Hle => /leP Hle.
  apply inj_le in Hle. move: Hle => /Z.leb_spec0 Hle.
  by apply (Zle_bool_trans _ _ _ Hrhsn1).
Qed.

Definition terms_value_nat (v : Valuation) (terms : list term) (init : nat) : nat :=
  fold_left (fun acc '(bi, xi) =>
               let vi := match PVM.find xi v with
                         | Some val => val
                         | None => 0 
                         end in
               acc + (bi * vi)) 
    terms init.

Lemma terms_value_nat_eq : forall (terms : list term) (init : nat) (v v' : Valuation),
    (forall var, List.In var (map snd terms) -> PVM.find var v = PVM.find var v') ->
    terms_value_nat v terms init = terms_value_nat v' terms init.
Proof.
  elim => [|[n var] terms IH]; first done.
  move => init v1 v2 Hvars /=.
  rewrite Hvars /=; last by left.
  apply IH => x Hin. apply Hvars => /=. by right.
Qed.  

Lemma satisfies_constraint2_equation : forall (c : Constraint2) (v : Valuation),
    satisfies_constraint2 v c = (terms_value_nat v (rhs_terms2 c) 0 <=? lhs_const2 c).
Proof. reflexivity. Qed.

Lemma sat_ctr2_eq : forall (c : Constraint2) (v v' : Valuation),
    (forall x : ProdVar.t, List.In x (map snd (rhs_terms2 c)) -> PVM.find x v = PVM.find x v') ->
    satisfies_constraint2 v c = satisfies_constraint2 v' c.
Proof.
  move => c v1 v2 H. rewrite !satisfies_constraint2_equation.
  rewrite (terms_value_nat_eq _ _ _ _ H). done.
Qed.

Lemma sat_ctr1_lhs_find_some : forall (c : Constraint1) (v : Valuation),
    satisfies_constraint1 v c -> exists n, PVM.find (lhs_var1 c) v = Some n.
Proof.
  rewrite /satisfies_constraint1 => c v.
  case (PVM.find (lhs_var1 c) v) => [n|]; [by exists n | done].
Qed.


(* ======================= satisfy all constraints ======================= *)
(* ==
   == added by jx
   == used for proofs about bab
   == 
   == *)

Fixpoint satisfies_all_constraint1 (v : Valuation) (cs : list Constraint1) : bool :=
  match cs with
  | nil => true
  | c :: cs' => andb (satisfies_constraint1 v c) (satisfies_all_constraint1 v cs')
  end.

Fixpoint satisfies_all_constraint2 (v : Valuation) (cs : list Constraint2) : bool :=
  match cs with
  | nil => true
  | c :: cs' => andb (satisfies_constraint2 v c) (satisfies_all_constraint2 v cs')
  end.

Lemma sat_all_in_ctr1 : forall (v : Valuation) (cs : list Constraint1) (c : Constraint1),
    satisfies_all_constraint1 v cs -> List.In c cs -> satisfies_constraint1 v c.
Proof.
  move => v. elim => [|hd tl IH]; first done.
  rewrite /= => c /andP [Hsathd Hsattl] [Hinhd | Hintl].
  - by rewrite -Hinhd.
  - by apply IH.
Qed.

Lemma sat_all_in_ctr2 : forall (v : Valuation) (cs : list Constraint2) (c : Constraint2),
    satisfies_all_constraint2 v cs -> List.In c cs -> satisfies_constraint2 v c.
Proof.
  move => v. elim => [|hd tl IH]; first done.
  rewrite /= => c /andP [Hsathd Hsattl] [Hinhd | Hintl].
  - by rewrite -Hinhd.
  - by apply IH.
Qed.

Lemma in_sat_all_ctr1 : forall (v : Valuation) (cs : list Constraint1),
    (forall c, List.In c cs -> satisfies_constraint1 v c) ->
    satisfies_all_constraint1 v cs.
Proof.
  move => v. elim => [|hd tl IH]; first done.
  rewrite /= => H. apply /andP; split.
  - apply H. left; done.
  - apply IH. move => c Hin. apply H. by right.
Qed.    

Lemma in_sat_all_ctr2 : forall (v : Valuation) (cs : list Constraint2),
    (forall c, List.In c cs -> satisfies_constraint2 v c) ->
    satisfies_all_constraint2 v cs.
Proof.
  move => v. elim => [|hd tl IH]; first done.
  rewrite /= => H. apply /andP; split.
  - apply H. left; done.
  - apply IH. move => c Hin. apply H. by right.
Qed.    

Lemma find_none_sat_all_ctr1 : forall (v : Valuation) (cs : list Constraint1),
    find (fun c : Constraint1 => negb (satisfies_constraint1 v c)) cs = None ->
    satisfies_all_constraint1 v cs.
Proof.
  move => v cs Hfind. move: (find_none _ _ Hfind) => H.
  apply in_sat_all_ctr1 => c Hin. apply negb_false_iff. by apply H. 
Qed.

Lemma find_none_sat_all_ctr2 : forall (v : Valuation) (cs : list Constraint2),
    find (fun c : Constraint2 => negb (satisfies_constraint2 v c)) cs = None ->
    satisfies_all_constraint2 v cs.
Proof.
  move => v cs Hfind. move: (find_none _ _ Hfind) => H.
  apply in_sat_all_ctr2 => c Hin. apply negb_false_iff. by apply H. 
Qed.

Lemma in_find_none: forall [A : Type] (f : A -> bool) (l : seq.seq A),
  (forall x : A, List.In x l -> f x = false) -> find f l = None.
Proof.
  move => A f. elim => [|a l IH]; first done.
  rewrite /= => H.
  have Ha : f a = false by (apply H; left).
  rewrite Ha. apply IH. move => x Hin. apply H. by right.
Qed.

Lemma sat_all_ctr1_find_none : forall (v : Valuation) (cs : list Constraint1),
    satisfies_all_constraint1 v cs ->
    find (fun c : Constraint1 => negb (satisfies_constraint1 v c)) cs = None.
Proof.
  move => v cs Hsat. apply in_find_none. move=> c Hin.
  apply negb_false_iff. apply (sat_all_in_ctr1 v cs); done.
Qed.
  
Lemma sat_all_ctr2_find_none : forall (v : Valuation) (cs : list Constraint2),
    satisfies_all_constraint2 v cs ->
    find (fun c : Constraint2 => negb (satisfies_constraint2 v c)) cs = None.
Proof.
  move => v cs Hsat. apply in_find_none. move=> c Hin.
  apply negb_false_iff. apply (sat_all_in_ctr2 v cs); done.
Qed.


End constraint.

(*Section test_constraint.

Definition ProdVar.t := [finType of 'I_10].
Check ProdVar.t. 

Fixpoint n_V (n : nat) : ProdVar.t :=
  match n with
  | 0 => ord0
  | S m => ordS (n_V m)
  end.

Definition v0 := PVM.empty.
(*Definition v1 := PVM.add (n_V 0) 1 v0.*)

(* 创建ϕ1类型的约束示例 *)
Definition example_phi1_constraint : Constraint ProdVar.t :=
  Phi1 {|
    lhs_var1 := ord0;
    rhs_const1 := -2;
    rhs_terms1 := [(2, ordS ord0); (3, ordS (ordS ord0))]
  |}.

(* 创建ϕ2类型的约束示例 *)
Definition example_phi2_constraint : Constraint ProdVar.t :=
  Phi2 {|
    lhs_const2 := 2;
    rhs_terms2 := [(1, ord0); (3, ordS ord0)]
  |}.

(* Compute (constraint1_exclusive_set ProdVar.t [:: ordS (ordS ord0)] {|
  lhs_var1 := ord0;
  rhs_const1 := -2;
  rhs_terms1 := [(2, ordS ord0); (3, ordS (ordS ord0))]
|}). *)

(* FIRLIS 约束集合 *)
Definition firlis_constraints : list (Constraint ProdVar.t) := [
  example_phi1_constraint;
  example_phi2_constraint
].

(* 示例变量赋值 *)
Definition example_valuation0 := (add_valuation ProdVar.t) (initial_valuation ProdVar.t) ord0 1.
Definition example_valuation1 := (add_valuation ProdVar.t) example_valuation0 (ordS ord0) 6.
Definition example_valuation2 := (add_valuation ProdVar.t) example_valuation1 (ordS (ordS ord0)) 2.

Compute (example_valuation2 (ordS ord0)).

(* 检查示例 *)
Eval compute in (satisfies_constraint example_valuation2 example_phi1_constraint).
(* 期望输出:  *)

Eval compute in (satisfies_constraint example_valuation2 example_phi2_constraint).
(* 期望输出:  *)

End test_constraint.
*)
