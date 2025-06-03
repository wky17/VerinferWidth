From HB Require Import structures.
From Coq Require Import ZArith Arith List Ascii String Lia FMaps.
From mathcomp Require Import all_ssreflect.
From mathcomp.tarjan Require Import kosaraju tarjan_nocolors acyclic acyclic_tsorted.
From Solver Require Import Env LoFirrtl HiEnv HiFirrtl branch_and_bound constraints floyd_sc scc graph extract_cs extract_cswithmin.
Import ListNotations.

Section acyclic.

Fixpoint max_list (l : seq Constraint1) (values : Valuation) (init : Z.t): Z.t :=
  match l with
  | nil => init
  | t :: tl => max_list tl values (Z.max init (rhs_value1 values t))
  end.

Definition initialize_tbsolved' (*hd : ProdVar.t*) (values : Valuation) (constraints : list Constraint1) : Z.t :=
  (*let v := match PVM.find hd values with
          | Some v' => v'
          | _ => 0
          end in*)
  max_list constraints values (*Z.of_nat v*) 0.

Fixpoint initialize_tbsolved (tbsolved : list ProdVar.t) (values : Valuation) (cs1 : PVM.t (list Constraint1)) : Valuation :=
  match tbsolved with
  | nil => values
  | hd :: tl => match PVM.find hd cs1 with
              | Some constraints => let nv := initialize_tbsolved' (*hd*) values constraints in 
              (*let nvalues := initialize_tbsolved tl values cs1 in PVM.add hd nv nvalues*)
                initialize_tbsolved tl (PVM.add hd (Z.to_nat nv) values) cs1
              | _ => values
              end
  end.

End acyclic.

Definition is_simple_cycle (l : list ProdVar.t) (cs : list Constraint1) : bool :=
  let cs' := filter (constraint1_in_set l) cs in
  forallb (fun c => match rhs_terms1 c with
                  | nil
                  | [::(1,_)] => true
                  | _ => false
                  end) cs'.

Fixpoint solve_alg (res : list (list ProdVar.t)) (solved : list (ProdVar.t)) (values : Valuation) (cs1 : PVM.t (list Constraint1)) : option Valuation :=
match res with
| nil => Some values
| [:: v] :: tl => (* acyclic *)
  match PVM.find v cs1 with
  | Some constraints =>
      let (cs_have_v, cs) := List.partition (fun c => in_bool v (rhs_vars c)) constraints in
      if forallb (fun c => (Z.leb (rhs_const1 c) 0) &&
        (rhs_terms1 c == [(1, v)])) (List.map (remove_solved_c values) cs_have_v) then
        let nv := PVM.add v (Z.to_nat (initialize_tbsolved' values cs)) values in
        let ns := [:: v] ++ solved  in
        (* 检查新解出来的v是否满足Phi2约束 
        let check_cs2 := filter (constraint2_in_set ns) cs2 in
        if (forallb (satisfies_constraint2 nv) check_cs2) then *)
          solve_alg tl ns nv cs1
        else None
  | _ => None
  end
| hd :: tl => 
  let tbsolved_cs := extract_cs hd cs1 in
  let tbsolved_cs' := remove_solveds values tbsolved_cs in
  if is_simple_cycle hd tbsolved_cs then (* simple_cycle *)
    (*match solve_simple_cycle hd tbsolved_cs cs2 solved nv0 with*)
    match solve_simple_cycle hd tbsolved_cs' with
    | Some nv => match merge_solution hd values nv with
      | Some new_values =>  solve_alg tl (hd ++ solved) new_values cs1 
      | _ => None
      end
    | None => None
    end
  else (* scc *)
    let remove_only_const := List.filter (fun c => List.length (rhs_terms1 c) != 0) tbsolved_cs' in
    match solve_ubs hd hd remove_only_const with
    | Some ubs => let nv0 := initialize_tbsolved hd values cs1 in
                  let bs := mergeValuations nv0 ubs in
                  (*let cs2' := filter (constraint2_in_set hd) cs2 in*)
      match (*branch_and_bound_natural'*) bab_bin hd bs tbsolved_cs' [] with
      | Some nv => match merge_solution hd nv0 nv with
        | Some new_values => solve_alg tl (hd ++ solved) new_values cs1 
        | _ => None
        end
      | _ => None
      end
    | None => None
    end
end.

Definition solve_alg_check (res : list (list ProdVar.t)) (cs1 : PVM.t (list Constraint1)) (cs2 : list min_rhs) : option Valuation :=
  match solve_alg res [] initial_valuation cs1 with
  | Some value => if (forallb (fun c => Z.leb (min_rhs_value value c) 1%Z) cs2) then Some value else None
  | _ => None
  end.

Lemma max_list_correctness values : forall cs init, Z.leb init (max_list cs values init) /\ (forall (c : Constraint1), List.In c cs -> Z.leb (rhs_value1 values c) (max_list cs values init)).
Proof.
  elim. 
  - (* 基础情况: cs = nil *)
    intros; split.
    + simpl. apply Z.leb_refl.
    + intros c H. inversion H.  (* 空列表无元素，矛盾 *)
  - (* 归纳情况: cs = c :: cs' *)
    intros hd tl IH init.
    simpl. split.
    + (* 证明第一部分: max_list >= init *)
      destruct (IH (Z.max init (rhs_value1 values hd))) as [H1 _].
      apply Zle_bool_trans with (n := init) (m := Z.max init (rhs_value1 values hd)); try done.
      apply Zle_imp_le_bool.
      apply Z.le_max_l.
    + (* 证明第二部分: 对所有c' \in c::cs'，max_list >= rhs_value1 c' *)
      intros c' Hc'.
      destruct (IH (Z.max init (rhs_value1 values hd))) as [_ H2].
      destruct Hc' as [-> | Hc'].
      * (* 子情况1: c' = c *)
        apply Zle_bool_trans with (n := rhs_value1 values c') (m := Z.max init (rhs_value1 values c')); try done.
        apply Zle_imp_le_bool.
        apply Z.le_max_r.
        move : (IH (Z.max init (rhs_value1 values c'))) => [IH' _]; assumption.
      * (* 子情况2: c' \in cs' *)
        apply H2 in Hc'.
        assumption.
Qed.

Lemma max_list_gt0 value : forall cs1 init, Z.le 0 init -> Z.le 0 (max_list cs1 value init).
Proof.
  elim.
  - (* Base case: empty list *)
    simpl; done.
  - (* Inductive step: t :: tl *)
    simpl; intros.
    apply H.
    apply Z.le_trans with (m := init).
    + assumption.
    + apply Z.le_max_l.
Qed.

Lemma satisfies1_initialize : forall (c : Constraint1) cs1 (a : ProdVar.t) init value, Z.le 0 init -> List.In c cs1 -> lhs_var1 c == a -> ~ List.In (lhs_var1 c) (rhs_vars c) -> satisfies_constraint1 (PVM.add a (Z.to_nat (max_list cs1 value init)) value) c.
Proof.
  simpl; intros c cs1 a init value Hinit H H0 H1.
  specialize (max_list_correctness value cs1 init); intros [H2 H3].
  rewrite /satisfies_constraint1.
  move /eqP : H0 => H0; subst.
  rewrite find_add_eq.
  unfold rhs_value1 in *.
  rewrite (terms_value_eq _ _ _ value).
  rewrite (power_value_eq _ _ value).
  apply H3 in H; clear H3.
  rewrite -> (Z2Nat.id _ (max_list_gt0 _ _ _ Hinit)); done.
  (*move /leP : H => H.
  move : H; apply Nat.leb_le.*)
  intros; rewrite find_add_neq //.
  rewrite /rhs_vars in H1.
  assert (forall [A : Type] (a b : A) (ls ls' : list A), List.In a ls' -> ~ List.In b (ls ++ ls') -> a <> b).
    clear; intros A a b ls ls' H_in H_not_in.
    intro H_eq.  (* 假设 a = b *)
    rewrite H_eq in H_in.  (* 将H_in中的a替换为b，得到In b ls *)
    apply H_not_in.  (* 导出矛盾 *)
    apply in_or_app.  (* 分解连接列表的成员关系 *)
    right.  (* 选择左边列表的情况 *)
    assumption.  (* 应用已得到的In b ls *)
  move : H0 H1; apply H4.
  intros; rewrite find_add_neq //.
  rewrite /rhs_vars in H1.
  assert (forall [A : Type] (a b : A) (ls ls' : list A), List.In a ls -> ~ List.In b (ls ++ ls') -> a <> b).
  clear; intros A a b ls ls' H_in H_not_in.
  intro H_eq.  (* 假设 a = b *)
  rewrite H_eq in H_in.  (* 将H_in中的a替换为b，得到In b ls *)
  apply H_not_in.  (* 导出矛盾 *)
  apply in_or_app.  (* 分解连接列表的成员关系 *)
  left.  (* 选择左边列表的情况 *)
  assumption.  (* 应用已得到的In b ls *)
  move : H0 H1; apply H4.
Qed.

Lemma remove_solved_correctness : forall terms cst values values0 new_terms new_cst, remove_solved values terms = (new_terms, new_cst) -> 
  (forall var, PVM.mem var values -> PVM.find var values = PVM.find var values0) ->
  terms_value values0 terms cst = terms_value values0 new_terms (cst + new_cst).
Proof.
  clear; elim. 
  - simpl; intros. inversion H; simpl. rewrite Z.add_0_r //.
  - simpl; intros [coe var] tl IH; intros.
    case Hfind : (PVM.find (elt:=nat) var values) => [val|]; rewrite Hfind in H. 
    * (* find some, var is solved *)
      simpl. destruct (remove_solved values tl) as [new_terms_tl new_cst_tl] eqn : Hnew_tl.
      inversion H; clear H; subst. rewrite -H0. rewrite Hfind. 
      rewrite (IH _ _ _ _ _ Hnew_tl); try done. rewrite (Z.add_comm new_cst_tl (Z.of_nat (coe * val))) Z.add_assoc //.
      apply find_mem. exists val; done.
    * (* find none, var is tbd *)
      simpl. destruct (remove_solved values tl) as [new_terms_tl new_cst_tl] eqn : Hnew_tl.
      inversion H; clear H; subst. simpl.
      rewrite terms_value_cst_add. rewrite terms_value_cst_add. apply Z.add_cancel_r.
      rewrite (IH _ _ _ _ _ Hnew_tl) //.
Qed.

Lemma remove_solved_c_correctness values values0 x : 
  (forall var, PVM.mem var values -> PVM.find var values = PVM.find var values0) ->
  rhs_value1 values0 x = rhs_value1 values0 (remove_solved_c values x).
Proof.
  intros; rewrite /remove_solved_c.
  destruct (remove_solved values (rhs_terms1 x)) as [new_terms new_cst] eqn : Hnew.
  rewrite /rhs_value1; simpl. apply Z.add_cancel_r.
  apply (remove_solved_correctness _ (rhs_const1 x) _ values0) in Hnew; try done.
Qed.

Lemma find_merge_notin_eq nv : forall tbsolved v initial new_values, ~List.In v tbsolved -> 
  merge_solution tbsolved initial nv = Some new_values -> PVM.find v initial = PVM.find v new_values.
Proof.
  elim. simpl; intros. inversion H0; done.
  simpl; intros. case Hfind : (PVM.find a nv) => [val|]; rewrite Hfind in H1; try discriminate. apply (H v) in H1. rewrite -H1 find_add_neq //.
    intro Heq; subst. intuition. intro Hin. intuition.
Qed.

Lemma find_merge_in_eq nv : forall tbsolved v initial new_values, NoDup tbsolved -> List.In v tbsolved -> 
  merge_solution tbsolved initial nv = Some new_values -> PVM.find v nv = PVM.find v new_values.
Proof.
  elim. simpl; intros. inversion H0; done.
  simpl; intros. case Hfind : (PVM.find a nv) => [val|]; rewrite Hfind in H2; try discriminate.
  destruct H1.
  * subst. apply NoDup_cons_iff in H0. move : H0 => [Hnotin Hnodup]. specialize (find_merge_notin_eq _ _ _ _ _ Hnotin H2); intro.
    rewrite find_add_eq in H0. rewrite Hfind -H0 //.
  * apply (H v) in H2; try done. apply NoDup_cons_iff in H0. exact H0.2.
Qed.

Lemma find_init_notin_eq c1map : forall tbsolved v initial, ~List.In v tbsolved -> (forall var, List.In var tbsolved -> exists cs, PVM.find var c1map = Some cs) ->
  PVM.find v initial = PVM.find v (initialize_tbsolved tbsolved initial c1map).
Proof.
  elim. simpl; intros; done.
  simpl; intros. destruct (H1 a) as [cs Hfind]. left; done. rewrite Hfind.
    rewrite -H. rewrite find_add_neq //. intuition. intuition.
    intros; apply H1. right; done.
Qed.

Lemma none_find_merge_none nv: forall tbsolved v new_values initial, merge_solution tbsolved initial nv = Some new_values -> 
  ~List.In v tbsolved -> PVM.find v initial = None -> PVM.find v nv = None -> PVM.find v new_values = None.
Proof.
  elim. simpl; intros. inversion H. rewrite -H4 //.
  simpl; intros. case Hfind : (PVM.find a nv) => [val|]; rewrite Hfind in H0; try discriminate.
    apply (H v) in H0; try done. intros Hin. intuition. rewrite find_add_neq //. intros Heq. intuition.
Qed.

Lemma none_find_init_none c1map : forall tbsolved v initial, 
  ~List.In v tbsolved -> PVM.find v initial = None -> PVM.find v (initialize_tbsolved tbsolved initial c1map) = None.
Proof.
  elim. simpl; intros; done.
  simpl; intros. case Hfind : (PVM.find a c1map) => [cs|]; try done. apply H. intro Hin; intuition. 
  rewrite find_add_neq //. intro Heq; intuition.
Qed.

Lemma remove_solved_terms_value_eq nv values initial : forall terms new_terms new_cst cst,
  (forall var, (exists val, PVM.find var initial = Some val /\ PVM.find var nv = Some val) \/ (PVM.find var initial = None /\ PVM.find var values = PVM.find var nv)) ->
  remove_solved initial terms = (new_terms, new_cst) -> 
  terms_value nv terms cst = terms_value values new_terms (cst + new_cst).
Proof.
  intros temrs new_terms new_cst cst H1. move : temrs new_terms new_cst cst.
  elim. simpl; intros. inversion H; simpl. rewrite Z.add_0_r //.
  simpl; intros [coe var]; simpl; intros. destruct (remove_solved initial l) as [terms' cst'] eqn : Htl.
  specialize (H1 var). destruct H1.
  * destruct H1 as [val [Hinit Hnv]]. rewrite Hinit in H0; rewrite Hnv. inversion H0. 
    rewrite (H terms' cst' (cst + Z.of_nat (coe * val))%Z). rewrite H2. rewrite (Z.add_comm cst' (Z.of_nat (coe * val))) Z.add_assoc //.
    try done.
  * destruct H1 as [Hinit Hv]. rewrite Hinit in H0. inversion H0. rewrite -H3; clear H2 H3 H0 new_terms new_cst. simpl.
    rewrite Hv. rewrite (H terms' cst'); try done. rewrite -Z.add_assoc (Z.add_comm (Z.of_nat (coe * match PVM.find (elt:=nat) var nv with
      | Some val => val
      | None => 0
      end)) cst') Z.add_assoc //.
Qed.

Lemma remove_solveds_sat values tbsolved : forall cs initial nv, forallb (satisfies_constraint1 values) (remove_solveds initial cs) -> 
  (forall c, List.In c cs -> List.In (lhs_var1 c) tbsolved /\ rhs_power c = nil) ->
  (forall var, List.In var tbsolved -> (exists val, PVM.find var values = Some val /\ PVM.find var nv = Some val)) ->
  (forall (var : ProdVar.t), (exists val, PVM.find var initial = Some val /\ PVM.find var nv = Some val) \/ (PVM.find var initial = None /\ PVM.find var values = PVM.find var nv)) ->
  forallb (satisfies_constraint1 nv) cs.
Proof.
  intros cs initial nv H0 H1 Hfind0 Hfind1. move : cs H0 H1.
  elim. simpl; done.
  simpl; intros. move /andP : H0 => [Hsat Hsats]. apply H in Hsats. apply rwP with (P := satisfies_constraint1 nv a /\ forallb (satisfies_constraint1 nv) l).
    apply andP. split; try done. clear H Hsats.
  unfold satisfies_constraint1 in *. rewrite /remove_solved_c in Hsat. destruct (remove_solved initial (rhs_terms1 a)) as [new_terms new_cst] eqn : Hremove. simpl in Hsat.
  specialize (H1 a) as Hlhs. assert (a = a \/ List.In a l) by (left;done). apply Hlhs in H; clear Hlhs. move : H => [Hlhs Hpower].
  apply Hfind0 in Hlhs. destruct Hlhs as [lhs_val [Hv Hnv]]. rewrite Hnv; rewrite Hv in Hsat. 
  unfold rhs_value1 in *; simpl in Hsat.
  assert (terms_value nv (rhs_terms1 a) (rhs_const1 a) + power_value nv (rhs_power a) = terms_value values new_terms (rhs_const1 a + new_cst) +
    power_value values (rhs_power a))%Z. rewrite Hpower; simpl; rewrite Z.add_0_r. rewrite Z.add_0_r.
    apply remove_solved_terms_value_eq with (initial := initial); try done. rewrite H //.
  intros; apply H1. right; done.
Qed.

Lemma forallb2satisfies_all_constraint1 values: forall cs, forallb (satisfies_constraint1 values) cs <-> satisfies_all_constraint1 values cs.
Proof.
  split. induction cs as [|c cs' IH]. simpl; intros; done. simpl; intros. move /andP : H => [H H1]. apply IH in H1. rewrite H H1 //.
  induction cs as [|c cs' IH]. simpl; intros; done. simpl; intros. move /andP : H => [H H1]. apply IH in H1. rewrite H H1 //.
Qed.

Lemma forallb2satisfies_all_constraint2 values: forall cs, forallb (satisfies_constraint2 values) cs <-> satisfies_all_constraint2 values cs.
Proof.
  split. induction cs as [|c cs' IH]. simpl; intros; done. simpl; intros. move /andP : H => [H H1]. apply IH in H1. rewrite H H1 //.
  induction cs as [|c cs' IH]. simpl; intros; done. simpl; intros. move /andP : H => [H H1]. apply IH in H1. rewrite H H1 //.
Qed.

Lemma merge_solution_mem_or nv : forall a initial new_values, merge_solution a initial nv = Some new_values -> forall v, (PVM.mem v new_values <-> List.In v a \/ PVM.mem v initial).
Proof.
  elim. simpl; intros. split; intros. inversion H; right; done. destruct H0; try done. inversion H;rewrite -H2; done.
  simpl; intros. case Hfind : (PVM.find (elt:=nat) a nv) => [val|]; rewrite Hfind in H0; try discriminate. split.
  * intros. apply (H _ _ H0) in H1. destruct H1. left; right; done. apply mem_add_or in H1. destruct H1. right; done. left; left. move /eqP : H1 => H1. rewrite H1 //.
  * intros. apply (H _ _ H0). destruct H1. destruct H1. right. apply mem_add_or; right; rewrite H1 //.
    left; done. right. apply mem_add_or; left; done.
Qed.

(*Lemma solve_simple_cycle_mem_or cs1 cs2 solved : forall tbsolved initial new_values, solve_simple_cycle tbsolved cs1 cs2 solved initial = Some new_values -> 
  forall v, (PVM.mem v new_values <-> List.In v tbsolved \/ PVM.mem v initial).
Proof.
  intros. rewrite /solve_simple_cycle in H. case Hsolve : (solve_simple_cycle_rec (Datatypes.length tbsolved) tbsolved
    [seq tempc <- cs1 | Datatypes.length (rhs_terms1 tempc) == 1] initial) => [s|]; rewrite Hsolve in H; try discriminate.
    case Hsat2 : (all (satisfies_constraint2 s)
      [seq x <- cs2 | constraint2_in_set (solved ++ tbsolved) x]); rewrite Hsat2 in H; try discriminate. inversion H. rewrite H1 in Hsolve. clear H H1 Hsat2 s.
  remember (Datatypes.length tbsolved) as n. clear Heqn.
  move : tbsolved initial n new_values Hsolve.
  elim. simpl; intros. split; intros. inversion Hsolve; right; done. destruct H; try done. inversion Hsolve. rewrite -H1; done.
  simpl; intros. case Hnvs : (solve_simple_cycle' n a
    [seq tempc <- cs1 | Datatypes.length (rhs_terms1 tempc) == 1] initial) => [nvs|]; rewrite Hnvs in Hsolve; try discriminate. split.
  rewrite /solve_simple_cycle' in Hnvs. case Hfinda : (PVM.find a initial) => [val|]; rewrite Hfinda in Hnvs; try discriminate.
  case Hval : (simplify_constraints a n (Z.of_nat val)
    (find_constraint1s a
      [seq tempc <- cs1 | Datatypes.length (rhs_terms1 tempc) == 1])
    [seq tempc <- cs1 | Datatypes.length (rhs_terms1 tempc) == 1] initial) => [new_value|]; rewrite Hval in Hnvs; try discriminate.
  inversion Hnvs. clear Hfinda Hval val Hnvs. 
  * intros. apply (H _ _ _ Hsolve) in H0. destruct H0. left; right; done.
    rewrite -H1 in H0. apply mem_add_or in H0. destruct H0.
    right; done. left; left. move /eqP : H0 => H0; done.
  * intros. apply (H _ _ _ Hsolve). destruct H0. destruct H0. subst.
    - rewrite /solve_simple_cycle' in Hnvs. case Hfinda : (PVM.find v initial) => [val|]; rewrite Hfinda in Hnvs; try discriminate.
      case Hval : (simplify_constraints v n (Z.of_nat val)
        (find_constraint1s v
          [seq tempc <- cs1 | Datatypes.length (rhs_terms1 tempc) == 1])
        [seq tempc <- cs1 | Datatypes.length (rhs_terms1 tempc) == 1] initial) => [new_value|]; rewrite Hval in Hnvs; try discriminate.
      inversion Hnvs. right. rewrite /add_valuation. apply mem_add_or. right; done.
    - left; done. rewrite /solve_simple_cycle' in Hnvs. case Hfinda : (PVM.find a initial) => [val|]; rewrite Hfinda in Hnvs; try discriminate.
      case Hval : (simplify_constraints a n (Z.of_nat val)
        (find_constraint1s a
          [seq tempc <- cs1 | Datatypes.length (rhs_terms1 tempc) == 1])
        [seq tempc <- cs1 | Datatypes.length (rhs_terms1 tempc) == 1] initial) => [new_value|]; rewrite Hval in Hnvs; try discriminate.
      inversion Hnvs. right. apply mem_add_or; left; done.
Qed.*)

Lemma initialize_mem_or c1map: forall a initial, (forall var, List.In var a -> exists cs, PVM.find var c1map = Some cs) -> forall v, (PVM.mem v (initialize_tbsolved a initial c1map) <-> List.In v a \/ PVM.mem v initial).
Proof.
  elim. simpl; intros. split; intros. right; done. destruct H0; try done.
  simpl; intros. destruct (H0 a) as [cs Hfind]. left; done. rewrite Hfind. split.
  * intros. apply H in H1. destruct H1. left; right; done. apply mem_add_or in H1. destruct H1. right; done. left; left. move /eqP : H1 => H1; rewrite H1 //.
    intros; apply H0; right; done.
  * intros. apply H. intros; apply H0; right; done. destruct H1. destruct H1. right. apply mem_add_or. right; rewrite H1 //. left; done.
    right. apply mem_add_or; left; done.
Qed.

Lemma merge_tbsolved_eq nv : forall a new_values initial, NoDup a -> merge_solution a initial nv = Some new_values ->
  forall var, List.In var a ->
  exists val : nat, PVM.find (elt:=nat) var nv = Some val /\ PVM.find (elt:=nat) var new_values = Some val.
Proof.
  elim. simpl; intros; done.
  simpl; intros. case Hfind : (PVM.find a nv) => [val|]; rewrite Hfind in H1; try discriminate.
  apply NoDup_cons_iff in H0. move : H0 => [Hnotin Hnodup]. destruct H2.
  - subst; exists val; split; try done. apply (find_merge_notin_eq _ _ _ _ _ Hnotin) in H1. 
    rewrite -H1 find_add_eq //.
  - move : H0. apply (H _ _ Hnodup H1).
Qed.

Definition tarjan_correctness (solved : list ProdVar.t) (scc_list : list (list ProdVar.t)) (c1map : PVM.t (list Constraint1)) : Prop :=
  (forall (scc : list ProdVar.t), List.In scc scc_list -> scc <> []) /\
  (NoDup (solved ++ (concat scc_list))) /\
  (forall (var : ProdVar.t), List.In var (constraints1_vars (extract_cs solved c1map)) -> List.In var solved) /\
  (forall (l1 l2 : list (list ProdVar.t)) (scc : list ProdVar.t), l1 ++ scc :: l2 = scc_list ->
    (forall (var : ProdVar.t), List.In var (constraints1_vars (extract_cs (solved ++ (concat l1) ++ scc) c1map)) -> List.In var (solved ++ (concat l1) ++ scc))).

Definition extract_correctness (c1map : PVM.t (list Constraint1)) (scc_list : list (list ProdVar.t)) : Prop :=
  (forall (var : ProdVar.t), List.In var (concat scc_list) -> exists (cs : list Constraint1), PVM.find var c1map = Some cs /\ forallb (fun c => lhs_var1 c == var) cs /\ cs <> []) (*/\
  (forall var, List.In var (concat scc_list) <-> List.In var (List.split (PVM.elements c1map)).1*).

Definition circuit_limitation (c1map : PVM.t (list Constraint1)) (scc_list : list (list ProdVar.t)) : Prop :=
  forall (scc : list ProdVar.t), List.In scc scc_list -> let cs := extract_cs scc c1map in 
  if (List.length scc == 1) then 
    forall c, List.In c cs -> in_bool (List.hd (N0,N0) scc) (rhs_vars c) -> rhs_power c = []
  else 
    forall c, List.In c cs -> rhs_power c = [].

Definition initial_correctness (initial : Valuation) (solved : list ProdVar.t) : Prop :=
  forall var, PVM.mem var initial <-> List.In var solved.


Lemma solve_alg_correctness : forall scclist c1map cs2, 
    tarjan_correctness nil scclist c1map 
  -> extract_correctness c1map scclist 
  -> circuit_limitation c1map scclist
  -> match solve_alg_check scclist c1map cs2 with
    | Some solution => forallb (satisfies_constraint1 solution) 
                                  (extract_cs (concat scclist) c1map) 
                    /\ forallb (fun c => Z.leb (min_rhs_value solution c) 1%Z) cs2
    | None => true
    end.
Proof.
  intros; rewrite /solve_alg_check.
  case Hsolve : (solve_alg scclist [] initial_valuation c1map) => [value|]; try done.
  destruct (forallb (fun c => Z.leb (min_rhs_value value c) 1%Z) cs2) eqn : Hcs2; try done.
  split; try done; clear Hcs2.
  move : scclist H H0 H1 value Hsolve.
  assert (Hhelper : forall (scclist : list (list ProdVar.t)) (solved : list ProdVar.t) initial,
    tarjan_correctness solved scclist c1map ->
    (forall (var : ProdVar.t), List.In var (concat scclist) -> exists (cs : list Constraint1), PVM.find var c1map = Some cs /\ forallb (fun c => lhs_var1 c == var) cs) ->
    circuit_limitation c1map scclist ->
    initial_correctness initial solved -> 
    forallb (satisfies_constraint1 initial) (extract_cs solved c1map) ->
    forall value : Valuation,
    solve_alg scclist solved initial c1map = Some value ->
    forallb (satisfies_constraint1 value)
      (extract_cs (solved ++ (concat scclist)) c1map)).
  elim.
  - simpl; intros solved initial Htarjan Hextract Hlimit Hinitial Hsat value Hsolve.
    assert (solved ++ [] = solved) by (apply cats0).
    rewrite H; clear H.
    inversion Hsolve. rewrite -H0 //.
  - intros a l IH solved initial Htarjan Hextract Hlimit Hinitial Hsat value Hsolve.
    simpl in Hsolve.
    case Hhd : a => [|hda tla].
    - rewrite /tarjan_correctness in Htarjan.
      specialize (Htarjan.1 a) as H'. rewrite Hhd in H'. intuition. (* tarjan, scclist 中的分量不是空 *)
    case Htla : tla => [|x y]; rewrite -Htla.
    - (* acyclic, infer single variable *)
      rewrite Htla in Hhd; rewrite Htla; clear Htla tla.
      rewrite Hhd in Hsolve Htarjan Hextract Hlimit; clear Hhd a.
      assert ((solved ++ [hda]) ++ concat l = solved ++ concat ([hda] :: l)) by (rewrite concat_cons; rewrite -> catA; done).
      rewrite -H; clear H.
      case Hfind : (PVM.find hda c1map) => [constraints|]; rewrite Hfind in Hsolve; try discriminate.
      destruct (List.partition (fun c : Constraint1 => in_bool hda (rhs_vars c)) constraints) as [cs_have_v cs] eqn : Hpart.
      case Hcst : (forallb (fun c : Constraint1 => (rhs_const1 c <=? 0)%Z && (rhs_terms1 c == [(1, hda)])) (List.map (remove_solved_c initial) cs_have_v)); rewrite Hcst in Hsolve; try discriminate.
      apply IH with (initial := PVM.add hda (Z.to_nat (initialize_tbsolved' initial cs)) initial); try done.
      (* tarjan start *)
      unfold tarjan_correctness in *.
      move : Htarjan => [Hnotempty [Hnodup Hsolved]]. split. intros; apply Hnotempty; intuition.
      split; rewrite concat_cons in Hnodup. rewrite -catA. simpl; simpl in Hnodup; done. move : Hsolved => [_ Hsolved].
      split. intros. specialize (Hsolved nil l [hda]). simpl; intros. move : H; apply Hsolved; done.
      move : Hsolved; clear; intros. specialize (Hsolved ([hda] :: l1) l2 scc).
      simpl in Hsolved. rewrite -catA; simpl. apply Hsolved; try intuition.
      rewrite -H //. rewrite -catA in H0; simpl in H0; done.
      (* tarjan end *)
      (* extract start *)
      intros; apply Hextract. simpl; right ;done.
      (* extract end *)
      (* limitation start *)
      move : Hlimit; clear; intros.
      unfold circuit_limitation in *.
      intros. apply (List.in_cons [hda]) in H. apply Hlimit in H; clear Hlimit. done.
      (* limitation end *)
      (* initial start *)
      move : Hinitial; clear; intros.
      unfold initial_correctness in *. split; intros. apply mem_add_or in H.
      destruct H. apply Hinitial in H. apply in_or_app; left; done. apply in_or_app; right. move /eqP : H => H; subst. apply in_eq.
      apply mem_add_or. apply in_app_or in H. destruct H. left; apply Hinitial; done. right. apply /eqP. apply (repeat_spec 1). intuition.
      (* initial end *)
      clear IH Hsolve value.
      apply forallb_forall.
      assert (extract_cs (solved ++ [hda]) c1map = extract_cs solved c1map ++ constraints).
        move : Hfind. clear.
        induction solved as [|h t IH].
        - (* Base case: solved = [] *)
          simpl; intros.
          rewrite Hfind cats0 //.
        - (* Inductive step: solved = h :: t *)
          simpl; intros.
          destruct (PVM.find h c1map) eqn:Hfind_h.
          + (* Case: Some l *)
            rewrite IH.
            rewrite catA //.
            done.
          + (* Case: None *)
            rewrite IH.
            reflexivity.
            done.
      rewrite H; clear H. 
      intros.
      apply in_app_or in H.
      assert (forall x, List.In x (extract_cs solved c1map) ->
        satisfies_constraint1 initial x = true) by (apply forallb_forall; rewrite Hsat //).
      clear Hsat.
      destruct H.
      - (* solved constraints *)
        generalize H; apply H0 in H; clear H0; intros.
        move : H; apply satisfies1_on_constrainedvars; intros.
        rewrite find_add_neq //.
        (* tarjan start *)
        unfold tarjan_correctness in *.
        move : Htarjan => [Hnotempty [Hnodup [Hsolved Htbsolved]]]. 
        specialize (Hsolved var); simpl in Hsolved.
        specialize (constraint1_vars2constraints1_vars _ H0 H); intro. apply Hsolved in H1.
        rewrite concat_cons in Hnodup; simpl in Hnodup. apply NoDup_remove_2 in Hnodup.
        intro Heq; subst. 
        assert (~ List.In hda solved /\ ~ List.In hda (concat l)).
          apply Decidable.not_or.
          intro Hypo. 
          apply in_app_iff with (a := hda) (l := solved) (l' := concat l) in Hypo. done.
        move : H2 => [H2 _]. done.
        (* tarjan end *)
      - (* new constraints *)
        apply (elements_in_partition _ _ Hpart) in H. 
        destruct H. 
        * rewrite /circuit_limitation in Hlimit.
          specialize (Hlimit [hda] (in_eq [hda] l)). simpl in Hlimit. rewrite Hfind cats0 in Hlimit.
          rewrite /satisfies_constraint1.
          assert (Hinconcat : List.In hda (concat ([hda] :: l))) by (rewrite concat_cons;simpl;left; done). apply Hextract in Hinconcat. rewrite Hfind in Hinconcat; clear Hfind.
          destruct Hinconcat as [cs' [Heq Hfind]]. inversion Heq; rewrite -H2 in Hfind; clear Heq H2 cs'.
          assert (forall c, List.In c constraints -> lhs_var1 c == hda) by (apply forallb_forall; done). clear Hfind.
          specialize (elements_in_partition _ _ Hpart x) as Hin.
          assert (List.In  x constraints) by (apply Hin; left; done). clear Hin.
          apply H1 in H2; clear H1. move /eqP : H2 => H2; subst.
          rewrite find_add_eq.
          remember ((Z.to_nat (initialize_tbsolved' initial cs))) as new_val.
          rewrite (remove_solved_c_correctness initial).
          assert (forall c, List.In c (List.map (remove_solved_c initial) cs_have_v) -> (rhs_const1 c <=? 0)%Z && (rhs_terms1 c == [(1, lhs_var1 x)])) by (apply forallb_forall; done). clear Hcst.
          specialize (H1 (remove_solved_c initial x)).
          generalize H; apply (in_map (remove_solved_c initial)) in H. apply H1 in H; clear H1. intro H1.
          move /andP : H => [Hcst Hterm]. move /eqP : Hterm => Hterm.
          rewrite /rhs_value1 Hterm. simpl. rewrite find_add_eq mul1n.
          assert ((rhs_power (remove_solved_c initial x)) = []).
            specialize (elements_in_partition _ _ Hpart x) as Hin.
            assert (List.In  x constraints) by (apply Hin; left; done). clear Hin.
            apply Hlimit in H; clear Hlimit.
            rewrite /remove_solved_c H. destruct (remove_solved initial (rhs_terms1 x)). simpl; done.
          rewrite partition_as_filter in Hpart. inversion Hpart; clear Hpart H H4.
          rewrite -H3 in H1; clear H3. apply filter_In in H1. exact H1.2.

          rewrite H; simpl. rewrite Z.add_0_r.
          specialize (Zle_bool_plus_mono _ _ _ _ Hcst (Z.leb_refl (Z.of_nat new_val))) as Hhelp. rewrite Z.add_0_l in Hhelp. done.
          move : Hinitial Htarjan; clear.
          intros; rewrite find_add_neq //.
          rewrite /initial_correctness in Hinitial; rewrite /tarjan_correctness in Htarjan. move : Htarjan => [_ [Hnodup _]].
          apply Hinitial in H. intro Heq; subst. rewrite concat_cons in Hnodup; simpl in Hnodup. apply NoDup_remove_2 in Hnodup.
          assert (~ List.In (lhs_var1 x) solved /\ ~ List.In (lhs_var1 x) (concat l)).
            apply Decidable.not_or.
            intro Hypo. 
            apply in_app_iff with (a := (lhs_var1 x)) (l := solved) (l' := concat l) in Hypo. done.
          move : H0 => [H0 _]. done.

        * apply satisfies1_initialize; try done.
          (* extract start *)
          assert (Hinconcat : List.In hda (concat ([hda] :: l))) by (rewrite concat_cons;simpl;left; done). apply Hextract in Hinconcat. rewrite Hfind in Hinconcat; clear Hfind.
          destruct Hinconcat as [cs' [Heq Hfind]]. inversion Heq; rewrite -H2 in Hfind; clear Heq H2 cs'.
          assert (forall c, List.In c constraints -> lhs_var1 c == hda) by (apply forallb_forall; done). clear Hfind.
          apply H1. 
          apply (elements_in_partition _ _ Hpart). right; done.
          (* extract end *)
          (* tarjan start *)
          rewrite partition_as_filter in Hpart. inversion Hpart; clear Hpart H2.
          rewrite -H3 in H; clear H3. apply filter_In in H. move : H => [Hin Hnot].
          assert (Hinconcat : List.In hda (concat ([hda] :: l))) by (rewrite concat_cons;simpl;left; done). apply Hextract in Hinconcat. rewrite Hfind in Hinconcat; clear Hfind.
          destruct Hinconcat as [cs' [Heq Hfind]]. inversion Heq; rewrite -H1 in Hfind; clear Heq H1 cs'.
          assert (forall c, List.In c constraints -> lhs_var1 c == hda) by (apply forallb_forall; done). clear Hfind.
          apply H in Hin; clear H. move /eqP : Hin => Hin; subst.
          intro Hin. apply In_in_bool in Hin. rewrite Hin in Hnot. done.
          (* tarjan end *)
    - (* scc *)
      generalize Hlimit; rewrite /circuit_limitation in Hlimit; intro Hlimit'. specialize (Hlimit a). assert ((Datatypes.length a == 1) = false).
        rewrite Hhd Htla. simpl. intuition. rewrite H in Hlimit; clear H.
      rewrite Hhd Htla in Hsolve. rewrite -Htla -Hhd in Hsolve. rewrite -Hhd. clear Htla x y Hhd hda tla.
      assert ((solved ++ a) ++ concat l = solved ++ concat (a :: l)) by (rewrite concat_cons; rewrite -> catA; done).
      rewrite -H; clear H.
      case Hsc_or_scc : (is_simple_cycle a (extract_cs a c1map)); rewrite Hsc_or_scc in Hsolve. 
      * (* simple cycle *)
        case Hsc : (solve_simple_cycle a
          (remove_solveds initial (extract_cs a c1map))) => [nv|]; rewrite Hsc in Hsolve; try discriminate.
        case Hmerged : (merge_solution a initial nv) => [new_values|]; rewrite Hmerged in Hsolve; try discriminate.
        apply IH with (initial := new_values); try done.
        (* tarjan start *)
        unfold tarjan_correctness in *.
        move : Htarjan => [Hnotempty [Hnodup Hsolved]]. split. intros; apply Hnotempty; intuition.
        split; rewrite concat_cons in Hnodup. rewrite -catA. simpl; simpl in Hnodup; done. move : Hsolved => [_ Hsolved].
        split. intros. specialize (Hsolved nil l a). simpl; intros. move : H; apply Hsolved; done.
        move : Hsolved; clear; intros. specialize (Hsolved (a :: l1) l2 scc).
        simpl in Hsolved. 
        assert ((solved ++ a) ++ concat l1 ++ scc = solved ++ (a ++ concat l1)%list ++ scc). 
          rewrite (catA (solved ++ a) (concat l1)). rewrite (catA solved (a ++ concat l1)%list).
          apply app_inv_tail_iff. intuition. 
        rewrite -H1 in Hsolved. apply Hsolved. rewrite H //. done.
        (* tarjan end *)
        (* extract start *)
        intros; apply Hextract. simpl. apply in_or_app; right; done.
        (* extract end *)
        (* limitation start *)
        move : Hlimit'; clear; intros.
        unfold circuit_limitation in *.
        intros. apply (List.in_cons a) in H; apply Hlimit' in H; clear Hlimit'. done.
        (* limitation end *)
        (* initial start *)
        assert (Hextract' : forall var0, List.In var0 a -> exists cs, PVM.find var0 c1map = Some cs).
          move : Hextract; clear; intros. destruct (Hextract var0) as [cs [Hfind _]]. simpl. apply in_or_app;left; done.
          exists cs; done.
        move : Hinitial Hmerged Hextract'; clear.
        unfold initial_correctness in *. 
        split; intros. 
        - apply (merge_solution_mem_or _ _ _ _ Hmerged) in H. apply in_or_app. destruct H. right; done.
          left; apply Hinitial; done.
        - apply in_app_or in H. destruct H. apply Hinitial in H. apply (merge_solution_mem_or _ _ _ _ Hmerged). right; done.
          apply (merge_solution_mem_or _ _ _ _ Hmerged); left; done.
        (* initial end *)
        clear IH Hsolve value.
        admit. (* to be filled *)
      * (* normal scc *)
        case Hubs : (solve_ubs a a (List.filter
          (fun c : Constraint1 => Datatypes.length (rhs_terms1 c) != 0)
          (remove_solveds initial (extract_cs a c1map)))) => [ubs|]; rewrite Hubs in Hsolve; try discriminate.
        remember (mergeValuations (initialize_tbsolved a initial c1map) ubs) as bs eqn : Hbs. 
        remember (remove_solveds initial (extract_cs a c1map)) as cs1' eqn : Hcs1.
        case Hbab : (bab_bin a bs cs1' nil) => [nv|]; rewrite Hbab in Hsolve; try discriminate. assert (Hbabmem : forall var, List.In var a <-> PVM.mem var nv) by admit.
        case Hmerged : (merge_solution a (initialize_tbsolved a initial c1map) nv) => [new_values|]; rewrite Hmerged in Hsolve; try discriminate.
        apply IH with (initial := new_values); try done.

        (* tarjan start *)
        unfold tarjan_correctness in *.
        move : Htarjan => [Hnotempty [Hnodup Hsolved]]. split. intros; apply Hnotempty; intuition.
        split; rewrite concat_cons in Hnodup. rewrite -catA. simpl; simpl in Hnodup; done. move : Hsolved => [_ Hsolved].
        split. intros. specialize (Hsolved nil l a). simpl; intros. move : H; apply Hsolved; done.
        move : Hsolved; clear; intros. specialize (Hsolved (a :: l1) l2 scc).
        simpl in Hsolved. 
        assert ((solved ++ a) ++ concat l1 ++ scc = solved ++ (a ++ concat l1)%list ++ scc). 
          rewrite (catA (solved ++ a) (concat l1)). rewrite (catA solved (a ++ concat l1)%list).
          apply app_inv_tail_iff. intuition. 
        rewrite -H1 in Hsolved. apply Hsolved. rewrite H //. done.
        (* tarjan end *)
        (* extract start *)
        intros; apply Hextract. simpl. apply in_or_app; right; done.
        (* extract end *)
        (* limitation start *)
        move : Hlimit'; clear; intros.
        unfold circuit_limitation in *.
        intros. apply (List.in_cons a) in H; apply Hlimit' in H; clear Hlimit'. done.
        (* limitation end *)
        (* initial start *)
        assert (Hextract' : forall var0, List.In var0 a -> exists cs, PVM.find var0 c1map = Some cs).
          move : Hextract; clear; intros. destruct (Hextract var0) as [cs [Hfind _]]. simpl. apply in_or_app;left; done.
          exists cs; done.
        move : Hinitial Hmerged Hextract'; clear.
        unfold initial_correctness in *. 
        split; intros. 
        - apply (merge_solution_mem_or _ _ _ _ Hmerged) in H. apply in_or_app. destruct H. right; done.
          apply initialize_mem_or in H; try done. destruct H. right; done. left; apply Hinitial; done.
        - apply in_app_or in H. destruct H. apply Hinitial in H. apply (merge_solution_mem_or _ _ _ _ Hmerged). right. apply (initialize_mem_or _ _ _ Hextract'); right; done.
          apply (merge_solution_mem_or _ _ _ _ Hmerged); left; done.
        (* initial end *)
        clear IH Hsolve value.
        specialize (bab_bin_correct1 a bs cs1' nil); intro Hbab_correctness. rewrite Hbab in Hbab_correctness.
        destruct Hbab_correctness; try done. destruct H as [s [Heq [Hsat1 _]]]. inversion Heq; rewrite -H0 in Hsat1. clear Heq H0 s.
        rewrite (extract_cs_app). apply forallb_forall. intros. apply in_app_or in H. destruct H. 
        * (* solved constraints *)
          assert (forall x, List.In x (extract_cs solved c1map) ->
            satisfies_constraint1 initial x = true) by (apply forallb_forall; rewrite Hsat //).
          clear Hsat.
          generalize H; apply H0 in H; clear H0; intros.
          move : H; apply satisfies1_on_constrainedvars; intros.
          assert (Hin_solved : List.In var solved).
            rewrite /tarjan_correctness in Htarjan. destruct Htarjan as [_ [Hnodup [Hsolved _]]].
            apply Hsolved; try done. move : H0 H; apply constraint1_vars2constraints1_vars.
          assert (Hnotin : ~List.In var a). rewrite /tarjan_correctness in Htarjan. destruct Htarjan as [_ [Hnodup [_ _]]].
            move : Hnodup Hin_solved; clear; intros. rewrite concat_cons in Hnodup. 
            apply in_split in Hin_solved. destruct Hin_solved as [l1 [l2 Hsolved]]. rewrite Hsolved in Hnodup.
            assert ((l1 ++ (var :: l2)%SEQ)%list ++ (a ++ concat l)%list = l1 ++ var :: (l2 ++ a ++ concat l)).
              rewrite -catA. simpl. intuition.
            rewrite H in Hnodup; clear H. apply NoDup_remove_2 in Hnodup. intro Hin.
            assert (List.In var (l1 ++ (l2 ++ a ++ concat l)%SEQ)%list). apply in_or_app; right. apply in_or_app; right. apply in_or_app; left;done.
            done.
          rewrite -(find_merge_notin_eq _ _ _ _ _ Hnotin Hmerged). apply (find_init_notin_eq _ _ _ _ Hnotin).
          move : Hextract; clear; intros. destruct (Hextract var) as [cs [Hfind _]]. simpl. apply in_or_app;left; done.
          exists cs; done.
        * (* new constraints *)
          assert (Hnodupa : NoDup a). rewrite /tarjan_correctness in Htarjan. move : Htarjan => [_ [Hnodup _]].
            simpl in Hnodup. apply NoDup_app_remove_l in Hnodup. apply NoDup_app_remove_r in Hnodup; done. 
          rewrite Hcs1 in Hsat1. apply forallb2satisfies_all_constraint1 in Hsat1. 
          apply remove_solveds_sat with (nv := new_values) (tbsolved := a) in Hsat1. 
          move : x H; apply forallb_forall; done.
          (* extract &limitation *)
          intros; split. move : H0; apply extract_cs_lhs_in. intros; apply Hextract. simpl; apply in_or_app; left; done.
          rewrite /circuit_limitation in Hlimit.
          apply Hlimit; try done. simpl; left; done.
          (* merge *)
          move : Hmerged; apply merge_tbsolved_eq; try done. 
          assert (forall var, PVM.mem var initial -> ~List.In var a).
            intros. rewrite /initial_correctness in Hinitial. apply Hinitial in H0. rewrite /tarjan_correctness in Htarjan.
            move : Htarjan => [_ [Hnodup _]]. rewrite concat_cons in Hnodup. 
            apply in_split in H0. destruct H0 as [l1 [l2 Hsolved]]. rewrite Hsolved in Hnodup.
            assert ((l1 ++ (var :: l2)%SEQ)%list ++ (a ++ concat l)%list = l1 ++ var :: (l2 ++ a ++ concat l)).
              rewrite -catA. simpl. intuition.
            rewrite H0 in Hnodup; clear H0. apply NoDup_remove_2 in Hnodup. intro Hin.
            assert (List.In var (l1 ++ (l2 ++ a ++ concat l)%SEQ)%list). apply in_or_app; right. apply in_or_app; right. apply in_or_app; left;done.
            done.
          assert (forall var, List.In var a -> exists cs, PVM.find var c1map = Some cs). move : Hextract; clear; intros.
            destruct (Hextract var) as [cs [Hfind _]]. simpl. apply in_or_app; left; done. exists cs; done. 
          move : Hnodupa Hbabmem H1 H0 Hmerged; clear; intros.
          destruct (PVM.find (elt:=nat) var initial) as [val|] eqn : Hfind.
          * left; exists val; split; try done. apply (find_merge_notin_eq _ _ var) in Hmerged; try done. rewrite -(find_init_notin_eq c1map a) in Hmerged; try done.
            rewrite -Hmerged Hfind //. 1,2 : apply H0. 1,2 : apply find_mem; exists val; done. 
          * right; split; try done. specialize (in_dec eq_dec var a); intro. destruct H. 
            - specialize (merge_tbsolved_eq _ _ _ _ Hnodupa Hmerged _ i); intros. destruct H as [val [Hfind'' Hfind']]; rewrite Hfind' Hfind'' //.
            - destruct (PVM.find var nv) as [val|] eqn : Hfind'. assert (exists val, PVM.find var nv = Some val) by (exists val; done). apply find_mem in H. apply Hbabmem in H. done.
              apply (none_find_merge_none _ _ _ _ _ Hmerged n) in Hfind'. rewrite Hfind' //.
              apply (none_find_init_none _ _ _ _ n Hfind).

  intros. rewrite /extract_correctness in H0. (*move : H0 => [H0 H2].*)
  apply (Hhelper _ _ initial_valuation) with (value := value) in H; try done. 
  intros. apply H0 in H2. destruct H2 as [cs [H2 [H3 _]]]. exists cs; try done.
Admitted.

Lemma max_list_small n values : forall (cs : list Constraint1) init, (Z.leb init n /\ (forall (c : Constraint1), List.In c cs -> Z.leb (rhs_value1 values c) n)) -> Z.leb (max_list cs values init) n.
Proof.
  elim.
  - (* 基础情况: cs = nil *)
    simpl. intros init [Hn Hforall]; apply Hn.
  - (* 归纳情况: cs = c :: cs' *)
    simpl. intros hd tl H init [Hn Hforall]. apply H. split.
    + (* 证明新的init <= n *)
      apply Zle_imp_le_bool.
      apply Z.max_lub; try done.
      apply (Zle_bool_imp_le _ _ Hn).
      apply Zle_bool_imp_le.
      apply Hforall.
      left; done.
    + (* 证明对于所有c' \in cs', n >= ... *)
      intros c' Hc'. apply Hforall.
      right; done.
Qed.

Lemma remove_solveds_terms_value_smaller temp_s initial: forall terms cst new_terms new_cst, smaller_valuation initial temp_s -> remove_solved initial terms = (new_terms, new_cst) ->
  (terms_value temp_s new_terms (cst + new_cst) <=? terms_value temp_s terms cst)%Z.
Proof.
  intros; apply Zle_imp_le_bool; move : terms cst new_terms new_cst H H0.
  elim. simpl; intros. inversion H0; simpl. lia. 
  simpl; intros [coe var]; intros; simpl. destruct (remove_solved initial l) as [terms' cst'] eqn : Htl.
  case Hinit : (PVM.find (elt:=nat) var initial) => [val|]; rewrite Hinit in H1.
  - inversion H1; clear H1 H4 new_cst. rewrite -H3; clear H3 new_terms. rewrite /smaller_valuation in H0. destruct (H0 var) as [value0 [value1 [Hfind0 [Hfind1 Hle]]]].
    apply find_mem; exists val; done. rewrite Hfind0 in Hinit; inversion Hinit. rewrite -H2; clear Hinit H2 val. rewrite Hfind1. rewrite Z.add_assoc.
    rewrite terms_value_cst_add. rewrite (terms_value_cst_add _ _ cst (Z.of_nat (coe * value1))). apply Z.add_le_mono.
    apply H; try done. apply inj_le. apply (elimT leP). apply leq_mul; try done.
  - inversion H1. clear H1 H3 new_terms. rewrite -H4; clear H4 new_cst. simpl. rewrite terms_value_cst_add. 
    rewrite (terms_value_cst_add _ _ cst (Z.of_nat (coe * match PVM.find (elt:=nat) var temp_s with
      | Some val => val
      | None => 0
      end))). apply Zplus_le_compat_r. apply H; try done.
Qed.

Lemma remove_solveds_smaller_sat temp_s initial : forall cs, forallb (satisfies_constraint1 temp_s) cs ->
  (forall c, List.In c cs -> rhs_power c = nil) ->
  smaller_valuation initial temp_s -> 
  (*forall var, List.In var tbsolved -> (exists val, PVM.find var values = Some val /\ PVM.find var nv = Some val)) ->
  (forall (var : ProdVar.t), (exists val, PVM.find var initial = Some val /\ PVM.find var nv = Some val) \/ (PVM.find var initial = None /\ PVM.find var values = PVM.find var nv)) ->*)
  forallb (satisfies_constraint1 temp_s) (remove_solveds initial cs).
Proof.
  elim. simpl; done.
  simpl; intros. move /andP : H0 => [Hsat Hsats]. apply H in Hsats; try done. apply rwP with (P := satisfies_constraint1 temp_s (remove_solved_c initial a) /\
    forallb (satisfies_constraint1 temp_s) (remove_solveds initial l)). apply andP. split; try done. clear H Hsats.
  unfold satisfies_constraint1 in *. rewrite /remove_solved_c. destruct (remove_solved initial (rhs_terms1 a)) as [new_terms new_cst] eqn : Hremove. simpl.
  case Hlhs : (PVM.find (elt:=nat) (lhs_var1 a) temp_s) => [val|]; rewrite Hlhs in Hsat; try done.
  unfold rhs_value1 in *; simpl. rewrite H1; rewrite H1 in Hsat; simpl. simpl in Hsat. rewrite Z.add_0_r. rewrite Z.add_0_r in Hsat.
  assert (terms_value temp_s new_terms (rhs_const1 a + new_cst) <=? terms_value temp_s (rhs_terms1 a) (rhs_const1 a))%Z by (apply remove_solveds_terms_value_smaller with (initial := initial); done).
  move : H Hsat. apply Zle_bool_trans. 1,2,3 : left; done. intros; apply H1; right; done.
Qed.

Lemma sat_solution_in_bs values cs a c1map: forall ubs bs initial, forallb (satisfies_constraint1 values) cs -> solve_ubs a a cs = Some ubs ->
  bs = mergeValuations (initialize_tbsolved a initial c1map) ubs -> In values bs.
Proof.
(*TBD*)
Admitted.

Lemma solve_alg_smallest : forall scclist c1map cs2, 
    tarjan_correctness nil scclist c1map 
  -> extract_correctness c1map scclist
  -> circuit_limitation c1map scclist
  -> match solve_alg_check scclist c1map cs2 with
    | Some solution => forall temp_s, 
        forallb (satisfies_constraint1 temp_s) (extract_cs (concat scclist) c1map) /\
        forallb (fun c => Z.leb (min_rhs_value temp_s c) 1%Z) cs2 -> smaller_valuation solution temp_s
    | None => true
    end.
Proof.
  intros; rewrite /solve_alg_check.
  case Hsolve : (solve_alg scclist [] initial_valuation c1map) => [value|]; try done.
  destruct (forallb (fun c => Z.leb (min_rhs_value value c) 1%Z) cs2) eqn : Hcs2; try done.
  move : scclist H H0 H1 value Hsolve Hcs2.
  assert (Hhelper : forall (scclist : list (list ProdVar.t)) (solved : list ProdVar.t) initial,
    tarjan_correctness solved scclist c1map ->
    extract_correctness c1map scclist ->
    circuit_limitation c1map scclist ->
    initial_correctness initial solved ->
    forall value : Valuation,
    solve_alg scclist solved initial c1map = Some value ->
    forallb (fun c => Z.leb (min_rhs_value value c) 1%Z) cs2 = true ->
    forall temp_s : Valuation,
    forallb (satisfies_constraint1 temp_s)
      (extract_cs (solved ++ (concat scclist)) c1map) /\
    forallb (fun c => Z.leb (min_rhs_value temp_s c) 1%Z) cs2 -> smaller_valuation initial temp_s ->
    smaller_valuation value temp_s).
  elim.
  - simpl; intros solved initial Htarjan Hextract Hlimit Hinitial value Hsolve Hcs2 temp_s Htemp Hinit.
    inversion Hsolve.
    rewrite -H0 //.
  - intros a l IH solved initial Htarjan Hextract Hlimit Hinitial value Hsolve Hcs2 temp_s Htemp Hinit.
    simpl in Hsolve.
    case Hhd : a => [|hda tla]; rewrite Hhd in Hsolve.
    - rewrite /tarjan_correctness in Htarjan.
      specialize (Htarjan.1 a) as H'. rewrite Hhd in H'. intuition. (* tarjan, scclist 中的分量不是空 *)
    case Htla : tla => [|x y]; rewrite Htla in Hsolve.
    - (* acyclic, infer single variable *)
      rewrite Htla in Hhd; clear Htla tla.
      rewrite Hhd in Htarjan Hextract Hlimit Htemp Hinitial; clear Hhd a.
      case Hfind : (PVM.find hda c1map) => [constraints|]; rewrite Hfind in Hsolve; try discriminate.
      destruct (List.partition (fun c : Constraint1 => in_bool hda (rhs_vars c)) constraints) as [cs_have_v cs] eqn : Hpart.
      case Hcst : (forallb (fun c : Constraint1 => (rhs_const1 c <=? 0)%Z && (rhs_terms1 c == [(1, hda)])) (List.map (remove_solved_c initial) cs_have_v)); rewrite Hcst in Hsolve; try discriminate.
      apply IH with (initial := PVM.add hda (Z.to_nat (initialize_tbsolved' initial cs)) initial) (solved := solved ++ [hda]); try done.
      (* tarjan start *)
      unfold tarjan_correctness in *.
      move : Htarjan => [Hnotempty [Hnodup Hsolved]]. split. intros; apply Hnotempty; intuition.
      split; rewrite concat_cons in Hnodup. rewrite -catA. simpl; simpl in Hnodup; done. move : Hsolved => [_ Hsolved].
      split. intros. specialize (Hsolved nil l [hda]). simpl; intros. move : H; apply Hsolved; done.
      move : Hsolved; clear; intros. specialize (Hsolved ([hda] :: l1) l2 scc).
      simpl in Hsolved. rewrite -catA; simpl. apply Hsolved; try intuition.
      rewrite -H //. rewrite -catA in H0; simpl in H0; done.
      (* tarjan end *)
      (* extract *)
      move : Hextract; clear; intros. unfold extract_correctness in *. intros; apply Hextract. simpl; right ;done.
      (* limitation start *)
      move : Hlimit; clear; intros.
      unfold circuit_limitation in *.
      intros. apply (List.in_cons [hda]) in H. apply Hlimit in H; clear Hlimit. done.
      (* limitation end *)
      (* initial start *)
      move : Hinitial; clear; intros.
      unfold initial_correctness in *. split; intros. apply mem_add_or in H.
      destruct H. apply Hinitial in H. apply in_or_app; left; done. apply in_or_app; right. move /eqP : H => H; subst. apply in_eq.
      apply mem_add_or. apply in_app_or in H. destruct H. left; apply Hinitial; done. right. apply /eqP. apply (repeat_spec 1). intuition.
      (* initial end *)
      assert ((solved ++ [hda]) ++ concat l = solved ++ concat ([hda] :: l)) by (rewrite concat_cons; rewrite -> catA; done).
      rewrite H //.
      clear IH Hsolve Hcs2 value.
      generalize Hinit; intros Hsmaller.
      rewrite /smaller_valuation; rewrite /smaller_valuation in Hinit.
      intros var Hin. 
      destruct (var == hda) eqn : Heq. 
      - (* is hda *)
        move /eqP : Heq => Heq.
        subst. rewrite find_add_eq.
        clear Hin Hinit.
        exists (Z.to_nat (initialize_tbsolved' initial cs)).
        move : Htemp => [Htemp1 Htemp2].
        assert (forallb (satisfies_constraint1 temp_s) cs).
          apply forallb_forall.
          intros.
          assert (forall c1map a ls, List.In a ls -> PVM.find a c1map = Some constraints -> forall c,
            List.In c constraints -> List.In c (extract_cs ls c1map)).
          {clear. intros c1map a ls Hin Hfind c Hc.
          induction ls as [| hd tl IH].
          - simpl in Hin. contradiction.
          - simpl in Hin. destruct Hin as [Heq | Htl].
            + (* hd = a *)
              subst.
              simpl. rewrite Hfind.
              apply in_or_app; left; done.
            + (* hd <> a *)
              simpl.
              apply IH in Htl; clear IH.
              case : (PVM.find hd c1map).
              intros.
              apply in_or_app; right; done.
              done. }
          apply H0 with (ls := solved ++ concat ([hda] :: l)) (c := x) in Hfind; try done; clear H0.
          assert (forall x : Constraint1, List.In x (extract_cs (solved ++ concat ([hda] :: l)) c1map) -> satisfies_constraint1 temp_s x = true).
          apply forallb_forall; done.
          clear Htemp1.
          apply H0 in Hfind; clear H0; done.
          apply in_or_app; right.
          apply in_concat; exists [hda].
          split. apply in_eq.
          simpl; left; done. apply (elements_in_partition _ _ Hpart); right; done.
        specialize (satisfies2le _ _ H hda); intros.
        (* init start *)
        assert (H2 : PVM.find hda initial = None).
          rewrite /initial_correctness in Hinitial.
          rewrite /tarjan_correctness in Htarjan. move : Htarjan => [_ [Hnodup _]].
          rewrite concat_cons in Hnodup; simpl in Hnodup. apply NoDup_remove_2 in Hnodup.
          assert (~ List.In hda solved /\ ~ List.In hda (concat l)).
            apply Decidable.not_or.
            intro Hypo. 
            apply in_app_iff with (a := hda) (l := solved) (l' := concat l) in Hypo. done.
          move : H1 => [H1 _]. 
          assert (~ PVM.mem hda initial). intros Hnot. apply Hinitial in Hnot. done.
          apply mem_find_none; done.
        (* initial correctness *)
        destruct (cs == []) eqn : Hcs_empty. move /eqP : Hcs_empty => Hcs_empty; subst.
          (* corner case, no cs *)
          clear H H0 Htemp2. assert (forallb (satisfies_constraint1 temp_s) cs_have_v).
            assert (forall c, List.In c (extract_cs (solved ++ concat ([hda] :: l)) c1map) -> satisfies_constraint1 temp_s c) by (apply forallb_forall; done). clear Htemp1.
            apply forallb_forall; intros. apply H. rewrite extract_cs_app. apply in_or_app; right. rewrite concat_cons. rewrite -> extract_cs_app. apply in_or_app; left.
            simpl; rewrite Hfind cats0. apply (elements_in_partition _ _ Hpart); left; done.
          assert (constraints <> nil). rewrite /extract_correctness in Hextract. destruct (Hextract hda) as [cs [Hfind2 [_ Hnotempty]]]. simpl; left; done. rewrite Hfind in Hfind2; inversion Hfind2; done.
          destruct (destruct_list constraints).
          destruct s as [hd [tl Hcons]]. 2 : done.
          assert (List.In  hd constraints) by (rewrite Hcons;simpl; left; done).
          apply (elements_in_partition _ _ Hpart) in H1; simpl in H1. destruct H1; try done.
          assert (forall c, List.In c cs_have_v -> satisfies_constraint1 temp_s c) by (apply forallb_forall; done). clear H.
          apply H3 in H1; clear H3. rewrite /satisfies_constraint1 in H1. case Hfindt : (PVM.find (lhs_var1 hd) temp_s) => [val|]; rewrite Hfindt in H1; try done.
          exists val; split; try done. rewrite /extract_correctness in Hextract. destruct (Hextract hda) as [cs [Hfind' [Hlhs _]]]. simpl; left; done. rewrite Hfind in Hfind'. inversion Hfind'. rewrite -H3 in Hlhs.
            clear Hfind' H3 cs.
          assert (forall c, List.In c constraints -> lhs_var1 c == hda) by (apply forallb_forall; done). clear Hlhs.
          assert (List.In  hd constraints) by (rewrite Hcons;simpl; left; done). apply H in H3; clear H. move/eqP : H3 => H3; subst. split; try done.
          (* corner case end *)
        move /eqP : Hcs_empty => Hcs_empty.
        apply satisfies1_exists_value with (a := hda) in H.
        destruct H as [value1 H].
        exists value1; split; try done; split; try done.
        rewrite H in H0.
        specialize (smaller_rhs_value Hsmaller); intros.
        rewrite /initialize_tbsolved'.
        (*rewrite H2; *)clear H2.
        assert ((max_list cs initial (Z.of_nat 0) <=? Z.of_nat value1)%Z).
        apply max_list_small.
        split.
        simpl; apply Zle_imp_le_bool; apply Zle_0_nat.
        intros.
        assert (Z.leb (rhs_value1 temp_s c) (Z.of_nat value1)).
          apply H0; split; try done.
          (* extract start *)
          destruct (Hextract hda) as [cs' [Hfind' [Hlhs _]]]. simpl; left; done. rewrite Hfind in Hfind'. inversion Hfind'. rewrite -H4 in Hlhs.
            clear Hfind' H4 cs'.
          assert (forall c, List.In c constraints -> lhs_var1 c == hda) by (apply forallb_forall; done). clear Hlhs.
          apply H3. 
          apply (elements_in_partition _ _ Hpart). right; done.
          (* extract end *)
        assert (forall var : ProdVar.t, List.In var (rhs_vars c) -> PVM.mem (elt:=nat) var initial).
          rewrite /initial_correctness in Hinitial. intros. apply Hinitial.
          rewrite /tarjan_correctness in Htarjan. move : Htarjan => [_ [_ [_ Htbsolved]]].
          specialize (Htbsolved nil l [hda]). simpl in Htbsolved.
          assert (var <> hda). move : Hpart H2 H4; clear ; intros.
            rewrite partition_as_filter in Hpart. inversion Hpart; clear Hpart H0. rewrite -H1 in H2; apply filter_In in H2.
            move : H2 => [H2 Hnotin]. intro Heq; subst. apply In_in_bool in H4. rewrite H4 in Hnotin. done.
          assert (List.In var (constraints1_vars (extract_cs (solved ++ [hda]) c1map))). 
            rewrite extract_cs_app constraints1_vars_app. apply in_or_app; right. simpl; rewrite Hfind cats0.
            assert (List.In c constraints) by (apply (elements_in_partition _ _ Hpart); right; done).
          apply (constraint1_vars2constraints1_vars _ H6). rewrite /constraint1_vars. rewrite /rhs_vars in H4. intuition.
          apply Htbsolved in H6; try done. apply in_app_or in H6. destruct H6; try done. simpl in H6. destruct H6; try intuition.
        move : (H1 c H4) H3.
        apply Zle_bool_trans.
        assert (Hge0 : Z.le 0 (max_list cs initial (Z.of_nat 0))) by (apply max_list_gt0; done). 
        assert (Hge0' : Z.le 0 (Z.of_nat value1)) by (apply Zle_0_nat).
        rewrite <- (Nat2Z.id value1).
        apply Zle_bool_imp_le in H2.
        apply (Z2Nat.inj_le _ _ Hge0 Hge0') in H2.
        move /leP : H2 => H2; done.
        (* extract start *)
        clear H2; destruct (destruct_list cs).
        destruct s as [hd [tl Hcons]].
        assert (List.In  hd cs) by (rewrite Hcons;simpl; left; done).
        exists hd; split; try done. rewrite /extract_correctness in Hextract. destruct (Hextract hda) as [cs' [Hfind' [Hlhs _]]]. simpl; left; done. rewrite Hfind in Hfind'. inversion Hfind'. rewrite -H3 in Hlhs.
          clear Hfind' H3 cs'.
        assert (forall c, List.In c constraints -> lhs_var1 c == hda) by (apply forallb_forall; done). clear Hlhs.
          apply H2. 
          apply (elements_in_partition _ _ Hpart). right; done.
        intuition.
        (* extract end *)
      - (* in initial *)
        rewrite find_add_neq.
        apply mem_add_or in Hin as H.
        clear Hin.
        destruct H.
        apply Hinit in H; clear Hinit; done.
        move /eqP : Heq => Heq; move /eqP : H => H; subst.
        done.
        move /eqP : Heq => Heq; done.

    - (* scc *)
      generalize Hlimit; rewrite /circuit_limitation in Hlimit; intro Hlimit'. specialize (Hlimit a). assert ((Datatypes.length a == 1) = false).
        rewrite Hhd Htla. simpl. intuition. rewrite H in Hlimit; clear H.
      rewrite -Htla -Hhd in Hsolve. clear Htla x y Hhd hda tla.
      assert ((solved ++ a) ++ concat l = solved ++ concat (a :: l)) by (rewrite concat_cons; rewrite -> catA; done).
      rewrite -H in Htemp; clear H.
      case Hsc_or_scc : (is_simple_cycle a (extract_cs a c1map)); rewrite Hsc_or_scc in Hsolve. 
      * (* simple cycle *)
        (*case Hsc : (solve_simple_cycle a (extract_cs a c1map) cs2 solved (initialize_tbsolved a initial c1map)) => [nv|]; rewrite Hsc in Hsolve; try discriminate.
        assert (smaller_valuation nv temp_s).
          clear IH Hsolve. admit. (* TBD *)

        move : Htemp H; apply IH with (initial := nv); try done.
        (* tarjan start *)
        unfold tarjan_correctness in *.
        move : Htarjan => [Hnotempty [Hnodup Hsolved]]. split. intros; apply Hnotempty; intuition.
        split; rewrite concat_cons in Hnodup. rewrite -catA. simpl; simpl in Hnodup; done.
        move : Hsolved; clear; intros. specialize (Hsolved (a :: l1) l2 scc).
        simpl in Hsolved. rewrite -catA; simpl. apply Hsolved; try intuition.
        rewrite -H //.
        assert ((solved ++ a) ++ concat l1 ++ scc = solved ++ (a ++ concat l1)%list ++ scc). 
          rewrite (catA (solved ++ a) (concat l1)). rewrite (catA solved (a ++ concat l1)%list).
          apply app_inv_tail_iff. intuition. 
        rewrite -H1 //.
        (* tarjan end *)
        (* extract start *)
        move : Hextract; clear; intros. unfold extract_correctness in *. intros; apply Hextract. simpl. apply in_or_app; right ;done.
        (* extract end *)
        (* limitation start *)
        move : Hlimit'; clear; intros.
        unfold circuit_limitation in *.
        intros. apply (List.in_cons a) in H; apply Hlimit' in H; clear Hlimit'. done.
        (* limitation end *)
        (* initial start *)
        assert (Hextract' : forall var0, List.In var0 a -> exists cs, PVM.find var0 c1map = Some cs).
          move : Hextract; clear; intros. destruct (Hextract var0) as [cs [Hfind _]]. simpl. apply in_or_app;left; done.
          exists cs; done.
        move : Hinitial Hsc Hextract'; clear.
        unfold initial_correctness in *. 
        split; intros. 
        - apply (solve_simple_cycle_mem_or _ _ _ _ _ _ Hsc var) in H. apply in_or_app. destruct H. right; done.
          apply initialize_mem_or in H; try done. destruct H. right; done. left; apply Hinitial; done.
        - apply in_app_or in H. destruct H. apply Hinitial in H. apply (solve_simple_cycle_mem_or _ _ _ _ _ _ Hsc). right. apply (initialize_mem_or _ _ _ Hextract'); right; done.
          apply (solve_simple_cycle_mem_or _ _ _ _ _ _ Hsc); left; done.
        (* initial end *)*) admit.

      * (* normal scc *)
        case Hubs : (solve_ubs a a (List.filter
          (fun c : Constraint1 => Datatypes.length (rhs_terms1 c) != 0)
          (remove_solveds initial (extract_cs a c1map)))) => [ubs|]; rewrite Hubs in Hsolve; try discriminate.
        remember (mergeValuations (initialize_tbsolved a initial c1map) ubs) as bs eqn : Hbs. 
        remember (remove_solveds initial (extract_cs a c1map)) as cs1' eqn : Hcs1.
        case Hbab : (bab_bin a bs cs1' nil) => [nv|]; rewrite Hbab in Hsolve; try discriminate. assert (Hbabmem : forall var, List.In var a <-> PVM.mem var nv) by admit.
        case Hmerged : (merge_solution a (initialize_tbsolved a initial c1map) nv) => [new_values|]; rewrite Hmerged in Hsolve; try discriminate.
        assert (smaller_valuation new_values temp_s).
          clear IH Hsolve.
          generalize Hinit; intros Hsmaller. rewrite /smaller_valuation. intros var Hin.
          assert (Hmem : PVM.mem var initial \/ List.In var a).
            apply (merge_solution_mem_or _ _ _ _ Hmerged) in Hin. destruct Hin. right; done. 
            assert (forall var, List.In var a -> (exists cs, PVM.find var c1map = Some cs)).
              move : Hextract; clear; intros. rewrite /extract_correctness in Hextract. destruct (Hextract var) as [cs [Hfind _]].
              simpl; apply in_or_app; left; done. exists cs; done.
            apply (initialize_mem_or _ _ _ H0) in H. destruct H. right; done. left; done.
          clear Hin; destruct Hmem. 
          rewrite /smaller_valuation in Hsmaller. generalize H; apply Hsmaller in H; clear Hsmaller; intros Hmem.
          - (* in initial *)
            assert (~List.In var a).
              move : Hmem Hinitial Htarjan; clear; intros. rewrite /initial_correctness in Hinitial; rewrite /tarjan_correctness in Htarjan.
              apply Hinitial in Hmem; clear Hinitial. move : Htarjan => [_ [Hnodup _]]. simpl in Hnodup; rewrite catA in Hnodup. apply NoDup_app_remove_r in Hnodup.
              apply (NoDup_app_notin_r _ _ Hnodup _ Hmem).
            assert (forall var, List.In var a -> exists cs, PVM.find var c1map = Some cs).
              move : Hextract; clear; intros. rewrite /extract_correctness in Hextract. destruct (Hextract var) as [cs [Hfind _]].
              simpl; apply in_or_app; left; done. exists cs; done.
            destruct H as [value0 [value1 H]]. apply (find_merge_notin_eq _ _ _ _ _ H0) in Hmerged.
            rewrite -(find_init_notin_eq _ _ _ _ H0 H1) in Hmerged.
            exists value0; exists value1. rewrite -Hmerged //.
          - (* in tbsolved *)
            assert (NoDup a). move : Htarjan; clear; intros.
              rewrite /tarjan_correctness in Htarjan. move : Htarjan => [_ [Hnodup _]]. apply NoDup_app_remove_l in Hnodup. simpl in Hnodup.
              apply NoDup_app_remove_r in Hnodup; done.
            rewrite -(find_merge_in_eq _ _ _ _ _ H0 H Hmerged).
            apply (bab_bin_smallest a) with (s := temp_s) in Hbab; try done. rewrite /le in Hbab.
              apply Hbabmem in H. apply find_mem in H; destruct H as [val Hfind]. generalize Hfind; apply Hbab in Hfind; destruct Hfind as [value1 Hfind].
              intros; exists val; exists value1; split; try done.
            admit. (* TBD *)
            split. assert (forallb (satisfies_constraint1 temp_s) cs1') by admit.
              move : H1 Hubs Hbs; clear; intros. rewrite /In. admit. (* TBD *)

            split. move : Hlimit Htemp Hcs1 Hsmaller; clear; intros. move : Htemp => [Htemp _].
              assert (forallb (satisfies_constraint1 temp_s) (extract_cs solved c1map) /\
                forallb (satisfies_constraint1 temp_s) (extract_cs a c1map)).
                split. rewrite extract_cs_app in Htemp. rewrite extract_cs_app in Htemp. apply forallb_forall; intros.
                assert (List.In x ((extract_cs solved c1map ++ extract_cs a c1map) ++ extract_cs (concat l) c1map)). apply in_or_app; left. apply in_or_app; left; done.
                clear H; move: x H0; apply forallb_forall; done.
                rewrite extract_cs_app in Htemp. rewrite extract_cs_app in Htemp. apply forallb_forall; intros.
                assert (List.In x ((extract_cs solved c1map ++ extract_cs a c1map) ++ extract_cs (concat l) c1map)). apply in_or_app; left. apply in_or_app; right; done.
                clear H; move: x H0; apply forallb_forall; done. clear Htemp. move : H => [Hsolved Ha].
              apply forallb2satisfies_all_constraint1. rewrite Hcs1; clear Hcs1 cs1'. apply remove_solveds_smaller_sat; try done.
              apply Hlimit; simpl; left; done.
            apply forallb2satisfies_all_constraint2. apply forallb_forall. intros; done.

        move : Htemp H; apply IH with (initial := new_values); try done.
        (* tarjan start *)
        unfold tarjan_correctness in *.
        move : Htarjan => [Hnotempty [Hnodup Hsolved]]. split. intros; apply Hnotempty; intuition.
        split; rewrite concat_cons in Hnodup. rewrite -catA. simpl; simpl in Hnodup; done. move : Hsolved => [_ Hsolved].
        split. intros. specialize (Hsolved nil l a). simpl; intros. move : H; apply Hsolved; done.
        move : Hsolved; clear; intros. specialize (Hsolved (a :: l1) l2 scc).
        simpl in Hsolved. 
        assert ((solved ++ a) ++ concat l1 ++ scc = solved ++ (a ++ concat l1)%list ++ scc). 
          rewrite (catA (solved ++ a) (concat l1)). rewrite (catA solved (a ++ concat l1)%list).
          apply app_inv_tail_iff. intuition. 
        rewrite -H1 in Hsolved. apply Hsolved. rewrite H //. done.
        (* tarjan end *)
        (* extract start *)
        move : Hextract; clear; intros. unfold extract_correctness in *. intros; apply Hextract. simpl. apply in_or_app; right ;done.
        (* extract end *)
        (* limitation start *)
        move : Hlimit'; clear; intros.
        unfold circuit_limitation in *.
        intros. apply (List.in_cons a) in H; apply Hlimit' in H; clear Hlimit'. done.
        (* limitation end *)
        (* initial start *)
        assert (Hextract' : forall var0, List.In var0 a -> exists cs, PVM.find var0 c1map = Some cs).
          move : Hextract; clear; intros. destruct (Hextract var0) as [cs [Hfind _]]. simpl. apply in_or_app;left; done.
          exists cs; done.
        move : Hinitial Hmerged Hextract'; clear.
        unfold initial_correctness in *. 
        split; intros. 
        - apply (merge_solution_mem_or _ _ _ _ Hmerged) in H. apply in_or_app. destruct H. right; done.
          apply initialize_mem_or in H; try done. destruct H. right; done. left; apply Hinitial; done.
        - apply in_app_or in H. destruct H. apply Hinitial in H. apply (merge_solution_mem_or _ _ _ _ Hmerged). right. apply (initialize_mem_or _ _ _ Hextract'); right; done.
          apply (merge_solution_mem_or _ _ _ _ Hmerged); left; done.
        (* initial end *)


  intros. apply (Hhelper _ _ initial_valuation) with (value := value) (temp_s := temp_s) in Hsolve; try done. 
  (*admit. (* initial_correctness *)
  move : H1 => [H1 H1'].
  split; try done.
  simpl.
  apply forallb_forall.  
  assert (forall x : Constraint1, List.In x (concat
    (List.split (PVM.elements c1map)).2) -> satisfies_constraint1 temp_s x = true) by (apply forallb_forall; rewrite H1 //).
  clear H1.
  intros. 
  assert (forall x : Constraint1, List.In x (concat (List.split (PVM.elements c1map)).2) <->
    List.In x (extract_cs (concat scclist) c1map)) by admit. (* extract_corrctness *)
  apply H3 in H1; clear H3.
  move : H1; apply H2.*)
Admitted.


(*Lemma is_goodubs_helper ls : forall tbsolved ubs cs1, NoDup tbsolved -> ls <> [] ->
  (forall c : Constraint1, List.In c cs1 -> List.In (lhs_var1 c) ls) ->
  (*forall var : ProdVar.t, List.In var (constraints1_vars cs1) -> List.In var ls) ->*)
  (forall c : Constraint1, List.In c cs1 -> rhs_power c = []) -> 
  (forall c : Constraint1, List.In c cs1 -> good_terms (rhs_terms1 c)) -> 
  solve_ubs tbsolved ls cs1 = Some ubs -> goodubs cs1 ubs.
Proof.
  elim. 
  - simpl; intros ubs cs1 Hnodup Hnotempty Hlhsin Hpower Hterm H.
    rewrite /goodubs; intros.
    inversion H; subst; clear H. unfold initial_valuation in *.
    rewrite /strict_smaller_valuation in H0; move : H0 => [_ [H0 _]]. destruct H0 as [var [H0 _]]. done.
    (*intro Hsat. unfold initial_valuation in *.
    assert (forall c, List.In c (List.filter
      (fun c : Constraint1 =>
      forallb ((PVM.mem (elt:=nat))^~ (PVM.empty nat)) (constraint1_vars c))
      cs1) -> satisfies_constraint1 temp_ub c) by (apply forallb_forall; done). clear Hsat.
    destruct (destruct_list cs1).
    destruct s as [hd [tl Hcons]].
    assert (List.In  (lhs_var1 hd) (constraints1_vars cs1)).
      rewrite Hcons; simpl; left; done.
    apply H0 in H; discriminate.
    intuition.*)

  - intros hd tl IH ubs cs1 Hnodup Hnotempty Hlhsin Hpower Hterm Hsolve.
    (* specialize (solve_ubs_in_cs _ _ _ _ Hsolve) as Hsolvein. 
    assert (Hsolvein : forall var : ProdVar.t, List.In var (constraints1_vars cs1) -> PVM.mem (elt:=nat) var ubs) by admit. *)
    simpl in Hsolve.
    destruct (solve_ub hd ls cs1) eqn:H_solve_hd;
    try discriminate.
    destruct (solve_ubs tl ls cs1) eqn:H_solve_tl;
    try discriminate.
    inversion Hsolve; subst; clear Hsolve.
    apply IH in H_solve_tl as H; clear IH; try done.
    unfold goodubs in *; intros (*Hmem*) temp_ub Hsmall. 
    assert (Hhd : ~ (PVM.mem hd v)). intro Hmem. apply (solve_ubs_tbsolved_in _ _ _ _ H_solve_tl) in Hmem. apply NoDup_cons_iff in Hnodup. move : Hnodup => [Hnodup _]; done.
    assert ((strict_smaller_valuation v (PVM.remove hd temp_ub)) \/ 
      (exists value1, PVM.find hd temp_ub = Some value1 /\ (Z.to_nat t) < value1)).
      unfold strict_smaller_valuation in Hsmall.
      move : Hsmall => [H1 [H2 H3]].
      destruct H2 as [var [H2 Hfind]].
      unfold add_valuation in *.
      destruct (var == hd) eqn : Hvar.
      - move /eqP : Hvar => Hvar; subst.
        right.
        (*specialize (add_mem hd (Z.to_nat t) v); intro Hfind.
        apply H2 in Hfind; clear H2.*)
        destruct Hfind as [value0 [value1 [Hfind0 Hfind1]]].
        rewrite find_add_eq in Hfind0; try done.
        inversion Hfind0; subst; clear Hfind0.
        exists value1; done.
      - move /eqP : Hvar => Hvar.
        left.
        unfold strict_smaller_valuation.
        split.
        - clear H2; intros var0 Hmem0.
          generalize Hmem0; intros Hmem'.
          apply (mem_add _ hd (Z.to_nat t)) in Hmem0.
          apply H1 in Hmem0.
          destruct Hmem0 as [value0 [value1 Hfind0]].
          rewrite find_add_neq in Hfind0; try done.
          rewrite find_remove_neq.
          exists value0; exists value1; done.
          1,2 : intro H4; subst; rewrite Hmem' in Hhd; done.
        - split. clear H1; exists var. split. 
          apply mem_add_or in H2. destruct H2; try done. move /eqP : H0 => H0; done.
          (*intro Hmem0.
          apply (mem_add _ hd (Z.to_nat t)) in Hmem0.
          apply H2 in Hmem0.*)
          destruct Hfind as [value0 [value1 Hfind0]].
          rewrite find_add_neq in Hfind0; try done.
          rewrite find_remove_neq; try done.
          exists value0; exists value1; done.
        - admit. (* TBD *)

    rewrite /strict_smaller_valuation in Hsmall. move : Hsmall => [_ [_ Hmemeq]].
    (*assert (List.filter (fun c : Constraint1 => forallb ((PVM.mem (elt:=nat))^~ (add_valuation hd (Z.to_nat t) v)) (constraint1_vars c))
    cs1 = cs1).
      apply filter_full.
      move : Hsolvein; clear; intros.
      apply forallb_forall; intros.
      apply Hsolvein.
      move : x n H0 H; clear; move: cs1.
      elim.
      - simpl; intros; try done.
      - simpl; intros.
        destruct H1; subst.
        destruct H0. left; done. right. apply in_or_app; left; done.
        apply H in H0; try done.
        right. apply in_or_app; right; done.
    rewrite H1; clear H1.*)
    destruct H0.
    - apply H in H0; try done; clear H.
      destruct H0 as [c0 [Hin Hunsat]].
      exists c0; split; try done. (*split. apply mem_add_or; left; done.*)
      unfold satisfies_constraint1 in *. 
      destruct (lhs_var1 c0 == hd) eqn : Heq. move/eqP : Heq => Heq; subst.
      * rewrite find_remove_eq in Hunsat. (*apply Z.leb_gt in Hunsat.
        case Hfindlhs : (PVM.find (elt:=nat) (lhs_var1 c0) temp_ub) => [a|]; apply Z.leb_gt.
      Search ((_<=?_)%Z).

      assert (Hneq : (lhs_var1 c0) <> hd) by (intro Heq; rewrite Heq in Hmem; done).
      rewrite find_remove_neq in Hunsat; try done.
      assert ((rhs_value1 (PVM.remove (elt:=nat) hd temp_ub) c0 <= rhs_value1 temp_ub c0)%Z) by admit.
      case Hfind : (PVM.find (elt:=nat) (lhs_var1 c0) temp_ub) => [val|]; rewrite Hfind in Hunsat; try done.
      1,2 : apply Z.leb_gt; apply Z.leb_gt in Hunsat; 
      move : Hunsat H; apply Z.lt_le_trans.*) admit. admit. 

    - clear H (*H_solve_tl Hmem Hhd tl v*).
      rewrite /solve_ub in H_solve_hd.
      case Hexists : (List.existsb (fun c : Constraint1 => (rhs_const1 c >? 0)%Z)
        (substitute_vs (List.filter (fun p : ProdVar.t => p != hd) ls) cs1)); rewrite Hexists in H_solve_hd; try discriminate.
      specialize (substitute_correctness temp_ub cs1 (List.filter (fun p : ProdVar.t => p != hd) ls) Hpower Hterm); intros Hsub.
      specialize (reduce_constraints1 (PVM.remove hd temp_ub) (substitute_vs (List.filter (fun p : ProdVar.t => p != hd) ls) cs1) hd); intro.
      assert (Z.le 0 t). apply (reduce_constraints1_helper _ _ _ _) in H_solve_hd; simpl in H_solve_hd; try done.
        move : H_solve_hd; clear; intros. destruct H_solve_hd as [c [Hin [coe [Hfind [Hcoe Heq]]]]]. rewrite -Heq; clear Heq.
        assert (H: (0 <= Z.abs (rhs_const1 c) / Z.of_nat (coe - 1))%Z). apply Z_div_nonneg_nonneg; try lia. lia. 
        apply substitute_vs_is_hd; try done. intro c; apply substitute_vs_good_terms; try done.

      rewrite H_solve_hd in H; clear H_solve_hd.
      destruct H0 as [value1 [Hfind Hlt]].
      assert (Z.lt t (Z.of_nat value1)).
        apply Z2Nat.inj_lt; try done.
        apply Nat2Z.is_nonneg.
        rewrite Nat2Z.id.
        apply (elimT leP); done.
      apply H in H0; clear H.
      rewrite Nat2Z.id in H0.
      rewrite (find_remove_add _ _ Hfind) in H0.
      destruct H0 as [c [H0 [H2 H3]]]. assert (exists c : Constraint1,
        List.In c (substitute_vs (List.filter (fun p : ProdVar.t => p != hd) ls) cs1) /\ satisfies_constraint1 temp_ub c = false) by (exists c; split; try done).
      specialize (substitute_vs_is_hd hd ls cs1 Hnotempty Hlhsin); intro.
      assert (forall c, List.In c (substitute_vs (List.filter (fun p : ProdVar.t => p != hd) ls) cs1) -> lhs_var1 c == hd) by (apply forallb_forall; done). clear H4.
      assert ((exists c : Constraint1,
        List.In c (substitute_vs (List.filter (fun p : ProdVar.t => p != hd) ls) cs1) /\
        PVM.mem (elt:=nat) (lhs_var1 c) temp_ub /\ satisfies_constraint1 temp_ub c = false)). move : Hfind H H5;clear; intros. destruct H as [c [Hin Hunsat]].
        apply H5 in Hin as H. move /eqP : H => H; subst. exists c; split; try done. split; try done. apply find_mem. exists value1; done.
      clear H H5. apply Hsub in H4. move : Hmemeq H4; clear; intros. destruct H4 as [c' [Hin [Hmem Hunsat]]]. exists c'; split;try done. split; try done. apply Hmemeq; try done.  

      apply substitute_vs_is_hd; try done. intros. split. move : H; apply substitute_vs_good_terms; try done. split. 
      specialize (List.In _nth _ _ c H); intros. destruct H2 as [n [Hle Hnth]].
      apply (existsb_nth _ _ c Hle) in Hexists. rewrite Hnth in Hexists. lia.
      move : H; apply substitute_vs_no_power; try done. 
      apply NoDup_cons_iff in Hnodup.
      exact Hnodup.2.
    Admitted.*)






(*Lemma is_goodbound solved cs initial : forall tbsolved ubs, is_good_smallest solved cs initial -> solve_ubs tbsolved tbsolved [seq x <- (split_constraints cs).1 | constraint1_in_set tbsolved x] = Some ubs -> isGoodbound solved tbsolved cs (initialize_tbsolved tbsolved solved initial cs) ubs.
Proof.
  intros; rewrite /isGoodbound.
  split; try apply initialize_tbsolved_correctness; try done.
  intros.
  assert (exists c, List.In c (List.filter (constraint1_in_set (List.map fst (PVM.elements ubs)))
    (split_constraints cs).1) -> satisfies_constraint1 temp_ub c = false).
  move : tbsolved ubs H H0 temp_ub H1.
  elim.
  - simpl; intros.
    rewrite /initial_valuation in H0; injection H0 as H0; subst.
    rewrite /smaller_valuation in H1.
    assert (Hempty : forall A, PVM.elements (PVM.empty A) = []) by admit.
    rewrite Hempty in H1; rewrite Hempty.
    simpl; simpl in H1.
    rewrite filter_empty_set.
    exists ({|
      lhs_var1 := (N0, N0);
      rhs_const1 := 0;
      rhs_terms1 := [(1, (N0,N0))]
    |}); intros.
    specialize List.in_nil with (a := {| lhs_var1 := (0%num, 0%num); rhs_const1 := 0; rhs_terms1 := [(1, (0%num, 0%num))] |}); intros.
    done.
  - simpl.
  
Admitted.*)


(*Definition c0 : Constraint1 :=
  {|
    lhs_var1 := (2%num, N0);
    rhs_const1 := 0;
    rhs_terms1 := [(1, (5%num, N0))];
    rhs_power := []
  |}.

Definition c1 : Constraint1 :=
  {|
    lhs_var1 := (2%num, N0);
    rhs_const1 := 32;
    rhs_terms1 := [];
    rhs_power := []
  |}.

Definition c2 : Constraint1 :=
  {|
    lhs_var1 := (3%num, N0);
    rhs_const1 := 1;
    rhs_terms1 := [(1, (2%num, N0))];
    rhs_power := []
  |}.

Definition c3 : Constraint1 :=
  {|
    lhs_var1 := (3%num, N0);
    rhs_const1 := 4;
    rhs_terms1 := [];
    rhs_power := []
  |}.

Definition c4 : Constraint1 :=
  {|
    lhs_var1 := (4%num, N0);
    rhs_const1 := -1;
    rhs_terms1 := [(1, (3%num, N0))];
    rhs_power := []
  |}.

Definition c5 : Constraint1 :=
  {|
    lhs_var1 := (5%num, N0);
    rhs_const1 := 0;
    rhs_terms1 := [(1, (2%num, N0))];
    rhs_power := []
  |}.

Definition c6 : Constraint1 :=
  {|
    lhs_var1 := (5%num, N0);
    rhs_const1 := 0;
    rhs_terms1 := [(1, (4%num, N0))];
    rhs_power := []
  |}.

Definition c1map0 := PVM.add (2%num, N0) [c0;c1] (PVM.empty (list Constraint1)).
Definition c1map1 := PVM.add (3%num, N0) [c2;c3] c1map0.
Definition c1map2 := PVM.add (4%num, N0) [c4] c1map1.
Definition c1map3 := PVM.add (5%num, N0) [c5;c6] c1map2.

Definition hd := [(2%num, N0);(3%num, N0);(4%num, N0);(5%num, N0)].
Definition nv0 := initialize_tbsolved hd initial_valuation c1map3.
Definition tbsolved_cs := extract_cs hd c1map3.
Definition constraints := combine_cs tbsolved_cs [].
Definition nv := solve_simple_cycle hd constraints [] nv0.
Definition nv' := solve_simple_cycle hd (map (fun c => Phi1 c) [c0; c2; c4;c5;c6]) [] nv0.
Definition nv1 := solve_simple_cycle_rec 4 hd [c0; c2; c4;c5;c6] nv0.
Definition nv2 := solve_simple_cycle' 4 (2%num, N0) [c0; c2; c4;c5;c6] nv0.
Definition nv3 := match nv2 with
  | Some nv2' => solve_simple_cycle' 4 (3%num, N0) [c0; c2; c4;c5;c6] nv2'
  | _ => None
  end.
Definition cs1 := find_constraint1s (3%num, N0) [c0; c2; c4;c5;c6].
Definition val := match nv2 with
  | Some nv2' => PVM.find (3%num, N0) nv2'
  | _ => None
  end.
Definition nv3' := match nv2 with
  | Some nv2' => simplify_constraints (3%num, N0) 4 33 cs1 [c0; c2; c4;c5;c6] nv2'
  | _ => None
  end.
Definition nval := match nv2 with
  | Some nv2' => simplify_constraint (3%num, N0) 4 0 33 c2 [c0; c2; c4;c5;c6] nv2' 
  | _ => None
  end.*)

Section solve_fun.

Variable (c : hfcircuit).

Definition solve_helper (c1map : PVM.t (list Constraint1)) (cs2 : list min_rhs) : option Valuation :=
  let cs1 := List.concat ((List.split (PVM.elements c1map)).2) in
  let dpdcg := build_dependency_graph cs1 in
  let res := rev (map rev (kosaraju dpdcg)) in
  let res' := map (map (@finProdVar2ProdVar c)) res in
  solve_alg_check res' c1map cs2.

Definition solve_fun (tmap : VM.t (ftype * forient)) : option Valuation :=
  match extract_constraints_c c tmap with
  | Some (c1maps, cs2) => fold_left (fun res c1map => match res, solve_helper c1map cs2 with
                                | None, new_values => new_values
                                | Some old_values, Some new_values => Some (branch_and_bound.smaller_valuation old_values new_values)
                                | Some old_values, _ => res
                                end) c1maps None
  | _ => None
  end.

Definition InferWidths_transp (p : hfport) (tmap : VM.t (ftype * forient)) : option hfport :=
  match p with
  | Finput v t => if (ftype_not_implicit t) then Some p
                  else (match VM.find v tmap with
                  | Some (ft, _) => Some (Finput v ft)
                  | _ => None
                  end)
  | Foutput v t => if (ftype_not_implicit t) then Some p
                  else (match VM.find v tmap with
                  | Some (ft, _) => Some (Foutput v ft)
                  | _ => None
                  end)
  end.

Fixpoint InferWidths_transps (ps : seq hfport) (tmap : VM.t (ftype * forient)) : option (seq hfport) :=
  match ps with
  | nil => Some nil
  | p :: tl => match InferWidths_transp p tmap, InferWidths_transps tl tmap with
                  | Some n, Some nss => Some (n :: nss)
                  | _, _ => None
                  end
  end.

Fixpoint InferWidths_transs (s : hfstmt) (tmap : VM.t (ftype * forient)) : option hfstmt :=
  match s with
  | Sskip => Some s
  | Swire v t => if (ftype_not_implicit t) then Some s
                  else (match VM.find v tmap with
                  | Some (ft, _) => Some (Swire v ft)
                  | _ => None
                  end)
  | Sreg v r => if (ftype_not_implicit (type r)) then Some s
                else (match VM.find v tmap with
                | Some (ft, _) => Some (Sreg v (mk_freg ft (clock r) (reset r)))
                | _ => None
                end)
  | Smem v m => Some s
  | Sinst v inst => Some s
  | Snode v e => Some s
  | Sfcnct v e => Some s
  | Sinvalid _ => Some s
  | Swhen c s1 s2 => match InferWidths_transss s1 tmap, InferWidths_transss s2 tmap with
                    | Some n1, Some n2 => Some (Swhen c n1 n2)
                    | _, _ => None
                    end
  end
with InferWidths_transss (sts : hfstmt_seq) (tmap : VM.t (ftype * forient)) : option hfstmt_seq :=
  match sts with
  | Qnil => Some Qnil
  | Qcons s ss => match InferWidths_transs s tmap, InferWidths_transss ss tmap with
                  | Some n, Some nss => Some (Qcons n nss)
                  | _, _ => None
                  end
  end.

Fixpoint update_tmap (tmap : VM.t (ftype * forient)) (new_widths : list (ProdVar.t * nat)) : option (VM.t (ftype * forient)) :=
  match new_widths with
  | nil => Some tmap
  | (pv, w) :: tl => match VM.find pv.1 tmap with
                    | Some (ft, ori) => match update_ftype (N.to_nat pv.2) w ft with (* 无implicit *)
                                | Some nft => update_tmap (VM.add pv.1 (nft, ori) tmap) tl
                                | _ => None
                                end
                    | _ => None
                    end
  end.

Definition InferWidths_fun : option hfcircuit :=
  match circuit_tmap c, c with
  | Some tmap, Fcircuit cv [::(FInmod mv ps ss)] =>
    match solve_fun tmap with
    | Some solution =>
      match update_tmap tmap (PVM.elements solution) with
      | Some newtm => match InferWidths_transps ps newtm, InferWidths_transss ss newtm with
                      | Some nps, Some nss => Some (Fcircuit cv [::(FInmod mv nps nss)])
                      | _, _ => None
                      end
      | _ => None
      end
    | _ => None
    end
  | _, _ => None
  end.

End solve_fun.