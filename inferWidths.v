From HB Require Import structures.
From Coq Require Import ZArith Arith List Ascii String Lia FMaps.
From mathcomp Require Import all_ssreflect.
From mathcomp.tarjan Require Import kosaraju tarjan_nocolors acyclic acyclic_tsorted.
From Solver Require Import Env LoFirrtl HiEnv HiFirrtl branch_and_bound constraints floyd_sc graph scc extract_cs extract_cswithmin.
Import ListNotations.

Section acyclic.

Fixpoint max_nl (l : list Z.t) (init : nat): nat :=
  match l with
  | nil => init
  | t :: tl => max_nl tl (Z.to_nat (Z.max (Z.of_nat init) t))
  end.

End acyclic.

Definition is_simple_cycle (cs : list Constraint1) : bool :=
  forallb (fun c => match rhs_terms1 c with
                  | nil
                  | [::(1,_)] => true
                  | _ => false
                  end) cs.

Definition solve_scc (hd : list ProdVar.t) (constraints : list Constraint1) : option Valuation := 
match hd with
| [:: v] => let (cs, cs_have_v) := List.partition (fun c => ((rhs_terms1 c) == nil) && ((rhs_power c) == nil)) constraints in
            let nval := max_nl (List.map (fun c => rhs_const1 c) cs) 0 in
            let nv := PVM.add v nval initial_valuation in
            if forallb (fun c => satisfies_constraint1 nv c) cs_have_v then
                Some nv else None
| _ => if is_simple_cycle constraints then solve_simple_cycle hd constraints 
    else let remove_only_const := List.filter (fun c => List.length (rhs_terms1 c) != 0) constraints in
        match solve_ubs_aux hd remove_only_const with
        | Some ubs => let bs := mergeBounds ubs in bab_bin hd bs constraints []
        | _ => None
        end 
end.

Fixpoint solve_alg (res : list (list ProdVar.t)) (values : Valuation) (cs1 : PVM.t (list Constraint1)) : option Valuation :=
match res with
| nil => Some values
| hd :: tl => 
    let tbsolved_cs := extract_cs hd cs1 in 
    let tbsolved_cs' := List.map (remove_solved_c values) tbsolved_cs in
    match solve_scc hd tbsolved_cs' with
    | Some nv => match merge_solution hd values nv with
        | Some new_values => solve_alg tl new_values cs1 
        | _ => None
        end
    | None => None
    end
end.

Definition solve_alg_check (res : list (list ProdVar.t)) (cs1 : PVM.t (list Constraint1)) (cs2 : list min_rhs) : option Valuation :=
  match solve_alg res initial_valuation cs1 with
  | Some value => if (forallb (fun c => Z.leb (min_rhs_value value c) 1%Z) cs2) then Some value else None
  | _ => None
  end.

(***************      Lemmas of computing max       ******************)

Lemma terms_value'_eq v c cst : terms_value v c cst = terms_value' v c cst.
Proof.
  move : c cst; elim. simpl; done.
  simpl; intros. rewrite H; clear H. unfold terms_value_aux. done.
Qed.

Lemma rhs_value1'_eq v c : rhs_power c = nil -> rhs_value1 v c = rhs_value1' v c.
Proof.
  unfold rhs_value1; unfold rhs_value1'. intro. rewrite H; simpl. rewrite Z.add_0_r.
  rewrite terms_value'_eq //.
Qed.

Lemma satisfies_constraint1_eq v c : rhs_power c = nil -> satisfies_constraint1' v c = satisfies_constraint1 v c.
Proof.
  intro. unfold satisfies_constraint1'; unfold satisfies_constraint1. destruct (PVM.find (lhs_var1 c) v); try done.
  rewrite rhs_value1'_eq //.
Qed.

Lemma satisfies_all_constraint1_eq v cs : (forall c, List.In c cs -> rhs_power c = nil) -> satisfies_all_constraint1 v cs = Solver.constraints.satisfies_all_constraint1 v cs.
Proof.
  intros. induction cs. simpl; done. simpl. rewrite IHcs. rewrite satisfies_constraint1_eq //. apply H; simpl; left; done.
  intros; apply H; simpl; right; done.
Qed.

Axiom NoDupA_NoDup : forall l, NoDupA (PVM.eq_key (elt:=nat)) l -> NoDup l.

Axiom key_NoDup : forall B (v : PVM.t B), NoDup (List.split (PVM.elements v)).1.

Axiom key_in_elements : forall [A : Type] (m : PVM.t A) v, List.In v (List.split (PVM.elements m)).1 <-> exists val, List.In (v, val) (PVM.elements m).

Lemma forallb2satisfies_all_constraint1 values: forall cs, forallb (satisfies_constraint1 values) cs <-> Solver.constraints.satisfies_all_constraint1 values cs.
Proof.
  split. induction cs as [|c cs' IH]. simpl; intros; done. simpl; intros. move /andP : H => [H H1]. apply IH in H1. rewrite H H1 //.
  induction cs as [|c cs' IH]. simpl; intros; done. simpl; intros. move /andP : H => [H H1]. apply IH in H1. rewrite H H1 //.
Qed.

Lemma max_list_correctness : forall zl init, init <= (max_nl zl init) /\ (forall z, List.In z zl -> Z.le z (Z.of_nat (max_nl zl init))).
Proof.
  elim. 
  - intros; split.
    + simpl; done. 
    + intros c H. intuition.
  - intros hd tl IH init.
    simpl. split.
    + destruct (IH (Z.to_nat (Z.max (Z.of_nat init) hd))) as [H1 _].
      assert (init <= Z.to_nat (Z.max (Z.of_nat init) hd)).
      { destruct (Z.max_spec (Z.of_nat init) hd) as [[Hlt Hmax] | [Hge Hmax]];
        rewrite Hmax; clear Hmax.
        - assert (Hnonneg : (0 <= hd)%Z) by lia. 
          rewrite <- (Nat2Z.id init). assert (Hnonneg2 : (0 <= (Z.of_nat init))%Z) by lia. 
          apply (introT leP).
          apply (Z2Nat.inj_le _ _ Hnonneg2 Hnonneg). try lia.
        - rewrite Nat2Z.id //. }
      apply (leq_trans H H1).
    + intros c' Hc'.
      destruct (IH (Z.to_nat (Z.max (Z.of_nat init) hd))) as [H1 H2].
      destruct Hc'.
      * subst.
        clear H2. 
        rewrite -(Nat2Z.id (max_nl tl (Z.to_nat (Z.max (Z.of_nat init) c')))) in H1.
        apply (elimT leP) in H1.
        apply Z2Nat.inj_le in H1.
        assert (c' <= Z.max (Z.of_nat init) c')%Z by (apply Z.le_max_r).
        move : H H1; apply Z.le_trans. 
        intuition. intuition.
      * apply H2; done.
Qed.

(***************      Lemmas of solving bounds       ******************)

Lemma substitute_constraint_lhs_eq x a b c : lhs_var1 (substitute_constraint x a b c) = lhs_var1 x.
Proof.
  rewrite /substitute_constraint.
  case : (List.find (fun p : term => p.2 == a) (rhs_terms1 x)); try done.
  intros [coe var]; simpl; done.
Qed.

Lemma substitute_c_correctness c1 c2 v : satisfies_constraint1 v c1 -> satisfies_constraint1 v c2 ->
  rhs_power c1 = nil -> rhs_power c2 = nil -> good_terms (rhs_terms1 c1) -> good_terms (rhs_terms1 c2) ->
  satisfies_constraint1 v (substitute_c c1 c2).
Proof.
  rewrite /substitute_c /satisfies_constraint1.
  intros Hsat1 Hsat2 Hhd_power Htl_power Hhd_term Htl_term.
  case Hfind1 : (PVM.find (lhs_var1 c1) v) => [val1|]; rewrite Hfind1 in Hsat1; try discriminate.
  case Hfind2 : (PVM.find (lhs_var1 c2) v) => [val2|]; rewrite Hfind2 in Hsat2; try discriminate.
  rewrite substitute_constraint_lhs_eq Hfind1. apply Zle_imp_le_bool. apply Zle_bool_imp_le in Hsat1. apply Zle_bool_imp_le in Hsat2.
  
  assert ((rhs_value1 v (substitute_constraint c1 (lhs_var1 c2) (rhs_terms1 c2) (rhs_const1 c2)) <= rhs_value1 v c1)%Z).
  { clear Hsat1. rewrite /substitute_constraint. 
    case Hfind : (List.find (fun p : term => p.2 == lhs_var1 c2) (rhs_terms1 c1)) => [[coe var]|]; try lia. 
    rewrite /rhs_value1 Hhd_power; simpl; rewrite Z.add_0_r; rewrite Z.add_0_r.
    assert ((terms_value v (fold_right (fun '(coe', var) (acc : list term) =>
              match List.find (fun p : term => p.2 == var) acc with
              | Some t =>
                  let (existing_coef, _) := t in
                  ((existing_coef + coe * coe')%N, var) :: remove term_dec (existing_coef, var) acc
              | None => ((coe * coe')%N, var) :: acc
              end) (remove term_dec (coe, lhs_var1 c2) (rhs_terms1 c1)) (rhs_terms1 c2))
          (rhs_const1 c1 + Z.of_nat coe * rhs_const1 c2) 
          = terms_value v (rhs_terms1 c1) (rhs_const1 c1) - Z.of_nat (coe * val2)
            + Z.of_nat coe * (terms_value v (rhs_terms1 c2) (rhs_const1 c2)))%Z).
    { apply substitute_constraint_rhs; try done.
      apply find_some in Hfind as Heq. 
      move /eqP : Heq.2 => Heq'; clear Heq. 
      simpl in Heq'; rewrite Heq' in Hfind; done. }
    rewrite H; clear H.
    rewrite Nat2Z.inj_mul -Z.sub_sub_distr -Zmult_minus_distr_l.
    apply (Zplus_le_reg_r _ _ (Z.of_nat coe * (Z.of_nat val2 - terms_value v (rhs_terms1 c2) (rhs_const1 c2))%Z)).
    rewrite Z.sub_add. rewrite -{1}(Z.add_0_r (terms_value v (rhs_terms1 c1) (rhs_const1 c1))).
    apply Z.add_le_mono_l.
    apply Ztac.mul_le; try intuition. apply Zle_minus_le_0.
    rewrite /rhs_value1 in Hsat2.
    rewrite Htl_power in Hsat2; simpl in Hsat2; rewrite Z.add_0_r in Hsat2; done. }
  move : H Hsat1; apply Z.le_trans.
Qed.

Lemma substitute_c_power c1 c2 : rhs_power c1 = nil -> rhs_power c2 = nil -> rhs_power (substitute_c c1 c2) = nil.
Proof.
  rewrite /substitute_c /substitute_constraint. intros.
  case : (List.find (fun p : term => p.2 == lhs_var1 c2) (rhs_terms1 c1)) => [[coe var]|]; simpl; try done.
Qed. 

Lemma substitute_cs_power cs new_c : (forall c, List.In c cs -> rhs_power c = nil) -> substitute_cs cs = Some new_c -> rhs_power new_c = nil.
Proof.
  move : cs new_c; elim. simpl; intros; try discriminate.
  simpl; intros. case Hsub : (substitute_cs l) => [c|]; rewrite Hsub in H1.
  inversion H1. apply /substitute_c_power. apply H0; left; done. move : Hsub; apply H. intros; apply H0; right; done.
  inversion H1. rewrite -H3; apply H0; left; done.
Qed. 

Lemma substitute_c_good_term c1 c2 : good_terms (rhs_terms1 c1) -> good_terms (rhs_terms1 c2) ->
  good_terms (rhs_terms1 (substitute_c c1 c2)).
Proof.
  intros Hterm1 Hterm2; intros. 
  rewrite /substitute_c /substitute_constraint; simpl.
  case Hfind : (List.find (fun p : term => p.2 == lhs_var1 c2) (rhs_terms1 c1)) => [[coe var]|]; try done.
  * simpl. apply substitute_good_terms; try done. apply good_terms_remove; try done.
    rewrite /good_terms in Hterm1. apply find_some in Hfind. move : Hfind.1. apply Hterm1.1.
Qed.

Lemma substitute_cs_good_term cs new_c : (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> substitute_cs cs = Some new_c -> good_terms (rhs_terms1 new_c).
Proof.
  move : cs new_c; elim. simpl; intros; try discriminate.
  simpl; intros. case Hsub : (substitute_cs l) => [c|]; rewrite Hsub in H1.
  inversion H1. apply /substitute_c_good_term. apply H0; left; done. move : Hsub; apply H. intros; apply H0; right; done.
  inversion H1. rewrite -H3; apply H0; left; done.
Qed. 

Lemma substitute_cs_correctness v : forall cs new_c, 
  (forall c, List.In c cs -> good_terms (rhs_terms1 c)) ->
  (forall c, List.In c cs -> rhs_power c = nil) ->
  forallb (satisfies_constraint1 v) cs -> substitute_cs cs = Some new_c -> satisfies_constraint1 v new_c.
Proof.
  elim. simpl; intros; try discriminate.
  simpl; intros. move /andP : H2 => [H4 H2]. case Hsub : (substitute_cs l) => [c|]; rewrite Hsub in H3.
  inversion H3; clear H3. apply (substitute_c_correctness _ _ _ H4).
  move : H2 Hsub; apply H. intros; apply H0; right; done. intros; apply H1; right; try done.
  apply H1; left; done. move : Hsub; apply substitute_cs_power. intros; apply H1; right; done. apply H0; left; done.
  move: Hsub; apply substitute_cs_good_term. intros; apply H0; right; done.
  inversion H3; clear H3. rewrite -H6 //.
Qed.

Lemma terms_value_ge_cst v : forall t cst, (cst <= terms_value v t cst)%Z.
Proof.
  elim. simpl; intros. intuition.
  simpl; intros. specialize (H (cst +
  Z.of_nat
    (a.1 *
     match PVM.find (elt:=nat) a.2 v with
     | Some val => val
     | None => 0
     end))%Z). move : H; apply Z.le_trans. intuition.
Qed.

Lemma compute_ub_correctness c ub v : satisfies_constraint1 v c -> compute_ub c = Some ub -> exists n : nat, PVM.find (lhs_var1 c) v = Some n /\ n <= ub.
Proof.
  rewrite /compute_ub; intros Hsat Hub. case Hfind : (List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c)) => [[coe var]|]; rewrite Hfind in Hub; try discriminate.
  case Hgt : (1 < coe); rewrite Hgt in Hub; try discriminate. inversion Hub; clear Hub H0.
  rewrite /satisfies_constraint1 in Hsat. case Hlhs : (PVM.find (lhs_var1 c) v) => [val|]; rewrite Hlhs in Hsat; try discriminate.
  exists val; split; try done. apply Zle_bool_imp_le in Hsat. 
  assert (Z.of_nat (coe * val) + rhs_const1 c <= rhs_value1 v c)%Z. 
  { clear Hgt Hsat. rewrite /rhs_value1.
    assert (terms_value v (rhs_terms1 c) (rhs_const1 c) <= terms_value v (rhs_terms1 c) (rhs_const1 c) + power_value v (rhs_power c))%Z.
      rewrite -{1}(Z.add_0_r (terms_value v (rhs_terms1 c) (rhs_const1 c))). apply Zplus_le_compat_l. rewrite /power_value.
      case : (rhs_power c); try done. intros. specialize (Z.pow_pos_nonneg 2 (terms_value v (a :: l) 0)); intro. 
      specialize (terms_value_ge_cst v (a :: l) 0); intro. apply H in H0; try done. intuition.
    move : H; apply Z.le_trans.
    assert (exists pre post, pre ++ (coe, lhs_var1 c) :: post = (rhs_terms1 c)).
      assert (Hin : List.In (coe, lhs_var1 c) (rhs_terms1 c)).
        apply find_some in Hfind; move : Hfind => [H H0]. move /eqP : H0 => H0; simpl in H0. subst var; done. 
      destruct (List.in_split _ _ Hin) as [pre [post Hsplit]].
      exists pre, post. symmetry. apply Hsplit.
    destruct H as [pre [post H]].
    rewrite -H; clear H. rewrite terms_value_app. simpl. rewrite Hlhs -(Z.add_0_l (rhs_const1 c + Z.of_nat (coe * val))) terms_value_cst_add.
    rewrite Z.add_assoc (Z.add_comm (Z.of_nat (coe * val)) (rhs_const1 c)) -{1}(Z.add_0_l (rhs_const1 c + Z.of_nat (coe * val))).
    apply Zplus_le_compat_r. apply Z.add_nonneg_nonneg. apply terms_value_ge_cst. apply terms_value_ge_cst. }
  specialize (Z.le_trans _ _ _ H Hsat); intro. clear Hsat H.
  rewrite Z.abs_neq. apply Z.le_add_le_sub_r in H0. rewrite -Z.add_opp_l in H0. apply Z.le_sub_le_add_r in H0.
  rewrite Nat2Z.inj_mul -{2}(Z.mul_1_l (Z.of_nat val)) -Z.mul_sub_distr_r in H0. apply Z.div_le_lower_bound in H0. 
  apply (introT leP). apply Nat2Z.inj_le. rewrite Z2Nat.id. rewrite Nat2Z.inj_sub; try simpl; try done.
    apply (elimT leP). apply ltnW; done. 
    rewrite Nat2Z.inj_sub; try simpl. move : H0; apply Z.le_trans. intuition. apply (elimT leP). apply ltnW; done. 
    apply (elimT ltP) in Hgt. apply Nat2Z.inj_lt in Hgt. simpl in Hgt. intuition.
    apply Z.le_add_le_sub_l in H0. apply (Z.le_trans _ _ _ H0).
    rewrite Nat2Z.inj_mul -{1}(Z.mul_1_l (Z.of_nat val)) -Z.mul_sub_distr_r. apply Z.mul_nonpos_nonneg.
    apply (elimT ltP) in Hgt. apply Nat2Z.inj_lt in Hgt. simpl in Hgt. intuition. apply Zle_0_nat.
Qed.

Lemma nodup_add_edge_find_eq c : forall l a adj g adj_inter g_inter b, ~ List.In a l -> fold_left
  (fun '(graph, adj_matrix) (xi : ProdVar.t) =>
  scc.add_edge graph adj_matrix xi (lhs_var1 c) c) l
  (g_inter, adj_inter) = (g, adj) -> find_adj_matrix a b adj = find_adj_matrix a b adj_inter.
Proof.
  elim. simpl; intros. inversion H0; done.
  simpl; intros. apply H with (a := a0) (b := b) in H1; clear H. rewrite /find_adj_matrix; rewrite /find_adj_matrix in H1.
  apply Decidable.not_or in H0. move : H0 => [H0 H2]. 
  case Hfind : (PVM.find a adj_inter) => [m'|]; rewrite Hfind in H1.
  - case Hfind' : (PVM.find (lhs_var1 c) m') => [cs1|]; rewrite Hfind' in H1.
    1,2 : rewrite find_add_neq in H1; try done. 1,2 : intuition.
  - rewrite find_add_neq in H1; try done. intuition.
  apply Decidable.not_or in H0. exact H0.2.
Qed.

Lemma add_edge_find_lhs_eq_eq c : forall vars g adj g' adj' a cs0, fold_left
    (fun '(graph, adj_matrix) (xi : ProdVar.t) =>
    scc.add_edge graph adj_matrix xi (lhs_var1 c) c) vars (g', adj') = (g, adj) -> NoDup vars ->
  List.In a vars -> find_adj_matrix a (lhs_var1 c) adj = Some cs0 -> 
  match find_adj_matrix a (lhs_var1 c) adj' with
  | Some cs' => cs0 = c :: cs'
  | None => cs0 = [c]
  end.
Proof.
  elim. simpl; intros; done.
  simpl; intros. destruct H2.
  - subst a0. clear H. destruct (scc.add_edge g' adj' a (lhs_var1 c) c) as [g_inter adj_inter] eqn : Hinter.
    assert (find_adj_matrix a (lhs_var1 c) adj = find_adj_matrix a (lhs_var1 c) adj_inter).
    { apply NoDup_cons_iff in H1. move : H0; apply nodup_add_edge_find_eq. exact H1.1. }
    rewrite H in H3; clear H H0 H1.
    rewrite /scc.add_edge in Hinter; inversion Hinter; clear Hinter H0. rewrite /find_adj_matrix; rewrite /find_adj_matrix in H3.
    case Hfinda : (PVM.find a adj') => [adj_a|]; rewrite Hfinda in H1.
    case Hfindlhs : (PVM.find (lhs_var1 c) adj_a) => [cs'|]; rewrite Hfindlhs in H1; subst adj_inter.
    1,2 : rewrite find_add_eq find_add_eq in H3; inversion H3; clear H0; done.
    subst adj_inter. rewrite find_add_eq find_add_eq in H3. inversion H3; done.
  - apply H with (a := a0) (cs0 := cs0) in H0; clear H; try done.
    rewrite /find_adj_matrix; rewrite /find_adj_matrix in H0. apply NoDup_cons_iff in H1. move : H1 => [H1 H1'].
    case Hfinda : (PVM.find a adj') => [adj_a|]; rewrite Hfinda in H0.
    case Hfindlhs : (PVM.find (lhs_var1 c) adj_a) => [cs'|]; rewrite Hfindlhs in H0.
    1,2,3 : rewrite find_add_neq in H0; try done.
    1,2,3 : destruct (a0 == a) eqn : Heq; move /eqP : Heq => Heq; try done. 1,2,3 : subst a. 1,2,3 : intuition.
    apply NoDup_cons_iff in H1. exact H1.2.
Qed.

Lemma add_edge_find_lhs_eq_neq c b : forall vars g adj g' adj' a, fold_left
    (fun '(graph, adj_matrix) (xi : ProdVar.t) =>
    scc.add_edge graph adj_matrix xi (lhs_var1 c) c) vars (g', adj') = (g, adj) -> 
  ~ List.In a vars -> find_adj_matrix a b adj = find_adj_matrix a b adj'.
Proof.
  elim. simpl; intros; inversion H. done.
  simpl; intros. apply Decidable.not_or in H1. move : H1 => [Hneq Hnotin].
  apply H with (a := a0) in H0; try done. clear Hnotin H. rewrite H0; clear H0.
  rewrite /find_adj_matrix.
  case Hfinda : (PVM.find a adj') => [adj_a|].
  case Hfindlhs : (PVM.find (lhs_var1 c) adj_a) => [cs'|].
  1,2,3 : rewrite find_add_neq; try done. 1,2,3 : intuition.
Qed.

Lemma add_edge_find_lhs_neq c : forall vars g adj g' adj' a b, fold_left
    (fun '(graph, adj_matrix) (xi : ProdVar.t) =>
    scc.add_edge graph adj_matrix xi (lhs_var1 c) c) vars (g', adj') = (g, adj) -> 
  b <> (lhs_var1 c) -> find_adj_matrix a b adj = find_adj_matrix a b adj'.
Proof.
  elim. simpl; intros; inversion H. done.
  simpl; intros.
  apply H with (a := a0) (b := b) in H0; try done. rewrite H0; clear H0 H.
  rewrite /find_adj_matrix.
  case Hfinda : (PVM.find a adj') => [adj_a|].
  case Hfindlhs : (PVM.find (lhs_var1 c) adj_a) => [cs'|].
  destruct (a == a0) eqn : Heqa; move /eqP : Heqa => Heqa.
  - subst a0. rewrite find_add_eq. rewrite find_add_neq; try done. rewrite Hfinda //.
  - rewrite find_add_neq //. intuition.
  destruct (a == a0) eqn : Heqa; move /eqP : Heqa => Heqa.
  - subst a0. rewrite find_add_eq. rewrite find_add_neq; try done. rewrite Hfinda //.
  - rewrite find_add_neq //. intuition.
  destruct (a == a0) eqn : Heqa; move /eqP : Heqa => Heqa.
  - subst a0. rewrite find_add_eq. rewrite find_add_neq; try done. rewrite Hfinda //.
  - rewrite find_add_neq //. intuition.
Qed.

Lemma find_adj_matrix_subset a b : forall cs cs0 g adj, (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> 
  scc.build_graph cs = (g, adj) -> find_adj_matrix a b adj = Some cs0 -> forall c : Constraint1, List.In c cs0 -> List.In c cs.
Proof. 
  elim. simpl; intros cs0 g adj Hterms; intros. inversion H; clear H. subst g adj. rewrite /find_adj_matrix find_empty_None in H0; discriminate.
  simpl; intros c_hd cs' IH cs0 g adj Hterms HBuild HFind c HIn. destruct (scc.build_graph cs') as [g' adj'].
  destruct (b == (lhs_var1 c_hd)) eqn:Heqb. destruct (in_bool a (List.split (rhs_terms1 c_hd)).2) eqn:Heqa.
  - (* eq eq *)
    apply In_in_bool in Heqa. move /eqP : Heqb => Heqb; subst b.
    apply (add_edge_find_lhs_eq_eq _ _ _ _ _ _ _ cs0 HBuild) in Heqa; try done.
    case Hfind : (find_adj_matrix a (lhs_var1 c_hd) adj') => [cs0'|]; rewrite Hfind in Heqa; subst cs0.
    simpl in HIn. destruct HIn. subst c_hd; left; done. right; move : Hfind c H; apply IH with (g := g'); try done.
    intros; apply Hterms. right; done.
    simpl in HIn. left; destruct HIn; try done. assert (good_terms (rhs_terms1 c_hd)) by (apply Hterms; left; done). rewrite /good_terms in H. exact H.2.
  - (* eq neq *) 
    apply not_true_iff_false in Heqa. assert (~ List.In a (List.split (rhs_terms1 c_hd)).2) by (move : Heqa; apply contra_not; apply In_in_bool).
    clear Heqa. move /eqP : Heqb => Heqb; subst b.
    apply (add_edge_find_lhs_eq_neq _ (lhs_var1 c_hd) _ _ _ _ _ _ HBuild) in H; try done. rewrite H in HFind.
    right; move : HFind c HIn; apply IH with (g := g'); try done. 
    intros; apply Hterms. right; done.
  - (* neq *)
    move /eqP : Heqb => Heqb.
    apply (add_edge_find_lhs_neq _ _ _ _ _ _ a _ HBuild) in Heqb; try done. rewrite Heqb in HFind.
    right; move : HFind c HIn; apply IH with (g := g'); try done.
    intros; apply Hterms. right; done.
Qed.

Lemma find_constraints_of_path_subset g adj p_hd p_tl cs cs0 : (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> 
  scc.build_graph cs = (g, adj) -> find_constraints_of_path adj p_hd p_tl = Some cs0 -> forall c, List.In c cs0 -> List.In c cs.
Proof.
  intro Hterms; intro; move : p_tl p_hd cs0. elim. simpl; intros. inversion H0; clear H0; subst cs0. try done.
  simpl; intros. case Hfind : (find_adj_matrix a p_hd adj) => [l0|]; rewrite Hfind in H1; try discriminate. case Hl0 : l0 => [|c' l0']; rewrite Hl0 in H1; try discriminate.
  case Hfindcs : (find_constraints_of_path adj a l) => [cs'|]; rewrite Hfindcs in H1; try discriminate. inversion H1; clear H1. subst cs0.
  simpl in H2. destruct H2.
  - subst c'; clear H0 Hfindcs. apply (find_adj_matrix_subset _ _ _ _ _ _ Hterms H) with (c := c) in Hfind; try done. rewrite Hl0; simpl; left; done.
  - move : Hfindcs c H1. apply H0.
Qed.

Lemma substitute_c_lhs_eq : forall (c c0 : Constraint1), lhs_var1 (substitute_c c c0) = lhs_var1 c.
Proof.
  rewrite /substitute_c; intros. apply substitute_constraint_lhs_eq.
Qed.

Lemma substitute_cs_none cs1 : substitute_cs cs1 = None -> cs1 = [].
Proof.
  destruct cs1. simpl; done. simpl; intros. case H0 : (substitute_cs cs1); rewrite H0 in H; try discriminate.
Qed.

Lemma substitute_cs_lhs_eq : forall cs c, substitute_cs cs = Some c -> exists c0, List.hd_error cs = Some c0 /\ lhs_var1 c0 = lhs_var1 c.
Proof.
  elim. simpl; intros; discriminate.
  simpl; intros. case Hsub : (substitute_cs l) => [new_c|]; rewrite Hsub in H0. inversion H0; clear H0; subst c. apply H in Hsub. destruct Hsub as [c_hd [Hhd Hlhs]].
  exists a; split; try done. rewrite /substitute_c /substitute_constraint. case Hfind : (List.find (fun p : term => p.2 == lhs_var1 new_c) (rhs_terms1 a)) => [[coe var]|]; try done.
  inversion H0; clear H0; subst a. exists c; split; try done.
Qed.

Lemma find_path_hd_eq_tgt_helper g a : forall n res0 res l b, match res0 with | Some res0' => hd_error res0' = Some a | None => true end 
  -> scc.find_path g a n l b res0 = Some res -> hd_error res = Some a.
Proof.
  elim. intros res0 res l; intros. simpl in H0. case Hres0 : res0 => [res'|]; rewrite Hres0 in H H0; try done. inversion H0. rewrite -H2; done.
  destruct (b == a) eqn:Heq; try discriminate. inversion H0; simpl; done.
  intros n IH res0 res l; intros. simpl in H0. case Hres0 : res0 => [res'|]; rewrite Hres0 in H H0; try done. inversion H0. rewrite -H2; done.
  destruct (b == a) eqn:Heq. inversion H0; simpl; done.
  destruct (PVM.find b g) as [children|] eqn:HChildren; [|discriminate].
  assert (Hhelper : forall children res0 res l, match res0 with | Some res0' => hd_error res0' = Some a | None => true end 
  -> foldl (fun (r : option (seq ProdVar.t)) (child : ProdVar.t) =>
    match r with
    | Some _ => None
    | None => scc.find_path g a n l child None
    end) res0 children = Some res -> hd_error res = Some a).
  { move : IH; clear; intro IH. elim. intros res0 res l; intros. simpl in H0. rewrite H0 in H; done.
    intros child children' IH' res0 res l; intros. simpl in H0. case Hres0 : res0 => [res0'|]; rewrite Hres0 in H H0; try done.
    - move : H0; apply IH'; done.
    - move : H0; apply IH'. case Hchild : (scc.find_path g a n l child None) => [res'|]; try done.
      move : Hchild; apply IH; done. }
  move : H0; apply Hhelper; done.
Qed.

Lemma find_path_hd_eq_tgt g n a b res : scc.find_path g a n nil b None = Some res -> List.hd_error res = Some a.
Proof.
  apply find_path_hd_eq_tgt_helper; done.
Qed.

Lemma find_adj_hd_eq a b : forall cs g adj cs0, (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> 
  scc.build_graph cs = (g, adj) -> find_adj_matrix a b adj = Some cs0 -> forall c, List.In c cs0 -> lhs_var1 c = b.
Proof.
  elim. simpl; intros g adj cs0 Hterms; intros. inversion H; subst g adj. rewrite /find_adj_matrix find_empty_None in H0; discriminate.
  intros c_hd cs' IH g adj cs0 Hterms HBuild HFind c HIn. simpl in HBuild. destruct (scc.build_graph cs') as [g' adj'].
  destruct (b == (lhs_var1 c_hd)) eqn:Heqb. destruct (in_bool a (List.split (rhs_terms1 c_hd)).2) eqn:Heqa.
  - (* eq eq *)
    apply In_in_bool in Heqa. move /eqP : Heqb => Heqb; subst b.
    apply (add_edge_find_lhs_eq_eq _ _ _ _ _ _ _ cs0 HBuild) in Heqa; try done.
    case Hfind : (find_adj_matrix a (lhs_var1 c_hd) adj') => [cs0'|]; rewrite Hfind in Heqa; subst cs0.
    simpl in HIn. destruct HIn. subst c_hd; done. move : Hfind c H; apply IH with (g := g'); try done. 
    intros; apply Hterms. right; done.
    simpl in HIn. destruct HIn; try done. subst c; done. assert (good_terms (rhs_terms1 c_hd)) by (apply Hterms; left; done). rewrite /good_terms in H. exact H.2.
  - (* eq neq *) 
    apply not_true_iff_false in Heqa. assert (~ List.In a (List.split (rhs_terms1 c_hd)).2) by (move : Heqa; apply contra_not; apply In_in_bool).
    clear Heqa. move /eqP : Heqb => Heqb; subst b.
    apply (add_edge_find_lhs_eq_neq _ (lhs_var1 c_hd) _ _ _ _ _ _ HBuild) in H; try done. rewrite H in HFind.
    move : HFind c HIn; apply IH with (g := g'); try done.
    intros; apply Hterms. right; done.
  - (* neq *)
    move /eqP : Heqb => Heqb.
    apply (add_edge_find_lhs_neq _ _ _ _ _ _ a _ HBuild) in Heqb; try done. rewrite Heqb in HFind.
    move : HFind c HIn; apply IH with (g := g'); try done.
    intros; apply Hterms. right; done.
Qed.

Lemma find_constraint_hd_eq adj x tl cs0 c_hd cs g : (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> 
  scc.build_graph cs = (g, adj) -> find_constraints_of_path adj x tl = Some cs0 -> hd_error cs0 = Some c_hd -> lhs_var1 c_hd = x.
Proof.
  intros Hterms Hbuild; move : tl x cs0 c_hd. elim. simpl; intros. inversion H; clear H; subst cs0. simpl in H0; discriminate.
  simpl; intros. case Hfind : (find_adj_matrix a x adj) => [l0|]; rewrite Hfind in H0; try discriminate.
  case Hl0 : l0 => [|l_hd l_tl]; rewrite Hl0 in H0; try discriminate. case Hfind_cs : (find_constraints_of_path adj a l) => [cs'|]; rewrite Hfind_cs in H0; try discriminate.
  inversion H0; clear H0. subst cs0. simpl in H1. inversion H1; clear H1 Hfind_cs. subst l_hd l0. specialize (find_adj_hd_eq _ _ _ _ _ _ Hterms Hbuild Hfind c_hd); intro. apply H0; simpl; left; done.
Qed.

Lemma not_empty_last_eq (A : Type) (a l : list A) :
  l <> [] -> hd_error (List.rev l ++ a) = hd_error (List.rev l).
Proof.
  move : l a; elim. simpl; intros; done.
  simpl; intros. destruct l as [|a' l'] eqn : Hl. simpl; try done.
  rewrite -Hl in H. rewrite -Hl. assert ((List.rev l ++ [a])%list ++ a0 = (List.rev l ++ [a] ++ a0)%list).
  rewrite List.app_assoc. intuition. rewrite H1; clear H1. generalize H; specialize (H ([a] ++ a0)). intros; rewrite H.
  symmetry. apply H1. 1,2 : rewrite Hl; done.
Qed.

Lemma find_constraints_of_path_nil adj p_hd p_tl : find_constraints_of_path adj p_hd p_tl = Some [] -> p_tl = [].
Proof.
  induction p_tl as [|a b IH]. done. simpl; intros. 
  case H1 : (find_adj_matrix a p_hd adj) => [l|]; rewrite H1 in H; try discriminate.
  case H2 : l => [|c l']; rewrite H2 in H; try discriminate.
  case H3 : (find_constraints_of_path adj a b) => [cs|]; rewrite H3 in H; try discriminate.
Qed.

Lemma find_path_last_eq_src_helper g a : forall n (res0 : option (list ProdVar.t)) (res l : list ProdVar.t) b, l <> nil ->
  match res0 with | Some res0' => List.hd_error (List.rev res0') = hd_error (List.rev l) | None => true end ->
  scc.find_path g a n l b res0 = Some res -> List.hd_error (List.rev res) = hd_error (List.rev l).
Proof.
  elim. simpl; intros res0 res l b Hl; intros. case Hres0 : res0 => [res0'|]; rewrite Hres0 in H H0. inversion H0; subst res; done.
  destruct (b == a) eqn:Heq; try discriminate. inversion H0. simpl. apply not_empty_last_eq; done.
  simpl; intros n IH res0 res l b Hl; intros. case Hres0 : res0 => [res0'|]; rewrite Hres0 in H H0.
  - inversion H0; subst res; done.
  - destruct (b == a) eqn:Heq. inversion H0; clear H0. simpl. apply not_empty_last_eq; done.
    destruct (PVM.find b g) as [children|] eqn:HChildren; [|discriminate].
    assert (hd_error (List.rev l) = hd_error (List.rev (b :: l))). simpl; symmetry; apply not_empty_last_eq; done.
    rewrite H1; clear H1. 
    assert (Hhelper : forall children (res0 : option (list ProdVar.t)) (res l : list ProdVar.t), l <> nil ->
      match res0 with | Some res0' => List.hd_error (List.rev res0') = hd_error (List.rev l) | None => true end ->
      foldl (fun (r : option (seq ProdVar.t)) (child : ProdVar.t) =>
        match r with
        | Some _ => None
        | None => scc.find_path g a n l child None
        end) res0 children = Some res -> hd_error (List.rev res) = hd_error (List.rev l)).
    { move : IH; clear; intro IH. elim. intros res0 res l Hl; intros. simpl in H0. rewrite H0 in H; done.
      intros child children' IH' res0 res l Hl; intros. simpl in H0. case Hres0 : res0 => [res0'|]; rewrite Hres0 in H H0.
      - move : H0; apply IH'; try done.
      - move : H0; apply IH'; try done. case Hchild : (scc.find_path g a n l child None) => [res'|]; try done.
        move : Hchild; apply IH; done. }
    move : H0; apply Hhelper; done.
Qed.

Lemma find_path_last_eq_src g n a b res : scc.find_path g a n nil b None = Some res -> List.hd_error (List.rev res) = Some b.
Proof.
  move : n. induction n as [|n' IH]. simpl; intros. destruct (b == a) eqn:Heq; try discriminate. move /eqP : Heq => Heq; subst b. inversion H; simpl; done.
  simpl; intros. destruct (b == a) eqn:Heq. inversion H. move /eqP : Heq => Heq; subst b. simpl; done.
  destruct (PVM.find b g) as [children|] eqn:HChildren; [|discriminate].
  assert (Hhelper : forall children (res0 : option (list ProdVar.t)) (res l : list ProdVar.t) n, l <> nil ->
    match res0 with | Some res0' => List.hd_error (List.rev res0') = hd_error (List.rev l) | None => true end ->
    foldl (fun (r : option (seq ProdVar.t)) (child : ProdVar.t) =>
      match r with
      | Some _ => None
      | None => scc.find_path g a n l child None
      end) res0 children = Some res -> hd_error (List.rev res) = hd_error (List.rev l)).
  { clear; elim. simpl; intros. rewrite H1 in H0; done.
    intros child children' IH' res0 res l n Hl; intros. simpl in H0. case Hres0 : res0 => [res0'|]; rewrite Hres0 in H H0.
    - move : H0; apply IH'; try done.
    - move : H0; apply IH'; try done. case Hchild : (scc.find_path g a n l child None) => [res'|]; try done.
      move : Hchild; apply find_path_last_eq_src_helper; try done. }
  apply Hhelper in H; try done.
Qed.

Lemma in_nodup_find_some a b l: List.In (a,b) l -> NoDup (List.split l).2 -> List.find (fun p : term => p.2 == b) l = Some (a,b).
Proof.
  intros HIn HNodup.
  induction l as [| (a0, b0) l IH]; simpl in *.
  - contradiction. 
  - destruct (List.split l) as [left right] eqn : Hsplitl. simpl in *.
    destruct HIn.
    + inversion H; clear H IH; subst a0 b0. rewrite eq_refl //.
    + destruct (b0 == b) eqn : Heqb. move /eqP : Heqb => Heqb; subst b0. apply NoDup_cons_iff in HNodup. move : HNodup => [HNodup _].
      apply in_split_r in H; rewrite Hsplitl in H; simpl in H. done.
      apply IH; try done. apply NoDup_cons_iff in HNodup. exact HNodup.2.
Qed.

Lemma find_adj_in_rhs a b : forall cs g adj cs0, (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> 
  scc.build_graph cs = (g, adj) -> find_adj_matrix a b adj = Some cs0 -> forall c, List.In c cs0 -> 
  exists coe, List.In (coe, a) (rhs_terms1 c).
Proof.
  elim. simpl; intros g adj cs0 Hterms; intros. inversion H; subst g adj. rewrite /find_adj_matrix find_empty_None in H0; discriminate.
  intros c_hd cs' IH g adj cs0 Hterms HBuild HFind c HIn. simpl in HBuild. destruct (scc.build_graph cs') as [g' adj'].
  destruct (b == (lhs_var1 c_hd)) eqn:Heqb. destruct (in_bool a (List.split (rhs_terms1 c_hd)).2) eqn:Heqa.
  - (* eq eq *)
    apply In_in_bool in Heqa. move /eqP : Heqb => Heqb; subst b.
    generalize Heqa; apply (add_edge_find_lhs_eq_eq _ _ _ _ _ _ _ cs0 HBuild) in Heqa; try done. intros.
    case Hfind : (find_adj_matrix a (lhs_var1 c_hd) adj') => [cs0'|]; rewrite Hfind in Heqa; subst cs0.
    simpl in HIn. destruct HIn. subst c_hd. 
      apply in_split_r_exists_in in Heqa0. destruct Heqa0 as [coe Heqa0]. apply in_nodup_find_some in Heqa0. apply find_some in Heqa0. exists coe; exact Heqa0.1.
    intros; apply Hterms. simpl; left; done.
    move : Hfind c H; apply IH with (g := g'); try done. intros; apply Hterms. right; done.
    simpl in HIn. destruct HIn; try done. subst c.
      apply in_split_r_exists_in in Heqa0. destruct Heqa0 as [coe Heqa0]. apply in_nodup_find_some in Heqa0. apply find_some in Heqa0. exists coe; exact Heqa0.1.
    1,2 : assert (good_terms (rhs_terms1 c_hd)) by (apply Hterms; left; done). 1,2 : rewrite /good_terms in H. 1,2 : exact H.2.
  - (* eq neq *) 
    apply not_true_iff_false in Heqa. assert (~ List.In a (List.split (rhs_terms1 c_hd)).2) by (move : Heqa; apply contra_not; apply In_in_bool).
    clear Heqa. move /eqP : Heqb => Heqb; subst b.
    apply (add_edge_find_lhs_eq_neq _ (lhs_var1 c_hd) _ _ _ _ _ _ HBuild) in H; try done. rewrite H in HFind.
    move : HFind c HIn; apply IH with (g := g'); try done.
    intros; apply Hterms. right; done.
  - (* neq *)
    move /eqP : Heqb => Heqb.
    apply (add_edge_find_lhs_neq _ _ _ _ _ _ a _ HBuild) in Heqb; try done. rewrite Heqb in HFind.
    move : HFind c HIn; apply IH with (g := g'); try done.
    intros; apply Hterms. right; done.
Qed.

Lemma find_constraints_of_path_correctness constraints g adj p_hd p_tl cs : (forall c, List.In c constraints -> good_terms (rhs_terms1 c)) -> 
  scc.build_graph constraints = (g, adj) -> 
  find_constraints_of_path adj p_hd p_tl = Some cs ->
  (forall c0 c1, (exists pre suf, pre ++ c0 :: c1 :: suf = cs) -> exists coe, List.In (coe, lhs_var1 c1) (rhs_terms1 c0)).
Proof.
  intros Hterms HBuild; move : p_tl p_hd cs. elim. simpl; intros. inversion H; subst cs. destruct H0 as [pre [suf H2]]. 
    apply app_eq_nil in H2. move : H2 => [_ H2]. discriminate.
  simpl; intros p_hd' p_tl' IH; intros. 
  destruct (find_adj_matrix p_hd' p_hd adj) as [l|] eqn:Hfind0; [|discriminate].
  destruct l as [|c c_tl] eqn:Hl; [discriminate|].
  destruct (find_constraints_of_path adj p_hd' p_tl') as [cs'|] eqn:Hfind; [|discriminate].
  inversion H; clear H; subst cs. destruct H0 as [pre [suf H0]].
  destruct (pre == []) eqn : Hc0.
  - move /eqP : Hc0 => Hc0; subst pre. simpl in H0. inversion H0; clear H0. subst c cs'.
    clear IH. specialize (find_constraint_hd_eq _ _ _ _ c1 _ _ Hterms HBuild Hfind); intro. rewrite H; simpl; try done.
    specialize (find_adj_in_rhs _ _ _ _ _ _ Hterms HBuild Hfind0 c0); intro. apply H0. simpl; left; done.
  - assert (exists pre', pre = c :: pre').
    { induction pre as [|a b]; try done. inversion H0. subst c cs'. exists b; done. }
    clear Hc0; destruct H as [pre' Hpre]; subst pre. inversion H0; clear H0.
    assert (exists pre' suf, pre' ++ [:: c0, c1 & suf] = cs') by (exists pre'; exists suf; try done).
    clear H1. move : Hfind c0 c1 H; apply IH.
Qed.

Lemma find_path_1 g var n x a : scc.find_path g var n [] x None = Some [a] -> var = x.
Proof.
  intros. generalize H. apply find_path_hd_eq_tgt in H. intros. apply find_path_last_eq_src in H0.
  simpl in H; simpl in H0. inversion H; inversion H0. subst a; done.
Qed.

Lemma solution_in_bd_case1 v cs c coe var x g adj n ub : (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs -> rhs_power c = nil) ->
  scc.build_graph cs = (g, adj) ->
  forallb (satisfies_constraint1 v) cs ->
  List.find (fun c : Constraint1 => List.existsb (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) cs = Some c ->
  List.find (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c) = Some (coe, var) ->
  solve_ub_case1 x c var g adj n = Some ub ->
  exists n0 : nat, PVM.find x v = Some n0 /\ n0 <= ub.
Proof.
  intros Hterm Hpower Hbuild; intros. rewrite /solve_ub_case1 in H2.
  assert (H' : forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done).
  case Hp0 : (scc.find_path g x n [] (lhs_var1 c) None) => [l|]; rewrite Hp0 in H2; try discriminate.
  case Hl : l => [|p0_hd p0_tl]; rewrite Hl in H2; try discriminate. rewrite Hl in Hp0; clear Hl l. 
  case Hp1 : (scc.find_path g var n [] x None) => [l|]; rewrite Hp1 in H2; try discriminate.
  case Hl : l => [|p1_hd p1_tl]; rewrite Hl in H2; try discriminate. rewrite Hl in Hp1; clear Hl l. 
  case Hcs0 : (find_constraints_of_path adj p0_hd p0_tl) => [cs0|]; rewrite Hcs0 in H2; try discriminate.
  case Hcs1 : (find_constraints_of_path adj p1_hd p1_tl) => [cs1|]; rewrite Hcs1 in H2; try discriminate.
  specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs0) as Hfind_cs_in0.
  specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs1) as Hfind_cs_in1.
  case Hsub0 : (substitute_cs cs0) => [c0|]; rewrite Hsub0 in H2.
  case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in H2.
  (* case1 *)
  - assert (x = (lhs_var1 (substitute_c c0 (substitute_c c c1)))). 
  { rewrite substitute_c_lhs_eq. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
    apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 Hlhs0]]. rewrite -Hlhs0. symmetry. move : Hbuild Hcs0 Hhd0; apply find_constraint_hd_eq; try done. }
    rewrite H3. apply compute_ub_correctness; try done.
    apply substitute_c_correctness. move : Hsub0; apply substitute_cs_correctness. 
    intros; apply Hterm. 2: intros; apply Hpower. 1,2 : apply Hfind_cs_in0; done. apply forallb_forall.
    intros; apply H'. apply Hfind_cs_in0;done.
    apply substitute_c_correctness. apply H'. apply find_some in H0. exact H0.1.
    move : Hsub1; apply substitute_cs_correctness.
    intros; apply Hterm. 2: intros; apply Hpower. 1,2 : apply Hfind_cs_in1; done. apply forallb_forall.
    intros; apply H'. apply Hfind_cs_in1;done. apply Hpower. 3 : apply Hterm. 1,3 : apply find_some in H0; exact H0.1.
    move : Hsub1; apply substitute_cs_power. intros; apply Hpower. 
    2: move : Hsub1; apply substitute_cs_good_term. 2 : intros; apply Hterm. 1,2 : apply Hfind_cs_in1; done. 
    move : Hsub0; apply substitute_cs_power. intros; apply Hpower. apply Hfind_cs_in0; done. 
    apply substitute_c_power. apply Hpower. apply find_some in H0. exact H0.1.
    move : Hsub1; apply substitute_cs_power. intros; apply Hpower. apply Hfind_cs_in1; done.
    move : Hsub0; apply substitute_cs_good_term. intros; apply Hterm. apply Hfind_cs_in0; done.
    apply substitute_c_good_term. apply Hterm. apply find_some in H0. exact H0.1.
    move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm. apply Hfind_cs_in1; done.
  (* case2 *)
  - assert (x = (lhs_var1 (substitute_c c0 c))).
  { rewrite substitute_c_lhs_eq. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
    apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 Hlhs0]]. rewrite -Hlhs0. symmetry. move : Hbuild Hcs0 Hhd0; apply find_constraint_hd_eq; try done. }
    rewrite H3. apply compute_ub_correctness; try done.
    apply substitute_c_correctness. move : Hsub0; apply substitute_cs_correctness. 
    intros; apply Hterm. 2: intros; apply Hpower. 1,2 : apply Hfind_cs_in0; done. apply forallb_forall.
    intros; apply H'. apply Hfind_cs_in0;done.
    apply H'. apply find_some in H0. exact H0.1.
    move : Hsub0; apply substitute_cs_power. intros; apply Hpower. apply Hfind_cs_in0; done. 
    apply Hpower. apply find_some in H0. exact H0.1.
    move : Hsub0; apply substitute_cs_good_term. intros; apply Hterm. apply Hfind_cs_in0; done.
    apply Hterm. apply find_some in H0. exact H0.1.
  case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in H2.
  (* case3 *)
  - assert (x = (lhs_var1 (substitute_c c c1))).
  { rewrite substitute_c_lhs_eq. apply substitute_cs_none in Hsub0. subst cs0. apply find_constraints_of_path_nil in Hcs0. subst p0_tl. apply find_path_1 in Hp0; done. }
    rewrite H3. apply compute_ub_correctness; try done.
    apply substitute_c_correctness. apply H'. apply find_some in H0. exact H0.1. move : Hsub1; apply substitute_cs_correctness. 
    intros; apply Hterm. 2: intros; apply Hpower. 1,2 : apply Hfind_cs_in1; done. apply forallb_forall.
    intros; apply H'. apply Hfind_cs_in1; done. apply Hpower. apply find_some in H0. exact H0.1.
    move : Hsub1; apply substitute_cs_power. intros; apply Hpower. apply Hfind_cs_in1; done.
    apply Hterm. apply find_some in H0. exact H0.1.  move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm. apply Hfind_cs_in1; done. 
  (* case4 *)
  - assert (x = (lhs_var1 c)).
  { apply substitute_cs_none in Hsub0. subst cs0. apply find_constraints_of_path_nil in Hcs0. subst p0_tl. apply find_path_1 in Hp0; done. }
    rewrite H3. apply compute_ub_correctness; try done. apply H'.
    apply find_some in H0. exact H0.1.
Qed.

Lemma solution_in_bd_case2 v cs c coe0 coe1 var0 var1 tl' x g adj n ub : 
  (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs -> rhs_power c = nil) ->
  scc.build_graph cs = (g, adj) ->
  forallb (satisfies_constraint1 v) cs ->
  List.find (fun c : Constraint1 => 1 < Datatypes.length (rhs_terms1 c)) cs = Some c ->
  rhs_terms1 c = [:: (coe0, var0), (coe1, var1) & tl'] ->
  solve_ub_case2 x c var0 var1 g adj n = Some ub ->
  exists n0 : nat, PVM.find x v = Some n0 /\ n0 <= ub.
Proof.
  intros Hterm Hpower Hbuild; intros. rewrite /solve_ub_case2 in H2.
  assert (H' : forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done).
  case Hp0 : (scc.find_path g x n [] (lhs_var1 c) None) => [l0|]; rewrite Hp0 in H2; try discriminate.
  case Hl0 : l0 => [|p0_hd p0_tl]; rewrite Hl0 in H2; try discriminate. rewrite Hl0 in Hp0; clear Hl0 l0. 
  case Hp1 : (scc.find_path g var0 n [] x None) => [l1|]; rewrite Hp1 in H2; try discriminate.
  case Hl1 : l1 => [|p1_hd p1_tl]; rewrite Hl1 in H2; try discriminate. rewrite Hl1 in Hp1; clear Hl1 l1. 
  case Hp2 : (scc.find_path g var1 n [] x None) => [l2|]; rewrite Hp2 in H2; try discriminate.
  case Hl2 : l2 => [|p2_hd p2_tl]; rewrite Hl2 in H2; try discriminate. rewrite Hl2 in Hp2; clear Hl2 l2. 
  case Hcs0 : (find_constraints_of_path adj p0_hd p0_tl) => [cs0|]; rewrite Hcs0 in H2; try discriminate.
  case Hcs1 : (find_constraints_of_path adj p1_hd p1_tl) => [cs1|]; rewrite Hcs1 in H2; try discriminate.
  case Hcs2 : (find_constraints_of_path adj p2_hd p2_tl) => [cs2|]; rewrite Hcs2 in H2; try discriminate.
  specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs0) as Hfind_cs_in0.
  specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs1) as Hfind_cs_in1.
  specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs2) as Hfind_cs_in2.
  case Hsub0 : (substitute_cs cs0) => [c0|]; rewrite Hsub0 in H2.
  case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in H2.
  case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in H2.
  (* case1 *)
  - assert (x = (lhs_var1 (substitute_c c0 (substitute_c (substitute_c c c1) c2)))). 
  { rewrite substitute_c_lhs_eq. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
    apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 Hlhs0]]. rewrite -Hlhs0. symmetry. move : Hbuild Hcs0 Hhd0; apply find_constraint_hd_eq; try done. }
    rewrite H3. apply compute_ub_correctness; try done.
    apply substitute_c_correctness. move : Hsub0; apply substitute_cs_correctness. 
    intros; apply Hterm. 2: intros; apply Hpower. 1,2 : apply Hfind_cs_in0; done. apply forallb_forall.
    intros; apply H'. apply Hfind_cs_in0;done.
    apply substitute_c_correctness. apply substitute_c_correctness. apply H'. apply find_some in H0. exact H0.1.
    move : Hsub1; apply substitute_cs_correctness.
    intros; apply Hterm. 2: intros; apply Hpower. 1,2 : apply Hfind_cs_in1; done. apply forallb_forall.
    intros; apply H'. apply Hfind_cs_in1;done. apply Hpower. 3 : apply Hterm. 1,3 : apply find_some in H0; exact H0.1.
    move : Hsub1; apply substitute_cs_power. intros; apply Hpower. 
    2: move : Hsub1; apply substitute_cs_good_term. 2 : intros; apply Hterm. 1,2 : apply Hfind_cs_in1; done. 
    move : Hsub2; apply substitute_cs_correctness.
    intros; apply Hterm. 2: intros; apply Hpower. 1,2 : apply Hfind_cs_in2; done. apply forallb_forall.
    intros; apply H'. apply Hfind_cs_in2;done. apply substitute_c_power.
    2 : move : Hsub1; apply substitute_cs_power. 3 : move : Hsub2; apply substitute_cs_power.
    2,3 : intros. 1,2,3 : apply Hpower. apply find_some in H0; exact H0.1.
    apply Hfind_cs_in1; done. apply Hfind_cs_in2; done.
    apply substitute_c_good_term.
    2 : move : Hsub1; apply substitute_cs_good_term. 3 : move : Hsub2; apply substitute_cs_good_term.
    2,3 : intros. 1,2,3 : apply Hterm. apply find_some in H0; exact H0.1.
    apply Hfind_cs_in1; done. apply Hfind_cs_in2; done.
    move : Hsub0; apply substitute_cs_power. intros; apply Hpower. apply Hfind_cs_in0; done.
    apply substitute_c_power. apply substitute_c_power.
    2 : move : Hsub1; apply substitute_cs_power. 3 : move : Hsub2; apply substitute_cs_power.
    2,3 : intros. 1,2,3 : apply Hpower. apply find_some in H0; exact H0.1.
    apply Hfind_cs_in1; done. apply Hfind_cs_in2; done.
    move : Hsub0; apply substitute_cs_good_term. intros; apply Hterm. apply Hfind_cs_in0; done.
    apply substitute_c_good_term. apply substitute_c_good_term.
    2 : move : Hsub1; apply substitute_cs_good_term. 3 : move : Hsub2; apply substitute_cs_good_term.
    2,3 : intros. 1,2,3 : apply Hterm. apply find_some in H0; exact H0.1.
    apply Hfind_cs_in1; done. apply Hfind_cs_in2; done.
  (* case2 *)
  - assert (x = (lhs_var1 (substitute_c c0 (substitute_c c c1)))).
  { rewrite substitute_c_lhs_eq. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
    apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 Hlhs0]]. rewrite -Hlhs0. symmetry. move : Hbuild Hcs0 Hhd0; apply find_constraint_hd_eq; try done. }
    rewrite H3. apply compute_ub_correctness; try done.
    apply substitute_c_correctness. move : Hsub0; apply substitute_cs_correctness. 
    intros; apply Hterm. 2: intros; apply Hpower. 1,2 : apply Hfind_cs_in0; done. apply forallb_forall.
    intros; apply H'. apply Hfind_cs_in0;done.
    apply substitute_c_correctness. apply H'. apply find_some in H0. exact H0.1.
    move : Hsub1; apply substitute_cs_correctness.
    intros; apply Hterm. 2: intros; apply Hpower. 3 : apply forallb_forall; intros; apply H'. 1,2,3 : apply Hfind_cs_in1; done.
    apply Hpower. 3: apply Hterm. 1,3 : apply find_some in H0; exact H0.1.
    1,2 : move : Hsub1. apply substitute_cs_power; intros; apply Hpower. 2 : apply substitute_cs_good_term; intros; apply Hterm. 1,2 : apply Hfind_cs_in1; done.
    1,3 : move : Hsub0. apply substitute_cs_power; intros; apply Hpower. 2 : apply substitute_cs_good_term; intros; apply Hterm. 1,2 : apply Hfind_cs_in0; done.
    apply substitute_c_power. 3 : apply substitute_c_good_term. apply Hpower. 3 : apply Hterm. 1,3 : apply find_some in H0; exact H0.1.
    1,2 : move : Hsub1. apply substitute_cs_power; intros; apply Hpower. 2 : apply substitute_cs_good_term; intros; apply Hterm. 1,2 : apply Hfind_cs_in1; done.
  case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in H2.
  (* case3 *)
  - assert (x = (lhs_var1 (substitute_c c0 (substitute_c c c2)))).
  { rewrite substitute_c_lhs_eq. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
    apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 Hlhs0]]. rewrite -Hlhs0. symmetry. move : Hbuild Hcs0 Hhd0; apply find_constraint_hd_eq; try done. }
    rewrite H3. apply compute_ub_correctness; try done.
    apply substitute_c_correctness.
    1,3 : move : Hsub0. apply substitute_cs_correctness; intros. apply Hterm. 2: apply Hpower. 1,2 : apply Hfind_cs_in0; done.
    apply forallb_forall. intros; apply H'. apply Hfind_cs_in0;done.
    apply substitute_cs_power. 4 : move : Hsub0; apply substitute_cs_good_term. intros; apply Hpower. 4 : intros; apply Hterm. 1,4 : apply Hfind_cs_in0; done.
    apply substitute_c_correctness. 7 : apply substitute_c_power. 9 : apply substitute_c_good_term.
    apply H'. 3,7:apply Hpower. 6:apply Hterm. 9:apply Hterm. 1,3,4,6,9: apply find_some in H0; exact H0.1.
    move : Hsub2; apply substitute_cs_correctness.
    intros; apply Hterm. 2: intros; apply Hpower. 3 : apply forallb_forall; intros; apply H'. 1,2,3 : apply Hfind_cs_in2; done.
    1,2,3,4 : move : Hsub2. 1,3:apply substitute_cs_power; intros; apply Hpower. 3,4 : apply substitute_cs_good_term; intros; apply Hterm. 1,2,3,4 : apply Hfind_cs_in2; done.
  (* case4 *)
  - assert (x = (lhs_var1 (substitute_c c0 c))).
  { rewrite substitute_c_lhs_eq. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
    apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 Hlhs0]]. rewrite -Hlhs0. symmetry. move : Hbuild Hcs0 Hhd0; apply find_constraint_hd_eq; try done. }
    rewrite H3. apply compute_ub_correctness; try done.
    apply substitute_c_correctness.
    1,3 : move : Hsub0. apply substitute_cs_correctness; intros. apply Hterm. 2: apply Hpower. 1,2 : apply Hfind_cs_in0; done.
    apply forallb_forall. intros; apply H'. apply Hfind_cs_in0;done.
    apply substitute_cs_power. 4 : move : Hsub0; apply substitute_cs_good_term. intros; apply Hpower. 4 : intros; apply Hterm. 1,4 : apply Hfind_cs_in0; done.
    apply H'. 2 : apply Hpower. 3 : apply Hterm. 1,2,3 : apply find_some in H0; exact H0.1.
  case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in H2.
  case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in H2.
  (* case5 *)
  - assert (x = (lhs_var1 (substitute_c (substitute_c c c1) c2))). 
  { rewrite substitute_c_lhs_eq. rewrite substitute_c_lhs_eq. apply substitute_cs_none in Hsub0. subst cs0. apply find_constraints_of_path_nil in Hcs0. subst p0_tl. apply find_path_1 in Hp0; done. }
    rewrite H3. apply compute_ub_correctness; try done.
    apply substitute_c_correctness. 
    apply substitute_c_correctness. 8 : apply substitute_c_power. 11 : apply substitute_c_good_term.
    apply H'. 3,8: apply Hpower. 6,11: apply Hterm. 1,3,4,6,7: apply find_some in H0; exact H0.1.
    1,2,3,5,7 : move : Hsub1. 6,7,8 : move : Hsub2. 1,6: apply substitute_cs_correctness.
    7,9,11 : apply substitute_cs_power. 10,11,12 : apply substitute_cs_good_term. 3,6 : apply forallb_forall.
    1-12 : intros; try apply Hterm; try apply H'; try apply Hpower. 1-12 : try (apply Hfind_cs_in1; done); try (apply Hfind_cs_in2; done).
  (* case2 *)
  - assert (x = (lhs_var1 (substitute_c c c1))).
  { rewrite substitute_c_lhs_eq. apply substitute_cs_none in Hsub0. subst cs0. apply find_constraints_of_path_nil in Hcs0. subst p0_tl. apply find_path_1 in Hp0; done. }
    rewrite H3. apply compute_ub_correctness; try done.
    apply substitute_c_correctness. apply H'. 3 : apply Hpower. 5 : apply Hterm. 1,3,5 : apply find_some in H0; exact H0.1.
    1,2,3 : move : Hsub1. apply substitute_cs_correctness. 4 : apply substitute_cs_power. 5 : apply substitute_cs_good_term.
    3 : apply forallb_forall. 1-5 : intros. 1,5 : apply Hterm. 3,5 : apply Hpower. 5 : apply H'.
    1-5 : apply Hfind_cs_in1; done.
  case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in H2.
  (* case3 *)
  - assert (x = (lhs_var1 (substitute_c c c2))).
  { rewrite substitute_c_lhs_eq. apply substitute_cs_none in Hsub0. subst cs0. apply find_constraints_of_path_nil in Hcs0. subst p0_tl. apply find_path_1 in Hp0; done. }
    rewrite H3. apply compute_ub_correctness; try done.
    apply substitute_c_correctness. apply H'. 3 : apply Hpower. 5 : apply Hterm. 1,3,5 : apply find_some in H0; exact H0.1.
    1,2,3 : move : Hsub2. apply substitute_cs_correctness. 4 : apply substitute_cs_power. 5 : apply substitute_cs_good_term.
    3 : apply forallb_forall. 1-5 : intros. 1,5 : apply Hterm. 3,5 : apply Hpower. 5 : apply H'.
    1-5 : apply Hfind_cs_in2; done.
  (* case4 *)
  - assert (x = (lhs_var1 c)).
  { apply substitute_cs_none in Hsub0. subst cs0. apply find_constraints_of_path_nil in Hcs0. subst p0_tl. apply find_path_1 in Hp0; done. }
    rewrite H3. apply compute_ub_correctness; try done. apply H'.
    apply find_some in H0. exact H0.1.
Qed.

Lemma find_mergeBounds_add_bs_eq x : forall l v0 v, PVM.find x v0 = PVM.find x v -> PVM.find x (add_bs l v0) = PVM.find x (add_bs l v).
Proof.
  elim. simpl; intros; done.
  simpl; intros [a0 a1]; intros. apply H. destruct (x == a0) eqn : Heq; move /eqP : Heq => Heq.
  subst a0. rewrite find_add_eq. rewrite find_add_eq //.
  rewrite find_add_neq; try done. rewrite find_add_neq; try done.
Qed.

Lemma find_mergeBounds_add_bs_not_in x : forall l v, ~ List.In x (List.split l).1 -> PVM.find x (add_bs l v) = PVM.find x v.
Proof.
  elim. simpl; intros; done.
  simpl; intros [a0 a1]; intros. rewrite H. rewrite find_add_neq //.
  1,2 : destruct (List.split l) as [left right] eqn : Hsplit; simpl in H0; apply Decidable.not_or in H0;
  move : H0 => [H0 H1]. intuition. simpl; done. 
Qed.

Lemma add_bs_app : forall l0 l1 v, add_bs (l0 ++ l1) v = add_bs l1 (add_bs l0 v).
Proof.
  elim. simpl; intros; done.
  simpl; intros [a0 a1]; intros. rewrite H //.
Qed.

Lemma solution_in_bds_case1 v cs1 c coe var tbsolved g adj n ubs : NoDup tbsolved -> (forall c, List.In c cs1 -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs1 -> rhs_power c = nil) ->
  scc.build_graph cs1 = (g, adj) ->
  forallb (satisfies_constraint1 v) cs1 ->
  List.find (fun c : Constraint1 => List.existsb (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) cs1 = Some c ->
  List.find (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c) = Some (coe, var) ->
  solve_ubs_case1 tbsolved c var g adj n initial_valuation = Some ubs -> 
  In v (mergeBounds ubs).
Proof.
  intros HNodup Hterm Hpower Hbuild; intros.
  assert (Hhelper : forall (tbsolved : seq ProdVar.t) (ubs initial : Valuation), In v (mergeBounds initial) ->
    (forall var, List.In var tbsolved -> ~PVM.mem var initial) -> NoDup tbsolved ->
    solve_ubs_case1 tbsolved c var g adj n initial = Some ubs -> In v (mergeBounds ubs)).
  { elim. simpl; intros ubs0 initial HIn Hinit Hnodup Hsolve. inversion Hsolve. rewrite -H4 //.
    simpl; intros hd tl IH ubs0 initial HIn Hinit Hnodup Hsolve. case Hsolve_hd : (solve_ub_case1 hd c var g adj n) => [ub|]; rewrite Hsolve_hd in Hsolve; try discriminate.
    move : Hsolve; apply IH. rewrite /In; intros. destruct (x == hd) eqn : Heq; move /eqP : Heq => Heq.
    - subst hd. specialize (solution_in_bd_case1 _ _ _ _ _ _ _ _ _ _ Hterm Hpower Hbuild H H0 H1 Hsolve_hd); intros.
      assert (forall v ub, PVM.find x v = Some ub -> PVM.find x (mergeBounds v) = Some (0,ub)).
      { clear; rewrite /mergeBounds; intros. specialize (key_NoDup _ v); intro Hnodup0. 
        remember (PVM.elements v) as l. apply find_in_elements in H. rewrite -Heql in H.
        clear Heql. remember (PVM.empty (nat * nat)) as v0; clear Heqv0. move : l v0 Hnodup0 H. elim. simpl; done.
        intros [a0 a1]; intros. simpl in H0; destruct H0.
        + inversion H0; clear H0 H. subst a0 a1. simpl. rewrite find_mergeBounds_add_bs_not_in. 
          apply find_add_eq. destruct (List.split l) as [left right] eqn : Hsplit. simpl in Hnodup0; rewrite Hsplit in Hnodup0; simpl in Hnodup0.
          apply NoDup_cons_iff in Hnodup0. simpl; exact Hnodup0.1.
        + apply H; try done. destruct (List.split l) as [left right] eqn : Hsplit. simpl in Hnodup0; rewrite Hsplit in Hnodup0; simpl in Hnodup0.
          apply NoDup_cons_iff in Hnodup0. simpl; exact Hnodup0.2. }
      destruct H4 as [n0 [H4 H4']]. exists n0; split; try done. specialize (H5 (PVM.add x ub initial) ub). rewrite H5 in H3. clear H5.
      inversion H3; clear H3; subst lb ub0. split; try done. apply find_add_eq.
    - assert (PVM.find x (mergeBounds (PVM.add hd ub initial)) = PVM.find x (mergeBounds initial)).
      { move : H3 Heq Hinit; clear; intros; rewrite /mergeBounds. specialize (PVM.elements_3w initial); intro Hnodup0. 
        specialize (elements_add' initial hd ub); intro. destruct H as [l0 [l1 [H0 H1]]]. apply mem_find_none. apply Hinit; left; done.
        rewrite -H0 -H1. rewrite -H0 in Hnodup0. apply NoDupA_NoDup in Hnodup0.
        rewrite add_bs_app. rewrite add_bs_app. simpl.
        apply find_mergeBounds_add_bs_eq. rewrite find_add_neq; try done. }
      rewrite H4 in H3; clear Heq H4. move : x lb ub0 H3. rewrite /In in HIn; done. 
      intros. intro. apply mem_add_or in H4. destruct H4. move : H4; apply Hinit; right; done. move /eqP : H4 => H4; subst hd. apply NoDup_cons_iff in Hnodup; move : Hnodup => [Hnotin _]; done.
      apply NoDup_cons_iff in Hnodup; exact Hnodup.2.
  }
  move : H2; apply Hhelper; try done.
Qed.

Lemma solution_in_bds_case2 v cs1 c coe0 var0 coe1 var1 tl' tbsolved g adj n ubs : NoDup tbsolved -> (forall c, List.In c cs1 -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs1 -> rhs_power c = nil) ->
  scc.build_graph cs1 = (g, adj) ->
  forallb (satisfies_constraint1 v) cs1 ->
  List.find (fun c : Constraint1 => 1 < Datatypes.length (rhs_terms1 c)) cs1 = Some c ->
  rhs_terms1 c = [:: (coe0, var0), (coe1, var1) & tl'] ->
  solve_ubs_case2 tbsolved c var0 var1 g adj n initial_valuation = Some ubs -> 
  In v (mergeBounds ubs).
Proof.
  intros HNodup Hterm Hpower Hbuild; intros.
  assert (Hhelper : forall (tbsolved : seq ProdVar.t) (ubs initial : Valuation), In v (mergeBounds initial) ->
    (forall var, List.In var tbsolved -> ~PVM.mem var initial) -> NoDup tbsolved ->
    solve_ubs_case2 tbsolved c var0 var1 g adj n initial = Some ubs -> In v (mergeBounds ubs)).
  { elim. simpl; intros ubs0 initial HIn Hinit Hnodup Hsolve. inversion Hsolve. rewrite -H4 //.
    simpl; intros hd tl IH ubs0 initial HIn Hinit Hnodup Hsolve. case Hsolve_hd : (solve_ub_case2 hd c var0 var1 g adj n) => [ub|]; rewrite Hsolve_hd in Hsolve; try discriminate.
    move : Hsolve; apply IH. rewrite /In; intros. destruct (x == hd) eqn : Heq; move /eqP : Heq => Heq.
    - subst hd. specialize (solution_in_bd_case2 _ _ _ _ _ _ _ _ _ _ _ _ _ Hterm Hpower Hbuild H H0 H1 Hsolve_hd); intros. 
      assert (forall v ub, PVM.find x v = Some ub -> PVM.find x (mergeBounds v) = Some (0,ub)).
      { clear; rewrite /mergeBounds; intros. specialize (key_NoDup _ v); intro Hnodup0. 
        remember (PVM.elements v) as l. apply find_in_elements in H. rewrite -Heql in H.
        clear Heql. remember (PVM.empty (nat * nat)) as v0; clear Heqv0. move : l v0 Hnodup0 H. elim. simpl; done.
        intros [a0 a1]; intros. simpl in H0; destruct H0.
        + inversion H0; clear H0 H. subst a0 a1. simpl. rewrite find_mergeBounds_add_bs_not_in. 
          apply find_add_eq. destruct (List.split l) as [left right] eqn : Hsplit. simpl in Hnodup0; rewrite Hsplit in Hnodup0; simpl in Hnodup0.
          apply NoDup_cons_iff in Hnodup0. simpl; exact Hnodup0.1.
        + apply H; try done. destruct (List.split l) as [left right] eqn : Hsplit. simpl in Hnodup0; rewrite Hsplit in Hnodup0; simpl in Hnodup0.
          apply NoDup_cons_iff in Hnodup0. simpl; exact Hnodup0.2. }
      destruct H4 as [n0 [H4 H4']]. exists n0; split; try done. specialize (H5 (PVM.add x ub initial) ub). rewrite H5 in H3. clear H5.
      inversion H3; clear H3; subst lb ub0. split; try done. apply find_add_eq.
    - assert (PVM.find x (mergeBounds (PVM.add hd ub initial)) = PVM.find x (mergeBounds initial)).
      { move : H3 Heq Hinit; clear; intros; rewrite /mergeBounds. specialize (PVM.elements_3w initial); intro Hnodup0. 
        specialize (elements_add' initial hd ub); intro. destruct H as [l0 [l1 [H0 H1]]]. apply mem_find_none. apply Hinit; left; done.
        rewrite -H0 -H1. rewrite -H0 in Hnodup0. apply NoDupA_NoDup in Hnodup0.
        rewrite add_bs_app. rewrite add_bs_app. simpl.
        apply find_mergeBounds_add_bs_eq. rewrite find_add_neq; try done. }
      rewrite H4 in H3; clear Heq H4. move : x lb ub0 H3. rewrite /In in HIn; done.
      intros. intro. apply mem_add_or in H4. destruct H4. move : H4; apply Hinit; right; done. move /eqP : H4 => H4; subst hd. apply NoDup_cons_iff in Hnodup; move : Hnodup => [Hnotin _]; done.
      apply NoDup_cons_iff in Hnodup; exact Hnodup.2.
  }
  move : H2; apply Hhelper; try done.
Qed.

Lemma solution_in_bds cs1 v tbsolved ubs : NoDup tbsolved -> (forall c, List.In c cs1 -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs1 -> rhs_power c = nil) ->
  solve_ubs_aux tbsolved cs1 = Some ubs -> forallb (satisfies_constraint1 v) cs1 -> 
  In v (mergeBounds ubs).
Proof.
  intros Hnodup Hterm Hpower.
  rewrite /solve_ubs_aux. destruct (scc.build_graph cs1) as [g adj] eqn : Hgraph.
  case Hcase1 : (List.find (fun c : Constraint1 => List.existsb (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) cs1) => [c|].
  - (* lhs >= coe * var + ... + cst c, coe > 1 *)
    intros. case Hfind_terms : (List.find (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) => [[coe var]|]; rewrite Hfind_terms in H; try discriminate.
    move : H0 Hcase1 Hfind_terms H; apply solution_in_bds_case1; try done.
  case Hcase2 : (List.find (fun c : Constraint1 => 1 < Datatypes.length (rhs_terms1 c)) cs1) => [c|].
  - (* lhs >= coe0 * var0 + coe1 * var1 + ... + cst c *)
    intros. case Hterms_hd : (rhs_terms1 c) => [|[coe0 var0] tl]; rewrite Hterms_hd in H; try discriminate.
    case Hterms_hd' : tl => [|[coe1 var1] tl']; rewrite Hterms_hd' in H; try discriminate. rewrite Hterms_hd' in Hterms_hd; clear Hterms_hd' tl.
    move : H0 Hcase2 Hterms_hd H; apply solution_in_bds_case2; try done. 
  intros; discriminate.
Qed.

Lemma no_compute_ub_unsat c : (exists coe, List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c) = Some (coe, lhs_var1 c) /\ coe > 1) -> 
  compute_ub c = None -> forall v, ~ satisfies_constraint1 v c.
Proof.
  rewrite /compute_ub; intros Hcoe Hub. destruct Hcoe as [coe [Hfind Hgt]].
  rewrite Hfind in Hub. rewrite Hgt in Hub; try discriminate.
Qed.

Lemma find_cons_neq var : forall (terms : list term) var' coe, var <> var' -> List.find (fun p : term => p.2 == var) terms = List.find (fun p : term => p.2 == var) ((coe,var') :: terms).
Proof.
  elim. simpl; intros. destruct (var' == var) eqn : Heq; try done; move /eqP : Heq => Heq. rewrite Heq in H; done. 
  simpl; intros [coe_hd var_hd] tl; intros; simpl. assert ((var' == var) = false) by (destruct (var' == var) eqn : Heq; try done; move /eqP : Heq => Heq; rewrite Heq in H0; done).
  rewrite H1; clear H1. destruct (var_hd == var); try done. 
Qed.

Lemma find_remove_neq var : forall (terms : list term) var' coe, var <> var' -> List.find (fun p : term => p.2 == var) terms = List.find (fun p : term => p.2 == var) (remove term_dec (coe,var') terms).
Proof.
  elim. simpl; intros; done.
  simpl; intros [coe_hd var_hd] tl; intros; simpl. 
  destruct (var_hd == var) eqn : Heq. move /eqP : Heq => Heq. 
  - subst var_hd.
    case Hdec : (term_dec (coe, var') (coe_hd, var)) => [left|right]. inversion left; subst var'; done.
    simpl. rewrite eq_refl //.
  - case Hdec : (term_dec (coe, var') (coe_hd, var_hd)) => [left|right]. apply H; done.
    simpl. rewrite Heq. apply H; done.
Qed.

Lemma substitute_coe_gt1 : forall (term0 term1 : list term) coe1 (var1 : ProdVar.t), 
  good_terms term1 ->
  List.find (fun p : term => p.2 == var1) term0 = Some (coe1, var1) ->
  forall coe' (var' : ProdVar.t), List.In (coe', var') term1 -> coe1 >1 \/ coe' >1 ->
  coe1 > 0 -> coe' > 0 ->
  exists coe : nat,
  List.find (fun p : term => p.2 == var')
    (fold_right
       (fun '(coe'0, var) (acc : seq term) =>
        match List.find (fun p : term => p.2 == var) acc with
        | Some t =>
            let (existing_coef, _) := t in
            (existing_coef + coe1 * coe'0, var)
            :: remove term_dec (existing_coef, var) acc
        | None => (coe1 * coe'0, var) :: acc
        end) (remove term_dec (coe1, var1) term0) 
       term1) = Some (coe, var') /\ 1 < coe.
Proof. 
  intros term0; elim. simpl; intros; done.
  intros [hd_coe hd_var] tl1 IH coe1 var1 Hterm; intros; simpl. simpl in H0; destruct H0.
  - inversion H0; clear H0. subst hd_coe hd_var. clear IH.
    case Hfind0 : (List.find (fun p : term => p.2 == var')
      (fold_right
        (fun '(coe'0, var) (acc : seq term) =>
          match List.find (fun p : term => p.2 == var) acc with
          | Some t =>
              let (existing_coef, _) := t in
              (existing_coef + coe1 * coe'0, var)
              :: remove term_dec (existing_coef, var) acc
          | None => (coe1 * coe'0, var) :: acc
          end) (remove term_dec (coe1, var1) term0) tl1)) => [[existing_coef var'']|].
    + simpl; rewrite eqxx. exists (existing_coef + coe1 * coe'); split; try done.
      assert (1 < coe1 * coe'). destruct H1. 
      * specialize (ltn_Pmull H0 H3); intro.
        apply (elimT leP) in H1; apply (elimT leP) in H3. apply (introT leP). move : H1. apply Nat.le_lt_trans; done.
      * specialize (ltn_Pmulr H0 H2); intro.
        apply (elimT leP) in H1; apply (elimT leP) in H2. apply (introT leP). move : H1. apply Nat.le_lt_trans; done.
      apply (elimT leP) in H0. apply (introT leP). apply (Nat.le_trans _ _ _ H0). intuition.
    + simpl; rewrite eqxx. exists (coe1 * coe'); split; try done. destruct H1. 
      * specialize (ltn_Pmull H0 H3); intro.
        apply (elimT leP) in H1; apply (elimT leP) in H3. apply (introT leP). move : H1. apply Nat.le_lt_trans; done.
      * specialize (ltn_Pmulr H0 H2); intro.
        apply (elimT leP) in H1; apply (elimT leP) in H2. apply (introT leP). move : H1. apply Nat.le_lt_trans; done.
  - remember (fold_right
      (fun '(coe'0, var) (acc : seq term) =>
      match List.find (fun p : term => p.2 == var) acc with
      | Some t =>
          let (existing_coef, _) := t in
          (existing_coef + coe1 * coe'0, var)
          :: remove term_dec (existing_coef, var) acc
      | None => (coe1 * coe'0, var) :: acc
      end) (remove term_dec (coe1, var1) term0) tl1) as new_term. rewrite -Heqnew_term.
    assert (exists coe : nat, List.find (fun p : term => p.2 == var') new_term  = Some (coe, var') /\ 1 < coe).
    { rewrite Heqnew_term; apply IH with (coe' := coe'); try done. move : Hterm; clear; unfold good_terms; intros.
      move : Hterm => [Hin Hnodup]; split. intros; apply (Hin _ var); simpl; right; done.
      simpl in Hnodup. destruct (List.split tl1) as [left right] eqn : Hsplit. simpl in Hnodup. apply NoDup_cons_iff in Hnodup. simpl; exact Hnodup.2. }
    destruct H4 as [coe [Hfind Hgt]]. clear IH. exists coe; split; try done; clear Hgt.
    assert (var' <> hd_var). { move : Hterm H0; clear; intros. unfold good_terms in Hterm. move : Hterm => [_ Hterm]. 
      simpl in Hterm. destruct (List.split tl1) as [left right] eqn : Hsplit. simpl in Hterm. apply NoDup_cons_iff in Hterm; move : Hterm => [Hterm _].
      apply in_split_r in H0. rewrite Hsplit in H0; simpl in H0. intuition; subst var'; apply Hterm in H0; done. }
    case Hfind0 : (List.find (fun p : term => p.2 == hd_var) new_term) => [[a b]|].
    rewrite -(find_cons_neq _ _ hd_var (a + coe1 * hd_coe)); try done. rewrite -(find_remove_neq _ _ hd_var a) //; try done.
    rewrite -(find_cons_neq _ _ hd_var (coe1 * hd_coe)); try done.
Qed.

Lemma substitute_c_terms_gt c c_hd : (exists coe : nat, List.In (coe, lhs_var1 c) (rhs_terms1 c_hd)) ->
  good_terms (rhs_terms1 c_hd) -> good_terms (rhs_terms1 c) ->
  forall coe var, List.In (coe, var) (rhs_terms1 c) -> exists coe' : nat, List.In (coe', var) (rhs_terms1 (substitute_c c_hd c)) /\ coe <= coe'.
Proof.
  rewrite /substitute_c /substitute_constraint; intros H Hterm Htermc; intros. destruct H as [coe_c Hin].
  assert (List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c_hd) = Some (coe_c, lhs_var1 c)).
  { clear H0. apply in_nodup_find_some; try done. unfold good_terms in Hterm. move : Hterm => [_ Hterm]; done. }
  rewrite H; clear H; simpl.
  assert (forall terms, List.In (coe, var) terms -> NoDup (List.split terms).2 -> exists coe' : nat, 
    List.In (coe', var)
      (fold_right
        (fun '(coe'0, var0) (acc : seq term) =>
          match List.find (fun p : term => p.2 == var0) acc with
          | Some t =>
              let (existing_coef, _) := t in
              (existing_coef + coe_c * coe'0, var0) :: remove term_dec (existing_coef, var0) acc
          | None => (coe_c * coe'0, var0) :: acc
          end) (remove term_dec (coe_c, lhs_var1 c) (rhs_terms1 c_hd)) terms) /\ 
    coe <= coe').
  { elim. simpl; done.
    simpl; intros [coe_hd var_hd] terms' IH Hhd Hnodup.
    destruct Hhd.
    - inversion H; clear H IH. subst coe_hd var_hd. 
      case : (List.find (fun p : term => p.2 == var)
        (fold_right
          (fun '(coe'0, var0) (acc : seq term) =>
            match List.find (fun p : term => p.2 == var0) acc with
            | Some t =>
                let (existing_coef, _) := t in
                (existing_coef + coe_c * coe'0, var0) :: remove term_dec (existing_coef, var0) acc
            | None => (coe_c * coe'0, var0) :: acc
            end) (remove term_dec (coe_c, lhs_var1 c) (rhs_terms1 c_hd)) terms')) => [[existing_coef var']|].
      + exists (existing_coef + coe_c * coe); split. simpl; left; done. 
        unfold good_terms in Hterm; move : Hterm => [Hterm _]. apply Hterm in Hin. move : Hin; clear.
        intro. assert (coe <= coe_c * coe). apply leq_pmull. induction coe_c; try done.
        assert (coe_c * coe <= existing_coef + coe_c * coe) by (apply leq_addl).
        move : H H0; apply leq_trans.
      + exists (coe_c * coe); split. simpl; left; done. 
        unfold good_terms in Hterm; move : Hterm => [Hterm _]. apply Hterm in Hin. move : Hin; clear.
        intro. apply leq_pmull. induction coe_c; try done. 
    - assert (var <> var_hd). { move: H Hnodup; clear; intros. destruct (List.split terms') as [left right] eqn : Hsplit.
        simpl in Hnodup. apply NoDup_cons_iff in Hnodup. move : Hnodup => [Hnodup _]. apply in_split_r in H; rewrite Hsplit in H; simpl in H.
        intuition; subst var. apply Hnodup in H; done. } 
      apply IH in H; clear IH. destruct H as [coe_new [Hin_new Hge]].
      remember (fold_right
        (fun '(coe'0, var0) (acc : seq term) =>
        match List.find (fun p : term => p.2 == var0) acc with
        | Some t =>
            let (existing_coef, _) := t in
            (existing_coef + coe_c * coe'0, var0) :: remove term_dec (existing_coef, var0) acc
        | None => (coe_c * coe'0, var0) :: acc
        end) (remove term_dec (coe_c, lhs_var1 c) (rhs_terms1 c_hd)) terms') as terms_new. rewrite -Heqterms_new.
      rewrite -Heqterms_new in Hin_new.
      case Hfind : (List.find (fun p : term => p.2 == var_hd) terms_new) => [[existing_coef varhd]|].
      1,2 : exists coe_new; split; try done.
      + apply List.in_cons. move : Hin_new; apply in_in_remove. intuition; inversion H; subst var; done.
      + apply List.in_cons; done. 
      destruct (List.split terms') as [left right] eqn : Hsplit. simpl in Hnodup; simpl. apply NoDup_cons_iff in Hnodup. exact Hnodup.2. }
  apply H; try done. unfold good_terms in Htermc. exact Htermc.2.
Qed. 

Lemma substitute_cs_terms_gt cs : (forall c, List.In c cs -> good_terms (rhs_terms1 c)) ->
  (forall c0 c1, (exists pre suf, pre ++ c0 :: c1 :: suf = cs) -> exists coe, List.In (coe, lhs_var1 c1) (rhs_terms1 c0)) ->
  forall new_c, substitute_cs cs = Some new_c -> forall last_c, List.hd_error (List.rev cs) = Some last_c -> forall coe var, List.In (coe, var) (rhs_terms1 last_c) -> exists coe', List.In (coe', var) (rhs_terms1 new_c) /\ coe <= coe'.
Proof.
  move : cs. elim. simpl; intros; done.
  intros c_hd c_tl IH Hterm; intros. simpl in H0.
  case Hsub : (substitute_cs c_tl) => [c|]; rewrite Hsub in H0; inversion H0; clear H0.
  subst new_c. simpl in H1. case Htl : c_tl => [|a b]. rewrite Htl in Hsub; simpl in Hsub; try discriminate. 
  generalize Hsub; apply IH with (coe := coe) (var := var) (last_c := last_c) in Hsub; try done; intros.
  destruct Hsub as [coe_c [Hin_c Hge_c]]. 
  assert (exists coe : nat, List.In (coe, lhs_var1 c) (rhs_terms1 c_hd)).
  { apply substitute_cs_lhs_eq in Hsub0. move : Hsub0 H; clear; intros. destruct Hsub0 as [c0 [Hhd Hlhs]].
    specialize (H c_hd c0). assert (exists pre suf, pre ++ [:: c_hd, c0 & suf] = c_hd :: c_tl).
    exists nil; simpl. destruct c_tl as [|a b]; try done. simpl in Hhd. inversion Hhd. exists b; done.
    apply H in H0; clear H. rewrite -Hlhs; done. }
  apply (substitute_c_terms_gt _ _ H0) in Hin_c. destruct Hin_c as [coe' [Hin Hge]].
  exists coe'; split; try done. move : Hge_c Hge. apply leq_trans. apply Hterm; simpl; left; done.
    move : Hsub0; apply substitute_cs_good_term. intros; apply Hterm; simpl; right; done. apply Hterm; simpl; right; done.
    apply H. destruct H0 as [pre [suf H0]]; rewrite -H0. exists (c_hd :: pre); exists suf. simpl; done.
  rewrite not_empty_last_eq in H1; try done. rewrite Htl //.
  subst c_hd. apply substitute_cs_none in Hsub. subst c_tl. clear IH H; simpl in H1. exists coe; split; try done. inversion H1; done.
Qed.

Lemma find_constraint_lst_in adj g x p_tl cs cs0 a : (forall c, List.In c cs -> good_terms (rhs_terms1 c)) ->
  scc.build_graph cs = (g, adj) -> find_constraints_of_path adj x p_tl = Some cs0 -> List.hd_error (List.rev p_tl) = Some a ->
  forall last_c, List.hd_error (List.rev cs0) = Some last_c -> exists coe, List.find (fun p : term => p.2 == a) (rhs_terms1 last_c) = Some (coe, a).
Proof.
  intros Hterm HBuild; move : p_tl x cs0. elim. simpl; intros. discriminate.
  simpl; intros hd p_tl' IH; intros. 
  case Hfindadj : (find_adj_matrix hd x adj) => [l|]; rewrite Hfindadj in H; try discriminate.
  case Hl : l => [|c_hd l']; rewrite Hl in H; try discriminate; subst l.
  case Hfind : (find_constraints_of_path adj hd p_tl') => [cs'|]; rewrite Hfind in H; try discriminate. inversion H; clear H; subst cs0. 
  simpl in H1.
  case Hcs' : cs' => [|cs'_hd cs'_tl]; rewrite Hcs' in H1.
  - subst cs'. simpl in H1; inversion H1; clear H1. subst c_hd. apply find_constraints_of_path_nil in Hfind; subst p_tl'.
    simpl in H0; inversion H0; clear H0; subst hd. specialize (find_adj_in_rhs _ _ _ _ _ _ Hterm HBuild Hfindadj last_c); intros.
    destruct H as [coe Hin]. simpl; left; done. exists coe. apply in_nodup_find_some; try done. 
    assert (List.In last_c cs). { specialize (find_adj_matrix_subset _ _ _ _ _ _ Hterm HBuild Hfindadj last_c); intro. apply H; simpl; left; done. }
    apply Hterm in H. unfold good_terms in H. exact H.2.
  - case Hp_tl' : p_tl' => [|p_tl'_hd p_tl'_tl]; rewrite Hp_tl' in H0.
    + subst p_tl'; clear IH. simpl in Hfind; inversion Hfind; clear Hfind; subst cs'. discriminate.
    + rewrite not_empty_last_eq in H0; rewrite not_empty_last_eq in H1. rewrite -Hcs' in H1. rewrite -Hp_tl' in H0. move : H1. apply (IH _ _ Hfind); try done.
    1,2,3 : done.
Qed.

Lemma substitute_cs_some : forall cs1 c, substitute_cs cs1 = Some c -> cs1 <> [].
Proof.
  elim. simpl; intros; discriminate. simpl; intros. done.
Qed.

Lemma substitute_cs_helper cs g adj x n x' p0_hd p0_tl c0 cs0 : scc.build_graph cs = (g, adj) -> (forall c : Constraint1, List.In c cs -> good_terms (rhs_terms1 c)) -> 
  scc.find_path g x n [] x' None = Some (p0_hd :: p0_tl) -> find_constraints_of_path adj p0_hd p0_tl = Some cs0 -> substitute_cs cs0 = Some c0 ->
  lhs_var1 c0 = x /\ exists coe, List.find (fun p : term => p.2 == x') (rhs_terms1 c0) = Some (coe, x').
Proof.
  intros Hbuild Hterm Hp0 Hcs0 Hsub0.
  generalize Hsub0; apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd Hlhs]]; rewrite -Hlhs; clear Hlhs. intros Hsub0.
  generalize Hp0; apply find_path_hd_eq_tgt in Hp0; simpl in Hp0. inversion Hp0; clear Hp0. subst p0_hd.
  intros. apply find_path_last_eq_src in Hp0. simpl in Hp0. case Hp0_tl : p0_tl => [|p0_hd' p0_tl']; rewrite Hp0_tl in Hp0.
    simpl in Hp0; inversion Hp0. subst p0_tl x. simpl in Hcs0. inversion Hcs0; subst cs0. simpl in Hhd; discriminate.
  rewrite -Hp0_tl in Hp0. rewrite not_empty_last_eq in Hp0.
  split. apply (find_constraint_hd_eq _ _ _ _ _ _ _ Hterm Hbuild Hcs0 Hhd).
  specialize (find_constraints_of_path_correctness _ _ _ _ _ _ Hterm Hbuild Hcs0); intro. 
  assert (forall c, List.In c cs0 -> good_terms (rhs_terms1 c)) by (intros; apply Hterm; apply (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs0) in H0; done).
  assert (exists last_c, hd_error (List.rev cs0) = Some last_c). { apply substitute_cs_some in Hsub0. move : Hsub0; clear; move : cs0. elim. simpl; done. simpl; intros.
    destruct l. exists a; simpl; done. destruct H as [last_c H]; try done. exists last_c. rewrite not_empty_last_eq //. }
  destruct H1 as [last_c H3].
  specialize (substitute_cs_terms_gt _ H0 H _ Hsub0 _ H3); intro. clear H H0.
  specialize (find_constraint_lst_in _ _ _ _ _ _ _ Hterm Hbuild Hcs0 Hp0 _ H3); intro. 
  destruct H as [lst_coe Hin].
  apply find_some in Hin. move : Hin => [Hin _].
  apply H1 in Hin; clear H1. destruct Hin as [coe' [Hin Hle]]. exists coe'. 
    specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs0); intro. apply substitute_cs_good_term in Hsub0.
    move : Hsub0 Hin; clear; intros. rewrite /good_terms in Hsub0. move : Hsub0 => [_ Hsub0]. apply in_nodup_find_some; try done.
    intros; apply Hterm; apply H; done. rewrite Hp0_tl //.
Qed.

Lemma add_edge_find_children_notin c : forall vars g adj g' adj' a, fold_left
    (fun '(graph, adj_matrix) (xi : ProdVar.t) =>
    scc.add_edge graph adj_matrix xi (lhs_var1 c) c) vars (g', adj') = (g, adj) -> 
  ~ List.In a vars -> PVM.find a g' = PVM.find a g.
Proof.
  elim. simpl; intros; inversion H. done.
  simpl; intros. apply Decidable.not_or in H1. move : H1 => [Hneq Hnotin].
  apply H with (a := a0) in H0; try done. clear Hnotin H. 
  destruct (PVM.find a g') as [children|]. 1,2: rewrite find_add_neq in H0; try done. 1,2 : intuition.
Qed.

Lemma add_edge_find_children_neq c : forall vars g adj g' adj' a b children, fold_left
    (fun '(graph, adj_matrix) (xi : ProdVar.t) =>
    scc.add_edge graph adj_matrix xi (lhs_var1 c) c) vars (g', adj') = (g, adj) -> 
  b <> (lhs_var1 c) -> PVM.find a g = Some children -> List.In b children -> exists children', PVM.find a g' = Some children' /\ List.In b children'.
Proof.
  elim. simpl; intros; inversion H; subst adj' g'. exists children; split; done.
  simpl; intros. destruct (scc.add_edge g' adj' a (lhs_var1 c) c) as [g_inter adj_inter] eqn : Hinter.
  apply H with (a := a0) (b := b) (children := children) in H0; try done. move : Hinter H0 H1; clear; intros.
  destruct H0 as [children [Hfind Hin]]. unfold scc.add_edge in Hinter; inversion Hinter; clear Hinter H2.
  destruct (PVM.find a g') as [children'|] eqn : Hfind'.
  destruct (a == a0) eqn : Heqa; move /eqP : Heqa => Heqa.
  - subst a0. subst g_inter. rewrite find_add_eq in Hfind. inversion Hfind; subst children; clear Hfind. simpl in Hin. destruct Hin. intuition.
    exists children'; split; done.
  - subst g_inter. rewrite find_add_neq in Hfind. exists children; split; done. intuition.
  subst g_inter.
  destruct (a == a0) eqn : Heqa; move /eqP : Heqa => Heqa.
  - subst a0. rewrite find_add_eq in Hfind. inversion Hfind; subst children. simpl in Hin. destruct Hin; try intuition.
  - rewrite find_add_neq in Hfind. exists children; split; done. intuition.
Qed.

Lemma build_graph_g_adj_eq a b : forall cs g adj, scc.build_graph cs = (g, adj) -> (forall c, List.In c cs -> (good_terms (rhs_terms1 c))) ->
  (exists children, PVM.find a g = Some children /\ List.In b children) ->
  exists cs0, find_adj_matrix a b adj = Some cs0 /\ cs0 <> nil.
Proof.
  elim. simpl; intros g adj HBuild Hterm; intros. inversion HBuild; clear HBuild. subst g adj. destruct H as [children [H0 H1]]. rewrite find_empty_None in H0; discriminate.
    simpl; intros c_hd cs' IH g adj HBuild Hterm. destruct (scc.build_graph cs') as [g' adj']. assert ((g', adj') = (g', adj')) by done. 
    assert (forall c : Constraint1, List.In c cs' -> good_terms (rhs_terms1 c)) by (intros; apply Hterm; simpl; right; done).
    specialize (IH _ _ H H0); clear H H0.
    intros. destruct H as [children [Hfind Hin]]. destruct (in_bool a (List.split (rhs_terms1 c_hd)).2) eqn : Hain.
    - (* a in vars *)
      destruct (b == (lhs_var1 c_hd)) eqn : Hb; move /eqP : Hb => Hb.
      + (* b is lhs *) 
        remember (List.split (rhs_terms1 c_hd)).2 as vars. subst b. 
        assert (good_terms (rhs_terms1 c_hd)) by (apply Hterm; left; done). unfold good_terms in H; move :H => [_ Hnodup]. rewrite -Heqvars in Hnodup. clear Heqvars. apply In_in_bool in Hain. 
        move : vars g' adj' IH g adj HBuild children Hfind Hin Hain Hnodup; clear.
        elim. simpl; intros; done.
        simpl; intros. apply NoDup_cons_iff in Hnodup; move : Hnodup => [Hnotin Hnodup]. destruct Hain. subst a0. clear H. 
        (* a0 = a *)
        generalize HBuild. apply add_edge_find_children_notin with (a := a) in HBuild; try done; intro. destruct (PVM.find a g') as [children'|] eqn : Hfind'.
        * rewrite find_add_eq in HBuild. rewrite Hfind in HBuild. inversion HBuild; subst children; clear HBuild Hin IH.
          apply nodup_add_edge_find_eq with (a := a) (b := lhs_var1 c_hd) in HBuild0; try done. rewrite HBuild0; clear HBuild0. unfold find_adj_matrix.
          destruct (PVM.find a adj') as [adja|] eqn : Hadja. destruct (PVM.find (lhs_var1 c_hd) adja) as [cs1|] eqn : Hcs1.
          rewrite find_add_eq. rewrite find_add_eq. exists (c_hd :: cs1); done.
          rewrite find_add_eq. rewrite find_add_eq. exists [c_hd]; done.
          rewrite find_add_eq. rewrite find_add_eq. exists [c_hd]; done.
        * rewrite find_add_eq in HBuild. rewrite Hfind in HBuild. inversion HBuild; subst children; clear HBuild Hin IH.
          apply nodup_add_edge_find_eq with (a := a) (b := lhs_var1 c_hd) in HBuild0; try done. rewrite HBuild0; clear HBuild0. unfold find_adj_matrix.
          destruct (PVM.find a adj') as [adja|] eqn : Hadja. destruct (PVM.find (lhs_var1 c_hd) adja) as [cs1|] eqn : Hcs1.
          rewrite find_add_eq. rewrite find_add_eq. exists (c_hd :: cs1); done.
          rewrite find_add_eq. rewrite find_add_eq. exists [c_hd]; done.
          rewrite find_add_eq. rewrite find_add_eq. exists [c_hd]; done.
        (* a0 in l *)
        destruct (scc.add_edge g' adj' a0 (lhs_var1 c_hd) c_hd) as [g_inter adj_inter] eqn : Hinter. move : HBuild children Hfind Hin H0 Hnodup; apply H.
        move : IH Hinter; clear; intros. unfold scc.add_edge in Hinter; inversion Hinter; clear Hinter. destruct H as [children [Hfind Hin]].
        unfold find_adj_matrix. destruct (PVM.find a0 g') as [children'|] eqn : Hfind'; subst g_inter.
        * destruct (a == a0) eqn : Ha; move /eqP : Ha => Ha.
          - subst a0. rewrite find_add_eq in Hfind. inversion Hfind; subst children; clear Hfind Hin IH. 
            destruct (PVM.find a adj') as [a0_adj|] eqn : Hadja0.
            + destruct (PVM.find (lhs_var1 c_hd) a0_adj) as [cs1|] eqn : Hcs1; subst adj_inter. rewrite find_add_eq. rewrite find_add_eq. exists (c_hd :: cs1); done.
              rewrite find_add_eq. rewrite find_add_eq. exists [c_hd]; done.
            + rewrite find_add_eq. rewrite find_add_eq. exists [c_hd]; done.
          - rewrite find_add_neq in Hfind; try done. destruct IH as [cs0 [Hadj Hnotnil]]. exists children; split; done. unfold find_adj_matrix in Hadj.
            destruct (PVM.find a adj') as [a_adj|] eqn : Hadja; try discriminate.
            destruct (PVM.find a0 adj') as [a0_adj|] eqn : Hadja0.
            + destruct (PVM.find (lhs_var1 c_hd) a0_adj) as [cs1|] eqn : Hcs1; subst adj_inter. rewrite find_add_neq; try done. rewrite Hadja. exists (cs0); split; done.
              rewrite find_add_neq; try done. rewrite Hadja. exists (cs0); split; done.
            + rewrite find_add_neq; try done. rewrite Hadja. exists (cs0); split; done.
        * destruct (a == a0) eqn : Ha; move /eqP : Ha => Ha.
          - subst a0. rewrite find_add_eq in Hfind. inversion Hfind; subst children; clear Hfind Hin IH. 
            destruct (PVM.find a adj') as [a0_adj|] eqn : Hadja0.
            + destruct (PVM.find (lhs_var1 c_hd) a0_adj) as [cs1|] eqn : Hcs1; subst adj_inter. rewrite find_add_eq. rewrite find_add_eq. exists (c_hd :: cs1); done.
              rewrite find_add_eq. rewrite find_add_eq. exists [c_hd]; done.
            + rewrite find_add_eq. rewrite find_add_eq. exists [c_hd]; done.
          - rewrite find_add_neq in Hfind; try done. destruct IH as [cs0 [Hadj Hnotnil]]. exists children; split; done. unfold find_adj_matrix in Hadj.
            destruct (PVM.find a adj') as [a_adj|] eqn : Hadja; try discriminate.
            destruct (PVM.find a0 adj') as [a0_adj|] eqn : Hadja0.
            + destruct (PVM.find (lhs_var1 c_hd) a0_adj) as [cs1|] eqn : Hcs1; subst adj_inter. rewrite find_add_neq; try done. rewrite Hadja. exists (cs0); split; done.
              rewrite find_add_neq; try done. rewrite Hadja. exists (cs0); split; done.
            + rewrite find_add_neq; try done. rewrite Hadja. exists (cs0); split; done.
      + apply (add_edge_find_children_neq _ _ _ _ _ _ _ _ _ HBuild Hb Hfind) in Hin. apply IH in Hin; clear IH.
        apply (add_edge_find_lhs_neq _ _ _ _ _ _ a _ HBuild) in Hb. rewrite Hb; done.
    - (* a not in *)
      assert (PVM.find a g' = PVM.find a g /\ find_adj_matrix a b adj' = find_adj_matrix a b adj).
      { apply not_true_iff_false in Hain. assert (~ List.In a (List.split (rhs_terms1 c_hd)).2) by (move : Hain; apply contra_not; apply In_in_bool).
        clear Hain. split. move : HBuild H; apply add_edge_find_children_notin. 
        apply (add_edge_find_lhs_eq_neq _ b _ _ _ _ _ _ HBuild) in H; try done. }
      move : H => [H H']. rewrite -H'. apply IH. exists children; rewrite H; split; try done.
Qed. 

Lemma find_path_correctness_helper g : forall n res0 res l (a b : ProdVar.t), (forall hd, List.hd_error l = Some hd -> exists children, PVM.find hd g = Some children /\ List.In b children) ->
  (forall x y, (exists pre suf, pre ++ y :: x :: suf = l) -> exists children, PVM.find x g = Some children /\ List.In y children) ->
  match res0 with | Some res0' => forall x y, (exists pre suf, pre ++ y :: x :: suf = res0') -> exists children, PVM.find x g = Some children /\ List.In y children | None => true end ->
  scc.find_path g a n l b res0 = Some res -> forall x y, (exists pre suf, pre ++ y :: x :: suf = res) -> exists children, PVM.find x g = Some children /\ List.In y children.
Proof.
  elim. intros res0 res l a b Hb Hl; intros. simpl in H0. case Hres0 : res0 => [res'|]; rewrite Hres0 in H H0. inversion H0; subst res'; clear H0.
    move : x y H1; done. subst res0; clear H. destruct (b == a) eqn:Heq; try discriminate. move /eqP : Heq => Heq. subst b. inversion H0; subst res; clear H0. 
    destruct H1 as [pre [suf H1]]. destruct pre as [|hd pre'] eqn : Hpre. subst pre; simpl in H1. inversion H1. subst y. apply Hb. rewrite -H2; simpl; done.
    assert (exists pre suf, pre ++ y :: x :: suf = l) by (exists pre'; exists suf; inversion H1; done). apply Hl in H; done.
  simpl; intros n IH res0 res l a b Hb Hl; intros. case Hres0 : res0 => [res'|]; rewrite Hres0 in H H0. inversion H0; subst res'. apply H; done.
  subst res0; clear H. destruct (b == a) eqn:Heq. 
  - move /eqP : Heq => Heq. subst b. inversion H0; subst res; clear H0.
    destruct H1 as [pre [suf H1]]. destruct pre as [|hd pre'] eqn : Hpre. subst pre; simpl in H1. inversion H1. subst y. apply Hb. rewrite -H2; simpl; done.
    assert (exists pre suf, pre ++ y :: x :: suf = l) by (exists pre'; exists suf; inversion H1; done). apply Hl in H; done.
  - destruct (PVM.find b g) as [children|] eqn:HChildren; try discriminate.
    assert (Hhelper : forall children' res0 res l, (forall child hd, List.In child children' -> List.hd_error l = Some hd -> exists children, PVM.find hd g = Some children /\ List.In child children) ->
      (forall x y, (exists pre suf, pre ++ y :: x :: suf = l) -> exists children, PVM.find x g = Some children /\ List.In y children) ->
      match res0 with | Some res0' => forall x y, (exists pre suf, pre ++ y :: x :: suf = res0') -> exists children, PVM.find x g = Some children /\ List.In y children | None => true end ->
      foldl (fun (r : option (seq ProdVar.t)) (child : ProdVar.t) =>
      match r with
      | Some _ => None
      | None => scc.find_path g a n l child None
      end) res0 children' = Some res -> 
      forall x y, (exists pre suf, pre ++ y :: x :: suf = res) -> exists children, PVM.find x g = Some children /\ List.In y children).
    { move : IH; clear; intro IH. elim. intros res0 res l Hb Hl; intros. simpl in H0. rewrite H0 in H. apply H; done.
      intros child children' IH' res0 res l Hb Hl; intros. simpl in H0. case Hres0 : res0 => [res0'|]; rewrite Hres0 in H H0.
      - move : H0 x y H1; apply IH'; try done. intros c0 hd Hin; apply Hb. simpl; right; done.
      - subst res0; clear H. move : H0 x y H1; apply IH'; try done. clear IH'. intros c0 hd Hin; apply Hb. simpl; right; done.
        case Hchild : (scc.find_path g a n l child None) => [res'|]; try done.
        move : Hchild; apply IH; try done. intros; apply Hb; try done. simpl; left; done. }
    move : H0 x y H1; apply Hhelper; try done. clear Hhelper. intros. simpl in H0. inversion H0; subst hd; clear H0. exists children; split; done.
    clear Hhelper IH. intros. destruct H as [pre [suf H]]. destruct pre as [|hd pre'] eqn : Hpre. subst pre; simpl in H. inversion H. subst y. apply Hb. rewrite -H2; simpl; done.
      assert (exists pre suf, pre ++ y :: x :: suf = l) by (exists pre'; exists suf; inversion H; done). apply Hl in H0; done.
Qed.

Lemma find_path_correctness cs g adj a b n res : scc.build_graph cs = (g, adj) -> (forall c, List.In c cs -> (good_terms (rhs_terms1 c))) ->
  scc.find_path g a n [] b None = Some res -> forall x y, (exists pre suf, pre ++ y :: x :: suf = res) -> 
  exists cs0, find_adj_matrix x y adj = Some cs0 /\ cs0 <> nil.
Proof.
  intros H Hterm; intros. apply (build_graph_g_adj_eq _ _ _ _ _ H); try done. destruct (a == b) eqn : Heq; move /eqP : Heq => Heq. subst b. 
    destruct n; simpl in H0; rewrite eq_refl in H0; inversion H0; rewrite -H3 in H1; destruct H1 as [pre [suf H1]]; destruct pre; try done; destruct pre; try done.
  move : H0 x y H1. apply find_path_correctness_helper; try done. intros. destruct H0 as [pre [suf H0]]. destruct pre; try done.
Qed.

Lemma find_constraints_of_path_exists cs g adj p_tl p_hd a b n: scc.build_graph cs = (g, adj) -> (forall c, List.In c cs -> (good_terms (rhs_terms1 c))) ->
  scc.find_path g a n [] b None = Some (p_hd :: p_tl) -> exists cs0, find_constraints_of_path adj p_hd p_tl = Some cs0.
Proof.
  intros HBuild Hterm Hp. specialize (find_path_correctness _ _ _ _ _ _ _ HBuild Hterm Hp); intro. clear HBuild Hp. move : p_tl p_hd H. elim. simpl; intros. exists nil; done.
  simpl; intros p_hd' p_tl' IH; intros. destruct (H p_hd' p_hd) as [cs0 [Hfind Hnotnil]]. exists nil; exists p_tl'; done. 
  rewrite Hfind. destruct cs0; try done; clear Hnotnil. destruct (IH p_hd') as [cs0' IH']. 
  intros; apply H. destruct H0 as [pre [suf H0]]. exists (p_hd :: pre); exists suf. rewrite -H0; simpl; done.
  rewrite IH'. exists (c::cs0'); done.
Qed.

Lemma no_ub_unsat_case1 cs c coe var x g adj n : (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs -> rhs_power c = nil) ->
  scc.build_graph cs = (g, adj) ->
  (exists p_hd p_tl, scc.find_path g x n [] (lhs_var1 c) None = Some (p_hd :: p_tl)) ->
  (exists p_hd p_tl, scc.find_path g var n [] x None = Some (p_hd :: p_tl)) ->
  List.find (fun c : Constraint1 => List.existsb (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) cs = Some c ->
  List.find (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c) = Some (coe, var) ->
  solve_ub_case1 x c var g adj n = None -> 
  forall v, ~ forallb (satisfies_constraint1 v) cs.
Proof.
  intros Hterm Hpower Hbuild Hp0 Hp1; intros. rewrite /solve_ub_case1 in H1.
  destruct Hp0 as [p0_hd [p0_tl Hp0]]. rewrite Hp0 in H1.
  destruct Hp1 as [p1_hd [p1_tl Hp1]]. rewrite Hp1 in H1.
  assert (Hcs0 : exists cs0, find_constraints_of_path adj p0_hd p0_tl = Some cs0) by (move : Hbuild Hterm Hp0; apply find_constraints_of_path_exists).
  destruct Hcs0 as [cs0 Hcs0]. rewrite Hcs0 in H1.
  assert (Hcs1 : exists cs1, find_constraints_of_path adj p1_hd p1_tl = Some cs1) by (move : Hbuild Hterm Hp1; apply find_constraints_of_path_exists).
  destruct Hcs1 as [cs1 Hcs1]. rewrite Hcs1 in H1. 
  remember (match substitute_cs cs0 with
    | Some c0 =>
        match substitute_cs cs1 with
        | Some c1 => substitute_c c0 (substitute_c c c1)
        | None => substitute_c c0 c
        end
    | None => match substitute_cs cs1 with
              | Some c1 => substitute_c c c1
              | None => c
              end
    end) as new_c.
  assert (exists coe, List.find (fun p : term => p.2 == lhs_var1 new_c) (rhs_terms1 new_c) = Some (coe, lhs_var1 new_c) /\ coe > 1).
  { clear H1.
    case Hsub0 : (substitute_cs cs0) => [c0|]; rewrite Hsub0 in Heqnew_c.
    - assert (lhs_var1 c0 = x /\ exists coe, List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c0) = Some (coe, lhs_var1 c)) by
        (move : Hbuild Hterm Hp0 Hcs0 Hsub0; apply substitute_cs_helper).
      case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in Heqnew_c.
      + assert (lhs_var1 c1 = var /\ exists coe, List.find (fun p : term => p.2 == x) (rhs_terms1 c1) = Some (coe, x)) by
          (move : Hbuild Hterm Hp1 Hcs1 Hsub1; apply substitute_cs_helper).
        move : H1 => [Heq0 [coe0 Hfind0]]; move : H2 => [Heq1 [coe1 Hfind1]]. subst x var. specialize (substitute_c_lhs_eq c c1); intro. remember (substitute_c c c1) as c1'. 
        apply find_some in H0. move : H0 => [Hin H0]; simpl in H0. apply in_nodup_find_some in Hin.
        assert (Hterm1 : good_terms (rhs_terms1 c1)). { move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm. move : Hbuild Hcs1 c2 H2; apply find_constraints_of_path_subset; done. }
        specialize (substitute_coe_gt1 _ (rhs_terms1 c1) _ _ Hterm1 Hin); intros. destruct (H2 coe1 (lhs_var1 c0)) as [coe' [Hfind' Hgt']]; clear H2. 
        apply find_some in Hfind1; exact Hfind1.1. left; done. intuition. 
        unfold good_terms in Hterm1. apply find_some in Hfind1; move : Hfind1 => [Hfind1 _]. move : Hterm1 => [Hterm1 _]; apply Hterm1 in Hfind1. destruct coe1; try done.
        remember ((fold_right
          (fun '(coe'0, var) (acc : seq term) =>
          match
            List.find (fun p : term => p.2 == var) acc
          with
          | Some t =>
              let (existing_coef, _) := t in
              (existing_coef + coe * coe'0, var)
              :: remove term_dec (existing_coef, var) acc
          | None => (coe * coe'0, var) :: acc
          end)
          (remove term_dec (coe, lhs_var1 c1) (rhs_terms1 c))
          (rhs_terms1 c1))) as terms_c1'.
        rewrite /substitute_c /substitute_constraint H1 Hfind0 in Heqnew_c; simpl in Heqnew_c. subst new_c; simpl. 
        apply substitute_coe_gt1 with (coe' := coe'); try done.
        rewrite Heqc1' /substitute_c /substitute_constraint Hin; simpl. apply substitute_good_terms. apply good_terms_remove.
        2 : move : Hsub1; apply substitute_cs_good_term. apply Hterm; apply find_some in H; exact H.1. intros; apply Hterm.
        move : Hbuild Hcs1 c2 H2; apply find_constraints_of_path_subset; done. intuition; rewrite H2 in H0; done.
        rewrite Heqc1' /substitute_c /substitute_constraint Hin; simpl. rewrite -Heqterms_c1'.
        apply find_some in Hfind'. exact Hfind'.1. right; done.
        apply substitute_cs_good_term in Hsub0. unfold good_terms in Hsub0; move : Hsub0 => [Hsub0 _].
          apply find_some in Hfind0; move : Hfind0 => [Hfind0 _]. apply Hsub0 in Hfind0. induction coe0; try done.
          intros; apply Hterm. move : Hbuild Hcs0 c2 H2; apply find_constraints_of_path_subset; done. intuition.
        apply find_some in H. move : H => [H _]; apply Hterm in H. rewrite /good_terms in H. exact H.2.
      + apply substitute_cs_none in Hsub1. subst cs1. apply find_constraints_of_path_nil in Hcs1. subst p1_tl.
        apply find_path_1 in Hp1. subst x. move : H1 => [H1 [coe' Hc0]]. subst var.
        rewrite /substitute_c /substitute_constraint in Heqnew_c.
        apply find_some in H0. move : H0 => [Hin H0]; simpl in H0. 
        rewrite Hc0 in Heqnew_c. subst new_c; simpl. 
        apply substitute_coe_gt1 with (coe' := coe); try done. apply Hterm. apply find_some in H. exact H.1.
        right; done. apply substitute_cs_good_term in Hsub0. unfold good_terms in Hsub0; move : Hsub0 => [Hsub0 _].
          apply find_some in Hc0; move : Hc0 => [Hc0 _]. apply Hsub0 in Hc0. destruct coe'; try done.
        intros; apply Hterm. move : Hbuild Hcs0 c1 H1; apply find_constraints_of_path_subset; done. intuition.
    - case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in Heqnew_c.
      + assert (lhs_var1 c1 = var /\ exists coe, List.find (fun p : term => p.2 == x) (rhs_terms1 c1) = Some (coe, x)).
          by (move : Hbuild Hterm Hp1 Hcs1 Hsub1; apply substitute_cs_helper).
        apply substitute_cs_none in Hsub0. subst cs0. apply find_constraints_of_path_nil in Hcs0. subst p0_tl.
        apply find_path_1 in Hp0. subst x. move : H1 => [H1 [coe' Hc0]]. subst var.
        rewrite /substitute_c /substitute_constraint in Heqnew_c.
        apply find_some in H0. move : H0 => [Hin H0]; simpl in H0. apply in_nodup_find_some in Hin.
        rewrite Hin in Heqnew_c. subst new_c; simpl. apply substitute_coe_gt1 with (coe' := coe'); try done.
          move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm. move : Hbuild Hcs1 c0 H1; apply find_constraints_of_path_subset; done.
          2: left; done. apply find_some in Hc0. exact Hc0.1. intuition.
        apply substitute_cs_good_term in Hsub1. unfold good_terms in Hsub1; move : Hsub1 => [Hsub1 _]. apply find_some in Hc0; move : Hc0 => [Hc0 _].
        apply Hsub1 in Hc0. destruct coe'; try done. intros; apply Hterm. move : Hbuild Hcs1 c0 H1; apply find_constraints_of_path_subset; done.
        apply find_some in H. move : H => [H _]; apply Hterm in H. rewrite /good_terms in H. exact H.2.
      + subst new_c. apply substitute_cs_none in Hsub0; apply substitute_cs_none in Hsub1. subst cs0 cs1. 
        apply find_constraints_of_path_nil in Hcs1; apply find_constraints_of_path_nil in Hcs0. subst p0_tl p1_tl.
        apply find_path_1 in Hp0. apply find_path_1 in Hp1. subst x var. apply find_some in H; move : H => [H _]. apply Hterm in H.
        exists coe; move: H0 H; clear; intros. apply find_some in H0; simpl in H0; move : H0 => [H0 H1].
        split; try done. apply in_nodup_find_some; try done. rewrite /good_terms in H. exact H.2. }
  specialize (no_compute_ub_unsat _ H2 H1 v); clear H2; intro.
  specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs0) as Hfind_cs_in0.
  specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs1) as Hfind_cs_in1.
  apply find_some in H; move : H => [H _].
  move : Heqnew_c H2 Hpower Hterm Hfind_cs_in0 Hfind_cs_in1 H; clear; intros.
  { case Hsub0 : (substitute_cs cs0) => [c0|]; rewrite Hsub0 in Heqnew_c.
    - case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in Heqnew_c.
      + subst new_c. move : H2; apply contra_not; intros. apply substitute_c_correctness.
        assert (forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done).
        move : Hsub0; apply substitute_cs_correctness.
        intros; apply Hterm. 2: intros; apply Hpower. 3: apply forallb_forall; intros; apply H1.
        1,2,3 : apply Hfind_cs_in0; done. 
        apply substitute_c_correctness. move : c H; apply forallb_forall; done.
        move : Hsub1; apply substitute_cs_correctness. intros; apply Hterm. 2: intros; apply Hpower.
        3 : assert (forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done).
        3 : apply forallb_forall; intros; apply H1. 1,2,3: apply Hfind_cs_in1; done.
        apply Hpower; try done. 2: apply Hterm; try done. move : Hsub1; apply substitute_cs_power.
        2 : move : Hsub1; apply substitute_cs_good_term. 3 : move : Hsub0; apply substitute_cs_power.
        1,2 : intros. apply Hpower. apply Hfind_cs_in1; done. apply Hterm. apply Hfind_cs_in1; done.
        intros; apply Hpower. apply Hfind_cs_in0; done. 
        apply substitute_c_power. apply Hpower; done. move : Hsub1; apply substitute_cs_power.
        intros; apply Hpower. apply Hfind_cs_in1; done. move : Hsub0; apply substitute_cs_good_term.
        intros; apply Hterm. apply Hfind_cs_in0; done. apply substitute_c_good_term.
        apply Hterm; done. move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm; apply Hfind_cs_in1; done.
      + subst new_c. move : H2; apply contra_not; intros.
        assert (forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done). clear H0.
        apply substitute_c_correctness. clear Hsub1.
        move : Hsub0; apply substitute_cs_correctness. intros; apply Hterm. 2: intros; apply Hpower.
        3 : apply forallb_forall; intros; apply H1.  1,2,3 : apply Hfind_cs_in0; done.
        apply H1; done. move : Hsub0; apply substitute_cs_power. intros; apply Hpower. apply Hfind_cs_in0; done.
        apply Hpower; done. move : Hsub0; apply substitute_cs_good_term. intros; apply Hterm. apply Hfind_cs_in0; done.
        apply Hterm; done.
    - clear Hsub0. case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in Heqnew_c.
      + subst new_c. move : H2; apply contra_not; intros. apply substitute_c_correctness.
        assert (forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done). clear H0.
        apply H1; done. move : Hsub1; apply substitute_cs_correctness. intros; apply Hterm.
        2: intros; apply Hpower. 1,2 : apply Hfind_cs_in1; done.
        assert (forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done). clear H0.
        apply forallb_forall; intros; apply H1; apply Hfind_cs_in1; done. apply Hpower; done.
        move : Hsub1; apply substitute_cs_power. intros; apply Hpower; apply Hfind_cs_in1; done.
        apply Hterm; done. move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm; apply Hfind_cs_in1; done.
      + subst new_c. move : H2; apply contra_not. intros; move : c H. apply forallb_forall; done. }
Qed.

Lemma no_ubs_unsat_case1 cs1 c coe var tbsolved g adj n initial : (forall c, List.In c cs1 -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs1 -> rhs_power c = nil) ->
  scc.build_graph cs1 = (g, adj) -> 
  (forall x, List.In x tbsolved -> exists p_hd p_tl, scc.find_path g x n [] (lhs_var1 c) None = Some (p_hd :: p_tl)) ->
  (forall x, List.In x tbsolved -> exists p_hd p_tl, scc.find_path g var n [] x None = Some (p_hd :: p_tl)) ->
  List.find (fun c : Constraint1 => List.existsb (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) cs1 = Some c ->
  List.find (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c) = Some (coe, var) ->
  solve_ubs_case1 tbsolved c var g adj n initial = None -> 
  forall v, ~ forallb (satisfies_constraint1 v) cs1.
Proof.
  move : tbsolved initial. elim. simpl; intros; try discriminate. 
  simpl; intros hd tl IH initial Hterm Hpower Hbuild Hp0 Hp1; intros.
  case Hsolve_hd : (solve_ub_case1 hd c var g adj n) => [ub|]; rewrite Hsolve_hd in H1.
  - move : H1 v; apply IH; try done. intros; apply Hp0; right; done. intros; apply Hp1; right; done. 
  - move : H H0 Hsolve_hd v; apply no_ub_unsat_case1; try done. apply Hp0; left; done. apply Hp1; left; done.
Qed.

Lemma substitute_c_terms_gt'_helper coe_0 x term0 var1 coe1 : forall (term1 : list term), List.In (coe_0, x) term0 -> x <> var1 ->
  NoDup (List.split term1).2 ->
  exists coe : nat, List.In (coe, x) (fold_right
    (fun '(coe'0, var) (acc : seq term) =>
    match
      List.find (fun p : term => p.2 == var) acc
    with
    | Some t =>
        let (existing_coef, _) := t in
        (existing_coef + coe1 * coe'0, var)
        :: remove term_dec (existing_coef, var) acc
    | None => (coe1 * coe'0, var) :: acc
    end) (remove term_dec (coe1, var1) term0) term1).
Proof.
  intros term1 Hin Hneq; move : term1. elim.
  simpl; intros; clear H. exists coe_0. move : Hin; apply in_in_remove. intuition. inversion H; subst x. apply Hneq; done.
  simpl; intros [coe_hd var_hd] terms IH Hnodup.
  remember (fold_right
            (fun '(coe'0, var) (acc : seq term) =>
             match
               List.find (fun p : term => p.2 == var) acc
             with
             | Some t =>
                 let (existing_coef, _) := t in
                 (existing_coef + coe1 * coe'0, var)
                 :: remove term_dec (existing_coef, var) acc
             | None => (coe1 * coe'0, var) :: acc
             end) (remove term_dec (coe1, var1) term0) terms) as terms'. rewrite -Heqterms'; rewrite -Heqterms' in IH.
  destruct IH as [coe' Hin']. destruct (List.split terms) as [left right] eqn : Hsplit. simpl in Hnodup; simpl. apply NoDup_cons_iff in Hnodup; exact Hnodup.2.
  destruct (List.find (fun p : term => p.2 == var_hd) terms') as [[existing_coef var_hd']|].
  - destruct (x == var_hd) eqn : Heq; move /eqP : Heq => Heq. subst x. exists (existing_coef + coe1 * coe_hd); simpl; left; done.
    exists coe'; right. move : Hin'; apply in_in_remove. intuition. apply Heq. inversion H; done.
  - destruct (x == var_hd) eqn : Heq; move /eqP : Heq => Heq. subst x. exists (coe1 * coe_hd); simpl; left; done.
    exists coe'; right; done.
Qed.

Lemma substitute_coe_gt1' : forall (term0 term1 : list term) , good_terms term0 -> good_terms term1 ->
  forall coe1 (var1 : ProdVar.t), List.find (fun p : term => p.2 == var1) term0 = Some (coe1, var1) ->
  forall coe_0 coe_1 x, x <> var1 -> List.In (coe_0, x) term0 -> List.In (coe_1, x) term1 ->
  exists coe : nat,
  List.find (fun p : term => p.2 == x)
    (fold_right
      (fun '(coe'0, var) (acc : seq term) =>
        match List.find (fun p : term => p.2 == var) acc with
        | Some t =>
            let (existing_coef, _) := t in
            (existing_coef + coe1 * coe'0, var)
            :: remove term_dec (existing_coef, var) acc
        | None => (coe1 * coe'0, var) :: acc
        end) (remove term_dec (coe1, var1) term0) 
      term1) = Some (coe, x) /\ 1 < coe.
Proof.
  intros term0; elim. simpl; intros; done.
  intros [hd_coe hd_var] tl1 IH Hterm0 Hterm1 coe1 var1 Hfind; intros; simpl. simpl in H1; destruct H1.
  - inversion H1; clear H1. subst hd_coe hd_var. clear IH.
    remember (fold_right
        (fun '(coe'0, var) (acc : seq term) =>
          match
            List.find (fun p : term => p.2 == var) acc
          with
          | Some t =>
              let (existing_coef, _) := t in
              (existing_coef + coe1 * coe'0, var)
              :: remove term_dec (existing_coef, var) acc
          | None => (coe1 * coe'0, var) :: acc
          end) (remove term_dec (coe1, var1) term0) tl1) as term'. rewrite -Heqterm'.
    assert (good_terms term').
    { assert (good_terms (remove term_dec (coe1, var1) term0)). apply good_terms_remove; done.
      assert (good_terms tl1). move : Hterm1; clear; unfold good_terms; intros. move : Hterm1 => [Hgt Hnodup].
        split. intros. apply (Hgt _ var); simpl; right; done. simpl in Hnodup. destruct (List.split tl1) as [left right]. simpl in Hnodup; apply NoDup_cons_iff in Hnodup. exact Hnodup.2.
      assert (coe1 <> 0). unfold good_terms in Hterm0; move : Hterm0 => [Hterm0 _]. apply find_some in Hfind; move : Hfind => [Hfind _]. apply Hterm0 in Hfind. destruct coe1; try done.
      specialize (substitute_good_terms H1 H2 H3); intro. rewrite -Heqterm' in H4; done. }
    assert (exists coe, List.In (coe, x) term'). rewrite Heqterm'; apply substitute_c_terms_gt'_helper with (coe_0 := coe_0); try done. 
      move : Hterm1; clear; intros. unfold good_terms in Hterm1; move : Hterm1 => [_ Hterm1]. simpl in Hterm1. destruct (List.split tl1) as [left right].
      simpl in Hterm1. apply NoDup_cons_iff in Hterm1. exact Hterm1.2.
    destruct H2 as [coe' H2]. apply in_nodup_find_some in H2. rewrite H2.
    simpl; rewrite eqxx. exists (coe' + coe1 * coe_1); split; try done.
    { assert (coe' > 0). unfold good_terms in H1; move : H1 => [H1 _]. apply find_some in H2; move : H2 => [H2 _]. apply H1 in H2. destruct coe'; try done.
      assert (coe1 * coe_1 > 0). rewrite muln_gt0. apply rwP with (P := (0 < coe1) /\ (0 < coe_1)). apply andP. split. apply find_some in Hfind; move : Hfind => [Hfind _].
        unfold good_terms in Hterm0; move : Hterm0 => [Hterm0 _]. apply Hterm0 in Hfind. destruct coe1; try done.
        unfold good_terms in Hterm1; move : Hterm1 => [Hterm1 _]. specialize (in_eq (coe_1,x) tl1); intro. apply Hterm1 in H4. destruct coe_1; try done.
      specialize (leq_add H3 H4); intro. done. } unfold good_terms in H1. exact H1.2.
    - remember (fold_right
      (fun '(coe'0, var) (acc : seq term) =>
      match List.find (fun p : term => p.2 == var) acc with
      | Some t =>
          let (existing_coef, _) := t in
          (existing_coef + coe1 * coe'0, var)
          :: remove term_dec (existing_coef, var) acc
      | None => (coe1 * coe'0, var) :: acc
      end) (remove term_dec (coe1, var1) term0) tl1) as new_term. rewrite -Heqnew_term.
    assert (exists coe : nat, List.find (fun p : term => p.2 == x) new_term  = Some (coe, x) /\ 1 < coe).
    { rewrite Heqnew_term; apply IH with (coe_0 := coe_0) (coe_1 := coe_1); try done. move : Hterm1; clear; unfold good_terms; intros.
      move : Hterm1 => [Hin Hnodup]; split. intros; apply (Hin _ var); simpl; right; done.
      simpl in Hnodup. destruct (List.split tl1) as [left right] eqn : Hsplit. simpl in Hnodup. apply NoDup_cons_iff in Hnodup. simpl; exact Hnodup.2. }
    destruct H2 as [coe [Hfind_new Hgt]]. clear IH. exists coe; split; try done; clear Hgt.
    assert (x <> hd_var). { move : Hterm1 H1; clear; intros. unfold good_terms in Hterm1. move : Hterm1 => [_ Hterm]. 
      simpl in Hterm. destruct (List.split tl1) as [left right] eqn : Hsplit. simpl in Hterm. apply NoDup_cons_iff in Hterm; move : Hterm => [Hterm _].
      apply in_split_r in H1. rewrite Hsplit in H1; simpl in H1. intuition; subst x; apply Hterm in H1; done. }
    case Hfind0 : (List.find (fun p : term => p.2 == hd_var) new_term) => [[a b]|].
    rewrite -(find_cons_neq _ _ hd_var (a + coe1 * hd_coe)); try done. rewrite -(find_remove_neq _ _ hd_var a) //; try done.
    rewrite -(find_cons_neq _ _ hd_var (coe1 * hd_coe)); try done.
Qed.

Lemma substitute_c_terms_gt' c c_hd : good_terms (rhs_terms1 c) ->
  forall coe var, List.In (coe, var) (rhs_terms1 c_hd) -> var <> (lhs_var1 c) -> exists coe' : nat, List.In (coe', var) (rhs_terms1 (substitute_c c_hd c)).
Proof.
  rewrite /substitute_c /substitute_constraint; intros Hterm; intros.
  case Hfind : (List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c_hd)) => [[coe_c x]|]. simpl.
  apply substitute_c_terms_gt'_helper with (coe_0 := coe); try done. unfold good_terms in Hterm. exact Hterm.2.
  exists coe; done.
Qed.

Lemma find_constraints_of_path_not_nil adj p_hd p_tl cs : find_constraints_of_path adj p_hd p_tl = Some cs -> cs <> nil -> p_tl <> nil.
Proof.
  move : p_tl p_hd cs. elim. simpl; intros. inversion H; subst cs; done.
  simpl; intros. done.
Qed.

Lemma find_path_gt1 g a n b res : scc.find_path g a n [] b None = Some res -> List.length res > 1 -> b <> a.
Proof.
  move : n b res. elim. simpl; intros. destruct (b == a) eqn : Heq; move /eqP : Heq => Heq; try done. inversion H; subst res. simpl in H0; done.
  intros. simpl in H0. destruct (b == a) eqn : Heq; move /eqP : Heq => Heq; try done. inversion H0; subst res. simpl in H1; done.
Qed.

Lemma no_ub_unsat_case2 cs c coe0 var0 coe1 var1 tl' x g adj n : (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs -> rhs_power c = nil) ->
  scc.build_graph cs = (g, adj) ->
  (exists p_hd p_tl, scc.find_path g x n [] (lhs_var1 c) None = Some (p_hd :: p_tl)) ->
  (exists p_hd p_tl, scc.find_path g var0 n [] x None = Some (p_hd :: p_tl)) ->
  (exists p_hd p_tl, scc.find_path g var1 n [] x None = Some (p_hd :: p_tl)) ->
  List.find (fun c : Constraint1 => 1 < Datatypes.length (rhs_terms1 c)) cs = Some c ->
  rhs_terms1 c = [:: (coe0, var0), (coe1, var1) & tl'] ->
  solve_ub_case2 x c var0 var1 g adj n = None -> 
  forall v, ~ forallb (satisfies_constraint1 v) cs.
Proof.
  intros Hterm Hpower Hbuild Hp0 Hp1 Hp2; intros. rewrite /solve_ub_case2 in H1.
  destruct Hp0 as [p0_hd [p0_tl Hp0]]. rewrite Hp0 in H1.
  destruct Hp1 as [p1_hd [p1_tl Hp1]]. rewrite Hp1 in H1.
  destruct Hp2 as [p2_hd [p2_tl Hp2]]. rewrite Hp2 in H1.
  assert (Hcs0 : exists cs0, find_constraints_of_path adj p0_hd p0_tl = Some cs0) by (move : Hbuild Hterm Hp0; apply find_constraints_of_path_exists).
  destruct Hcs0 as [cs0 Hcs0]. rewrite Hcs0 in H1.
  assert (Hcs1 : exists cs1, find_constraints_of_path adj p1_hd p1_tl = Some cs1) by (move : Hbuild Hterm Hp1; apply find_constraints_of_path_exists).
  destruct Hcs1 as [cs1 Hcs1]. rewrite Hcs1 in H1. 
  assert (Hcs2 : exists cs2, find_constraints_of_path adj p2_hd p2_tl = Some cs2) by (move : Hbuild Hterm Hp2; apply find_constraints_of_path_exists).
  destruct Hcs2 as [cs2 Hcs2]. rewrite Hcs2 in H1. 
  remember (match substitute_cs cs0 with
    | Some c0 =>
      match substitute_cs cs1 with
      | Some c1 =>
          match substitute_cs cs2 with
          | Some c2 => substitute_c c0 (substitute_c (substitute_c c c1) c2)
          | None => substitute_c c0 (substitute_c c c1)
          end
      | None =>
          match substitute_cs cs2 with
          | Some c2 => substitute_c c0 (substitute_c c c2)
          | None => substitute_c c0 c
          end
      end
    | None =>
      match substitute_cs cs1 with
      | Some c1 =>
          match substitute_cs cs2 with
          | Some c2 => substitute_c (substitute_c c c1) c2
          | None => substitute_c c c1
          end
      | None => match substitute_cs cs2 with
                | Some c2 => substitute_c c c2
                | None => c
                end
      end
    end) as new_c.
  assert (exists coe, List.find (fun p : term => p.2 == lhs_var1 new_c) (rhs_terms1 new_c) = Some (coe, lhs_var1 new_c) /\ coe > 1).
  { clear H1.
    case Hsub0 : (substitute_cs cs0) => [c0|]; rewrite Hsub0 in Heqnew_c.
    - assert (lhs_var1 c0 = x /\ exists coe, List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c0) = Some (coe, lhs_var1 c)) by
        (move : Hbuild Hterm Hp0 Hcs0 Hsub0; apply substitute_cs_helper).
      case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in Heqnew_c.
      + assert (lhs_var1 c1 = var0 /\ exists coe, List.find (fun p : term => p.2 == x) (rhs_terms1 c1) = Some (coe, x)) by
          (move : Hbuild Hterm Hp1 Hcs1 Hsub1; apply substitute_cs_helper).
        case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in Heqnew_c.
        * assert (lhs_var1 c2 = var1 /\ exists coe, List.find (fun p : term => p.2 == x) (rhs_terms1 c2) = Some (coe, x)) by
            (move : Hbuild Hterm Hp2 Hcs2 Hsub2; apply substitute_cs_helper).
          move : H1 => [Heq0 [coe_0 Hfind0]]; move : H2 => [Heq1 [coe_1 Hfind1]]; move : H3 => [Heq2 [coe_2 Hfind2]]. subst x var0 var1. 
          remember (substitute_c c c1) as c1'. remember (substitute_c c1' c2) as c2'.
          rewrite /substitute_c /substitute_constraint in Heqnew_c.
          specialize (substitute_c_lhs_eq c c1); intro. rewrite -Heqc1' in H1.
          specialize (substitute_c_lhs_eq c1' c2); intro. rewrite -Heqc2' in H2. rewrite H2 H1 Hfind0 in Heqnew_c.
          rewrite Heqnew_c; simpl. assert (exists coe, List.find (fun p : term => p.2 == lhs_var1 c0) (rhs_terms1 c2') = Some (coe, lhs_var1 c0) /\ coe > 1). 
          { clear Heqnew_c. rewrite Heqc2' /substitute_c /substitute_constraint. 
            assert (exists coe, List.In (coe, lhs_var1 c2) (rhs_terms1 c1')).
            { rewrite Heqc1'; apply substitute_c_terms_gt' with (coe := coe1). 2: rewrite H0; simpl; right; left; done. 
              move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm. move : Hbuild Hcs1 c3 H3; apply find_constraints_of_path_subset; done. 
              move : H0 Hterm H; clear; intros. apply find_some in H; move : H => [H _]. apply Hterm in H; clear Hterm. unfold good_terms in H; move : H => [_ H].
               rewrite H0 in H; simpl in H. destruct (List.split tl') as [left right]; simpl in H. apply NoDup_cons_iff in H; move : H => [H _]. simpl in H. 
               apply Decidable.not_or in H. exact H.1. }
            destruct H3 as [coe2' Hfind2']. apply in_nodup_find_some in Hfind2'. rewrite Hfind2'; simpl. 
            assert (exists coe, List.In (coe, lhs_var1 c0) (rhs_terms1 c1') /\ coe_1 <= coe). 
            { rewrite Heqc1'. apply substitute_c_terms_gt. rewrite H0; exists coe0; simpl; left; done.
              apply Hterm; apply find_some in H; exact H.1. move : Hsub1; apply substitute_cs_good_term. 
              intros; apply Hterm. move : Hbuild Hcs1 c3 H3; apply find_constraints_of_path_subset; try done.
              apply find_some in Hfind1; exact Hfind1.1. }
            destruct H3 as [coe1' [Hin1' Hge1']]. apply find_some in Hfind2; move : Hfind2 => [Hfind2 _].
            move : Hin1' Hfind2. apply substitute_coe_gt1'; try done.
            rewrite Heqc1'. apply substitute_c_good_term. 2 : move : Hsub1. 3 : move : Hsub2. 2,3: apply substitute_cs_good_term; intros.
            1,2,3 : apply Hterm. apply find_some in H; exact H.1. move : Hbuild Hcs1 c3 H3; apply find_constraints_of_path_subset; try done.
            move : Hbuild Hcs2 c3 H3; apply find_constraints_of_path_subset; try done. 
            move : Hp2 Hcs2 Hsub2; clear; intros. apply substitute_cs_some in Hsub2. apply (find_constraints_of_path_not_nil _ _ _ _ Hcs2) in Hsub2.
              apply find_path_gt1 in Hp2; try done. destruct p2_tl; try done.
            assert (good_terms (rhs_terms1 c1')). rewrite Heqc1'; apply substitute_c_good_term. apply Hterm. apply find_some in H; exact H.1.
              move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm. move : Hbuild Hcs1 c3 H3; apply find_constraints_of_path_subset; done.
            unfold good_terms in H3; exact H3.2. }
          destruct H3 as [coe' [Hin' Hgt']]. apply find_some in Hin'; move : Hin' => [Hin' _]. apply substitute_coe_gt1 with (coe' := coe'); try done.
          clear Heqnew_c. rewrite Heqc2'; apply substitute_c_good_term. rewrite Heqc1'; apply substitute_c_good_term.
          apply Hterm; apply find_some in H; exact H.1.
          move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm. move : Hbuild Hcs1 c3 H3; apply find_constraints_of_path_subset; try done.
          move : Hsub2; apply substitute_cs_good_term. intros; apply Hterm. move : Hbuild Hcs2 c3 H3; apply find_constraints_of_path_subset; try done. right; done.
          apply substitute_cs_good_term in Hsub0. unfold good_terms in Hsub0; move : Hsub0 => [Hsub0 _]. apply find_some in Hfind0; move : Hfind0 => [Hfind0 _]. apply Hsub0 in Hfind0. destruct coe_0; try done.
          intros; apply Hterm. move : Hbuild Hcs0 c3 H3; apply find_constraints_of_path_subset; try done. intuition.
        * apply substitute_cs_none in Hsub2. subst cs2. apply find_constraints_of_path_nil in Hcs2. subst p2_tl.
          apply find_path_1 in Hp2. subst x. move : H1 => [H1 [coe_0 Hfind0]]. move : H2 => [H2 [coe_1 Hfind1]]. subst var0 var1.
          remember (substitute_c c c1) as c1'. rewrite /substitute_c /substitute_constraint in Heqnew_c.
          specialize (substitute_c_lhs_eq c c1); intro. rewrite -Heqc1' in H1. rewrite H1 Hfind0 in Heqnew_c.
          rewrite Heqnew_c; simpl. assert (exists coe, List.find (fun p : term => p.2 == lhs_var1 c0) (rhs_terms1 c1') = Some (coe, lhs_var1 c0) /\ coe > 1). 
          { clear Heqnew_c. rewrite Heqc1' /substitute_c /substitute_constraint. 
            assert (List.In (coe0, lhs_var1 c1) (rhs_terms1 c)) by (rewrite H0; simpl; left; done).
            apply in_nodup_find_some in H2. rewrite H2; simpl. clear H2 H1.
            assert (List.In (coe1, lhs_var1 c0) (rhs_terms1 c)) by (rewrite H0; simpl; right; left; done).
            apply find_some in Hfind1; move : Hfind1 => [Hfind1 _]. move : H1 Hfind1; apply substitute_coe_gt1'; try done.
              apply Hterm. apply find_some in H; exact H.1. move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm.
              move : Hbuild Hcs1 c2 H1; apply find_constraints_of_path_subset; done.
            apply in_nodup_find_some. rewrite H0; simpl; left; done. 1-3 : apply find_some in H; move : H => [H _]; apply Hterm in H; unfold good_terms in H. 1,3 : exact H.2.
            move : H => [_ H]. rewrite H0 in H. simpl in H. destruct (List.split tl') as [left right]; simpl in H. apply NoDup_cons_iff in H; move : H => [H _]. simpl in H. 
              apply Decidable.not_or in H. exact H.1. }
          destruct H2 as [coe' [Hin' Hgt']]. apply find_some in Hin'; move : Hin' => [Hin' _]. apply substitute_coe_gt1 with (coe' := coe'); try done.
          clear Heqnew_c. rewrite Heqc1'; apply substitute_c_good_term. apply Hterm; apply find_some in H; exact H.1.
          move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm. move : Hbuild Hcs1 c2 H2; apply find_constraints_of_path_subset; try done. right; done.
          apply substitute_cs_good_term in Hsub0. unfold good_terms in Hsub0; move : Hsub0 => [Hsub0 _]. apply find_some in Hfind0; move : Hfind0 => [Hfind0 _]. apply Hsub0 in Hfind0. destruct coe_0; try done.
          intros; apply Hterm. move : Hbuild Hcs0 c2 H2; apply find_constraints_of_path_subset; try done. intuition.
      + apply substitute_cs_none in Hsub1. subst cs1. apply find_constraints_of_path_nil in Hcs1. subst p1_tl. apply find_path_1 in Hp1. subst x. 
        case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in Heqnew_c.
        * assert (lhs_var1 c2 = var1 /\ exists coe, List.find (fun p : term => p.2 == var0) (rhs_terms1 c2) = Some (coe, var0)) by
            (move : Hbuild Hterm Hp2 Hcs2 Hsub2; apply substitute_cs_helper).
          move : H1 => [Heq0 [coe_0 Hfind0]]; move : H2 => [Heq2 [coe_2 Hfind2]]. subst var0 var1. 
          remember (substitute_c c c2) as c2'. rewrite /substitute_c /substitute_constraint in Heqnew_c.
          specialize (substitute_c_lhs_eq c c2); intro. rewrite -Heqc2' in H1. rewrite H1 Hfind0 in Heqnew_c.
          rewrite Heqnew_c; simpl. assert (exists coe, List.find (fun p : term => p.2 == lhs_var1 c0) (rhs_terms1 c2') = Some (coe, lhs_var1 c0) /\ coe > 1). 
          { clear Heqnew_c. rewrite Heqc2' /substitute_c /substitute_constraint. 
            assert (List.In (coe1, lhs_var1 c2) (rhs_terms1 c)) by (rewrite H0; simpl; right; left; done).
            apply in_nodup_find_some in H2. rewrite H2; simpl. clear H2 H1.
            assert (List.In (coe0, lhs_var1 c0) (rhs_terms1 c)) by (rewrite H0; simpl; left; done).
            apply find_some in Hfind2; move : Hfind2 => [Hfind2 _]. move : H1 Hfind2; apply substitute_coe_gt1'; try done.
              apply Hterm. apply find_some in H; exact H.1. move : Hsub2; apply substitute_cs_good_term. intros; apply Hterm.
              move : Hbuild Hcs2 c1 H1; apply find_constraints_of_path_subset; done.
            apply in_nodup_find_some. rewrite H0; simpl; right; left; done. 1-3 : apply find_some in H; move : H => [H _]; apply Hterm in H; unfold good_terms in H. 1,3 : exact H.2.
            move : H => [_ H]. rewrite H0 in H. simpl in H. destruct (List.split tl') as [left right]; simpl in H. apply NoDup_cons_iff in H; move : H => [H _]. simpl in H. 
              apply Decidable.not_or in H; move : H => [H _]. intuition. }
          destruct H2 as [coe' [Hin' Hgt']]. apply find_some in Hin'; move : Hin' => [Hin' _]. apply substitute_coe_gt1 with (coe' := coe'); try done.
          clear Heqnew_c. rewrite Heqc2'; apply substitute_c_good_term. apply Hterm; apply find_some in H; exact H.1.
          move : Hsub2; apply substitute_cs_good_term. intros; apply Hterm. move : Hbuild Hcs2 c1 H2; apply find_constraints_of_path_subset; try done. right; done.
          apply substitute_cs_good_term in Hsub0. unfold good_terms in Hsub0; move : Hsub0 => [Hsub0 _]. apply find_some in Hfind0; move : Hfind0 => [Hfind0 _]. apply Hsub0 in Hfind0. destruct coe_0; try done.
          intros; apply Hterm. move : Hbuild Hcs0 c1 H2; apply find_constraints_of_path_subset; try done. intuition.
        * apply substitute_cs_none in Hsub2. subst cs2. apply find_constraints_of_path_nil in Hcs2. subst p2_tl. apply find_path_1 in Hp2. subst var0.
          move : H0 Hterm H; clear. intros. apply find_some in H; move : H => [H _]. apply Hterm in H; clear Hterm.
          unfold good_terms in H; move : H => [_ H]. rewrite H0 in H; clear H0. simpl in H. destruct (List.split tl') as [left right]; simpl in H.
          apply NoDup_cons_iff in H; move : H => [H _]. intuition.
    - apply substitute_cs_none in Hsub0. subst cs0. apply find_constraints_of_path_nil in Hcs0. subst p0_tl. apply find_path_1 in Hp0. subst x.
      case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in Heqnew_c.
      + assert (lhs_var1 c1 = var0 /\ exists coe, List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c1) = Some (coe, lhs_var1 c)) by
          (move : Hbuild Hterm Hp1 Hcs1 Hsub1; apply substitute_cs_helper).
        case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in Heqnew_c.
        * assert (lhs_var1 c2 = var1 /\ exists coe, List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c2) = Some (coe, lhs_var1 c)) by
            (move : Hbuild Hterm Hp2 Hcs2 Hsub2; apply substitute_cs_helper).
          move : H1 => [Heq1 [coe_1 Hfind1]]; move : H2 => [Heq2 [coe_2 Hfind2]]. subst var0 var1.
          remember (substitute_c c c1) as c1'. 
          specialize (substitute_c_lhs_eq c c1); intro. rewrite -Heqc1' in H1.
          specialize (substitute_c_lhs_eq c1' c2); intro. rewrite -Heqnew_c in H2. rewrite H2 H1. clear H1 H2.
          rewrite /substitute_c /substitute_constraint in Heqnew_c.
          assert (exists coe, List.In (coe, lhs_var1 c2) (rhs_terms1 c1')).
          { clear Heqnew_c. rewrite Heqc1'; apply substitute_c_terms_gt' with (coe := coe1). 2: rewrite H0; simpl; right; left; done. 
            move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm. move : Hbuild Hcs1 c0 H1; apply find_constraints_of_path_subset; done. 
            move : H0 Hterm H; clear; intros. apply find_some in H; move : H => [H _]. apply Hterm in H; clear Hterm. unfold good_terms in H; move : H => [_ H].
             rewrite H0 in H; simpl in H. destruct (List.split tl') as [left right]; simpl in H. apply NoDup_cons_iff in H; move : H => [H _]. simpl in H. 
             apply Decidable.not_or in H. exact H.1. }
          assert (good_terms (rhs_terms1 c1')).
          { rewrite Heqc1'; apply substitute_c_good_term. apply Hterm; apply find_some in H; exact H.1.
            move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm. move : Hbuild Hcs1 c0 H2; apply find_constraints_of_path_subset; try done. }
          destruct H1 as [coe2' Hfind2']. apply in_nodup_find_some in Hfind2'. rewrite Hfind2' in Heqnew_c; simpl in Heqnew_c. 
          rewrite Heqnew_c; simpl. clear Heqnew_c.
          assert (exists coe, List.In (coe, lhs_var1 c) (rhs_terms1 c1') /\ coe_1 <= coe).
          { rewrite Heqc1'; apply substitute_c_terms_gt. exists coe0; rewrite H0; simpl; left; done.
            apply Hterm. apply find_some in H; exact H.1. move : Hsub1; apply substitute_cs_good_term. intros; apply Hterm. move : Hbuild Hcs1 c0 H1; apply find_constraints_of_path_subset; try done.
            apply find_some in Hfind1; exact Hfind1.1. } destruct H1 as [coe1' [H1 _]].
          apply find_some in Hfind2; move : Hfind2 => [Hfind2 _].
          move : H1 Hfind2; apply substitute_coe_gt1'; try done.
          move : Hsub2; apply substitute_cs_good_term. intros; apply Hterm. move : Hbuild Hcs2 c0 H1; apply find_constraints_of_path_subset; try done.
          apply substitute_cs_some in Hsub2. apply (find_constraints_of_path_not_nil _ _ _ _ Hcs2) in Hsub2.
            apply find_path_gt1 in Hp2; try done. destruct p2_tl; try done.
          unfold good_terms in H2; exact H2.2.
        * apply substitute_cs_none in Hsub2. subst cs2. apply find_constraints_of_path_nil in Hcs2. subst p2_tl. apply find_path_1 in Hp2. subst var1.
          move : H1 => [Heq0 [coe_0 Hfind0]]; subst var0. rewrite Heqnew_c /substitute_c /substitute_constraint.
          assert (List.In (coe0, lhs_var1 c1) (rhs_terms1 c)) by (rewrite H0; simpl; left; done). 
          apply in_nodup_find_some in H1. rewrite H1; simpl.
          assert (List.In (coe1, lhs_var1 c) (rhs_terms1 c)) by (rewrite H0; simpl; right; left; done). 
          assert (List.In (coe_0, lhs_var1 c) (rhs_terms1 c1)) by (apply find_some in Hfind0; exact Hfind0.1).
          move : H2 H3; apply substitute_coe_gt1'; try done.
          apply Hterm; apply find_some in H; exact H.1.
          move : Hsub1; apply substitute_cs_good_term; intros. apply Hterm. move : Hbuild Hcs1 c0 H2; apply find_constraints_of_path_subset; try done.
          move : H H0 Hterm; clear; intros. 1,2 : apply find_some in H; move : H => [H _]; apply Hterm in H; clear Hterm; unfold good_terms in H; move : H => [_ H]; try done.
            rewrite H0 in H; simpl in H. destruct (List.split tl') as [left right]; simpl in H. apply NoDup_cons_iff in H; move : H => [H _]. simpl in H. 
            apply Decidable.not_or in H. exact H.1. 
      + apply substitute_cs_none in Hsub1. subst cs1. apply find_constraints_of_path_nil in Hcs1. subst p1_tl. apply find_path_1 in Hp1. subst var0.
        case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in Heqnew_c.
        * assert (lhs_var1 c2 = var1 /\ exists coe, List.find (fun p : term => p.2 == lhs_var1 c) (rhs_terms1 c2) = Some (coe, lhs_var1 c)) by
            (move : Hbuild Hterm Hp2 Hcs2 Hsub2; apply substitute_cs_helper).
          move : H1 => [Heq2 [coe_2 Hfind2]]. subst var1. rewrite Heqnew_c /substitute_c /substitute_constraint.
          assert (List.In (coe1, lhs_var1 c2) (rhs_terms1 c)) by (rewrite H0; simpl; right; left; done). 
          apply in_nodup_find_some in H1. rewrite H1; simpl.
          assert (List.In (coe0, lhs_var1 c) (rhs_terms1 c)) by (rewrite H0; simpl; left; done). 
          assert (List.In (coe_2, lhs_var1 c) (rhs_terms1 c2)) by (apply find_some in Hfind2; exact Hfind2.1).
          move : H2 H3; apply substitute_coe_gt1'; try done.
          apply Hterm; apply find_some in H; exact H.1.
          move : Hsub2; apply substitute_cs_good_term; intros. apply Hterm. move : Hbuild Hcs2 c0 H2; apply find_constraints_of_path_subset; try done.
          move : H H0 Hterm; clear; intros. 1,2 : apply find_some in H; move : H => [H _]; apply Hterm in H; clear Hterm; unfold good_terms in H; move : H => [_ H]; try done.
            rewrite H0 in H; simpl in H. destruct (List.split tl') as [left right]; simpl in H. apply NoDup_cons_iff in H; move : H => [H _]. simpl in H. 
            apply Decidable.not_or in H; move : H => [H _]. intuition.
        * subst c. apply substitute_cs_none in Hsub2. subst cs2. apply find_constraints_of_path_nil in Hcs2. subst p2_tl. apply find_path_1 in Hp2. subst var1.
          move : H0 Hterm H; clear. intros. apply find_some in H; move : H => [H _]. apply Hterm in H; clear Hterm.
          unfold good_terms in H; move : H => [_ H]. rewrite H0 in H; clear H0. simpl in H. destruct (List.split tl') as [left right]; simpl in H.
          apply NoDup_cons_iff in H; move : H => [H _]. intuition. }
  specialize (no_compute_ub_unsat _ H2 H1 v); clear H2; intro.
  specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs0) as Hfind_cs_in0.
  specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs1) as Hfind_cs_in1.
  specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs2) as Hfind_cs_in2.
  apply find_some in H; move : H => [H _].
  move : Heqnew_c H2 Hpower Hterm Hfind_cs_in0 Hfind_cs_in1 Hfind_cs_in2 H; clear; intros.
  { case Hsub0 : (substitute_cs cs0) => [c0|]; rewrite Hsub0 in Heqnew_c.
    - case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in Heqnew_c.
      * case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in Heqnew_c.
        + subst new_c. move : H2; apply contra_not; intros.
          assert (forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done). clear H0.
          apply substitute_c_correctness.
          move : Hsub0; apply substitute_cs_correctness. 5 : move : Hsub0; apply substitute_cs_power.
          7 : move : Hsub0; apply substitute_cs_good_term.
          1,7 : intros; apply Hterm. 3,6: intros; apply Hpower. 5: apply forallb_forall; intros; apply H1.
          1-5 : apply Hfind_cs_in0; done. 
          apply substitute_c_correctness. apply substitute_c_correctness. 8,12 : apply substitute_c_power. 10:apply substitute_c_power.
          14,16 : apply substitute_c_good_term. 16: apply substitute_c_good_term. apply H1; done.
          2,7,9 : apply Hpower; done. 3,10,12: apply Hterm; done. 
          move : Hsub1; apply substitute_cs_correctness. 4,7,8 : move : Hsub1; apply substitute_cs_power. 7,11,12 : move : Hsub1; apply substitute_cs_good_term.
          1-9 : intros. 1,7-9 : apply Hterm. 5,7-9 : apply Hpower. 9: apply forallb_forall; intros; apply H1. 1-9 : apply Hfind_cs_in1; done.
          1-5 : move : Hsub2. apply substitute_cs_correctness. 4,5 : apply substitute_cs_power. 6,7 : apply substitute_cs_good_term. 3: apply forallb_forall.
          1-7 : intros. 1,6,7 : apply Hterm. 4,6,7 : apply Hpower. 7: apply H1. 1-7 : apply Hfind_cs_in2; done.
        + subst new_c. move : H2; apply contra_not; intros.
          assert (forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done). clear H0.
          apply substitute_c_correctness. clear Hsub2.
          2 : apply substitute_c_correctness. 9 : apply substitute_c_power. 12 : apply substitute_c_good_term.
          2 : apply H1; done. 3,8 : apply Hpower;done. 4,9 : apply Hterm; done.
          1,5,7 : move : Hsub0. apply substitute_cs_correctness. 4 : apply substitute_cs_power. 5 : apply substitute_cs_good_term. 3 : apply forallb_forall.
          1-5 : intros. 1,5 : apply Hterm. 3,5 : apply Hpower. 5 : apply H1. 1-5 : apply Hfind_cs_in0; done. 
          1-5 : move : Hsub1. apply substitute_cs_correctness. 4,6 : apply substitute_cs_power. 6,7 : apply substitute_cs_good_term. 3 : apply forallb_forall.
          1-7 : intros. 1,6,7 : apply Hterm. 4,6,7 : apply Hpower. 7 : apply H1. 1-7 : apply Hfind_cs_in1; done.
      * case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in Heqnew_c.
        + subst new_c. move : H2; apply contra_not; intros.
          assert (forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done). clear H0.
          apply substitute_c_correctness. clear Hsub1.
          2 : apply substitute_c_correctness. 9 : apply substitute_c_power. 12 : apply substitute_c_good_term.
          2 : apply H1; done. 3,8 : apply Hpower;done. 4,9 : apply Hterm; done.
          1,5,7 : move : Hsub0. apply substitute_cs_correctness. 4 : apply substitute_cs_power. 5 : apply substitute_cs_good_term. 3 : apply forallb_forall.
          1-5 : intros. 1,5 : apply Hterm. 3,5 : apply Hpower. 5 : apply H1. 1-5 : apply Hfind_cs_in0; done. 
          1-5 : move : Hsub2. apply substitute_cs_correctness. 4,6 : apply substitute_cs_power. 6,7 : apply substitute_cs_good_term. 3 : apply forallb_forall.
          1-7 : intros. 1,6,7 : apply Hterm. 4,6,7 : apply Hpower. 7 : apply H1. 1-7 : apply Hfind_cs_in2; done.
        + subst new_c. move : H2; apply contra_not. intros.
          assert (forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done). clear H0.
          apply substitute_c_correctness. clear Hsub1 Hsub2.
          2 : apply H1; done. 3 : apply Hpower;done. 4 : apply Hterm; done.
          1-3 : move : Hsub0. apply substitute_cs_correctness. 3 : apply forallb_forall. 4 : apply substitute_cs_power. 5 : apply substitute_cs_good_term.
          1-5 : intros. 1,5 : apply Hterm. 3,5 : apply Hpower. 5 : apply H1. 1-5 : apply Hfind_cs_in0; done.
    - case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in Heqnew_c.
      * case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in Heqnew_c.
        + subst new_c. move : H2; apply contra_not; intros.
          assert (forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done). clear H0.
          apply substitute_c_correctness. clear Hsub0.
          apply substitute_c_correctness. 8 : apply substitute_c_power. 11 : apply substitute_c_good_term.
          apply H1; done. 2,7: apply Hpower;done. 3,8 : apply Hterm; done.
          1-3,5,7 : move : Hsub1. apply substitute_cs_correctness. 4,6 : apply substitute_cs_power. 6,7 : apply substitute_cs_good_term. 3 : apply forallb_forall.
          1-7 : intros. 1,6,7 : apply Hterm. 4,6,7 : apply Hpower. 7 : apply H1. 1-7 : apply Hfind_cs_in1; done. 
          1-3 : move : Hsub2. apply substitute_cs_correctness. 4 : apply substitute_cs_power. 5 : apply substitute_cs_good_term. 3 : apply forallb_forall.
          1-5 : intros. 1,5 : apply Hterm. 3,5 : apply Hpower. 5 : apply H1. 1-5 : apply Hfind_cs_in2; done.
        + subst new_c. move : H2; apply contra_not; intros.
          assert (forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done). clear H0.
          apply substitute_c_correctness. clear Hsub0 Hsub2.
          apply H1; done. 2 : apply Hpower;done. 3 : apply Hterm; done.
          1-3 : move : Hsub1. apply substitute_cs_correctness. 4 : apply substitute_cs_power. 5 : apply substitute_cs_good_term. 3 : apply forallb_forall.
          1-5 : intros. 1,5 : apply Hterm. 3,5 : apply Hpower. 5 : apply H1. 1-5 : apply Hfind_cs_in1; done.
      * case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in Heqnew_c.
        + subst new_c. move : H2; apply contra_not. intros.
          assert (forall c, List.In c cs -> satisfies_constraint1 v c) by (apply forallb_forall; done). clear H0.
          apply substitute_c_correctness. clear Hsub1 Hsub0.
          apply H1; done. 2 : apply Hpower;done. 3 : apply Hterm; done.
          1-3 : move : Hsub2. apply substitute_cs_correctness. 3 : apply forallb_forall. 4 : apply substitute_cs_power. 5 : apply substitute_cs_good_term.
          1-5 : intros. 1,5 : apply Hterm. 3,5 : apply Hpower. 5 : apply H1. 1-5 : apply Hfind_cs_in2; done.
        + subst new_c. move : H2; apply contra_not. intros. move : c H; apply forallb_forall; done. }
Qed.

Lemma no_ubs_unsat_case2 cs1 c coe0 var0 coe1 var1 tl' tbsolved g adj n initial : (forall c, List.In c cs1 -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs1 -> rhs_power c = nil) ->
  scc.build_graph cs1 = (g, adj) ->
  (forall x, List.In x tbsolved -> exists p_hd p_tl, scc.find_path g x n [] (lhs_var1 c) None = Some (p_hd :: p_tl)) ->
  (forall x, List.In x tbsolved -> exists p_hd p_tl, scc.find_path g var0 n [] x None = Some (p_hd :: p_tl)) ->
  (forall x, List.In x tbsolved -> exists p_hd p_tl, scc.find_path g var1 n [] x None = Some (p_hd :: p_tl)) ->
  List.find (fun c : Constraint1 => 1 < Datatypes.length (rhs_terms1 c)) cs1 = Some c ->
  rhs_terms1 c = [:: (coe0, var0), (coe1, var1) & tl'] ->
  solve_ubs_case2 tbsolved c var0 var1 g adj n initial = None -> 
  forall v, ~ forallb (satisfies_constraint1 v) cs1.
Proof.
  move : tbsolved initial. elim. simpl; intros; try discriminate. 
  simpl; intros hd tl IH initial Hterm Hpower Hbuild Hp0 Hp1 Hp2; intros.
  case Hsolve_hd : (solve_ub_case2 hd c var0 var1 g adj n) => [ub|]; rewrite Hsolve_hd in H1.
  - move : H1 v; apply IH; try done. intros; apply Hp0; right; done. intros; apply Hp1; right; done. intros; apply Hp2; right; done. 
  - move : H H0 Hsolve_hd v; apply no_ub_unsat_case2; try done. apply Hp0; left; done. apply Hp1; left; done. apply Hp2; left; done.
Qed.

Definition scc_correctness (scc : list ProdVar.t) (cs : list Constraint1) : Prop := 
  forall a b g adj, List.In a scc -> List.In b scc -> build_graph cs = (g, adj) -> exists p_hd p_tl, scc.find_path g a (List.length scc) [] b None = Some (p_hd :: p_tl).

Axiom not_simple_scc_correctness : forall cs1 tbsolved, ~ is_simple_cycle cs1 -> 
  (forall var : ProdVar.t, List.In var (constraints1_vars cs1) -> List.In var tbsolved) -> 
  scc_correctness tbsolved cs1.

Lemma no_ubs_unsat cs1 tbsolved : ~ is_simple_cycle cs1 -> (*NoDup tbsolved -> tbsolved <> [] -> *)
  (forall var : ProdVar.t, List.In var (constraints1_vars cs1) -> List.In var tbsolved) -> 
  (forall c : Constraint1, List.In c cs1 -> rhs_power c = []) -> 
  (forall c : Constraint1, List.In c cs1 -> good_terms (rhs_terms1 c)) ->
  solve_ubs_aux tbsolved cs1 = None -> forall (v : Valuation), ~ forallb (satisfies_constraint1 v) cs1.
Proof.
  intros Hnot_simple Hvars_in_hd Hpower Hterm. specialize (not_simple_scc_correctness _ _ Hnot_simple Hvars_in_hd) as Hscc. rewrite /solve_ubs_aux. destruct (scc.build_graph cs1) as [g adj] eqn : Hgraph.
  case Hcase1 : (List.find (fun c : Constraint1 =>
    List.existsb (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) cs1) => [c|].
  - (* c : lhs >= coe * var + ... + cst c, coe > 1 *)
    intros. case Hfind_terms : (List.find (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) => [[coe var]|]; rewrite Hfind_terms in H.
    move : H v; generalize Hfind_terms; generalize Hcase1; apply no_ubs_unsat_case1; try done. 
    1,2:intros; unfold scc_correctness in Hscc; apply Hscc with (adj := adj); try done. 1,2:apply Hvars_in_hd;
    apply find_some in Hcase1; apply (constraint1_vars2constraints1_vars _ Hcase1.1). unfold constraint1_vars; simpl; left; done.
    unfold constraint1_vars; simpl. right. apply find_some in Hfind_terms; move : Hfind_terms => [Hfind_terms _]. apply in_split_r in Hfind_terms; simpl in Hfind_terms.
    apply in_or_app; left. rewrite -split2_eq_mapsnd //.
    apply find_some in Hcase1. destruct Hcase1 as [Hin Hexists]. apply existsb_exists in Hexists. destruct Hexists as [x [Hinx Hgt]].
    apply find_none with (x := x) in Hfind_terms; try done. rewrite Hgt in Hfind_terms; discriminate.
  case Hcase2 : (List.find (fun c : Constraint1 => 1 < Datatypes.length (rhs_terms1 c)) cs1) => [c|]. 
  - (* lhs >= coe0 * var0 + coe1 * var1 + ... + cst c *)
    intros. case Hterms_hd : (rhs_terms1 c) => [|[coe0 var0] tl]; rewrite Hterms_hd in H.
    apply find_some in Hcase2. destruct Hcase2 as [_ Hgt]. rewrite Hterms_hd in Hgt; simpl in Hgt. try done.
    case Hterms_hd' : tl => [|[coe1 var1] tl']; rewrite Hterms_hd' in H. rewrite Hterms_hd' in Hterms_hd.
    apply find_some in Hcase2. destruct Hcase2 as [_ Hgt]. rewrite Hterms_hd in Hgt; simpl in Hgt. try done. rewrite Hterms_hd' in Hterms_hd; clear Hterms_hd' tl.
    move : H v; generalize Hterms_hd; generalize Hcase2; apply no_ubs_unsat_case2; try done. 
    1-3:intros; unfold scc_correctness in Hscc; apply Hscc with (adj := adj); try done. 1-3:apply Hvars_in_hd;
    apply find_some in Hcase2; apply (constraint1_vars2constraints1_vars _ Hcase2.1). unfold constraint1_vars; simpl; left; done.
    1,2:unfold constraint1_vars; rewrite Hterms_hd; simpl; right. left; done. right; left; done.
  { intros; move : Hnot_simple Hcase1 Hcase2 Hterm; clear; intros.
  rewrite /is_simple_cycle in Hnot_simple. apply forallb_neg_neg in Hnot_simple.
  destruct Hnot_simple as [x [Hin Hrhs]]. case Hnil : (rhs_terms1 x) => [|[coe var] tl]; rewrite Hnil in Hrhs; try discriminate.
  assert (coe <> 0).
    { clear Hrhs. apply Hterm in Hin. rewrite Hnil /good_terms in Hin. apply (Hin.1 coe var). simpl; left; done. }
  case Hcoe0 : coe => [|n0]; rewrite Hcoe0 in Hrhs; try lia. case Hcoe1 : n0 => [|n]; rewrite Hcoe1 in Hrhs.
  case Htl : tl => [|a al]; rewrite Htl in Hrhs; try discriminate. clear Hrhs.
  rewrite Htl in Hnil. apply find_none with (x := x) in Hcase2; try done. rewrite Hnil in Hcase2; simpl in Hcase2. intuition.
  rewrite Hcoe1 in Hcoe0. apply find_none with (x := x) in Hcase1; try done. rewrite Hnil in Hcase1; simpl in Hcase1. rewrite Hcoe0 in Hcase1. 
  intuition. } 
Qed.

Lemma add_edge_of_cs'_mem_eq cs a var : PVM.mem var a -> PVM.mem var (add_edge_of_cs' cs a).
Proof.
  intro. move : cs. elim. simpl; done.
  simpl; intros hd tl IH. apply find_mem.
  case Hfind : (PVM.find (lhs_var1 hd) a) => [dst_map|]; try done. destruct (rhs_terms1 hd) as [|[n v] ts] eqn : Hterm.
  destruct (NVM.find Zero dst_map) as [dist|]. remember (NVM.add Zero (Z.max dist (rhs_const1 hd)) dst_map) as x.
  - destruct (var == (lhs_var1 hd)) eqn : Heq; move /eqP : Heq => Heq. subst var. exists x; apply find_add_eq.
    rewrite find_add_neq; try done. apply find_mem; done.
  - remember (NVM.add Zero (rhs_const1 hd) dst_map) as x. destruct (var == (lhs_var1 hd)) eqn : Heq; move /eqP : Heq => Heq.
    subst var. exists x; apply find_add_eq. rewrite find_add_neq; try done. apply find_mem; done.
  destruct n as [|n0]. 2 : destruct n0. 2: destruct ts. 
  1,3-5: apply find_mem; done.
  destruct (NVM.find (Node v) dst_map) as [dist|]. remember (NVM.add (Node v) (Z.max dist (rhs_const1 hd)) dst_map) as x.
  - destruct (var == (lhs_var1 hd)) eqn : Heq; move /eqP : Heq => Heq. subst var. exists x; apply find_add_eq.
    rewrite find_add_neq; try done. apply find_mem; done.
  - remember (NVM.add (Node v) (rhs_const1 hd) dst_map) as x. destruct (var == (lhs_var1 hd)) eqn : Heq; move /eqP : Heq => Heq.
    subst var. exists x; apply find_add_eq. rewrite find_add_neq; try done. apply find_mem; done.
Qed.

Lemma floyd_update'_mem_eq a b c d var : PVM.mem var d -> PVM.mem var (floyd_update' a b c d).
Proof.
  intros. apply find_mem in H. destruct H as [val H]. destruct (PVM.find var (floyd_update' a b c d)) as [x|] eqn : Hfind.
  apply find_mem; exists x; done.
  apply (pfind_floyd_update_some _ _ a b c H) in Hfind; try done.
Qed.

Lemma inner_loop2_mem_eq a b var : PVM.mem var b -> PVM.mem var (inner_loop2 a b).
Proof.
  move : a b; elim. simpl; done.
  simpl; intros. apply H; clear H. remember (floyd_update' a a [:: Zero, Node a & List.map [eta Node] l] b) as m.
  destruct (PVM.find var (inner_loop1 l m a)) as [x|] eqn : Hfind. apply find_mem; exists x; done.
  assert (exists val, PVM.find var m = Some val). apply find_mem. rewrite Heqm; apply floyd_update'_mem_eq; done.
  destruct H as [val H]. apply (pfind_innedr_loop1_some _ _ _ _ H) in Hfind; done.
Qed.

Lemma map0_in v : forall ls var, List.In var ls -> PVM.mem var (map0 ls v).
Proof.
  elim. simpl; done.
  simpl; intros. destruct H0. subst a; clear H. apply find_mem. rewrite find_add_eq. exists (NVM.add (Node var) 0%Z (NVM.empty Z.t)); done.
  destruct (var == a) eqn : Heq; move /eqP : Heq => Heq. subst a. apply find_mem. rewrite find_add_eq. exists (NVM.add (Node var) 0%Z (NVM.empty Z.t)); done.
  apply find_mem. rewrite find_add_neq; try done. apply H in H0. apply find_mem; done.
Qed.

Lemma solve_scc_correctness hd cs1 nv : hd <> nil -> solve_scc hd cs1 = Some nv -> 
  (forall c, List.In c cs1 -> (rhs_power c) = nil) ->
  (forall c, List.In c cs1 -> (forall v, List.In v (constraint1_vars c) -> List.In v hd)) ->
  forallb (satisfies_constraint1 nv) cs1.
Proof.
  rewrite /solve_scc; intros Hnotempty Hsolve Hp Hvars_in_hd.
  destruct hd as [|a l] eqn : Hhd. done.
  destruct l as [|hda tla] eqn : Htl.
  - (* trivial *)
    clear Htl Hhd Hnotempty l hd.
    destruct (List.partition (fun c : Constraint1 => (rhs_terms1 c == []) && (rhs_power c == [])) cs1) as [cs cs_have_v] eqn : Hpart.
    case Hsat : (forallb [eta satisfies_constraint1 (PVM.add a (max_nl (List.map [eta rhs_const1] cs) 0) initial_valuation)] cs_have_v); rewrite Hsat in Hsolve; try discriminate.
    inversion Hsolve; clear H0 Hsolve nv.
    apply forallb_forall; intros. assert (Hlhs : lhs_var1 x = a). 
      specialize (Hvars_in_hd _ H (lhs_var1 x)). move : Hvars_in_hd; clear; intro. simpl in Hvars_in_hd. destruct Hvars_in_hd; try done. left; done.
    apply (elements_in_partition _ _ Hpart) in H. destruct H.
    * rewrite /satisfies_constraint1. rewrite Hlhs; clear Hlhs.
      rewrite find_add_eq. apply Zle_imp_le_bool.
      remember (max_nl (List.map [eta rhs_const1] cs) 0) as new_val.   
      rewrite partition_as_filter in Hpart. inversion Hpart; clear Hpart H2. generalize H. intros Hin.
      rewrite -H1 in H. apply filter_In in H. move : H => [_ H]. move /andP : H => [Hterm Hpower]. move /eqP : Hterm => Hterm; move /eqP : Hpower => Hpower.
      rewrite /rhs_value1 Hterm Hpower; clear Hterm Hpower; simpl. rewrite Z.add_0_r.
      specialize (max_list_correctness (List.map [eta rhs_const1] cs) 0) as Hmax. move : Hmax => [Hinit Hle].
      apply (in_map [eta rhs_const1]) in Hin. apply Hle in Hin. 
      rewrite Heqnew_val //.
    * clear Hlhs. move : x H. apply forallb_forall. done. 
  - (* scc *)
    rewrite -Hhd in Hsolve Hvars_in_hd. clear Htl Hhd Hnotempty l a.
    case His_simple : (is_simple_cycle cs1); rewrite His_simple in Hsolve.
    * (* floyd *)
      apply solve_simple_cycle_correctness in Hsolve. rewrite satisfies_all_constraint1_eq in Hsolve; try done. apply forallb2satisfies_all_constraint1 in Hsolve. done.
      { rewrite /conform1_m. split. 
        2 : intros. 1,2:unfold floyd_loop_map'. specialize (Hvars_in_hd _ H (lhs_var1 c)). 2 : specialize (Hvars_in_hd _ H x).
        1,2:move : Hvars_in_hd; intro; apply find_mem; apply inner_loop2_mem_eq; unfold init_dist_map'; apply add_edge_of_cs'_mem_eq; apply map0_in; apply Hvars_in_hd;
        unfold constraint1_vars. simpl; left; done. unfold rhs_vars1 in H0. simpl; right. apply in_or_app; left; done. } 
    * (* bab *)
      case Hubs : (solve_ubs_aux hd (List.filter (fun c : Constraint1 => Datatypes.length (rhs_terms1 c) != 0) cs1)) => [ubs|]; rewrite Hubs in Hsolve; try discriminate.
      specialize (bab_bin_correct1 hd (mergeBounds ubs) cs1 nil); intro Hbab_correctness. rewrite Hsolve in Hbab_correctness.
      destruct Hbab_correctness; try done. destruct H as [s [Heq [Hsat1 _]]]. inversion Heq; rewrite H0 in Hsolve. clear Heq H0 nv.
      apply forallb2satisfies_all_constraint1 in Hsat1. done.
Qed.

Lemma max_list_small n : forall zl init, (init <= n /\ (forall z, List.In z zl -> Z.le z (Z.of_nat n))) -> (max_nl zl init) <= n.
Proof.
  induction zl as [| t tl IH]; intros init [H_init H_all].
  - (* nil case *)
    simpl; auto.
  - (* cons case *)
    simpl.
    assert (Ht: (t <= Z.of_nat n)%Z) by (apply H_all; left; auto).
    assert (H_max_val: (Z.max (Z.of_nat init) t <= Z.of_nat n)%Z).
    { apply Z.max_lub. apply Nat2Z.inj_le. apply (elimT leP). done. done. }
    assert (H_nonneg: (0 <= Z.max (Z.of_nat init) t)%Z).
    { apply Z.le_trans with (Z.of_nat init); [apply Zle_0_nat | apply Z.le_max_l]. }
    apply Z2Nat.inj_le in H_max_val; try assumption; try apply Zle_0_nat.
    rewrite Nat2Z.id in H_max_val.
    apply IH; split; auto. apply (introT leP). done.
    intros z H_in; apply H_all; right; auto.
Qed.

Lemma mergeBounds_find_lb : forall ubs var lb ub, PVM.find var (mergeBounds ubs) = Some (lb,ub) -> lb = 0.
Proof.
  unfold mergeBounds; intros. remember (PVM.elements ubs) as l. clear Heql ubs. 
  assert (forall l var v, (PVM.find var v = None \/ exists ub, PVM.find var v = Some (0, ub)) -> forall lb' ub', PVM.find var (add_bs l v) = Some (lb', ub') -> lb' = 0).
    elim. simpl; intros. destruct H0. rewrite H1 in H0; discriminate. destruct H0 as [ub'' H0]. rewrite H0 in H1; inversion H1. done.
    simpl; intros [var_hd coe_hd] tl; intros. apply H0 in H2; try done. destruct (var0 == var_hd) eqn : Heq; move /eqP : Heq => Heq.
    - subst var0. right. rewrite find_add_eq. exists coe_hd; done.
    - destruct H1. left. rewrite find_add_neq; try done.
      right. rewrite find_add_neq; try done.
  apply H0 in H; try done. left. apply find_empty_None.
Qed.

Lemma solve_ubs_case1_mem a b c d e : forall ls f g, solve_ubs_case1 ls a b c d e f = Some g -> forall var, PVM.mem var f -> PVM.mem var g.
Proof.
  elim. simpl; intros. inversion H; subst g; done.
  simpl; intros. destruct (solve_ub_case1 a0 a b c d e) as [ub|]; try discriminate.
  apply H with (var := var) in H0; try done. apply mem_add; done.
Qed.

Lemma solve_ubs_case1_ls_mem a b c d e : forall ls f g, solve_ubs_case1 ls a b c d e f = Some g -> forall var, List.In var ls -> PVM.mem var g.
Proof.
  elim. simpl; intros; done.
  simpl; intros. destruct H1. 
  - subst a0; clear H. destruct (solve_ub_case1 var a b c d e) as [ub|]; try discriminate.
    apply (solve_ubs_case1_mem _ _ _ _ _ _ _ _ H0). apply find_mem. rewrite find_add_eq. exists ub; done.
  - destruct (solve_ub_case1 a0 a b c d e) as [ub|]; try discriminate. apply H with (var := var) in H0; try done.
Qed.

Lemma solve_ubs_case2_mem a b c0 c1 d e : forall ls f g, solve_ubs_case2 ls a b c0 c1 d e f = Some g -> forall var, PVM.mem var f -> PVM.mem var g.
Proof.
  elim. simpl; intros. inversion H; subst g; done.
  simpl; intros. destruct (solve_ub_case2 a0 a b c0 c1 d e) as [ub|]; try discriminate.
  apply H with (var := var) in H0; try done. apply mem_add; done.
Qed.

Lemma solve_ubs_case2_ls_mem a b c0 c1 d e : forall ls f g, solve_ubs_case2 ls a b c0 c1 d e f = Some g -> forall var, List.In var ls -> PVM.mem var g.
Proof.
  elim. simpl; intros; done.
  simpl; intros. destruct H1. 
  - subst a0; clear H. destruct (solve_ub_case2 var a b c0 c1 d e) as [ub|]; try discriminate.
    apply (solve_ubs_case2_mem _ _ _ _ _ _ _ _ _ H0). apply find_mem. rewrite find_add_eq. exists ub; done.
  - destruct (solve_ub_case2 a0 a b c0 c1 d e) as [ub|]; try discriminate. apply H with (var := var) in H0; try done.
Qed.

Lemma solve_ubs_aux_in_mem cs : forall ls ubs, solve_ubs_aux ls cs = Some ubs -> forall var, List.In var ls -> PVM.mem var ubs.
Proof.
  intros ls ubs H. unfold solve_ubs_aux in H. destruct (scc.build_graph cs) as [g adj] eqn : Hbuild.
  case Hfind0 : (List.find (fun c : Constraint1 =>
    List.existsb (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) cs) => [c|]; rewrite Hfind0 in H.
  case Hfind1 : (List.find (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) => [[coe var]|]; rewrite Hfind1 in H; try discriminate.
  - move : H; apply solve_ubs_case1_ls_mem.
  case Hfind1 : (List.find (fun c : Constraint1 =>
    1 < Datatypes.length (rhs_terms1 c)) cs) => [c|]; rewrite Hfind1 in H; try discriminate. destruct (rhs_terms1 c) as [|[coe0 var0] l]; try discriminate.
  destruct l as [|[coe1 var1] tl]; try discriminate.
  - move : H; apply solve_ubs_case2_ls_mem.
Qed.

Lemma add_bs_mem var : forall ls v, PVM.mem var v -> PVM.mem var (add_bs ls v).
Proof.
  elim. simpl; intros; done.
  simpl; intros [var_hd ub_hd] tl; intros. apply H. apply mem_add; done.
Qed.

Lemma mergeBounds_key_eq ubs var: PVM.mem var ubs -> PVM.mem var (mergeBounds ubs).
Proof.
  rewrite /mergeBounds /initial_bounds; intros. 
  apply mem_in_elements in H. destruct H as [ub H]. remember (PVM.elements ubs) as l.
  assert (forall l v var ub, List.In (var, ub) l -> PVM.mem var (add_bs l v)). clear. elim.
  - simpl; intros; done.
  - simpl; intros [var_hd ub_hd] tl; intros. destruct H0. 
    + inversion H0; clear H0 H. subst var_hd ub_hd. apply add_bs_mem. apply find_mem. rewrite find_add_eq.
      exists (0,ub); done.
    + move : H0; apply H.
  move : H; apply H0.
Qed.

Lemma init_map0_exists hd init_map0 : init_map0 = (fold_left
  (fun (temp_matrix : PVM.t (NVM.t Z)) (v : ProdVar.t) => PVM.add v (NVM.add (Node v) 0%Z (NVM.empty Z.t)) temp_matrix)
  hd (PVM.empty (NVM.t Z.t))) -> forall v, List.In v hd -> exists dst_map, PVM.find v init_map0 = Some dst_map.
Proof.
  remember (PVM.empty (NVM.t Z.t)) as m0. clear Heqm0. move : hd init_map0 m0. elim.
  - done.
  - intros x xs IH; intros.
    simpl in H; simpl in H0. destruct H0.
    + subst v. clear IH.
      assert (forall m dst m0 , PVM.find x m = Some dst -> m0 = fold_left
        (fun (temp_matrix : PVM.t (NVM.t Z)) (v : ProdVar.t) =>
        PVM.add v (NVM.add (Node v) 0%Z (NVM.empty Z.t)) temp_matrix) xs m -> exists dst0, PVM.find x m0 = Some dst0). {
        clear. move : xs. elim. 
        simpl; intros. subst m0; exists dst; done.
        simpl; intros. 
        assert (exists dst0, PVM.find x (PVM.add a (NVM.add (Node a) 0%Z (NVM.empty Z.t)) m) = Some dst0). {
          destruct (x == a) eqn : Heq; move /eqP : Heq => Heq. 
          subst x. rewrite find_add_eq. exists (NVM.add (Node a) 0%Z (NVM.empty Z.t)); done.
          rewrite find_add_neq; try done. exists dst; done. } 
        destruct H2 as [dst0 H2]. move : H2 H1; apply H. }
      move : H; apply H0 with (dst := NVM.add (Node x) 0%Z (NVM.empty Z.t)). apply find_add_eq.
    + apply (IH init_map0 _ H _ H0).
Qed.

Lemma add_edge_of_cs_find_exists v init_map dst0 : PVM.find v init_map = Some dst0 -> forall c_tl fm, fm = add_edge_of_cs c_tl init_map -> exists dst, PVM.find v fm = Some dst.
Proof.
  intros. move : c_tl init_map dst0 H fm H0. elim.
  simpl; intros. subst fm. exists dst0; done.
  simpl; intros. remember (match PVM.find (elt:=NVM.t Z.t) (lhs_var1 a) init_map with
    | Some dst_map =>
        match rhs_terms1 a with
        | [] =>
            match NVM.find (elt:=Z.t) Zero dst_map with
            | Some dist =>
                PVM.add (lhs_var1 a)
                  (NVM.add Zero (Z.max dist (rhs_const1 a))
                    dst_map) init_map
            | None =>
                PVM.add (lhs_var1 a)
                  (NVM.add Zero (rhs_const1 a) dst_map) init_map
            end
        | t :: l =>
            let (n, v) := t in
            match n with
            | 0 => init_map
            | n0.+1 =>
                match n0 with
                | 0 =>
                    match l with
                    | [] =>
                        match
                          NVM.find (elt:=Z.t) (Node v) dst_map
                        with
                        | Some dist =>
                            PVM.add (lhs_var1 a)
                              (NVM.add (Node v)
                                (Z.max dist (rhs_const1 a))
                                dst_map) init_map
                        | None =>
                            PVM.add (lhs_var1 a)
                              (NVM.add (Node v) 
                                (rhs_const1 a) dst_map) init_map
                        end
                    | _ :: _ => init_map
                    end
                | _.+1 => init_map
                end
            end
        end
    | None => init_map
    end) as init_map0.
  assert (exists dst, PVM.find v init_map0 = Some dst). {
    subst init_map0; move : H0; clear. intro.
    destruct (PVM.find (elt:=NVM.t Z.t) (lhs_var1 a) init_map).
    destruct (rhs_terms1 a) as [|[coe var] l]. destruct (NVM.find (elt:=Z.t) Zero t).
    3 : destruct coe. 4 : destruct coe. 4 : destruct l. 4 : destruct (NVM.find (elt:=Z.t) (Node var) t).
    3,6-8 : exists dst0; done. 1-4 : destruct (v == (lhs_var1 a)) eqn : Heq; move /eqP : Heq => Heq.
    1,3,5,7 : subst v; rewrite find_add_eq.
    exists (NVM.add Zero (Z.max t0 (rhs_const1 a)) t); done.
    exists (NVM.add Zero (rhs_const1 a) t); done.
    exists (NVM.add (Node var) (Z.max t0 (rhs_const1 a)) t); done.
    exists (NVM.add (Node var) (rhs_const1 a) t); done.
    1-4 : rewrite find_add_neq; try done. 1-4 : exists dst0 ;done. 
  }
  destruct H2 as [dst H2]. move : H2 fm H1; apply H.
Qed.

Lemma solve_scc_smallest hd cs1 nv : hd <> nil -> NoDup hd -> solve_scc hd cs1 = Some nv -> cs1 <> nil -> 
  (forall c, List.In c cs1 -> (forall v, List.In v (constraint1_vars c) -> List.In v hd)) ->
  (forall c, List.In c cs1 -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs1 -> rhs_power c = nil) ->
  forall temp_s, forallb (satisfies_constraint1 temp_s) cs1 -> le nv temp_s.
Proof.
  rewrite /solve_scc; intros Hnotemptyscc Hnodup Hsolve Hnotempty Hvars_in_hd Hterm Hpower.
  destruct hd as [|a l] eqn : Hhd. done.
  destruct l as [|hda tla] eqn : Htl.
  - (* trivial *)
    clear Htl Hhd Hnotemptyscc l hd Hterm Hpower. assert (Hlhs : forall x, List.In x cs1 -> lhs_var1 x = a) . 
      intros. specialize (Hvars_in_hd _ H (lhs_var1 x)). move : Hvars_in_hd; clear; intro. simpl in Hvars_in_hd. destruct Hvars_in_hd; try done. left; done.
    destruct (List.partition (fun c : Constraint1 => (rhs_terms1 c == []) && (rhs_power c == [])) cs1) as [cs cs_have_v] eqn : Hpart.
    case Hsat : (forallb [eta satisfies_constraint1 (PVM.add a (max_nl (List.map [eta rhs_const1] cs) 0) initial_valuation)] cs_have_v); rewrite Hsat in Hsolve; try discriminate.
    inversion Hsolve; clear H0 Hsolve nv. intros. rewrite /le. intros var value0 Hin.
    assert (Heq : var = a).
    { destruct (var == a) eqn : H0.
      move /eqP : H0 => H0. done.
      rewrite find_add_neq in Hin. rewrite /initial_valuation in Hin. rewrite find_empty_None in Hin. discriminate. 
      move /eqP : H0 => H0; done. }
    subst. rewrite find_add_eq in Hin. inversion Hin; clear Hin.
    assert (forallb (satisfies_constraint1 temp_s) cs).
    { apply forallb_forall. intros. 
      assert (forall x : Constraint1, List.In x cs1 -> satisfies_constraint1 temp_s x = true) by (apply forallb_forall; done). clear H. 
      apply H2. apply (elements_in_partition _ _ Hpart); left; done. }
      specialize (satisfies2le _ _ H0 a); intros.
    assert (exists c : Constraint1, List.In c cs1 /\ lhs_var1 c == a).
    { destruct (destruct_list cs1).
      destruct s as [hd [tl Hcons]]. 2 : done.
      assert (List.In hd cs1) by (rewrite Hcons;simpl; left; done).
      exists hd; split; try done. apply Hlhs in H3. rewrite H3 //. }
    apply satisfies1_exists_value with (a := a) in H; try done. clear H3.
    destruct H as [value1 H]. exists value1; split; try done.
    apply max_list_small. split; try done.
    intros. apply in_map_iff in H3. destruct H3 as [x [Hcst Hin]]. rewrite -Hcst. rewrite H in H2.
    assert (List.In x cs /\ lhs_var1 x == a).
    { split; try done. assert (List.In x cs1). 
      apply (elements_in_partition _ _ Hpart). left; done. apply Hlhs in H3. rewrite H3 //. }
    apply H2 in H3; clear H2.
    rewrite partition_as_filter in Hpart. inversion Hpart; clear Hpart H5. generalize Hin.
    rewrite -H4 in Hin. apply filter_In in Hin. move : Hin => [_ Hnil]. intros Hin. move /andP : Hnil => [Hterm Hpower]. move /eqP : Hterm => Hterm; move /eqP : Hpower => Hpower.
    rewrite /rhs_value1 Hterm Hpower in H3. clear Hterm Hpower; simpl in H3. rewrite Z.add_0_r in H3.
    apply Zle_bool_imp_le. done.
  - (* scc *)
    rewrite -Hhd in Hsolve Hvars_in_hd Hnodup. clear Htl Hhd Hnotemptyscc l a.
    case His_simple : (is_simple_cycle cs1); rewrite His_simple in Hsolve.
    * (* floyd *)
      intros. assert (exists fm, well_formed fm cs1).
      { unfold well_formed; unfold conform1_m.
        exists (init_dist_map hd cs1). intros c Hin.
        remember (init_dist_map hd cs1) as fm. unfold init_dist_map in *.
        remember (fold_left
          (fun (temp_matrix : PVM.t (NVM.t Z)) (v : ProdVar.t) => PVM.add v (NVM.add (Node v) 0%Z (NVM.empty Z.t)) temp_matrix)
          hd (PVM.empty (NVM.t Z.t))) as init_map0.
        specialize (init_map0_exists _ _ Heqinit_map0) as Hinit. clear Heqinit_map0. move : Hvars_in_hd His_simple c Hin init_map0 Hinit Heqfm. clear. move : cs1.
        elim; try done. intros c_hd c_tl IH. intros. simpl in Hin. rewrite /rhs_vars1. destruct Hin.
        + subst c. clear IH.
          simpl in Heqfm. destruct (Hinit (lhs_var1 c_hd)) as [dst_map Hdst_map].
          apply (Hvars_in_hd c_hd). simpl; left; done. unfold constraint1_vars. simpl; left; done.
          rewrite Hdst_map in Heqfm. simpl in His_simple. move /andP: His_simple => [His_simple _]. destruct (rhs_terms1 c_hd) as [|[coe var] l] eqn : Hrhs_terms.
          split; try done. destruct (NVM.find (elt:=Z.t) Zero dst_map).
          apply add_edge_of_cs_find_exists with (v := lhs_var1 c_hd) (dst0 := NVM.add Zero (Z.max t (rhs_const1 c_hd)) dst_map) in Heqfm. done.
          apply find_add_eq.
          apply add_edge_of_cs_find_exists with (v := lhs_var1 c_hd) (dst0 := NVM.add Zero (rhs_const1 c_hd) dst_map) in Heqfm. done.
          apply find_add_eq.
          destruct coe as [|coe0]; try done. destruct coe0; try done. destruct l; try done. clear His_simple. simpl. 
          split. destruct (NVM.find (elt:=Z.t) (Node var) dst_map) as [dist|].
          apply add_edge_of_cs_find_exists with (v := lhs_var1 c_hd) (dst0 := NVM.add (Node var) (Z.max dist (rhs_const1 c_hd)) dst_map) in Heqfm. done.
          apply find_add_eq.
          apply add_edge_of_cs_find_exists with (v := lhs_var1 c_hd) (dst0 := NVM.add (Node var) (rhs_const1 c_hd) dst_map) in Heqfm. done.
          apply find_add_eq.
          intros. destruct H; try done. subst x. 
          assert (Hhelper : exists dst0, PVM.find var match NVM.find (elt:=Z.t) (Node var) dst_map with
            | Some dist => PVM.add (lhs_var1 c_hd) (NVM.add (Node var) (Z.max dist (rhs_const1 c_hd)) dst_map) init_map0
            | None => PVM.add (lhs_var1 c_hd) (NVM.add (Node var) (rhs_const1 c_hd) dst_map) init_map0
            end = Some dst0). {
              destruct (NVM.find (elt:=Z.t) (Node var) dst_map) as [dist|].
              destruct (var == (lhs_var1 c_hd)) eqn : Heq.
              move /eqP : Heq => Heq; subst var.
              rewrite find_add_eq. exists (NVM.add (Node (lhs_var1 c_hd)) (Z.max dist (rhs_const1 c_hd)) dst_map); done.
              rewrite find_add_neq. apply Hinit. apply (Hvars_in_hd c_hd). simpl; left; done.
              unfold constraint1_vars; simpl; right. rewrite Hrhs_terms; simpl. left; done.
              move /eqP : Heq => Heq; done.
              destruct (var == (lhs_var1 c_hd)) eqn : Heq.
              move /eqP : Heq => Heq; subst var.
              rewrite find_add_eq. exists (NVM.add (Node (lhs_var1 c_hd)) (rhs_const1 c_hd) dst_map); done.
              rewrite find_add_neq. apply Hinit. apply (Hvars_in_hd c_hd). simpl; left; done.
              unfold constraint1_vars; simpl; right. rewrite Hrhs_terms; simpl. left; done.
              move /eqP : Heq => Heq; done.
            }
          destruct Hhelper as [dst0 Hhelper].
          apply add_edge_of_cs_find_exists with (v := var) (dst0 := dst0) in Heqfm; try done.
        + assert (Hvars_in_hd' : forall c : Constraint1, List.In c c_tl -> forall v : ProdVar.t, List.In v (constraint1_vars c) -> List.In v hd).
          { intros c0 Hin. apply (Hvars_in_hd c0). simpl; right; done. }
          simpl in His_simple. move /andP : His_simple => [Hc_hd His_simple']. simpl in Heqfm.
          destruct (rhs_terms1 c_hd) as [|[coe var] l] eqn : Hrhs_terms.
          move : Heqfm; apply (IH Hvars_in_hd' His_simple' _ H). clear Hvars_in_hd' His_simple' IH H.
          intros v Hin; apply Hinit in Hin. destruct Hin as [dst_map Hinit0]. destruct (v == (lhs_var1 c_hd)) eqn : Heq.
          move /eqP : Heq => Heq; subst v. rewrite Hinit0. destruct (NVM.find (elt:=Z.t) Zero dst_map).
          rewrite find_add_eq. exists (NVM.add Zero (Z.max t (rhs_const1 c_hd)) dst_map); done.
          rewrite find_add_eq. exists (NVM.add Zero (rhs_const1 c_hd) dst_map); done.
          destruct (PVM.find (elt:=NVM.t Z.t) (lhs_var1 c_hd) init_map0). destruct (NVM.find (elt:=Z.t) Zero t).
          rewrite find_add_neq. exists (dst_map); done. move /eqP : Heq => Heq; done.
          rewrite find_add_neq. exists (dst_map); done. move /eqP : Heq => Heq; done.
          exists (dst_map); done.
          destruct coe as [|coe0]; try done. destruct coe0; try done. destruct l; try done. clear Hc_hd.
          move : Heqfm; apply (IH Hvars_in_hd' His_simple' _ H). clear Hvars_in_hd' His_simple' IH H.
          intros v Hin; apply Hinit in Hin. destruct Hin as [dst_map Hinit0]. destruct (v == (lhs_var1 c_hd)) eqn : Heq.
          move /eqP : Heq => Heq; subst v. rewrite Hinit0. destruct (NVM.find (elt:=Z.t) (Node var) dst_map).
          rewrite find_add_eq. exists (NVM.add (Node var) (Z.max t (rhs_const1 c_hd)) dst_map); done.
          rewrite find_add_eq. exists (NVM.add (Node var) (rhs_const1 c_hd) dst_map); done.
          destruct (PVM.find (elt:=NVM.t Z.t) (lhs_var1 c_hd) init_map0). destruct (NVM.find (elt:=Z.t) (Node var) t).
          rewrite find_add_neq. exists (dst_map); done. move /eqP : Heq => Heq; done.
          rewrite find_add_neq. exists (dst_map); done. move /eqP : Heq => Heq; done.
          exists (dst_map); done. }
      destruct H0 as [fm H0]. apply (scc_smallest _ H0 Hsolve). 
      rewrite satisfies_all_constraint1_eq; try done. apply forallb2satisfies_all_constraint1. done.
    * (* bab *)
      case Hubs : (solve_ubs_aux hd (List.filter (fun c : Constraint1 => Datatypes.length (rhs_terms1 c) != 0) cs1)) => [ubs|]; rewrite Hubs in Hsolve; try discriminate.
      intros. apply (bab_bin_smallest hd) with (s := temp_s) in Hsolve; try done.
      { unfold branch_and_bound.well_formed. split.
      + unfold well_defined. intros. apply mergeBounds_find_lb in H0. rewrite H0. done.
      + split. unfold conform1. split. 
        specialize (Hvars_in_hd _ H0 (lhs_var1 c)); specialize (solve_ubs_aux_in_mem _ _ _ Hubs (lhs_var1 c)); intro.
          apply mergeBounds_key_eq in H1. apply find_mem in H1. destruct H1 as [[val0 val1] H1]. exists val0; exists val1; done.
          apply Hvars_in_hd. unfold constraint1_vars. simpl; left; done.
        intros x Hrhs; specialize (Hvars_in_hd _ H0 x); specialize (solve_ubs_aux_in_mem _ _ _ Hubs x); intro.
          apply mergeBounds_key_eq in H1. apply find_mem in H1. destruct H1 as [[val0 val1] H1]. exists val0; exists val1; done.
          apply Hvars_in_hd. unfold constraint1_vars. unfold rhs_vars in Hrhs. simpl; right; done.
      + unfold conform2. intros; done. }
      split. remember (List.filter (fun c : Constraint1 => Datatypes.length (rhs_terms1 c) != 0) cs1) as cs1'.
        assert (forallb (satisfies_constraint1 temp_s) cs1').
        { apply forallb_forall. assert (forall x, List.In x cs1 -> satisfies_constraint1 temp_s x = true) by (apply forallb_forall; done).
          intros; apply H0. rewrite Heqcs1' in H1. apply filter_In in H1. exact H1.1. }
        move : Hubs H0; apply solution_in_bds; try done. intros; apply Hterm. 2 : intros; apply Hpower. 1,2 : rewrite Heqcs1' in H0; apply filter_In in H0; exact H0.1.
      split. apply forallb2satisfies_all_constraint1. done. simpl; done.
Qed.

Lemma max_list_lt : forall zl init val,
    val < max_nl zl init ->
    (val < init) \/ (exists z, List.In z zl /\ (Z.of_nat val < z)%Z).
Proof.
  induction zl as [|t tl IH]; intros init val H.
  - simpl in H. left; auto.
  - simpl in H.
    apply IH in H.
    destruct H as [Hval | [z [Hin Hlt]]].
    + set (m := Z.max (Z.of_nat init) t).
      destruct (Z_ge_lt_dec (Z.of_nat init) t) as [Hge | Hlt'].
      * rewrite Z.max_l in Hval; auto.
        rewrite Nat2Z.id in Hval.
        left; auto. apply Z.ge_le; auto.
      * rewrite Z.max_r in Hval; [|apply Z.lt_le_incl; auto].
        assert (t >= 0)%Z.
        { destruct (Z_ge_lt_dec t 0) as [Hpos|Hneg]; [auto|].
          specialize (Z.lt_trans _ _ _ Hlt' Hneg); intros. intuition. }
        right; exists t. split; try done. simpl; left; done.
        rewrite -(Z2Nat.id t); try intuition.
        apply Nat2Z.inj_lt. apply (elimT leP). done.
    + right. exists z. split; [right; auto|auto].
Qed.

Lemma constraint1s_vars2constraint1_vars : forall cs var, List.In var (constraints1_vars cs) -> exists x, List.In x cs /\ List.In var (constraint1_vars x).
Proof.
  intros cs. induction cs as [|c1 tl IHcs]; intros var HIn.
  - inversion HIn. 
  - simpl in *.
    destruct HIn as [Hc1 | HIn_tl].
    + subst var. exists c1. split. left; done. left; done.
    + apply in_app_or in HIn_tl. destruct HIn_tl.
      exists c1; split. left; done. right; done.
      apply IHcs in H. destruct H as [x [HIn H]]. exists x; split; try done. right; done.
Qed.

Fixpoint In_bool (v : Valuation) (bs : list (ProdVar.t * (nat * nat))) : bool :=
  match bs with
  | [] => true
  | (var, (lb, ub)) :: tl => match PVM.find var v with
    | Some val => (lb <= val) && (val <= ub)
    | _ => false
    end && In_bool v tl
  end.

Lemma In_bool_spec : forall v l x lb ub,
  List.In (x, (lb, ub)) l ->
  In_bool v l = true ->
  exists n, PVM.find x v = Some n /\ lb <= n /\ n <= ub.
Proof.
  induction l as [| [y [lb_y ub_y]] tl IH]; intros x lb ub Hin Hbool.
  - inversion Hin. 
  - simpl in Hbool.
    destruct Hin as [Heq | Hin_tl].
    + injection Heq as <- <- <-. 
      destruct (PVM.find y v) eqn:Hfind; [|discriminate].
      rewrite andb_true_iff in Hbool. destruct Hbool as [Hrange _].
      rewrite andb_true_iff in Hrange. destruct Hrange as [Hlow Hhigh].
      exists n; split; auto.
    + destruct (PVM.find y v) eqn:Hfind; [|discriminate].
      rewrite andb_true_iff in Hbool. destruct Hbool as [_ Htl].
      apply IH with (x:=x) (lb:=lb) (ub:=ub); auto.
Qed.

Lemma In_bool_universal : forall v l,
  (forall x lb ub, List.In (x, (lb, ub)) l -> 
   exists n, PVM.find x v = Some n /\ lb <= n /\ n <= ub) ->
  In_bool v l = true.
Proof.
  induction l as [| [x [lb ub]] tl IH]; intros Hforall.
  - reflexivity. 
  - simpl.
    assert (List.In (x, (lb, ub)) ((x, (lb, ub)) :: tl)) by (simpl; left; done).
    specialize (Hforall x lb ub H) as Hdestruct; clear H.
    destruct Hdestruct as [n [Hfind [Hlow Hhigh]]].
    rewrite Hfind.
    rewrite Hlow Hhigh andb_true_r.
    apply IH.
    intros y lb_y ub_y Hin.
    apply Hforall; right; auto.
Qed.

Lemma In_In_bool : forall v bs, In_bool v (PVM.elements bs) <-> In v bs.
Proof.
  intros v bs.
  split; intros H.
  - unfold In; intros x lb ub Hfind. apply find_in_elements in Hfind.
    apply In_bool_spec with (l := PVM.elements bs); auto.
  - apply In_bool_universal.
    intros x lb ub Hin. unfold In in H. apply H.
    apply find_in_elements. done.
Qed.

Definition In_bool' (v : Valuation) (bs : list (ProdVar.t * (nat * nat))) : bool :=
  forallb (fun '(var,(lb,ub)) => 
    match PVM.find var v with
    | Some val => (lb <= val) && (val <= ub)
    | _ => false
    end) bs.

Lemma In_bool_In_bool' : forall v bs, In_bool v bs <-> In_bool' v bs.
Proof.
  split; intros H.
  - (* In_bool -> In_bool' *)
    unfold In_bool'.
    induction bs as [| [var [lb ub]] bs IH].
    + reflexivity. 
    + simpl in H.
      simpl. move /andP : H => [H H'].
      apply IH in H'; clear IH. rewrite H H' //.
  - (* In_bool' -> In_bool *)
    unfold In_bool' in H.
    induction bs as [| [var [lb ub]] bs IH].
    + reflexivity. 
    + simpl.
      simpl in H. move /andP : H => [H H'].
      apply IH in H'; clear IH. rewrite H H' //.
Qed.

Lemma compute_ub_gt_unsat c ub v val : compute_ub c = Some ub -> PVM.find (lhs_var1 c) v = Some val -> ub < val -> satisfies_constraint1 v c = false.
Proof.
  intro. assert (satisfies_constraint1 v c -> exists n : nat, PVM.find (elt:=nat) (lhs_var1 c) v = Some n /\ n <= ub).
    intros; apply compute_ub_correctness; try done. intros. apply not_true_iff_false; apply (contra_not H0); clear H0.
  intro. destruct H0 as [n [Hn Hn']]. rewrite H1 in Hn; inversion Hn; subst n. clear Hn. 
  specialize (leq_ltn_trans Hn' H2); intro. rewrite ltnn in H0. done.
Qed.

Lemma substitute_c_unsat c0 c1 v : good_terms (rhs_terms1 c0) -> good_terms (rhs_terms1 c1) -> rhs_power c0 = nil -> rhs_power c1 = nil -> satisfies_constraint1 v (substitute_c c0 c1) = false -> satisfies_constraint1 v c0 = false \/ satisfies_constraint1 v c1 = false.
Proof.
  intros. assert (satisfies_constraint1 v c0 /\ satisfies_constraint1 v c1 -> satisfies_constraint1 v (substitute_c c0 c1)). intros [H4 H5]. apply (substitute_c_correctness _ _ _ H4 H5); try done.
  apply not_true_iff_false in H3; apply (contra_not H4) in H3. destruct (satisfies_constraint1 v c0); try (left; done). destruct (satisfies_constraint1 v c1); try (right; done). intuition.
Qed.

Lemma substitute_cs_unsat cs c v : (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs -> rhs_power c = nil) -> substitute_cs cs = Some c -> satisfies_constraint1 v c = false -> forallb (satisfies_constraint1 v) cs = false.
Proof.
  intros. assert (forallb (satisfies_constraint1 v) cs -> satisfies_constraint1 v c). intros. apply (substitute_cs_correctness _ _ _ H H0 H3 H1).
  apply not_true_iff_false. apply (contra_not H3). apply not_true_iff_false. done.
Qed.
 
Lemma solve_ubs_case1_notin_unsat cs c var tbsolved g adj n ubs : (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs -> rhs_power c = nil) ->
  scc.build_graph cs = (g, adj) -> NoDup tbsolved ->
  List.find (fun c : Constraint1 => List.existsb (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) cs = Some c ->
  (*List.find (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c) = Some (coe, var) -> *)
  solve_ubs_case1 tbsolved c var g adj n initial_valuation = Some ubs -> 
  forall v, ~In v (mergeBounds ubs) ->
  forallb (satisfies_constraint1 v) cs = false.
Proof.
  intros Hterm Hpower Hbuild HNodup Hc.
  assert (Hhelper : forall (tbsolved : seq ProdVar.t) (ubs initial : Valuation), (forall v, ~In v (mergeBounds initial) -> forallb (satisfies_constraint1 v) cs = false) ->
    (forall var, List.In var tbsolved -> ~PVM.mem var initial) -> NoDup tbsolved ->
    solve_ubs_case1 tbsolved c var g adj n initial = Some ubs -> forall v, ~In v (mergeBounds ubs) -> forallb (satisfies_constraint1 v) cs = false).
  { elim. simpl; intros ubs0 initial Hinitial Hmem Hnodup Hsolve. inversion Hsolve. rewrite -H0 //.
    simpl; intros hd tl IH ubs0 initial Hinitial Hmem Hnodup Hsolve. case Hsolve_hd : (solve_ub_case1 hd c var g adj n) => [ub|]; rewrite Hsolve_hd in Hsolve; try discriminate.
    move : Hsolve; apply IH. clear IH. intros. assert (~In_bool v (PVM.elements (mergeBounds (PVM.add hd ub initial)))) by (intro; apply In_In_bool in H0; done). clear H.
    assert (~In_bool' v (PVM.elements (elt:=nat * nat) (mergeBounds (PVM.add hd ub initial)))) by (intro; apply In_bool_In_bool' in H; done). clear H0.
    unfold In_bool' in H. apply forallb_neg_neg in H. destruct H as [[x [lb_x ub_x]] [Hin Hbs]].
    destruct (x == hd) eqn : Heq; move /eqP : Heq => Heq.
    - subst x. assert (lb_x = 0 /\ ub_x = ub). 
      { apply find_in_elements in Hin. unfold mergeBounds in Hin. assert (~ PVM.mem hd initial) by (apply Hmem; left; done). move : H Hin; clear; intros. 
        specialize (elements_add' initial hd ub); intro. destruct H0 as [l0 [l1 [_ Hele1]]]. apply mem_find_none; done.
        rewrite -Hele1 in Hin. rewrite add_bs_app in Hin. simpl in Hin.
        rewrite find_mergeBounds_add_bs_not_in in Hin. rewrite find_add_eq in Hin. inversion Hin; subst lb_x ub_x; done.
        specialize (key_NoDup _ (PVM.add hd ub initial)); intro. rewrite -Hele1 split_app in H0; simpl in H0. destruct (List.split l1) as [left right] eqn : Hsplit.
        simpl in H0. simpl. apply NoDup_app_remove_l in H0. apply NoDup_cons_iff in H0; exact H0.1. }
      clear Hin Hinitial. move : H => [H H']; subst lb_x ub_x.
      unfold solve_ub_case1 in Hsolve_hd.
      case Hp0 : (scc.find_path g hd n [] (lhs_var1 c) None) => [l|]; rewrite Hp0 in Hsolve_hd; try discriminate.
      case Hl : l => [|p0_hd p0_tl]; rewrite Hl in Hsolve_hd; try discriminate. rewrite Hl in Hp0; clear Hl l. 
      case Hp1 : (scc.find_path g var n [] hd None) => [l|]; rewrite Hp1 in Hsolve_hd; try discriminate.
      case Hl : l => [|p1_hd p1_tl]; rewrite Hl in Hsolve_hd; try discriminate. rewrite Hl in Hp1; clear Hl l. 
      case Hcs0 : (find_constraints_of_path adj p0_hd p0_tl) => [cs0|]; rewrite Hcs0 in Hsolve_hd; try discriminate.
      case Hcs1 : (find_constraints_of_path adj p1_hd p1_tl) => [cs1|]; rewrite Hcs1 in Hsolve_hd; try discriminate.
      specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs0) as Hfind_cs_in0.
      specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs1) as Hfind_cs_in1.
      case Hsub0 : (substitute_cs cs0) => [c0|]; rewrite Hsub0 in Hsolve_hd.
      case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in Hsolve_hd.
      (* case1 *)
      - destruct (PVM.find hd v) as [val|] eqn : Hfind_hd. 
        * apply andb_false_iff in Hbs. destruct Hbs; try done. specialize (leqVgt val ub); intro. rewrite H in H0; clear H. rewrite orb_false_l in H0.
          apply (compute_ub_gt_unsat _ _ v _ Hsolve_hd) in H0. apply substitute_c_unsat in H0. destruct H0. 
          apply (substitute_cs_unsat cs0) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3: apply Hfind_cs_in0; done.
          apply substitute_c_unsat in H. destruct H. apply not_true_iff_false; apply forallb_neg_neg. exists c; split; try done. apply find_some in Hc; exact Hc.1.
          apply (substitute_cs_unsat cs1) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3:  apply Hfind_cs_in1; done.
          6 : apply substitute_c_good_term. 9: apply substitute_c_power. 1,6:apply Hterm. 4,9: apply Hpower. 1,2,4,5 : apply find_some in Hc; exact Hc.1.
          1,4 : move : Hsub1; apply substitute_cs_good_term. 3,6 : move : Hsub1; apply substitute_cs_power. 1-4: intros. 1,2 : apply Hterm; apply Hfind_cs_in1; done. 1,2 : apply Hpower; apply Hfind_cs_in1; done.
          1,2: move : Hsub0. apply substitute_cs_good_term; intros; apply Hterm. 2:apply substitute_cs_power; intros; apply Hpower. 1,2 : apply Hfind_cs_in0; done.  
          assert (hd = (lhs_var1 (substitute_c c0 (substitute_c c c1)))). 
          { rewrite substitute_c_lhs_eq. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
          apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 Hlhs0]]. rewrite -Hlhs0. symmetry. move : Hbuild Hcs0 Hhd0; apply find_constraint_hd_eq; try done. }
          rewrite -H //.
        * clear Hbs. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
          apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 _]]. 
          generalize Hhd0; apply (find_constraint_hd_eq _ _ _ _ _ _ _ Hterm Hbuild Hcs0) in Hhd0; intro. apply not_true_iff_false. apply forallb_neg_neg. exists c_hd; split.
          apply Hfind_cs_in0. destruct cs0; try done. simpl in Hhd1. inversion Hhd1; subst c_hd. simpl; left; done. 
          unfold satisfies_constraint1. rewrite Hhd0 Hfind_hd //.
      (* case2 *)
      - destruct (PVM.find hd v) as [val|] eqn : Hfind_hd. 
        * apply andb_false_iff in Hbs. destruct Hbs; try done. specialize (leqVgt val ub); intro. rewrite H in H0; clear H. rewrite orb_false_l in H0.
          apply (compute_ub_gt_unsat _ _ v _ Hsolve_hd) in H0. apply substitute_c_unsat in H0. destruct H0. 
          apply (substitute_cs_unsat cs0) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3: apply Hfind_cs_in0; done.
          apply not_true_iff_false; apply forallb_neg_neg. exists c; split; try done. apply find_some in Hc; exact Hc.1.
          1,3 : move : Hsub0. apply substitute_cs_good_term. 2: apply substitute_cs_power. intros; apply Hterm. 2 : intros; apply Hpower. 1,2 : apply Hfind_cs_in0; done.
          apply Hterm. 2 : apply Hpower. 1,2 : apply find_some in Hc; exact Hc.1.
          assert (hd = (lhs_var1 (substitute_c c0 c))).
          { rewrite substitute_c_lhs_eq. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
            apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 Hlhs0]]. rewrite -Hlhs0. symmetry. move : Hbuild Hcs0 Hhd0; apply find_constraint_hd_eq; try done. }
          rewrite -H //.
        * clear Hbs. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
          apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 _]]. 
          generalize Hhd0; apply (find_constraint_hd_eq _ _ _ _ _ _ _ Hterm Hbuild Hcs0) in Hhd0; intro. apply not_true_iff_false. apply forallb_neg_neg. exists c_hd; split.
          apply Hfind_cs_in0. destruct cs0; try done. simpl in Hhd1. inversion Hhd1; subst c_hd. simpl; left; done. 
          unfold satisfies_constraint1. rewrite Hhd0 Hfind_hd //.
      case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in Hsolve_hd.
      (* case3 *)
      - destruct (PVM.find hd v) as [val|] eqn : Hfind_hd. 
        * apply andb_false_iff in Hbs. destruct Hbs; try done. specialize (leqVgt val ub); intro. rewrite H in H0; clear H. rewrite orb_false_l in H0.
          apply (compute_ub_gt_unsat _ _ v _ Hsolve_hd) in H0. apply substitute_c_unsat in H0. destruct H0.
          apply not_true_iff_false; apply forallb_neg_neg. exists c; split; try done. apply find_some in Hc; exact Hc.1.
          apply (substitute_cs_unsat cs1) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3: apply Hfind_cs_in1; done.
          2,4 : move : Hsub1. 2:apply substitute_cs_good_term. 3: apply substitute_cs_power. 2: intros; apply Hterm. 3 : intros; apply Hpower. 3,2 : apply Hfind_cs_in1; done.
          apply Hterm. 2 : apply Hpower. 1,2 : apply find_some in Hc; exact Hc.1.
          assert (hd = (lhs_var1 (substitute_c c c1))).
          { rewrite substitute_c_lhs_eq. apply substitute_cs_none in Hsub0. subst cs0. apply find_constraints_of_path_nil in Hcs0. subst p0_tl. apply find_path_1 in Hp0; done. }
          rewrite -H //.
        * clear Hbs. apply substitute_cs_none in Hsub0; subst cs0. apply find_constraints_of_path_nil in Hcs0; subst p0_tl.
          apply find_path_1 in Hp0; subst hd. apply not_true_iff_false. apply forallb_neg_neg. exists c; split.
          apply find_some in Hc; exact Hc.1. unfold satisfies_constraint1. rewrite Hfind_hd //.
      (* case4 *)
      - destruct (PVM.find hd v) as [val|] eqn : Hfind_hd. 
        * apply andb_false_iff in Hbs. destruct Hbs; try done. specialize (leqVgt val ub); intro. rewrite H in H0; clear H. rewrite orb_false_l in H0.
          apply (compute_ub_gt_unsat _ _ v _ Hsolve_hd) in H0.
          apply not_true_iff_false; apply forallb_neg_neg. exists c; split; try done. apply find_some in Hc; exact Hc.1.
          apply substitute_cs_none in Hsub0; subst cs0. apply find_constraints_of_path_nil in Hcs0; subst p0_tl.
          apply find_path_1 in Hp0; subst hd. done.
        * clear Hbs. apply substitute_cs_none in Hsub0; subst cs0. apply find_constraints_of_path_nil in Hcs0; subst p0_tl.
          apply find_path_1 in Hp0; subst hd. apply not_true_iff_false. apply forallb_neg_neg. exists c; split.
          apply find_some in Hc; exact Hc.1. unfold satisfies_constraint1. rewrite Hfind_hd //.
    - apply Hinitial; clear Hinitial. 
      assert (List.In (x,(lb_x, ub_x)) (PVM.elements (mergeBounds initial))). 
      { assert (~ PVM.mem hd initial) by (apply Hmem; left; done). move : Heq Hin H; clear; intros. unfold mergeBounds in *. apply find_in_elements in Hin.
        destruct (elements_add' initial hd ub) as [l0 [l1 [H1 H0]]]. apply mem_find_none; done.
        rewrite -H0 in Hin. rewrite add_bs_app in Hin. simpl in Hin.
        assert (PVM.find x (PVM.add hd (0, ub) (add_bs l0 (PVM.empty (nat * nat)))) = PVM.find x (add_bs l0 (PVM.empty (nat * nat)))). rewrite find_add_neq; try done.
        apply find_mergeBounds_add_bs_eq with (l:=l1) in H2. rewrite H2 in Hin. rewrite -add_bs_app in Hin.
        apply find_in_elements. rewrite -H1. done. } clear Hin.
      intro. apply In_In_bool in H0. apply In_bool_In_bool' in H0. unfold In_bool' in H0. move : H0. apply forallb_neg_neg.
      exists (x,(lb_x, ub_x)); split; try done. intros. intro. apply mem_add_or in H0. destruct H0. move : H0; apply Hmem; right; done.
      move /eqP : H0 => H0. subst var0. 1,2 : apply NoDup_cons_iff in Hnodup; intuition. }
  apply Hhelper; try done; clear Hhelper. intros.
  assert (In v (mergeBounds initial_valuation)). 
    rewrite /In /initial_valuation /mergeBounds. simpl; intros. rewrite find_empty_None in H0. discriminate.
  try done.
Qed.

Lemma solve_ubs_case2_notin_unsat cs c var0 var1 tbsolved g adj n ubs : (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs -> rhs_power c = nil) ->
  scc.build_graph cs = (g, adj) -> NoDup tbsolved ->
  List.find (fun c : Constraint1 => 1 < Datatypes.length (rhs_terms1 c)) cs = Some c ->
  (*rhs_terms1 c = [:: (coe0, var0), (coe1, var1) & tl'] ->*)
  solve_ubs_case2 tbsolved c var0 var1 g adj n initial_valuation = Some ubs -> 
  forall v, ~In v (mergeBounds ubs) ->
  forallb (satisfies_constraint1 v) cs = false.
Proof.
  intros Hterm Hpower Hbuild HNodup Hc.
  assert (Hhelper : forall (tbsolved : seq ProdVar.t) (ubs initial : Valuation), (forall v, ~In v (mergeBounds initial) -> forallb (satisfies_constraint1 v) cs = false) ->
    (forall var, List.In var tbsolved -> ~PVM.mem var initial) -> NoDup tbsolved ->
    solve_ubs_case2 tbsolved c var0 var1 g adj n initial = Some ubs -> forall v, ~In v (mergeBounds ubs) -> forallb (satisfies_constraint1 v) cs = false).
  { elim. simpl; intros ubs0 initial Hinitial Hmem Hnodup Hsolve. inversion Hsolve. rewrite -H0 //.
    simpl; intros hd tl IH ubs0 initial Hinitial Hmem Hnodup Hsolve. case Hsolve_hd : (solve_ub_case2 hd c var0 var1 g adj n) => [ub|]; rewrite Hsolve_hd in Hsolve; try discriminate.
    move : Hsolve; apply IH. clear IH. intros. assert (~In_bool v (PVM.elements (mergeBounds (PVM.add hd ub initial)))) by (intro; apply In_In_bool in H0; done). clear H.
    assert (~In_bool' v (PVM.elements (elt:=nat * nat) (mergeBounds (PVM.add hd ub initial)))) by (intro; apply In_bool_In_bool' in H; done). clear H0.
    unfold In_bool' in H. apply forallb_neg_neg in H. destruct H as [[x [lb_x ub_x]] [Hin Hbs]].
    destruct (x == hd) eqn : Heq; move /eqP : Heq => Heq.
    - subst x. assert (lb_x = 0 /\ ub_x = ub). 
      { apply find_in_elements in Hin. unfold mergeBounds in Hin. assert (~ PVM.mem hd initial) by (apply Hmem; left; done). move : H Hin; clear; intros. 
        specialize (elements_add' initial hd ub); intro. destruct H0 as [l0 [l1 [_ Hele1]]]. apply mem_find_none; done.
        rewrite -Hele1 in Hin. rewrite add_bs_app in Hin. simpl in Hin.
        rewrite find_mergeBounds_add_bs_not_in in Hin. rewrite find_add_eq in Hin. inversion Hin; subst lb_x ub_x; done.
        specialize (key_NoDup _ (PVM.add hd ub initial)); intro. rewrite -Hele1 split_app in H0; simpl in H0. destruct (List.split l1) as [left right] eqn : Hsplit.
        simpl in H0. simpl. apply NoDup_app_remove_l in H0. apply NoDup_cons_iff in H0; exact H0.1. }
      clear Hin Hinitial. move : H => [H H']; subst lb_x ub_x.
      unfold solve_ub_case2 in Hsolve_hd.
      case Hp0 : (scc.find_path g hd n [] (lhs_var1 c) None) => [l|]; rewrite Hp0 in Hsolve_hd; try discriminate.
      case Hl : l => [|p0_hd p0_tl]; rewrite Hl in Hsolve_hd; try discriminate. rewrite Hl in Hp0; clear Hl l. 
      case Hp1 : (scc.find_path g var0 n [] hd None) => [l|]; rewrite Hp1 in Hsolve_hd; try discriminate.
      case Hl : l => [|p1_hd p1_tl]; rewrite Hl in Hsolve_hd; try discriminate. rewrite Hl in Hp1; clear Hl l. 
      case Hp2 : (scc.find_path g var1 n [] hd None) => [l|]; rewrite Hp2 in Hsolve_hd; try discriminate.
      case Hl : l => [|p2_hd p2_tl]; rewrite Hl in Hsolve_hd; try discriminate. rewrite Hl in Hp2; clear Hl l. 
      case Hcs0 : (find_constraints_of_path adj p0_hd p0_tl) => [cs0|]; rewrite Hcs0 in Hsolve_hd; try discriminate.
      case Hcs1 : (find_constraints_of_path adj p1_hd p1_tl) => [cs1|]; rewrite Hcs1 in Hsolve_hd; try discriminate.
      case Hcs2 : (find_constraints_of_path adj p2_hd p2_tl) => [cs2|]; rewrite Hcs2 in Hsolve_hd; try discriminate.
      specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs0) as Hfind_cs_in0.
      specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs1) as Hfind_cs_in1.
      specialize (find_constraints_of_path_subset _ _ _ _ _ _ Hterm Hbuild Hcs2) as Hfind_cs_in2.
      case Hsub0 : (substitute_cs cs0) => [c0|]; rewrite Hsub0 in Hsolve_hd.
      case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in Hsolve_hd.
      case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in Hsolve_hd.
      (* case1 *)
      - destruct (PVM.find hd v) as [val|] eqn : Hfind_hd. 
        * apply andb_false_iff in Hbs. destruct Hbs; try done. specialize (leqVgt val ub); intro. rewrite H in H0; clear H. rewrite orb_false_l in H0.
          apply (compute_ub_gt_unsat _ _ v _ Hsolve_hd) in H0. apply substitute_c_unsat in H0. destruct H0. 
          apply (substitute_cs_unsat cs0) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3: apply Hfind_cs_in0; done.
          apply substitute_c_unsat in H. destruct H. apply substitute_c_unsat in H. destruct H. apply not_true_iff_false; apply forallb_neg_neg. exists c; split; try done. apply find_some in Hc; exact Hc.1.
          apply (substitute_cs_unsat cs1) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3:  apply Hfind_cs_in1; done.
          6,11 : apply substitute_c_good_term. 8 : apply substitute_c_good_term. 12,16: apply substitute_c_power. 14 : apply substitute_c_power. 1,6,8:apply Hterm. 5,12,14: apply Hpower. 1-3,5-7 : apply find_some in Hc; exact Hc.1.
          1,4,5 : move : Hsub1; apply substitute_cs_good_term. 4,8,9 : move : Hsub1; apply substitute_cs_power. 1-6: intros. 1-3 : apply Hterm; apply Hfind_cs_in1; done. 1-3 : apply Hpower; apply Hfind_cs_in1; done.
          apply (substitute_cs_unsat cs2) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3: apply Hfind_cs_in2; done.
          1,2: move : Hsub2; apply substitute_cs_good_term. 3,4: move : Hsub2; apply substitute_cs_power. 1-4: intros. 1-2 : apply Hterm; apply Hfind_cs_in2; done. 1-2 : apply Hpower; apply Hfind_cs_in2; done.
          1,2: move : Hsub0. apply substitute_cs_good_term; intros; apply Hterm. 2:apply substitute_cs_power; intros; apply Hpower. 1,2 : apply Hfind_cs_in0; done.  
          assert (hd = (lhs_var1 (substitute_c c0 (substitute_c (substitute_c c c1) c2)))). 
          { rewrite substitute_c_lhs_eq. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
          apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 Hlhs0]]. rewrite -Hlhs0. symmetry. move : Hbuild Hcs0 Hhd0; apply find_constraint_hd_eq; try done. }
          rewrite -H //.
        * clear Hbs. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
          apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 _]]. 
          generalize Hhd0; apply (find_constraint_hd_eq _ _ _ _ _ _ _ Hterm Hbuild Hcs0) in Hhd0; intro. apply not_true_iff_false. apply forallb_neg_neg. exists c_hd; split.
          apply Hfind_cs_in0. destruct cs0; try done. simpl in Hhd1. inversion Hhd1; subst c_hd. simpl; left; done. 
          unfold satisfies_constraint1. rewrite Hhd0 Hfind_hd //.
      (* case2 *)
      - destruct (PVM.find hd v) as [val|] eqn : Hfind_hd. 
        * apply andb_false_iff in Hbs. destruct Hbs; try done. specialize (leqVgt val ub); intro. rewrite H in H0; clear H. rewrite orb_false_l in H0.
          apply (compute_ub_gt_unsat _ _ v _ Hsolve_hd) in H0. apply substitute_c_unsat in H0. destruct H0. 
          apply (substitute_cs_unsat cs0) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3: apply Hfind_cs_in0; done.
          apply substitute_c_unsat in H. destruct H. apply not_true_iff_false; apply forallb_neg_neg. exists c; split; try done. apply find_some in Hc; exact Hc.1.
          apply (substitute_cs_unsat cs1) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3:  apply Hfind_cs_in1; done.
          6 : apply substitute_c_good_term. 9: apply substitute_c_power. 1,6:apply Hterm. 4,9: apply Hpower. 1,2,4,5 : apply find_some in Hc; exact Hc.1.
          1,4 : move : Hsub1; apply substitute_cs_good_term. 3,6 : move : Hsub1; apply substitute_cs_power. 1-4: intros. 1,2 : apply Hterm; apply Hfind_cs_in1; done. 1,2 : apply Hpower; apply Hfind_cs_in1; done.
          1,2: move : Hsub0. apply substitute_cs_good_term; intros; apply Hterm. 2:apply substitute_cs_power; intros; apply Hpower. 1,2 : apply Hfind_cs_in0; done.  
          assert (hd = (lhs_var1 (substitute_c c0 (substitute_c c c1)))). 
          { rewrite substitute_c_lhs_eq. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
          apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 Hlhs0]]. rewrite -Hlhs0. symmetry. move : Hbuild Hcs0 Hhd0; apply find_constraint_hd_eq; try done. }
          rewrite -H //.
        * clear Hbs. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
          apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 _]]. 
          generalize Hhd0; apply (find_constraint_hd_eq _ _ _ _ _ _ _ Hterm Hbuild Hcs0) in Hhd0; intro. apply not_true_iff_false. apply forallb_neg_neg. exists c_hd; split.
          apply Hfind_cs_in0. destruct cs0; try done. simpl in Hhd1. inversion Hhd1; subst c_hd. simpl; left; done. 
          unfold satisfies_constraint1. rewrite Hhd0 Hfind_hd //.
      case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in Hsolve_hd.
      (* case3 *)
      - destruct (PVM.find hd v) as [val|] eqn : Hfind_hd. 
        * apply andb_false_iff in Hbs. destruct Hbs; try done. specialize (leqVgt val ub); intro. rewrite H in H0; clear H. rewrite orb_false_l in H0.
          apply (compute_ub_gt_unsat _ _ v _ Hsolve_hd) in H0. apply substitute_c_unsat in H0. destruct H0. 
          apply (substitute_cs_unsat cs0) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3: apply Hfind_cs_in0; done.
          apply substitute_c_unsat in H. destruct H. apply not_true_iff_false; apply forallb_neg_neg. exists c; split; try done. apply find_some in Hc; exact Hc.1.
          apply (substitute_cs_unsat cs2) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3:  apply Hfind_cs_in2; done.
          6 : apply substitute_c_good_term. 9: apply substitute_c_power. 1,6:apply Hterm. 4,9: apply Hpower. 1,2,4,5 : apply find_some in Hc; exact Hc.1.
          1,4 : move : Hsub2; apply substitute_cs_good_term. 3,6 : move : Hsub2; apply substitute_cs_power. 1-4: intros. 1,2 : apply Hterm; apply Hfind_cs_in2; done. 1,2 : apply Hpower; apply Hfind_cs_in2; done.
          1,2: move : Hsub0. apply substitute_cs_good_term; intros; apply Hterm. 2:apply substitute_cs_power; intros; apply Hpower. 1,2 : apply Hfind_cs_in0; done.  
          assert (hd = (lhs_var1 (substitute_c c0 (substitute_c c c2)))). 
          { rewrite substitute_c_lhs_eq. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
          apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 Hlhs0]]. rewrite -Hlhs0. symmetry. move : Hbuild Hcs0 Hhd0; apply find_constraint_hd_eq; try done. }
          rewrite -H //.
        * clear Hbs. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
          apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 _]]. 
          generalize Hhd0; apply (find_constraint_hd_eq _ _ _ _ _ _ _ Hterm Hbuild Hcs0) in Hhd0; intro. apply not_true_iff_false. apply forallb_neg_neg. exists c_hd; split.
          apply Hfind_cs_in0. destruct cs0; try done. simpl in Hhd1. inversion Hhd1; subst c_hd. simpl; left; done. 
          unfold satisfies_constraint1. rewrite Hhd0 Hfind_hd //.
      (* case4 *)
      - destruct (PVM.find hd v) as [val|] eqn : Hfind_hd. 
        * apply andb_false_iff in Hbs. destruct Hbs; try done. specialize (leqVgt val ub); intro. rewrite H in H0; clear H. rewrite orb_false_l in H0.
          apply (compute_ub_gt_unsat _ _ v _ Hsolve_hd) in H0. apply substitute_c_unsat in H0. destruct H0. 
          apply (substitute_cs_unsat cs0) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3: apply Hfind_cs_in0; done.
          apply not_true_iff_false; apply forallb_neg_neg. exists c; split; try done. apply find_some in Hc; exact Hc.1.
          1,3 : move : Hsub0. apply substitute_cs_good_term. 2: apply substitute_cs_power. intros; apply Hterm. 2 : intros; apply Hpower. 1,2 : apply Hfind_cs_in0; done.
          apply Hterm. 2 : apply Hpower. 1,2 : apply find_some in Hc; exact Hc.1.
          assert (hd = (lhs_var1 (substitute_c c0 c))).
          { rewrite substitute_c_lhs_eq. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
            apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 Hlhs0]]. rewrite -Hlhs0. symmetry. move : Hbuild Hcs0 Hhd0; apply find_constraint_hd_eq; try done. }
          rewrite -H //.
        * clear Hbs. apply find_path_hd_eq_tgt in Hp0. simpl in Hp0; inversion Hp0; clear Hp0. subst p0_hd.
          apply substitute_cs_lhs_eq in Hsub0. destruct Hsub0 as [c_hd [Hhd0 _]]. 
          generalize Hhd0; apply (find_constraint_hd_eq _ _ _ _ _ _ _ Hterm Hbuild Hcs0) in Hhd0; intro. apply not_true_iff_false. apply forallb_neg_neg. exists c_hd; split.
          apply Hfind_cs_in0. destruct cs0; try done. simpl in Hhd1. inversion Hhd1; subst c_hd. simpl; left; done. 
          unfold satisfies_constraint1. rewrite Hhd0 Hfind_hd //.
      case Hsub1 : (substitute_cs cs1) => [c1|]; rewrite Hsub1 in Hsolve_hd.
      case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in Hsolve_hd.
      (* case 5 *)
      - destruct (PVM.find hd v) as [val|] eqn : Hfind_hd. 
        * apply andb_false_iff in Hbs. destruct Hbs; try done. specialize (leqVgt val ub); intro. rewrite H in H0; clear H. rewrite orb_false_l in H0.
          apply (compute_ub_gt_unsat _ _ v _ Hsolve_hd) in H0. apply substitute_c_unsat in H0. destruct H0. 
          apply substitute_c_unsat in H. destruct H. apply not_true_iff_false; apply forallb_neg_neg. exists c; split; try done. apply find_some in Hc; exact Hc.1.
          apply (substitute_cs_unsat cs1) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3: apply Hfind_cs_in1; done.
          6 : apply substitute_c_good_term. 9: apply substitute_c_power. 1,6:apply Hterm. 4,9: apply Hpower. 1,2,4,5 : apply find_some in Hc; exact Hc.1.
          1,4 : move : Hsub1; apply substitute_cs_good_term. 3,6 : move : Hsub1; apply substitute_cs_power. 1-4: intros. 1,2 : apply Hterm; apply Hfind_cs_in1; done. 1,2 : apply Hpower; apply Hfind_cs_in1; done.
          apply (substitute_cs_unsat cs2) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3:  apply Hfind_cs_in2; done.
          1,2: move : Hsub2. apply substitute_cs_good_term; intros; apply Hterm. 2:apply substitute_cs_power; intros; apply Hpower. 1,2 : apply Hfind_cs_in2; done.  
          assert (hd = (lhs_var1 (substitute_c (substitute_c c c1) c2))). 
          { rewrite substitute_c_lhs_eq. rewrite substitute_c_lhs_eq. apply substitute_cs_none in Hsub0. subst cs0. apply find_constraints_of_path_nil in Hcs0. subst p0_tl. apply find_path_1 in Hp0; done. }
          rewrite -H //.
        * clear Hbs. apply substitute_cs_none in Hsub0; subst cs0. apply find_constraints_of_path_nil in Hcs0; subst p0_tl.
          apply find_path_1 in Hp0; subst hd. apply not_true_iff_false. apply forallb_neg_neg. exists c; split.
          apply find_some in Hc; exact Hc.1. unfold satisfies_constraint1. rewrite Hfind_hd //.
      (* case 6 *)
      - destruct (PVM.find hd v) as [val|] eqn : Hfind_hd. 
        * apply andb_false_iff in Hbs. destruct Hbs; try done. specialize (leqVgt val ub); intro. rewrite H in H0; clear H. rewrite orb_false_l in H0.
          apply (compute_ub_gt_unsat _ _ v _ Hsolve_hd) in H0. apply substitute_c_unsat in H0. destruct H0.
          apply not_true_iff_false; apply forallb_neg_neg. exists c; split; try done. apply find_some in Hc; exact Hc.1.
          apply (substitute_cs_unsat cs1) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3: apply Hfind_cs_in1; done.
          2,4 : move : Hsub1. 2:apply substitute_cs_good_term. 3: apply substitute_cs_power. 2: intros; apply Hterm. 3 : intros; apply Hpower. 3,2 : apply Hfind_cs_in1; done.
          apply Hterm. 2 : apply Hpower. 1,2 : apply find_some in Hc; exact Hc.1.
          assert (hd = (lhs_var1 (substitute_c c c1))).
          { rewrite substitute_c_lhs_eq. apply substitute_cs_none in Hsub0. subst cs0. apply find_constraints_of_path_nil in Hcs0. subst p0_tl. apply find_path_1 in Hp0; done. }
          rewrite -H //.
        * clear Hbs. apply substitute_cs_none in Hsub0; subst cs0. apply find_constraints_of_path_nil in Hcs0; subst p0_tl.
          apply find_path_1 in Hp0; subst hd. apply not_true_iff_false. apply forallb_neg_neg. exists c; split.
          apply find_some in Hc; exact Hc.1. unfold satisfies_constraint1. rewrite Hfind_hd //.
      case Hsub2 : (substitute_cs cs2) => [c2|]; rewrite Hsub2 in Hsolve_hd.
      (* case 7 *)
      - destruct (PVM.find hd v) as [val|] eqn : Hfind_hd. 
        * apply andb_false_iff in Hbs. destruct Hbs; try done. specialize (leqVgt val ub); intro. rewrite H in H0; clear H. rewrite orb_false_l in H0.
          apply (compute_ub_gt_unsat _ _ v _ Hsolve_hd) in H0. apply substitute_c_unsat in H0. destruct H0.
          apply not_true_iff_false; apply forallb_neg_neg. exists c; split; try done. apply find_some in Hc; exact Hc.1.
          apply (substitute_cs_unsat cs2) in H; try done. apply not_true_iff_false in H; apply forallb_neg_neg in H. apply not_true_iff_false; apply forallb_neg_neg.
          destruct H as [y [Hin Hunsat]]. exists y; split; try done. 2 : intros; apply Hterm. 3: intros; apply Hpower. 1-3: apply Hfind_cs_in2; done.
          2,4 : move : Hsub2. 2:apply substitute_cs_good_term. 3: apply substitute_cs_power. 2: intros; apply Hterm. 3 : intros; apply Hpower. 3,2 : apply Hfind_cs_in2; done.
          apply Hterm. 2 : apply Hpower. 1,2 : apply find_some in Hc; exact Hc.1.
          assert (hd = (lhs_var1 (substitute_c c c2))).
          { rewrite substitute_c_lhs_eq. apply substitute_cs_none in Hsub0. subst cs0. apply find_constraints_of_path_nil in Hcs0. subst p0_tl. apply find_path_1 in Hp0; done. }
          rewrite -H //.
        * clear Hbs. apply substitute_cs_none in Hsub0; subst cs0. apply find_constraints_of_path_nil in Hcs0; subst p0_tl.
          apply find_path_1 in Hp0; subst hd. apply not_true_iff_false. apply forallb_neg_neg. exists c; split.
          apply find_some in Hc; exact Hc.1. unfold satisfies_constraint1. rewrite Hfind_hd //.
      (* case 8 *)
      - destruct (PVM.find hd v) as [val|] eqn : Hfind_hd. 
        * apply andb_false_iff in Hbs. destruct Hbs; try done. specialize (leqVgt val ub); intro. rewrite H in H0; clear H. rewrite orb_false_l in H0.
          apply (compute_ub_gt_unsat _ _ v _ Hsolve_hd) in H0.
          apply not_true_iff_false; apply forallb_neg_neg. exists c; split; try done. apply find_some in Hc; exact Hc.1.
          apply substitute_cs_none in Hsub0; subst cs0. apply find_constraints_of_path_nil in Hcs0; subst p0_tl.
          apply find_path_1 in Hp0; subst hd. done.
        * clear Hbs. apply substitute_cs_none in Hsub0; subst cs0. apply find_constraints_of_path_nil in Hcs0; subst p0_tl.
          apply find_path_1 in Hp0; subst hd. apply not_true_iff_false. apply forallb_neg_neg. exists c; split.
          apply find_some in Hc; exact Hc.1. unfold satisfies_constraint1. rewrite Hfind_hd //.
    - apply Hinitial; clear Hinitial. 
      assert (List.In (x,(lb_x, ub_x)) (PVM.elements (mergeBounds initial))). 
      { assert (~ PVM.mem hd initial) by (apply Hmem; left; done). move : Heq Hin H; clear; intros. unfold mergeBounds in *. apply find_in_elements in Hin.
        destruct (elements_add' initial hd ub) as [l0 [l1 [H1 H0]]]. apply mem_find_none; done.
        rewrite -H0 in Hin. rewrite add_bs_app in Hin. simpl in Hin.
        assert (PVM.find x (PVM.add hd (0, ub) (add_bs l0 (PVM.empty (nat * nat)))) = PVM.find x (add_bs l0 (PVM.empty (nat * nat)))). rewrite find_add_neq; try done.
        apply find_mergeBounds_add_bs_eq with (l:=l1) in H2. rewrite H2 in Hin. rewrite -add_bs_app in Hin.
        apply find_in_elements. rewrite -H1. done. } clear Hin.
      intro. apply In_In_bool in H0. apply In_bool_In_bool' in H0. unfold In_bool' in H0. move : H0. apply forallb_neg_neg.
      exists (x,(lb_x, ub_x)); split; try done. intros. intro. apply mem_add_or in H0. destruct H0. move : H0; apply Hmem; right; done.
      move /eqP : H0 => H0. subst var. 1,2 : apply NoDup_cons_iff in Hnodup; intuition. }
  apply Hhelper; try done; clear Hhelper. intros.
  assert (In v (mergeBounds initial_valuation)). 
    rewrite /In /initial_valuation /mergeBounds. simpl; intros. rewrite find_empty_None in H0. discriminate.
  try done.
Qed.

Lemma solve_ubs_aux_notin_unsat hd cs ubs : solve_ubs_aux hd cs = Some ubs -> NoDup hd ->
  (forall c, List.In c cs -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs -> rhs_power c = nil) ->
  forall v, ~In v (mergeBounds ubs) -> forallb (satisfies_constraint1 v) cs = false.
Proof.
  intros Hsolve Hnodup Hterm Hpower; unfold solve_ubs_aux in Hsolve. destruct (scc.build_graph cs) as [g adj] eqn : Hbuild.
  case Hcase1 : (List.find (fun c : Constraint1 => List.existsb (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) cs) => [c|]; rewrite Hcase1 in Hsolve.
  - (* lhs >= coe * var + ... + cst c, coe > 1 *)
    intros. case Hfind_terms : (List.find (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) => [[coe var]|]; rewrite Hfind_terms in Hsolve; try discriminate.
    move : Hbuild Hnodup Hcase1 Hsolve v H; apply solve_ubs_case1_notin_unsat; try done. 
  case Hcase2 : (List.find (fun c : Constraint1 => 1 < Datatypes.length (rhs_terms1 c)) cs) => [c|]; rewrite Hcase2 in Hsolve; try discriminate.
  - (* lhs >= coe0 * var0 + coe1 * var1 + ... + cst c *)
    intros. case Hterms_hd : (rhs_terms1 c) => [|[coe0 var0] tl]; rewrite Hterms_hd in Hsolve; try discriminate.
    case Hterms_hd' : tl => [|[coe1 var1] tl']; rewrite Hterms_hd' in Hsolve; try discriminate. rewrite Hterms_hd' in Hterms_hd; clear Hterms_hd' tl.
    move : Hbuild Hnodup Hcase2 Hsolve v H; apply solve_ubs_case2_notin_unsat; try done. 
Qed.

Lemma solve_scc_unsat hd cs1 : hd <> nil -> NoDup hd -> solve_scc hd cs1 = None -> cs1 <> nil -> (forall c, List.In c cs1 -> List.In (lhs_var1 c) hd) -> 
  (forall c, List.In c cs1 -> good_terms (rhs_terms1 c)) -> (forall c, List.In c cs1 -> rhs_power c = nil) ->
  (forall c, List.In c cs1 -> (forall v, List.In v (constraint1_vars c) -> List.In v hd)) ->
  forall v, forallb (satisfies_constraint1 v) cs1 = false.
Proof.
  rewrite /solve_scc; intros Hnotemptyscc Hnodup Hsolve Hnotempty Hlhs_in_hd Hterms Hpowers Hvars_in_hd.
  destruct hd as [|a l] eqn : Hhd. done.
  destruct l as [|hda tla] eqn : Htl.
  - (* trivial *)
    clear Htl Hhd Hnotemptyscc l hd Hnodup. assert (Hlhs : forall c, List.In c cs1 -> lhs_var1 c = a) by (intros; apply Hlhs_in_hd in H; simpl in H; destruct H; try done).
    destruct (List.partition (fun c : Constraint1 => (rhs_terms1 c == []) && (rhs_power c == [])) cs1) as [cs cs_have_v] eqn : Hpart.
    case Hsat : (forallb [eta satisfies_constraint1 (PVM.add a (max_nl (List.map [eta rhs_const1] cs) 0) initial_valuation)] cs_have_v); rewrite Hsat in Hsolve; try discriminate.
    clear Hsolve. 
    intros. remember (max_nl (List.map [eta rhs_const1] cs) 0) as new_val.
    case Hmem : (PVM.find a v) => [val|]. 
    case Hgeq : (new_val <= val).
    * apply not_true_iff_false; apply forallb_neg_neg; 
      apply not_true_iff_false in Hsat; apply forallb_neg_neg in Hsat. destruct Hsat as [x [Hin Hunsat]].
      exists x; split. apply (elements_in_partition _ _ Hpart); right; done.
      { rewrite /satisfies_constraint1 in Hunsat; rewrite /satisfies_constraint1.
        assert (List.In x cs1). apply (elements_in_partition _ _ Hpart); right; done. specialize (Hlhs _ H) as H2.
        rewrite H2 Hmem; rewrite H2 find_add_eq in Hunsat. apply Z.leb_gt. apply Z.leb_gt in Hunsat.
        rewrite /rhs_value1; rewrite /rhs_value1 in Hunsat.
        specialize (Hpowers _ H) as Hpowerx. rewrite Hpowerx in Hunsat; rewrite Hpowerx; simpl in Hunsat; simpl. 
          rewrite Z.add_0_r; rewrite Z.add_0_r in Hunsat. 
        rewrite partition_as_filter in Hpart. inversion Hpart; clear Hpart. clear H1. 
        rewrite -H3 in Hin. apply filter_In in Hin. destruct Hin as [_ Hhave_v].
        apply negb_true_iff in Hhave_v. apply andb_false_iff in Hhave_v. destruct Hhave_v.
        + (* (terms-v) + power *)
          move /eqP : H0 => H0.
          assert ((terms_value (PVM.add a new_val initial_valuation) (rhs_terms1 x) (rhs_const1 x)) - (Z.of_nat new_val)
            <= (terms_value v (rhs_terms1 x) (rhs_const1 x)) - (Z.of_nat val))%Z.
          { assert (Hgood_terms : good_terms (rhs_terms1 x)) by (apply Hterms; done). 
            rewrite /good_terms in Hgood_terms; move : Hgood_terms => [Hcoe Hnodup].
            assert (exists coe, rhs_terms1 x = [(coe,a)]).
            { clear Hunsat. destruct (rhs_terms1 x) as [|(c, var) tl] eqn : Hrhs; [contradiction |].
              clear H0. simpl in Hnodup. destruct (List.split tl) as [left right] eqn : Hsplit.
              simpl in Hnodup.
              assert (List.In var [a]) as Heq.
              { apply (Hvars_in_hd _ H). rewrite /constraint1_vars. simpl; right. apply in_or_app. left.
                rewrite Hrhs. simpl; left; done. }
              simpl in Heq. destruct Heq; try done.  
              subst var.
              destruct tl as [|(c', var') tl'].
              - exists c; auto.
              - assert (List.In var' [a]) as Heq.
                { apply (Hvars_in_hd _ H). rewrite /constraint1_vars. simpl; right. apply in_or_app. left.
                  rewrite Hrhs. simpl; right; left; done. }
                simpl in Heq. destruct Heq; try done.  
                subst var'. simpl in Hsplit. destruct (List.split tl') as [left' right'] eqn : Hsplit'.
                inversion Hsplit. rewrite -H4 in Hnodup. move : Hnodup; clear; intros.
                apply NoDup_cons_iff in Hnodup. move : Hnodup => [Hnodup _].
                intuition. }
            destruct H1 as [coe Hterm]. clear H0 Hnodup.
            rewrite Hterm; simpl. rewrite Hmem find_add_eq.
            assert (coe <> 0) by (apply Hcoe with (var := a); rewrite Hterm; apply in_eq).
            move : H0 Hgeq; clear.
            { intros Hcoe Hle.
              rewrite <- Z.add_sub_assoc, <- Z.add_sub_assoc.
              apply Z.add_le_mono_l.
              rewrite Nat2Z.inj_mul; rewrite Nat2Z.inj_mul.
              rewrite -{2}(Z.mul_1_l (Z.of_nat new_val)).
              rewrite -{2}(Z.mul_1_l (Z.of_nat val)).
              rewrite -Z.mul_sub_distr_r; rewrite -Z.mul_sub_distr_r.
              assert (Hcoeff_nonneg : ((Z.of_nat coe - 1) >= 0)%Z) by
                (destruct coe; [contradiction|]; lia).  
              apply Zmult_le_compat_l; [|lia].
              apply Nat2Z.inj_le. apply (elimT leP). done. }}
          apply Zlt_left_lt in Hunsat. apply (Z.lt_le_trans _ _ _ Hunsat) in H1.
          rewrite -Z.add_opp_r in H1. apply Zlt_left_rev in H1; done.
        rewrite Hpowerx in H0. discriminate. } 
    * specialize (leqVgt new_val val); intros. rewrite Hgeq in H. rewrite orb_false_l in H. clear Hgeq.
      rewrite Heqnew_val in H. 
      apply max_list_lt in H. destruct H. intuition. destruct H as [z [Hin Hlt]].
      apply in_map_iff in Hin. destruct Hin as [x [Hcst Hin]].
      rewrite partition_as_filter in Hpart. inversion Hpart; clear Hpart H1.
      apply not_true_iff_false; apply forallb_neg_neg. rewrite -H0 in Hin; apply filter_In in Hin.
      move : Hin => [Hin Hcs]. move /andP : Hcs => [Hterm Hpower]. move /eqP : Hterm => Hterm; move /eqP : Hpower => Hpower.
      exists x; split; try done. 
      rewrite /satisfies_constraint1. apply Hlhs in Hin. rewrite Hin Hmem.
      apply Z.leb_gt. rewrite /rhs_value1 Hterm Hpower. simpl. rewrite Z.add_0_r.
      rewrite Hcst //. 
    * apply not_true_iff_false; apply forallb_neg_neg.
      destruct (destruct_list cs1).
      destruct s as [hd [tl Hcons]]. 2 : done. exists hd. rewrite Hcons. split. simpl; left; done. rewrite /satisfies_constraint1.
      assert (List.In hd cs1) by (rewrite Hcons; simpl; left; done). specialize (Hlhs _ H) as H2. rewrite H2 Hmem //.
  - (* scc *)
    rewrite -Hhd in Hsolve Hvars_in_hd Hlhs_in_hd Hnodup. clear Htl Hhd Hnotemptyscc l a.
    case His_simple : (is_simple_cycle cs1); rewrite His_simple in Hsolve.
    * (* floyd *)
      move : Hsolve; apply scc_none_unsat.
    * (* bab *)
      case Hubs : (solve_ubs_aux hd (List.filter (fun c : Constraint1 => Datatypes.length (rhs_terms1 c) != 0) cs1)) => [ubs|]; rewrite Hubs in Hsolve; try discriminate.
      intro. case Hin : (In_bool v (PVM.elements (mergeBounds ubs))).
      + apply In_In_bool in Hin. apply bab_bin_none_unsat with (v := v) in Hsolve; try done. 
      + assert (~In v (mergeBounds ubs)) by (intro; apply In_In_bool in H; rewrite H in Hin; discriminate).
        apply solve_ubs_aux_notin_unsat with (v := v) in Hubs; try done. 
        move : Hubs Hterms Hpowers; clear; intros. apply not_true_iff_false; apply forallb_neg_neg. apply not_true_iff_false in Hubs; apply forallb_neg_neg in Hubs. destruct Hubs as [x [Hin Hunsat]].
          apply filter_In in Hin; move : Hin => [Hin _]. exists x; split; try done. 
        1,2: intros; apply filter_In in H0; move : H0 => [H0 _]. apply Hterms; done. apply Hpowers; done.
      clear Hsolve. assert (forall v : Valuation, ~ forallb (satisfies_constraint1 v) (List.filter (fun c : Constraint1 => Datatypes.length (rhs_terms1 c) != 0) cs1)).
      { move : Hubs; apply no_ubs_unsat. apply not_true_iff_false in His_simple. move : His_simple; apply contra_not.
        unfold is_simple_cycle; intros. remember (fun c : Constraint1 =>
          match rhs_terms1 c with
          | [] => true
          | p :: l =>
              let (n, _) := p in
              match n with
              | 0 => false
              | n0.+1 => match n0 with
                        | 0 => match l with
                                | [] => true
                                | _ :: _ => false
                                end
                        | _.+1 => false
                        end
              end
          end) as f. apply forallb_forall. remember (List.filter
          (fun c : Constraint1 => Datatypes.length (rhs_terms1 c) != 0) cs1) as cs1'.
        assert (forall c, List.In c cs1' -> f c = true) by (apply forallb_forall; done). intros. destruct (Datatypes.length (rhs_terms1 x) == 0) eqn : Hcst.
        + move /eqP : Hcst => Hcst. subst f. move : Hcst; clear; intro. destruct (rhs_terms1 x); try done.
        + apply H0. rewrite Heqcs1'; apply filter_In; split; try done. remember (Datatypes.length (rhs_terms1 x)) as a. move : Hcst; clear.
          unfold "!=". intros. rewrite Hcst //.
        intros. apply constraint1s_vars2constraint1_vars in H. destruct H as [x [Hin0 Hin1]]. apply filter_In in Hin0. move : Hin0.1 var Hin1; apply Hvars_in_hd.
        intros; apply Hpowers. 2 : intros; apply Hterms. 1,2 : apply filter_In in H; exact H.1. }
      move : H; clear; intros. apply not_true_iff_false. apply forallb_neg_neg. specialize (H v). apply forallb_neg_neg in H.
      destruct H as [y [Hin Hunsat]]; exists y; split; try done. apply filter_In in Hin. exact Hin.1.
Qed.

Lemma merge_smaller temp_s nv : forall a initial new_values, le initial temp_s -> le nv temp_s ->
    merge_solution a initial nv = Some new_values -> le new_values temp_s.
Proof.
  elim. simpl; intros. inversion H1. rewrite -H3 //.
  simpl; intros. case Hfind : (PVM.find (elt:=nat) a nv) => [val|]; rewrite Hfind in H2; try discriminate.
  apply H in H2; try done.
  move : H0 H1 Hfind; clear; unfold le; intros.
  case Heq : (var == a); move /eqP : Heq => Heq.
  - subst var. apply H1 in Hfind. rewrite find_add_eq in H. inversion H. rewrite -H3 //.
  - rewrite find_add_neq in H; try done. apply H0 in H. done.
Qed.

Lemma remove_solved_correctness initial nv new_values : forall terms cst new_terms new_cst, remove_solved initial terms = (new_terms, new_cst) -> 
  (forall (var : ProdVar.t) (value0 : nat), PVM.find var initial = Some value0 -> PVM.find var new_values = Some value0) ->
  (forall (var : ProdVar.t) (value0 : nat), PVM.find var nv = Some value0 -> PVM.find var new_values = Some value0) ->
  (forall (var : ProdVar.t), PVM.find var initial = None -> PVM.find var nv = None -> PVM.find var new_values = None) ->
  terms_value new_values terms cst = terms_value nv new_terms (cst + new_cst).
Proof.
  intros. move : terms cst new_terms new_cst H; elim. 
  - simpl; intros. inversion H; simpl. rewrite Z.add_0_r //.
  - simpl; intros [coe var] tl IH; intros. 
    case Hfind : (PVM.find (elt:=nat) var initial) => [val|]; rewrite Hfind in H. 
    * (* find some, var is solved *)
      simpl. destruct (remove_solved initial tl) as [new_terms_tl new_cst_tl] eqn : Hnew_tl.
      inversion H; clear H; subst. apply H0 in Hfind. rewrite Hfind. 
      rewrite (IH _ new_terms new_cst_tl); try done.
      rewrite (Z.add_comm new_cst_tl (Z.of_nat (coe * val))) Z.add_assoc //.
    * (* find none *)
      simpl. destruct (remove_solved initial tl) as [new_terms_tl new_cst_tl] eqn : Hnew_tl.
      inversion H; clear H; subst. simpl.
      rewrite terms_value_cst_add. rewrite terms_value_cst_add.
      case Hfind' : (PVM.find (elt:=nat) var nv) => [val|].
      + apply H1 in Hfind'. rewrite Hfind'. 
        apply Z.add_cancel_r. apply IH; try done.
      + specialize (H2 _ Hfind Hfind'). rewrite H2 muln0. simpl. rewrite Z.add_0_r Z.add_0_r.
        apply IH; try done.
Qed.

Lemma remove_solved_c_correctness nv initial new_values x : 
  rhs_power x = nil ->
  (forall (var : ProdVar.t) (value0 : nat), PVM.find var initial = Some value0 -> PVM.find var new_values = Some value0) ->
  (forall (var : ProdVar.t) (value0 : nat), PVM.find var nv = Some value0 -> PVM.find var new_values = Some value0) ->
  (forall (var : ProdVar.t), PVM.find var initial = None -> PVM.find var nv = None -> PVM.find var new_values = None) ->
  rhs_value1 new_values x = rhs_value1 nv (remove_solved_c initial x).
Proof.
  intros; rewrite /remove_solved_c.
  destruct (remove_solved initial (rhs_terms1 x)) as [new_terms new_cst] eqn : Hnew. 
  - rewrite H. rewrite /rhs_value1 H; simpl. rewrite Z.add_0_r Z.add_0_r. move : Hnew H0 H1 H2; apply remove_solved_correctness. 
Qed.

Lemma remove_solved_c_sat nv initial new_values : forall x, rhs_power x = nil ->
  (forall (var : ProdVar.t) (value0 : nat), PVM.find var initial = Some value0 -> PVM.find var new_values = Some value0) ->
  (forall (var : ProdVar.t) (value0 : nat), PVM.find var nv = Some value0 -> PVM.find var new_values = Some value0) ->
  (forall (var : ProdVar.t), PVM.find var initial = None -> PVM.find var nv = None -> PVM.find var new_values = None) ->
  satisfies_constraint1 nv (remove_solved_c initial x) = true -> satisfies_constraint1 new_values x = true.
Proof.
  rewrite /satisfies_constraint1; intros x Hgood_power Hfind_initial Hfind_nv; intros.
  assert (lhs_var1 (remove_solved_c initial x) = lhs_var1 x). 
  { rewrite /remove_solved_c. destruct (remove_solved initial (rhs_terms1 x)) as [new_terms new_cst]. case : (rhs_power x); simpl; try done.
    intros [coe var] l. case : (PVM.find (elt:=nat) var initial); simpl; try done. }
  rewrite H1 in H0. clear H1. 
  case Hfind1 : (PVM.find (elt:=nat) (lhs_var1 x) nv) => [val|]; rewrite Hfind1 in H0; try discriminate.
  apply Hfind_nv in Hfind1. rewrite Hfind1.
  apply Zle_imp_le_bool. apply Zle_bool_imp_le in H0.
  rewrite -(remove_solved_c_correctness _ _ new_values) in H0; try done.
Qed.

Lemma remove_solved_smallest initial nv : forall terms cst new_terms new_cst, le initial nv ->
  remove_solved initial terms = (new_terms, new_cst) -> (terms_value nv new_terms (cst + new_cst) <= terms_value nv terms cst)%Z.
Proof.
  elim. simpl; intros. inversion H0; simpl. lia. 
  simpl; intros [coe var]; intros; simpl. destruct (remove_solved initial l) as [terms' cst'] eqn : Htl.
  case Hinit : (PVM.find (elt:=nat) var initial) => [val|]; rewrite Hinit in H1.
  - inversion H1; clear H1 H4 new_cst. rewrite -H3; clear H3 new_terms. rewrite /smaller_valuation in H0. 
    rewrite /le in H0. destruct (H0 _ _ Hinit) as [value1 [Hfind1 Hle]].
    rewrite Hfind1. rewrite Z.add_assoc.
    rewrite terms_value_cst_add. rewrite (terms_value_cst_add _ _ cst (Z.of_nat (coe * value1))). apply Z.add_le_mono.
    apply H; try done. apply inj_le. apply (elimT leP). apply leq_mul; try done.
  - inversion H1. clear H1 H3 new_terms. rewrite -H4; clear H4 new_cst. simpl. rewrite terms_value_cst_add. 
    rewrite (terms_value_cst_add _ _ cst (Z.of_nat (coe * match PVM.find (elt:=nat) var nv with
      | Some val => val
      | None => 0
      end))). apply Zplus_le_compat_r. apply H; try done.
Qed.

Lemma remove_solved_c_sat' nv initial : forall x, le initial nv -> rhs_power x = nil ->
  satisfies_constraint1 nv x = true -> satisfies_constraint1 nv (remove_solved_c initial x) = true.
Proof.
  rewrite /satisfies_constraint1; intros x H Hgood_power; intros.
  assert (lhs_var1 (remove_solved_c initial x) = lhs_var1 x). 
  { rewrite /remove_solved_c. destruct (remove_solved initial (rhs_terms1 x)) as [new_terms new_cst]. case : (rhs_power x); simpl; try done.
    intros [coe var] l. case : (PVM.find (elt:=nat) var initial); simpl; try done. }
  rewrite H1; clear H1. 
  case Hfind1 : (PVM.find (elt:=nat) (lhs_var1 x) nv) => [val|]; rewrite Hfind1 in H0; try discriminate.
  apply Zle_imp_le_bool. apply Zle_bool_imp_le in H0.
  assert (rhs_value1 nv (remove_solved_c initial x) <= rhs_value1 nv x)%Z.
  { rewrite /rhs_value1. rewrite /remove_solved_c. destruct (remove_solved initial (rhs_terms1 x)) as [new_terms new_cst] eqn: Hnew. simpl.
    rewrite Hgood_power; simpl. rewrite Z.add_0_r. rewrite Z.add_0_r. move : Hnew; apply remove_solved_smallest; try done.
  }
  move : H1 H0; apply Z.le_trans.
Qed.

Definition le_bool (v0 v1 : Valuation) : bool :=
  let eles := PVM.elements v0 in
  forallb (fun '(var, val) => match PVM.find var v1 with
          | Some value1 => val <= value1
          | _ => false
          end) eles.

Lemma le_le_bool v0 v1 : le v0 v1 <-> le_bool v0 v1.
Proof.
  split.
  - unfold le; unfold le_bool.
    intros. apply forallb_forall. intros [var val] Hin. apply find_in_elements in Hin. apply H in Hin.
    clear H; destruct Hin as [value1 [Hfind1 Hle]]. rewrite Hfind1 //.
  - unfold le; unfold le_bool.
    intros. assert (forall x, List.In x (PVM.elements v0) -> (fun '(var, val) =>
      match PVM.find (elt:=nat) var v1 with
      | Some value1 => val <= value1
      | None => false
      end) x). apply forallb_forall; done. clear H. 
    apply find_in_elements in H0. apply H1 in H0; clear H1. 
    case Hfind : (PVM.find var v1) => [value1|]; rewrite Hfind in H0; try discriminate.
    exists value1; split; try done.
Qed.

Lemma remove_solved_unsat nv initial : le_bool initial nv -> forall x, rhs_power x = nil ->
  satisfies_constraint1 nv (remove_solved_c initial x) = false -> satisfies_constraint1 nv x = false.
Proof.
  rewrite /satisfies_constraint1; intros Hle x Hgood_power; intros.
  assert (lhs_var1 (remove_solved_c initial x) = lhs_var1 x). 
  { rewrite /remove_solved_c. destruct (remove_solved initial (rhs_terms1 x)) as [new_terms new_cst]. case : (rhs_power x); simpl; try done.
    intros [coe var] l. case : (PVM.find (elt:=nat) var initial); simpl; try done. }
  rewrite H0 in H; clear H0. 
  case Hfind1 : (PVM.find (elt:=nat) (lhs_var1 x) nv) => [val|]; rewrite Hfind1 in H; try done.
  apply Z.leb_gt. apply Z.leb_gt in H. 
  assert (rhs_value1 nv (remove_solved_c initial x) <= rhs_value1 nv x)%Z. apply le_le_bool in Hle.
  { rewrite /rhs_value1. rewrite /remove_solved_c. destruct (remove_solved initial (rhs_terms1 x)) as [new_terms new_cst] eqn: Hnew. simpl.
    rewrite Hgood_power; simpl. rewrite Z.add_0_r. rewrite Z.add_0_r. move : Hnew; apply remove_solved_smallest; try done.
  }
  move : H H0; apply Z.lt_le_trans.
Qed.

Lemma merge_solution_find_notin nv : forall tbsolved v initial new_values, ~List.In v tbsolved -> 
  merge_solution tbsolved initial nv = Some new_values -> PVM.find v initial = PVM.find v new_values.
Proof.
  elim. simpl; intros. inversion H0; done.
  simpl; intros. case Hfind : (PVM.find a nv) => [val|]; rewrite Hfind in H1; try discriminate. apply (H v) in H1. rewrite -H1 find_add_neq //.
    intro Heq; subst. intuition. intro Hin. intuition.
Qed.

Lemma solve_alg_nodup_solved_eq c1map : forall l var v0 v value, solve_alg l v0 c1map = Some v -> ~List.In var (List.concat l) -> PVM.find var v0 = Some value -> PVM.find var v = Some value.
Proof.
  elim. simpl; intros. inversion H. subst v; done.
  simpl; intros. destruct (solve_scc a (List.map (remove_solved_c v0) (extract_cs a c1map))) as [nv|]; try discriminate.
  destruct (merge_solution a v0 nv) as [v0'|] eqn : Hmerge; try discriminate.
  apply merge_solution_find_notin with (v := var) in Hmerge; try done. rewrite Hmerge in H2.
  move : H2; apply H; try done. 
  move : H1; apply contra_not. intro; apply in_or_app; right; done.
  move : H1; apply contra_not. intro; apply in_or_app; left; done.
Qed.

Lemma merge_solution_mem_or nv : forall a initial new_values, merge_solution a initial nv = Some new_values -> forall v, (PVM.mem v new_values <-> List.In v a \/ PVM.mem v initial).
Proof.
  elim. simpl; intros. split; intros. inversion H; right; done. destruct H0; try done. inversion H;rewrite -H2; done.
  simpl; intros. case Hfind : (PVM.find (elt:=nat) a nv) => [val|]; rewrite Hfind in H0; try discriminate. split.
  * intros. apply (H _ _ H0) in H1. destruct H1. left; right; done. apply mem_add_or in H1. destruct H1. right; done. left; left. move /eqP : H1 => H1. rewrite H1 //.
  * intros. apply (H _ _ H0). destruct H1. destruct H1. right. apply mem_add_or; right; rewrite H1 //.
    left; done. right. apply mem_add_or; left; done.
Qed.

Lemma extract_cs_exist_c x c1map : forall vl, List.In x (extract_cs vl c1map) -> exists v, List.In v vl /\ exists cs, PVM.find v c1map = Some cs /\ List.In x cs.
Proof.
  elim. simpl; done.
  simpl; intros. destruct (PVM.find a c1map) as [cs|] eqn : Hfind.
  - apply in_app_or in H0. destruct H0. clear H. exists a; split. left; done. exists cs; split; done.
  1,2 : apply H in H0; clear H; destruct H0 as [v [Hin Hexists]]; exists v; split; try done; right; done.
Qed.

Lemma merge_solution_find_in nv : forall a new_values initial, NoDup a -> merge_solution a initial nv = Some new_values ->
  forall var, List.In var a ->
  exists val : nat, PVM.find (elt:=nat) var nv = Some val /\ PVM.find (elt:=nat) var new_values = Some val.
Proof.
  elim. simpl; intros; done.
  simpl; intros. case Hfind : (PVM.find a nv) => [val|]; rewrite Hfind in H1; try discriminate.
  apply NoDup_cons_iff in H0. move : H0 => [Hnotin Hnodup]. destruct H2.
  - subst; exists val; split; try done. apply (merge_solution_find_notin _ _ _ _ _ Hnotin) in H1. 
    rewrite -H1 find_add_eq //.
  - move : H0. apply (H _ _ Hnodup H1).
Qed.

Lemma solve_simple_cycle_mem_in cs : forall ls nv, solve_simple_cycle ls cs = Some nv -> forall var, PVM.mem var nv -> List.In var ls.
Proof.
  intros. unfold solve_simple_cycle in H. destruct (forallb
    (fun c : ProdVar.t =>
    match get_weight c (Node c) (floyd_loop_map ls cs) with
    | Some w => (w =? 0)%Z
    | None => false
    end) ls); try discriminate. assert (forall (ls : seq ProdVar.t) (nv v : Valuation) m,
    save_longest_dist ls m v = Some nv ->
    forall var : PVM.key, PVM.mem (elt:=nat) var nv -> List.In var ls \/ PVM.mem var v). clear. elim. 
  - simpl; intros. inversion H. right; done.
  - simpl; intros. destruct (PVM.find a m) as [dst_map|] eqn : Hfind; try discriminate. destruct (List.split (NVM.elements dst_map)) as [_ dists].
    apply H with (var := var) in H0; try done. destruct H0. left; right; done. apply mem_add_or in H0. destruct H0. right; done. left; left. move /eqP : H0 => H0. rewrite H0 //.
  apply H1 with (var := var) in H; try done. destruct H; try done.
Qed.

Lemma solve_ubs_case1_ls_mem_in a b c d e : forall ls f g, solve_ubs_case1 ls a b c d e f = Some g -> forall var, PVM.mem var g -> List.In var ls \/ PVM.mem var f.
Proof.
  elim. simpl; intros. inversion H; subst g. right; done.
  simpl; intros hd tl IH; intros. destruct (solve_ub_case1 hd a b c d e) as [ub|] eqn : Hub; try discriminate.
  apply (IH _ _ H) in H0. destruct H0. 
  left; right; done.
  apply mem_add_or in H0. destruct H0. right; done.
  left; left. move /eqP : H0 => H0. rewrite H0 //.
Qed.

Lemma solve_ubs_case2_ls_mem_in a b c0 c1 d e : forall ls f g, solve_ubs_case2 ls a b c0 c1 d e f = Some g -> forall var, PVM.mem var g -> List.In var ls \/ PVM.mem var f.
Proof.
  elim. simpl; intros. inversion H; subst g. right; done.
  simpl; intros hd tl IH; intros. destruct (solve_ub_case2 hd a b c0 c1 d e) as [ub|]; try discriminate.
  apply (IH _ _ H) in H0. destruct H0. 
  left; right; done.
  apply mem_add_or in H0. destruct H0. right; done.
  left; left. move /eqP : H0 => H0. rewrite H0 //.
Qed.

Lemma solve_ubs_aux_mem_in cs : forall ls ubs, solve_ubs_aux ls cs = Some ubs -> forall var, PVM.mem var ubs -> List.In var ls.
Proof. 
  intros ls ubs H. unfold solve_ubs_aux in H. destruct (scc.build_graph cs) as [g adj] eqn : Hbuild.
  case Hfind0 : (List.find (fun c : Constraint1 =>
    List.existsb (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) cs) => [c|]; rewrite Hfind0 in H.
  case Hfind1 : (List.find (fun t : nat * ProdVar.t => 1 < t.1) (rhs_terms1 c)) => [[coe var]|]; rewrite Hfind1 in H; try discriminate.
  - intros. apply (solve_ubs_case1_ls_mem_in _ _ _ _ _ _ _ _ H) in H0. unfold initial_valuation in H0. destruct H0; done.
  case Hfind1 : (List.find (fun c : Constraint1 =>
    1 < Datatypes.length (rhs_terms1 c)) cs) => [c|]; rewrite Hfind1 in H; try discriminate. destruct (rhs_terms1 c) as [|[coe0 var0] l]; try discriminate.
  destruct l as [|[coe1 var1] tl]; try discriminate.
  - intros. apply (solve_ubs_case2_ls_mem_in _ _ _ _ _ _ _ _ _ H) in H0. unfold initial_valuation in H0. destruct H0; done.
Qed.

(*Lemma add_bs_mem var : forall ls v, PVM.mem var v -> PVM.mem var (add_bs ls v).
Proof.
  elim. simpl; intros; done.
  simpl; intros [var_hd ub_hd] tl; intros. apply H. apply mem_add; done.
Qed.
*)

Lemma mergeBounds_key_eq' ubs var : PVM.mem (elt:=nat * nat) var (mergeBounds ubs) -> PVM.mem (elt:=nat) var ubs.
Proof.
  rewrite /mergeBounds /initial_bounds; intros. 
  apply mem_in_elements. remember (PVM.elements ubs) as l.
  assert (forall l v var, PVM.mem var (add_bs l v) -> PVM.mem var v \/ exists ub, List.In (var, ub) l). clear. elim.
  - simpl; intros. left; done.
  - simpl; intros [var_hd ub_hd] tl; intros. apply H in H0. clear H. destruct H0.
    apply mem_add_or in H. destruct H. left; done. right. exists ub_hd. left. move /eqP : H => H; subst var. done.
    right. destruct H as [ub H]. exists ub; right; done.
  apply H0 in H. destruct H; try done.
Qed.

Lemma solve_scc_mem_in a cs nv : solve_scc a cs = Some nv -> forall var, PVM.mem var nv -> List.In var a.
Proof.
  unfold solve_scc. destruct a. 2 : destruct a. 
  2 : destruct (List.partition (fun c : Constraint1 => (rhs_terms1 c == []) && (rhs_power c == [])) cs) as [cs0 cs_have_v].
  2 : destruct (forallb [eta satisfies_constraint1 (PVM.add t (max_nl (List.map [eta rhs_const1] cs0) 0) initial_valuation)]
    cs_have_v); intros; try discriminate. 2:inversion H; remember (max_nl (List.map [eta rhs_const1] cs0) 0) as n; rewrite -H2 in H0; apply mem_add_or in H0; destruct H0.
  2 : rewrite /initial_valuation in H0; apply find_mem in H0; destruct H0 as [val H0]; rewrite find_empty_None in H0; discriminate. 2: move /eqP : H0 => H0; subst t; simpl; left; done.
  1,2 : intros; destruct (is_simple_cycle cs). 1,3 : apply (solve_simple_cycle_mem_in _ _ _ H) in H0; done.
  destruct (solve_ubs_aux [] (List.filter (fun c : Constraint1 => Datatypes.length (rhs_terms1 c) != 0) cs)) eqn : Hbs; try discriminate. 
  2 : destruct (solve_ubs_aux [:: t, t0 & a] (List.filter (fun c : Constraint1 => Datatypes.length (rhs_terms1 c) != 0) cs)) eqn : Hbs; try discriminate. 
  1,2 : apply (bab_bin_mem_in _ _ _ _ H) in H0. 1,2 : apply mergeBounds_key_eq' in H0. 1,2 : apply (solve_ubs_aux_mem_in _ _ _ Hbs _ H0).
Qed.

Lemma merge_solution_find_none nv: forall tbsolved new_values initial, merge_solution tbsolved initial nv = Some new_values -> 
  forall v, PVM.find v initial = None -> PVM.find v nv = None -> PVM.find v new_values = None.
Proof.
  elim. simpl; intros. inversion H. rewrite -H3 //.
  simpl; intros. case Hfind : (PVM.find a nv) => [val|]; rewrite Hfind in H0; try discriminate.
    apply H with (v := v) in H0; try done. destruct (a == v) eqn : Heq; move /eqP : Heq => Heq. rewrite Heq H2 in Hfind; discriminate.
    rewrite find_add_neq //. intuition.
Qed.

Definition tarjan_correctness (initial : Valuation) (scc_list : list (list ProdVar.t)) (c1map : PVM.t (list Constraint1)) : Prop :=
  (forall (scc : list ProdVar.t), List.In scc scc_list -> scc <> []) /\
  (NoDup (concat scc_list)) /\ (forall (var : ProdVar.t), PVM.mem var initial -> ~List.In var (concat scc_list)) /\
  (forall (l1 l2 : list (list ProdVar.t)) (scc : list ProdVar.t), l1 ++ scc :: l2 = scc_list ->
    (forall (var : ProdVar.t), List.In var (constraints1_vars (extract_cs scc c1map)) -> List.In var ((concat l1) ++ scc) \/ PVM.mem var initial)).

Definition extract_correctness (c1map : PVM.t (list Constraint1)) (scc_list : list (list ProdVar.t)) : Prop :=
  (forall (var : ProdVar.t), List.In var (concat scc_list) -> exists (cs : list Constraint1), PVM.find var c1map = Some cs /\ forallb (fun c => lhs_var1 c == var) cs /\ cs <> []
    /\ (forall c, List.In c cs -> good_terms (rhs_terms1 c) /\ (rhs_power c) = nil)).

Lemma remove_solved_vars initial : forall t new_terms new_cst, remove_solved initial t = (new_terms, new_cst) -> forall var, List.In var (List.map snd new_terms) ->
  List.In var (List.map snd t) /\ ~ PVM.mem var initial.
Proof.
  elim. simpl; intros. inversion H; subst new_terms new_cst. simpl in H0; done.
  simpl; intros [coe_hd var_hd] tl; intros. destruct (remove_solved initial tl) as [t' c']. destruct (PVM.find (elt:=nat) var_hd initial) as [val|] eqn : Hfind.
  - inversion H0; subst new_terms new_cst; clear H0. apply H with (new_cst := c') in H1; try done. move : H1 => [H1 H0]. split; try right; try done.
  - inversion H0; subst new_terms new_cst; clear H0. simpl in H1. destruct H1. subst var. split. left; simpl; done. intro. apply find_mem in H0. destruct H0 as [val H0]. rewrite H0 in Hfind; discriminate.
    apply H with (new_cst := c') in H0; try done. move : H0 => [H1 H0]. split; try right; try done.
Qed.

Lemma remove_solved_c_vars c v initial : ~ PVM.mem (lhs_var1 c) initial -> rhs_power c = nil -> List.In v (constraint1_vars (remove_solved_c initial c)) -> List.In v (constraint1_vars c) /\ ~PVM.mem v initial.
Proof.
  unfold remove_solved_c. destruct (remove_solved initial (rhs_terms1 c)) as [new_terms new_cst] eqn : Hremove. intros H Hp H0.
  simpl. rewrite Hp; simpl. rewrite cats0. rewrite Hp in H0; simpl in H0; rewrite cats0 in H0. destruct H0. subst v; split; try left; try done.
    apply (remove_solved_vars _ _ _ _ Hremove) in H0. move : H0 => [H0 H2]. split; try right; try done.
Qed.

Lemma solve_alg_correctness : forall scclist c1map cs2, 
    tarjan_correctness initial_valuation scclist c1map 
  -> extract_correctness c1map scclist 
  -> match solve_alg_check scclist c1map cs2 with
    | Some solution => forallb (satisfies_constraint1 solution) 
                                  (extract_cs (concat scclist) c1map) 
                    /\ forallb (fun c => Z.leb (min_rhs_value solution c) 1%Z) cs2
    | None => true
    end.
Proof.
  intros; rewrite /solve_alg_check.
  case Hsolve : (solve_alg scclist initial_valuation c1map) => [value|]; try done.
  destruct (forallb (fun c => Z.leb (min_rhs_value value c) 1%Z) cs2) eqn : Hcs2; try done.
  split; try done; clear Hcs2 cs2.
  move : scclist H H0 value Hsolve.
  assert (Hhelper : forall scclist initial,
    tarjan_correctness initial scclist c1map ->
    extract_correctness c1map scclist ->
    forall value : Valuation,
    solve_alg scclist initial c1map = Some value ->
    forallb (satisfies_constraint1 value) (extract_cs (concat scclist) c1map)).
  elim.
  - simpl; done.
  - intros a l IH initial Htarjan Hextract value Hsolve.
    simpl in Hsolve; simpl. rewrite -> extract_cs_app. 
    case Hscc : (solve_scc a (List.map (remove_solved_c initial) (extract_cs a c1map))) => [nv|]; rewrite Hscc in Hsolve; try discriminate.
    case Hmerge : (merge_solution a initial nv) => [new_values|]; rewrite Hmerge in Hsolve; try discriminate.
    apply forallb_forall. intros. apply in_app_or in H. destruct H.
    - (* in tbsolved*) 
    clear IH. generalize Hscc; intro Hnv. apply solve_scc_correctness in Hscc.
    assert (forall x, List.In x (List.map (remove_solved_c initial) (extract_cs a c1map)) -> satisfies_constraint1 nv x = true) by (apply forallb_forall; done). clear Hscc.
    generalize H; intro Hx. apply (in_map (remove_solved_c initial)) in H. apply H0 in H; clear H0.
    apply remove_solved_c_sat with (new_values := new_values) in H.
    assert (forall var value0, PVM.find var new_values = Some value0 -> PVM.find var value = Some value0). 
    { intros; generalize H0. apply (solve_alg_nodup_solved_eq _ _ _ _ _ _ Hsolve). 
      assert (exists val, PVM.find (elt:=nat) var new_values = Some val) by (exists value0; done). apply find_mem in H1.
      apply (merge_solution_mem_or _ _ _ _ Hmerge) in H1. move : Htarjan H1; clear; intros.
      unfold tarjan_correctness in Htarjan. move : Htarjan => [_ [H [H0 _]]]. destruct H1.
      - simpl in H. apply (NoDup_app_notin_r _ _ H) in H1. done.
      - apply H0 in H1. move : H1; apply contra_not. simpl; intro. apply in_or_app; right; done. }
    assert (forall var, List.In var (rhs_vars x) -> PVM.mem var new_values).
    { move : Hx Hmerge Htarjan; clear; intros. apply (merge_solution_mem_or _ _ _ _ Hmerge). unfold tarjan_correctness in Htarjan. move : Htarjan => [_ [_ [_ H0]]].
      specialize (H0 nil l a); simpl in H0. apply H0. done. apply (constraint1_vars2constraints1_vars _ Hx). unfold constraint1_vars. simpl; right. unfold rhs_vars in H; done. }
    move : H0 H H1; clear.
    { unfold satisfies_constraint1; intros.
      case Hfind0 : (PVM.find (lhs_var1 x) new_values) => [val|]; rewrite Hfind0 in H; try discriminate.
      apply H0 in Hfind0; rewrite Hfind0. apply Zle_bool_imp_le in H. apply Zle_imp_le_bool.
      rewrite -(rhs_value1_eq _ new_values value); try done.
      intros. apply H1 in H2; clear H1. apply find_mem in H2. destruct H2 as [val0 H2]. rewrite H2.
      apply H0 in H2. rewrite H2 //. }
    unfold extract_correctness in Hextract. apply extract_cs_exist_c in Hx. destruct Hx as [v [Hina [cs [Hfind Hincs]]]].
    destruct (Hextract v) as [cs' [Hfind' [_ [_ Hgood]]]]. simpl; apply in_or_app; left; done. rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
    apply Hgood in Hincs; exact Hincs.2.
    intros; apply (merge_solution_find_notin _ _ var) in Hmerge. rewrite -Hmerge //. assert (exists val, PVM.find (elt:=nat) var initial = Some val) by (exists value0; done). apply find_mem in H1.
      unfold tarjan_correctness in Htarjan. move : Htarjan => [_ [_ [Htarjan _]]]. apply Htarjan in H1. move: H1; apply contra_not. intros; apply in_or_app; left; done.
    intros; apply merge_solution_find_in with (var := var) in Hmerge. destruct Hmerge as [value0' [H1 H2]]. rewrite H1 in H0; rewrite H2 //.
    unfold tarjan_correctness in Htarjan. move : Htarjan => [_ [Hnodup _]]. simpl in Hnodup. apply NoDup_app_remove_r in Hnodup; done.
    apply (solve_scc_mem_in _ _ _ Hnv). apply find_mem. exists value0; done.
    intro; apply (merge_solution_find_none _ _ _ _ Hmerge).
    unfold tarjan_correctness in Htarjan; move : Htarjan => [Htarjan _]. apply Htarjan. simpl; left; done.
    unfold extract_correctness in Hextract. intros. apply in_map_iff in H0; destruct H0 as [c0 [Hremove Hin]]; subst c. 
      apply extract_cs_exist_c in Hin. destruct Hin as [v [Hina [cs [Hfind Hincs]]]]. destruct (Hextract v) as [cs' [Hfind' [_ [_ Hgood]]]]. simpl; apply in_or_app; left; done. rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
      apply Hgood in Hincs; move : Hincs => [_ Hincs]. move : Hincs; clear; unfold remove_solved_c. intro; rewrite Hincs. destruct (remove_solved initial (rhs_terms1 c0)); simpl; done.
    move : Htarjan Hextract; clear; intros. apply in_map_iff in H. destruct H as [c' [Hremove Hin]]. 
      unfold tarjan_correctness in Htarjan. move : Htarjan => [_ [_ [Hinit Htarjan]]]. assert ([] ++ a :: l = a :: l) by (simpl; done).
      specialize (Htarjan _ _ _ H); clear H. subst c. apply remove_solved_c_vars in H0. move : H0 => [H0 H]. apply (constraint1_vars2constraints1_vars _ Hin) in H0.
      apply Htarjan in H0; clear Htarjan. destruct H0; try done.
    1,2 : unfold extract_correctness in Hextract; apply extract_cs_exist_c in Hin; destruct Hin as [var [Hina [cs [Hfind Hincs]]]];
    destruct (Hextract var) as [cs' [Hfind' [Hlhs [_ Hgood]]]]. 1,3: simpl; apply in_or_app; left; done. 1,2: rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
    * assert (forall c, List.In c cs -> lhs_var1 c == var) by (apply forallb_forall; done). apply H in Hincs. clear H Hlhs. move /eqP : Hincs => Hincs; subst var.
      intro. apply Hinit in H; clear Hinit. simpl in H. apply H. apply in_or_app; left; done. 
    * apply Hgood in Hincs; exact Hincs.2.
    - (* induction *)
    move : x H. apply forallb_forall. move : Hsolve; apply IH.
    (* tarjan start *) move : Hmerge Htarjan; clear; intros.
    unfold tarjan_correctness in *.
    move : Htarjan => [Hnotempty [Hnodup [Hinitial Hsolved]]]. split. intros; apply Hnotempty; intuition.
    split. simpl in Hnodup. apply NoDup_app_remove_l in Hnodup; done.
    split. intros. apply (merge_solution_mem_or _ _ _ _ Hmerge) in H. destruct H. simpl in Hnodup; apply NoDup_app_notin_r with (var := var) in Hnodup; try done.
      apply Hinitial in H. move : H; apply contra_not. intros; simpl; apply in_or_app; right; done.
    intros. assert ((a :: l1) ++ scc :: l2 = a :: l) by (rewrite -H; simpl; done). specialize (Hsolved _ _ _ H1); clear H1. apply Hsolved in H0. destruct H0.
    + simpl in H0. apply in_app_or in H0. destruct H0. apply in_app_or in H0. destruct H0. right; apply (merge_solution_mem_or _ _ _ _ Hmerge). left; done.
      left; apply in_or_app; left; done. left; apply in_or_app; right; done.
    + right. apply (merge_solution_mem_or _ _ _ _ Hmerge). right; done.
    (* tarjan end *)
    (* extract start *)
    move : Hextract; unfold extract_correctness; clear; intros. apply Hextract. simpl; apply in_or_app; right ;done.
    (* extract end *)
  intro scclist; apply Hhelper.
Qed.

Lemma extract_cs_not_nil c1map : forall vl, vl <> nil -> (forall var : ProdVar.t, List.In var vl ->
  exists cs : seq Constraint1, PVM.find (elt:=seq Constraint1) var c1map = Some cs /\ cs <> nil) -> extract_cs vl c1map <> nil.
Proof.
  elim. simpl; done.
  simpl; intros. clear H0. destruct (H1 a) as [cs [Hfind Hnotnil]]. left; done. rewrite Hfind. destruct cs; done.
Qed.

Lemma remove_solved_good_terms initial : forall t nt nc, good_terms t -> remove_solved initial t = (nt, nc) -> good_terms nt.
Proof.
  elim; simpl. intros. inversion H0; done.
  simpl; intros [coe var] tl; intros. destruct (remove_solved initial tl) as [nt' nc'] eqn : Hremove. destruct (PVM.find (elt:=nat) var initial) eqn : Hfind; inversion H1; subst nt nc.
  - apply H with (nc := nc'); try done. apply good_terms_tl in H0; done.
  - clear H1. specialize (good_terms_tl H0) as H1. assert ((nt',nc') = (nt',nc')) by (done). apply (H _ _ H1) in H2; clear H.
    unfold good_terms. unfold good_terms in H0; move : H0 => [H0 H3]. split. intros. simpl in H. destruct H. 
    + inversion H; subst coe0 var0. apply H0 with (var := var); simpl; left; done.
    + unfold good_terms in H2. apply H2.1 in H; done.
    simpl. destruct (List.split nt') eqn : Hsplit'. simpl. apply NoDup_cons.
    specialize (remove_solved_vars _ _ _ _ Hremove var) as Hvars. assert (List.In var (List.map snd nt') -> List.In var (List.map snd tl)) by (intros; apply Hvars in H; exact H.1).
    clear Hvars. specialize (contra_not H) as H'; clear H. rewrite -split2_eq_mapsnd -split2_eq_mapsnd Hsplit' in H'. apply H'.
    simpl in H3. destruct (List.split tl) as [left right] eqn : Hsplit. simpl in H3. apply NoDup_cons_iff in H3. exact H3.1.
    unfold good_terms in H2. rewrite Hsplit' in H2. exact H2.2.
Qed.

Lemma remove_solved_c_good_terms c initial : good_terms (rhs_terms1 c) -> good_terms (rhs_terms1 (remove_solved_c initial c)).
Proof.
  intro Hgood. unfold remove_solved_c. destruct (remove_solved initial (rhs_terms1 c)) as [new_terms new_cst] eqn : Hremove.
  destruct (rhs_power c) as [|[coe var] p_tl]; simpl. 2 : destruct (PVM.find (elt:=nat) var initial); simpl.
  1,2,3 : move : Hremove; apply remove_solved_good_terms; done.
Qed.

Lemma solve_alg_smallest : forall scclist c1map cs2, 
    tarjan_correctness initial_valuation scclist c1map 
  -> extract_correctness c1map scclist
  -> match solve_alg_check scclist c1map cs2 with
    | Some solution => forall temp_s, 
        forallb (satisfies_constraint1 temp_s) (extract_cs (concat scclist) c1map) /\
        forallb (fun c => Z.leb (min_rhs_value temp_s c) 1%Z) cs2 -> le solution temp_s
    | None => true
    end.
Proof.
  intros; rewrite /solve_alg_check.
  case Hsolve : (solve_alg scclist initial_valuation c1map) => [value|]; try done.
  destruct (forallb (fun c => Z.leb (min_rhs_value value c) 1%Z) cs2) eqn : Hcs2; try done.
  move : scclist H H0 value Hsolve Hcs2.
  assert (Hhelper : forall (scclist : list (list ProdVar.t)) initial,
    tarjan_correctness initial scclist c1map ->
    extract_correctness c1map scclist ->
    forall value : Valuation,
    solve_alg scclist initial c1map = Some value ->
    forallb (fun c => Z.leb (min_rhs_value value c) 1%Z) cs2 = true ->
    forall temp_s : Valuation,
    forallb (satisfies_constraint1 temp_s)
      (extract_cs (concat scclist) c1map) /\
    forallb (fun c => Z.leb (min_rhs_value temp_s c) 1%Z) cs2 -> le initial temp_s ->
    le value temp_s).
  elim.
  - simpl; intros.
    inversion H1.
    rewrite -H6 //.
  - intros a l IH initial Htarjan Hextract value Hsolve Hcs2 temp_s Htemp Hsmaller.
    simpl in Hsolve.
    case Hscc : (solve_scc a (List.map (remove_solved_c initial) (extract_cs a c1map))) => [nv|]; rewrite Hscc in Hsolve; try discriminate.
    case Hmerge : (merge_solution a initial nv) => [new_values|]; rewrite Hmerge in Hsolve; try discriminate.
    apply IH with (initial := new_values); try done. 
    (* tarjan start *) move : Hmerge Htarjan; clear; intros.
    unfold tarjan_correctness in *.
    move : Htarjan => [Hnotempty [Hnodup [Hinitial Hsolved]]]. split. intros; apply Hnotempty; intuition.
    split. simpl in Hnodup. apply NoDup_app_remove_l in Hnodup; done.
    split. intros. apply (merge_solution_mem_or _ _ _ _ Hmerge) in H. destruct H. simpl in Hnodup; apply NoDup_app_notin_r with (var := var) in Hnodup; try done.
      apply Hinitial in H. move : H; apply contra_not. intros; simpl; apply in_or_app; right; done.
    intros. assert ((a :: l1) ++ scc :: l2 = a :: l) by (rewrite -H; simpl; done). specialize (Hsolved _ _ _ H1); clear H1. apply Hsolved in H0. destruct H0.
    + simpl in H0. apply in_app_or in H0. destruct H0. apply in_app_or in H0. destruct H0. right; apply (merge_solution_mem_or _ _ _ _ Hmerge). left; done.
      left; apply in_or_app; left; done. left; apply in_or_app; right; done.
    + right. apply (merge_solution_mem_or _ _ _ _ Hmerge). right; done.
    (* tarjan end *)
    (* extract start *)
    move : Hextract; unfold extract_correctness; clear; intros. apply Hextract. simpl; apply in_or_app; right ;done.
    (* extract end *)
    { move : Htemp => [Htemp1 Htemp2]. split; try done. move : Htemp1; clear; intros. simpl in Htemp1. apply forallb_forall.
      assert (forall x, List.In x (extract_cs (a ++ concat l)%list c1map) -> satisfies_constraint1 temp_s x) by (apply forallb_forall; done). clear Htemp1.
      intros; apply H. rewrite extract_cs_app. apply in_or_app; right; done. }
    clear IH Hsolve Hcs2 value. apply solve_scc_smallest with (temp_s := temp_s) in Hscc.
    move : Hsmaller Hscc Hmerge; apply merge_smaller. 
    unfold tarjan_correctness in Htarjan; move : Htarjan => [Htarjan _]. apply Htarjan. simpl; left; done.
    unfold tarjan_correctness in Htarjan; move : Htarjan => [_ [Hnodup _]]; simpl in Hnodup; apply NoDup_app_remove_r in Hnodup; done.
    { assert (a <> []) by (unfold tarjan_correctness in Htarjan; move : Htarjan => [Htarjan _]; apply Htarjan; simpl; left; done).
      apply (extract_cs_not_nil c1map) in H.
      remember (extract_cs a c1map) as cs. move : H; clear. destruct cs; try done.
      intros. unfold extract_correctness in Hextract. destruct (Hextract var) as [cs [Hfind [_ [Hnotnil _]]]]. simpl; apply in_or_app; left; done. exists cs; split; done. }
    move : Htarjan Hextract; clear; intros. apply in_map_iff in H. destruct H as [c' [Hremove Hin]]. 
      unfold tarjan_correctness in Htarjan. move : Htarjan => [_ [_ [Hinit Htarjan]]]. assert ([] ++ a :: l = a :: l) by (simpl; done).
      specialize (Htarjan _ _ _ H); clear H. subst c. apply remove_solved_c_vars in H0. move : H0 => [H0 H]. apply (constraint1_vars2constraints1_vars _ Hin) in H0.
      apply Htarjan in H0; clear Htarjan. destruct H0; try done.
    1,2 : unfold extract_correctness in Hextract; apply extract_cs_exist_c in Hin; destruct Hin as [var [Hina [cs [Hfind Hincs]]]];
    destruct (Hextract var) as [cs' [Hfind' [Hlhs [_ Hgood]]]]. 1,3: simpl; apply in_or_app; left; done. 1,2: rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
    * assert (forall c, List.In c cs -> lhs_var1 c == var) by (apply forallb_forall; done). apply H in Hincs. clear H Hlhs. move /eqP : Hincs => Hincs; subst var.
      intro. apply Hinit in H; clear Hinit. simpl in H. apply H. apply in_or_app; left; done. 
    * apply Hgood in Hincs; exact Hincs.2.
    { intros. apply in_map_iff in H. destruct H as [x [Hremove Hin]]. subst c. apply remove_solved_c_good_terms. 
      move : Hextract Hin; clear; intros. unfold extract_correctness in Hextract. apply extract_cs_exist_c in Hin. destruct Hin as [var [Hina [cs [Hfind Hincs]]]].
      destruct (Hextract var) as [cs' [Hfind' [_ [_ Hgood]]]]. simpl; apply in_or_app; left; done. rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
      apply Hgood in Hincs. exact Hincs.1. }
    unfold extract_correctness in Hextract. intros. apply in_map_iff in H; destruct H as [c0 [Hremove Hin]]; subst c. 
      apply extract_cs_exist_c in Hin. destruct Hin as [v [Hina [cs [Hfind Hincs]]]]. destruct (Hextract v) as [cs' [Hfind' [_ [_ Hgood]]]]. simpl; apply in_or_app; left; done. rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
      apply Hgood in Hincs; move : Hincs => [_ Hincs]. move : Hincs; clear; unfold remove_solved_c. intro; rewrite Hincs. destruct (remove_solved initial (rhs_terms1 c0)); simpl; done.
    assert (forall x, List.In x (extract_cs a c1map) -> satisfies_constraint1 temp_s x = true).
    { intros. move : Htemp => [Htemp _]. assert (forall x, List.In x (extract_cs (concat (a :: l)) c1map) -> satisfies_constraint1 temp_s x = true) by (apply forallb_forall; done).
      apply H0. simpl. rewrite -> extract_cs_app. apply in_or_app; left; done. } clear Htemp.
    apply forallb_forall; intros. apply in_map_iff in H0. destruct H0 as [x' [Hx' Hin']].
    generalize Hin'; intro Hin. apply H in Hin'; clear H. subst x. assert (rhs_power x' = nil).
      move : Hextract Hin; clear; intros. unfold extract_correctness in Hextract. apply extract_cs_exist_c in Hin. destruct Hin as [var [Hina [cs [Hfind Hincs]]]].
      destruct (Hextract var) as [cs' [Hfind' [_ [_ Hgood]]]]. simpl; apply in_or_app; left; done. rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
      apply Hgood in Hincs. exact Hincs.2.
    move : Hsmaller H Hin'; apply remove_solved_c_sat'.

  intros. apply (Hhelper scclist initial_valuation); try done.
Qed.

Definition initial_smallest (initial : Valuation) (c1map : PVM.t (list Constraint1)) :=
  let eles := (List.split (PVM.elements initial)).1 in
  let cs := extract_cs eles c1map in
  forall v, ~(le initial v) -> forallb (satisfies_constraint1 v) cs = false.

Lemma mem_extract_cs c1map : forall a b, (forall v, List.In v a -> List.In v b) -> forall c, List.In c (extract_cs a c1map) -> List.In c (extract_cs b c1map).
Proof.
  intros a b Hsub c Hin.
  induction a as [|x xs IH].
  - (* Case a = nil *)
    simpl in Hin. contradiction. (* nil 列表不可能包含元素 *)
  - (* Case a = x :: xs *)
    simpl in Hin.
    destruct (PVM.find x c1map) eqn:Hfind.
    + (* Subcase: find returns Some l *)
      apply in_app_or in Hin.      (* 分解连接操作 *)
      destruct Hin as [Hin|Hin].
      * (* Subsubcase: c is in l (from x) *)
        assert (List.In x b) by (apply Hsub; simpl; left; done).
        move : H Hfind Hin; clear; move : b x c l.
        elim. intros; contradiction. (* 空列表不可能包含v *)
        simpl; intros. destruct H0 as [Heq|Hin'].
        * (* v 是当前元素 *)
          subst x. rewrite Hfind. apply in_or_app. left. assumption.
        * (* v 在尾部 *)
          specialize (H _ _ _ Hin' Hfind Hin).
          case Hfinda : (PVM.find a c1map) => [c0|]; try done.
          apply in_or_app. right. assumption. 
      * move : Hin; apply IH. intros; apply Hsub. simpl; right; done.
    + (* Subcase: find returns None *)
      apply IH; auto.                (* 直接递归 *)
      intros v Hv. apply Hsub. right. exact Hv.
Qed.

Lemma merge_solution_exists_some nv : forall a initial, (forall var, List.In var a -> exists val, PVM.find var nv = Some val) -> exists new_values, merge_solution a initial nv = Some new_values.
Proof.
  elim. simpl; intros. exists initial; done.
  simpl; intros. destruct (H0 a) as [val H1]. left;done. rewrite H1.
  apply H. intros; apply H0. right; done.
Qed.

Lemma solve_simple_cycle_in_find_some a cs nv : solve_simple_cycle a cs = Some nv -> forall var : ProdVar.t, List.In var a -> exists val : nat, PVM.find (elt:=nat) var nv = Some val.
Proof.
  intros. unfold solve_simple_cycle in H. destruct (forallb
    (fun c : ProdVar.t =>
    match get_weight c (Node c) (floyd_loop_map a cs) with
    | Some w => (w =? 0)%Z
    | None => false
    end) a); try discriminate. assert (forall (ls : seq ProdVar.t) (nv v : Valuation) m,
    save_longest_dist ls m v = Some nv ->
    forall var, List.In var ls \/ PVM.mem var v -> PVM.mem (elt:=nat) var nv). clear. elim. 
  - simpl; intros. inversion H. rewrite -H2. destruct H0; done.
  - simpl; intros. destruct (PVM.find a m) as [dst_map|] eqn : Hfind; try discriminate. destruct (List.split (NVM.elements dst_map)) as [_ dists].
    apply H with (var := var) in H0; try done. destruct H1. destruct H1. right; subst a. apply find_mem; exists (Z.to_nat (maxz_list dists)). apply find_add_eq. left; done. 
    right. apply mem_add_or; left; done.
  apply H1 with (var := var) in H; try done. apply find_mem; done. left;done.
Qed.

Lemma solve_scc_in_find_some a cs nv : solve_scc a cs = Some nv -> forall var, List.In var a -> exists val, PVM.find var nv = Some val.
Proof.
  unfold solve_scc. destruct a eqn : Ha. 2 : destruct l eqn : Hl. 
  2 : destruct (List.partition (fun c : Constraint1 => (rhs_terms1 c == []) && (rhs_power c == [])) cs) as [cs0 cs_have_v].
  2 : destruct (forallb [eta satisfies_constraint1 (PVM.add t (max_nl (List.map [eta rhs_const1] cs0) 0) initial_valuation)]
    cs_have_v); intros; try discriminate. 2: inversion H; remember (max_nl (List.map [eta rhs_const1] cs0) 0) as n; simpl in H0; destruct H0; try done; subst t; rewrite find_add_eq; exists n; done.
  1,2 : rewrite -Ha; destruct (is_simple_cycle cs). 1,3 : apply solve_simple_cycle_in_find_some.
  1,2 : destruct (solve_ubs_aux a (List.filter (fun c : Constraint1 => Datatypes.length (rhs_terms1 c) != 0) cs)) eqn : Hbs; try discriminate. 
  1,2 : intros; apply bab_bin_some_in_bounds in H; unfold In in H; apply solve_ubs_aux_in_mem with (var := var) in Hbs; try done; apply mergeBounds_key_eq in Hbs; apply find_mem in Hbs;
  destruct Hbs as [[lb ub] Hbs]. 1,3: apply H in Hbs; destruct Hbs as [n [Hbs _]]; exists n ;done. 
  1,2 : unfold well_defined; intros; apply mergeBounds_find_lb in H1; rewrite H1; done.
Qed.

Lemma remove_solved_c_lhs_eq c initial : lhs_var1 c = lhs_var1 (remove_solved_c initial c).
Proof.
  unfold remove_solved_c. destruct (remove_solved initial (rhs_terms1 c)) as [nt nc]. destruct (rhs_power c) as [|[coe var] tl]; simpl; try done.
  destruct (PVM.find (elt:=nat) var initial); simpl; try done.
Qed.

Lemma solve_alg_return_unsat c1map : forall scclist, 
    tarjan_correctness initial_valuation scclist c1map 
  -> extract_correctness c1map scclist 
  -> match solve_alg scclist initial_valuation c1map with
    | None => forall v, forallb (satisfies_constraint1 v) (extract_cs (concat scclist) c1map) = false 
    | _ => True
    end.
Proof.
  assert (Hhelper : forall (scclist : list (list ProdVar.t)) initial,
    tarjan_correctness initial scclist c1map ->
    extract_correctness c1map scclist ->
    solve_alg scclist initial c1map = None ->
    initial_smallest initial c1map ->
    forall v, forallb (satisfies_constraint1 v) (extract_cs ((List.split (PVM.elements initial)).1 ++ concat scclist) c1map) = false).
  elim.
  - simpl; intros. discriminate.
  - intros a l IH initial Htarjan Hextract Hsolve Hinitial v.
    simpl in Hsolve; simpl. rewrite -> extract_cs_app. 
    case Hscc : (solve_scc a (List.map (remove_solved_c initial) (extract_cs a c1map))) => [nv|]; rewrite Hscc in Hsolve; try discriminate.
    case Hmerge : (merge_solution a initial nv) => [new_values|]; rewrite Hmerge in Hsolve; try discriminate.
    - (* l unsat *)
      apply IH with (v := v) in Hsolve; try done.
      apply not_true_iff_false. apply forallb_neg_neg.
      apply not_true_iff_false in Hsolve. apply forallb_neg_neg in Hsolve. destruct Hsolve as [x [Hin Hunsat]].
      exists x; split; try done. 
      rewrite -extract_cs_app. move : Hin; apply mem_extract_cs. move : Hmerge; clear. intros. 
      { apply in_app_or in H. destruct H.
        - apply merge_solution_mem_or with (v := v) in Hmerge. apply key_in_elements in H. apply mem_in_elements in H.
          apply Hmerge in H. destruct H. apply in_or_app; right. apply in_or_app; left; done.
          apply mem_in_elements in H. apply in_or_app; left. apply key_in_elements; done.
        - apply in_or_app; right. apply in_or_app; right; done. }
      (* tarjan start *) move : Hmerge Htarjan; clear; intros.
      unfold tarjan_correctness in *.
      move : Htarjan => [Hnotempty [Hnodup [Hinitial Hsolved]]]. split. intros; apply Hnotempty; intuition.
      split. simpl in Hnodup. apply NoDup_app_remove_l in Hnodup; done.
      split. intros. apply (merge_solution_mem_or _ _ _ _ Hmerge) in H. destruct H. simpl in Hnodup; apply NoDup_app_notin_r with (var := var) in Hnodup; try done.
        apply Hinitial in H. move : H; apply contra_not. intros; simpl; apply in_or_app; right; done.
      intros. assert ((a :: l1) ++ scc :: l2 = a :: l) by (rewrite -H; simpl; done). specialize (Hsolved _ _ _ H1); clear H1. apply Hsolved in H0. destruct H0.
      + simpl in H0. apply in_app_or in H0. destruct H0. apply in_app_or in H0. destruct H0. right; apply (merge_solution_mem_or _ _ _ _ Hmerge). left; done.
        left; apply in_or_app; left; done. left; apply in_or_app; right; done.
      + right. apply (merge_solution_mem_or _ _ _ _ Hmerge). right; done.
      (* tarjan end *)
      (* extract start *)
      move : Hextract; unfold extract_correctness; clear; intros. apply Hextract. simpl; apply in_or_app; right ;done.
      (* extract end *)
      { move : Hinitial Hscc Hmerge Htarjan Hextract; clear.
        unfold initial_smallest; intros. assert (H0 : a <> []) by (unfold tarjan_correctness in Htarjan; move : Htarjan => [Htarjan _]; apply Htarjan; simpl; left; done).
        assert (H1 : List.map (remove_solved_c initial) (extract_cs a c1map) <> []).
        { apply (extract_cs_not_nil c1map) in H0.
          remember (extract_cs a c1map) as cs. move : H0; clear. destruct cs; try done.
          intros. unfold extract_correctness in Hextract. destruct (Hextract var) as [cs [Hfind [_ [Hnotnil _]]]]. simpl; apply in_or_app; left; done. exists cs; split; done. }
        assert (H2 : forall c, List.In c (List.map (remove_solved_c initial) (extract_cs a c1map)) -> (forall var, List.In var (constraint1_vars c) -> List.In var a)).
        { move : Htarjan Hextract; clear; intros. apply in_map_iff in H. destruct H as [c' [Hremove Hin]]. 
          unfold tarjan_correctness in Htarjan. move : Htarjan => [_ [_ [Hinit Htarjan]]]. assert ([] ++ a :: l = a :: l) by (simpl; done).
          specialize (Htarjan _ _ _ H); clear H. subst c. apply remove_solved_c_vars in H0. move : H0 => [H0 H]. apply (constraint1_vars2constraints1_vars _ Hin) in H0.
          apply Htarjan in H0; clear Htarjan. destruct H0; try done.
          1,2 : unfold extract_correctness in Hextract; apply extract_cs_exist_c in Hin; destruct Hin as [var' [Hina [cs [Hfind Hincs]]]];
          destruct (Hextract var') as [cs' [Hfind' [Hlhs [_ Hgood]]]]. 1,3: simpl; apply in_or_app; left; done. 1,2: rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
          * assert (forall c, List.In c cs -> lhs_var1 c == var') by (apply forallb_forall; done). apply H in Hincs. clear H Hlhs. move /eqP : Hincs => Hincs; subst var'.
            intro. apply Hinit in H; clear Hinit. simpl in H. apply H. apply in_or_app; left; done. 
          * apply Hgood in Hincs; exact Hincs.2. }
        assert (H3 : forall c, List.In c (List.map (remove_solved_c initial) (extract_cs a c1map)) -> good_terms (rhs_terms1 c)).
        { move : Htarjan Hextract;clear. intros. apply in_map_iff in H. destruct H as [x [Hremove Hin]]. subst c. apply remove_solved_c_good_terms. 
          move : Hextract Hin; clear; intros. unfold extract_correctness in Hextract. apply extract_cs_exist_c in Hin. destruct Hin as [var [Hina [cs [Hfind Hincs]]]].
          destruct (Hextract var) as [cs' [Hfind' [_ [_ Hgood]]]]. simpl; apply in_or_app; left; done. rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
          apply Hgood in Hincs. exact Hincs.1. }
        assert (H4 : forall c, List.In c (List.map (remove_solved_c initial) (extract_cs a c1map)) -> rhs_power c = []).
        { move : Hextract;clear. intros. apply in_map_iff in H. destruct H as [x [Hremove Hin]]. subst c. unfold extract_correctness in Hextract. apply extract_cs_exist_c in Hin. destruct Hin as [var [Hina [cs [Hfind Hincs]]]].
          destruct (Hextract var) as [cs' [Hfind' [_ [_ Hgood]]]]. simpl; apply in_or_app; left; done. rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
          apply Hgood in Hincs; move : Hincs => [_ H]. unfold remove_solved_c. rewrite H. destruct (remove_solved initial (rhs_terms1 x)); done. }
        assert (H5 : NoDup a) by (unfold tarjan_correctness in Htarjan; move : Htarjan => [_ [Hnodup _]]; simpl in Hnodup; apply NoDup_app_remove_r in Hnodup; done).
        specialize (solve_scc_smallest _ _ _ H0 H5 Hscc H1 H2 H3 H4 v); clear H1 H2 H3 H4 H5; intros H1. 
        specialize (contra_not H1); intros; clear H1.
        destruct (le_bool initial v) eqn : Hle_initial.
        * apply le_le_bool in Hle_initial; clear Hinitial.
          assert (~ le nv v). 
          { move : H Hle_initial Hmerge; clear; intros; move : H. apply contra_not. intros. move : Hle_initial H Hmerge; apply merge_smaller. }
          apply H2 in H1; clear H H2. apply not_true_iff_false in H1.
          apply not_true_iff_false. apply forallb_neg_neg.
          apply not_true_iff_false in H1. apply forallb_neg_neg in H1. destruct H1 as [x [Hin Hunsat]].
          apply in_map_iff in Hin. destruct Hin as [x' [Hx' Hin]]. exists x'; split.
          assert (forall v, List.In v a -> List.In v (List.split (PVM.elements (elt:=nat) new_values)).1).
          { move : Hmerge; clear. intros. apply merge_solution_mem_or with (v := v) in Hmerge. apply key_in_elements. apply mem_in_elements. apply Hmerge; left; done. }
          apply (mem_extract_cs _ _ _ H) in Hin; done.
          rewrite -Hx' in Hunsat; clear Hx' x. move : Hunsat; apply remove_solved_unsat.
          apply le_le_bool; done. 
          { move : Hin Hextract; clear; intros. unfold extract_correctness in Hextract; apply extract_cs_exist_c in Hin; destruct Hin as [var' [Hina [cs [Hfind Hincs]]]];
            destruct (Hextract var') as [cs' [Hfind' [Hlhs [_ Hgood]]]]. simpl; apply in_or_app; left; done. rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
            apply Hgood in Hincs; exact Hincs.2. }
        * assert (~ le initial v) by (apply not_true_iff_false in Hle_initial; move : Hle_initial; apply contra_not; apply le_le_bool; done). clear H2 H Hle_initial.
          apply Hinitial in H1; clear Hinitial.
          apply not_true_iff_false. apply forallb_neg_neg.
          apply not_true_iff_false in H1. apply forallb_neg_neg in H1. destruct H1 as [x [Hin Hunsat]].
          exists x; split; try done.
          assert (forall v, List.In v (List.split (PVM.elements initial)).1 -> List.In v (List.split (PVM.elements new_values)).1).
          { move : Hmerge; clear. intros. apply merge_solution_mem_or with (v := v) in Hmerge. apply key_in_elements. apply mem_in_elements. 
            apply key_in_elements in H. apply mem_in_elements in H. apply Hmerge; right; done. }
          apply (mem_extract_cs _ _ _ H) in Hin; done. }
    - (* merge error *)
      specialize (solve_scc_in_find_some _ _ _ Hscc); intro. apply (merge_solution_exists_some nv a initial) in H. destruct H as [x H]. rewrite H in Hmerge; discriminate.
    - (* a unsat *) clear IH Hsolve. 
      destruct (le_bool initial v) eqn : Hle.
      * apply solve_scc_unsat with (v := v) in Hscc.
        apply not_true_iff_false. apply forallb_neg_neg.
        apply not_true_iff_false in Hscc. apply forallb_neg_neg in Hscc. destruct Hscc as [x [Hin Hunsat]].
        apply in_map_iff in Hin. destruct Hin as [x' [Hx' Hin]]. exists x'; split.
        apply in_or_app; right. rewrite extract_cs_app. apply in_or_app; left; done. rewrite -Hx' in Hunsat; clear Hx' x.
        move : Hunsat; apply remove_solved_unsat; try done. 
        { move : Hin Hextract; clear; intros. unfold extract_correctness in Hextract; apply extract_cs_exist_c in Hin; destruct Hin as [var' [Hina [cs [Hfind Hincs]]]];
          destruct (Hextract var') as [cs' [Hfind' [Hlhs [_ Hgood]]]]. simpl; apply in_or_app; left; done. rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
          apply Hgood in Hincs; exact Hincs.2. }
        unfold tarjan_correctness in Htarjan; move : Htarjan => [Htarjan _]; apply Htarjan; simpl; left; done.
        unfold tarjan_correctness in Htarjan; move : Htarjan => [_ [Hnodup _]]. simpl in Hnodup. apply NoDup_app_remove_r in Hnodup; done.
        { assert (a <> []) by (unfold tarjan_correctness in Htarjan; move : Htarjan => [Htarjan _]; apply Htarjan; simpl; left; done).
          apply (extract_cs_not_nil c1map) in H.
          remember (extract_cs a c1map) as cs. move : H; clear. destruct cs; try done.
          intros. unfold extract_correctness in Hextract. destruct (Hextract var) as [cs [Hfind [_ [Hnotnil _]]]]. simpl; apply in_or_app; left; done. exists cs; split; done. }
        intros. apply in_map_iff in H. destruct H as [x [Hremove Hin]]. subst c. rewrite -remove_solved_c_lhs_eq. unfold extract_correctness in Hextract.
        apply extract_cs_exist_c in Hin; destruct Hin as [var' [Hina [cs [Hfind Hincs]]]]. destruct (Hextract var') as [cs' [Hfind' [Hlhs _]]]. simpl; apply in_or_app; left; done. rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
        assert (forall c, List.In c cs -> lhs_var1 c == var') by (apply forallb_forall; done). apply H in Hincs. move /eqP :Hincs => Hincs. rewrite Hincs //.
        { move : Htarjan Hextract;clear. intros. apply in_map_iff in H. destruct H as [x [Hremove Hin]]. subst c. apply remove_solved_c_good_terms. 
          move : Hextract Hin; clear; intros. unfold extract_correctness in Hextract. apply extract_cs_exist_c in Hin. destruct Hin as [var [Hina [cs [Hfind Hincs]]]].
          destruct (Hextract var) as [cs' [Hfind' [_ [_ Hgood]]]]. simpl; apply in_or_app; left; done. rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
          apply Hgood in Hincs. exact Hincs.1. }
        unfold extract_correctness in Hextract. intros. apply in_map_iff in H; destruct H as [c0 [Hremove Hin]]; subst c. 
          apply extract_cs_exist_c in Hin. destruct Hin as [v' [Hina [cs [Hfind Hincs]]]]. destruct (Hextract v') as [cs' [Hfind' [_ [_ Hgood]]]]. simpl; apply in_or_app; left; done. rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
          apply Hgood in Hincs; move : Hincs => [_ Hincs]. move : Hincs; clear; unfold remove_solved_c. intro; rewrite Hincs. destruct (remove_solved initial (rhs_terms1 c0)); simpl; done.
        { move : Htarjan Hextract; clear; intros. apply in_map_iff in H. destruct H as [c' [Hremove Hin]]. 
          unfold tarjan_correctness in Htarjan. move : Htarjan => [_ [_ [Hinit Htarjan]]]. assert ([] ++ a :: l = a :: l) by (simpl; done).
          specialize (Htarjan _ _ _ H); clear H. subst c. apply remove_solved_c_vars in H0. move : H0 => [H0 H]. apply (constraint1_vars2constraints1_vars _ Hin) in H0.
          apply Htarjan in H0; clear Htarjan. destruct H0; try done.
          1,2 : unfold extract_correctness in Hextract; apply extract_cs_exist_c in Hin; destruct Hin as [var' [Hina [cs [Hfind Hincs]]]];
          destruct (Hextract var') as [cs' [Hfind' [Hlhs [_ Hgood]]]]. 1,3: simpl; apply in_or_app; left; done. 1,2: rewrite Hfind in Hfind'; inversion Hfind'; clear Hfind'; subst cs'.
          * assert (forall c, List.In c cs -> lhs_var1 c == var') by (apply forallb_forall; done). apply H in Hincs. clear H Hlhs. move /eqP : Hincs => Hincs; subst var'.
            intro. apply Hinit in H; clear Hinit. simpl in H. apply H. apply in_or_app; left; done. 
          * apply Hgood in Hincs; exact Hincs.2. }
      * rewrite /initial_smallest in Hinitial.
        assert (~(le initial v)) by (apply not_true_iff_false in Hle; move : Hle; apply contra_not; intros; apply le_le_bool; done). clear Hle. 
        apply Hinitial in H; clear Hinitial.
        apply not_true_iff_false. apply forallb_neg_neg.
        apply not_true_iff_false in H. apply forallb_neg_neg in H. destruct H as [x [Hin Hunsat]].
        exists x; split; try done. apply in_or_app; left; done.

  intros. case H2 : (solve_alg scclist initial_valuation c1map); try done.
  specialize (Hhelper _ _ H H0 H2). rewrite /initial_valuation in Hhelper. simpl in Hhelper.
  apply Hhelper; try done.
  clear; rewrite /initial_smallest; intros.
  assert (le (PVM.empty nat) v). 
    clear; rewrite /le. intros. discriminate. 
  done.
Qed.

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
