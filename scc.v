From mathcomp Require Import all_ssreflect.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From Solver Require Import Env LoFirrtl HiEnv HiFirrtl constraints graph.
Require Import Coq.Bool.Bool.
From Coq Require Import ZArith Arith List Ascii String Lia FMaps.
Import ListNotations.

Set Implicit Arguments.
Import Prenex Implicits.

Definition substitute_constraint (c : Constraint1) (v : ProdVar.t) (terms : list (nat * ProdVar.t)) (cst : Z.t) : Constraint1 :=
  match find (fun p : term => snd p == v) (rhs_terms1 c) with
  | Some (coe, _) =>
    let new_terms := 
        fold_right (fun '(coe', var) (acc : list term) =>
            match find (fun p : term => snd p == var) acc with
            | None => (coe * coe', var) :: acc 
            | Some (existing_coef, _) =>
                (existing_coef + coe * coe', var) :: (List.remove term_dec (existing_coef, var) acc)
            end
        ) (List.remove term_dec (coe, v) (rhs_terms1 c)) terms in
      {| lhs_var1 := lhs_var1 c;
        rhs_const1 := Z.add (rhs_const1 c) ((Z.of_nat coe) * cst);
        rhs_power := nil;
        rhs_terms1 := new_terms |}
  | None => c
  end.

Section SccCorrectness.

Definition good_terms (terms : list term) : Prop :=
  (forall coe var, List.In (coe, var) terms -> coe <> 0)
  /\ NoDup (List.split terms).2.

Lemma good_terms_NoDup : forall (terms : list term),
  good_terms terms -> NoDup terms.
Proof.
  intros terms [H1 H2]. 
  induction terms as [|[coe var] ts IH].  
  - apply NoDup_nil. 
  - apply NoDup_cons. 
    + intro H.  
      destruct (List.split ts) as [coes vars] eqn : Hsplit.
      simpl in H2. rewrite Hsplit in H2; simpl in H2.
      apply in_split_r in H; rewrite Hsplit in H; simpl in H. apply NoDup_cons_iff in H2. intuition.
    + apply IH. 
      * intros; apply (H1 _ var0). right; done.
      * destruct (List.split ts) as [coes vars] eqn : Hsplit.
        simpl in H2. rewrite Hsplit in H2; simpl in H2. simpl. apply (NoDup_remove_1 nil vars var); simpl; done.
Qed.

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

Lemma terms_value_some_fold valuation : forall terms init result,
  terms_value valuation terms (Some init) = Some result ->
  result =
    fold_left
      (fun (acc : Z) (ax : nat * ProdVar.t) =>
        (acc +
        Z.of_nat
          (ax.1 *
            match PVM.find (elt:=nat) ax.2 valuation with
            | Some val => val
            | None => 0
            end))%Z) terms init.
Proof.
  elim => [|[coe var] tl IH] init result Hvalue /=.
  - injection Hvalue as Heq. subst result. reflexivity.
  - change
      (match PVM.find var valuation with
       | Some val =>
           terms_value valuation tl (Some (init + Z.of_nat (coe * val))%Z)
       | None => None
       end = Some result) in Hvalue.
    destruct (PVM.find var valuation) as [val|] eqn:Hfind.
    + have Htail := IH (init + Z.of_nat (coe * val))%Z result Hvalue.
      simpl. exact Htail.
    + discriminate.
Qed.

Definition terms_value_default (valuation : Valuation)
    (terms : list term) (init : Z) : Z :=
  fold_left
    (fun (acc : Z) (ax : term) =>
      (acc +
       Z.of_nat
         (ax.1 *
          match PVM.find (elt:=nat) ax.2 valuation with
          | Some val => val
          | None => 0
          end))%Z) terms init.

Lemma terms_value_default_cst_add valuation : forall terms cst cst0,
  terms_value_default valuation terms (cst + cst0)%Z =
  (terms_value_default valuation terms cst + cst0)%Z.
Proof.
  elim => [|[coe var] terms IH] cst cst0.
  - reflexivity.
  - change
      (terms_value_default valuation terms
         (cst + cst0 +
          Z.of_nat
            (coe *
             match PVM.find (elt:=nat) var valuation with
             | Some val => val
             | None => 0
             end))%Z =
       terms_value_default valuation terms
         (cst +
          Z.of_nat
            (coe *
             match PVM.find (elt:=nat) var valuation with
             | Some val => val
             | None => 0
             end))%Z + cst0)%Z.
    replace (cst + cst0 +
       Z.of_nat
         (coe *
          match PVM.find (elt:=nat) var valuation with
          | Some val => val
          | None => 0
          end))%Z with
      ((cst +
        Z.of_nat
          (coe *
           match PVM.find (elt:=nat) var valuation with
           | Some val => val
           | None => 0
           end)) + cst0)%Z by ring.
    rewrite (IH _ cst0).
    f_equal.
Qed.

Lemma terms_value_default_app valuation : forall terms0 terms1 cst,
  terms_value_default valuation (terms0 ++ terms1) cst =
  terms_value_default valuation terms1
    (terms_value_default valuation terms0 cst).
Proof.
  move => terms0 terms1 cst.
  rewrite /terms_value_default fold_left_app.
  reflexivity.
Qed.

Lemma terms_value_default_remove valuation (hd : ProdVar.t) :
  forall terms coe cst,
  NoDup terms ->
  List.find (fun p : term => p.2 == hd) terms = Some (coe, hd) ->
  terms_value_default valuation terms cst =
    (terms_value_default valuation
       (List.remove term_dec (coe, hd) terms) cst +
     Z.of_nat
       (coe *
        match PVM.find (elt:=nat) hd valuation with
        | Some val => val
        | None => 0
        end))%Z.
Proof.
  elim => [|[coe' var'] terms IH] coe cst Hnodup Hfind.
  - simpl in Hfind. discriminate.
  - simpl in Hfind.
    case Heq : (var' == hd).
    + move /eqP : Heq => Heq. subst var'.
      rewrite eq_refl /= in Hfind.
      injection Hfind as E. subst coe'.
      apply NoDup_cons_iff in Hnodup.
      destruct Hnodup as [Hnotin Hnodup].
      have Hremove :
        List.remove term_dec (coe, hd) ((coe, hd) :: terms) = terms.
      { simpl. case: (term_dec (coe, hd) (coe, hd)) => [Hequal|Hneq].
        - by rewrite notin_remove.
        - exfalso. apply Hneq. reflexivity. }
      rewrite Hremove /= terms_value_default_cst_add.
      reflexivity.
    + have Hneq : var' <> hd by (move /eqP: Heq; exact).
      apply NoDup_cons_iff in Hnodup.
      destruct Hnodup as [_ Hnodup].
      rewrite Heq /= in Hfind.
      have Hremove :
        List.remove term_dec (coe, hd) ((coe', var') :: terms) =
        (coe', var') :: List.remove term_dec (coe, hd) terms.
      { simpl. case: (term_dec (coe, hd) (coe', var')) => [Hequal|Hnotequal].
        - inversion Hequal. subst. exfalso. apply Hneq. reflexivity.
        - reflexivity. }
      rewrite Hremove /=.
      exact: (IH coe
        (cst + Z.of_nat
          (coe' *
           match PVM.find (elt:=nat) var' valuation with
           | Some val => val
           | None => 0
           end))%Z Hnodup Hfind).
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
  unfold satisfies_constraint1, rhs_value1.

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
    - apply le_0_n.
    - apply (elimT leP); done.

  rewrite Hfindhd Z2Nat.id; try done.
  assert (Hpower : (rhs_power c) = nil) by (apply Hterm in Hin; clear Hterm; exact Hin.2.2).
  assert (Hcst : Z.le (rhs_const1 c) 0) by (apply Hterm in Hin; clear Hterm; exact Hin.2.1).
  rewrite Hpower; clear Hpower; simpl. clear Hin.
  case Hvalue : (terms_value valuation (rhs_terms1 c) (Some (rhs_const1 c))) => [rhs|] /=.
  2: reflexivity.
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

  have Hfold := @terms_value_some_fold valuation (rhs_terms1 c)
    (rhs_const1 c) rhs Hvalue.
  rewrite -Hfold in H0.
  exact: (Z.lt_le_trans _ _ _ H1 H0).
  move => c' Hin'.
  exact: ((Hterm c' Hin').1).
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

Definition substitute_rhs_terms (hd : ProdVar.t) (coe : nat)
    (terms_hd terms_tl : list term) : list term :=
  fold_right
    (fun '(coe', var) (acc : list term) =>
      match List.find (fun p : term => p.2 == var) acc with
      | Some t =>
          let (existing_coef, _) := t in
          (existing_coef + coe * coe', var)
            :: List.remove term_dec (existing_coef, var) acc
      | None => (coe * coe', var) :: acc
      end)
    (List.remove term_dec (coe, hd) terms_tl) terms_hd.

Lemma substitute_constraint_rhs_default valuation
    (hd : ProdVar.t) hd_val coe :
  forall (terms_hd terms_tl : list term) (cst_hd cst_tl : Z),
  good_terms terms_tl -> good_terms terms_hd ->
  List.find (fun p : term => snd p == hd) terms_tl = Some (coe, hd) ->
  PVM.find hd valuation = Some hd_val ->
  terms_value_default valuation (substitute_rhs_terms hd coe terms_hd terms_tl)
    (cst_tl + Z.of_nat coe * cst_hd)%Z =
  (terms_value_default valuation terms_tl cst_tl -
   Z.of_nat (coe * hd_val) +
   Z.of_nat coe * terms_value_default valuation terms_hd cst_hd)%Z.
Proof.
  elim => [|[coe_hd var_hd] terms_hd' IH]
      terms_tl cst_hd cst_tl Hgood_tl Hgood_hd Hfind Hlookup.
  - rewrite /substitute_rhs_terms /= terms_value_default_cst_add.
    have Hremove := @terms_value_default_remove valuation hd
      terms_tl coe cst_tl (good_terms_NoDup Hgood_tl) Hfind.
    rewrite Hlookup in Hremove.
    rewrite Hremove.
    unfold terms_value_default.
    simpl.
    rewrite Nat2Z.inj_mul.
    ring.
  - rewrite /substitute_rhs_terms /=.
    rewrite (terms_value_default_cst_add valuation
      terms_hd' cst_hd
      (Z.of_nat
        (coe_hd *
         match PVM.find (elt:=nat) var_hd valuation with
         | Some val => val
         | None => 0
         end))).
    remember (fold_right
      (fun '(coe', var) (acc : list term) =>
        match List.find (fun p : term => p.2 == var) acc with
        | Some t =>
            let (existing_coef, _) := t in
            (existing_coef + coe * coe', var)
              :: List.remove term_dec (existing_coef, var) acc
        | None => (coe * coe', var) :: acc
        end) (List.remove term_dec (coe, hd) terms_tl) terms_hd')
      as combined_hd'.
    rewrite -Heqcombined_hd'.
    have Hfind_in := find_some _ _ Hfind.
    have Hcoe_nonzero : coe <> 0.
    { exact: (Hgood_tl.1 coe hd Hfind_in.1). }
    have Hgood_comb : good_terms combined_hd'.
    {
        rewrite Heqcombined_hd'.
        apply substitute_good_terms.
        - apply good_terms_remove. exact Hgood_tl.
        - apply good_terms_tl with (a := (coe_hd, var_hd)).
          exact Hgood_hd.
        - exact Hcoe_nonzero.
    }
    case Hfind_hd :
      (List.find (fun p : term => p.2 == var_hd) combined_hd')
      => [[existing_coef var_hd']|].
    + have Hvar_eq : var_hd' = var_hd.
      {
        have [_ Hkey] := find_some _ _ Hfind_hd.
        move /eqP : Hkey => Hkey. simpl in Hkey. exact Hkey.
      }
      subst var_hd'.
      rewrite Z.mul_add_distr_l Z.add_assoc.
      have Hcons :
        (existing_coef + coe * coe_hd, var_hd)
          :: List.remove term_dec (existing_coef, var_hd) combined_hd' =
        [(existing_coef + coe * coe_hd, var_hd)]
          ++ List.remove term_dec (existing_coef, var_hd) combined_hd'
        by reflexivity.
      rewrite Hcons.
      rewrite (terms_value_default_app valuation
        [(existing_coef + coe * coe_hd, var_hd)]
        (remove term_dec (existing_coef, var_hd) combined_hd')
        (cst_tl + Z.of_nat coe * cst_hd)%Z).
      clear Hcons. simpl.
      set (val_hd := match PVM.find (elt:=nat) var_hd valuation with
                     | Some val => val | None => 0 end).
      have Hdist :
        ((existing_coef + coe * coe_hd) * val_hd)%nat =
        (existing_coef * val_hd + (coe * coe_hd) * val_hd)%nat.
      { apply Nat.mul_add_distr_r. }
      rewrite Hdist.
      rewrite Nat2Z.inj_add.
      rewrite (Nat2Z.inj_mul (coe * coe_hd)
        val_hd).
      rewrite (Nat2Z.inj_mul coe coe_hd).
      rewrite (Nat2Z.inj_mul coe_hd val_hd) Z.mul_assoc Z.add_assoc.
      have Hremove := @terms_value_default_remove valuation var_hd
        combined_hd' existing_coef
        (cst_tl + Z.of_nat coe * cst_hd)%Z
        (good_terms_NoDup Hgood_comb) Hfind_hd.
      fold val_hd in Hremove.
      rewrite Nat2Z.inj_mul in Hremove.
      rewrite Nat2Z.inj_mul.
      rewrite -Z.add_assoc.
      rewrite (terms_value_default_cst_add valuation
        (remove term_dec (existing_coef, var_hd) combined_hd')
        (cst_tl + Z.of_nat coe * cst_hd)
        (Z.of_nat existing_coef * Z.of_nat val_hd +
         Z.of_nat coe * Z.of_nat coe_hd * Z.of_nat val_hd)).
      rewrite Z.add_assoc.
      rewrite -Hremove.
      have HIH := IH terms_tl cst_hd cst_tl Hgood_tl
        (good_terms_tl Hgood_hd) Hfind Hlookup.
      rewrite Heqcombined_hd'.
      rewrite HIH.
      ring.
    + have Hcons :
        (coe * coe_hd, var_hd) :: combined_hd' =
        [(coe * coe_hd, var_hd)] ++ combined_hd'
        by reflexivity.
      rewrite Hcons.
      rewrite (terms_value_default_app valuation
        [(coe * coe_hd, var_hd)] combined_hd'
        (cst_tl + Z.of_nat coe * cst_hd)%Z).
      clear Hcons. simpl.
      set (val_hd := match PVM.find (elt:=nat) var_hd valuation with
                     | Some val => val | None => 0 end).
      rewrite Nat2Z.inj_mul Nat2Z.inj_mul.
      rewrite (terms_value_default_cst_add valuation combined_hd'
        (cst_tl + Z.of_nat coe * cst_hd)
        (Z.of_nat coe * Z.of_nat coe_hd * Z.of_nat val_hd)).
      have HIH := IH terms_tl cst_hd cst_tl Hgood_tl
        (good_terms_tl Hgood_hd) Hfind Hlookup.
      rewrite /substitute_rhs_terms in HIH.
      rewrite Heqcombined_hd'.
      rewrite HIH.
      rewrite (Nat2Z.inj_mul coe_hd val_hd).
      ring.
Qed.

Lemma substitute_constraint_rhs valuation
    (hd : ProdVar.t) hd_val coe :
  forall (terms_hd terms_tl : list term) (cst_hd cst_tl result tail hd_rhs : Z),
  good_terms terms_tl -> good_terms terms_hd ->
  List.find (fun p : term => snd p == hd) terms_tl = Some (coe, hd) ->
  PVM.find hd valuation = Some hd_val ->
  terms_value valuation
    (substitute_rhs_terms hd coe terms_hd terms_tl)
    (Some (cst_tl + Z.of_nat coe * cst_hd)%Z) = Some result ->
  terms_value valuation terms_tl (Some cst_tl) = Some tail ->
  terms_value valuation terms_hd (Some cst_hd) = Some hd_rhs ->
  result =
    (tail - Z.of_nat (coe * hd_val) + Z.of_nat coe * hd_rhs)%Z.
Proof.
  move => terms_hd terms_tl cst_hd cst_tl result tail hd_rhs
    Hgood_tl Hgood_hd Hfind Hlookup Hresult Htail Hhd.
  have Hresult_fold := @terms_value_some_fold valuation
    (substitute_rhs_terms hd coe terms_hd terms_tl)
    (cst_tl + Z.of_nat coe * cst_hd)%Z result Hresult.
  have Htail_fold := @terms_value_some_fold valuation terms_tl
    cst_tl tail Htail.
  have Hhd_fold := @terms_value_some_fold valuation terms_hd
    cst_hd hd_rhs Hhd.
  change (result = terms_value_default valuation
      (substitute_rhs_terms hd coe terms_hd terms_tl)
      (cst_tl + Z.of_nat coe * cst_hd)%Z) in Hresult_fold.
  change (tail = terms_value_default valuation terms_tl cst_tl) in Htail_fold.
  change (hd_rhs = terms_value_default valuation terms_hd cst_hd) in Hhd_fold.
  rewrite (@substitute_constraint_rhs_default valuation hd hd_val coe
    terms_hd terms_tl cst_hd cst_tl Hgood_tl Hgood_hd Hfind Hlookup)
    in Hresult_fold.
  rewrite -Htail_fold -Hhd_fold in Hresult_fold.
  exact Hresult_fold.
Qed.

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
  end. 

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
  end.

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
