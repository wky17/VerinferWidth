From mathcomp Require Import all_ssreflect.
From Coq Require Import ZArith Arith List Ascii String Lia FMaps.
From Solver Require Import Env LoFirrtl HiEnv HiFirrtl constraints.
Require Import Coq.Bool.Bool.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
(*Unset Strict Implicit.*) 
Import Prenex Implicits.

(* ------------ solve simple cycle ------------ *)


Definition terms_value_aux (v : Valuation) (ax : (nat * ProdVar.t)) (acc : Z.t) : Z.t :=
  let vi := match PVM.find ax.2 v with
            | Some val => val
            | None => 0
            end in
  Z.add acc (Z.of_nat (ax.1 * vi)).
  
Fixpoint terms_value' (v : Valuation) (terms : list (nat * ProdVar.t)) (acc : Z.t) : Z.t :=
  match terms with
  | nil => acc
  | hd::tl => terms_value' v tl (terms_value_aux v hd acc) 
  end.

Definition power_value' (v : Valuation) (terms : list (nat * ProdVar.t)) : Z.t :=
  match terms with
  | nil => 0
  | _ => let n := terms_value' v terms 0 in Z.pow 2 n
  end.

Definition rhs_value1' (v: Valuation) (c : Constraint1) : Z.t :=
  terms_value' v c.(rhs_terms1) c.(rhs_const1) (* + power_value' v c.(rhs_power) *) .

Definition rhs_vars' (c : Constraint1) : list ProdVar.t :=
  map snd (rhs_terms1 c) (* ++ map snd (rhs_power c) *) .

Definition satisfies_constraint1' (v: Valuation) (c: Constraint1) : bool :=
  match PVM.find c.(lhs_var1) v with
  | Some val => Z.leb (rhs_value1' v c) (Z.of_nat val)
  | None => false
  end.

Fixpoint satisfies_all_constraint1 (v : Valuation) (cs : list Constraint1) : bool :=
  match cs with
  | nil => true
  | c :: cs' => andb (satisfies_constraint1' v c) (satisfies_all_constraint1 v cs')
  end.

Inductive node : Type :=
| Zero
| Node : ProdVar.t -> node. 

Module NodeVar <: OrderedType.

  Definition t := node.
  Definition eq (x y : t) : Prop :=
    match x, y with
    | Zero, Zero => true
    | Node p1, Node p2 => ProdVar.eq p1 p2
    | _, _ => false
    end.

  Lemma eq_refl (x : t) : eq x x.
  Proof.
    destruct x; simpl.
    - reflexivity.
    - apply ProdVar.eq_refl.
  Qed.

  Lemma eq_sym (x y : t) : eq x y -> eq y x.
  Proof.
    destruct x, y; simpl; auto.
    apply ProdVar.eq_sym.
  Qed.

  Lemma eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof.
    destruct x, y, z; simpl; auto; try done.
    intros H1 H2.
    eapply ProdVar.eq_trans; eauto.
  Qed.

  (* 定义等式判断的可判定性 *)
  Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    destruct x, y; simpl; try done.
    - left; reflexivity.
    - right; congruence.
    - right; congruence.
    - destruct (ProdVar.eq_dec t0 t1).
      + left; assumption.
      + right; congruence.
  Defined.

  (* 定义严格小于关系lt *)
  Definition lt (x y : t) : Prop :=
    match x, y with
    | Zero, Node _ => true
    | Node p1, Node p2 => ProdVar.lt p1 p2
    | _, _ => false
    end.

  (* 证明lt是传递的 *)
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    destruct x, y, z; simpl; auto; try done.
    intros Hlt1 Hlt2. eapply ProdVar.lt_trans; eauto.
  Qed.

  (* 证明lt蕴含不等 *)
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    destruct x, y; simpl; auto.
    apply ProdVar.lt_not_eq.
  Qed.

  (* 定义比较函数 *)
  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    destruct x, y; simpl.
    - apply EQ. reflexivity.
    - apply LT. reflexivity.
    - apply GT. reflexivity.
    - destruct (ProdVar.compare t0 t1).
      + apply LT. assumption.
      + apply EQ. assumption.
      + apply GT. assumption.
  Defined.

  (* 定义布尔等式判断函数 *)
  Definition eqn (x y : t) : bool :=
    match x, y with
    | Zero, Zero => true
    | Node p1, Node p2 => ProdVar.eqn p1 p2
    | _, _ => false
    end.

  (* 证明布尔等式与命题等式的一致性 *)
  Lemma eqP : Equality.axiom eqn.
  Proof.
    intros x y. unfold eqn, eq.
    destruct x, y; simpl; try solve [constructor; congruence].
    - destruct (ProdVar.eqP t0 t1) as [Heq|Hneq].
      + rewrite Heq. constructor; auto.
      + constructor. congruence.
  Qed.

End NodeVar.

Module NVM := VarMap NodeVar.

Section simplecycle.
Definition adj_matrix := PVM.t (NVM.t Z.t).


Lemma node_eq_leibniz : forall (v a : NodeVar.t), NodeVar.eq v a -> v = a.
Proof.
  intros v a H.
  destruct v; destruct a; simpl in H; try discriminate; try reflexivity.
  destruct H as [H1 H2]. apply f_equal.
  destruct t as [x1 x2]; destruct t0 as [y1 y2]; simpl in H1, H2.
  move /eqP : H1 ->; move /eqP : H2 ->. reflexivity.
Qed.

Lemma find_add_neq_z_fm : forall (v a : ProdVar.t) (val : NVM.t Z) (fm : adj_matrix), v <> a -> PVM.find v (PVM.add a val fm) = PVM.find v fm.
Proof. move => v a val fm. apply find_add_neq. Qed.

Lemma find_add_neq_z : forall (v a : NodeVar.t) (val : Z) (fm : NVM.t Z), v <> a -> NVM.find v (NVM.add a val fm) = NVM.find v fm.
Proof.
  move => v a val fm Hneq.
  apply NVM.Lemmas.find_add_neq.
  move => Heq. apply Hneq. exact: node_eq_leibniz.
Qed.

Lemma find_add_eq_z_fm : forall (a : ProdVar.t) (val : NVM.t Z) (fm : adj_matrix), PVM.find a (PVM.add a val fm) = Some val.
Proof. move => a val fm. apply find_add_eq. Qed.

Lemma find_add_eq_z : forall (a : NodeVar.t) (val : Z) (fm : NVM.t Z), NVM.find a (NVM.add a val fm) = Some val.
Proof. move => a val fm. apply NVM.Lemmas.find_add_eq. apply NodeVar.eq_refl. Qed.


Definition get_weight (src : ProdVar.t) (dst : NodeVar.t) (m : adj_matrix) : option Z.t :=
  match PVM.find src m with
  | Some dst_map => NVM.find dst dst_map
  | None => None
  end.

Fixpoint add_edge_of_cs (cs : list Constraint1) (m : adj_matrix) : adj_matrix :=
  match cs with
  | nil => m
  | hd :: tl => let new_m := match PVM.find (lhs_var1 hd) m, (rhs_terms1 hd) with 
            (* 经过第一步init，记录所有v到v的距离为0，所有lhs应该都可以被find *)
            | Some dst_map, nil => match NVM.find Zero dst_map with (* 常数约束, 修改lhs到0点的距离 *) 
                            | Some dist => let new_dst_map := NVM.add Zero (Z.max dist (rhs_const1 hd)) dst_map in
                                    PVM.add (lhs_var1 hd) new_dst_map m
                            | None => let new_dst_map := NVM.add Zero (rhs_const1 hd) dst_map in
                                    PVM.add (lhs_var1 hd) new_dst_map m
                            end
            | Some dst_map, [(1,v)] => match NVM.find (Node v) dst_map with (* 修改lhs到v的距离 *) 
                            | Some dist => let new_dst_map := NVM.add (Node v) (Z.max dist (rhs_const1 hd)) dst_map in
                                    PVM.add (lhs_var1 hd) new_dst_map m
                            | None => let new_dst_map := NVM.add (Node v) (rhs_const1 hd) dst_map in
                                    PVM.add (lhs_var1 hd) new_dst_map m
                            end
            | _, _ => m (* 不存在其他形式的约束 *)
            end in add_edge_of_cs tl new_m
  end.

Fixpoint add_edge_of_cs' (cs : list Constraint1) (m : adj_matrix) : adj_matrix :=
  match cs with
  | nil => m
  | hd :: tl => match PVM.find (lhs_var1 hd) m, (rhs_terms1 hd) with 
            (* 经过第一步init，记录所有v到v的距离为0，所有lhs应该都可以被find *)
                | Some dst_map, nil =>
                    match NVM.find Zero dst_map with (* 常数约束, 修改lhs到0点的距离 *) 
                    | Some dist =>
                        let new_dst_map := NVM.add Zero (Z.max dist (rhs_const1 hd)) dst_map in
                        PVM.add (lhs_var1 hd) new_dst_map (add_edge_of_cs' tl m)
                    | None =>
                        let new_dst_map := NVM.add Zero (rhs_const1 hd) dst_map in
                        PVM.add (lhs_var1 hd) new_dst_map (add_edge_of_cs' tl m)
                    end
                | Some dst_map, [(1,v)] =>
                    match NVM.find (Node v) dst_map with (* 修改lhs到v的距离 *) 
                    | Some dist =>
                        let new_dst_map := NVM.add (Node v) (Z.max dist (rhs_const1 hd)) dst_map in
                        PVM.add (lhs_var1 hd) new_dst_map (add_edge_of_cs' tl m)
                    | None =>
                        let new_dst_map := NVM.add (Node v) (rhs_const1 hd) dst_map in
                        PVM.add (lhs_var1 hd) new_dst_map (add_edge_of_cs' tl m)
                    end
            | _, _ => (add_edge_of_cs' tl m) (* 不存在其他形式的约束 *)
            end 
  end.

Definition add_edge_of_c (c : Constraint1) (m : adj_matrix) : adj_matrix :=
  match PVM.find (lhs_var1 c) m, (rhs_terms1 c) with 
  | Some dst_map, nil =>
      match NVM.find Zero dst_map with (* 常数约束, 修改lhs到0点的距离 *) 
      | Some dist =>
          let new_dst_map := NVM.add Zero (Z.max dist (rhs_const1 c)) dst_map in
          PVM.add (lhs_var1 c) new_dst_map m
      | None =>
          let new_dst_map := NVM.add Zero (rhs_const1 c) dst_map in
          PVM.add (lhs_var1 c) new_dst_map m
      end
  | Some dst_map, [(1,v)] =>
      match NVM.find (Node v) dst_map with (* 修改lhs到v的距离 *) 
      | Some dist =>
          let new_dst_map := NVM.add (Node v) (Z.max dist (rhs_const1 c)) dst_map in
          PVM.add (lhs_var1 c) new_dst_map m
      | None =>
          let new_dst_map := NVM.add (Node v) (rhs_const1 c) dst_map in
          PVM.add (lhs_var1 c) new_dst_map m
      end
  | _, _ => m (* 不存在其他形式的约束 *)
  end .

(* Fixpoint add_edge_of_c_s cs m := *)
(*   match cs with *)
(*   |nil => m *)
(*   | h ::t => add_edge_of_c_s t (add_edge_of_c h m) *)
(*   end. *)

Fixpoint add_edge_of_c_s cs m :=
  match cs with
  |nil => m
  | h ::t => add_edge_of_c h (add_edge_of_c_s t m)
  end.
  
          
Definition init_dist_map (nodes : list ProdVar.t) (cs : list Constraint1) : adj_matrix :=
  (* 自己到自己设为0 *)
  let map0 := List.fold_left (fun temp_matrix v => let temp_dst_map := NVM.add (Node v) 0%Z (NVM.empty Z.t) in(* v到v距离为0 *)
                                PVM.add v temp_dst_map temp_matrix) nodes (PVM.empty (NVM.t Z.t)) in
  (* 将每一条约束画出边 *)
  add_edge_of_cs cs map0.
(* 其他为None，即为两点间还没有边，距离的最大值为-∞ *)

Fixpoint map0 (n : list ProdVar.t) m :=
  match n with
  | nil => m
  | hd :: tl => 
      let temp_dst_map := NVM.add (Node hd) 0%Z (NVM.empty Z.t) (* v到v距离为0 *)
      in
      PVM.add hd temp_dst_map (map0 tl m)
      (* map0 tl (PVM.add hd temp_dst_map m) *)
  end.

Definition init_dist_map' (nodes : list ProdVar.t) (cs : list Constraint1) : adj_matrix :=
  add_edge_of_cs' cs (map0 nodes (PVM.empty (NVM.t Z.t))).


Definition floyd_update (k i: ProdVar.t) (nodes : list NodeVar.t) (m : adj_matrix) : adj_matrix :=
  (* 对给定中间节点 k 和源节点 i，更新 i 到所有目标节点的最长路径。 *)
  match PVM.find i m with
  | None => m
  | Some dst_map => let new_dst_map := 
      List.fold_left (fun acc j => (* j是dst，已存i到j最大路径是w *)
        match NVM.find j acc, get_weight i (Node k) m, get_weight k j m with
        | Some w, Some w1, Some w2 => let new_w := Z.max w (Z.add w1 w2) in
                              NVM.add j new_w acc
        | _, Some w1, Some w2 => let new_w := Z.add w1 w2 in
                              NVM.add j new_w acc
        | _, _, _ => acc
        end
      ) nodes dst_map in PVM.add i new_dst_map m
  end.

(* new dist for j, if i -> k -> j is longer *)
Definition new_dst_map_aux dm j k i m : NVM.t Z.t:=
  match NVM.find j dm, get_weight i (Node k) m, get_weight k j m with
  | Some w, Some w1, Some w2 =>
      let new_w := Z.max w (Z.add w1 w2) in
      NVM.add j new_w dm
  | _, Some w1, Some w2 =>
      let new_w := Z.add w1 w2 in
      NVM.add j new_w dm
  | _, _, _ => dm
  end.

(* new dist for all nodes n, if i -> k -> n is longer  *)
Fixpoint new_dst_map (n : list NodeVar.t) dm k i m : NVM.t Z.t :=
  match n with
  | nil => dm
  | hd :: tl => new_dst_map_aux (new_dst_map tl dm k i m) hd k i m
  end.

(* add dm in m for a given i, using the updated dist map caused by k *)
Definition floyd_update' (k i: ProdVar.t) (nodes : list NodeVar.t) (m : adj_matrix) : adj_matrix :=
  match PVM.find i m with
  | None => m
  | Some dst_map => PVM.add i (new_dst_map nodes dst_map k i m) m
  end.

Definition floyd_loop_map (nodes: list ProdVar.t) (cs : list Constraint1) : adj_matrix :=
  List.fold_left (fun dist k =>
    List.fold_left (fun dist' i =>
      floyd_update k i (Zero :: map (fun p => Node p) nodes) dist'
    ) nodes dist
    ) nodes (init_dist_map nodes cs).

(* add dm in m for all nodes n and Zero, using the update dist map caused by k*)
Fixpoint inner_loop1 (n : list ProdVar.t) (m : adj_matrix) (k : ProdVar.t) :=
  match n with
  | nil => m
  | hd :: tl =>
      (* floyd_update' k hd (Zero :: map (fun p => Node p) n) (inner_loop1 tl m k) *)
      inner_loop1 tl (floyd_update' k hd (Zero :: map (fun p => Node p) n) m) k
  end.                             

(* add dm in m for all nodes n and Zero, inductively update dist map caused by all nodes n*)
Fixpoint inner_loop2 (n : list ProdVar.t) (m : adj_matrix) :=
  match n with
  | nil => m
  | hd :: tl => inner_loop2 tl (inner_loop1 n m hd)
  end.

(* use inner_loop2 for nodes and init_dist_map*)
Definition floyd_loop_map' (nodes: list ProdVar.t) (cs : list Constraint1) : adj_matrix :=
  inner_loop2 nodes (init_dist_map' nodes cs).

Lemma find_empty_None : forall [A : Type] s, PVM.find s (PVM.empty A) = None.
Proof. move => A s. reflexivity. Qed.

Lemma map0_correct : forall nds n  ml d,
    PVM.find n (map0 nds (PVM.empty (NVM.t Z.t))) = Some ml ->
    NVM.find (Node n) ml = Some d -> d= Z0.
Proof.
  elim => [|nhd ntl Hm] n ml d .
  - rewrite /=find_empty_None//.
  - rewrite/=.
    case Hnhd : (n == nhd).
    + rewrite (eqP Hnhd) find_add_eq_z_fm.
      move => Hml; injection Hml; move => Heq; rewrite -Heq find_add_eq_z//.
      move => Hinj; by injection Hinj.
    + rewrite find_add_neq_z_fm. apply Hm.
      intro; rewrite H eq_refl //in Hnhd.
Qed.



Lemma map0_correct_nn : forall nds n s ml ,
    (s == n) = false ->
    PVM.find n (map0 nds (PVM.empty (NVM.t Z.t))) = Some ml ->
    NVM.find (Node s) ml = None.
Proof.
  elim => [|nhd ntl Hm] n s ml .
  - rewrite /=find_empty_None//.
  - rewrite/=.
    case Hnhd : (n == nhd).
    + rewrite (eqP Hnhd) find_add_eq_z_fm.
      move => Hneq Hml; injection Hml; move => Heq. rewrite -Heq find_add_neq_z//.
      move => Hinj; inversion Hinj; rewrite H0 eq_refl// in Hneq.
    + rewrite find_add_neq_z_fm. apply Hm.
      intro; rewrite H eq_refl //in Hnhd.
Qed.
            
Lemma add_edge_of_cs_correct : forall cs d fm0 ml0 ml1,
    PVM.find d fm0 = Some ml0 ->
    PVM.find d (add_edge_of_cs' cs fm0) = Some ml1 ->
    forall s dst0 dst1,
      NVM.find s ml0 = Some dst0 ->
      NVM.find s ml1 = Some dst1 ->
      Z.le dst0 dst1.
Proof.
  elim => [|csh cstl Hm] d fm0 ml0 ml1.
  - rewrite /=. move => Hf0 Hf1 s dst0 dst1. rewrite Hf0 in Hf1.
    injection Hf1; move =>Heq. rewrite Heq; move => Hnf0 Hnf1.
    rewrite Hnf0 in Hnf1; injection Hnf1; move =>Heqn; rewrite Heqn; lia.
  - rewrite/=. move => Hfd.
    case Hlhs: (PVM.find (lhs_var1 csh) fm0) => [vcsh|].
    + case Hrhs: (rhs_terms1 csh) => [|[rhshd vrhs] rhstl].
      * case Hzero : (NVM.find Zero vcsh) => [vzero|].
        { move : Hlhs.
          case Hdeq : (d == lhs_var1 csh).
          -
            rewrite -(eqP Hdeq). move => Hfdfm0.
            rewrite find_add_eq_z_fm => Hvdeq.
            injection Hvdeq; move => Heq. rewrite -Heq.
            rewrite Hfd in Hfdfm0; injection Hfdfm0; move => Heq'; rewrite Heq' in Heq *.
            move => s dst0 dst1. move => Hnfd0.
            case Hszero : s => [|vs].
            +
              rewrite find_add_eq_z; move => Hfdz; injection Hfdz; move => Heqvz.
              rewrite -Heqvz.
              rewrite Hszero in Hnfd0. rewrite Hnfd0 in Hzero; injection Hzero.
              move => Heqdst0. rewrite Heqdst0. exact: Z.le_max_l.
            +
              rewrite find_add_neq_z.
              rewrite -Hszero Hnfd0; move => Hdst01; injection Hdst01; move => Hdst.
              lia.
              intro. inversion H.
          -
            rewrite find_add_neq_z_fm. move => Hfcsh. move : Hfd.
            apply Hm.
            intro. rewrite H in Hdeq. rewrite eq_refl //in Hdeq.
        }
        { move : Hlhs.
          case Hdeq : (d == lhs_var1 csh).
          -
            rewrite -(eqP Hdeq). move => Hfdfm0.
            rewrite find_add_eq_z_fm => Hvdeq.
            injection Hvdeq; move => Heq. rewrite -Heq.
            rewrite Hfd in Hfdfm0; injection Hfdfm0; move => Heq'; rewrite Heq' in Heq *.
            move => s dst0 dst1. move => Hnfd0.
            case Hszero : s => [|vs].
            +
              rewrite Hszero in Hnfd0. rewrite Hzero in Hnfd0. discriminate.
            +
              rewrite find_add_neq_z.
              rewrite -Hszero Hnfd0; move => Hdst01; injection Hdst01; move => Hdst.
              lia.
              intro. inversion H.
          -
            rewrite find_add_neq_z_fm. move => Hfcsh. move : Hfd.
            apply Hm.
            intro. rewrite H in Hdeq. rewrite eq_refl //in Hdeq.
        }
      * move : Hrhs.
        case Hrhshd : rhshd => [|n].
        {
          move => _. move : Hfd. apply Hm.
        }
        { case Hn : n => [|m].
          -
            case rhstl => [|rhstlh rhstlt].
            +
              move => Hrterm.
              case Hfdvrhs : (NVM.find (Node vrhs) vcsh) => [dist|].
              *
                move : Hlhs.
                case Hdeq : (d == lhs_var1 csh).
                {
                  rewrite -(eqP Hdeq). move => Hfdfm0.
                  rewrite Hfd in Hfdfm0; injection Hfdfm0; move => Heqml0.
                  rewrite find_add_eq_z_fm => Hvdeq.
                  injection Hvdeq; move => Heq. rewrite -Heq.
                  rewrite Heqml0 in Heq *.
                  move => s dst0 dst1. 
                  case Hszero : s => [|vs].
                  -
                    rewrite find_add_neq_z. move => Hfdz0 Hfdz1.
                    rewrite Hfdz1 in Hfdz0; injection Hfdz0.
                    move => Heqdst0; rewrite Heqdst0. lia.
                    intro. inversion H.
                  -
                    case Hvseq : (vs == vrhs).
                    + rewrite (eqP Hvseq) find_add_eq_z Hfdvrhs.
                      move => Hdst0 Hdst1. injection Hdst1; injection Hdst0. move => Heqdst0  Heqdst1.
                      rewrite -Heqdst1 -Heqdst0.
                      apply Z.le_max_l.
                    + rewrite find_add_neq_z. move => Hdst0 Hdst1.
                      rewrite Hdst1 in Hdst0; injection Hdst0; move => Hdst01. lia.
                      intro. injection H; move => Heqvs; rewrite Heqvs eq_refl //in Hvseq. 
                }
                {
                  rewrite find_add_neq_z_fm. move => _.
                  move : Hfd. apply Hm.
                  intro. rewrite H eq_refl //in Hdeq.
                }
              * move : Hlhs.
                case Hdeq : (d == lhs_var1 csh).
                {
                  rewrite -(eqP Hdeq) find_add_eq_z_fm.
                  move => Hfd'. rewrite Hfd in Hfd'; injection Hfd'.
                  move => Heqml0; rewrite Heqml0. 
                  move => Hml1; injection Hml1; move => Heqml1.
                  rewrite -Heqml1. move => s dst0 dst1.
                  case Hszero : s => [|vs].
                  -
                    rewrite find_add_neq_z.
                    move => Hd0 Hd1; rewrite Hd0 in Hd1; injection Hd1; move => Heq01. lia.
                    intro. inversion H.
                  - 
                    case Hveq : (vs == vrhs).
                    + rewrite (eqP Hveq) . move => Hsm; rewrite Hsm in Hfdvrhs; discriminate.
                    + rewrite find_add_neq_z.
                      move => Hd0 Hd1; rewrite Hd0 in Hd1; injection Hd1; move => Heq01. lia.
                      intro; injection H; move => Hf; rewrite Hf eq_refl// in Hveq.
                }
                {
                  rewrite find_add_neq_z_fm. move => _. move : Hfd.
                  apply Hm.
                  intro. rewrite H eq_refl //in Hdeq .
                }
        
              * move => _. move : Hfd. apply Hm.
            + move => _. move : Hfd. apply Hm.
        }
        move : Hfd. apply Hm.
Qed.

Lemma add_edge_of_c_find_map : forall c c' fm ,
    ~ PVM.find c fm = None ->
    ~ PVM.find c (add_edge_of_c c' fm) = None.
Proof.
  move => c c' fm Hnn.
  rewrite /add_edge_of_c.
  case Hfdc : (PVM.find (lhs_var1 c') fm) => [fdc|]; last done.
  case Hrhs : (rhs_terms1 c') => [|[a v] tl].
  - case Hfdz : (NVM.find Zero fdc) => [fdz|];
     ( case Heq : (c == lhs_var1 c');
       [rewrite (eqP Heq) find_add_eq_z_fm// |
          rewrite find_add_neq_z_fm//;
            move => Hneq; rewrite Hneq eq_refl// in Heq]).
  - case Ha : a=>[|n]; first done.
    case Hn : n=>[|m]; last done.
    case Htl: tl=> [|ttl]; last done.
    case Hfdv : (NVM.find (Node v) fdc)=>[fdv|];
     ( case Heq : (c == lhs_var1 c');
       [rewrite (eqP Heq) find_add_eq_z_fm// |
          rewrite find_add_neq_z_fm//;
            move => Hneq; rewrite Hneq eq_refl// in Heq]).
Qed.

Lemma add_edge_of_c_s_find_map : forall cs c fm ,
    ~ PVM.find (c) fm = None ->
    ~ PVM.find (c) (add_edge_of_c_s cs fm) = None.
Proof.
  elim => cs fm Hfdc; rewrite /=//.
  move => c fm0 Hnn.
  apply add_edge_of_c_find_map. by apply Hfdc.
Qed.  

(*Lemma add_edge_of_c_find_edge : forall c c' fm ml ml0 v ,
    (rhs_terms1 c) = [(1, v)] ->
    PVM.find (lhs_var1 c) fm = Some ml0 ->
    ~ NVM.find (Node v) ml0 = None ->
    PVM.find (lhs_var1 c) (add_edge_of_c c' fm) = Some ml ->
    ~ NVM.find (Node v) ml = None.
Proof.
  move => c c' fm ml0 ml v Hrhs.
  rewrite /add_edge_of_c.
  case Hfdc : (PVM.find (lhs_var1 c) fm) => [fdc|]; last done.
  move => Hfdml; injection Hfdml; move => Hmleq; rewrite Hmleq in Hfdc *.
  move => Hfdn.
  case Hlhseq : (lhs_var1 c == lhs_var1 c').
  - rewrite -(eqP Hlhseq) Hfdc.
    case Hrhsc : (rhs_terms1 c') => [|[a r] tl].
    +
Admitted.*)

Lemma add_edge_of_c_find_edge' : forall c fm ml v ,
    (rhs_terms1 c) = [(1, v)] ->
    ~ PVM.find (lhs_var1 c) fm = None ->
    PVM.find (lhs_var1 c) (add_edge_of_c c fm) = Some ml ->
    ~ NVM.find (Node v) ml = None.
Proof.
  move => c fm ml v Hrhs.
  rewrite /add_edge_of_c.
  case Hfdc : (PVM.find (lhs_var1 c) fm) => [fdc|]; last done.
  move => _.
  (* move => Hfdml; injection Hfdml; move => Hmleq; rewrite Hmleq in Hfdc *. *)
  rewrite Hrhs.
  case Hnfds : (NVM.find (Node v) fdc) => [nfdv|];
  (rewrite find_add_eq_z_fm; move => Hml;
    injection Hml; move => Heq; rewrite -Heq find_add_eq_z//).
Qed.

Lemma add_edge_of_c_find_edge'' : forall c fm v ,
    (rhs_terms1 c) = [(1, v)] ->
    ~ PVM.find (lhs_var1 c) fm = None ->
    (forall ml, PVM.find (lhs_var1 c) (add_edge_of_c c fm) = Some ml ->
    ~ NVM.find (Node v) ml = None).
Proof.
  move => c fm v Hrhs Hfdc.
  rewrite /add_edge_of_c. move => ml.
  case Hfdcfm : (PVM.find (lhs_var1 c) fm) => [fdc|]; last done.
  (* move => Hfdml; injection Hfdml; move => Hmleq; rewrite Hmleq in Hfdc *. *)
  rewrite Hrhs. 
  case Hnfds : (NVM.find (Node v) fdc) => [nfdv|]. 
  - rewrite find_add_eq_z_fm; move => Hml; injection Hml; move => Heq; rewrite -Heq.
    rewrite find_add_eq_z//.
  - rewrite find_add_eq_z_fm; move => Hml; injection Hml; move => Heq.
    rewrite -Heq find_add_eq_z//.
Qed.

Fixpoint find_s2d_cs (s : ProdVar.t) (d : ProdVar.t) cs : list Z :=
  match cs with
  | nil => nil
  | hd :: tl => if (lhs_var1 hd == s) && (rhs_terms1 hd == [(1,d)])
                then (rhs_const1 hd) :: (find_s2d_cs s d tl)
                else (find_s2d_cs s d tl)
  end.

Fixpoint max_const1 (s : ProdVar.t) (d : ProdVar.t) cs  : Z :=
  match cs with
  | nil => 0
  | hd :: tl => if (lhs_var1 hd == s) && (rhs_terms1 hd == [(1,d)])
               then Z.max (rhs_const1 hd) (max_const1 s d tl)
               else (max_const1 s d tl)
  end.

Lemma add_edge_of_c_sm_max : forall c v fm dm0 d0 dm,
    (rhs_terms1 c) = [(1, v)] ->
    PVM.find (lhs_var1 c) fm = Some dm0 ->
    NVM.find (Node v) dm0 = Some d0 ->
    PVM.find (lhs_var1 c) (add_edge_of_c c fm) = Some dm ->
    NVM.find (Node v) dm = Some (Z.max d0 (rhs_const1 c)).
Proof.
  move =>  c v fm dm0 d0 dm Hrhs Hfdc0 Hfdv0 .
  rewrite /add_edge_of_c Hfdc0 Hrhs Hfdv0 find_add_eq_z_fm.
  move => Hinj; injection Hinj; move => Heq; rewrite -Heq.
  rewrite find_add_eq_z//. 
Qed.

Lemma add_edge_of_c_sm_max_same : forall c c' v fm dm0 d0 dm,
    PVM.find c fm = Some dm0 ->
    NVM.find (Node v) dm0 = Some d0 ->
    (lhs_var1 c') = c -> rhs_terms1 c' = [(1,v)] ->
    PVM.find c (add_edge_of_c c' fm) = Some dm ->
    NVM.find (Node v) dm = Some (Z.max d0 (rhs_const1 c')).
Proof.
  move =>  c c' v fm dm0 d0 dm Hfdc0 Hfdv0 Hleq  Hreq.
  rewrite /add_edge_of_c Hleq Hfdc0 Hreq Hfdv0 find_add_eq_z_fm.
  move => Hinj; injection Hinj; move => Heq; rewrite -Heq.
  rewrite find_add_eq_z//.
Qed.

Lemma add_edge_of_c_sm_max_diff : forall c c' v fm dm0 d0 dm,
    PVM.find c fm = Some dm0 ->
    NVM.find (Node v) dm0 = Some d0 ->
    (((lhs_var1 c') == c) && (rhs_terms1 c' == [(1,v)])) = false ->
    PVM.find c (add_edge_of_c c' fm) = Some dm ->
    NVM.find (Node v) dm = Some d0.
Proof.
  move =>  c c' v fm dm0 d0 dm Hfdc0 Hfdv0 Hneq.
  rewrite /add_edge_of_c.
  rewrite andb_false_iff in Hneq. move : Hneq => [Hneql|Hneqr].
  - case Hfdc' : (PVM.find (lhs_var1 c') fm ) => [ml'|].
    + case Hrhs : (rhs_terms1 c') => [|[a s] tl].
      * case Hfdz' : (NVM.find Zero ml') => [mlz'|].
        { rewrite find_add_neq_z_fm.
          rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
          move => Heq; rewrite Heq eq_refl// in Hneql. }
        { rewrite find_add_neq_z_fm.
          rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
          move => Heq; rewrite Heq eq_refl// in Hneql. }
      * case Ha : a => [|n].
        { rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//. }
        { case Hn : n => [|m] .
          - case Htl : tl => [|tltl].
            + case Hfds : (NVM.find (Node s) ml' ) => [d1|].
              * rewrite find_add_neq_z_fm. 
                rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
                move => Heq; rewrite Heq eq_refl// in Hneql.
              * rewrite find_add_neq_z_fm. 
                rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
                move => Heq; rewrite Heq eq_refl// in Hneql.
            + rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
          - rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
        }
    + rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
  - case Hleq : ((lhs_var1 c') == c).
    + rewrite (eqP Hleq) Hfdc0.
      case Hrhs : (rhs_terms1 c') => [|[a s] tl].
      * case Hfdz' : (NVM.find Zero dm0) => [mlz'|].
        { rewrite find_add_eq_z_fm.
          move => Hinj; injection Hinj; move => Heq; rewrite -Heq find_add_neq_z//.
        }
        { rewrite find_add_eq_z_fm.
          move => Hinj; injection Hinj; move => Heq; rewrite -Heq find_add_neq_z//.
        }
      * case Ha : a => [|n].
        { rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//. }
        { case Hn : n => [|m] .
          - case Htl : tl => [|tltl].
            + case Hfds : (NVM.find (Node s) dm0) => [d1|].
              * rewrite find_add_eq_z_fm. 
                move => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
                rewrite find_add_neq_z//.
                rewrite Ha Hn Htl in Hrhs. rewrite Hrhs in Hneqr.
                move => Hvs; injection Hvs; move => Heqvs; rewrite Heqvs eq_refl // in Hneqr.
              * rewrite find_add_eq_z_fm. 
                move => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
                rewrite find_add_neq_z//.
                rewrite Ha Hn Htl in Hrhs. rewrite Hrhs in Hneqr.
                move => Hvs; injection Hvs; move => Heqvs; rewrite Heqvs eq_refl // in Hneqr.
            + rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
          - rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
        }
    + case Hfdc' : (PVM.find (lhs_var1 c') fm) => [ml'|].
      * case Hrhs : (rhs_terms1 c') => [|[a s] tl].
      { case Hfdz' : (NVM.find Zero ml') => [mlz'|].
        - rewrite find_add_neq_z_fm.
          rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
          move => Heq; rewrite Heq eq_refl// in Hleq.
        - rewrite find_add_neq_z_fm.
          rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
          move => Heq; rewrite Heq eq_refl// in Hleq.
      }
      { case Ha : a => [|n].
        - rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
        - case Hn : n => [|m] .
          + case Htl : tl => [|tltl].
            * case Hfds : (NVM.find (Node s) ml' ) => [d1|].
              { rewrite find_add_neq_z_fm. 
                rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
                move => Heq; rewrite Heq eq_refl// in Hleq.
              }
              { rewrite find_add_neq_z_fm. 
                rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
                move => Heq; rewrite Heq eq_refl// in Hleq.
              }
            * rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
          + rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
        }
  - rewrite Hfdc0 => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
Qed.

Lemma add_edge_of_c_le : forall c v fm dm0 d0 d1 dm,
    (rhs_terms1 c) = [(1, v)] ->
    PVM.find (lhs_var1 c) fm = Some dm0 ->
    NVM.find (Node v) dm0 = Some d0 ->
    PVM.find (lhs_var1 c) (add_edge_of_c c fm) = Some dm ->
    NVM.find (Node v) dm = Some d1 ->
    Z.le d0 d1.
Proof.
  move =>  c v fm dm0 d0 d1 dm Hrhs Hfdc0 Hfdv0 Hfdc1 Hfdv1.
  move : (@add_edge_of_c_sm_max c v fm dm0 d0 dm Hrhs Hfdc0 Hfdv0 Hfdc1).
  rewrite Hfdv1.
  move => Hinj; injection Hinj; move => Heq; rewrite Heq. lia.
Qed.
  
Lemma add_edge_of_c_nn_max : forall c v fm dm0 dm dst,
    PVM.find (lhs_var1 c) fm = Some dm0 ->
    NVM.find (Node v) dm0 = None ->
    PVM.find (lhs_var1 c) (add_edge_of_c c fm) = Some dm ->
    NVM.find (Node v) dm = Some dst ->
    dst = rhs_const1 c.
Proof.
  move =>  c v fm dm0 dm dst Hfdc0 Hfdv0 .
  rewrite /add_edge_of_c Hfdc0.
  case Hrhs : (rhs_terms1 c) => [|[a s] tl].
  - case Hfdz0 : (NVM.find Zero dm0) => [dz0|].
    + rewrite find_add_eq_z_fm.
      move => Hinj; injection Hinj; move => Heq; rewrite -Heq.
      rewrite find_add_neq_z => Hneq. rewrite Hneq // in Hfdv0.
      inversion Hneq.
    + rewrite find_add_eq_z_fm.
      move => Hinj; injection Hinj; move => Heq; rewrite -Heq.
      rewrite find_add_neq_z => Hneq. rewrite Hneq // in Hfdv0.
      inversion Hneq.
  - case Ha : a => [|n].
    + rewrite Hfdc0. move => Heq; injection Heq; move => Hdm; rewrite -Hdm Hfdv0//.
    + case Hn : n=> [|m].
      * case Htl : tl => [|tltl].
        {
          rewrite Ha Hn Htl in Hrhs.
          case Hsv : (s == v).
          - rewrite (eqP Hsv) Hfdv0 find_add_eq_z_fm.
            move => Hinj; injection Hinj; move => Heq; rewrite -Heq.
            rewrite find_add_eq_z. move=> Hinj2; by injection Hinj2.
          - case Hfds : (NVM.find (Node s) dm0) => [dsts|].
            + rewrite find_add_eq_z_fm.
              move => Hinj; injection Hinj; move => Heq; rewrite -Heq.
              rewrite find_add_neq_z. rewrite Hfdv0//.
              move => H; injection H; move => Hnsv; rewrite Hnsv eq_refl// in Hsv.
            + rewrite find_add_eq_z_fm.
              move => Hinj; injection Hinj; move => Heq; rewrite -Heq.
              rewrite find_add_neq_z. rewrite Hfdv0//.
              move => H; injection H; move => Hnsv; rewrite Hnsv eq_refl// in Hsv.
        }
      * rewrite Hfdc0. move => Heq; injection Heq; move => Hdm; rewrite -Hdm Hfdv0//.
  -rewrite Hfdc0. move => Heq; injection Heq; move => Hdm; rewrite -Hdm Hfdv0//.
Qed.

(*Lemma add_edge_of_c_nn_nn : forall c c' v fm dm0 dm,
    PVM.find (c) fm = Some dm0 ->
    NVM.find (Node v) dm0 = None ->
    ((lhs_var1 c' == c) && (rhs_terms1 c' == [(1, v)])) = false ->
    PVM.find (c) (add_edge_of_c c' fm) = Some dm ->
    NVM.find (Node v) dm = None.
Proof.
Admitted.
  
Lemma add_edge_of_c_s_same : forall cst csh c fm  ,
    PVM.find (lhs_var1 c) (add_edge_of_c csh (add_edge_of_c_s cst fm)) = 
      PVM.find (lhs_var1 c) (add_edge_of_c_s cst (add_edge_of_c csh fm)).
Proof.
Admitted.

Lemma add_edge_of_cs_c_s_same : forall cs fm,
  add_edge_of_c_s cs fm = add_edge_of_cs' cs fm.
Proof.
Admitted.*)

Lemma nvm_add_find_some : forall (a : NodeVar.t) (w : Z) (dst : NVM.t Z) (n : NodeVar.t) v,
  NVM.find n dst = Some v -> exists v', NVM.find n (NVM.add a w dst) = Some v'.
Proof.
  move => a w dst n v H.
  case: (NodeVar.eq_dec n a) => [Heq|Hne].
  - rewrite (node_eq_leibniz _ _ Heq). rewrite find_add_eq_z. by exists w.
  - have Hnea : n <> a.
      { move => He. apply Hne. rewrite He. exact (NodeVar.eq_refl a). }
    rewrite find_add_neq_z //.

    by exists v.
Qed.
Lemma add_edge_of_c_find_some_mono : forall c c' fm ml ml' n v,
    PVM.find c fm = Some ml ->
    NVM.find n ml = Some v ->
    PVM.find c (add_edge_of_c c' fm) = Some ml' ->
    NVM.find n ml' <> None.
Proof.
  move => c c' fm ml ml' n v Hfdc0 Hfdv0 Hfdc.
  rewrite /add_edge_of_c in Hfdc.
  case Hfc' : (PVM.find (lhs_var1 c') fm) => [dst_map|]; last first.
  - rewrite Hfc' in Hfdc. rewrite Hfdc0 in Hfdc.
    by injection Hfdc => <-; rewrite Hfdv0.
  rewrite Hfc' in Hfdc.
  case Hrhs : (rhs_terms1 c') => [|a tl].
  { (* rhs = [] : Zero edge *)
    rewrite Hrhs in Hfdc. clear Hrhs.
    rewrite /= in Hfdc.
    case Hz0 : (NVM.find Zero dst_map) => [dist0|] in Hfdc.
    { case Heq : (c == lhs_var1 c').
      - rewrite (eqP Heq) in Hfdc. rewrite find_add_eq_z_fm in Hfdc.
        injection Hfdc => Hml'. rewrite -Hml'.
        rewrite (eqP Heq) in Hfdc0. rewrite Hfdc0 in Hfc'.
        injection Hfc' => Hmle. move: Hfdv0. rewrite Hmle. move => Hfdv0.
        move: (@nvm_add_find_some Zero (Z.max dist0 (rhs_const1 c')) dst_map n v Hfdv0) => [v2 Hv2].
        by rewrite Hv2.
      - have Hn : c <> lhs_var1 c'.
        { move => Hc. rewrite Hc eq_refl in Heq. done. }
        move: Hfdc. rewrite (find_add_neq_z_fm _ _ Hn). move => Hfdc.
        rewrite Hfdc0 in Hfdc.
        by injection Hfdc => <-; rewrite Hfdv0. }
    { case Heq : (c == lhs_var1 c').
      - rewrite (eqP Heq) in Hfdc. rewrite find_add_eq_z_fm in Hfdc.
        injection Hfdc => Hml'. rewrite -Hml'.
        rewrite (eqP Heq) in Hfdc0. rewrite Hfdc0 in Hfc'.
        injection Hfc' => Hmle. move: Hfdv0. rewrite Hmle. move => Hfdv0.
        move: (@nvm_add_find_some Zero (rhs_const1 c') dst_map n v Hfdv0) => [v2 Hv2].
        by rewrite Hv2.
      - have Hn : c <> lhs_var1 c'.
        { move => Hc. rewrite Hc eq_refl in Heq. done. }
        move: Hfdc. rewrite (find_add_neq_z_fm _ _ Hn). move => Hfdc.
        rewrite Hfdc0 in Hfdc.
        by injection Hfdc => <-; rewrite Hfdv0. } }
  { (* rhs = a :: tl *)
    rewrite Hrhs in Hfdc. clear Hrhs.
    destruct a as [na va].
    destruct tl as [|b tl2].
    { destruct na as [|na1].
      { rewrite /= in Hfdc. rewrite Hfdc0 in Hfdc.
        by injection Hfdc => <-; rewrite Hfdv0. }
      destruct na1 as [|na2].
      { (* na = 1 *)
        rewrite /= in Hfdc.
        case Hv : (NVM.find (Node va) dst_map) => [dist|] in Hfdc.
        { case Heq : (c == lhs_var1 c').
          - rewrite (eqP Heq) in Hfdc. rewrite find_add_eq_z_fm in Hfdc.
            injection Hfdc => Hml'. rewrite -Hml'.
            rewrite (eqP Heq) in Hfdc0. rewrite Hfdc0 in Hfc'.
            injection Hfc' => Hmle. move: Hfdv0. rewrite Hmle. move => Hfdv0.
            move: (@nvm_add_find_some (Node va) (Z.max dist (rhs_const1 c')) dst_map n v Hfdv0) => [v2 Hv2].
            by rewrite Hv2.
          - have Hn : c <> lhs_var1 c'.
            { move => Hc. rewrite Hc eq_refl in Heq. done. }
            move: Hfdc. rewrite (find_add_neq_z_fm _ _ Hn). move => Hfdc.
            rewrite Hfdc0 in Hfdc.
            by injection Hfdc => <-; rewrite Hfdv0. }
        { case Heq : (c == lhs_var1 c').
          - rewrite (eqP Heq) in Hfdc. rewrite find_add_eq_z_fm in Hfdc.
            injection Hfdc => Hml'. rewrite -Hml'.
            rewrite (eqP Heq) in Hfdc0. rewrite Hfdc0 in Hfc'.
            injection Hfc' => Hmle. move: Hfdv0. rewrite Hmle. move => Hfdv0.
            move: (@nvm_add_find_some (Node va) (rhs_const1 c') dst_map n v Hfdv0) => [v2 Hv2].
            by rewrite Hv2.
          - have Hn : c <> lhs_var1 c'.
            { move => Hc. rewrite Hc eq_refl in Heq. done. }
            move: Hfdc. rewrite (find_add_neq_z_fm _ _ Hn). move => Hfdc.
            rewrite Hfdc0 in Hfdc.
            by injection Hfdc => <-; rewrite Hfdv0. } }
      (* na >= 2 *)
      rewrite /= in Hfdc. rewrite Hfdc0 in Hfdc.
      by injection Hfdc => <-; rewrite Hfdv0. }
    (* >= 2 terms *)
    destruct na as [|na1].
    rewrite /= in Hfdc. rewrite Hfdc0 in Hfdc.
    by injection Hfdc => <-; rewrite Hfdv0.
    destruct na1 as [|na2].
    rewrite /= in Hfdc. rewrite Hfdc0 in Hfdc.
    by injection Hfdc => <-; rewrite Hfdv0.
    rewrite /= in Hfdc. rewrite Hfdc0 in Hfdc.
    by injection Hfdc => <-; rewrite Hfdv0.
}

Qed.


Lemma add_edge_of_c_s_find_edge' : forall cs c fm ml0 ml v ,
    PVM.find c fm = Some ml0 ->
    ~ NVM.find (Node v) ml0 = None ->
    PVM.find c (add_edge_of_c_s cs fm) = Some ml ->
    ~ NVM.find (Node v) ml = None.
Proof.
  elim => [|csh cst IHm] c fm ml0 ml v Hfdc0 Hfdv0 Hfdc.
  - rewrite /= in Hfdc. rewrite Hfdc0 in Hfdc.
    by injection Hfdc => e; rewrite -e.
  rewrite /= in Hfdc.
  case Hf0 : (NVM.find (Node v) ml0) => [v0|]; last by case: (Hfdv0 Hf0).
  case Hstep : (PVM.find c (add_edge_of_c_s cst fm)) => [ml1|].
  - case Hfd1 : (NVM.find (Node v) ml1) => [dst1|].
    + exact (@add_edge_of_c_find_some_mono c csh (add_edge_of_c_s cst fm) ml1 ml (Node v) dst1 Hstep Hfd1 Hfdc).
    + move: (IHm c fm ml0 ml1 v Hfdc0 Hfdv0 Hstep). by rewrite Hfd1.
  + have Hnn : ~ PVM.find c fm = None by rewrite Hfdc0.
    move: (add_edge_of_c_s_find_map cst c fm Hnn). by rewrite Hstep.
Qed.

Lemma add_edge_of_c_s_nn_max0 : forall c fm ml0 s cst ml1,
    PVM.find c fm = Some ml0 ->
    NVM.find (Node s) ml0 = None ->
    PVM.find c (add_edge_of_c_s cst fm) = Some ml1 ->
    NVM.find (Node s) ml1 = None ->
    max_const1 c s cst = Z0.
Proof.
  move => c fm ml0 s cst ml1 Hfdc0 Hfds0 Hfdc Hfds.
  elim: cst ml1 Hfdc Hfds => [|csh cst IHm] ml1 Hfdc Hfds.
  - by rewrite /=.
  - (* cons *)
  rewrite /max_const1.
  case Hc2s : ((lhs_var1 csh == c) && (rhs_terms1 csh == [(1, s)])).
  - move/andP : Hc2s => [/eqP Hceq /eqP Hseq].
    exfalso.
    have Hnn : ~ PVM.find c fm = None by rewrite Hfdc0.
    move : (add_edge_of_c_s_find_map cst c fm Hnn).
    have Hnn2 : ~ PVM.find c (add_edge_of_c_s cst fm) = None.
      by move: (add_edge_of_c_s_find_map cst c fm Hnn); rewrite /=.
    rewrite -Hceq in Hnn2 Hfdc.
    move : (@add_edge_of_c_find_edge'' csh (add_edge_of_c_s cst fm) s Hseq Hnn2 ml1 Hfdc).
    by rewrite Hfds.
  - rewrite /max_const1.
    case Hst : (PVM.find c (add_edge_of_c_s cst fm)) => [ml1'|].
    + case Hfds1 : (NVM.find (Node s) ml1') => [dst1|].
      * move : (@add_edge_of_c_sm_max_diff c csh s (add_edge_of_c_s cst fm) ml1' dst1 ml1 Hst Hfds1 Hc2s Hfdc) => H1.
        rewrite H1 in Hfds. by discriminate Hfds.
      * exact (IHm ml1' Hst Hfds1).
      
    + have Hnn : ~ PVM.find c fm = None by rewrite Hfdc0.
      move : (add_edge_of_c_s_find_map cst c fm Hnn). by rewrite Hst.
Qed.
  
(*Lemma add_edge_of_c_s_correct2 : forall cs c s fm ml0 ml dst,
    PVM.find c fm = Some ml0 ->
    NVM.find (Node s) ml0 = None ->
    PVM.find c (add_edge_of_c_s cs fm) = Some ml ->
    NVM.find (Node s) ml = Some dst ->
    Z.of_nat (Z.to_nat dst) = (max_const1 c s cs).
Proof.
  elim => [|csh cst IHm] c s fm ml0 ml dst.
  - rewrite /=. move => Hfdc0 Hfds0. rewrite Hfdc0; move => Hinj; injection Hinj; move => Heq.
    rewrite -Heq Hfds0//.
  - rewrite /=. move => Hfdc0 Hfds0 Hfdc Hfds.
    case Hfdc1 : (PVM.find c (add_edge_of_c_s cst fm)) => [ml1|].
    + case Hfds1 : (NVM.find (Node s) ml1) => [dst1|].
      * case Hc2s : ((lhs_var1 csh == c) && (rhs_terms1 csh == [(1, s)])).
        { move/andP : Hc2s => [/eqP Hceq /eqP Hseq].
          move : (add_edge_of_c_sm_max_same csh (add_edge_of_c_s cst fm) Hfdc1 Hfds1 Hceq Hseq Hfdc) => Hfds'.
          rewrite Hfds in Hfds'; injection Hfds'; move => Hdsteq; rewrite Hdsteq.
          move : (IHm c s fm ml0 ml1 dst1 Hfdc0 Hfds0 Hfdc1 Hfds1) => Hmax1.
          symmetry. rewrite {1}Z.max_comm.
          rewrite -Hmax1. 
          rewrite 2!ZifyInst.of_nat_to_nat_eq. lia.
        }
        { apply IHm with fm ml0 ml1; try done.
          move : (add_edge_of_c_sm_max_diff c csh s (add_edge_of_c_s cst fm) Hfdc1 Hfds1 Hc2s Hfdc) => Hfds1'.
          rewrite Hfds in Hfds1'; injection Hfds1'; move => Heq; rewrite Heq//.
        }
      * case Hc2s : ((lhs_var1 csh == c) && (rhs_terms1 csh == [(1, s)])).
        { move/andP : Hc2s => [/eqP Hceq /eqP Hseq].
          rewrite -Hceq in Hfdc0 Hfdc1 Hfdc *.
          move : (add_edge_of_c_nn_max csh s (add_edge_of_c_s cst fm) Hfdc1 Hfds1 Hfdc Hfds) => Hfds'.
          
          rewrite (add_edge_of_c_s_nn_max0 (lhs_var1 csh) fm  s cst Hfdc0 Hfds0 Hfdc1 Hfds1).
          rewrite ZifyInst.of_nat_to_nat_eq Hfds' Z.max_comm//. 
        }
        {
          rewrite (add_edge_of_c_nn_nn c csh s (add_edge_of_c_s cst fm) Hfdc1 Hfds1 Hc2s Hfdc)// in Hfds.
        }
    + have Hfdcnn : PVM.find c fm <> None by rewrite Hfdc0.
      move : (add_edge_of_c_s_find_map cst c fm Hfdcnn). rewrite Hfdc1//.
Qed.*)

Lemma add_edge_of_c_s_correct1 : forall cs c s fm ml0 ml dst0 dst,
    PVM.find c fm = Some ml0 ->
    NVM.find (Node s) ml0 = Some dst0 ->
    PVM.find c (add_edge_of_c_s cs fm) = Some ml ->
    NVM.find (Node s) ml = Some dst ->
    Z.of_nat (Z.to_nat dst) = Z.max dst0 (max_const1 c s cs).
Proof.
  elim => [|csh cst IHm] c s fm ml0 ml dst0 dst.
  - rewrite /= Z.max_comm -ZifyInst.of_nat_to_nat_eq.
    move => Hfdc0 Hfds0 Hfdc .
    rewrite Hfdc0 in Hfdc; injection Hfdc; move => Heq; rewrite -Heq Hfds0.
    move => Hdst; injection Hdst; move => Heqd; rewrite Heqd//.
  - rewrite /=.
    move => Hfdc0 Hfds0 Hfdc Hfds.
    case Hfdc1 : (PVM.find c (add_edge_of_c_s cst fm)) => [ml1|].
    + case Hfds1 : (NVM.find (Node s) ml1) => [dst1|].
      * case Hc2s : ((lhs_var1 csh == c) && (rhs_terms1 csh == [(1, s)])).
        { move/andP : Hc2s => [/eqP Hceq /eqP Hseq].
          move : (add_edge_of_c_sm_max_same csh (add_edge_of_c_s cst fm) Hfdc1 Hfds1 Hceq Hseq Hfdc) => Hfds'.
          rewrite Hfds in Hfds'; injection Hfds'; move => Hdsteq; rewrite Hdsteq.
          move : (IHm c s fm ml0 ml1 dst0 dst1 Hfdc0 Hfds0 Hfdc1 Hfds1) => Hmax1.
          symmetry. rewrite {1}Z.max_comm -Z.max_assoc. rewrite Z.max_comm in Hmax1.
          rewrite -Hmax1. 
          rewrite 2!ZifyInst.of_nat_to_nat_eq. lia.
        }
        { apply IHm with fm ml0 ml1; try done.
          move : (add_edge_of_c_sm_max_diff c csh s (add_edge_of_c_s cst fm) Hfdc1 Hfds1 Hc2s Hfdc) => Hfds1'.
          rewrite Hfds in Hfds1'; injection Hfds1'; move => Heq; rewrite Heq//.
        }
      * have Hnfdnn : (NVM.find (Node s) ml0 <> None ) by rewrite Hfds0.
        move : (add_edge_of_c_s_find_edge' cst c fm s Hfdc0 Hnfdnn Hfdc1).
        rewrite Hfds1//.
    + have Hfdnn : (~PVM.find c fm = None) by rewrite Hfdc0//.
      move : (add_edge_of_c_s_find_map cst c fm Hfdnn).
      rewrite Hfdc1//.
Qed.

(*Lemma add_edge_of_c_s_correct_map0 : forall cs c s nds ml0 ml dst,
    PVM.find c (map0 nds (PVM.empty (NVM.t Z.t))) = Some ml0 ->
    PVM.find c (add_edge_of_c_s cs (map0 nds (PVM.empty (NVM.t Z.t)))) = Some ml ->
    NVM.find (Node s) ml = Some dst ->
    Z.of_nat (Z.to_nat dst) = Z.max 0 (max_const1 c s cs).
Proof.
  move => cs c s nds ml0 ml dst Hfdc0 Hfdc Hfds.
  case Hfds0 : ( NVM.find (Node s) ml0) => [dst0|].
    + move : (add_edge_of_c_s_correct1 cs c s (map0 nds (PVM.empty (NVM.t Z.t))) Hfdc0 Hfds0 Hfdc Hfds) => Haux.
      case Hcs : (s == c).
      * rewrite (eqP Hcs) in Hfds Hfds0.
        move : (map0_correct nds c Hfdc0 Hfds0) => Hdst0.
        rewrite Hdst0 // in Haux.
      * move : (map0_correct_nn nds c s Hcs Hfdc0). rewrite Hfds0//.
    + move : (add_edge_of_c_s_correct2 cs c s (map0 nds (PVM.empty (NVM.t Z.t))) Hfdc0 Hfds0 Hfdc Hfds). lia.
Qed.

Lemma init_dist_map_correct1 : forall nds d cs ml0 ml1,
    PVM.find d (map0 nds (PVM.empty (NVM.t Z.t))) = Some ml0 ->
    PVM.find d (init_dist_map' nds cs) = Some ml1 ->
    forall s dst,
      NVM.find (Node s) ml1 = Some dst ->
      Z.of_nat (Z.to_nat dst) = Z.max 0 (max_const1 d s cs).
Proof.
  move => nds d cs ml0 ml1 Hfdd0 Hfdd s dst Hfds0. move: Hfdd.
  rewrite /init_dist_map'-add_edge_of_cs_c_s_same. move => Hfdd.
  exact : (@add_edge_of_c_s_correct_map0 cs d s nds ml0 ml1 dst Hfdd0 Hfdd Hfds0).
Qed.*)


  
(* Lemma add_edge_of_c_s_correct1 : forall cs c s fm ml0 ml dst0 dst, *)
(*     In c cs -> (rhs_terms1 c) = [(1,s)] -> *)
(*     PVM.find (lhs_var1 c) fm = Some ml0 -> *)
(*     NVM.find (Node s) ml0 = Some dst0 -> *)
(*     PVM.find (lhs_var1 c) (add_edge_of_c_s cs fm) = Some ml -> *)
(*     NVM.find (Node s) ml = Some dst -> *)
(*     dst = Z.max dst0 (max_const1 (lhs_var1 c) s cs). *)
(* Proof. *)
(*   elim => [|csh cst IHm] c s fm ml0 ml dst0 dst; first done. *)
(*   move => Hin Hrhst Hfdc0 Hfds0. *)
(*   (* have Hfdnn : (~PVM.find (lhs_var1 c) fm = None) by rewrite Hfdc0//. *) *)
(*   (* move : (@add_edge_of_c_s_find_edge (csh::cst) c fm ml s Hin Hrhst Hfdnn).  *) *)
(*   rewrite /=. move => Hadd.  *)
(*   rewrite /=in Hin. move: Hin => [Heq|Hin]. *)
(*   - rewrite Heq  in Hadd *. rewrite Hrhst 2!eq_refl/=.  *)
(*     have Hfdnn : (~PVM.find (lhs_var1 c) fm = None) by rewrite Hfdc0//. *)
(*     have Hnfdnn : (NVM.find (Node s) ml0 <> None ) by rewrite Hfds0. *)
(*     case Hfdc1 : (PVM.find (lhs_var1 c) (add_edge_of_c_s cst fm)) => [ml1|]. *)
(*     + case Hfds1 : (NVM.find (Node s) ml1) => [dst1|]. *)
(*       * move : (@add_edge_of_c_sm_max c s (add_edge_of_c_s cst fm) ml1 dst1 ml Hrhst Hfdc1 Hfds1 Hadd) => Haux. *)
(*         generalize Hfdc1. *)
(*         rewrite add_edge_of_cs_c_s_same => Hfdc1'. *)
(*         move : (@add_edge_of_cs_correct cst (lhs_var1 c) fm ml0 ml1 Hfdc0 Hfdc1' (Node s) dst0 dst1 Hfds0 Hfds1) => Hle01. *)
(*         rewrite Haux. move => Hinj; injection Hinj; move => Heq2; rewrite -Heq2. *)
(*         lia. *)
(*       * move: (@add_edge_of_c_s_find_edge' cst c fm ml0 ml1 s Hrhst Hfdc0 Hnfdnn Hfdc1). *)
(*         rewrite Hfds1//. *)
(*     + move : (add_edge_of_c_s_find_map cst c fm Hfdnn). *)
(*       rewrite Hfdc1//. *)
(*   - have Hfdnn : (~PVM.find (lhs_var1 c) fm = None) by rewrite Hfdc0//. *)
(*     have Hnfdnn : (NVM.find (Node s) ml0 <> None ) by rewrite Hfds0. *)
(*     case Hfdc1 : (PVM.find (lhs_var1 c) (add_edge_of_c_s cst fm)) => [ml1|]. *)
(*     + case Hfds1 : (NVM.find (Node s) ml1) => [dst1|]. *)
(*       move : (IHm c s fm ml0 ml1 dst0 dst1 Hin Hrhst Hfdc0 Hfds0 Hfdc1 Hfds1). *)
(*       move => Hdst1. *)
(*       move : (@add_edge_of_c_sm_max).  *)
(* Admitted. *)

(*Lemma add_edge_of_cs_correct1 : forall cs c s fm ml0 ml dst0 dst,
    PVM.find (lhs_var1 c) fm = Some ml0 ->
    NVM.find (Node s) ml0 = Some dst0 ->
    PVM.find (lhs_var1 c) (add_edge_of_cs' cs fm) = Some ml ->
    NVM.find (Node s) ml = Some dst ->
    Z.le (rhs_const1 c) dst.
Proof.
(*   move => cs c s fm ml0 ml dst0 dst. *)
(*   rewrite -add_edge_of_cs_c_s_same. move => Hfdc0 Hfds0 Hfdc Hfds. *)
(*   move : (add_edge_of_c_s_correct1 cs (lhs_var1 c) s fm Hfdc0 Hfds0 Hfdc Hfds). *)
  
(* Qed. *)
Admitted.*)
  
Lemma new_dst_map_aux_correct :
  forall dm n s d m dst0 dst1,
    NVM.find n dm = Some dst0 ->
    NVM.find n (new_dst_map_aux dm n s d m) = Some dst1 ->
    Z.le dst0 dst1.
Proof.
  move => dm n s d m dst0 dst1 Hfd0.
  rewrite /new_dst_map_aux.
  rewrite Hfd0.
  case Hgwd : (get_weight d (Node s) m) => [wd|].
  - case Hgws : (get_weight s n m) => [ws|].
    + rewrite find_add_eq_z.
      move => Heqmax; injection Heqmax; move => Heq.
      rewrite -Heq. apply Z.le_max_l.
    + move => Hfd1; rewrite Hfd0 in Hfd1; injection Hfd1; move => Heq.
      lia.
  - move => Hfd1; rewrite Hfd0 in Hfd1; injection Hfd1; move => Heq.
    lia.
Qed.

Lemma new_dst_map_aux_correct1 :
  forall dm j k i m dst0 dstn dik dkj,
    get_weight i (Node k) m = Some dik ->
    get_weight k j m = Some dkj ->
    NVM.find j dm = Some dst0 ->
    NVM.find j (new_dst_map_aux dm j k i m) = Some dstn ->
    dstn = Z.max (Z.add dik dkj) dst0.
Proof.
  move => dm n s d m dst0 dstn dik dkj Hgwik Hgwkj Hfdn0 .
  rewrite /new_dst_map_aux. 
  rewrite Hfdn0 Hgwik Hgwkj find_add_eq_z.
  move => Hinj; injection Hinj; move => Heq; rewrite -Heq.
  lia.
Qed.

Lemma new_dst_map_aux_correct2 :
  forall dm j k i m dstn dik dkj,
    get_weight i (Node k) m = Some dik ->
    get_weight k j m = Some dkj ->
    NVM.find j dm = None ->
    NVM.find j (new_dst_map_aux dm j k i m) = Some dstn ->
    dstn = (Z.add dik dkj) .
Proof.
  move => dm n s d m dstn dik dkj Hgwik Hgwkj Hfdn.  
  rewrite /new_dst_map_aux. 
  rewrite Hfdn Hgwik Hgwkj find_add_eq_z.
  move => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
Qed.

Instance Symmetric_neq {A : Type} : Symmetric (fun x y : A => x <> y).
Proof.
  intros x y Hneq Heq.
  apply Hneq.                  (* 目标：x = y → False *)
  symmetry in Heq; assumption. (* 将 y=x 转为 x=y *)
Qed.

Lemma new_dst_map_aux_correct3 :
  forall dm j k i m x dst0,
    NVM.find j dm = Some dst0 ->
    (x <> j)->
    NVM.find j (new_dst_map_aux dm x k i m) = Some dst0.
Proof.
  move => dm j k i m x dstn Hfdj0 Hfdn.  
  rewrite /new_dst_map_aux. 
  case Hfdn1 : (NVM.find x dm) => [dstn1|].
  - case Hgwik : (get_weight i (Node k) m) => [wik|].
    case Hgwkx : (get_weight k x m ) => [wkx|]; last done.
    rewrite find_add_neq_z//; last by symmetry.
    rewrite Hfdj0//.
  - case Hgwik : (get_weight i (Node k) m) => [wik|].
    case Hgwkx : (get_weight k x m ) => [wkx|]; last done.
    rewrite find_add_neq_z//; last by symmetry.
    rewrite Hfdj0//.
Qed.

(* Lemma new_dst_map_aux_correct3 : *)
(*   forall dm j k i m x dst0 dik dkj, *)
(*     NVM.find j dm = Some dst0 -> *)
(*     get_weight i (Node k) m = Some dik -> *)
(*     get_weight k j m = Some dkj -> *)
(*     (x <> j)-> *)
(*     NVM.find j (new_dst_map_aux dm x k i m) = Some dst0. *)
(* Proof. *)
(*   move => dm j k i m x dstn dik dkj Hfdj0 Hgwik Hgwkj Hfdn.   *)
(*   rewrite /new_dst_map_aux.  *)
(*   case Hfdn1 : (NVM.find x dm) => [dstn1|]. *)
(*   - rewrite Hgwik. *)
(*     case Hgwkx : (get_weight k x m ) => [wkx|]; last done. *)
(*     rewrite find_add_neq_z; last by symmetry. *)
(*     rewrite Hfdj0//. *)
(*   - rewrite Hgwik. *)
(*     case Hgwkx : (get_weight k x m ) => [wkx|]; last done. *)
(*     rewrite find_add_neq_z; last by symmetry. *)
(*     rewrite Hfdj0//. *)
(* Qed. *)

Lemma new_dst_map_aux_correct4 :
  forall dm j k i m x (* dik dkj *),
    NVM.find j dm = None ->
    (j <> x)->
    NVM.find j (new_dst_map_aux dm x k i m) = None.
Proof.
  move => dm j k i m x (* dik dkj Hgwik Hgwkj *) Hfdj Hneq.  
  rewrite /new_dst_map_aux. 
  case Hfdx : (NVM.find x dm) => [dstn0|].
  - case Hgwik : (get_weight i (Node k) m) => [wik|].
    + case Hgwkx : (get_weight k x m) => [wkx|].
      * rewrite find_add_neq_z; first rewrite Hfdj//; last done.
      * rewrite Hfdj//.
    + rewrite Hfdj//.
  - case Hgwik : (get_weight i (Node k) m) => [wik|].
    + case Hgwkx : (get_weight k x m) => [wkx|].
      * rewrite find_add_neq_z; first rewrite Hfdj//; last done.
      * rewrite Hfdj//.
    + rewrite Hfdj//.
Qed.

Lemma new_dst_map_aux_nn :
  forall dm j k i m x dst,
    NVM.find j dm = Some dst ->
    ~ (NVM.find j (new_dst_map_aux dm x k i m) = None).
Proof.
  move => dm j k i m x dst Hfdj0.
  rewrite /new_dst_map_aux.
  case Hfdx0 : (NVM.find x dm) => [dstx|].
  - case Hgwik : (get_weight i (Node k) m) => [wik|].
    + case Hgwkx : (get_weight k x m) => [wkx|].
      move : Hfdj0 Hfdx0 Hgwkx.
      * case Hj : j => [|vj]; case Hx : x => [|vx]; move => Hfdj0 Hfdx0 Hgwkx.
        rewrite find_add_eq_z//.
        rewrite find_add_neq_z; first rewrite Hfdj0//; last done.
        rewrite find_add_neq_z; first rewrite Hfdj0//; last done.
        case Hjx : (vj == vx).
        rewrite (eqP Hjx) find_add_eq_z//.
        rewrite find_add_neq_z; first rewrite Hfdj0//.
        move => Hinj; injection Hinj; move => Heq; rewrite -Heq eq_refl // in Hjx.
      * rewrite Hfdj0//.
    + rewrite Hfdj0//.
  - case Hgwik : (get_weight i (Node k) m) => [wik|].
    + case Hgwkx : (get_weight k x m) => [wkx|].
      move : Hfdj0 Hfdx0 Hgwkx.
      * case Hj : j => [|vj]; case Hx : x => [|vx]; move => Hfdj0 Hfdx0 Hgwkx.
        rewrite find_add_eq_z//.
        rewrite find_add_neq_z; first rewrite Hfdj0//; last done.
        rewrite find_add_neq_z; first rewrite Hfdj0//; last done.
        case Hjx : (vj == vx).
        rewrite (eqP Hjx) find_add_eq_z//.
        rewrite find_add_neq_z; first rewrite Hfdj0//.
        move => Hinj; injection Hinj; move => Heq; rewrite -Heq eq_refl // in Hjx.
      * rewrite Hfdj0//.
    + rewrite Hfdj0//.
Qed.

Lemma new_dst_map_nn :
  forall nds dm j k i m dst,
    NVM.find j dm = Some dst ->
    ~ (NVM.find j (new_dst_map nds dm k i m) = None).
Proof.
  elim => [|nhd ntl IHm] dm j k i m dst Hfdj0; rewrite/=.
  - rewrite Hfdj0//.
  - case Hfdj1 : (NVM.find j (new_dst_map ntl dm k i m))=> [dst1|].
    exact : (new_dst_map_aux_nn (new_dst_map ntl dm k i m) j k i m nhd Hfdj1).
    move : (IHm dm j k i m dst Hfdj0). rewrite Hfdj1//.
Qed.

Lemma in_notin_neq_p : forall l (a b: ProdVar.t) ,
    In a l -> ~ In b l -> a <> b.
Proof.
  elim => [|hd tl IHm]; rewrite /=//.
  move => a b [Heq |Hin] Hnin; apply Decidable.not_or in Hnin; move : Hnin => [Hneq Hnin].
  rewrite Heq // in Hneq.
  apply IHm; try done.
Qed.

Lemma in_notin_neq_n : forall l (a b: node) ,
    In a l -> ~ In b l -> a <> b.
Proof.
  elim => [|hd tl IHm]; rewrite /=//.
  move => a b [Heq |Hin] Hnin; apply Decidable.not_or in Hnin; move : Hnin => [Hneq Hnin].
  rewrite Heq // in Hneq.
  apply IHm; try done.
Qed.

Lemma new_dst_map_correct2 :
  forall nds dm j k i m dst0 dstn,
    ~ In j nds ->
    NVM.find j dm = Some dst0 ->
    NVM.find j (new_dst_map nds dm k i m) = Some dstn ->
    dst0 = dstn.
Proof.
  elim => [|nhd ntl IHm] dm j k i m d0 dn; rewrite /=.
  - move => _ Hfdj0 ; rewrite Hfdj0; move => Hinj; by injection Hinj.
  - move => Hnin Hfd0 Hfdn. apply Decidable.not_or in Hnin.
    move : Hnin => [Hneq Hnin].
    case Hfdj1 : (NVM.find j (new_dst_map ntl dm k i m)) => [d1|].
    + move : (@new_dst_map_aux_correct3 (new_dst_map ntl dm k i m) j k i m nhd d1 Hfdj1 Hneq).
      rewrite Hfdn; move => Hinj; injection Hinj; move => Heq1n.
      move : (@IHm dm j k i m d0 d1 Hnin Hfd0 Hfdj1); rewrite -Heq1n//.
    + move : (@new_dst_map_nn ntl dm j k i m d0 Hfd0); rewrite Hfdj1//.
Qed.    

Lemma new_dst_map_correct1 :
  forall nds dm j k i m dst0 dstn dik dkj,
    In j nds -> NoDup nds ->
    NVM.find j dm = Some dst0 ->
    NVM.find j (new_dst_map nds dm k i m) = Some dstn ->
    get_weight i (Node k) m = Some dik ->
    get_weight k j m = Some dkj ->
    dstn = Z.max dst0 (Z.add dik dkj).
Proof.
  elim => [|nhd ntl IHm] dm j k i m dst0 dstn dik dkj; first done.
  rewrite /=.
  move => [Heq|Hin] Hnd Hfdj0 Hfdjn Hgwik Hgwkj.
  -rewrite Heq in Hnd Hfdjn.
   rewrite NoDup_cons_iff in Hnd; move : Hnd => [Hnin Hnd].
   case Hfdj1 : (NVM.find j (new_dst_map ntl dm k i m)) => [dst1|].
   + move : (new_dst_map_aux_correct1 (new_dst_map ntl dm k i m) j k i m Hgwik Hgwkj Hfdj1 Hfdjn).
     move : (new_dst_map_correct2 ntl dm j k i m Hnin Hfdj0 Hfdj1) => Hd01; rewrite Hd01 Z.max_comm//.
   + move : (new_dst_map_nn ntl dm j k i m Hfdj0); rewrite Hfdj1//.
  - rewrite NoDup_cons_iff in Hnd; move : Hnd => [Hnin Hnd].
    case Hfdj1 : (NVM.find j (new_dst_map ntl dm k i m)) => [dst1|].
    + move : (not_eq_sym (in_notin_neq_n ntl Hin Hnin)) => Hneq. 
      move : (@new_dst_map_aux_correct3 (new_dst_map ntl dm k i m) j k i m nhd dst1 Hfdj1 Hneq).
      rewrite Hfdjn; move => Hinj; injection Hinj; move => Heq; rewrite Heq.
      exact : (IHm dm j k i m dst0 dst1 dik dkj Hin Hnd Hfdj0 Hfdj1 Hgwik Hgwkj).
    + move : (new_dst_map_nn ntl dm j k i m Hfdj0); rewrite Hfdj1//.
Qed.

(* Lemma new_dst_map_correct1 : *)
(*   forall nds dm j k i m dst0 dstn dik dkj, *)
(*     NVM.find j dm = Some dst0 -> *)
(*     NVM.find j (new_dst_map nds dm k i m) = Some dstn -> *)
(*     get_weight i (Node k) m = Some dik -> *)
(*     get_weight k j m = Some dkj -> *)
(*     Z.le (Z.add dik dkj) dst0 -> *)
(*     dstn = Z.max dst0 (Z.add dik dkj). *)
(* Proof. *)
(*   elim => [|nhd ntl IHm] dm j k i m dst0 dstn dik dkj. *)
(*   - rewrite /=. move => Hfdj0; rewrite Hfdj0; move => Hinj1; injection Hinj1; move => Heq1; rewrite -Heq1.  *)
(*     move => Hgwik Hgwkj Hle. Search Z.max. apply Z.max_unicity. lia.  *)
(*   - move => Hfdj0 Hfdj Hgwik Hgwkj. move : Hfdj. rewrite /=.  *)
(*     case Hfdj1 : (NVM.find j (new_dst_map ntl dm k i m)) => [dst1|]. *)
(*     + move : Hfdj0 Hgwkj Hfdj1.  *)
(*       case Hj : j =>[|vj]; case Hnhd : nhd => [|vn]. *)
(*       * move => Hfdj0 Hgwkj Hfdj1 Hfdj Hle. *)
(*         move : (new_dst_map_aux_correct1 (new_dst_map ntl dm k i m) Zero k i m Hgwik Hgwkj Hfdj1 Hfdj). *)
(*         move : (IHm dm Zero  k i m dst0 dst1 dik dkj Hfdj0 Hfdj1 Hgwik Hgwkj Hle) => Haux. *)
(*         move : Hle => _. *)
(*         rewrite Haux. lia. *)
(*       * have Hneq : (nhd <> Zero) by rewrite Hnhd//. *)
(*         move => Hfdj0 Hgwkj Hfdj1 Hfdj Hle. *)
(*         move : (new_dst_map_aux_correct3 (new_dst_map ntl dm k i m)  k i m Hfdj1 Hgwik Hgwkj Hneq ). *)
(*         rewrite Hnhd Hfdj => Hinj; injection Hinj; move => Heq; rewrite Heq. *)
(*         exact : (IHm  dm Zero k i m dst0 dst1 dik dkj Hfdj0 Hfdj1 Hgwik Hgwkj Hle). *)
(*       * have Hneq : (Zero <> Node vj) by done. *)
(*         move => Hfdj0 Hgwkj Hfdj1 Hfdj Hle. *)
(*         move : (new_dst_map_aux_correct3 (new_dst_map ntl dm k i m)  k i m Hfdj1 Hgwik Hgwkj Hneq ). *)
(*         rewrite Hfdj => Hinj; injection Hinj; move => Heq; rewrite Heq. *)
(*         exact : (IHm  dm (Node vj) k i m dst0 dst1 dik dkj Hfdj0 Hfdj1 Hgwik Hgwkj Hle). *)
(*       * case Hnj : (vj == vn). *)
(*         { *)
(*           rewrite (eqP Hnj). move => Hfdj0 Hgwkj Hfdj1 Hfdj Hle. *)
(*           move : (new_dst_map_aux_correct1 (new_dst_map ntl dm k i m) (Node vn) k i m Hgwik Hgwkj Hfdj1 Hfdj). *)
(*           move : (IHm dm (Node vn) k i m dst0 dst1 dik dkj Hfdj0 Hfdj1 Hgwik Hgwkj Hle) => Haux. *)
(*           move : Hle => _. *)
(*           rewrite Haux. lia. *)
(*         } *)
(*         { *)
(*           have Hneq : (Node vn <> Node vj) by move => Hinj; injection Hinj; move => Heq; rewrite Heq eq_refl// in Hnj. *)
(*           move => Hfdj0 Hgwkj Hfdj1 Hfdj Hle. *)
(*           move : (new_dst_map_aux_correct3 (new_dst_map ntl dm k i m)  k i m Hfdj1 Hgwik Hgwkj Hneq ). *)
(*         rewrite Hfdj => Hinj; injection Hinj; move => Heq; rewrite Heq. *)
(*         exact : (IHm  dm (Node vj) k i m dst0 dst1 dik dkj Hfdj0 Hfdj1 Hgwik Hgwkj Hle). *)
(*         } *)
(*     + move => Hfdjn. *)
(*       move : (new_dst_map_nn ntl dm j k i m Hfdj0). rewrite Hfdj1//. *)
(* Qed. *)

Lemma new_dst_map_aux_nnsm nhd j dm k i m dstn :
  NVM.find j dm = None ->
  NVM.find j (new_dst_map_aux dm nhd k i m) = Some dstn ->
  nhd = j.
Proof.
  move => Hfdj0. rewrite /new_dst_map_aux.
  case Hfdn0: (NVM.find nhd dm) => [dstn0|].
  - case Hgwik : (get_weight i (Node k) m) => [wik|].
    + case Hgwkn : (get_weight k nhd m) => [wkn|].
      * move : Hfdj0 Hfdn0 Hgwkn.
        case Hn : nhd => [|vn]; case Hj : j =>[|vj]; move => Hfdj0; try done.
        rewrite find_add_neq_z; last done; rewrite Hfdj0//.
        rewrite find_add_neq_z; last done; rewrite Hfdj0//.
        case Hjn : (vj == vn).
        rewrite (eqP Hjn)//.
        rewrite find_add_neq_z. rewrite Hfdj0//. move => Hinj; injection Hinj; move => Heq; rewrite Heq eq_refl // in Hjn.
      * rewrite Hfdj0//.
    + rewrite Hfdj0//.
  - case Hgwik : (get_weight i (Node k) m) => [wik|].
    + case Hgwkn : (get_weight k nhd m) => [wkn|].
      * move : Hfdj0 Hfdn0 Hgwkn.
        case Hn : nhd => [|vn]; case Hj : j =>[|vj]; move => Hfdj0; try done.
        rewrite find_add_neq_z; last done; rewrite Hfdj0//.
        rewrite find_add_neq_z; last done; rewrite Hfdj0//.
        case Hjn : (vj == vn).
        rewrite (eqP Hjn)//.
        rewrite find_add_neq_z. rewrite Hfdj0//. move => Hinj; injection Hinj; move => Heq; rewrite Heq eq_refl // in Hjn.
      * rewrite Hfdj0//.
    + rewrite Hfdj0//.
Qed.

Lemma new_dst_map_nnsm : forall nds j dm k i m dstn,
    NVM.find j dm = None ->
    NVM.find j (new_dst_map nds dm k i m) = Some dstn ->
    In j nds.
Proof.
  elim => [|nhd ntl IHm] j dm k i m dstn Hfdj0; rewrite /=.
  - rewrite Hfdj0//.
  - move => Hfdjn.
    case Hfdj1 : (NVM.find j (new_dst_map ntl dm k i m)) => [dst1|].
    + right. move : Hfdj1. apply IHm; done.
    + left.
      exact : (new_dst_map_aux_nnsm nhd j (new_dst_map ntl dm k i m) k i m Hfdj1 Hfdjn).
Qed.

(* Lemma new_dst_map_aux_smsm  j dm k i m dik dkj dst0 dstn : *)
(*   NVM.find j dm = Some dst0 -> *)
(*   get_weight i (Node k) m = Some dik -> *)
(*   get_weight k j m = Some dkj -> *)
(*   NVM.find j (new_dst_map_aux dm j k i m) = Some dstn -> *)
(*   dstn = Z.max dst0 (Z.add dik dkj). *)
(* Proof. *)
(*   rewrite /new_dst_map_aux. move => Hfdj0 Hgw1 Hgw2; rewrite Hfdj0 Hgw1 Hgw2. *)
(*   rewrite find_add_eq_z. move => Hinj; by injection Hinj. *)
(* Qed. *)

Lemma new_dst_map_correct3 :
  forall nds dm j k i m  dstn dik dkj,
    NVM.find j dm = None ->
    NVM.find j (new_dst_map nds dm k i m) = Some dstn ->
    get_weight i (Node k) m = Some dik ->
    get_weight k j m = Some dkj ->
    dstn = (Z.add dik dkj).
Proof.
  move => nds dm j k i m dstn dik dkj Hfdj0 Hfdj1.
  move : (new_dst_map_nnsm nds j dm k i m Hfdj0 Hfdj1) => Hin.
  move : nds dm j k i m dstn dik dkj Hfdj0 Hfdj1 Hin.
  elim => [|nhd ntl IHm] dm j k i m dstn dik dkj Hfdj0 Hfdjn Hin Hgwik Hgwkj; first done.
  rewrite /= in Hin Hfdjn. move : Hin => [Heq|Hin].
  - rewrite Heq in Hfdjn Hgwkj.
    case Hfdj1 : (NVM.find j (new_dst_map ntl dm k i m)) =>[dst1|].
    + move : (new_dst_map_aux_correct1 (new_dst_map ntl dm k i m) j k i m Hgwik Hgwkj Hfdj1 Hfdjn) => Hdstaux.
      rewrite Hdstaux.
      move : (new_dst_map_nnsm ntl j dm k i m Hfdj0 Hfdj1) => Hin.
      move : (IHm dm j k i m dst1 dik dkj Hfdj0 Hfdj1 Hin Hgwik Hgwkj) => Hdstaux2.
      rewrite Hdstaux2. lia.
    + exact : (new_dst_map_aux_correct2 (new_dst_map ntl dm k i m) j k i m Hgwik Hgwkj Hfdj1 Hfdjn).
  - case Hfdj1 : (NVM.find j (new_dst_map ntl dm k i m)) =>[dst1|].
    + move : (IHm dm j k i m dst1 dik dkj Hfdj0 Hfdj1 Hin Hgwik Hgwkj) => Hdstaux2.
      move : Hfdj0 Hgwkj Hfdj1 Hfdjn.
      case Hj : j => [|vj]; case Hn : nhd => [|vn]; move => Hfdj0 Hgwkj Hfdj1 Hfdjn.
      * move : (new_dst_map_aux_correct1 (new_dst_map ntl dm k i m) Zero k i m Hgwik Hgwkj Hfdj1 Hfdjn) => Hdstaux.
        rewrite Hdstaux Hdstaux2. lia.
      * have Hneq : Node vn <> Zero by done.
        move : (@new_dst_map_aux_correct3 (new_dst_map ntl dm k i m) Zero k i m (Node vn) dst1  Hfdj1  Hneq) => Hdstaux.
        rewrite Hfdjn in Hdstaux . injection Hdstaux; move => Heq; rewrite Heq Hdstaux2//.
      * have Hneq : Zero <> Node vj by done.
        move : (@new_dst_map_aux_correct3 (new_dst_map ntl dm k i m) (Node vj) k i m Zero dst1 Hfdj1 Hneq) => Hdstaux.
        rewrite Hfdjn in Hdstaux . injection Hdstaux; move => Heq; rewrite Heq Hdstaux2//.
      * case Hnj : (vn == vj).
        rewrite (eqP Hnj) in Hfdjn.
        move : (new_dst_map_aux_correct1 (new_dst_map ntl dm k i m) (Node vj) k i m Hgwik Hgwkj Hfdj1 Hfdjn) => Hdstaux.
        rewrite Hdstaux Hdstaux2. lia.
        have Hneq : Node vn <> Node vj.
        move => Hinj; injection Hinj; move => Heq; rewrite Heq eq_refl// in Hnj.
        move : (@new_dst_map_aux_correct3 (new_dst_map ntl dm k i m) (Node vj) k i m (Node vn) dst1 Hfdj1 Hneq) => Hdstaux.
        rewrite Hfdjn in Hdstaux . injection Hdstaux; move => Heq; rewrite Heq Hdstaux2//.
  - move : (new_dst_map_aux_nnsm nhd j (new_dst_map ntl dm k i m) k i m Hfdj1 Hfdjn) => Heq.
    rewrite Heq in Hfdjn.
    exact : (new_dst_map_aux_correct2 (new_dst_map ntl dm k i m) j k i m Hgwik Hgwkj Hfdj1 Hfdjn).
Qed.


Fixpoint in_bool_n (a : node) (l : list node) : bool :=
  match l with
  | [] => false
  | Node hd :: tl => match a with
                     | Node n => (hd == n) || in_bool_n a tl
                     | Zero => in_bool_n a tl
                     end
  | Zero :: tl => match a with
                  | Zero => true
                  | _ => in_bool_n a tl
                  end
  end.

Lemma In_in_bool_n : forall a l, in_bool_n a l <-> In a l.
Proof.
intros a l. split; intro H.
- induction l as [|hd tl IH]; simpl in H.
  + discriminate H.
  + destruct a; destruct hd; simpl in H.
    * left. reflexivity.
    * right. apply IH. exact H.
    * right. apply IH. exact H.
    * move/orP: H => [H|H].
      -- left. move/eqP: H => H. rewrite H. reflexivity.
      -- right. apply IH. exact H.
- induction l as [|hd tl IH]; simpl in H.
  + contradiction.
  + destruct a; destruct hd; simpl.
    * destruct H as [H|H].
      ++ unfold is_true. reflexivity.
      ++ unfold is_true. reflexivity.
    * destruct H as [H|H].
      ++ discriminate H.
      ++ apply IH. exact H.
    * destruct H as [H|H].
      ++ discriminate H.
      ++ apply IH. exact H.
    * destruct H as [H|H].
      -- injection H. intro Heq. apply/orP. left.
         rewrite Heq. by rewrite eqxx.
      -- apply/orP. right. apply IH. exact H.
Qed.

Lemma notin_zero_map_node : forall (ntl : list ProdVar.t),
    ~ In Zero (map [eta Node] ntl).
Proof.
  induction ntl as [|hd tl IH]; simpl.
  - auto.
  - intro H. destruct H as [H|H].
    + discriminate H.
    + apply IH. exact H.
Qed.

Lemma notin_node_map_node : forall (j : ProdVar.t) (ntl : list ProdVar.t),
    ~ In j ntl -> ~ In (Node j) (map [eta Node] ntl).
Proof.
  induction ntl as [|hd tl IH]; simpl; intros Hnin H.
  - destruct H.
  - destruct H as [H|H].
    + injection H. intro Heq. subst j.
      apply Hnin. left. reflexivity.
    + apply IH.
      * intro Hin. apply Hnin. right. exact Hin.
      * exact H.
Qed.

Lemma nodup_map_node : forall (ntl : list ProdVar.t),
    NoDup ntl -> NoDup (map [eta Node] ntl).
Proof.
  induction ntl as [|hd tl IH]; simpl; intros Hnd.
  - constructor.
  - inversion Hnd; subst.
    constructor.
    + apply (notin_node_map_node hd tl H1).
    + apply IH. exact H2.
Qed.

Lemma nodup_addzero : forall j ntl,
    NoDup ntl -> ~ In (j) ntl -> 
    NoDup [:: Zero, Node j & map [eta Node] ntl].
Proof.
  intros j ntl Hnd Hnin.
  apply NoDup_cons.
  - simpl. intro H. destruct H as [H|H].
    + discriminate H.
    + apply (notin_zero_map_node ntl). exact H.
  - apply NoDup_cons.
    + apply (notin_node_map_node j ntl Hnin).
    + apply (@nodup_map_node ntl Hnd).
Qed.

Lemma floyd_update_correct1 :
  forall nds k i s m dmi0 dmin dst0 dstn dik dkj,
    In s nds ->
    NoDup nds ->
    PVM.find i m = Some dmi0 ->
    NVM.find s dmi0 = Some dst0 ->
    PVM.find i (floyd_update' k i nds m) = Some dmin ->
               get_weight i (Node k) m = Some dik ->
               get_weight k s m = Some dkj ->
               NVM.find s dmin = Some dstn ->
               dstn = Z.max dst0 (Z.add dik dkj).
Proof.
  move => nds k i s m dmi0 dmin dst0 dstn dik dkj Hin Hnd Hfdi0 Hfds0. 
  rewrite /floyd_update' /= Hfdi0 find_add_eq_z_fm.
  move => Hinj; injection Hinj; move => Heq; rewrite -Heq.
  move => Hgwik Hgekj Hfdsn.
  apply new_dst_map_correct1 with nds dmi0 s k i m; try done.
Qed.

Lemma floyd_update_correct2 :
  forall nds k i s m dmi0 dmin dstn dik dkj,
    PVM.find i m = Some dmi0 ->
    NVM.find s dmi0 = None ->
    PVM.find i (floyd_update' k i nds m) = Some dmin ->
               get_weight i (Node k) m = Some dik ->
               get_weight k s m = Some dkj ->
               NVM.find s dmin = Some dstn ->
               dstn = (Z.add dik dkj).
Proof.
  move => nds k i s m dmi0 dmin dstn dik dkj Hfdi0. 
  rewrite /floyd_update' /= Hfdi0 find_add_eq_z_fm.
  move => Hfds0.
  move => Hinj; injection Hinj; move => Heq; rewrite -Heq.
  move => Hgwik Hgekj Hfdsn.
  apply new_dst_map_correct3 with nds dmi0 s k i m; try done.
Qed.

Lemma floyd_update_correct3 :
  forall nds k i j m dmi0 dmin,
    PVM.find i m = Some dmi0 ->
    i <> j ->
    PVM.find i (floyd_update' k j nds m) = Some dmin ->
    dmi0 = dmin.
Proof.
  rewrite/floyd_update'. move => nds k i j m dmi0 dmin Hfdi0 Hneq.
  case Hfdj0 : (PVM.find j m) =>[dmij|].
  - rewrite find_add_neq_z_fm// Hfdi0; move => Hinj; by injection Hinj.
    rewrite Hfdi0; move => Hinj; by injection Hinj.
Qed.

Lemma floyd_update_correct4 :
  forall nds k i j m,
    PVM.find i m = None ->
    i <> j ->
    PVM.find i (floyd_update' k j nds m) = None.
Proof.
  rewrite/floyd_update'. move => nds k i j m Hfdi0 Hneq.
  case Hfdj0 : (PVM.find j m) =>[dmij|].
  - rewrite find_add_neq_z_fm// Hfdi0; move => Hinj; by injection Hinj.
    done.
Qed.

Lemma floyd_update_correct5 :
  forall nds k i j s m dmi0 dmin,
    ~ In s nds ->
    PVM.find i m = Some dmi0 ->
    PVM.find i (floyd_update' k j nds m) = Some dmin ->
    NVM.find s dmi0 = NVM.find s dmin.
Proof.
  move => nds k i j s m d0 dn Hnin Hfdi0.
  rewrite /floyd_update'.
  case Hij : (i == j).
  - rewrite -(eqP Hij) Hfdi0 find_add_eq_z_fm; move => Hinj.
    injection Hinj; move => Heq; rewrite -Heq.
    case Hnfds : (NVM.find s d0) => [ds|]; case Hnfdsn : (NVM.find s (new_dst_map nds d0 k i m)) => [dsn|]; last done.
    move : (new_dst_map_correct2 nds d0 s k i m Hnin Hnfds Hnfdsn) => Heq2; rewrite Heq2//.
    move : (new_dst_map_nn nds d0 s k i m Hnfds); rewrite Hnfdsn//.
    move : (new_dst_map_nnsm nds s d0 k i m Hnfds Hnfdsn) => Hin. contradiction.
  - case Hfdj : (PVM.find j m ) => [dj|].
    rewrite find_add_neq_z_fm; last by (move => Heq; rewrite -Heq eq_refl //in Hij).
    rewrite Hfdi0; move => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
    rewrite Hfdi0; move => Hinj; injection Hinj; move => Heq; rewrite -Heq//.
Qed.

Lemma floyd_update_smnn :
  forall nds k i j m dmi0,
    PVM.find i m = Some dmi0 ->
    ~ PVM.find i (floyd_update' k j nds m) = None.
Proof.
  intros.
  rewrite /floyd_update'.
  case Hfdj : (PVM.find j m) => [dmj|].
  case Hij : (i == j) .
  rewrite (eqP Hij) find_add_eq_z_fm//.
  rewrite find_add_neq_z_fm; first rewrite H//.
  move => Heq; rewrite Heq eq_refl // in Hij.
  rewrite H//.
Qed.

Lemma floyd_update_smnn_nodes :
  forall nds k i j m dmi0 dmin s dis,
    PVM.find i m = Some dmi0 ->
    PVM.find i (floyd_update' k j nds m) = Some dmin ->
    NVM.find s dmi0 = Some dis ->
    ~ (NVM.find s dmin = None).
Proof.
  move => nds k i j m dmi0 dmin s dis Hfdi0 Hfdin Hfds.
  rewrite /floyd_update' in Hfdin.
  case Hfdj : (PVM.find j m) => [dmj|] in Hfdin.
  - case Hij : (i == j).
    + rewrite -(eqP Hij) find_add_eq_z_fm in Hfdin.
      rewrite (eqP Hij) in Hfdi0.
      rewrite Hfdi0 in Hfdj; injection Hfdj => Hdm; rewrite -Hdm in Hfdin.
      injection Hfdin => Hdmn.
      rewrite -Hdmn; apply (new_dst_map_nn nds dmi0 s k i m Hfds).
    + rewrite find_add_neq_z_fm// in Hfdin; last by (move => Heq; rewrite Heq eq_refl //in Hij).
      rewrite Hfdi0 in Hfdin.
      injection Hfdin => Hdmn; rewrite -Hdmn.
      by rewrite Hfds.
  - rewrite Hfdi0 in Hfdin.
    injection Hfdin => Hdmn; rewrite -Hdmn.
    by rewrite Hfds.
Qed.

Lemma floyd_update_gw_diff : forall nds i m k j ml0 dik0 dikn,
    PVM.find i m = Some ml0 ->
    i <> j ->
    get_weight i (Node k) m = Some dik0 ->
    get_weight i (Node k) (floyd_update' k j nds m) = Some dikn ->
    dik0 = dikn.
Proof.
  move => nds i m k j ml0 dik0 dikn Hfdi0 Hneq.
  rewrite /get_weight Hfdi0. 
  case Hfdin : (PVM.find i (floyd_update' k j nds m)) => [ml1|].
  - move : (floyd_update_correct3 nds k m Hfdi0 Hneq Hfdin) => Hmleq.
    rewrite Hmleq. move => Hfdk0. rewrite Hfdk0.
    move => Hinj; by injection Hinj.
  - move : (floyd_update_smnn nds k i j m Hfdi0).
    rewrite Hfdin//.
Qed.

Lemma floyd_update_gw_same1 : forall nds i m k ml0 dik0 dkk dikn,
    In (Node k) nds -> NoDup nds ->
    PVM.find i m = Some ml0 ->
    get_weight k (Node k) m = Some dkk ->
    get_weight i (Node k) m = Some dik0 ->
    get_weight i (Node k) (floyd_update' k i nds m) = Some dikn ->
    dikn = Z.max dik0 (Z.add dik0 dkk).
Proof.
  move => nds i m k ml0 dik0 dkk dikn Hin Hnd Hfdi0.
  move => Hgwki Hgwik Hgwikn. generalize Hgwki Hgwik Hgwikn.
  rewrite /get_weight Hfdi0.
  case Hfdk : (PVM.find k m) => [dmk|]; last done.
  move => Hfdki Hfdik.
  case  Hfdin : (PVM.find i (floyd_update' k i nds m)) => [dimn|]; last done.
  move => Hfdikn. 
  exact : (floyd_update_correct1 k i (Node k) m Hin Hnd Hfdi0 Hfdik Hfdin Hgwik Hgwki Hfdikn ).
Qed.
  
Lemma floyd_update_gw_same2 : forall nds i m k j ml0 dij0 dik0 dkj0 dikn,
    In (Node j) nds -> NoDup nds ->
    PVM.find i m = Some ml0 ->
    NVM.find (Node j) ml0 = Some dij0 ->
    get_weight k (Node j) m = Some dkj0 ->
    get_weight i (Node k) m = Some dik0 ->
    j <> k ->
    get_weight i (Node j) (floyd_update' k i nds m) = Some dikn ->
    dikn = Z.max dij0 (Z.add dik0 dkj0).
Proof.
  move => nds i m k j ml0 dij0 dik0 dkj0 dikn Hin Hnd Hfdi0 Hnfdj0 Hgwkj Hgwik Hneq Hgwijn.
  generalize Hgwkj Hgwik Hgwijn.
  rewrite /get_weight Hfdi0.
  case Hfdk0 : (PVM.find k m) => [mlk|]; last done.
  case Hfdin : (PVM.find i (floyd_update' k i nds m)) => [mln|]; last done.
  move => Hfdj0 Hnfdk0 Hnfdjn.
  apply floyd_update_correct1 with nds k i (Node j) m ml0 mln; try done.
Qed.

Lemma floyd_update_gw_smnn : forall i k dik0 y x nds m,
  get_weight i k m = Some dik0 ->
  ~ (get_weight i k (floyd_update' y x nds m) = None).
Proof.
  move => i k dik0 y x nds m.
  rewrite /get_weight.
  case Hfdi0 : (PVM.find i m) => [mli0|]; last done.
  case Hfdin : (PVM.find i (floyd_update' y x nds m)) => [mlin|].
  - 
    exact : (@floyd_update_smnn_nodes nds y i x m mli0 mlin k dik0 Hfdi0 Hfdin).
  - move : (@floyd_update_smnn nds y i x m mli0 Hfdi0). rewrite Hfdin//.
Qed.

Lemma noin_addzero : forall j ntl,
    ~ (In ([eta Node] j) [:: Zero & map [eta Node] ntl] ) ->
    ~ In j ntl.
Proof.
  rewrite /=. move => j nds /Decidable.not_or Hnor Hin. move : Hnor => [Hl Hr].
  - apply Hr. by apply in_map.
Qed.

Definition del_node d n := match n with | Node p => p | Zero => d end.

Lemma noin_addzero' : forall j ntl,
    ~ In j ntl ->
    ~ (In ([eta Node] j) [:: Zero & map [eta Node] ntl] ).
Proof.
  move => j ns Hnin. rewrite /= => Hor. move : Hor=> [Hl| Hr].
  done. apply Hnin.
  have Hj : j = del_node j ([eta Node] j) by rewrite /=//.
  have Hns : ns = (map (del_node j) (map [eta Node] ns)).
  elim ns; rewrite /=//. move => a l IHm. rewrite -IHm//.
  rewrite Hj Hns. by apply in_map.
Qed.

Lemma inner_loop1_correct2 : forall nds i m k j ml0 mln ,
    ~ In j nds -> NoDup nds ->
    PVM.find i m = Some ml0 ->
    PVM.find i (inner_loop1 nds m k) = Some mln ->
    NVM.find (Node j) ml0 = NVM.find (Node j) mln.
Proof.
  elim => [|nhd ntl IHm] i m k j ml0 mln Hin Hndp Hfd0; rewrite /=.
  - rewrite Hfd0; move => Hinj; injection Hinj; move => Heq; rewrite Heq//.
  - case Hfd1 : (PVM.find i (floyd_update' k nhd [:: Zero, Node nhd & map [eta Node] ntl] m)) => [ml1|]. 
    + move => Hfdn.
      move : (noin_addzero' (nhd::ntl) Hin) => Hnins. rewrite map_cons in Hnins.
      move : (floyd_update_correct5 [:: Zero, Node nhd & map [eta Node] ntl] k i nhd (Node j) m Hnins Hfd0 Hfd1 ) => Heq01.
      rewrite Heq01.
      move : Hndp; move => /NoDup_cons_iff [Hnin Hndp]. rewrite /= in Hin.
      move /Decidable.not_or : Hin => [Hneq Hin].
      exact : (IHm i (floyd_update' k nhd [:: Zero, Node nhd & map [eta Node] ntl] m) k j ml1 mln Hin Hndp Hfd1 Hfdn) => Heq1n.
    + move : (floyd_update_smnn [:: Zero, Node nhd & map [eta Node] ntl] k i nhd m Hfd0).
      rewrite Hfd1//.
Qed.

(*Lemma inner_loop1_correct1 : forall nds i m k j ml0 mln dik0 dkj0 (* dkk0 *) dikn dkjn (* dkkn *) dij0 dijn,
    In j nds -> NoDup nds ->
    PVM.find i m = Some ml0 ->
    PVM.find i (inner_loop1 nds m k) = Some mln ->
    get_weight i (Node k) m = Some dik0 ->
    get_weight k (Node j) m = Some dkj0 ->
    (* get_weight k (Node k) m = Some dkk0 -> *)
    get_weight i (Node k) (inner_loop1 nds m k) = Some dikn ->
    get_weight k (Node j) (inner_loop1 nds m k) = Some dkjn ->
    (* get_weight k (Node k) (inner_loop1 nds m k) = Some dkkn -> *)
    NVM.find (Node j) ml0 = Some dij0 ->
    NVM.find (Node j) mln = Some dijn ->
    dijn = Z.max dij0 (Z.add dikn dkjn).
Proof.
  (*elim => [|nhd ntl IHm] i m k j ml0 mln dik0 dkj0 (* dkk0 *) dikn dkjn (* dkkn *) dij0 dijn; rewrite /=//.
  move => [Heq |Hin]. move => /NoDup_cons_iff [Hnin Hndp].
  - rewrite Heq in Hnin *. 
    case Hfdi1 : (PVM.find i (floyd_update' k j [:: Zero, Node j & map [eta Node] ntl] m)) => [ml1|].
    + move => Hfdi0 Hfdin Hgwik Hgwkj (* Hgwkk *) Hgwikn Hgwkjn (* Hgwkkn *) Hnfdij0 Hnfdijn .
      move : (@floyd_update_smnn_nodes [:: Zero, Node j & map [eta Node] ntl] k i j m ml0 ml1 (Node j) dij0 Hfdi0 Hfdi1 Hnfdij0) => Hnfdij1nn.
      case Hnfdj1 : (NVM.find (Node j) ml1) => [dij1|]; last done.
      have Hgwij1 : (get_weight i (Node j) (floyd_update' k j [:: Zero, Node j & map [eta Node] ntl] m)) = Some dij1.
      rewrite /get_weight Hfdi1 Hnfdj1//.
      (* move : (@floyd_update_gw_smnn k (Node k) dkk0 k j [:: Zero, Node j & map [eta Node] ntl] m Hgwkk) => Hgwkknn. *)
      (* case Hgwkk1 : (get_weight k (Node k) (floyd_update' k j [:: Zero, Node j & map [eta Node] ntl] m)) => [dkk1|]; last done. (* dkk1 *) *)
      have Hjin : In (Node j) [:: Zero, Node j & map [eta Node] ntl] by rewrite /=; right; left.
      case Hijeq : (i == j).
      * rewrite (eqP Hijeq) in Hfdi1 Hfdi0 Hfdin Hgwik Hgwikn Hnfdij0 Hnfdijn Hgwij1 Hjin.
        move : (floyd_update_correct1 k j (Node j) m Hjin (nodup_addzero j Hndp Hnin) Hfdi0 Hnfdij0 Hfdi1 Hgwik Hgwkj Hnfdj1) => Hdst01.
        move : (inner_loop1_correct2 j (floyd_update' k j [:: Zero, Node j & map [eta Node] ntl] m) k j Hnin Hndp Hfdi1 Hfdin).
        rewrite  Hnfdijn Hnfdj1. move => Hinj; injection Hinj; move => Hdij1n; rewrite -Hdij1n.
        move : (IHm j (floyd_update' k j [:: Zero, Node j & map [eta Node] ntl] m) k j ml1 mln dik0 dkj0 dikn dkjn dij1 dijn).
        
        (* What has been changed, need to be checked *)
        move : (@floyd_update_gw_smnn i (Node k) dik0 k i [:: Zero, Node i & map [eta Node] ntl] m Hgwik) => Hgwiknn.
        case Hgwik1 : (get_weight i (Node k) (floyd_update' k i [:: Zero, Node i & map [eta Node] ntl] m)) => [dik1|]; last done. (* dik1 *)
        (* move : (@floyd_update_gw_same1 [:: Zero, Node i & map [eta Node] ntl] i m k ml0 dik0 dkk0 dik1 Hfdi0 Hgwkk Hgwik Hgwik1). *)
        move : (@floyd_update_gw_smnn k j dkj0 k i [:: Zero, Node i & map [eta Node] ntl] m Hgwkj) => Hgwkjnn.
        case Hgwkj1 : (get_weight k j (floyd_update' k i [:: Zero, Node i & map [eta Node] ntl] m)) => [dkj1|]; last done. (* dkj1 *)
        assert ((dik1 + dkj1 <= dij1)%Z ). admit. 
        move : (@IHm i (floyd_update' k i [:: Zero, Node i & map [eta Node] ntl] m) k j ml1 mln dik1 dkj1 dkk1 dikn dkjn dkkn dij1 dijn Hfdi1 Hfdin Hgwik1 Hgwkj1 Hgwkk1 Hgwikn Hgwkjn Hgwkkn Hnfdj1 Hnfdjn Hle0 H).
        rewrite Haux. lia.
      * move => Hfdi0 Hfd0n Hgwik Hgwkj Hgwkk Hgwikn Hgwkjn Hgwkkn Hnfdij0 Hfdjn Hlen Hle0.
        have Hneq : (i <> nhd). move => Heq; rewrite Heq eq_refl // in Heqin.
        move : (@floyd_update_correct3 [:: Zero, Node nhd & map [eta Node] ntl] k i nhd m ml0 ml1 Hfdi0 Hneq Hfdi1) => Haux.
        generalize Hnfdij0. rewrite Haux => Hnfdj1.
        have Hgwij1 : (get_weight i j (floyd_update' k nhd [:: Zero, Node nhd & map [eta Node] ntl] m)) = Some dij0.
        rewrite /get_weight. rewrite  Hfdi1 Hnfdj1//.
        move : (@floyd_update_gw_smnn k (Node k) dkk0 k nhd [:: Zero, Node nhd & map [eta Node] ntl] m Hgwkk) => Hgwkknn.
        case Hgwkk1 : (get_weight k (Node k) (floyd_update' k nhd [:: Zero, Node nhd & map [eta Node] ntl] m)) => [dkk1|]; last done. (* dkk1 *) 
        (* move : (@floyd_update_correct3). [:: Zero, Node nhd & map [eta Node] ntl] k i j m Hfdi0 Hnfdij0 Hfdi1 Hgwik Hgwkj Hlen Hnfdj1) => Haux. *)
        move : (@floyd_update_gw_smnn i (Node k) dik0 k nhd [:: Zero, Node nhd & map [eta Node] ntl] m Hgwik) => Hgwiknn.
        case Hgwik1 : (get_weight i (Node k) (floyd_update' k nhd [:: Zero, Node nhd & map [eta Node] ntl] m)) => [dik1|]; last done. (* dik1 *)
        (* move : (@floyd_update_gw_same1 [:: Zero, Node i & map [eta Node] ntl] i m k ml0 dik0 dkk0 dik1 Hfdi0 Hgwkk Hgwik Hgwik1). *)
        move : (@floyd_update_gw_smnn k j dkj0 k nhd [:: Zero, Node nhd & map [eta Node] ntl] m Hgwkj) => Hgwkjnn.
        case Hgwkj1 : (get_weight k j (floyd_update' k nhd [:: Zero, Node nhd & map [eta Node] ntl] m)) => [dkj1|]; last done. (* dkj1 *)
        assert ((dik1 + dkj1 <= dij0)%Z ). admit. 
        exact : (@IHm i (floyd_update' k nhd [:: Zero, Node nhd & map [eta Node] ntl] m) k j ml1 mln dik1 dkj1 dkk1 dikn dkjn dkkn dij0 dijn Hfdi1 Hfd0n Hgwik1 Hgwkj1 Hgwkk1 Hgwikn Hgwkjn Hgwkkn Hnfdj1 Hfdjn Hlen H).
    + move => Hfdi0.
      move : (@floyd_update_smnn [:: Zero, Node nhd & map [eta Node] ntl] k i nhd m ml0 Hfdi0).
      rewrite Hfdi1//.*)
Admitted.

Lemma inner_loop1_gw1 : forall nds i m k j ml0 mln dik0 dkj0 dkk0 dikn dkjn dkkn dij0 dijn,
  PVM.find i m = Some ml0 ->
  PVM.find i (inner_loop1 nds m k) = Some mln ->
  get_weight i (Node k) m = Some dik0 ->
  get_weight k j m = Some dkj0 ->
  get_weight k (Node k) m = Some dkk0 ->
  get_weight i (Node k) (inner_loop1 nds m k) = Some dikn ->
  get_weight k j (inner_loop1 nds m k) = Some dkjn ->
  get_weight k (Node k) (inner_loop1 nds m k) = Some dkkn ->
  Z.le (Z.add dikn dkjn) dijn ->
  Z.le (Z.add dik0 dkj0) dij0 ->
  get_weight i j m = Some dij0 ->
  get_weight i j (inner_loop1 nds m k) = Some (Z.max dij0 (Z.add dikn dkjn)).
Proof.
Admitted.*)



(* Lemma inner_loop2_correct1 : forall nds i m j ml0 mln (* dik0 dkj0 dkk0 *)  dij0 dijn, *)
(*   PVM.find i m = Some ml0 -> *)
(*   PVM.find i (inner_loop2 nds m) = Some mln -> *)
(*   (* get_weight i (Node k) m = Some dik0 -> *) *)
(*   (* get_weight k j m = Some dkj0 -> *) *)
(*   (* get_weight k (Node k) m = Some dkk0 -> *) *)
(*   NVM.find j ml0 = Some d -> *)
(*   (* Z.le (Z.add dikn dkjn) dijn -> *) *)
(*   (* Z.le (Z.add dik0 dkj0) dij0 -> *) *)
(*   (fall k j dikn dkjn       NVM.find j mln = Some dijn      get_weight i (Node k) (inner_loop2 nds m) = Some dikn      get_weight k j (inner_loop2 nds m) = Some dkjn      get_weight k (Node k) (inner_loop2 nds m) = Som)e dkkn      dijn = Z.max dij0 (Z.add dikn)dkjn)). *)
(* Proof. *)
(*   elim => [|nhd ntl IHm]  i m k j ml0 mln dik0 dkj0 dkk0 dikn dkjn dkkn dij0 dijn. *)
(*   - rewrite /=. move => Hfdi0; rewrite Hfdi0; move => Hinj; injection Hinj; move => Heq; rewrite Heq. *)
(*     move => Hik0 Hkj0 Hkk0 Hikn Hkjn Hkkn Hnfdj0. rewrite Hnfdj0; move => Hinj2; injection Hinj2. *)
(*     move => Heq2; rewrite Heq2. lia. *)
(*   - rewrite /=. move => Hfdi0 Hfdin Hik0 Hkj0 Hkk0 Hikn Hkjn Hkkn Hnfdj0 Hnfdjn Hlen Hle0. *)
(*     have Hreplace : (inner_loop1 ntl (floyd_update' nhd nhd [:: Zero, Node nhd & map [eta Node] ntl] m) nhd = inner_loop1 (nhd::ntl) m nhd) by rewrite/=//. *)
(*     rewrite Hreplace in Hfdin Hikn Hkjn Hkkn. *)
(*     case Hgwik1 : *)
(*       (get_weight i (Node k) (inner_loop1 (nhd :: ntl) m nhd)) => [dik1|]; last admit. (*inner_loop1_gw_smnn*) *)
(*     case Hgwkj1 :  *)
(*       (get_weight k j (inner_loop1 (nhd :: ntl) m nhd)) => [dkj1|]; last admit. (*inner_loop1_gw_smnn*) *)
(*     case Hgwkk1 : (get_weight k (Node k) (inner_loop1 (nhd :: ntl) m nhd)) => [dkk1|]; last admit. (*inner_loop1_gw_smnn*) *)
(*     case Hfdi1 : (PVM.find i (inner_loop1 (nhd :: ntl) m nhd)) => [ml1|]. (*inner_loop1_smnn*) *)
(*     case Hnfdj1 : (NVM.find j ml1) => [dij1|]; last admit. (*inner_loop1_node_smnn*) *)
(*       have Hmono1 : (Z.le (dik1 + dkj1) dij1)%Z. admit. (*inner_loop1_get_weight_mono *) *)
(*     + move : (@inner_loop1_correct1 (nhd::ntl) i m nhd j ml0 ml1 dik0 dkj0 dkk0 dik1 dkj1 dkk1 dij0  dij1 Hfdi0 Hfdi1 Hik0 Hkj0 Hkk0 Hgwik1 Hgwkj1 Hgwkk1 Hnfdj0 Hnfdj1 Hmono1 Hle0) => Haux. *)
(*       move : (@IHm i (inner_loop1 (nhd :: ntl) m k) k j ml1 mln dik1 dkj1 dkk1 dikn dkjn dkkn dij1 dijn Hfdi1 Hfdin). *)

      
    
(* Admitted. *)

Lemma nvm_find_aux_some : forall n dm nhd s d m,
  NVM.find n dm <> None ->
  NVM.find n (new_dst_map_aux dm nhd s d m) <> None.
Proof.
  move => n dm nhd s d m Hnn.
  rewrite /new_dst_map_aux.
  case Hfd1 : (NVM.find nhd dm) => [dnhd|]; case Hgws : (get_weight d (Node s) m) => [w1|]; case Hgwn : (get_weight s nhd m) => [w2|].
  all: rewrite /=.
  (* 1: Some,Some,Some *)
  - case: (NodeVar.eq_dec n nhd) => [Heq|Hneq].
    + rewrite (node_eq_leibniz _ _ Heq).
      by rewrite find_add_eq_z.
    + rewrite find_add_neq_z; last by move => He; apply Hneq; rewrite He; exact (NodeVar.eq_refl nhd).
      exact Hnn.
  (* 2: Some,Some,None *)
  - case: (NodeVar.eq_dec n nhd) => [Heq|Hneq].
    + rewrite (node_eq_leibniz _ _ Heq).
      by rewrite Hfd1.
    + exact Hnn.
  (* 3: Some,None,Some *)
  - by [].
  (* 4: Some,None,None *)
  - by [].
  (* 5: None,Some,Some *)
  - case: (NodeVar.eq_dec n nhd) => [Heq|Hneq].
    + rewrite (node_eq_leibniz _ _ Heq).
      by rewrite find_add_eq_z.
    + rewrite find_add_neq_z; last by move => He; apply Hneq; rewrite He; exact (NodeVar.eq_refl nhd).
      exact Hnn.
  (* 6: None,Some,None *)
  - case: (NodeVar.eq_dec n nhd) => [Heq|Hneq].
    + exact Hnn.
    + exact Hnn.
  (* 7: None,None,Some *)
  - by [].
  (* 8: None,None,None *)
  - by [].
Qed.

Lemma find_new_dst_map_some : forall n dm dst0 ntl s d m,
  NVM.find n dm = Some dst0 ->
  NVM.find n (new_dst_map ntl dm s d m) = None -> False.
Proof.
  move => n dm dst0 ntl s d m Hfd0 Hfd1.
  move: ntl dm Hfd0 Hfd1.
  elim => [|nhd ntl IHm] dm Hfd0 Hfd1; rewrite /=.
  - rewrite Hfd0 in Hfd1. discriminate.
  - rewrite /= in Hfd1.
    case Hfd2 : (NVM.find n (new_dst_map ntl dm s d m)) => [dst1|].
    + move: (nvm_find_aux_some n (new_dst_map ntl dm s d m) nhd s d m) => Haux.
      rewrite Hfd2 in Haux.
      have Hsn : Some dst1 <> None; first discriminate.
      move: (Haux Hsn) => Hc.
      exact (Hc Hfd1).
    + case: (IHm dm Hfd0 Hfd2) => //.
Qed.

Lemma pfind_floyd_update_some : forall d m ml0 i nhd ntl,
  PVM.find d m = Some ml0 ->
  PVM.find d (floyd_update' i nhd ntl m) = None -> False.
Proof.
  move => d m ml0 i nhd ntl Hfd0.
  by apply: (floyd_update_smnn ntl i d nhd m Hfd0).
Qed.

Lemma prod_eq_leibniz : forall (v a : ProdVar.t), ProdVar.eq v a -> v = a.
Proof.
  move => v a. case: v => [v1 v2]. case: a => [a1 a2]. move => [H1 H2]. rewrite /= in H1 H2. move: H1 H2 => /eqP -> /eqP ->. done.
Qed.

Lemma find_floyd_update_some : forall d m ml0 i nhd ntl fu1 s dst,
    PVM.find d m = Some ml0 ->
    PVM.find d (floyd_update' i nhd ntl m) = Some fu1 ->
    NVM.find s ml0 = Some dst ->
    NVM.find s fu1 = None -> False.
Proof.
  move => d m ml0 i nhd ntl fu1 s dst Hfd0 Hfd1 Hfs0 Hfs1.
  rewrite /floyd_update' in Hfd1.
  case Hfdnhd : (PVM.find nhd m) => [dmnhd|].
  - case: (ProdVar.eq_dec d nhd) => [Heq|Hneq].
    + have Hle : d = nhd := prod_eq_leibniz Heq.
      rewrite Hle in Hfd1. rewrite Hfdnhd in Hfd1.
      rewrite find_add_eq_z_fm in Hfd1.
      rewrite Hle in Hfd0. rewrite Hfdnhd in Hfd0.
      injection Hfd0 => Hml. rewrite <- Hml in Hfs0.
      injection Hfd1 => Hfu. rewrite <- Hfu in Hfs1.
      move: (new_dst_map_nn ntl dmnhd s i nhd m Hfs0); rewrite Hfs1. by [].
    + rewrite Hfdnhd in Hfd1. rewrite find_add_neq_z_fm in Hfd1;
        last by move => Heq; apply: Hneq; rewrite Heq; exact: ProdVar.eq_refl.
      rewrite Hfd0 in Hfd1. injection Hfd1 => Hfu. rewrite <- Hfu in Hfs1.
      congruence.
  - rewrite Hfdnhd in Hfd1. rewrite Hfd0 in Hfd1.
      injection Hfd1 => Hfu. rewrite <- Hfu in Hfs1. congruence.
Qed.

Lemma pfind_innedr_loop1_some : forall d m ml0 nhd ntl,
  PVM.find d m = Some ml0 ->
  PVM.find d (inner_loop1 ntl m nhd) = None -> False.
Proof.
  move => d m ml0 nhd ntl Hfd0 Hfd1.
  have HH : forall ns m' v, PVM.find d m' = Some v ->
            PVM.find d (inner_loop1 ns m' nhd) = None -> False.
  { elim => [|hd ns IHm] m' v Hfd0' Hfd1'; rewrite /=.
    - rewrite Hfd0' in Hfd1'. discriminate.
    - have Hsm := (floyd_update_smnn (Zero::map Node (hd::ns)) nhd d hd m' Hfd0').
      case Hfdm : (PVM.find d (floyd_update' nhd hd (Zero::map Node (hd::ns)) m')) => [w|].
      + exact: (IHm _ w Hfdm Hfd1').
      + move: Hsm; rewrite Hfdm. move => Hc. exact: (Hc erefl). }
  exact: (HH ntl m ml0 Hfd0 Hfd1).
Qed.

Lemma find_inner_loop1_some : forall d m ml0 nhd ntl vin1 s dst0,
  PVM.find d m = Some ml0 ->
  PVM.find d (inner_loop1 ntl m nhd) = Some vin1 ->
  NVM.find s ml0 = Some dst0 ->
  NVM.find s vin1 = None -> False.
Proof.
  move => d m ml0 nhd ntl vin1 s dst0 Hfd0 Hfd1 Hfs0 Hfs1.
  have HH : forall ns m' v0 v1 dst, PVM.find d m' = Some v0 ->
            PVM.find d (inner_loop1 ns m' nhd) = Some v1 ->
            NVM.find s v0 = Some dst ->
            NVM.find s v1 = None -> False.
  { elim => [|hd ns IHm] m' v0 v1 dst Hfd0' Hfd1' Hfs0' Hfs1'; rewrite /= in Hfd1' *.
    - rewrite Hfd0' in Hfd1'. injection Hfd1' => Hv. rewrite <- Hv in Hfs1'.
      congruence.
    - case Hfdm : (PVM.find d (floyd_update' nhd hd (Zero::map Node (hd::ns)) m')) => [w|].
      + case Hfsw : (NVM.find s w) => [dw|].
        * exact: (IHm _ w v1 dw Hfdm Hfd1' Hfsw Hfs1').
        * exact: (@find_floyd_update_some d m' v0 nhd hd (Zero::map Node (hd::ns)) w s dst Hfd0' Hfdm Hfs0' Hfsw).
      + have Hsm := (floyd_update_smnn (Zero::map Node (hd::ns)) nhd d hd m' Hfd0').
        move: Hsm; rewrite Hfdm. move => Hc. exact: (Hc erefl). }
  exact: (HH ntl m ml0 vin1 dst0 Hfd0 Hfd1 Hfs0 Hfs1).
Qed.

Lemma new_dst_map_correct :
  forall ns dm n s d m dst0 dst1,
    NVM.find n dm = Some dst0 ->
    NVM.find n (new_dst_map ns dm s d m) = Some dst1 ->
    Z.le dst0 dst1.
Proof.
  elim => [|nhd ntl Hm] dm n s d m dst0 dst1.
  - rewrite /=.
    move => Hfd0 Hfd1; rewrite Hfd0 in Hfd1; injection Hfd1; move => Heq.
    lia.
  - rewrite /= /new_dst_map_aux.
    case Hfnhd : (NVM.find nhd (new_dst_map ntl dm s d m) ) => [vnhd|].
    + case Hgwd : (get_weight d (Node s) m) => [wd|].
      * case Hgws : (get_weight s nhd m) => [ws|].
        {
          case Hn : n => [|vn].
          - move : Hfnhd.
            case Hnhd : nhd => [|vhd].
            + rewrite find_add_eq_z.
              move => Hfd1 Hfd0 Hdst1.
              move : (Hm dm Zero s d m dst0 vnhd Hfd0 Hfd1) => Hle2.
              injection Hdst1; move => Heqdst1; rewrite -Heqdst1.
              rewrite Z.max_le_iff. left; done.
            + rewrite find_add_neq_z. move => _.
              apply Hm.
              done.
          - move : Hfnhd.
            case Hnhd : nhd => [|vhd].
            + rewrite find_add_neq_z. move => _.
              apply Hm.
              done.
            + case Heqvn : (vhd == vn).
              * rewrite (eqP Heqvn) find_add_eq_z.
                move => Hfd1 Hfd0 Hdst1.
                move : (Hm dm (Node vn) s d m dst0 vnhd Hfd0 Hfd1) => Hle2.
                injection Hdst1; move => Heqdst1; rewrite -Heqdst1.
                rewrite Z.max_le_iff. left; done.
              * rewrite find_add_neq_z. move => _.
                apply Hm.
                intro; injection H; move => Heq; rewrite Heq eq_refl// in Heqvn.
        }
        {
          apply Hm.
        }
      * apply Hm.
    * case Hgwd : (get_weight d (Node s) m) => [wd|].
      * case Hgws : (get_weight s nhd m) => [ws|].
        {
          case Hn : n => [|vn].
          - move : Hfnhd.
            case Hnhd : nhd => [|vhd].
            + rewrite find_add_eq_z. move => Hfdzn Hfdzs.
              move : (find_new_dst_map_some Zero dm ntl s d m Hfdzs Hfdzn); done.
            + rewrite find_add_neq_z. move =>_.
              apply Hm.
              intro; inversion H.
          - move : Hfnhd.
            case Hnhd : nhd => [|vhd].
            + rewrite find_add_neq_z. move =>_.
              apply Hm.
              intro; inversion H.
            + case Hvhdn : (vhd == vn).
              * rewrite (eqP Hvhdn) find_add_eq_z.
                move => Hfdzn Hfdzs.
                move : (find_new_dst_map_some (Node vn) dm ntl s d m Hfdzs Hfdzn); done.
              * rewrite find_add_neq_z. move =>_.
                apply Hm.
                intro; injection H; move => Heq; rewrite Heq eq_refl// in Hvhdn.
        }
        {
          apply Hm.
        }
      * apply Hm.
Qed.

Lemma floyd_update_correct : forall nds d k i m ml0 ml1,
  PVM.find d m = Some ml0 ->
  PVM.find d (floyd_update' k i nds m) = Some ml1 ->
    forall s dst0 dst1,
      NVM.find s ml0 = Some dst0 ->
      NVM.find s ml1 = Some dst1 ->
      Z.le dst0 dst1.
Proof.
  move => nds d k i m ml0 ml1 .
  rewrite /floyd_update'. 
  case Hfdi : (PVM.find i m) => [mli|].
  - move : Hfdi.
    case Heqdi : (d == i).
    +
      rewrite (eqP Heqdi) find_add_eq_z_fm. 
      move => Himli Himl0 Hml1 s dst0 dst1 .
      rewrite Himli in Himl0; injection Himl0; move => Heqml.
      injection Hml1; move => Heqml1.
      rewrite -Heqml1 -Heqml. apply new_dst_map_correct.
    +
      rewrite find_add_neq_z_fm.
      move => Himli Himl0 Hml1.
      rewrite Hml1 in Himl0; injection Himl0; move => Heqml01.
      rewrite Heqml01. move => s dst0 dst1 Hs0 Hs1.
      rewrite Hs0 in Hs1; injection Hs1; move => Heqdst. lia.
      intro. rewrite H eq_refl //in Heqdi.
  - move => Himli Himl0.
      rewrite Himli in Himl0; injection Himl0; move => Heqml01.
      rewrite Heqml01. move => s dst0 dst1 Hs0 Hs1.
      rewrite Hs0 in Hs1; injection Hs1; move => Heqdst. lia.
Qed.

(* inner_loop1 is : add dm in m for all nodes n and Zero, using the update dist map caused by k*)
Lemma inner_loop1_correct : forall nds d (m: adj_matrix) k ml0 ml1,
  PVM.find d m = Some ml0 ->
  PVM.find d (inner_loop1 nds m k) = Some ml1 ->
    forall s dst0 dst1,
      NVM.find s ml0 = Some dst0 ->
      NVM.find s ml1 = Some dst1 ->
      Z.le dst0 dst1.
Proof.
  elim => [|nhd ntl Hm] d m i ml0 ml1; rewrite/=.
  - move => Hfd0 Hfd1 s dst0 dst1. rewrite Hfd0 in Hfd1.
    injection Hfd1; move => Heqml01; rewrite Heqml01.
    move => Hdst0 Hdst1; rewrite Hdst0 in Hdst1; injection Hdst1. lia.
  - case Hfu : (PVM.find d (floyd_update' i nhd [:: Zero, Node nhd & map [eta Node] ntl] m)) => [fu1|].
    + move => Hfddml0 Hfddin1 s dst0 dst1.
      case Hnfus1 : (NVM.find s fu1) => [vsfu1|].
      * move => Hnfdsml0 Hnfdsml1.
        move : (floyd_update_correct [:: Zero, Node nhd & map [eta Node] ntl] d i nhd m Hfddml0 Hfu s Hnfdsml0 Hnfus1).
        move : (Hm d (floyd_update' i nhd [:: Zero, Node nhd & map [eta Node] ntl] m) i fu1 ml1 Hfu Hfddin1 s vsfu1 dst1 Hnfus1 Hnfdsml1).
        lia.
      * move => Hdst0.
        move : (find_floyd_update_some d m i nhd [:: Zero, Node nhd & map [eta Node] ntl] s Hfddml0 Hfu Hdst0 Hnfus1). done.
    + move => Hfddml0 Hfddin1.
      move : (pfind_floyd_update_some d m i nhd [:: Zero, Node nhd & map [eta Node] ntl] Hfddml0 Hfu). done.
Qed.              

Lemma inner_loop2_correct : forall nds d (m: adj_matrix) ml0 ml1,
  PVM.find d m = Some ml0 ->
  PVM.find d (inner_loop2 nds m) = Some ml1 ->
    forall s dst0 dst1,
      NVM.find s ml0 = Some dst0 ->
      NVM.find s ml1 = Some dst1 ->
      Z.le dst0 dst1.
Proof.
  elim => [|nhd ntl Hm] d m ml0 ml1.
  - rewrite /=. move => Hfdml0 Hfdml1; rewrite Hfdml0 in Hfdml1.
    injection Hfdml1; move => Heq; rewrite Heq.
    move => s dst0 dst1 Hnfds0 Hnfds1; rewrite Hnfds0 in Hnfds1.
    injection Hnfds1. lia.
  - rewrite /=.
    replace ((inner_loop1 ntl (floyd_update' nhd nhd [:: Zero, Node nhd & map [eta Node] ntl] m) nhd)) with (inner_loop1 (nhd :: ntl) m nhd)
      by done.
    case Hfdin1 : (PVM.find d (inner_loop1 (nhd :: ntl) m nhd)) => [vin1|].
    + move => Hfdml0 Hfdin2 s dst0 dst1 Hdst0 Hdst1.
      case Hfdvin1 : (NVM.find s vin1) => [dstin1|].
      * move : (Hm d (inner_loop1 (nhd :: ntl) m nhd) vin1 ml1 Hfdin1 Hfdin2 s dstin1 dst1 Hfdvin1 Hdst1).
        move : (inner_loop1_correct (nhd :: ntl) d m nhd Hfdml0 Hfdin1 s Hdst0 Hfdvin1).
        lia.
      * move : (find_inner_loop1_some d m nhd (nhd::ntl) s Hfdml0 Hfdin1 Hdst0 Hfdvin1). done.
    + move => Hfdml0 Hfdin2 s dst0 dst1 Hdst0 Hdst1.
      move : (pfind_innedr_loop1_some d m nhd (nhd::ntl) Hfdml0 Hfdin1). done.
Qed.

(*Lemma in_init_dist_map : forall nds s cs ml0,
    PVM.find s (init_dist_map' nds cs) = Some ml0 ->
    In s nds.
Proof.
  elim => [|nhd ntl Hm] s cs ml0.
  - rewrite /init_dist_map'/=.
    move : cs s ml0.
    elim => [|cshd cstl Hn] s ml0.
    + rewrite /= (find_empty_None s)//.
    + rewrite /=. apply Hn.
  - rewrite /init_dist_map' /=.
Admitted.

Lemma in_init_dist_mapd : forall nds s cs ml0 d dst,
    PVM.find s (init_dist_map' nds cs) = Some ml0 ->
    NVM.find (Node d) ml0 = Some dst ->
    In d nds.
Proof.
Admitted.*)

Lemma init_dist_map_correct : forall nds d cs ml0 ml1,
    PVM.find d (map0 nds (PVM.empty (NVM.t Z.t))) = Some ml0 ->
    PVM.find d (init_dist_map' nds cs) = Some ml1 ->
    forall s dst0 dst1,
      NVM.find s ml0 = Some dst0 ->
      NVM.find s ml1 = Some dst1 ->
      Z.le dst0 dst1.
Proof.
  move => nds d cs ml0 ml1 Hfd0 Hfd1 s dst0 dst1 Hnfd0 Hnfd1.
  rewrite /init_dist_map'.
  exact : (@add_edge_of_cs_correct cs d (map0 nds (PVM.empty (NVM.t Z.t))) ml0 ml1 Hfd0 Hfd1 s dst0 dst1 Hnfd0 Hnfd1).
Qed.
  
Lemma floyd_loop_map_correct :
  forall nds cs s d  ml0 ml dst0 dst1,
    PVM.find s (init_dist_map' nds cs) = Some ml0 ->
    PVM.find s (floyd_loop_map' nds cs) = Some ml ->
    NVM.find (Node d) ml0 = Some dst0 ->
    NVM.find (Node d) ml = Some dst1 ->
    Z.le dst0 dst1.
Proof.
  elim => [|nhd ntl Hm].
  - move => cs s d ml0 ml1 dst0 dst1.
    rewrite /init_dist_map'/floyd_loop_map'/init_dist_map' /=.
    move => Hfdml0 Hfdml1 .
    rewrite Hfdml0 in Hfdml1. injection Hfdml1; move => Heq; rewrite Heq.
    move => Hdst0 Hdst1; rewrite Hdst0 in Hdst1; injection Hdst1. lia.
  - move => cs s d ml0 ml1 dst0 dst1 Hfdsml0 Hfdsml1 Hdst0 Hdst1.
    rewrite /floyd_loop_map' in Hfdsml1.
    exact : (inner_loop2_correct (nhd::ntl) s (init_dist_map' (nhd :: ntl) cs) Hfdsml0 Hfdsml1 (Node d) Hdst0 Hdst1).
Qed.
    
Fixpoint maxz_list (l : list Z.t) : Z.t :=
  match l with
  | nil => 0%Z
  | t :: tl => Z.max t (maxz_list tl)
  end.

Fixpoint save_longest_dist (simple_cycle : list ProdVar.t) (m : adj_matrix) (values : Valuation) : option Valuation :=
  match simple_cycle with
  | nil => Some values
  | hd :: tl => match PVM.find hd m with
    | Some dst_map => let (_, dists) := List.split (NVM.elements dst_map) in 
                      let new_values := PVM.add hd (Z.to_nat (maxz_list dists)) values in
                      save_longest_dist tl m new_values
    | None => None
    end
  end.

Lemma le_maxz_list : forall l a,
    In a l -> Z.le a (maxz_list l).
Proof.
  elim => [|hd tl Hm] a.
  - rewrite /=//.
  - rewrite /=. move => [Hin| Hin].
    + rewrite Hin. apply Z.le_max_l.
    + rewrite Z.max_le_iff. right. by apply Hm.
Qed.

Lemma split_map (A B : Type) (l : list (A*B)) :
  split l = (map fst l, map snd l).
Proof.
  induction l as [|[x y] tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma findA_in (A B : Type) (f : A -> bool) (l : list (A*B)) (a : A) (b : B) :
    findA f l = Some b -> In (a,b) l -> f a = true -> In b (snd (split l)).
Proof.
  move => _ Hin _.
  rewrite split_map /=.
  elim: l Hin => [|[x y] tl IH] Hin.
  by [].
  case: Hin => [Heq|Hin'].
  - injection Heq as <- <-. by left.
  - right. by apply IH.
Qed.

Lemma findA_sound :
 forall (A B : Type) (f : A -> bool) (l : list (A*B)) (b : B),
   findA f l = Some b -> exists a, In (a,b) l /\ f a = true.
Proof.
  move => A B f l.
  elim: l => [|[x y] tl IH] b Hfind.
  rewrite /findA /= in Hfind. discriminate.
  rewrite /findA /= in Hfind.
  case Hfx : (f x).
  - rewrite Hfx in Hfind.
    injection Hfind as <-.
    exists x. rewrite /=.
    apply: conj => //.
    by left.
  - rewrite Hfx in Hfind.
    case: (IH b Hfind) => [a [Hin Hfa]].
    exists a. rewrite /=.
    apply: conj; first by right.
    done.
Qed.

Lemma nvm_find_in_split :
  forall (m : NVM.M.t nat) (k : NVM.M.key) (v : nat),
    NVM.M.find k m = Some v -> In v (snd (split (NVM.M.elements m))).
Proof.
  move => m k v Hfind.
  rewrite NVM.Lemmas.elements_o in Hfind.
  case: (@findA_sound node (nat) (NVM.Lemmas.eqb k) _ _ Hfind) => [a [Hin Hfa]].
  exact (@findA_in node nat (NVM.Lemmas.eqb k) (NVM.M.elements m) a v Hfind Hin Hfa).
Qed.

(* Definition In (v : Valuation) (bds : Bounds) : Prop := *)
(*   forall (x : ProdVar.t) (lb ub : nat), *)
(*     PVM.find x bds = Some (lb, ub) -> *)
(*     (exists n, PVM.find x v = Some n /\ lb <= n /\ n <= ub). *)

Definition In_fm (v : Valuation) (fm : adj_matrix) : Prop :=
  forall (s : ProdVar.t) (*len : Z*) md,
    PVM.find s fm = Some md ->
    (* NVM.find (Node d) md = Some len  ->*)
    (exists n , PVM.find s v = Some n /\ (Z.le (maxz_list (split (NVM.elements md)).2) (Z.of_nat n))).

Fixpoint uni_ns (ns : list ProdVar.t) :=
  match ns with
  | nil => true
  | c :: s => ~~(c \in s) && uni_ns s
  end.

Definition In_ns c cs := (c \in cs) && (uni_ns cs).

Fixpoint uni_cs (ns : list Constraint1) :=
  match ns with
  | nil => true
  | c :: s => ~~(c \in s) && uni_cs s
  end.

Definition In_cs c cs := (c \in cs) && (uni_cs cs).

(* Definition well_defined_m (m : adj_matrix) : Prop := *)
(*   forall (x : ProdVar.t) dst, PVM.find x m = Some dst . *)

Definition rhs_vars1 :=
fun c : Constraint1 => (map snd (rhs_terms1 c)).
 
Definition conform1_m (cs : list Constraint1) (m : adj_matrix) :=
  forall (c : Constraint1),
    In c cs -> 
    (exists dst, PVM.find (lhs_var1 c) m = Some dst) /\
      (forall x, List.In x (rhs_vars1 c) -> exists dst, PVM.find x m = Some dst).

Lemma conform1_m_back : forall hd tl fm,
    conform1_m (hd :: tl) fm -> conform1_m (tl) fm .
Proof.
  move => hd tl fm H c Hin. exact: (H c (or_intror Hin)).
Qed.

Definition well_formed (m : adj_matrix) (cs1 : list Constraint1) :=
  (* well_defined_m m /\  *)conform1_m cs1 m.

Lemma z2n2z : forall z, (0 <= z)%Z -> Z.of_nat (Z.to_nat z) = z.
Proof. move => z Hz. lia. Qed.

Lemma maxz_list_ge0 : forall (l : list Z.t), (0 <= maxz_list l)%Z.
Proof.
  elim => [|hd tl IH]; rewrite /=.
  - done.
  - rewrite Z.max_le_iff. by right.
Qed.

(* dominates c v fm: for constraints of the shape c.lhs <= c.const + s (in v),
   the value assigned to s in v is dominated by the max edge weight in the
   adjacency list of c.lhs in fm. This is an explicit premise supplied to the
   final theorem. *)
Definition dominates (c : Constraint1) (v : Valuation) (fm : adj_matrix) : Prop :=
  match rhs_terms1 c, rhs_power c with
  | [:: (1, s)], [::] =>
      match PVM.find (lhs_var1 c) fm with
      | Some cm =>
          match split (NVM.elements cm) with
          | (_, dist) =>
              exists d : nat, PVM.find s v = Some d /\
                ((rhs_const1 c + Z.of_nat d) <=? Z.of_nat (Z.to_nat (maxz_list dist)))%Z = true
          end
      | None => True
      end
  | _, _ => True
  end.

Definition dominates_all (cs : list Constraint1) (v : Valuation) (fm : adj_matrix) : Prop :=
  forall c, In c cs -> dominates c v fm.

Lemma dom_add_find :
  forall (c:Constraint1) (s:ProdVar.t) (fm:adj_matrix) (cm:NVM.t Z.t)
         (a:list node) (dist:list Z.t) (v0:Valuation) (dn:nat),
    PVM.find (lhs_var1 c) fm = Some cm ->
    rhs_terms1 c = [(1,s)] -> (rhs_power c) = nil ->
    split (NVM.elements cm) = (a, dist) ->
    dominates c (PVM.add (lhs_var1 c) dn v0) fm ->
    PVM.find (lhs_var1 c) v0 = None ->
    exists d : nat, PVM.find s (PVM.add (lhs_var1 c) dn v0) = Some d.
Proof.
  move => c s fm cm a dist v0 dn Hfdc Hrhs Hpow Hspl Hdom Hcv0.
  rewrite /dominates Hrhs Hpow Hfdc Hspl in Hdom.
  case: Hdom => d [Hd _]. exists d. done.
Qed.

Lemma satisfies_constraint1_add_maxzlist :
  forall (c:Constraint1) (s:ProdVar.t) (fm:adj_matrix) (cm:NVM.t Z.t)
         (a:list node) (dist:list Z.t) (v0:Valuation),
    PVM.find (lhs_var1 c) fm = Some cm ->
    rhs_terms1 c = [(1,s)] -> (rhs_power c) = nil ->
    split (NVM.elements cm) = (a, dist) ->
    dominates c (PVM.add (lhs_var1 c) (Z.to_nat (maxz_list dist)) v0) fm ->
    PVM.find (lhs_var1 c) v0 = None ->
    satisfies_constraint1' (PVM.add (lhs_var1 c) (Z.to_nat (maxz_list dist)) v0) c.
Proof.
  move => c s fm cm a dist v0 Hfdc Hrhs Hrhsp Hspl Hdom Hcv0.
  rewrite /satisfies_constraint1' find_add_eq /rhs_value1' Hrhs/=.
  rewrite /terms_value_aux/= mul1n.
  rewrite /dominates Hrhs Hrhsp Hfdc Hspl in Hdom.
  case: Hdom => [v [Hfindv Hle]].
  by rewrite Hfindv Hle.
Qed.


Lemma terms_value'_ext :
  forall (v v' : Valuation) (terms : list (nat * ProdVar.t)) (acc : Z.t),
    (forall y, In y (map snd terms) -> PVM.find y v = PVM.find y v') ->
    terms_value' v terms acc = terms_value' v' terms acc.
Proof.
  move => v v' terms.
  elim: terms => [|hd tl IH] acc Hsame.
  - done.
  - rewrite /= /terms_value_aux.
    have Heq : PVM.find (snd hd) v = PVM.find (snd hd) v'.
    { apply Hsame. rewrite /=. by left. }
    rewrite Heq.
    apply IH => y Hy. apply Hsame. rewrite /=. by right.
Qed.

Lemma rhs_value1'_ext :
  forall (c : Constraint1) (v v' : Valuation),
    (forall y, In y (rhs_vars' c) -> PVM.find y v = PVM.find y v') ->
    rhs_value1' v c = rhs_value1' v' c.
Proof.
  move => c v v' Hsame.
  rewrite /rhs_value1' /rhs_vars' in Hsame *.
  by apply terms_value'_ext.
Qed.

Lemma sat_preserve_add :
  forall (c : Constraint1) (x : ProdVar.t) (dn : nat) (v v' : Valuation),
    ~ In x (lhs_var1 c :: rhs_vars' c) ->
    (forall y, In y (lhs_var1 c :: rhs_vars' c) -> PVM.find y v = PVM.find y v') ->
    satisfies_constraint1' v c = true ->
    satisfies_constraint1' (PVM.add x dn v') c = true.
Proof.
  move => c x dn v v' Hnin Hsame Hsat.
  rewrite /satisfies_constraint1' in Hsat |- *.
  have Hneql : lhs_var1 c <> x.
  { move => E. apply Hnin. rewrite E. by left. }
  rewrite (find_add_neq (v:=lhs_var1 c) (a:=x) (dn)) //.
  have Hlhs : PVM.find (lhs_var1 c) v = PVM.find (lhs_var1 c) v'.
  { apply Hsame. by left. }
  rewrite Hlhs in Hsat |- *.
  have Hr := (rhs_value1'_ext c v (PVM.add x dn v')).
  rewrite Hr in Hsat |- *; last first.
    move => y Hy.
    rewrite (find_add_neq (v:=y) (a:=x) (dn)) //; last first.
    { move => E. apply Hnin. rewrite -E. by right. }
    by apply Hsame; right.
  done.
Qed.

Lemma sl_find_notin :
  forall sc fm v v1 x,
    save_longest_dist sc fm v = Some v1 ->
    ~ In x sc ->
    PVM.find x v1 = PVM.find x v.
Proof.
  elim => [|hd tl IH] fm v v1 x Hsave Hnin; first by rewrite /= in Hsave; injection Hsave as <-.
  rewrite /save_longest_dist /= in Hsave.
  case Hf : (PVM.find hd fm) => [dst_map|]; last by rewrite Hf in Hsave.
  case Hs : (split (NVM.elements dst_map)) => [a dists] //.
  move: Hsave. rewrite Hf Hs /=. move => Hsave0.
  move: (IH fm (PVM.add hd (Z.to_nat (maxz_list dists)) v) v1 x Hsave0) => HI.
  have Hxhd : x <> hd.
  { move => E. apply Hnin. rewrite E. by left. }
  rewrite (find_add_neq (v:=x) (a:=hd) _) // in HI.
  apply HI.
  move => E. apply Hnin. by right.
Qed.

Lemma sl_find_pin :
  forall sc fm v v1 x dn cm,
    save_longest_dist sc fm v = Some v1 ->
    PVM.find x v = Some dn ->
    PVM.find x fm = Some cm ->
    dn = Z.to_nat (maxz_list (split (NVM.elements cm)).2) ->
    PVM.find x v1 = Some dn.
Proof.
  elim => [|hd tl IH] fm v v1 x dn cm Hsave Hfx Hfmc Hdn;
    first by rewrite /= in Hsave; injection Hsave as <-.
  rewrite /save_longest_dist /= in Hsave.
  case Hf : (PVM.find hd fm) => [dst_map|]; last by rewrite Hf in Hsave.
  case Hs : (split (NVM.elements dst_map)) => [a dists] //.
  move: Hsave. rewrite Hf Hs /=. move => Hsave0.
  have Hfxv : PVM.find x (PVM.add hd (Z.to_nat (maxz_list dists)) v) = Some dn.
  { case: (ProdVar.eq_dec x hd) => [E|Hne].
    - rewrite E find_add_eq.
      have Hcd : cm = dst_map.
      { rewrite -E in Hf. by congruence. }
      rewrite -Hcd in Hs. rewrite Hs in Hdn. by rewrite Hdn.
    - have Hxhd : x <> hd by move => E2; apply Hne; apply eq_from_prodvar_eq; exact E2.
      by rewrite (find_add_neq (v:=x) (a:=hd) _) //. }
  exact: (IH fm _ v1 x dn cm Hsave0 Hfxv Hfmc Hdn).
Qed.

Lemma sl_find_in :
  forall sc fm v v1 x cm,
    save_longest_dist sc fm v = Some v1 ->
    In x sc ->
    PVM.find x fm = Some cm ->
    PVM.find x v1 = Some (Z.to_nat (maxz_list (split (NVM.elements cm)).2)).
Proof.
  elim => [|hd tl IH] fm v v1 x cm Hsave Hin Hfmc.
  { move: Hin => []. }
  rewrite /save_longest_dist /= in Hsave.
  case Hf : (PVM.find hd fm) => [dst_map|]; last by rewrite Hf in Hsave.
  case Hs : (split (NVM.elements dst_map)) => [a dists] //.
  move: Hsave. rewrite Hf Hs /=. move => Hsave0.
  move: Hin => [E|Hin].
  - rewrite E in Hf.
    have Hcd : cm = dst_map by congruence.
    rewrite -Hcd in Hs.
    have H1 : PVM.find x (PVM.add hd (Z.to_nat (maxz_list dists)) v)
              = Some (Z.to_nat (maxz_list dists)).
    { by rewrite E find_add_eq. }
    have H3 : Z.to_nat (maxz_list dists)
              = Z.to_nat (maxz_list (split (NVM.elements cm)).2).
    { rewrite Hs. done. }
    have Hp := (@sl_find_pin tl fm (PVM.add hd (Z.to_nat (maxz_list dists)) v)
                 v1 x (Z.to_nat (maxz_list dists)) cm Hsave0 H1 Hfmc H3).
    by rewrite -H3.
  - exact: (IH fm (PVM.add hd (Z.to_nat (maxz_list dists)) v) v1 x cm Hsave0 Hin Hfmc).
Qed.

(* 已被加强版 save_longest_dist_correct（dominates_at 方案）取代，原证明思路废弃。 *)

(* 加强版 save_longest_dist_correct：
   由于 lhs 不在 sc 中的约束在 v1 中保持 v0 值（可能为 None），
   且 rhs 值与 fm 最长路径的关系需要图论性质，原陈述不可证。
   这里把两个关键性质作为显式前提：
   - 所有约束的 lhs 都在 sc 中（保证 sl_find_in 适用）；
   - dominates_at：对每条约束，rhs 在 v1 下的值不超过 lhs 在 fm 中
     最长路径距离（这正是满足 satisfies_constraint1' 所需的比较）。 *)
Definition dominates_at (c : Constraint1) (v : Valuation) (fm : adj_matrix) : Prop :=
  match PVM.find (lhs_var1 c) fm with
  | Some cm => (rhs_value1' v c <=? Z.of_nat (Z.to_nat (maxz_list (split (NVM.elements cm)).2)))%Z = true
  | None => True
  end.

Lemma save_longest_dist_correct : forall cs sc fm v0 v1,
    conform1_m cs fm ->
    (forall c, In c cs -> In (lhs_var1 c) sc) ->
    (forall c, In c cs -> dominates_at c v1 fm) ->
    save_longest_dist sc fm v0 = Some v1 ->
    satisfies_all_constraint1 v1 cs.
Proof.
  elim => [|hd tl IH] sc fm v0 v1 Hconf Hlhs Hdom Hsave; first done.
  rewrite /=. apply/andP. split.
  - have Hhd : In hd (hd :: tl) by left.
    rewrite /satisfies_constraint1'.
    move: (Hconf hd Hhd) => [[cm Hcm] Hrhs].
    have Hfind := (@sl_find_in sc fm v0 v1 (lhs_var1 hd) cm Hsave (Hlhs hd Hhd) Hcm).
    rewrite Hfind.
    have Hdm := Hdom hd Hhd. rewrite /dominates_at Hcm in Hdm.
    exact: Hdm.
  - apply (IH sc fm v0 v1) => //.
    + move => c Hc. exact: (Hconf c (or_intror Hc)).
    + move => c Hc. exact: (Hlhs c (or_intror Hc)).
    + move => c Hc. exact: (Hdom c (or_intror Hc)).
Qed.

(*Lemma find_val_save_longest_dist : forall sc cs v0 val dst,
    
    save_longest_dist sc (floyd_loop_map' sc cs) v0 = Some val ->
    forall s, In s sc -> PVM.find s  (floyd_loop_map' sc cs) = Some dst ->
              PVM.find s val = Some (Z.to_nat (maxz_list (split (NVM.elements dst)).2)).
Proof.
Admitted.*)

Fixpoint negcycb (simple_cycle : list ProdVar.t) m b : bool :=
  match simple_cycle with
  | nil => b
  | hd :: tl => negcycb tl m (b && (match (get_weight hd (Node hd) m) with
                 | None => false
                 | Some w => Z.eqb w 0%Z
                 end))
  end.

Definition solve_simple_cycle (simple_cycle : list ProdVar.t) (cs : list Constraint1) : option Valuation :=
  let m := floyd_loop_map' simple_cycle cs in
  (* 矩阵中，从自己回到自己的最长路径，依然是0(初始化时为0，每次更新取max)，则不存在正环 *)
  if negcycb simple_cycle m true
  then
    save_longest_dist simple_cycle m initial_valuation
  else None.

Definition solve_simple_cycle' (simple_cycle : list ProdVar.t) (cs : list Constraint1) v0 : option Valuation :=
  let m := floyd_loop_map' simple_cycle cs in
  (* 矩阵中，从自己回到自己的最长路径，依然是0(初始化时为0，每次更新取max)，则不存在正环 *)
  if negcycb simple_cycle m true
  then
    save_longest_dist simple_cycle m v0
  else None.

Lemma solve_simple_cycle_eq : forall sc cs ,
    solve_simple_cycle' sc cs initial_valuation =
      solve_simple_cycle sc cs.
Proof.
  move => sc cs.
  rewrite /solve_simple_cycle'/solve_simple_cycle.
  by [].
Qed.

End simplecycle.

Lemma solve_simple_cycle_correctness' :
  forall sc cs v0 val,
    (* In_fm v0 (floyd_loop_map' sc cs) -> *)
    conform1_m cs (floyd_loop_map' sc cs) ->
    (forall c, In c cs -> In (lhs_var1 c) sc) ->
    (forall c, In c cs -> dominates_at c val (floyd_loop_map' sc cs)) ->
    solve_simple_cycle' sc cs v0 = Some val ->
    satisfies_all_constraint1 val cs.
Proof.
  move => sc cs v0 val (*Hin*) Hconf Hlhs Hdom.
  rewrite /solve_simple_cycle'.
  case Hpos : (negcycb sc (floyd_loop_map' sc cs) true); last done.
  move => Hsve.
  exact: (@save_longest_dist_correct cs sc (floyd_loop_map' sc cs) v0 val Hconf Hlhs Hdom Hsve).
Qed.

Lemma solve_simple_cycle_correctness :
  forall sc cs val,
    (* In_fm v0 (floyd_loop_map' sc cs) -> *)
    conform1_m cs (floyd_loop_map' sc cs) ->
    (forall c, In c cs -> In (lhs_var1 c) sc) ->
    (forall c, In c cs -> dominates_at c val (floyd_loop_map' sc cs)) ->
    solve_simple_cycle sc cs = Some val ->
    satisfies_all_constraint1 val cs.
Proof.
  move => sc cs val (*Hin*) Hconf Hlhs Hdom.
  rewrite -solve_simple_cycle_eq.
  rewrite /solve_simple_cycle'.
  case Hpos : (negcycb sc (floyd_loop_map' sc cs) true); last done.
  move => Hsve.
  exact: (@save_longest_dist_correct cs sc (floyd_loop_map' sc cs) initial_valuation val Hconf Hlhs Hdom Hsve).
Qed.

Definition scc_smallest_prop (fm : adj_matrix) cs1 (ret : option Valuation) :=
  forall (sol : Valuation), well_formed fm cs1 -> ret = Some sol ->
  forall (s : Valuation), 
    satisfies_all_constraint1 s cs1 ->
    le sol s.

Axiom scc_smallest_aux :
  forall (vars : list ProdVar.t) (fm: adj_matrix)
         (cs1 : list Constraint1) ,
    scc_smallest_prop fm cs1 (solve_simple_cycle' vars cs1 initial_valuation).

Lemma scc_smallest' :
    forall (sc : list ProdVar.t) fm
           (cs : list Constraint1) (val : Valuation),
       well_formed fm cs ->
       solve_simple_cycle' sc cs initial_valuation = Some val ->
       forall (s : Valuation), 
         satisfies_all_constraint1 s cs ->
         le val s.
Proof.
  exact scc_smallest_aux.
Qed.

Lemma scc_smallest :
    forall (sc : list ProdVar.t) fm
           (cs : list Constraint1) (val : Valuation),
       well_formed fm cs ->
       solve_simple_cycle sc cs = Some val ->
       forall (s : Valuation), 
         satisfies_all_constraint1 s cs ->
         le val s.
Proof.
  move => sc fm cs val.
  rewrite -solve_simple_cycle_eq. 
  exact : scc_smallest_aux.
Qed.

Axiom scc_none_unsat : forall (cs : list Constraint1) (sc : list ProdVar.t), solve_simple_cycle sc cs = None -> forall v : Valuation, forallb (satisfies_constraint1 v) cs = false.

  
(* Theorem solve_simple_cycle_smallest : *)
(*   forall (sc : list ProdVar.t)  *)
(*          (cs : list Constraint1) (v0 val : Valuation), *)
(*     solve_simple_cycle' sc cs v0 = Some val -> *)
(*     forall (s : Valuation), conform1_m cs (floyd_loop_map' sc cs) /\ *)
(*                               satisfies_all_constraint1 s cs -> *)
(*                             le val s. *)
(* Proof. *)
(*   move => sc cs v0 val . *)
(*   rewrite /solve_simple_cycle'. *)
(*   case Hpos : (negcycb sc (floyd_loop_map' sc cs) true); last done. *)
(*   move : cs sc v0 val Hpos. *)
(*   elim => [|cshd cstl IHm] sc v0 val. *)
(*   - rewrite /=. *)
(*     rewrite /conform1_m/=.  *)
(*     rewrite /floyd_loop_map' /init_dist_map'/=.  *)
(*   - rewrite /=. move => Hneg Hsave s. rewrite /le. *)
(*     rewrite /conform1_m => [[Hin /andP [Hst Hst1]] r]. *)
(*     move => nm Hfdr. *)
(*     have Hincons : In cshd (cshd :: cstl). rewrite /=; by left. *)
(*     move : (Hin cshd Hincons) => [[dm Hdm] Hfd]. *)
(*     have Hinrhs : (In r sc). admit. *)
(*     have Hinx : (In r (rhs_vars1 cshd)). admit. *)
(*     move : (Hfd r Hinx) => [dst Hdst]. *)
(*     move : (find_val_save_longest_dist sc (cshd :: cstl) v0 Hsave r Hinrhs Hdst). *)
(*     move : Hst. rewrite /satisfies_constraint1'. *)
(*     case Hfdcshd :( PVM.find (lhs_var1 cshd) s) => [vhd|]; last done. *)
(*     exists (Z.to_nat (maxz_list (split (NVM.elements dst)).2)) . *)
(*     rewrite Hfdr in find_val_save_longest_dist0. *)
(*     injection find_val_save_longest_dist0;  move => Heq. *)
(*     rewrite Heq. *)
(*     split. *)
(*     admit. done. *)
          
(* Admitted. *)
