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


Lemma find_add_neq_z_fm : forall (v a : ProdVar.t) (val : NVM.t Z) (fm : adj_matrix), v <> a -> PVM.find v (PVM.add a val fm) = PVM.find v fm.
 (* find_add_None *)
Proof.
Admitted.

Lemma find_add_neq_z : forall (v a : NodeVar.t) (val : Z) (fm : NVM.t Z), v <> a -> NVM.find v (NVM.add a val fm) = NVM.find v fm.
 (* find_add_None *)
Proof.
Admitted.

Lemma find_add_eq_z_fm : forall (a : ProdVar.t) (val : NVM.t Z) (fm : adj_matrix), PVM.find a (PVM.add a val fm) = Some val.
 (* find_add_None *)
Proof.
Admitted.

Lemma find_add_eq_z : forall (a : NodeVar.t) (val : Z) (fm : NVM.t Z), NVM.find a (NVM.add a val fm) = Some val.
Proof.
Admitted.


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

Axiom find_empty_None : forall [A : Type] s, PVM.find s (PVM.empty A) = None.

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

Lemma add_edge_of_c_find_edge : forall c c' fm ml ml0 v ,
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
Admitted.

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

Lemma add_edge_of_c_nn_nn : forall c c' v fm dm0 dm,
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
Admitted.

Lemma add_edge_of_c_s_find_edge : forall cs c fm ml v ,
    In c cs ->
    (rhs_terms1 c) = [(1, v)] ->
    ~ PVM.find (lhs_var1 c) fm = None ->
    PVM.find (lhs_var1 c) (add_edge_of_c_s cs fm) = Some ml ->
    ~ NVM.find (Node v) ml = None.
Proof.
  elim => [|csh cst IHm] c fm ml v ; first done.
  move => Hin; rewrite /= in Hin; move : Hin => [Hin|Hintl] Hrhst Hn0. 
  - rewrite /= Hin. move => Hnn.
    have Hn1: (PVM.find (lhs_var1 c) (add_edge_of_c_s cst fm) <> None).
    by apply add_edge_of_c_s_find_map.
    exact : (add_edge_of_c_find_edge'' c (add_edge_of_c_s cst fm) Hrhst Hn1 Hnn).
  - rewrite /=. move => Hnn.
    rewrite add_edge_of_c_s_same in Hnn.
    apply IHm with c (add_edge_of_c csh fm); try done.
    by apply add_edge_of_c_find_map.
Qed.

Lemma add_edge_of_c_s_find_edge' : forall cs c fm ml0 ml v ,
    (* (rhs_terms1 c) = [(1, v)] -> *)
    PVM.find c fm = Some ml0 ->
    ~ NVM.find (Node v) ml0 = None ->
    PVM.find  c (add_edge_of_c_s cs fm) = Some ml ->
    ~ NVM.find (Node v) ml = None.
Proof.
Admitted.

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

Lemma add_edge_of_c_s_nn_max0 : forall c fm ml0 s cst ml1,
    PVM.find c fm = Some ml0 ->
    NVM.find (Node s) ml0 = None ->
    PVM.find c (add_edge_of_c_s cst fm) = Some ml1 ->
    NVM.find (Node s) ml1 = None ->
    max_const1 c s cst = Z0.
Proof. Admitted.

Lemma add_edge_of_c_s_correct2 : forall cs c s fm ml0 ml dst,
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
Qed.
  
Lemma add_edge_of_c_s_correct_map0 : forall cs c s nds ml0 ml dst,
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
Qed.


  
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

Lemma add_edge_of_cs_correct1 : forall cs c s fm ml0 ml dst0 dst,
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
Admitted.
  
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
                     | Zero => false
                     end
  | Zero :: tl => match a with
                  | Zero => in_bool_n a tl
                  | _ => false
                  end
  end.

Lemma In_in_bool_n : forall a l, in_bool_n a l <-> In a l.
Proof.
Admitted.

Lemma nodup_addzero : forall j ntl,
    NoDup ntl -> ~ In (j) ntl -> 
    NoDup [:: Zero, Node j & map [eta Node] ntl].
Proof.
Admitted.

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
Admitted.

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

Lemma inner_loop1_correct1 : forall nds i m k j ml0 mln dik0 dkj0 (* dkk0 *) dikn dkjn (* dkkn *) dij0 dijn,
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
Admitted.



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

      
Lemma find_new_dst_map_some : forall n dm dst0 ntl s d m,
  NVM.find n dm = Some dst0 ->
  NVM.find n (new_dst_map ntl dm s d m) = None -> False.
Proof.
Admitted.

Lemma pfind_floyd_update_some : forall d m ml0 i nhd ntl,
  PVM.find d m = Some ml0 ->
  PVM.find d (floyd_update' i nhd ntl m) = None -> False.
Proof.
Admitted.
  
Lemma find_floyd_update_some : forall d m ml0 i nhd ntl fu1 s dst,
    PVM.find d m = Some ml0 ->
    PVM.find d (floyd_update' i nhd ntl m) = Some fu1 ->
    NVM.find s ml0 = Some dst ->
    NVM.find s fu1 = None -> False.
Proof.
Admitted.

Lemma pfind_innedr_loop1_some :forall d m ml0 nhd ntl,
  PVM.find d m = Some ml0 ->
  PVM.find d (inner_loop1 ntl m nhd) = None -> False.
Proof.
Admitted.

Lemma find_inner_loop1_some : forall d m ml0 nhd ntl vin1 s dst0,
  PVM.find d m = Some ml0 ->
  PVM.find d (inner_loop1 ntl m nhd) = Some vin1 ->
  NVM.find s ml0 = Some dst0 ->
  NVM.find s vin1 = None -> False.
Proof.
Admitted.
  
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

Lemma in_init_dist_map : forall nds s cs ml0,
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
Admitted.

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
Proof. Admitted.

Definition well_formed (m : adj_matrix) (cs1 : list Constraint1) :=
  (* well_defined_m m /\  *)conform1_m cs1 m.


Lemma satisfies_constraint1_add_maxzlist :
  forall c s fm cm a dist v0,
    PVM.find (lhs_var1 c) fm = Some cm ->
    rhs_terms1 c = [(1,s)] -> (rhs_power c) = nil ->
    (rhs_const1 c <=? Z.of_nat (Z.to_nat (maxz_list dist)))%Z ->
    split (NVM.elements cm) = (a, dist) ->
    PVM.find (lhs_var1 c) v0 = None ->
    satisfies_constraint1' (PVM.add (lhs_var1 c) (Z.to_nat (maxz_list dist)) v0) c.
Proof.
  move => c s fm cm a dist v0 Hfdc Hrhs Hrhsp Hle Hspl Hcv0 .
  rewrite /satisfies_constraint1' find_add_eq /rhs_value1' Hrhs/=.
  rewrite /terms_value_aux/= mul1n.
  case Hs : (PVM.find s (PVM.add (lhs_var1 c) (Z.to_nat (maxz_list dist)) v0) ) => [vs|].
  -  admit.
  -rewrite Z.add_0_r.

Admitted.

Lemma satisfies_all_constraint1_add_maxzlist :
  forall cs dist c s fm schm a v0 ,
    In c cs ->
    rhs_terms1 c = [(1,s)] -> (rhs_power c) = nil ->
    (rhs_const1 c <=? Z.of_nat (Z.to_nat (maxz_list dist)))%Z ->
    PVM.find (lhs_var1 c) fm = Some schm ->
    split (NVM.elements schm) = (a, dist) ->
    PVM.find (lhs_var1 c) v0 = None ->
    ~ (satisfies_all_constraint1 v0 cs) ->
    satisfies_all_constraint1
      (PVM.add (lhs_var1 c) (Z.to_nat (maxz_list dist)) v0) cs.
Proof.
  elim => [|cshd cstl Hm] dst c s fm schm a v0 Hin Hrhs Hrhsp Hrhsc Hcf Hfdsch Hfdnn (* Hnn *) ; first done . 
  - rewrite/=. move/negP => Hst. rewrite negb_andb in Hst.
    move/orP : Hst => [Hsthd|Hsttl].
    move : Hsthd. rewrite /satisfies_constraint1'.
    case Hcshd : (PVM.find (lhs_var1 cshd) v0) => [hd|].
    +      rewrite /=in Hin. move : Hin => [Heq |Hin]. 
      * 
  (*     intro; rewrite H eq_refl // in Hvareq. *)
  (* - apply Hm with fm schm a; try done. admit.  *)
    (* case Hvareq : (lhs_var1 csh == sch). *)
    (* + rewrite (eqP Hvareq) find_add_eq. *)
    (*   move : (Hin sch schm Hfdsch ) => [ x [Hfd0 Hv0]]. *)
    (*   rewrite Had/= in Hv0. *)
      (* rewrite Hfd0 (* ZifyInst.of_nat_to_nat_eq *). move => Hrhsv0.  *)
      (* have Haux : (rhs_value1 v0 csh  <=? rhs_value1 (PVM.add sch (Z.to_nat (maxz_list dst)) v0) csh )%Z. *)
      (* apply smaller_rhs_value. rewrite /smaller_valuation. *)
      (* move => v Hmem. *)
      (* case Hvscheq : (v == sch). *)
      (* * rewrite (eqP Hvscheq).  *)
      (*   exists x, (Z.to_nat (maxz_list dst)). *)
      (*   rewrite find_add_eq Hfd0 Hv0 Nat2Z.id//.  *)
      (* * rewrite -find_mem in Hmem. move : Hmem => [val Hmem]. *)
      (*   move : Hmem. *)
      (*   rewrite find_add_neq. move => Hmem.  *)
      (*   exists val, val. rewrite Hmem//. *)
      (*   intro. rewrite H eq_refl //in Hvscheq. *)
      (* move => var Hinv.  *)
      (* admit. *)
      (* move : (Zle_bool_trans _ _ _ Haux Hrhsv0) => Hle. *)
Admitted.

Lemma save_longest_dist_correct : forall cs sc fm v0 v1,
    conform1_m cs fm ->
    save_longest_dist sc fm v0 = Some v1 ->
    satisfies_all_constraint1 v1 cs.
Proof.
  elim => [|schd sctl Hm] cs fm v0 v1 Hin Hst; rewrite /=//. 
  - apply/andP. split.
    move : Hst. 
    admit.
  - apply Hm with cs fm v0; try done.
    by apply conform1_m_back with schd.
    
    (* rewrite /save_longest_dist in Hst. *)
    (* rewrite /conform1_m in Hin. *)
    (* move => Hx; injection Hx; move => Heq'; rewrite -Heq'//.  *)
    (* case Hfschd : (PVM.find schd fm ) => [vfm|]; last done. *)
    (* case Hspl : (split (NVM.elements vfm)) => [a dst]. *)
    (* apply Hm; try done. *)
    (* apply satisfies_all_constraint1_add_maxzlist with fm vfm a; try done. *)
(* Qed.                            (*  *) *)
Admitted.

Lemma find_val_save_longest_dist : forall sc cs v0 val dst,
    
    save_longest_dist sc (floyd_loop_map' sc cs) v0 = Some val ->
    forall s, In s sc -> PVM.find s  (floyd_loop_map' sc cs) = Some dst ->
              PVM.find s val = Some (Z.to_nat (maxz_list (split (NVM.elements dst)).2)).
Proof.
Admitted.
        
Definition solve_simple_cycle (simple_cycle : list ProdVar.t) (cs : list Constraint1) : option Valuation :=
  let m := floyd_loop_map simple_cycle cs in
  (* 矩阵中，从自己回到自己的最长路径，依然是0(初始化时为0，每次更新取max)，则不存在正环 *)
  if (forallb (fun c => match get_weight c (Node c) m with
                          None => false
                        | Some w => Z.eqb w 0%Z end) simple_cycle)
  then
    save_longest_dist simple_cycle m initial_valuation
  else None.

Fixpoint negcycb (simple_cycle : list ProdVar.t) m b : bool :=
  match simple_cycle with
  | nil => b
  | hd :: tl => negcycb tl m (b && (match (get_weight hd (Node hd) m) with
                 | None => false
                 | Some w => Z.eqb w 0%Z
                 end))
  end.

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
Admitted.

End simplecycle.

Lemma solve_simple_cycle_correctness' :
  forall sc cs v0 val,
    (* In_fm v0 (floyd_loop_map' sc cs) -> *)
    conform1_m cs (floyd_loop_map' sc cs) ->
    solve_simple_cycle' sc cs v0 = Some val ->
    satisfies_all_constraint1 val cs.
Proof.
  move => sc cs v0 val (*Hin*).
  rewrite /solve_simple_cycle'.
  case Hpos : (negcycb sc (floyd_loop_map' sc cs) true); last done.
  move => Hinval Hsve.
  exact: (save_longest_dist_correct sc v0 Hinval Hsve).
Qed.


Lemma solve_simple_cycle_correctness :
  forall sc cs val,
    (* In_fm v0 (floyd_loop_map' sc cs) -> *)
    conform1_m cs (floyd_loop_map' sc cs) ->
    solve_simple_cycle sc cs = Some val ->
    satisfies_all_constraint1 val cs.
Proof.
  move => sc cs val (*Hin*).
  rewrite -solve_simple_cycle_eq.
  rewrite /solve_simple_cycle'.
  case Hpos : (negcycb sc (floyd_loop_map' sc cs) true); last done.
  move => Hinval Hsve.
  exact: (save_longest_dist_correct sc initial_valuation Hinval Hsve).
Qed.

Definition scc_smallest_prop (fm : adj_matrix) cs1 (ret : option Valuation) :=
  forall (sol : Valuation), well_formed fm cs1 -> ret = Some sol ->
  forall (s : Valuation), 
    satisfies_all_constraint1 s cs1 ->
    le sol s.

Lemma scc_smallest_aux :
  forall (vars : list ProdVar.t) (fm: adj_matrix)
         (cs1 : list Constraint1) ,
    scc_smallest_prop fm cs1 (solve_simple_cycle' vars cs1 initial_valuation).
Proof.
  elim => [|n ns IHm]. 
  
Admitted.

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

Lemma scc_none_unsat cs : forall sc, solve_simple_cycle sc cs = None -> forall v : Valuation, forallb (satisfies_constraint1 v) cs = false.
Proof.
(* Added by KY *)
Admitted.

  
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
