From mathcomp Require Import all_ssreflect.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From Solver Require Import Env LoFirrtl HiEnv HiFirrtl constraints scc.
Require Import Coq.Bool.Bool.
From mathcomp.tarjan Require Import kosaraju.
Require Import Program.
Require Import Recdef.
Import ListNotations.
(* From Equations Require Import Equations. *)
(* Require Import Arith Lia. *)


Set Implicit Arguments.
(*Unset Strict Implicit.*) 
Import Prenex Implicits.

Lemma leq_mean : forall (a b : nat), a <= b -> a <= (a + b) / 2.
Proof.
  move => a b Hle.
  have {1}-> : a = (a + a) / 2 by rewrite addnn -muln2 Nat.div_mul.
  apply /leP. apply Nat.div_le_mono; first done.
  apply /leP. by rewrite leq_add2l.
Qed.

Lemma mean_leq : forall (a b : nat), a <= b -> (a + b) / 2 <= b.
Proof.
  move => a b Hle.
  have {2}-> : b = (b + b) / 2 by rewrite addnn -muln2 Nat.div_mul.
  apply /leP. apply Nat.div_le_mono; first done.
  apply /leP. by rewrite leq_add2r.
Qed.

Lemma mean_ltn : forall (a b : nat), a < b -> (a + b) / 2 < b.
Proof.
  move => a b Hlt.
  rewrite ltn_neqAle. apply /andP. split.
  - apply /eqP => Heq. Check Nat.div_mul. Check divn2. Search divn (_ / _)%nat. Search (_ <= _ / _)%coq_nat.
    have Hba : b <= a.
    {
      rewrite -(leq_add2r b). rewrite addnn -mul2n.
      rewrite -{1}Heq. apply /leP. exact: Nat.mul_div_le.
    }
    rewrite leqNgt in Hba. by rewrite Hlt in Hba.
  - apply mean_leq. by intuition.
Qed.

  
Section Bounds.

(* 定义对于上下界的类型 *)
Definition Bounds := PVM.t (nat * nat).
Definition initial_bounds := PVM.empty (nat * nat).
Definition add_bound := PVM.add.
Definition mergeValuations (v1 v2 : Valuation) : Bounds :=
  PVM.map2 (fun x y => match x,y with
    | Some lb, Some ub => Some (lb, ub)
    | _, _ => None
    end) v1 v2.

(*Definition Bounds := V -> (nat * nat).
Definition initial_bounds : Bounds := fun _ => (0, 0).
Definition add_bound (s : Bounds) (x : V) (v : nat * nat) :=
  fun n => if n == x then v else s n.

(* 合并两个 Valuation 为一个 Bounds *)
Definition mergeValuations (v1 v2 : Valuation V) : Bounds :=
  fun x =>
    let val1 := v1 x in
    let val2 := v2 x in
    if (val1 <=? val2) then (val1, val2)  (* 对于无值情况 *)
    else (0, 0).   有值的情况 *)


(* =================== product_bounds =================== *)

Definition product_bounds (bounds : Bounds) : nat :=
  let eles := PVM.elements bounds in
  fold_left (fun acc '(v, bs) =>
               let '(lb, ub) := bs in
               acc + (ub - lb))
            eles 0.

Definition product_bounds_ifold (l : list (ProdVar.t * (nat * nat))) (init : nat) : nat :=
  fold_left (fun acc '(v, bs) =>
               let '(lb, ub) := bs in
               acc + (ub - lb))
    l init.

Lemma product_bounds_equation : forall (bds : Bounds),
  product_bounds bds = product_bounds_ifold (PVM.elements bds) 0.
Proof. done. Qed.

Lemma product_bounds_ifold_addn : forall (l : list (ProdVar.t * (nat * nat))) (m n : nat),
    product_bounds_ifold l (m + n) = (product_bounds_ifold l m) + n.
Proof.
  elim => [|[xhd [lbhd ubhd]] l IHl]; first done.
  rewrite /= => m n.
  rewrite -addnA (addnC n) addnA //=.
Qed.

Lemma product_bounds_ifold_eq : forall (l : list (ProdVar.t * (nat * nat))) (init : nat),
    product_bounds_ifold l init = init ->
    forall (x : ProdVar.t) (lb ub : nat), List.In (x, (lb, ub)) l -> ub - lb = 0.
Proof.
  elim => [|[xhd [lbhd ubhd]] l IHl]; first done.
  rewrite /= => init.
  rewrite addnC -(add0n (_ + init)). 
  rewrite product_bounds_ifold_addn.
  rewrite addnA -{2}(add0n init).
  rewrite Nat.add_cancel_r Nat.eq_add_0 => H x lb ub. move: H => [Hl Hhd].
  move => [[_ <- <-] | Hin].
  - done.
  - exact: (IHl _ Hl _ _ _ Hin).
Qed.


(* =================== length =================== *)

Definition length (x : ProdVar.t) (bds : Bounds) : nat :=
  match PVM.find x bds with
  | Some (lb, ub) => (ub - lb) 
  | None => 0
  end.

Lemma length_not0_neq : forall x bds lb ub,
    length x bds != 0 -> PVM.find x bds = Some (lb, ub) -> lb <> ub.
Proof.
  move => x bds lb ub. rewrite /length => Hlen Hfind. rewrite Hfind in Hlen.
  move => Heq. rewrite Heq /= in Hlen.
  have H0 : ub - ub = 0 by intuition.
  rewrite H0 in Hlen. done.
Qed.

Lemma length0_ge : forall x bds lb ub,
    length x bds = 0 -> PVM.find x bds = Some (lb, ub) -> lb >= ub.
Proof.
  move => x bds lb ub. rewrite /length => Hlen Hfind. rewrite Hfind in Hlen.
  move: Hlen => /eqP Hlen. by rewrite -subn_eq0.
Qed.

Lemma length_not0_ex : forall x bds,
    length x bds != 0 -> (exists lb ub, PVM.find x bds = Some (lb, ub)).
Proof.
  move => x bds. rewrite /length.
  case Hfind : (PVM.find x bds) => [[lb ub]|]; last by discriminate.
  move => Hneq. by exists lb, ub.
Qed.

Lemma find_some_length_not0_neq : forall vs bds v lb ub,
    find (fun x : ProdVar.t => length x bds != 0) vs = Some v ->
    PVM.find v bds = Some (lb, ub) -> lb <> ub.
Proof.
  move => vs bds v lb ub Hfind.
  move: (find_some _ _ Hfind) => [_ Hlen].
  by apply length_not0_neq.
Qed.

Lemma find_some_length_not0_ex : forall vs bds v,
    find (fun x : ProdVar.t => length x bds != 0) vs = Some v ->
    (exists lb ub, PVM.find v bds = Some (lb, ub)).
Proof.
  move => vs bds v Hfind.
  move: (find_some _ _ Hfind) => [_ Hlen].
  by apply length_not0_ex.
Qed.

Lemma find_none_length_not0_all0 : forall vs bds,
    find (fun x : ProdVar.t => length x bds != 0) vs = None ->
    forall v, In v vs -> length v bds = 0.
Proof.
  move => vs bds Hfind. move: (find_none _ _ Hfind) => H v Hin.
  move: (H v Hin). by move=> /eqP Hlen.
Qed.

Lemma product0_length0 : forall (bds : Bounds),
    product_bounds bds = 0 -> forall x, length x bds = 0.
Proof.
  move => bds.
  rewrite (product_bounds_equation) /length => Hprd x.
  move: (product_bounds_ifold_eq _ Hprd) => H.
  case Hfxbds : (PVM.find x bds) => [[lb ub]|]; last done.
  apply (H x). by apply find_in_elements.
Qed.


(* =================== halve =================== *)

(* take the lower half of _bds_ *)
Definition halve (bds : Bounds) : Bounds :=
  PVM.map (fun '(lb,ub) => (lb, (lb + ub)/2)) bds.

Lemma find_none_halve : forall (x : ProdVar.t) (bds : Bounds),
    PVM.find x bds = None -> PVM.find x (halve bds) = None.
Proof.
  move => x bds H. rewrite /halve. by apply find_none_map.
Qed.

Lemma find_some_halve : forall (x : ProdVar.t) (bds : Bounds) (lb ub : nat),
    PVM.find x bds = Some (lb, ub) -> PVM.find x (halve bds) = Some (lb, (lb + ub)/2).
Proof.
  move => x bds lb ub H. rewrite /halve.
  set f := (fun '(lb0, ub0) => (lb0, (lb0 + ub0) / 2)).
  have Heq : f (lb, ub) = (lb, (lb + ub) / 2) by trivial.
  rewrite -Heq. by apply find_some_map.
Qed.

Lemma find_halve_none : forall (x : ProdVar.t) (bds : Bounds),
    PVM.find x (halve bds) = None -> PVM.find x bds = None.
Proof.
  rewrite /halve => x bds H. by apply (find_map_none H).
Qed.

Lemma find_halve_some : forall (x : ProdVar.t) (bds : Bounds) (lb ub : nat),
    PVM.find x (halve bds) = Some (lb, ub) ->
    exists ub', ub = (lb + ub') / 2 /\ PVM.find x bds = Some (lb, ub').
Proof.
  move => x bds lb ub H. move: (find_map_some H) => [[a b] Hex].
  move: Hex => [[<- Hub] Hfind]. by exists b.
Qed.


(* =================== update bounds =================== *)

(* 修改x的上界为v *)
Definition update_ub (s : Bounds) (x : ProdVar.t) (v : nat) :=
  match PVM.find x s with
  | Some (lb, _) => PVM.add x (lb, v) s 
  | _ => s 
  end.

(* 修改x的下界为v *)
Definition update_lb (s : Bounds) (x : ProdVar.t) (v : nat) :=
  match PVM.find x s with
  | Some (_, ub) => PVM.add x (v, ub) s 
  | _ => s 
  end.


(* =================== well_defined =================== *)

Definition well_defined (bds : Bounds) : Prop :=
  forall (x : ProdVar.t) (lb ub : nat), PVM.find x bds = Some (lb, ub) -> lb <= ub.

Lemma wd_halve : forall (bds : Bounds), well_defined bds -> well_defined (halve bds).
Proof.  
  rewrite /well_defined => bds H x lb ub Hfh.
  move: (find_halve_some _ _ Hfh) => [ub' [Heq Hf]].
  rewrite Heq. apply H in Hf. by apply leq_mean.
Qed.

Lemma length0_wd_eq : forall x bds lb ub,
    length x bds = 0 -> PVM.find x bds = Some (lb, ub) -> well_defined bds -> lb = ub.
Proof.
  move => x bds lb ub Hlen Hf. rewrite /well_defined => Hwd.
  move: (length0_ge _ _ Hlen Hf) => Hge.
  move: (Hwd _ _ _ Hf) => Hle.
  apply /eqP. rewrite eqn_leq. by intuition.
Qed.

Lemma wd_update_ub : forall (bds : Bounds) (x : ProdVar.t) (lb ub : nat),
    well_defined bds -> PVM.find x bds = Some (lb, ub) ->
    well_defined (update_ub bds x ((lb + ub) / 2)).
Proof.
  move => bds x lb ub Hwd Hfxbds.
  rewrite /well_defined /update_ub Hfxbds => y lby uby.
  move: (eq_dec y x) => [-> | Hneq].
  - rewrite HiFirrtl.find_add_eq => [[<- <-]].
    apply leq_mean. exact: (Hwd _ _ _ Hfxbds).
  - rewrite (HiFirrtl.find_add_neq Hneq) => Hfybds.
    exact: (Hwd _ _ _ Hfybds).
Qed.

Lemma wd_update_lb : forall (bds : Bounds) (x : ProdVar.t) (lb ub : nat),
    well_defined bds -> PVM.find x bds = Some (lb, ub) -> lb <> ub ->
    well_defined (update_lb bds x ((lb + ub) / 2).+1).
Proof.
  move => bds x lb ub Hwd Hfxbds Hlbub.
  rewrite /well_defined /update_lb Hfxbds => y lby uby.
  move: (eq_dec y x) => [-> | Hneq].
  - rewrite HiFirrtl.find_add_eq => [[<- <-]].
    apply mean_ltn.
    rewrite ltn_neqAle. apply /andP. split; last exact: (Hwd _ _ _ Hfxbds).
    by apply /eqP.
  - rewrite (HiFirrtl.find_add_neq Hneq) => Hfybds.
    exact: (Hwd _ _ _ Hfybds).
Qed.


(* =================== In v bds =================== *)

(* [In v bds] means: forall x in dom(bds), v(x) \in bds(x) *)
(* v can contain more variables than bds. *)
(* Variables that are not in bds are unbounded. *)
Definition In (v : Valuation) (bds : Bounds) : Prop :=
  forall (x : ProdVar.t) (lb ub : nat),
    PVM.find x bds = Some (lb, ub) ->
    (exists n, PVM.find x v = Some n /\ lb <= n /\ n <= ub).

Lemma in_wd : forall (bds : Bounds) (v : Valuation), In v bds -> well_defined bds.
Proof.
  rewrite /In /well_defined => bds v H x lb ub Hfxbds.
  move: (H _ _ _ Hfxbds) => [n [Hfxv [Hlbn Hnub]]].
  by apply (leq_trans Hlbn).
Qed.

Lemma in_bounds_dec : forall (v : Valuation) (bds : Bounds) (x : ProdVar.t) (lb ub : nat),
    well_defined bds ->
    In v bds ->  PVM.find x bds = Some (lb, ub) -> lb <> ub ->
    In v (update_ub bds x ((lb+ub)/2)) \/ In v (update_lb bds x ((lb+ub)/2).+1).
Proof.
  move => v bds x lb ub. rewrite /well_defined /In /update_lb /update_ub => Hwd Hin Hf Hneq.
  rewrite Hf.
  move: (Hin _ _ _ Hf) => [n [Hfxv [Hlbn Hnub]]].
  move: (Hwd _ _ _ Hf) => Hlbub.
  move: (leqVgt n ((lb + ub) / 2)) => /orP [Hle | Hlt].
  - left. move => y lby uby.
    move: (eq_dec x y) => [<- | Hxy].
    + rewrite HiFirrtl.find_add_eq. move => [<- <-].
      by (exists n).
    + apply nesym in Hxy. rewrite (HiFirrtl.find_add_neq Hxy). exact: Hin.
  - right. move => y lby uby.
    move: (eq_dec x y) => [<- | Hxy].
    + rewrite HiFirrtl.find_add_eq. move => [<- <-].
      by (exists n).
    + apply nesym in Hxy. rewrite (HiFirrtl.find_add_neq Hxy). exact: Hin.
Qed.

Lemma length0_in_bounds_eq : forall (x : ProdVar.t) (bds : Bounds) (lb ub : nat) (v v' : Valuation),
    PVM.find x bds = Some (lb, ub) -> length x bds = 0 ->
    well_defined bds -> In v bds -> In v' bds ->
    PVM.find x v = PVM.find x v'.
Proof.
  rewrite /In => x bds lb ub v1 v2 Hfxbds Hlen Hwd Hv1bds Hv2bds.
  move: (length0_wd_eq _ Hlen Hfxbds Hwd) => Heq.
  rewrite Heq in Hfxbds.
  move: (Hv1bds _ _ _ Hfxbds) => [n1 [-> /andP Hn1]].
  move: (Hv2bds _ _ _ Hfxbds) => [n2 [-> /andP Hn2]].
  rewrite -eqn_leq in Hn1. rewrite -eqn_leq in Hn2.
  by move: Hn1 Hn2 => /eqP <- /eqP <-.
Qed.  

Lemma in_halve_in_bounds : forall (bds : Bounds) (v : Valuation),
    well_defined bds -> In v (halve bds) -> In v bds.
Proof.
  rewrite /In => bds v Hwd Hin x lb ub Hfxbds.
  move: (find_some_halve _ _ Hfxbds) => Hfxhbds.
  move: (Hin _ _ _ Hfxhbds) => [n [Hfxv [Hlbn Hnm]]].
  exists n; repeat split; try done.
  move: (Hwd _ _ _ Hfxbds) => Hlbub.
  apply (leq_trans Hnm). exact: mean_leq.
Qed.

Lemma in_update_ub_le :
  forall (bds : Bounds) (v : Valuation) (x : ProdVar.t) (lb ub : nat) (n n' : nat),
    PVM.find x v = Some n -> PVM.find x bds = Some (lb, ub) ->
    In v (update_ub bds x n') -> n <= n'.
Proof.
  rewrite /In /update_ub => bds v x lb ub n1 n2 Hfxv Hfxbds.
  rewrite Hfxbds => Hin.
  move: (Hin x lb n2). rewrite HiFirrtl.find_add_eq => H.
  case: H => [| n H]; first done.
  rewrite Hfxv in H. move: H => [[->] H]. by intuition.
Qed.

Lemma in_update_ub_in_bounds : forall (bds : Bounds) (x : ProdVar.t) (lb ub : nat) (v : Valuation),
    well_defined bds -> PVM.find x bds = Some (lb, ub) ->
    In v (update_ub bds x ((lb + ub) / 2)) -> In v bds.
Proof.
  rewrite /update_ub => bds x lb ub v Hwd Hfxbds.
  rewrite Hfxbds /In => Hin y lby uby.
  move: (eq_dec y x) => [-> Hfxbds' | Hneq Hfybds].
  - move: (Hin x lb ((lb + ub) / 2)).
    rewrite HiFirrtl.find_add_eq => H.
    case: H => [|n [Hfxv [Hlbn Hnm]]]; first done.
    exists n. split; first done.
    move: Hfxbds'. rewrite Hfxbds => [[<- <-]]. split; first done. 
    apply (leq_trans Hnm). apply mean_leq. exact: (Hwd _ _ _ Hfxbds).
  - move: (Hin y lby uby).
    rewrite (HiFirrtl.find_add_neq Hneq) => H.
    case: H => [|n [Hfyv [Hlbyn Hnuby]]]; first done.
    exists n. repeat split; done.
Qed.

Lemma in_update_lb_in_bounds : forall (bds : Bounds) (x : ProdVar.t) (lb ub : nat) (v : Valuation),
    well_defined bds -> PVM.find x bds = Some (lb, ub) -> lb <> ub ->
    In v (update_lb bds x ((lb + ub) / 2).+1) -> In v bds.
Proof.
  rewrite /update_lb => bds x lb ub v Hwd Hfxbds Hlbub.
  rewrite Hfxbds /In => Hin y lby uby.
  move: (eq_dec y x) => [-> Hfxbds' | Hneq Hfybds].
  - move: (Hin x ((lb + ub) / 2).+1 ub).
    rewrite HiFirrtl.find_add_eq => H.
    case: H => [|n [Hfxv [Hlbn Hnm]]]; first done.
    exists n. split; first done.
    move: Hfxbds'. rewrite Hfxbds => [[<- <-]]. split; last done.
    apply ltnW. apply: (@leq_ltn_trans _ _ _ _ Hlbn).
    apply leq_mean. exact: (Hwd _ _ _ Hfxbds).
  - move: (Hin y lby uby).
    rewrite (HiFirrtl.find_add_neq Hneq) => H.
    move: (H Hfybds) => [n [Hfyv [Hlbyn Hnuby]]].
    exists n. repeat split; done.
Qed.


(* =================== key_value =================== *)

(* 生成本轮检查的解 *)
Definition key_value (s : Bounds) : Valuation :=
  PVM.map (fun '(lb,ub) => (lb + ub)/2) s.

Lemma find_none_key_value : forall (x : ProdVar.t) (bds : Bounds),
    PVM.find x bds = None -> PVM.find x (key_value bds) = None.
Proof.
  move => x bds H. rewrite /key_value. by apply find_none_map.
Qed.

Lemma find_some_key_value : forall (x : ProdVar.t) (bds : Bounds) (lb ub : nat),
    PVM.find x bds = Some (lb, ub) -> PVM.find x (key_value bds) = Some ((lb + ub)/2).
Proof.
  move => x bds lb ub H. rewrite /key_value.
  set f := (fun '(lb0, ub0) => (lb0 + ub0) / 2).
  have Heq : f (lb, ub) = (lb + ub) / 2 by trivial.
  rewrite -Heq. by apply find_some_map.
Qed.

Lemma find_key_value_None : forall (x : ProdVar.t) (bds : Bounds),
    PVM.find x (key_value bds) = None -> PVM.find x bds = None.
Proof.
  rewrite /key_value => x bds. by apply find_map_none.
Qed.

Lemma find_key_value_some : forall (x : ProdVar.t) (bds : Bounds) (n : nat),
    PVM.find x (key_value bds) = Some n ->
    exists lb ub, n = (lb + ub) / 2 /\ PVM.find x bds = Some (lb, ub).
Proof.
  rewrite /key_value => x bds n.
  set f := (fun '(lb0, ub0) => (lb0 + ub0) / 2).
  move => H.
  move: (find_map_some H) => [[lb ub] [Heq Hf]].
  exists lb, ub. rewrite Heq //=.
Qed.

Lemma key_value_in_bounds : forall bounds, well_defined bounds -> In (key_value bounds) bounds.
Proof.
  rewrite /well_defined /In /key_value => bds Hwd x lb ub Hfind.
  move: (Hwd _ _ _ Hfind) => Hlbub.
  exists ((lb + ub) / 2); repeat split.
  - set f := (fun '(lb0, ub0) => (lb0 + ub0) / 2).
    have <- : (f (lb, ub) = (lb + ub) / 2) by trivial.
    by apply find_some_map.
  - by apply leq_mean.
  - by apply mean_leq.
Qed.

Lemma key_value_in_halve : forall bounds, well_defined bounds -> In (key_value bounds) (halve bounds).
Proof.
  move => bds Hwd. apply wd_halve in Hwd. rewrite /well_defined in Hwd.
  rewrite /In => x lb ub Hfh. move: (Hwd _ _ _ Hfh) => Hle.
  move: (find_halve_some _ _ Hfh) => [ub' [Hub Hf]].
  exists ub. repeat split; try done.
  rewrite (find_some_key_value _ _ Hf) Hub //=.
Qed.

Lemma in_product0_vars_eq_kv : forall (v : Valuation) (bds : Bounds),
    In v bds -> product_bounds bds = 0 ->
    forall (x : ProdVar.t) (n : nat), PVM.find x (key_value bds) = Some n ->
                                      PVM.find x v = Some n.
Proof.
  move => v bds Hvbds Hbds x n Hfxkv.
  move: (find_key_value_some _ _ Hfxkv) => [lb [ub [Heq Hfxbds]]].
  move: (product0_length0 _ Hbds x) => Hlenx.
  move: (in_wd Hvbds) => Hwd.
  move: (key_value_in_bounds Hwd) => Hkvbds.
  rewrite -Hfxkv. 
  exact: (length0_in_bounds_eq _ Hfxbds Hlenx).
Qed.


End Bounds.


Section WellFormedness.

Definition conform1 (cs : list Constraint1) (bds : Bounds) :=
  forall (c : Constraint1),
    List.In c cs ->
    (exists lb ub, PVM.find (lhs_var1 c) bds = Some (lb, ub)) /\
      (forall x, List.In x (rhs_vars c) -> exists lb ub, PVM.find x bds = Some (lb, ub)).

Definition conform2 (cs : list Constraint2) (bds : Bounds) :=
  forall (c : Constraint2),
    List.In c cs ->
    forall x, List.In x (map snd (rhs_terms2 c)) -> exists lb ub, PVM.find x bds = Some (lb, ub).

Lemma conform1_halve : forall (cs : list Constraint1) (bds : Bounds),
    conform1 cs bds -> conform1 cs (halve bds).
Proof.
  rewrite /conform1 => cs bds Hcf c Hccs.
  move: (Hcf c Hccs) => [Hlv Hrvs]. split.
  - move: Hlv => [lb [ub Hlv]].
    exists lb, ((lb + ub) / 2). exact: find_some_halve.
  - move => x Hx.
    move: (Hrvs x Hx) => [lb [ub Hxbds]].
    exists lb, ((lb + ub) / 2). exact: find_some_halve.
Qed.

Lemma conform2_halve : forall (cs : list Constraint2) (bds : Bounds),
    conform2 cs bds -> conform2 cs (halve bds).
Proof.
  rewrite /conform2 => cs bds Hcf c Hccs x Hx.
  move: (Hcf c Hccs x Hx) => [lb [ub Hxbds]].
  exists lb, ((lb + ub) / 2). exact: find_some_halve.
Qed.

Lemma conform1_update_ub :
  forall (cs : list Constraint1) (bds : Bounds) (x : ProdVar.t) (n : nat),
    conform1 cs bds -> conform1 cs (update_ub bds x n).
Proof.
  rewrite /update_ub => cs bds x n.
  case Hfxbds : (PVM.find x bds) => [[lb ub]|]; last done.
  rewrite /conform1 => Hcf c Hccs.
  move: (Hcf c Hccs) => [Hlv Hrvs]. split.
  - move: (eq_dec (lhs_var1 c) x) => [-> | Hneq].
    + rewrite HiFirrtl.find_add_eq. by (exists lb, n).
    + rewrite (HiFirrtl.find_add_neq Hneq). exact: Hlv.
  - move => y Hy. move: (eq_dec y x) => [-> | Hneq].
    + rewrite HiFirrtl.find_add_eq. by (exists lb, n).
    + rewrite (HiFirrtl.find_add_neq Hneq). exact: Hrvs.
Qed.

Lemma conform1_update_lb :
  forall (cs : list Constraint1) (bds : Bounds) (x : ProdVar.t) (n : nat),
    conform1 cs bds -> conform1 cs (update_lb bds x n).
Proof.
  rewrite /update_lb => cs bds x n.
  case Hfxbds : (PVM.find x bds) => [[lb ub]|]; last done.
  rewrite /conform1 => Hcf c Hccs.
  move: (Hcf c Hccs) => [Hlv Hrvs]. split.
  - move: (eq_dec (lhs_var1 c) x) => [-> | Hneq].
    + rewrite HiFirrtl.find_add_eq. by (exists n, ub).
    + rewrite (HiFirrtl.find_add_neq Hneq). exact: Hlv.
  - move => y Hy. move: (eq_dec y x) => [-> | Hneq].
    + rewrite HiFirrtl.find_add_eq. by (exists n, ub).
    + rewrite (HiFirrtl.find_add_neq Hneq). exact: Hrvs.
Qed.

Lemma conform2_update_ub :
  forall (cs : list Constraint2) (bds : Bounds) (x : ProdVar.t) (n : nat),
    conform2 cs bds -> conform2 cs (update_ub bds x n).
Proof.
  rewrite /update_ub => cs bds x n.
  case Hfxbds : (PVM.find x bds) => [[lb ub]|]; last done.
  rewrite /conform2 => Hcf c Hccs y Hy. move: (eq_dec y x) => [-> | Hneq].
  - rewrite HiFirrtl.find_add_eq. by (exists lb, n).
  - rewrite (HiFirrtl.find_add_neq Hneq). exact: (Hcf c Hccs y Hy).
Qed.

Lemma conform2_update_lb :
  forall (cs : list Constraint2) (bds : Bounds) (x : ProdVar.t) (n : nat),
    conform2 cs bds -> conform2 cs (update_lb bds x n).
Proof.
  rewrite /update_lb => cs bds x n.
  case Hfxbds : (PVM.find x bds) => [[lb ub]|]; last done.
  rewrite /conform2 => Hcf c Hccs y Hy. move: (eq_dec y x) => [-> | Hneq].
  - rewrite HiFirrtl.find_add_eq. by (exists n, ub).
  - rewrite (HiFirrtl.find_add_neq Hneq). exact: (Hcf c Hccs y Hy).
Qed.




Definition well_formed (bds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2) :=
  well_defined bds /\ conform1 cs1 bds /\ conform2 cs2 bds.

Lemma wf_wd : forall (bds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2),
    well_formed bds cs1 cs2 -> well_defined bds.
Proof.
  rewrite /well_formed => bds cs1 cs2 [H _] //=.
Qed.

Lemma wf_find_lhs_ctr1 :
  forall (bds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2) (c : Constraint1),
    well_formed bds cs1 cs2 -> List.In c cs1 ->
    exists lb ub, PVM.find (lhs_var1 c) bds = Some (lb, ub).
Proof.
  rewrite /well_formed => bds cs1 cs2 c [_ [Hcf1 _]] Hccs1.
  move: (Hcf1 _ Hccs1) => [H _]. exact: H.
Qed.

Lemma wf_find_rhs_ctr1 :
  forall (bds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2) (c : Constraint1),
    well_formed bds cs1 cs2 -> List.In c cs1 ->
    forall x, List.In x (rhs_vars c) -> exists lb ub, PVM.find x bds = Some (lb, ub).
Proof.
  rewrite /well_formed => bds cs1 cs2 c [_ [Hcf1 _]] Hccs1.
  move: (Hcf1 _ Hccs1) => [_ H]. exact: H.
Qed.

Lemma wf_find_rhs_ctr2 :
  forall (bds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2) (c : Constraint2),
    well_formed bds cs1 cs2 -> List.In c cs2 ->
    forall x, List.In x (map snd (rhs_terms2 c)) -> exists lb ub, PVM.find x bds = Some (lb, ub).
Proof.
  rewrite /well_formed => bds cs1 cs2 c [_ [_ Hcf2]] Hccs2 x Hx.
  exact: (Hcf2 _ Hccs2 x Hx).
Qed.

Lemma wf_halve : forall (bds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2),
    well_formed bds cs1 cs2 -> well_formed (halve bds) cs1 cs2.
Proof.
  rewrite /well_formed => bds cs1 cs2 [Hwd [Hcf1 Hcf2]]. split; last split.
  - exact: wd_halve.
  - exact: conform1_halve.
  - exact: conform2_halve.
Qed.

Lemma wf_update_ub :
  forall (bds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2)
         (x : ProdVar.t) (lb ub : nat),
    well_formed bds cs1 cs2 -> PVM.find x bds = Some (lb, ub) ->
    well_formed (update_ub bds x ((lb + ub) / 2)) cs1 cs2.
Proof.
  rewrite /well_formed => bds cs1 cs2 x lb ub [Hwd [Hcf1 Hcf2]] Hfxbds.
  split; last split.
  - exact: wd_update_ub.
  - exact: conform1_update_ub.
  - exact: conform2_update_ub.
Qed.

Lemma wf_update_lb :
  forall (bds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2)
         (x : ProdVar.t) (lb ub : nat),
    well_formed bds cs1 cs2 -> PVM.find x bds = Some (lb, ub) -> lb <> ub ->
    well_formed (update_lb bds x ((lb + ub) / 2).+1) cs1 cs2.
Proof.
  rewrite /well_formed => bds cs1 cs2 x lb ub [Hwd [Hcf1 Hcf2]] Hfxbds Hneq.
  split; last split.
  - exact: wd_update_lb.
  - exact: conform1_update_lb.
  - exact: conform2_update_lb.
Qed.


End WellFormedness.


Section bnb.  

(*Fixpoint new_ubs (node : Valuation V) (s : Bounds) (scc : list V) : list Bounds :=
  match scc with
  | nil => nil
  | hd :: tl => if ((s hd).1 == (s hd).2) then new_ubs node s tl
    else let child := update_ub s hd (node hd) in child :: (new_ubs node s tl)
  end.

(* 为不满足的Phi1约束生成新搜索点 *)
Definition new_nodes1 (node : Valuation V) (bounds : Bounds) (c : Constraint1 V) : list Bounds :=
  let lhs := lhs_var1 c in
  let rhs_vars := map snd (rhs_terms1 c) in
  if ((bounds lhs).1 == (bounds lhs).2) then 
    new_ubs node bounds rhs_vars
  else 
    let children := update_lb bounds lhs (node lhs) in
    children :: (new_ubs node bounds rhs_vars).

(* 为不满足的Phi2约束生成新搜索点 *)
Definition new_nodes2 (node : Valuation V) (bounds : Bounds) (c : Constraint2 V) : list Bounds :=
  let rhs_vars := map snd (rhs_terms2 c) in
  new_ubs node bounds rhs_vars.*)


(* 求 option Valuation 的较小值，没有则返回None *)
Definition smaller_solution (v1 v2 : option Valuation) : option Valuation :=
  match v1, v2 with
  | None, _ => v2
  | Some v, None => v1
  | Some v, Some v' => Some (PVM.map2 (fun v1 v2 => match v1, v2 with
                            | Some v1' , Some v2' => Some (minn v1' v2')
                            | _, _ => None
                            end) v v')
  end.

Fixpoint valuation_in (v : Valuation) (vl : list Valuation) : bool :=
  match vl with
  | nil => false
  | hd :: tl => (PVM.equal eqn hd v) || (valuation_in v tl)
  end.



(* =================== termination proofs =================== *)

Lemma product_bounds_helper : forall (l1 : list (ProdVar.t * (nat * nat))) init0 init1, init0 < init1 -> fold_left
  (fun (acc : nat) '(_, bs) => let '(lb0, ub0) := bs in (acc + (ub0 - lb0))) l1
  init0 <
  fold_left
  (fun (acc : nat) '(_, bs) => let '(lb0, ub0) := bs in (acc + (ub0 - lb0))) l1
  init1.
Proof.
  elim. simpl; intros; done.
  simpl; intros. apply H. destruct a as [v [lb0 ub0]]. rewrite (ltn_add2r _ init0 init1) //.
Qed.

Lemma bab_bin_g1 :
  seq.seq ProdVar.t ->
  forall (bounds : Bounds) (cs1 : seq.seq Constraint1),
  seq.seq Constraint2 ->
  forall c1 : Constraint1,
  find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = Some c1 ->
  (product_bounds bounds == 0) = false ->
  forall v : ProdVar.t,
  find (fun x : ProdVar.t => length x bounds != 0) (rhs_vars c1) = Some v ->
  forall (p : nat * nat) (lb ub : nat),
  p = (lb, ub) ->
  PVM.find v bounds = Some (lb, ub) -> (product_bounds (update_lb bounds v ((lb + ub) / 2).+1) < product_bounds bounds)%coq_nat.
Proof.
  intros.
  rewrite /product_bounds /update_lb H3. 
  specialize (elements_add bounds v (((lb + ub) / 2).+1, ub) H3); intro Heles.
  destruct Heles as [l0 [l1 [Hele Hele_add]]].
  rewrite -Hele -Hele_add.
  rewrite fold_left_app. rewrite fold_left_app.
  remember (fold_left
    (fun (acc : nat) '(_, bs) => let '(lb0, ub0) := bs in (acc + (ub0 - lb0)))
    l0 0) as init.
  apply (elimT ltP). 
  apply (product_bounds_helper l1 (init + (ub - ((lb + ub) / 2).+1)) (init + (ub - lb))).
  rewrite ltn_add2l //. apply find_some in H1.
  move : H1 H3; clear. intros [Hin Hlength] Hfind. rewrite /length Hfind in Hlength. assert (lb < ub). move /eqP : Hlength => Hlength.
  specialize (leqVgt ub lb); intro. destruct (ub <= lb) eqn : Hle. rewrite -subn_eq0 in Hle. move /eqP : Hle => Hle. done.
  rewrite orb_false_l in H; done.
  apply ltn_sub2l; try done.
  rewrite -(addn1 ((lb + ub) / 2)). 

  assert (lb = (lb + lb)/2). rewrite addnn -muln2. rewrite Nat.div_mul; auto.
  assert (lb <= (lb + ub) / 2). rewrite {1}H0. apply (introT leP). apply (Nat.div_le_mono (lb + lb) (lb + ub) 2); try done.
    apply (elimT leP). rewrite leq_add2l. intuition.
  specialize (ltnSn ((lb + ub) / 2)); intro. rewrite addn1. move : H1 H2; apply leq_ltn_trans.
Qed.

Lemma bab_bin_g2 :
  seq.seq ProdVar.t ->
  forall (bounds : Bounds) (cs1 : seq.seq Constraint1),
  seq.seq Constraint2 ->
  forall c1 : Constraint1,
  find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = Some c1 ->
  (product_bounds bounds == 0) = false ->
  forall v : ProdVar.t,
  find (fun x : ProdVar.t => length x bounds != 0) (rhs_vars c1) = Some v ->
  forall (p : nat * nat) (lb ub : nat),
  p = (lb, ub) ->
  PVM.find v bounds = Some (lb, ub) -> (product_bounds (update_ub bounds v ((lb + ub) / 2)) < product_bounds bounds)%coq_nat.
Proof.
  intros.
  rewrite /product_bounds /update_ub H3. 
  specialize (elements_add bounds v (lb, (lb + ub) / 2) H3); intro Heles.
  destruct Heles as [l0 [l1 [Hele Hele_add]]].
  rewrite -Hele -Hele_add.
  rewrite fold_left_app. rewrite fold_left_app.
  remember (fold_left
    (fun (acc : nat) '(_, bs) => let '(lb0, ub0) := bs in (acc + (ub0 - lb0)))
    l0 0) as init.
  apply (elimT ltP). 
  apply (product_bounds_helper l1 (init + (((lb + ub) / 2) - lb)) (init + (ub - lb))).
  rewrite ltn_add2l //. apply find_some in H1.
  move : H1 H3; clear. intros [Hin Hlength] Hfind. rewrite /length Hfind in Hlength. assert (lb < ub). move /eqP : Hlength => Hlength.
  specialize (leqVgt ub lb); intro. destruct (ub <= lb) eqn : Hle. rewrite -subn_eq0 in Hle. move /eqP : Hle => Hle. done.
  rewrite orb_false_l in H; done.
  rewrite ltn_sub2rE. specialize (Nat.div_lt_upper_bound (lb + ub) 2 ub); intro. 
    apply (introT ltP). apply H0; try done. apply (elimT ltP). 
    rewrite -(ltn_add2r ub) in H. rewrite addnn -mul2n in H. done.
  assert (lb = (lb + lb)/2) by (rewrite addnn -muln2; rewrite Nat.div_mul; auto).
  rewrite {1}H0; clear H0. apply (introT leP). apply (Nat.div_le_mono (lb + lb) (lb + ub) 2); try done.
  apply (elimT leP). rewrite leq_add2l. intuition.
Qed.

Lemma bab_bin_g3 :
  seq.seq ProdVar.t ->
  forall (bounds : Bounds) (cs1 : seq.seq Constraint1),
  seq.seq Constraint2 ->
  forall c1 : Constraint1,
  find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = Some c1 ->
  (product_bounds bounds == 0) = false ->
  find (fun x : ProdVar.t => length x bounds != 0) (rhs_vars c1) = None ->
  (length (lhs_var1 c1) bounds == 0) = false ->
  forall (p : nat * nat) (lb ub : nat),
  p = (lb, ub) ->
  PVM.find (lhs_var1 c1) bounds = Some (lb, ub) ->
  (product_bounds (update_lb bounds (lhs_var1 c1) ((lb + ub) / 2).+1) < product_bounds bounds)%coq_nat.
Proof.
  intros.
  rewrite /product_bounds /update_lb H4. 
  specialize (elements_add bounds (lhs_var1 c1) (((lb + ub) / 2).+1, ub) H4); intro Heles.
  destruct Heles as [l0 [l1 [Hele Hele_add]]].
  rewrite -Hele -Hele_add.
  rewrite fold_left_app. rewrite fold_left_app.
  remember (fold_left
    (fun (acc : nat) '(_, bs) => let '(lb0, ub0) := bs in (acc + (ub0 - lb0)))
    l0 0) as init.
  apply (elimT ltP). 
  apply (product_bounds_helper l1 (init + (ub - ((lb + ub) / 2).+1)) (init + (ub - lb))).
  rewrite ltn_add2l //. rewrite /length H4 in H2. assert (lb < ub). move /eqP : H2 => H2.
  specialize (leqVgt ub lb); intro. destruct (ub <= lb) eqn : Hle. rewrite -subn_eq0 in Hle. move /eqP : Hle => Hle. done.
  rewrite orb_false_l in H5; done.
  apply ltn_sub2l; try done. 
  rewrite -(addn1 ((lb + ub) / 2)). move : H5; clear; intros.
  
  assert (lb = (lb + lb)/2). rewrite addnn -muln2. rewrite Nat.div_mul; auto.
  assert (lb <= (lb + ub) / 2). rewrite {1}H. apply (introT leP). apply (Nat.div_le_mono (lb + lb) (lb + ub) 2); try done.
    apply (elimT leP). rewrite leq_add2l. intuition.
  specialize (ltnSn ((lb + ub) / 2)); intro. rewrite addn1. move : H0 H1; apply leq_ltn_trans.
Qed.

Lemma bab_bin_g4 :
  seq.seq ProdVar.t ->
  forall (bounds : Bounds) (cs1 : seq.seq Constraint1) (cs2 : seq.seq Constraint2),
  find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = None ->
  forall c2 : Constraint2,
  find (fun c : Constraint2 => ~~ satisfies_constraint2 (key_value bounds) c) cs2 = Some c2 ->
  (product_bounds bounds == 0) = false ->
  forall v : ProdVar.t,
  find (fun x : ProdVar.t => length x bounds != 0) (map snd (rhs_terms2 c2)) = Some v ->
  forall (p : nat * nat) (lb ub : nat),
  p = (lb, ub) ->
  PVM.find v bounds = Some (lb, ub) -> (product_bounds (update_lb bounds v ((lb + ub) / 2).+1) < product_bounds bounds)%coq_nat.
Proof.
  intros.
  rewrite /product_bounds /update_lb H4. 
  specialize (elements_add bounds v (((lb + ub) / 2).+1, ub) H4); intro Heles.
  destruct Heles as [l0 [l1 [Hele Hele_add]]].
  rewrite -Hele -Hele_add.
  rewrite fold_left_app. rewrite fold_left_app.
  remember (fold_left
    (fun (acc : nat) '(_, bs) => let '(lb0, ub0) := bs in (acc + (ub0 - lb0)))
    l0 0) as init.
  apply (elimT ltP). 
  apply (product_bounds_helper l1 (init + (ub - ((lb + ub) / 2).+1)) (init + (ub - lb))).
  rewrite ltn_add2l //. apply find_some in H2.
  move : H2 H4; clear. intros [Hin Hlength] Hfind. rewrite /length Hfind in Hlength. assert (lb < ub). move /eqP : Hlength => Hlength.
  specialize (leqVgt ub lb); intro. destruct (ub <= lb) eqn : Hle. rewrite -subn_eq0 in Hle. move /eqP : Hle => Hle. done.
  rewrite orb_false_l in H; done.

  apply ltn_sub2l; try done. 
  rewrite -(addn1 ((lb + ub) / 2)). move : H; clear; intros.
  
  assert (lb = (lb + lb)/2). rewrite addnn -muln2. rewrite Nat.div_mul; auto.
  assert (lb <= (lb + ub) / 2). rewrite {1}H0. apply (introT leP). apply (Nat.div_le_mono (lb + lb) (lb + ub) 2); try done.
    apply (elimT leP). rewrite leq_add2l. intuition.
  specialize (ltnSn ((lb + ub) / 2)); intro. rewrite addn1. move : H1 H2; apply leq_ltn_trans.
Qed.

Lemma bab_bin_g5 :
  seq.seq ProdVar.t ->
  forall (bounds : Bounds) (cs1 : seq.seq Constraint1) (cs2 : seq.seq Constraint2),
  find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = None ->
  forall c2 : Constraint2,
  find (fun c : Constraint2 => ~~ satisfies_constraint2 (key_value bounds) c) cs2 = Some c2 ->
  (product_bounds bounds == 0) = false ->
  forall v : ProdVar.t,
  find (fun x : ProdVar.t => length x bounds != 0) (map snd (rhs_terms2 c2)) = Some v ->
  forall (p : nat * nat) (lb ub : nat),
  p = (lb, ub) ->
  PVM.find v bounds = Some (lb, ub) -> (product_bounds (update_ub bounds v ((lb + ub) / 2)) < product_bounds bounds)%coq_nat.
Proof.
  intros.
  rewrite /product_bounds /update_ub H4. 
  specialize (elements_add bounds v (lb, (lb + ub) / 2) H4); intro Heles.
  destruct Heles as [l0 [l1 [Hele Hele_add]]].
  rewrite -Hele -Hele_add.
  rewrite fold_left_app. rewrite fold_left_app.
  remember (fold_left
    (fun (acc : nat) '(_, bs) => let '(lb0, ub0) := bs in (acc + (ub0 - lb0)))
    l0 0) as init.
  apply (elimT ltP). 
  apply (product_bounds_helper l1 (init + (((lb + ub) / 2) - lb)) (init + (ub - lb))).
  rewrite ltn_add2l //. apply find_some in H2.
  move : H2 H4; clear. intros [Hin Hlength] Hfind. rewrite /length Hfind in Hlength. assert (lb < ub). move /eqP : Hlength => Hlength.
  specialize (leqVgt ub lb); intro. destruct (ub <= lb) eqn : Hle. rewrite -subn_eq0 in Hle. move /eqP : Hle => Hle. done.
  rewrite orb_false_l in H; done.
  rewrite ltn_sub2rE. specialize (Nat.div_lt_upper_bound (lb + ub) 2 ub); intro. 
    apply (introT ltP). apply H0; try done. apply (elimT ltP). 
    rewrite -(ltn_add2r ub) in H. rewrite addnn -mul2n in H. done.
  assert (lb = (lb + lb)/2) by (rewrite addnn -muln2; rewrite Nat.div_mul; auto).
  rewrite {1}H0; clear H0. apply (introT leP). apply (Nat.div_le_mono (lb + lb) (lb + ub) 2); try done.
  apply (elimT leP). rewrite leq_add2l. intuition.
Qed.

Lemma product_bounds_ifold_zero l init :
  forallb (fun '(v, (lb, ub)) => ub - lb == 0) l ->
  product_bounds_ifold l init = init.
Proof.
  elim: l init => [| [v [lb ub]] l IH] init H_all //=.
  - (* 非空列表 *)
    assert (forall x, List.In x ((v, (lb, ub)) :: l) -> (fun '(_, y) => let '(lb, ub) := y in ub - lb == 0) x = true) by (apply forallb_forall; done).
    specialize (H (v, (lb, ub))); simpl in H.
    assert ((ub - lb == 0) = true) by (apply H; left; done). move /eqP : H0 => H0.
    rewrite H0 addn0.
    apply: IH.
    apply forallb_forall. intros; simpl.
    assert (forall x, List.In x ((v, (lb, ub)) :: l) -> (fun '(_, y) => let '(lb, ub) := y in ub - lb == 0) x = true) by (apply forallb_forall; done).
    apply H2; simpl; right; done.
Qed.

Lemma bab_bin_g6 :
  seq.seq ProdVar.t ->
  forall (bounds : Bounds) (cs1 : seq.seq Constraint1) (cs2 : seq.seq Constraint2),
  find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = None ->
  find (fun c : Constraint2 => ~~ satisfies_constraint2 (key_value bounds) c) cs2 = None ->
  (product_bounds bounds == 0) = false -> (product_bounds (halve bounds) < product_bounds bounds)%coq_nat.
Proof.
  intros.
  rewrite /product_bounds /halve elements_map. 
  assert (exists x, length x bounds != 0). move : H1; clear; intro. 
  { move/eqP: H1 => H_sum_nonzero. 
    assert (~ (product_bounds_ifold (PVM.elements bounds) 0 = 0)). rewrite -product_bounds_equation //.
    apply (contra_not (product_bounds_ifold_zero (PVM.elements bounds) 0)) in H. apply forallb_neg_neg in H. 
    destruct H as [[x [lb ub]] [Hin Hlength]]. unfold length. apply find_in_elements in Hin. exists x; rewrite Hin. 
    unfold "!=". rewrite Hlength //. }
  destruct H2 as [x Hlength]. rewrite /length in Hlength. case Hfind : (PVM.find x bounds) => [[lb ub]|]; rewrite Hfind in Hlength; try done.
  assert (lb < ub). move /eqP : Hlength => Hlength.
    specialize (leqVgt ub lb); intro. destruct (ub <= lb) eqn : Hle. rewrite -subn_eq0 in Hle. move /eqP : Hle => Hle. done.
    rewrite orb_false_l in H2; done.
  remember (fun (acc : nat) '(_, bs) => let '(lb0, ub0) := bs in (acc + (ub0 - lb0))%nat) as f.
  apply find_in_elements in Hfind as Hin.
  apply in_split in Hin. destruct Hin as [l1 [l2 Heles]]. rewrite Heles. rewrite map_app.
  rewrite fold_left_app. rewrite fold_left_app.
  remember (fold_left f
    (map
      (fun '(key, value) =>
        (key,
        let '(lb0, ub0) := value in (lb0, (lb0 + ub0) / 2)))
      l1) 0) as init0. assert (init0 <= (fold_left f l1 0)).
  * rewrite Heqinit0; move : Heqf; clear; intros.
    assert (forall (l1 : seq.seq (PVM.key * (nat * nat))) init0 init1, init0 <= init1 ->
      fold_left f
        (map
          (fun '(key, value) =>
            (key,
            let '(lb0, ub0) := value in (lb0, (lb0 + ub0) / 2)))
          l1) init0 <= fold_left f l1 init1).
    + elim. simpl; intros. done.
      intros [v [lb ub]] tl IH; intros. apply IH; clear IH. rewrite Heqf.
      rewrite -(leq_add2r (ub - lb) init0 init1) in H. move : H; apply leq_trans.
      rewrite leq_add2l. clear. specialize (leqVgt ub lb); intro. destruct (ub <= lb) eqn : Hle.
      - clear H. assert ((lb + ub) / 2 <= lb). 
          assert (lb = (lb + lb)/2) by (rewrite addnn -muln2; rewrite Nat.div_mul; auto).
          rewrite {2}H. apply (introT leP). apply (Nat.div_le_mono (lb + ub) (lb + lb) 2); try done. apply (elimT leP). rewrite leq_add2l. intuition.
        move /eqP : H => H. move /eqP : Hle => Hle. rewrite H Hle //.
      - rewrite orb_false_l in H; clear Hle. assert ((lb + ub) / 2 - lb < ub - lb).
        rewrite ltn_sub2rE. specialize (Nat.div_lt_upper_bound (lb + ub) 2 ub); intro. 
          apply (introT ltP). apply H0; try done. apply (elimT ltP). 
          rewrite -(ltn_add2r ub) in H. rewrite addnn -mul2n in H. done.
        assert (lb = (lb + lb)/2) by (rewrite addnn -muln2; rewrite Nat.div_mul; auto).
        rewrite {1}H0; clear H0. apply (introT leP). apply (Nat.div_le_mono (lb + lb) (lb + ub) 2); try done.
        apply (elimT leP). rewrite leq_add2l. intuition. intuition.
    apply H; done.
  remember (fun '(key, value) =>
    (key, let '(lb0, ub0) := value in (lb0, (lb0 + ub0) / 2))) as f0.
  assert (forall l init0 init1, init0 < init1 -> fold_left f (map f0 l) init0 <
    fold_left f l init1). move : Heqf Heqf0; clear; intros Heqf Heqf0. elim. simpl; intros; done.
  + intros [v [lb ub]] tl IH; intros. apply IH; clear IH. rewrite Heqf Heqf0.
    assert (init0 + ((lb + ub) / 2 - lb) <= init0 + (ub - lb)).
      rewrite leq_add2l. clear. specialize (leqVgt ub lb); intro. destruct (ub <= lb) eqn : Hle.
      - clear H. assert ((lb + ub) / 2 <= lb). 
          assert (lb = (lb + lb)/2) by (rewrite addnn -muln2; rewrite Nat.div_mul; auto).
          rewrite {2}H. apply (introT leP). apply (Nat.div_le_mono (lb + ub) (lb + lb) 2); try done. apply (elimT leP). rewrite leq_add2l. intuition.
        move /eqP : H => H. move /eqP : Hle => Hle. rewrite H Hle //.
      - rewrite orb_false_l in H; clear Hle. assert ((lb + ub) / 2 - lb < ub - lb).
        rewrite ltn_sub2rE. specialize (Nat.div_lt_upper_bound (lb + ub) 2 ub); intro. 
          apply (introT ltP). apply H0; try done. apply (elimT ltP). 
          rewrite -(ltn_add2r ub) in H. rewrite addnn -mul2n in H. done.
        assert (lb = (lb + lb)/2) by (rewrite addnn -muln2; rewrite Nat.div_mul; auto).
        rewrite {1}H0; clear H0. apply (introT leP). apply (Nat.div_le_mono (lb + lb) (lb + ub) 2); try done.
        apply (elimT leP). rewrite leq_add2l. intuition. intuition.
    assert (init0 + (ub - lb) < init1 + (ub - lb)). rewrite ltn_add2r //.
    move : H0 H1; apply leq_ltn_trans.
  simpl. apply (elimT ltP). apply H4. rewrite Heqf0. remember (fold_left f l1 0) as init1.
  move : H2 H3 Heqf; clear; intros. rewrite Heqf.
  assert (init0 + ((lb + ub) / 2 - lb) <= init0 + (ub - lb) - 1).
    rewrite -ltnS. rewrite subn1 prednK. rewrite ltn_add2l. move : H2; clear; intros.
    rewrite ltn_sub2rE. specialize (Nat.div_lt_upper_bound (lb + ub) 2 ub); intro. 
      apply (introT ltP). apply H; try done. apply (elimT ltP). 
      rewrite -(ltn_add2r ub) in H2. rewrite addnn -mul2n in H2. done.
    assert (lb = (lb + lb)/2) by (rewrite addnn -muln2; rewrite Nat.div_mul; auto).
    rewrite {1}H; clear H. apply (introT leP). apply (Nat.div_le_mono (lb + lb) (lb + ub) 2); try done.
    apply (elimT leP). rewrite leq_add2l. intuition. rewrite addn_gt0. rewrite -subn_gt0 in H2. rewrite H2 orb_true_r //. 
  assert (init0 + (ub - lb) - 1 < init1 + (ub - lb)). 
    rewrite -(ltn_add2r 1) addn1 subn1 addn1 prednK. rewrite ltnS. rewrite leq_add2r //.
    rewrite addn_gt0. rewrite -subn_gt0 in H2. rewrite H2 orb_true_r //. 
  move : H H0; apply leq_ltn_trans.
Qed.

Lemma bab_bin_g7 :
  seq.seq ProdVar.t ->
  forall (bounds : Bounds) (cs1 : seq.seq Constraint1),
  seq.seq Constraint2 ->
  forall c1 : Constraint1,
  find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = Some c1 ->
  (product_bounds bounds == 0) = false ->
  find (fun x : ProdVar.t => length x bounds != 0) (rhs_vars c1) = None ->
  (length (lhs_var1 c1) bounds == 0) = false ->
  forall (p : nat * nat) (lb ub : nat),
  p = (lb, ub) ->
  PVM.find (lhs_var1 c1) bounds = Some (lb, ub) ->
  (product_bounds (update_ub bounds (lhs_var1 c1) ((lb + ub) / 2)) < product_bounds bounds)%coq_nat.
Proof.
  intros.
  rewrite /product_bounds /update_ub H4. 
  specialize (elements_add bounds (lhs_var1 c1) (lb, (lb + ub) / 2) H4); intro Heles.
  destruct Heles as [l0 [l1 [Hele Hele_add]]].
  rewrite -Hele -Hele_add.
  rewrite fold_left_app. rewrite fold_left_app.
  remember (fold_left
    (fun (acc : nat) '(_, bs) => let '(lb0, ub0) := bs in (acc + (ub0 - lb0)))
    l0 0) as init.
  apply (elimT ltP). 
  apply (product_bounds_helper l1 (init + (((lb + ub) / 2) - lb)) (init + (ub - lb))).
  rewrite ltn_add2l //. 
    rewrite /length H4 in H2. assert (lb < ub). move /eqP : H2 => H2.
    specialize (leqVgt ub lb); intro. destruct (ub <= lb) eqn : Hle. rewrite -subn_eq0 in Hle. move /eqP : Hle => Hle. done.
    rewrite orb_false_l in H5; done.
  rewrite ltn_sub2rE. specialize (Nat.div_lt_upper_bound (lb + ub) 2 ub); intro. 
    apply (introT ltP). apply H6; try done. apply (elimT ltP). 
    rewrite -(ltn_add2r ub) in H5. rewrite addnn -mul2n in H5. done.
  assert (lb = (lb + lb)/2) by (rewrite addnn -muln2; rewrite Nat.div_mul; auto).
  rewrite {1}H6; clear H6. apply (introT leP). apply (Nat.div_le_mono (lb + lb) (lb + ub) 2); try done.
  apply (elimT leP). rewrite leq_add2l. intuition.
Qed.


(* =================== bab_bin =================== *)

Definition prioritize_fst (v v' : option Valuation) : option Valuation :=
  match v with
  | None => v'
  | Some s => Some s
  end.

Function bab_bin (scc : list ProdVar.t) (bounds : Bounds)
                 (cs1 : list Constraint1) (cs2 : list Constraint2)
  { measure product_bounds bounds } : option Valuation :=
  let current_node := key_value bounds in 
  let unsat1 := find (fun c => negb (satisfies_constraint1 current_node c)) cs1 in
  let unsat2 := find (fun c => negb (satisfies_constraint2 current_node c)) cs2 in
  match unsat1, unsat2 with
  | None, None => (* 约束都满足,是一个解 *)
      if (product_bounds bounds == 0) (* current_node 是bounds中的唯一取值 *)
      then (Some current_node)
      else (* 不是唯一取值，缩小上界，继续寻找更优解 *)
        bab_bin scc (halve bounds) cs1 cs2
  | Some c1, _ => (* Phi1 不被满足 *)
      if (product_bounds bounds == 0) (* current_node 是bounds中的唯一取值 *)
      then None (* 但不满足约束 *)
      else (* 不是唯一取值，继续搜索 *)
        match find (fun x => length x bounds != 0) (rhs_vars c1) with
        (* pick a splittable var in rhs *)
        | Some v =>
            match PVM.find v bounds with
            | Some (lb, ub) =>
                prioritize_fst
                  (* find a best solution in the lower half *)
                  (bab_bin scc (update_ub bounds v ((lb+ub)/2)) cs1 cs2)
                  (* no solution in lower half, then search the upper half *)
                  (bab_bin scc (update_lb bounds v ((lb+ub)/2).+1) cs1 cs2)
            | None => None (* IMPOSSIBLE *)
            end
        | None => (* should ONLY search the upper half of the lhs variable, since the lower half must contain no solution *)
            if length c1.(lhs_var1) bounds == 0 then None
            else
              match PVM.find c1.(lhs_var1) bounds with
              | Some (lb, ub) =>
                  (* bab_bin scc (update_lb bounds (c1.(lhs_var1)) ((lb+ub)/2).+1) cs1 cs2 *)
                  (* to ease the proof: *)
                  prioritize_fst
                    (bab_bin scc (update_lb bounds (c1.(lhs_var1)) ((lb+ub)/2).+1) cs1 cs2)
                    (bab_bin scc (update_ub bounds (c1.(lhs_var1)) ((lb+ub)/2)) cs1 cs2)
              | None => None (* IMPOSSIBLE *)
              end
        end
  | None, Some c2 => (* Phi2 不被满足 *)
      if (product_bounds bounds == 0) (* current_node 是bounds中的唯一取值 *)
      then None (* 但不满足约束 *)
      else (* 不是唯一取值，继续搜索 *)
        match find (fun x => length x bounds != 0) (map snd (rhs_terms2 c2)) with
        (* pick a splittable var in rhs *)
        | Some v =>
            match PVM.find v bounds with
            | Some (lb, ub) =>
                (* match bab_bin scc (update_ub bounds v val) cs1 cs2 with *)
                (* (* find a best solution in the lower half *) *)
                (* | Some sol => Some sol *)
                (* (* no solution in the lower half, then search the upper half *) *)
                (* | None => bab_bin scc (update_lb bounds v val.+1) cs1 cs2 *)
                (* end *)
                prioritize_fst
                  (* find a best solution in the lower half *)
                  (bab_bin scc (update_ub bounds v ((lb+ub)/2)) cs1 cs2)
                  (* no solution in lower half, then search the upper half *)
                  (bab_bin scc (update_lb bounds v ((lb+ub)/2).+1) cs1 cs2)
            | None => None (* IMPOSSIBLE *)
            end
        | None => None (* no solution *)
        end
  end.
Proof.
  - exact: bab_bin_g1.
  - exact: bab_bin_g2.
  - exact: bab_bin_g7.
  - exact: bab_bin_g3.
  - exact: bab_bin_g4.
  - exact: bab_bin_g5.
  - exact: bab_bin_g6.
Defined.


(* =================== bab_bin correctness 1 =================== *)

Theorem bab_bin_correct1 : 
  forall (vars : list ProdVar.t) (bounds : Bounds)
         (cs1 : list Constraint1) (cs2 : list Constraint2),
    bab_bin vars bounds cs1 cs2 = None \/
      (exists s, bab_bin vars bounds cs1 cs2 = Some s /\
                   satisfies_all_constraint1 s cs1 /\ satisfies_all_constraint2 s cs2).
Proof.
  move => vars.
  apply bab_bin_ind with
    (P := (fun (bounds : Bounds) cs1 cs2 (sol : option Valuation) =>
             sol = None \/
               (exists s, sol = Some s /\ satisfies_all_constraint1 s cs1 /\ satisfies_all_constraint2 s cs2)))
        => /=.
  - move => bds cs1 cs2 Hcs1 Hcs2 _. right; exists (key_value bds); split; first done; split.
    + by apply find_none_sat_all_ctr1.
    + by apply find_none_sat_all_ctr2.
  - done.
  - intros; by left.
  - move => bds cs1 cs2 c1 Hcs1 _ _ [] _; first done.
    move => _ rv Hrv lb ub Hrv_bds IHl IHu.
    case: IHl => [ Hbabl | [s [Hbabl Hs]]].
    + rewrite Hbabl //=.
    + rewrite Hbabl /=. right; exists s; done.
  - intros; by left.
  - intros; by left.
  - move => bds cs1 cs2 c1 Hcs1 _ _ [] _; first done.
    move => _ Hrvs []; first done.
    move => Hlenlv _ lb ub Hlv_bds IHu IHl.
    case: IHu => [ Hbabu | [s [Hbabu Hs]]].
    + rewrite Hbabu //=.
    + rewrite Hbabu /=. right; exists s; done.
  - intros; by left.
  - intros; by left.
  - move => bds cs1 cs2 _ c2 Hcs2 [] _; first done.
    move => _ rv Hrv lb ub Hrv_bds IHl IHu.
    case: IHl => [ Hbabl | [s [Hbabl Hs]]].
    + rewrite Hbabl //=.
    + rewrite Hbabl /=. right; exists s; done.
  - intros; by left.
  - intros; by left.
Qed.

Corollary bab_bin_some_sat_all : 
  forall (vars : list ProdVar.t) (bounds : Bounds)
         (cs1 : list Constraint1) (cs2 : list Constraint2) (s : Valuation),
    bab_bin vars bounds cs1 cs2 = Some s ->
    satisfies_all_constraint1 s cs1 /\ satisfies_all_constraint2 s cs2.
Proof.
  move => vars bds cs1 cs2 s Hs.
  move: (bab_bin_correct1 vars bds cs1 cs2) => [Hnone | Hsome].
  - rewrite Hs in Hnone. done.
  - move: Hsome => [v [Hv Hcs]].
    rewrite Hv in Hs. injection Hs => Heq. by rewrite -Heq.
Qed.


(* =================== bab_bin in bounds =================== *)

Definition bab_bin_some_in_bounds_P (bounds : Bounds) (cs1 : list Constraint1)
  (cs2 : list Constraint2) (sol : option Valuation) :=
  forall (s : Valuation), well_defined bounds -> sol = Some s -> In s bounds.


Lemma bab_bin_some_in_bounds_aux :
  forall (vars : list ProdVar.t) (bounds : Bounds)
         (cs1 : list Constraint1) (cs2 : list Constraint2),
    bab_bin_some_in_bounds_P bounds cs1 cs2 (bab_bin vars bounds cs1 cs2).
Proof.
  move => vars. apply bab_bin_ind; rewrite /bab_bin_some_in_bounds_P /=; try done.
  - move => bds _ _ _ _ _ s Hwd [<-]. exact: key_value_in_bounds.
  - move => bds cs1 cs2 _ _ _ _ _ IH s Hwd Hbab.
    move: (wd_halve Hwd) => Hwdh.
    move: (IH _ Hwdh Hbab). exact: in_halve_in_bounds.
  - move => bds cs1 cs2 c1 Hc1 _ _ []; first done.
    move => /eqP Hbds _ rv Hrv lb ub Hfrvbds.
    rewrite -/((lb+ub)/2) => IHl IHu s Hwd.
    rewrite /prioritize_fst.
    case Hbabl : (bab_bin vars (update_ub bds rv ((lb + ub) / 2)) cs1 cs2) => [lsol|].
    + move => [<-].
      move: (IHl _ (wd_update_ub _ Hwd Hfrvbds) Hbabl).
      exact: in_update_ub_in_bounds.
    + move => Hbabu.
      move: (find_some_length_not0_neq _ _ Hrv Hfrvbds) => Hlbub.
      move: (IHu _ (wd_update_lb _ Hwd Hfrvbds Hlbub) Hbabu).
      exact: in_update_lb_in_bounds.
  - move => bds cs1 cs2 c1 Hcs1 _ _ []; first done.
    move => /eqP Hbds _ Hrvs []; first done.
    move => /eqP/eqP Hlenlv _ lb ub Hflvbds.
    rewrite -/((lb+ub)/2) => IHu IHl s Hwd.
    rewrite /prioritize_fst.
    case Hbabu : (bab_bin vars (update_lb bds (lhs_var1 c1) ((lb + ub) / 2).+1) cs1 cs2) => [usol|].
    + move => [<-].
      move: (length_not0_neq _ _ Hlenlv Hflvbds) => Hlbub.
      move: (IHu _ (wd_update_lb _ Hwd Hflvbds Hlbub) Hbabu).
      exact: in_update_lb_in_bounds.
    + move => Hbabl.
      move: (IHl _ (wd_update_ub _ Hwd Hflvbds) Hbabl).
      exact: in_update_ub_in_bounds.
  - move => bds cs1 cs2 Hcs1 c2 Hc2 []; first done.
    move => /eqP Hbds _ rv Hrv lb ub Hfrvbds.
    rewrite -/((lb+ub)/2) => IHl IHu s Hwd.
    rewrite /prioritize_fst.
    case Hbabl : (bab_bin vars (update_ub bds rv ((lb + ub) / 2)) cs1 cs2) => [lsol|].
    + move => [<-].
      move: (IHl _ (wd_update_ub _ Hwd Hfrvbds) Hbabl).
      exact: in_update_ub_in_bounds.
    + move => Hbabu.
      move: (find_some_length_not0_neq _ _ Hrv Hfrvbds) => Hlbub.
      move: (IHu _ (wd_update_lb _ Hwd Hfrvbds Hlbub) Hbabu).
      exact: in_update_lb_in_bounds.
Qed.

Lemma bab_bin_some_in_bounds : 
  forall (vars : list ProdVar.t) (bounds : Bounds)
         (cs1 : list Constraint1) (cs2 : list Constraint2) (s : Valuation),
    well_defined bounds ->
    bab_bin vars bounds cs1 cs2 = Some s -> In s bounds.
Proof.
  exact: bab_bin_some_in_bounds_aux.
Qed.



(* =================== bab_bin correctness 2 =================== *)

Lemma in_product0_ctr1_eq_kv :
  forall (bds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2) (v : Valuation),
    well_formed bds cs1 cs2 ->
    In v bds -> product_bounds bds = 0 ->
    forall c, List.In c cs1 ->
              satisfies_constraint1 v c = satisfies_constraint1 (key_value bds) c.
Proof.
  move => bds cs1 cs2 v Hwf Hvbds Hbds c Hccs1.
  move: (in_product0_vars_eq_kv Hvbds Hbds) => H.
  apply sat_ctr1_eq.
  - move: (wf_find_lhs_ctr1 _ Hwf Hccs1) => [lb [ub Hflvbds]].
    move: (find_some_key_value _ _ Hflvbds) => Hflvkv.
    rewrite (H _ _ Hflvkv) Hflvkv //=.
  - move => x Hxrvs.
    move: (wf_find_rhs_ctr1 _ Hwf Hccs1 _ Hxrvs) => [lb [ub Hfxbds]].
    move: (find_some_key_value _ _ Hfxbds) => Hfxkv.
    rewrite (H _ _ Hfxkv) Hfxkv //=.
Qed.

Lemma in_product0_ctr2_eq_kv :
  forall (bds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2) (v : Valuation),
    well_formed bds cs1 cs2 ->
    In v bds -> product_bounds bds = 0 ->
    forall c, List.In c cs2 ->
              satisfies_constraint2 v c = satisfies_constraint2 (key_value bds) c.
Proof.
  move => bds cs1 cs2 v Hwf Hvbds Hbds c Hccs2.
  move: (in_product0_vars_eq_kv Hvbds Hbds) => H.
  apply sat_ctr2_eq => x Hxrvs.
  move: (wf_find_rhs_ctr2 _ Hwf Hccs2 _ Hxrvs) => [lb [ub Hfxbds]].
  move: (find_some_key_value _ _ Hfxbds) => Hfxkv.
  rewrite (H _ _ Hfxkv) Hfxkv //=.
Qed.  


Definition bab_bin_correct2_P (bounds : Bounds) cs1 cs2 (sol : option Valuation) :=
  well_formed bounds cs1 cs2 ->
  (exists v, In v bounds /\
               satisfies_all_constraint1 v cs1 /\ satisfies_all_constraint2 v cs2) ->
  (exists s, sol = Some s /\
               satisfies_all_constraint1 s cs1 /\ satisfies_all_constraint2 s cs2).

Lemma bab_bin_correct2_aux :
  forall (vars : list ProdVar.t) (bounds : Bounds)
         (cs1 : list Constraint1) (cs2 : list Constraint2),
    bab_bin_correct2_P bounds cs1 cs2 (bab_bin vars bounds cs1 cs2).
Proof.
  move => vars. apply bab_bin_ind; rewrite /bab_bin_correct2_P /=.
  - move => bds cs1 cs2 Hcs1 Hcs2 _ _ _. exists (key_value bds); split; first done; split.
    + by apply find_none_sat_all_ctr1.
    + by apply find_none_sat_all_ctr2.
  - move => bds cs1 cs2 Hcs1 Hcs2 [] Hbds; first done.
    move => _ IH Hwf He. apply IH; first by apply wf_halve. exists (key_value bds). repeat split.
    + apply key_value_in_halve. by apply (wf_wd Hwf).
    + by apply find_none_sat_all_ctr1.
    + by apply find_none_sat_all_ctr2.
  - move => bds cs1 cs2 c1 Hcs1 _ _ /eqP Hbds.
    move => Hwf [v [Hv [Hvcs1 Hvcs2]]].
    move: (find_some_in_ctr1 _ _ Hcs1) => Hc1cs1.
    move: (find_some_sat_ctr1 _ _ Hcs1) => Hkvc1.
    move: (sat_all_in_ctr1 _ _ _ Hvcs1 Hc1cs1) => Hvc1.
    rewrite (in_product0_ctr1_eq_kv Hwf Hv Hbds _ Hc1cs1) in Hvc1. rewrite Hvc1 in Hkvc1.
    by discriminate.
    (* move: (in_bounds_product0 Hv Hbds) => Hveq. *)
    (* apply sat_all_ctr1_find_none in Hvcs1. rewrite Hveq Hcs1 in Hvcs1.  *)
  - move => bds cs1 cs2 c1 Hcs1 _ _ []; first done. 
    move => /eqP Hbds _ rv Hrv lb ub Hlbub. rewrite -/((lb+ub)/2) => IHl IHu Hwf He.
    move: (find_some_length_not0_neq _ _ Hrv Hlbub) => Hneq.
    case: He => s [Hs [Hscs1 Hscs2]].
    move: (in_bounds_dec rv (wf_wd Hwf) Hs Hlbub Hneq) => [Hinl | Hinu].
    + have Hl : (exists v : Valuation,
                    In v (update_ub bds rv ((lb + ub) / 2)) /\
                      satisfies_all_constraint1 v cs1 /\ satisfies_all_constraint2 v cs2)
        by (exists s).
      move: (IHl (wf_update_ub _ Hwf Hlbub) Hl) => [ls [Hbabls Hlscs]].
      rewrite /prioritize_fst Hbabls. by (exists ls).
    + rewrite /prioritize_fst.
      move: (bab_bin_correct1 vars (update_ub bds rv ((lb + ub) / 2)) cs1 cs2)
          => [Hlnone | [ls [Hlsome Hlscs]]].
      * rewrite Hlnone.
        have Hu : (exists v : Valuation,
                      In v (update_lb bds rv ((lb + ub) / 2).+1) /\
                        satisfies_all_constraint1 v cs1 /\ satisfies_all_constraint2 v cs2)
          by (exists s).
        move: (IHu (wf_update_lb _ Hwf Hlbub Hneq) Hu) => [us [Hbabus Huscs]]. by (exists us).
      * rewrite Hlsome. by (exists ls).
  - move => bds cs1 cs2 c1 Hcs1 _ _ []; first done. 
    move => /eqP Hbds _ rv Hrv Hrvbds Hwf.
    move: (find_some_length_not0_ex _ _ Hrv) => [lb [ub H]].
    rewrite H in Hrvbds. done.
  - move => bds cs1 cs2 c1 Hcs1 _ _ []; first done. 
    move => /eqP Hbds _ Hfrvs /eqP Hlenlv Hwf [v [Hvbds [Hvcs1 Hvcs2]]].
    move: (find_some_sat_ctr1 _ _ Hcs1) => Hc1.
    move: (find_some_in_ctr1 _ _ Hcs1) => Hc1cs1.
    move: (sat_all_in_ctr1 _ _ _ Hvcs1 Hc1cs1) => Hvc1.
    move: (wf_find_lhs_ctr1 _ Hwf Hc1cs1) => [lb_c1lhs [ub_c1lhs Hfc1lhs]].
    move: (key_value_in_bounds (wf_wd Hwf)) => Hkvbds.
    move: (length0_in_bounds_eq _ Hfc1lhs Hlenlv (wf_wd Hwf) Hvbds Hkvbds) => Heq_lhs.
    move: (find_none_length_not0_all0 _ _ Hfrvs) => Hlenrvs.
    have Heq_rhs : (forall x : ProdVar.t, List.In x (rhs_vars c1) ->
                                          PVM.find x v = PVM.find x (key_value bds)).
    {
      move => x Hxrhs.
      move: (wf_find_rhs_ctr1 _ Hwf Hc1cs1 _ Hxrhs) => [lbx [ubx Hxbds]].
      move: (Hlenrvs _ Hxrhs) => Hlenx.
      by apply (@length0_in_bounds_eq x bds lbx ubx _ _ Hxbds Hlenx (wf_wd Hwf)).
    }
    move: (sat_ctr1_eq _ _ _ Heq_lhs Heq_rhs) => Heq.
    rewrite Heq in Hvc1. rewrite Hvc1 in Hc1. by discriminate.
  - move => bds cs1 cs2 c1 Hcs1 _ _ []; first done. 
    move => Hbds _ Hfrvs []; first done.
    move => /eqP/eqP Hlenlv _ lb_lv ub_lv Hlbub. rewrite -/((lb_lv+ub_lv)/2) => IHu IHl Hwf He.
    move: (length_not0_neq _ _ Hlenlv Hlbub) => Hneq.
    case: He => [v [Hvbds Hvcs]].
    move: (in_bounds_dec _ (wf_wd Hwf) Hvbds Hlbub Hneq) => [Hinl | Hinu].
    + rewrite /prioritize_fst.
      move: (bab_bin_correct1 vars (update_lb bds (lhs_var1 c1) ((lb_lv + ub_lv) / 2).+1) cs1 cs2)
          => [Hunone | [us [Husome Huscs]]].
      * rewrite Hunone.
        have Hl : (exists v : Valuation,
                      In v (update_ub bds (lhs_var1 c1) ((lb_lv + ub_lv) / 2)) /\
                        satisfies_all_constraint1 v cs1 /\ satisfies_all_constraint2 v cs2)
          by (exists v).
        move: (IHl (wf_update_ub _ Hwf Hlbub) Hl) => [ls [Hbabls Hlscs]].
        rewrite /prioritize_fst Hbabls. by (exists ls).
      * rewrite Husome. by (exists us).
    + have Hu : (exists v : Valuation,
                    In v (update_lb bds (lhs_var1 c1) ((lb_lv + ub_lv) / 2).+1) /\
                      satisfies_all_constraint1 v cs1 /\ satisfies_all_constraint2 v cs2)
        by (exists v).
      move: (IHu (wf_update_lb _ Hwf Hlbub Hneq) Hu) => [us [Hbabus Huscs]].
      rewrite /prioritize_fst Hbabus. by (exists us).
  - move => bds cs1 cs2 c1 Hcs1 _ _ []; first done. 
    move => Hbds _ Hfrvs []; first done.
    move => /eqP/eqP Hlenlv _ Hlvbds.
    move: (length_not0_ex _ _ Hlenlv) => [lb [ub H]].
    rewrite H in Hlvbds. done.
  - move => bds cs1 cs2 _ c2 Hcs2 /eqP Hbds.
    move => Hwf [v [Hv [Hvcs1 Hvcs2]]].
    move: (find_some_in_ctr2 _ _ Hcs2) => Hc2cs2.
    move: (find_some_sat_ctr2 _ _ Hcs2) => Hkvc2.
    move: (sat_all_in_ctr2 _ _ _ Hvcs2 Hc2cs2) => Hvc2.
    rewrite (in_product0_ctr2_eq_kv Hwf Hv Hbds _ Hc2cs2) in Hvc2. rewrite Hvc2 in Hkvc2.
    by discriminate.
    (* move: (in_bounds_product0 Hv Hbds) => Hveq. *)
    (* apply sat_all_ctr2_find_none in Hvcs2. rewrite Hveq Hcs2 in Hvcs2. by discriminate. *)
  - move => bds cs1 cs2 _ c2 Hcs2 []; first done. 
    move => /eqP Hbds _ rv Hrv lb ub Hlbub. rewrite -/((lb+ub)/2) => IHl IHu Hwf He.
    move: (find_some_length_not0_neq _ _ Hrv Hlbub) => Hneq.
    case: He => s [Hs [Hscs1 Hscs2]].
    move: (in_bounds_dec rv (wf_wd Hwf) Hs Hlbub Hneq) => [Hinl | Hinu].
    + have Hl : (exists v : Valuation,
                    In v (update_ub bds rv ((lb + ub) / 2)) /\
                      satisfies_all_constraint1 v cs1 /\ satisfies_all_constraint2 v cs2)
        by (exists s).
      move: (IHl (wf_update_ub _ Hwf Hlbub) Hl) => [ls [Hbabls Hlscs]].
      rewrite /prioritize_fst Hbabls. by (exists ls).
    + rewrite /prioritize_fst.
      move: (bab_bin_correct1 vars (update_ub bds rv ((lb + ub) / 2)) cs1 cs2)
          => [Hlnone | [ls [Hlsome Hlscs]]].
      * rewrite Hlnone.
        have Hu : (exists v : Valuation,
                      In v (update_lb bds rv ((lb + ub) / 2).+1) /\
                        satisfies_all_constraint1 v cs1 /\ satisfies_all_constraint2 v cs2)
          by (exists s).
        move: (IHu (wf_update_lb _ Hwf Hlbub Hneq) Hu) => [us [Hbabus Huscs]]. by (exists us).
      * rewrite Hlsome. by (exists ls).
  - move => bds cs1 cs2 _ c2 Hcs2 []; first done. 
    move => /eqP Hbds _ rv Hrv Hrvbds Hwf.
    move: (find_some_length_not0_ex _ _ Hrv) => [lb [ub H]].
    rewrite H in Hrvbds. done.
  - move => bds cs1 cs2 _ c2 Hcs2 []; first done. 
    move => /eqP Hbds _ Hfrvs Hwf [v [Hvbds [Hvcs1 Hvcs2]]].
    move: (find_some_sat_ctr2 _ _ Hcs2) => Hc2.
    move: (find_some_in_ctr2 _ _ Hcs2) => Hc2cs2.
    move: (sat_all_in_ctr2 _ _ _ Hvcs2 Hc2cs2) => Hvc2.
    move: (key_value_in_bounds (wf_wd Hwf)) => Hkvbds.
    move: (find_none_length_not0_all0 _ _ Hfrvs) => Hlenrvs.
    have Heq_rhs : (forall x : ProdVar.t, List.In x (map snd (rhs_terms2 c2)) ->
                                          PVM.find x v = PVM.find x (key_value bds)).
    {
      move => x Hxrhs.
      move: (wf_find_rhs_ctr2 _ Hwf Hc2cs2 _ Hxrhs) => [lbx [ubx Hxbds]].
      move: (Hlenrvs _ Hxrhs) => Hlenx.
      by apply (@length0_in_bounds_eq x bds lbx ubx _ _ Hxbds Hlenx (wf_wd Hwf)).
    }
    move: (sat_ctr2_eq _ _ _ Heq_rhs) => Heq.
    rewrite Heq in Hvc2. rewrite Hvc2 in Hc2. by discriminate.
Qed.


Theorem bab_bin_correct2 :
  forall (vars : list ProdVar.t) (bounds : Bounds)
         (cs1 : list Constraint1) (cs2 : list Constraint2),
    well_formed bounds cs1 cs2 ->
    (exists v, In v bounds /\
                 satisfies_all_constraint1 v cs1 /\ satisfies_all_constraint2 v cs2) ->
    (exists s, bab_bin vars bounds cs1 cs2 = Some s /\
                 satisfies_all_constraint1 s cs1 /\ satisfies_all_constraint2 s cs2).
Proof.
  exact: bab_bin_correct2_aux.
Qed.


(* =================== smaller_valuation =================== *)

(* 求 Valuation 的较小值 *)
Definition smaller_valuation (v1 v2 : Valuation) : Valuation :=
  PVM.map2 (fun v v' => match v, v' with
                        | Some n , Some n' => Some (minn n n')
                        | _, _ => None
                        end) v1 v2.

Lemma smaller_val_eq : forall (v v' : Valuation) (x : ProdVar.t) (n n' : nat),
    PVM.find x v = Some n -> PVM.find x v' = Some n' ->
    PVM.find x (smaller_valuation v v') = Some (minn n n').
Proof.
  rewrite /smaller_valuation => v1 v2 x n1 n2 Hfxv1 Hfxv2.
  set f:= (fun v v' => match v, v' with
                       | Some n , Some n' => Some (minn n n')
                       | _, _ => None
                       end).
  rewrite PVM.map2_1; last by (left; apply (find_some_in Hfxv1)).
  rewrite Hfxv1 Hfxv2 //=.
Qed.  

Lemma smaller_val_le_l : forall (v v' : Valuation), le (smaller_valuation v v') v.
Proof.
  rewrite /le /smaller_valuation.
  set f:= (fun v v' => match v, v' with
                       | Some n , Some n' => Some (minn n n')
                       | _, _ => None
                       end).
  move => v1 v2 x n Hfsv.
  move: (find_some_in Hfsv) => Hinsv.
  move: (PVM.map2_2 Hinsv) => Hin.
  move: Hfsv; rewrite (PVM.map2_1 _ Hin).
  case (PVM.find x v1) => [n1|]; case (PVM.find x v2) => [n2|]; rewrite /=; try done.
  move => [<-]. exists n1. split; first done.
  exact: geq_minl.
Qed.  

Lemma smaller_val_le_r : forall (v v' : Valuation), le (smaller_valuation v v') v'.
Proof.
  rewrite /le /smaller_valuation.
  set f:= (fun v v' => match v, v' with
                       | Some n , Some n' => Some (minn n n')
                       | _, _ => None
                       end).
  move => v1 v2 x n Hfsv.
  move: (find_some_in Hfsv) => Hinsv.
  move: (PVM.map2_2 Hinsv) => Hin.
  move: Hfsv; rewrite (PVM.map2_1 _ Hin).
  case (PVM.find x v1) => [n1|]; case (PVM.find x v2) => [n2|]; rewrite /=; try done.
  move => [<-]. exists n2. split; first done.
  exact: geq_minr.
Qed.

Lemma smaller_val_in_bounds : forall (v v' : Valuation) (bds : Bounds),
    In v bds -> In v' bds -> In (smaller_valuation v v') bds.
Proof.
  rewrite /In => v1 v2 bds Hin1 Hin2 x lb ub Hfxbds.
  move: (Hin1 _ _ _ Hfxbds) => [n1 [Hfxv1 [Hlbn1 Hn1ub]]].
  move: (Hin2 _ _ _ Hfxbds) => [n2 [Hfxv2 [Hlbn2 Hn2ub]]].
  exists (minn n1 n2); repeat split.
  - exact: smaller_val_eq.
  - rewrite leq_min. apply /andP. done.
  - rewrite geq_min. apply /orP. by left.
Qed.    

Lemma smaller_val_in_update_ub :
  forall (v v' : Valuation) (bds : Bounds) (x : ProdVar.t) (n : nat),
    In v (update_ub bds x n) -> In v' (update_lb bds x n.+1) ->
    In (smaller_valuation v v') (update_ub bds x n).
Proof.
  rewrite /update_ub /update_lb => v1 v2 bds x n.
  case Hfxbds : (PVM.find x bds) => [[lb ub]|]; last exact: smaller_val_in_bounds.
  rewrite /In => Hin1 Hin2 y lby uby.
  move: (eq_dec y x) => [-> | Hneq].
  - rewrite HiFirrtl.find_add_eq => [[<- <-]].
    case (Hin1 x lb n) => [|n1 [Hxv1 [Hlbn1 Hn1n]]];
                          first by rewrite HiFirrtl.find_add_eq.
    case (Hin2 x n.+1 ub) => [|n2 [Hxv2 [HSnn2 Hn2ub]]];
                             first by rewrite HiFirrtl.find_add_eq.
    exists (minn n1 n2); repeat split.
    + exact: smaller_val_eq.
    + rewrite leq_min. apply /andP. split; first done. apply ltnW.
      apply: (leq_ltn_trans _ HSnn2). by apply (leq_trans Hlbn1).
    + rewrite geq_min. apply /orP. by left.
  - rewrite (HiFirrtl.find_add_neq Hneq) => Hfy.
    case (Hin1 y lby uby) => [|n1 [Hyv1 [Hlbyn1 Hn1uby]]];
                             first by rewrite (HiFirrtl.find_add_neq Hneq).
    case (Hin2 y lby uby) => [|n2 [Hyv2 [Hlbyn2 Hn2uby]]];
                             first by rewrite (HiFirrtl.find_add_neq Hneq).
    exists (minn n1 n2); repeat split.
    + exact: smaller_val_eq.
    + rewrite leq_min. apply /andP. done.
    + rewrite geq_min. apply /orP. by left.
Qed.  

Lemma smaller_val_in_halve : forall (v v' : Valuation) (bds : Bounds),
    In v (halve bds) -> In v' bds -> In (smaller_valuation v v') (halve bds).
Proof.
  rewrite /In => vh v bds Hinh Hin x lb ub Hfxhbds.
  move: (Hinh _ _ _ Hfxhbds) => [nh [Hfxvh [Hlbnh Hnhub]]].
  move: (find_halve_some _ _ Hfxhbds) => [ub' [Hub Hfxbds]].
  move: (Hin _ _ _ Hfxbds) => [n [Hfxv [Hlbn Hnub']]].
  exists (minn nh n). repeat split.
  + exact: smaller_val_eq.
  + rewrite leq_min. apply /andP. done.
  + rewrite geq_min. apply /orP. by left.
Qed.


(* Key property:
   if there are two solutions, their smaller_valuation is also a solution. *)
Theorem smaller_sol_is_sol :
  forall (cs1 : list Constraint1) (cs2 : list Constraint2) (s s' : Valuation),
    satisfies_all_constraint1 s cs1 /\ satisfies_all_constraint2 s cs2 ->
    satisfies_all_constraint1 s' cs1 /\ satisfies_all_constraint2 s' cs2 ->
    satisfies_all_constraint1 (smaller_valuation s s') cs1 /\
      satisfies_all_constraint2 (smaller_valuation s s') cs2.
Proof.
Admitted.


Corollary sol_in_halve : forall (bds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2),
  forall (sol : Valuation), In sol (halve bds) /\
                              satisfies_all_constraint1 sol cs1 /\ satisfies_all_constraint2 sol cs2 ->
                            forall s, In s bds /\
                                        satisfies_all_constraint1 s cs1 /\ satisfies_all_constraint2 s cs2 ->
                                      (exists s', In s' (halve bds) /\ le s' s /\
                                                    satisfies_all_constraint1 s' cs1 /\ satisfies_all_constraint2 s' cs2).
Proof.
  move => bds cs1 cs2 sol [Hinsol Hsatsol] s [Hins Hsats].
  exists (smaller_valuation sol s).
  split; last split.
  - exact: smaller_val_in_halve.
  - exact: smaller_val_le_r.
  - exact: smaller_sol_is_sol.
Qed.


(* =================== bab_bin returns smallest solution =================== *)

Lemma in_product0_kv_le :
  forall (v : Valuation) (bds : Bounds),
    In v bds -> product_bounds bds = 0 -> le (key_value bds) v.
Proof.
  rewrite /le => v bds Hvbds Hbds x n Hfxkv.
  rewrite (in_product0_vars_eq_kv Hvbds Hbds _ Hfxkv).
  by (exists n).
Qed.

Definition bab_bin_smallest_P (bounds : Bounds) cs1 cs2 (ret : option Valuation) :=
  forall (sol : Valuation), well_formed bounds cs1 cs2 -> ret = Some sol ->
  forall (s : Valuation), In s bounds /\
                            satisfies_all_constraint1 s cs1 /\ satisfies_all_constraint2 s cs2 ->
                          le sol s.

Lemma bab_bin_smallest_aux :
  forall (vars : list ProdVar.t) (bounds : Bounds)
         (cs1 : list Constraint1) (cs2 : list Constraint2),
    bab_bin_smallest_P bounds cs1 cs2 (bab_bin vars bounds cs1 cs2).
Proof.
  move => vars. apply bab_bin_ind; rewrite /bab_bin_smallest_P /=; try done.
  - move => bds cs1 cs2 Hcs1 Hcs2 /eqP Hbds sol Hwf Hkv s [Hsbds [Hscs1 Hscs2]].
    (* move: (in_bounds_product0 Hsbds Hbds). *)
    case: Hkv => <-. exact: in_product0_kv_le.
  - move => bds cs1 cs2 Hcs1 Hcs2 []; first done.
    move => /eqP Hbds _ IH sol Hwf Hbab s Hs.
    apply wf_halve in Hwf. move: (IH _ Hwf Hbab) => IHsol.
    have Hsol : In sol (halve bds) /\ satisfies_all_constraint1 sol cs1 /\ satisfies_all_constraint2 sol cs2.
    { split; [by apply (bab_bin_some_in_bounds _ _ _ (wf_wd Hwf) Hbab) | by apply (bab_bin_some_sat_all _ _ _ _ Hbab)]. }
    move: (sol_in_halve _ _ Hsol Hs) => [sh [Hsh [Hshs Hshcs]]].
    apply: (le_trans _ Hshs). by apply IHsol.
  - move => bds cs1 cs2 c1 Hc1 _ _ []; first done.
    move => /eqP Hbds _ rv Hrv lb ub Hlbub.
    rewrite -/((lb+ub)/2) => IHl IHu sol Hwf.
    rewrite /prioritize_fst.
    case Hbabl : (bab_bin vars (update_ub bds rv ((lb + ub) / 2)) cs1 cs2) => [lsol|].
    + move => [] <- s [Hsbds Hscs].
      move: (wf_update_ub rv Hwf Hlbub) => Hwfl.
      move: (IHl _ Hwfl Hbabl) => Hl.
      move: (find_some_length_not0_neq _ _ Hrv Hlbub) => Hneq.
      move: (in_bounds_dec _ (wf_wd Hwf) Hsbds Hlbub Hneq) => [Hs | Hs].
      * by apply Hl.
      * move: (bab_bin_some_in_bounds _ _ _ (wf_wd Hwfl) Hbabl) => Hlsol.
        move: (bab_bin_some_sat_all _ _ _ _ Hbabl) => Hlsolcs.
        move: (smaller_val_in_update_ub _ _ _ Hlsol Hs) => Hsv.
        move: (smaller_sol_is_sol _ _ _ _ Hlsolcs Hscs) => Hsvcs.
        have Hlsolsv : le lsol (smaller_valuation lsol s) by apply Hl.
        apply (le_trans Hlsolsv); by apply smaller_val_le_r.
    + move => Hbabu s [Hsbds Hscs].
      move: (find_some_length_not0_neq _ _ Hrv Hlbub) => Hneq.
      move: (in_bounds_dec _ (wf_wd Hwf) Hsbds Hlbub Hneq) => [Hs | Hs].
      * have Hel : (exists v : Valuation,
                       In v (update_ub bds rv ((lb + ub) / 2)) /\
                         satisfies_all_constraint1 v cs1 /\ satisfies_all_constraint2 v cs2)
          by (exists s).
        move: (wf_update_ub rv Hwf Hlbub) => Hwfl.
        move: (@bab_bin_correct2 vars _ _ _ Hwfl Hel) => [lsol [Hbabl' _]].
        by rewrite Hbabl' in Hbabl.
      * apply IHu; first (by apply wf_update_lb); done.
  - move => bds cs1 cs2 c1 Hc1 _ _ []; first done.
    move => /eqP Hbds _ Hrvs []; first done.
    move => /eqP/eqP Hlenlv _ lb ub Hlbub.
    rewrite -/((lb+ub)/2) => IHu IHl sol Hwf.
    rewrite /prioritize_fst.
    case Hbabu : (bab_bin vars (update_lb bds (lhs_var1 c1) ((lb + ub) / 2).+1) cs1 cs2) => [usol|].
    + move => [] <- s [Hsbds [Hscs1 Hscs2]].
      move: (length_not0_neq _ _ Hlenlv Hlbub) => Hneq.
      move: (wf_update_lb (lhs_var1 c1) Hwf Hlbub Hneq) => Hwfu.
      move: (IHu _ Hwfu Hbabu) => Hu.
      move: (in_bounds_dec _ (wf_wd Hwf) Hsbds Hlbub Hneq) => [Hs | Hs].
      * move: (find_some_in_ctr1 _ _ Hc1) => Hc1cs1.
        apply find_some_sat_ctr1 in Hc1.
        move: (sat_all_in_ctr1 _ _ _ Hscs1 Hc1cs1) => Hsc1.
        move: (key_value_in_bounds (wf_wd Hwf)) => Hkvbds.
        have Heq_rhs : (forall x : ProdVar.t, List.In x (rhs_vars c1) ->
                                              PVM.find x s = PVM.find x (key_value bds)).
        {
          move => x Hxrhs.
          move: (wf_find_rhs_ctr1 _ Hwf Hc1cs1 _ Hxrhs) => [lbx [ubx Hxbds]].
          move: (find_none_length_not0_all0 _ _ Hrvs) => Hlenrvs.
          move: (Hlenrvs _ Hxrhs) => Hlenx. Check length0_in_bounds_eq.
          by apply (@length0_in_bounds_eq x bds lbx ubx _ _ Hxbds Hlenx (wf_wd Hwf)).
        }
        move: (find_some_key_value _ _ Hlbub) => Hlvkv.
        move: (sat_ctr1_lhs_find_some _ _ Hsc1) => [lvn Hlvn].
        move: (in_update_ub_le _ _ _ Hlvn Hlbub Hs) => Hle.
        move: (unsat_ctr1_le _ _ _ Heq_rhs Hlvn Hlvkv Hle Hc1).
        rewrite Hsc1 //=.
      * by apply Hu.
    + move => Hbabl s [Hsbds Hscs].
      move: (length_not0_neq _ _ Hlenlv Hlbub) => Hneq.
      move: (in_bounds_dec _ (wf_wd Hwf) Hsbds Hlbub Hneq) => [Hs | Hs].
      * apply IHl; first (by apply wf_update_ub); done.
      * have Heu : (exists v : Valuation,
                       In v (update_lb bds (lhs_var1 c1) ((lb + ub) / 2).+1) /\
                         satisfies_all_constraint1 v cs1 /\ satisfies_all_constraint2 v cs2)
          by (exists s).
        move: (wf_update_lb (lhs_var1 c1) Hwf Hlbub Hneq) => Hwfu.
        move: (@bab_bin_correct2 vars _ _ _ Hwfu Heu) => [usol [Hbabu' _]].
        by rewrite Hbabu' in Hbabu.
  - move => bds cs1 cs2 Hcs1 c2 Hc2 []; first done.
    move => /eqP Hbds _ rv Hrv lb ub Hlbub.
    rewrite -/((lb+ub)/2) => IHl IHu sol Hwf.
    rewrite /prioritize_fst.
    case Hbabl : (bab_bin vars (update_ub bds rv ((lb + ub) / 2)) cs1 cs2) => [lsol|].
    + move => [] <- s [Hsbds Hscs].
      move: (wf_update_ub rv Hwf Hlbub) => Hwfl.
      move: (IHl _ Hwfl Hbabl) => Hl.
      move: (find_some_length_not0_neq _ _ Hrv Hlbub) => Hneq.
      move: (in_bounds_dec _ (wf_wd Hwf) Hsbds Hlbub Hneq) => [Hs | Hs].
      * by apply Hl.
      * move: (bab_bin_some_in_bounds _ _ _ (wf_wd Hwfl) Hbabl) => Hlsol.
        move: (bab_bin_some_sat_all _ _ _ _ Hbabl) => Hlsolcs.
        move: (smaller_val_in_update_ub _ _ _ Hlsol Hs) => Hsv.
        move: (smaller_sol_is_sol _ _ _ _ Hlsolcs Hscs) => Hsvcs.
        have Hlsolsv : le lsol (smaller_valuation lsol s) by apply Hl.
        apply (le_trans Hlsolsv); by apply smaller_val_le_r.
    + move => Hbabu s [Hsbds Hscs].
      move: (find_some_length_not0_neq _ _ Hrv Hlbub) => Hneq.
      move: (in_bounds_dec _ (wf_wd Hwf) Hsbds Hlbub Hneq) => [Hs | Hs].
      * have Hel : (exists v : Valuation,
                       In v (update_ub bds rv ((lb + ub) / 2)) /\
                         satisfies_all_constraint1 v cs1 /\ satisfies_all_constraint2 v cs2)
          by (exists s).
        move: (wf_update_ub rv Hwf Hlbub) => Hwfl.
        move: (@bab_bin_correct2 vars _ _ _ Hwfl Hel) => [lsol [Hbabl' _]].
        by rewrite Hbabl' in Hbabl.
      * apply IHu; first (by apply wf_update_lb); done.
Qed.

Theorem bab_bin_smallest :
  forall (vars : list ProdVar.t) (bounds : Bounds)
         (cs1 : list Constraint1) (cs2 : list Constraint2) (sol : Valuation),
    well_formed bounds cs1 cs2 -> bab_bin vars bounds cs1 cs2 = Some sol ->
    forall (s : Valuation), In s bounds /\
                              satisfies_all_constraint1 s cs1 /\ satisfies_all_constraint2 s cs2 ->
                            le sol s.
Proof.
  exact: bab_bin_smallest_aux.
Qed.

Lemma bab_bin_mem_in cs1 cs2 : forall ls bs sol, bab_bin ls bs cs1 cs2 = Some sol -> forall var, PVM.mem var sol -> PVM.mem var bs.
Proof.
(* Added by KY *)
Admitted.

Lemma bab_bin_none_unsat cs1 cs2 : forall ls bs, bab_bin ls bs cs1 cs2 = None -> forall v : Valuation, In v bs -> forallb (satisfies_constraint1 v) cs1 = false.
Proof.
(* Added by KY *)
Admitted.

End bnb.

Section test_bnb.
(*Definition c0 : Constraint1 :=
  {|
    lhs_var1 := (3%num, N0);
    rhs_const1 := 4;
    rhs_terms1 := [(2, (4%num, N0))]
  |}.

Definition c1 : Constraint1 :=
  {|
    lhs_var1 := (5%num, N0);
    rhs_const1 := -2;
    rhs_terms1 := [(1, (3%num, N0))]
  |}.

Definition c2 : Constraint1 :=
  {|
    lhs_var1 := (4%num, N0);
    rhs_const1 := -2;
    rhs_terms1 := [(1, (5%num, N0))]
  |}.

Definition ubs := solve_ubs [(3%num, N0);(4%num, N0);(5%num, N0)] [(3%num, N0);(4%num, N0);(5%num, N0)] [c0;c1;c2].

Definition c3 : Constraint1 :=
  {|
    lhs_var1 := (2%num, N0);
    rhs_const1 := 0;
    rhs_terms1 := [(1, (3%num, N0))]
  |}.

Definition ubs' := solve_ubs [(3%num, N0);(4%num, N0);(5%num, N0)] [(3%num, N0);(4%num, N0);(5%num, N0)] [c0;c1;c2;c3].

Definition bound0 := add_bound (3%num, N0) (0,4) initial_bounds.
Definition bound1 := add_bound (4%num, N0) (0,0) bound0.
Definition bound2 := add_bound (5%num, N0) (0,2) bound1.

Definition nbs := branch_and_bound_natural' [(3%num, N0);(4%num, N0);(5%num, N0)] bound2 [c0;c1;c2] [] None [].

Compute (product_bounds bound2 [(n_V 1); (n_V 2); (n_V 3)]).
Definition test_b0 := update_ub bound2 (n_V 1) 5.
Compute (product_bounds test_b0 [(n_V 1); (n_V 2); (n_V 3)]).
Definition test_b1 := update_lb bound2 (n_V 1) 2.
Compute (product_bounds test_b1 [(n_V 1); (n_V 2); (n_V 3)]).
Definition node := key_value bound2.
Compute (node (n_V 1)).
Compute (node (n_V 2)).
Compute (node (n_V 3)).
Definition unsat1 := find (fun c => negb (satisfies_constraint1 node c)) [c0;c1;c2].
Compute unsat1.
Definition unsat2 := find (fun c => negb (satisfies_constraint2 node c)) [c3;c4].
Compute unsat2.
Definition children := fold_left (fun s hd => if ((bound2 hd).1 == (bound2 hd).2) then s else
let nb := update_ub bound2 hd (node hd) in 
  nb :: s) [(n_V 1); (n_V 2); (n_V 3)] 
  nil.
Compute (length children).

Compute (forallb (fun v => node v == (bound2 v).1) [(n_V 1); (n_V 2); (n_V 3)]).
Definition children' := map (fun v => update_ub bound2 v (node v)) [(n_V 1); (n_V 2); (n_V 3)].
Definition child0' := List.hd (initial_bounds V) children'.
Compute (child0' (n_V 1)).
Compute (child0' (n_V 2)).
Compute (child0' (n_V 3)).
Definition new_node := key_value (List.hd (initial_bounds V) children').
Compute (new_node (n_V 1)).
Compute (new_node (n_V 2)).
Compute (new_node (n_V 3)).

Compute (List.length children').
Compute (product_bounds (List.hd (initial_bounds V) children') [(n_V 1); (n_V 2); (n_V 3)] == 1).
Definition child1' := List.nth 1 children' (initial_bounds V).
Compute (child1' (n_V 1)).
Compute (child1' (n_V 2)).
Compute (child1' (n_V 3)).

Compute (forallb (fun b => product_bounds b [(n_V 1); (n_V 2); (n_V 3)] == 1) children').

(*Definition children := new_nodes1 V node bound2 c0.
Definition child0 := List.hd (initial_bounds V) children.
Compute (child0 (n_V 1)).
Compute (child0 (n_V 2)).
Compute (child0 (n_V 3)).
Definition child1 := List.nth 1 children (initial_bounds V).
Compute (child1 (n_V 1)).
Compute (child1 (n_V 2)).
Compute (child1 (n_V 3)).
Definition child2 := List.nth 2 children (initial_bounds V).
Compute (child2 (n_V 1)).
Compute (child2 (n_V 2)).
Compute (child2 (n_V 3)).
Definition new_solution0 := branch_and_bound_natural V [(n_V 1); (n_V 2); (n_V 3)] child0 [c0;c1;c2] [c3;c4].
Compute (match new_solution0 with
  | Some v => v (n_V 1)
  | None => 0
  end).
Compute (child2 (n_V 2)).
Compute (child2 (n_V 3)).
*)
Definition res := branch_and_bound_natural [(n_V 1); (n_V 2); (n_V 3)] bound2 [c0;c1;c2] [c3;c4] None nil.

Definition smaller_solution0 := smaller_solution (Some node) None.
Compute (match smaller_solution0 with
| Some s0 => s0 (n_V 2)
| None => 0
end).
(*Definition smaller_solution1 := if ((bound2 (n_V 1)).1 == (bound2 (n_V 1)).2) 
  then smaller_solution0 else
  let nb := update_ub bound2 (n_V 1) (node (n_V 1)) in 
    smaller_solution (branch_and_bound_natural [(n_V 1); (n_V 2); (n_V 3)] nb [c0;c1;c2] [c3;c4] smaller_solution0 [::node]) smaller_solution0.
Definition smaller_solution2 := if ((bound2 (n_V 2)).1 == (bound2 (n_V 2)).2) 
  then smaller_solution0 else
  let nb := update_ub bound2 (n_V 2) (node (n_V 2)) in 
    smaller_solution (branch_and_bound_natural [(n_V 1); (n_V 2); (n_V 3)] nb [c0;c1;c2] [c3;c4] smaller_solution1) smaller_solution1 nil.

Definition smaller_solution2' := Some (add_valuation V (add_valuation V (add_valuation V (initial_valuation V) (n_V 1) 3) (n_V 2) 1) (n_V 3) 1).

Definition smaller_solution3 := if ((bound2 (n_V 3)).1 == (bound2 (n_V 3)).2) 
  then smaller_solution0 else
  let nb := update_ub bound2 (n_V 3) (node (n_V 3)) in 
    smaller_solution (branch_and_bound_natural [(n_V 1); (n_V 2); (n_V 3)] nb [c0;c1;c2] [c3;c4] smaller_solution2) smaller_solution2 nil.
Definition smaller_solution' := fold_left (fun s hd => if ((bound2 hd).1 == (bound2 hd).2) then s else
  let nb := update_ub bound2 hd (node hd) in 
    smaller_solution (branch_and_bound_natural [(n_V 1); (n_V 2); (n_V 3)] nb [c0;c1;c2] [c3;c4] s) s
    ) [(n_V 1); (n_V 2); (n_V 3)] smaller_solution0. ocaml 10min *)
*)
End test_bnb.

Section solve_scc.
(*Definition solve_scc (scc : list V) (constraints : list (Constraint V)) (values : Valuation V) : option (Valuation V) :=
  let cs1 := (split_constraints constraints).1 in
  let cs2 := (split_constraints constraints).2 in
  let ubs := solve_ubs scc cs1 in
  let bs := mergeValuations values ubs in
  branch_and_bound_natural scc bs cs1 cs2 None.*)
End solve_scc.

(*Fixpoint solve_ubs' (scc : list V) (constraints : list (Constraint1 V)) : (Valuation V) :=
  match scc with
  | [] => initial_valuation V 
  | hd :: tl => let ub := 10 - (nat_of_ord hd) in
     add_valuation V (solve_ubs' tl constraints) hd ub
  end.

Definition res1 := solve_ubs' [(n_V 1); (n_V 2); (n_V 3)] [c0; c1; c2'].
Compute (res1 (n_V 3)).*)

(* 根据不满足的phi1约束生成新的节点 
Definition expand_node1 (node : Valuation V) (values upper_bounds : Valuation V) (c : Constraint1 V) : list (Valuation V) :=
  let base_val := node (lhs_var1 V c) in
  let new_val := (base_val + upper_bounds (lhs_var1 V c)) / 2 in
  let new_node1 := fun x => if x == lhs_var1 V c then new_val else node x in
  let new_nodes := map (fun '(_, var) =>
      let new_val := (node var + values var) / 2 in
      (fun x => if x == var then new_val else node x)
      ) (rhs_terms1 V c) in
  new_node1 :: new_nodes. (* 根据需求，可以添加更多不同的子节点生成策略 *)

(* 根据不满足的phi2约束生成新的节点 *)
Definition expand_node2 (node : Valuation V) (values upper_bounds : Valuation V) (c : Constraint2 V) : list (Valuation V) :=
  map (fun '(_, var) =>
         let new_val := (node var + values var) / 2 in
         (fun x => if x == var then new_val else node x)
      ) (rhs_terms2 V c).

(* 主函数，分支定界求解 *)
Program Fixpoint branch_and_bound_natural (node_queue : list (Valuation V)) (values upper_bounds : Valuation V) 
         (cs1 : list (Constraint1 V)) (cs2 : list (Constraint2 V)) (solution : option (Valuation V)) {measure } : option (Valuation V) :=
  match node_queue with
  | nil => solution
  | current_node :: rest_queue =>
    let unsat1 := find (fun c => negb (satisfies_constraint1 V current_node c)) cs1 in
    let unsat2 := find (fun c => negb (satisfies_constraint2 V current_node c)) cs2 in
    match unsat1, unsat2, solution with
    | None, None, None => (* 约束都满足,是一个解.没有已发现的解 *)
            Some current_node 
    | None, None, Some s => (* 约束都满足,取已知解和该解中的较小值 *)
            Some (merge_min current_node s)
    | Some c1, _, _ => (* Phi1 不被满足 *)
      let children := expand_node1 current_node values upper_bounds c1 in
      branch_and_bound_natural (rest_queue ++ children) values upper_bounds cs1 cs2 solution
    | None, Some c2, _ => (* Phi2 不被满足 *)
      let children := expand_node2 current_node values upper_bounds c2 in
      branch_and_bound_natural (rest_queue ++ children) values upper_bounds cs1 cs2 solution
    end
  end.*)

(* ========================================================================= *)
(* ===== old implementation by Keyin, for reference ======================== *)
(* ========================================================================= *)

(*
Program Fixpoint branch_and_bound_natural (scc : list ProdVar.t) (bounds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2)
  (solution : option Valuation) {measure (product_bounds bounds)} : option Valuation :=
  let current_node := key_value bounds in
  let unsat1 := find (fun c => negb (satisfies_constraint1 current_node c)) cs1 in
  let unsat2 := find (fun c => negb (satisfies_constraint2 current_node c)) cs2 in
  match unsat1, unsat2 with
  | None, None => (* 约束都满足,是一个解 *)
    if (product_bounds bounds == 0) (* current_node 是bounds中的唯一取值 *)
      then (Some current_node)
     else (* 不是唯一取值，缩小上界，继续寻找更优解 *)
      (*let children := *)
(*         fold_left (fun ls hd => if ((bounds hd).1 == (bounds hd).2) then ls else  *)
(*           (update_ub bounds hd (current_node hd)) :: ls) scc nil *)
(*       in  *)
(*       fold_left (fun s nb => branch_and_bound_natural scc nb cs1 cs2 s) children (smaller_solution (Some current_node) solution) *)
(*       *)
      fold_left (fun s hd =>
          match PVM.find hd bounds, PVM.find hd current_node with
            | Some (lb, ub), Some hdv => if (lb == ub) then s else
                let nb := update_ub bounds hd hdv in
                branch_and_bound_natural scc nb cs1 cs2 s
            | _, _ => s
            end)
            scc (smaller_solution (Some current_node) solution)
  | Some c1, _ => (* Phi1 不被满足 *)
    if (product_bounds bounds == 0) (* current_node 是bounds中的唯一取值 *)
      then solution (* 但不满足约束 *)
     else (* 不是唯一取值，继续搜索 *)
      (*let children := new_nodes1 current_node bounds c1 in *)
(*       fold_left (fun s nb => branch_and_bound_natural scc nb cs1 cs2 s) children solution*)

      let ns := match PVM.find (lhs_var1 c1) bounds, PVM.find (lhs_var1 c1) current_node with
        | Some (lb, ub), Some lhsv => if (lb == ub) then solution else
            branch_and_bound_natural scc (update_lb bounds (lhs_var1 c1) (lhsv+1)) cs1 cs2 solution
        | _, _ => solution
        end in
      fold_left (fun s hd =>
          match PVM.find hd bounds, PVM.find hd current_node with
            | Some (lb, ub), Some hdv => if (lb == ub) then s else
                let nb := update_ub bounds hd hdv in
                branch_and_bound_natural scc nb cs1 cs2 s
            | _, _ => s
            end) (rhs_vars c1) ns

  | None, Some c2 => (* Phi2 不被满足 *)
    if (product_bounds bounds == 0) (* current_node 是bounds中的唯一取值 *)
      then solution (* 但不满足约束 *)
     else (* 不是唯一取值，继续搜索 *)
      (*let children := new_nodes2 current_node bounds c2 in *)
(*       fold_left (fun s nb => branch_and_bound_natural scc nb cs1 cs2 s) children solution *)

      fold_left (fun s hd =>
          match PVM.find hd bounds, PVM.find hd current_node with
            | Some (lb, ub), Some hdv => if (lb == ub) then s else
                let nb := update_ub bounds hd hdv in
                branch_and_bound_natural scc nb cs1 cs2 s
            | _, _ => s
            end) (map snd (rhs_terms2 c2)) solution
  end.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.


Lemma branch_and_bound_correctness : forall (solved tbsolved : list ProdVar.t) (cs : list Constraint) (initial ubs : Valuation), 
  isGoodbound solved tbsolved cs initial ubs ->
  (*let bound := mergeValuations initial ubs in
  let cs1 := filter (constraint1_in_set tbsolved) (split_constraints cs).1 in
  let cs2 := filter (constraint2_in_set tbsolved) (split_constraints cs).2 in*)
  match branch_and_bound_natural tbsolved (mergeValuations initial ubs) 
    (filter (constraint1_in_set tbsolved) (split_constraints cs).1)
    (filter (constraint2_in_set tbsolved) (split_constraints cs).2) None with
  | Some s => let cs' := List.filter (constraint_in_set (solved ++ tbsolved)) cs in
              satisfies_all s cs'
  | _ => true
  end.
Proof.
Admitted.

Lemma branch_and_bound_smallest : forall (solved tbsolved : list ProdVar.t) (cs : list Constraint) (initial ubs : Valuation), 
  isGoodbound solved tbsolved cs initial ubs ->
  let bound := mergeValuations initial ubs in
  let cs1 := filter (constraint1_in_set tbsolved) (split_constraints cs).1 in
  let cs2 := filter (constraint2_in_set tbsolved) (split_constraints cs).2 in
  match branch_and_bound_natural tbsolved bound cs1 cs2 None with
  | Some s => let cs' := List.filter (constraint_in_set (solved ++ tbsolved)) cs in satisfies_all s cs' ->
    forall temp_s, satisfies_all temp_s cs' -> (*PVM.equal leq*) smaller_valuation s temp_s
  | _ => true
  end.
Proof.
Admitted.

Program Fixpoint branch_and_bound_natural' (scc : list ProdVar.t) (bounds : Bounds) (cs1 : list Constraint1) (cs2 : list Constraint2)
  (solution : option Valuation) (searched : list Valuation) {measure (product_bounds bounds)} : (option Valuation) * (list Valuation) :=
  let current_node := key_value bounds in if valuation_in current_node searched then (solution, searched) else
  let n_searched := current_node :: searched in
  let unsat1 := find (fun c => negb (satisfies_constraint1 current_node c)) cs1 in
  let unsat2 := find (fun c => negb (satisfies_constraint2 current_node c)) cs2 in
  match unsat1, unsat2 with
  | None, None => (* 约束都满足,是一个解 *)
    if (product_bounds bounds == 0) (* current_node 是bounds中的唯一取值 *)
      then (Some current_node, n_searched)
     else (* 不是唯一取值，缩小上界，继续寻找更优解 *)
      fold_left (fun '(s, n_searched') hd => 
          match PVM.find hd bounds, PVM.find hd current_node with
            | Some (lb, ub), Some hdv => if (lb == ub) then (s, n_searched') else
                let nb := update_ub bounds hd hdv in
                branch_and_bound_natural' scc nb cs1 cs2 s n_searched'
            | _, _ => (s, n_searched')
            end)
            scc (smaller_solution (Some current_node) solution, n_searched)
  | Some c1, _ => (* Phi1 不被满足 *)
    if (product_bounds bounds == 0) (* current_node 是bounds中的唯一取值 *)
      then (solution, n_searched) (* 但不满足约束 *)
     else (* 不是唯一取值，继续搜索 *)
      let ns := match PVM.find (lhs_var1 c1) bounds, PVM.find (lhs_var1 c1) current_node with
        | Some (lb, ub), Some lhsv => if (lb == ub) then (solution, n_searched) else
            branch_and_bound_natural' scc (update_lb bounds (lhs_var1 c1) (lhsv+1)) cs1 cs2 solution n_searched
        | _, _ => (solution, n_searched) 
        end in
      fold_left (fun '(s, n_searched') hd => 
          match PVM.find hd bounds, PVM.find hd current_node with
            | Some (lb, ub), Some hdv => if (lb == ub) then (s, n_searched') else
                let nb := update_ub bounds hd hdv in
                branch_and_bound_natural' scc nb cs1 cs2 s n_searched'
            | _, _ => (s, n_searched')
            end) (rhs_vars c1) ns

  | None, Some c2 => (* Phi2 不被满足 *)
    if (product_bounds bounds == 0) (* current_node 是bounds中的唯一取值 *)
      then (solution, n_searched) (* 但不满足约束 *)
     else (* 不是唯一取值，继续搜索 *)
      fold_left (fun '(s, n_searched') hd => 
          match PVM.find hd bounds, PVM.find hd current_node with
            | Some (lb, ub), Some hdv => if (lb == ub) then (s, n_searched') else
                let nb := update_ub bounds hd hdv in
                branch_and_bound_natural' scc nb cs1 cs2 s n_searched'
            | _, _ => (s, n_searched')
            end) (map snd (rhs_terms2 c2)) (solution, n_searched)
  end.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Check branch_and_bound_natural'.
*)
