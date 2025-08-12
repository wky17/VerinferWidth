From mathcomp Require Import all_ssreflect.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
From Solver Require Import Env LoFirrtl HiEnv HiFirrtl constraints.
From mathcomp.tarjan Require Import kosaraju.

Definition Constraint1_non_power : Type :=
  { x : Constraint1 | rhs_power x = nil }.

Definition build_non_power_constraint1 (lhs : ProdVar.t) (rhs_const : Z.t) (rhs_terms : list (nat * ProdVar.t)) : Constraint1_non_power.
Proof.
  refine (exist _ 
    {| 
      lhs_var1 := lhs; 
      rhs_const1 := rhs_const; 
      rhs_terms1 := rhs_terms; 
      rhs_power := nil 
    |} 
    _).
  reflexivity.
Defined. 

Definition T := ProdVar.t.
Definition G := T -> list T.
Definition Adj := T -> T -> list Constraint1.

Definition add_edge graph adj_matrix (from to : T) (c : Constraint1) : G * Adj :=
  (fun v => if (v == from) then to :: graph v else graph v, 
  fun x y => if ((x == from) && (y == to)) then c :: adj_matrix x y else adj_matrix x y).

Fixpoint build_graph (constraints : list Constraint1) : G * Adj :=
  match constraints with
  | [] => (fun _ => nil, fun _ _ => nil)
  | c0 :: cs =>
      fold_left (fun '(graph, adj_matrix) (coef_var : nat * ProdVar.t) =>
                   let (_, xi) := coef_var in add_edge graph adj_matrix xi (lhs_var1 c0) c0)
                (rhs_terms1 c0) (build_graph cs)
  end.

Fixpoint find_path (g : G) (y : T) n (v : list T) (x : T) res : option (list T) :=
  match res with
  | Some p => res
  | None =>
  if x == y then Some (y :: v) else
  if n is n'.+1 then foldl (fun r child => match r with
    | Some p => res 
    | None => find_path g y n' (x :: v) child None
    end) res (g x) else None
  end.

Set Implicit Arguments.
(*Unset Strict Implicit.*) 
Import Prenex Implicits.

Section dpdcgraph.
(* -------------------- Method 2 -------------------- *)

Variable  (c : hfcircuit).
Definition Graph : Type := finProdVar c -> finProdVar c -> bool.

Definition add_dependency (g : Graph) (from to : finProdVar c) : Graph :=
  fun x y => g x y || (((finProdVar2ProdVar x) == (finProdVar2ProdVar from)) && ((finProdVar2ProdVar y) == (finProdVar2ProdVar to))).

(*Definition collect_graph_nodes : list (finProdVar c) := enum (finProdVar c).
  foldl (fun acc v =>
            let connected_to_v := filter (fun u => Graph u v) (enum V) in
            foldl (fun acc u => if u \in acc then acc else u :: acc) acc connected_to_v) [] (enum ).
*)
Fixpoint build_dependency_graph (constraints : list Constraint1) : Graph :=
  match constraints with
  | [] => fun _ _ => false
  | c0 :: cs =>
      let graph := build_dependency_graph cs in
      fold_left (fun g (coef_var : nat * ProdVar.t) =>
                   let (_, xi) := coef_var in add_dependency g (ProdVar2finProdVar c xi) (ProdVar2finProdVar c (lhs_var1 c0)))
                (rhs_terms1 c0)
                graph
  end.

(*Definition c0 : Constraint1 := {|
  lhs_var1 := (1%num, 0%num);
  rhs_const1 := 0;
  rhs_terms1 := [(1, (2%num, 0%num))]
|}.

Definition emptyg : Graph := fun _ _ => false.
Definition g := (*add_dependency emptyg (ProdVar2finProdVar c (0%num, 0%num)) (ProdVar2finProdVar c (1%num, 0%num)).*)
  build_dependency_graph [c0].
Definition res_r := kosaraju g.
Compute ((finProdVar2ProdVar (ProdVar2finProdVar c (0%num, 0%num))) == (finProdVar2ProdVar (ProdVar2finProdVar c (1%num, 0%num)))).
Compute (g (ProdVar2finProdVar c (0%num, 0%num)) (ProdVar2finProdVar c (1%num, 0%num))).*)

(* ------------ distinguish simple cycle from sccs ------------ *)

Definition is_simple_cycle (l : list ProdVar.t) (constraints : list Constraint) : bool :=
  let cs := filter (constraint1_in_set l) (split_constraints' constraints).1 in
  forallb (fun c => match rhs_terms1 c, rhs_power c with
                  | nil, nil
                  | [::(1,_)], nil => true
                  | _, _ => false
                  end) cs.

(*Definition is_simple_cycle (l : list (finProdVar c)) (graph : Graph) : bool :=
  match l with
  | [] => false  (* An empty list *)
  | x :: nil => false (* A single element *)
  | x :: xs =>
    let nl := xs ++ [:: x] in 
    forallb (fun '(a, b) => 
        forallb (fun z => if (b == z) then (graph a z) else negb (graph a z)) l
    ) (combine l nl)
  end.*)

(*Fixpoint find_substitute_nums (terms : list (nat * V)) (visited : list V) (constraints : list (Constraint1 V)) : nat :=
  match terms with
  | nil => 0
  | (_, hd) :: tl => if hd \in visited then 0
    else find_substitute_num hd visited constraints + find_substitute_nums tl visited constraints
  end
with find_substitute_num (hd : V) (visited : list V) (constraints : list (Constraint1 V)) : nat :=
  let new_visited := x :: visited in
  let cs := find_constraint1s V hd constraints in
  map (fun c => find_substitute_nums (rhs_terms1 c) new_visited) cs
  fold_left () 0*)

(* 找出从x到y的所有不含环路经，y是目标 
Fixpoint find_paths_helper (n : nat) (x y : V) (visited : list V) : list (list V) :=
  match n with
  | 0 => []
  | S m => 
    if (x == y) then
      [[y]] (* 如果到达目标，将目标作为路径返回 *)
    else
      let visited' := x :: visited in
      let successors := filter (fun z => Graph x z) collect_graph_nodes in (* 取x的后继 *)
      let unvisited_successors := filter (fun z => ~~(z \in visited')) successors in (* 取没有访问过的后继 *)
      let paths_from_successors := flat_map (fun z => find_paths_helper m z y visited') unvisited_successors in
      map (cons x) paths_from_successors
  end.

Definition find_paths (x y : V) : list (list V) :=
  find_paths_helper (List.length collect_graph_nodes) x y [].

Definition find_paths_num (x y : V) (visited : list V) : nat :=
  List.length (find_paths_helper (List.length collect_graph_nodes - List.length visited) x y visited).

Fixpoint find_paths_amount (x : V) (yl visited : list V) : nat :=
  match yl with
  | nil => 0
  | hd :: tl => let p1 := find_paths_helper (length collect_graph_nodes - length visited) x hd visited in
    let p2 := find_paths_amount x tl visited in
    length p1 + p2
  end.*)

End dpdcgraph.

(* -------------------- Method 1 -------------------- 

Section dpdcgraph'.
(* 把Constraint1中的依赖关系画为有向图 *)
(* 定义类型别名 *)
Variable (V : finType).
Definition Graph := V -> list V.

(* 定义空的依赖关系图 *)
Definition empty_graph : Graph := fun _ => nil.

(* 向图中添加依赖关系 *)
Definition add_dependency' (g : Graph) (v1 v2 : V) : Graph :=
  fun v => if (v == v1) then v2 :: g v else g v.

(* 从一个约束获取依赖关系 *)
Definition extract_dependencies (c : Constraint1 V) : Graph :=
  fold_left (fun g (term : nat * V) => 
    let '(_, var) := term in
    add_dependency' g (lhs_var1 c) var)
  (rhs_terms1 c) 
  empty_graph.

(* 将多个约束组合成一个依赖关系图 *)
Fixpoint constraints_to_graph (constraints : list (Constraint V)) : Graph :=
  match constraints with
  | [] => empty_graph
  | (Phi1 c) :: cs => 
      let g := extract_dependencies c in
      fun v => g v ++ constraints_to_graph cs v
  | _ :: cs => constraints_to_graph cs
  end.

End dpdcgraph'.

Section Test_graph.
Definition V := [finType of 'I_3].
(*Arguments empty_graph {V}.
Arguments add_dependency' {V}.*)
Definition G := add_dependency' (empty_graph V) ord0 (ordS ord0).

End Test_graph.*)
