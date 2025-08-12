From mathcomp Require Import all_ssreflect.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
From Solver Require Import Env LoFirrtl HiEnv HiFirrtl constraints.
From mathcomp.tarjan Require Import kosaraju.

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

(* ------------ distinguish simple cycle from sccs ------------ *)

Definition is_simple_cycle (l : list ProdVar.t) (constraints : list Constraint) : bool :=
  let cs := filter (constraint1_in_set l) (split_constraints' constraints).1 in
  forallb (fun c => match rhs_terms1 c, rhs_power c with
                  | nil, nil
                  | [::(1,_)], nil => true
                  | _, _ => false
                  end) cs.

End dpdcgraph.
