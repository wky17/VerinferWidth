open Extraction.Constraints
open Graph

(* 将自然数对 (k1, k2) 映射到自然数 *)
let pair_to_nat (k1, k2) =
  let s = k1 + k2 in
  (s * (s + 1)) / 2 + k2

(* 将自然数 n 映射回自然数对 (k1, k2) *)
let nat_to_pair n =
  let t = int_of_float (floor ((sqrt (float (8 * n + 1)) -. 1.0) /. 2.0)) in
  let k2 = n - (t * (t + 1)) / 2 in
  let k1 = t - k2 in
  (k1, k2)

module G = Pack.Digraph (* 使用 Pack.Digraph 有向图模块 *)
module SCC = Components.Make(G) (* 强连通分量计算模块 *)

(* 构建从约束列表到有向图的函数 *)
let build_graph_from_constraints constraints =
  let g = G.create () in
  (* 使用哈希表记录已创建的节点，避免重复创建 *)
  let node_table = Hashtbl.create 100 in
  (* 辅助函数：获取或创建节点 *)
  let get_node var =
    try Hashtbl.find node_table var
    with Not_found ->
      let node = G.V.create var in
      Hashtbl.add node_table var node;
      node
  in
  (* 遍历所有约束 *)
  Stdlib.List.iter (fun c ->
    (* 获取左侧变量对应的节点 *)
    let lhs_node = get_node (pair_to_nat c.lhs_var1) in
    (if not (G.mem_vertex g lhs_node) then
      G.add_vertex g lhs_node);
    
    (* 遍历右侧项，为每个变量创建边 *)
    Stdlib.List.iter (fun (_, rhs_var) ->
      let rhs_node = get_node (pair_to_nat rhs_var) in
      G.add_edge g lhs_node rhs_node
    ) (Stdlib.List.append c.rhs_terms1 c.rhs_power)
  ) constraints;
  g

(* 打印图结构 *)
let print_graph g =
  (* 打印所有节点 *)
  Printf.printf "Nodes: [";
  G.iter_vertex (fun v -> Printf.printf "%d; " (G.V.label v)) g;
  Printf.printf "]\n";

  (* 打印所有边 *)
  Printf.printf "Edges:\n";
  G.iter_edges (fun src dst ->
    Printf.printf "%d -> %d\n" 
      (G.V.label src) 
      (G.V.label dst)
  ) g
