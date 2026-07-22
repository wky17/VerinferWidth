open Extraction.InferWidths_multimod
open Graph

(* too slow..
type my_vertex = int * (int * int)

module V = struct
  type t = my_vertex
  let compare = Stdlib.compare 
  let hash = Hashtbl.hash
  let equal = (=)
end

module G = Imperative.Digraph.Concrete(V)
module SCC = Components.Make(G)

let build_graph_from_constraints constraints =
  let g = G.create () in
  let node_cache = Hashtbl.create 1000 in 
  
  let get_node v =
    match Hashtbl.find_opt node_cache v with
    | Some n -> n
    | None ->
        Hashtbl.add node_cache v v; 
        v
  in

  List.iter (fun c ->
    let lhs_node = get_node c.lhs_var1 in
    (if not (G.mem_vertex g lhs_node) then
        G.add_vertex g lhs_node);
    List.iter (fun (_, rhs_var) ->
      let rhs_node = get_node rhs_var in
      G.add_edge g lhs_node rhs_node
    ) (c.rhs_power @ c.rhs_terms1)
  ) constraints;
  g*)

  let pair_to_nat (x, y) = (x + y) * (x + y + 1) / 2 + y

  let nat_to_pair n =
    let t = int_of_float (floor ((sqrt (float (8 * n + 1)) -. 1.0) /. 2.0)) in
    let k2 = n - (t * (t + 1)) / 2 in
    let k1 = t - k2 in
    (k1, k2)
  
  let triple_to_nat (a, (b, c)) = pair_to_nat (a, pair_to_nat (b, c))
  
  let nat_to_triple n =
    let (a, t) = nat_to_pair n in
    let (b, c) = nat_to_pair t in
    (a, (b, c))
  
  module G = Pack.Digraph
  module SCC = Components.Make(G) 
  
  let build_graph_from_constraints constraints =
    let g = G.create () in
    let node_table = Hashtbl.create 1000 in
    let get_node var =
      try Hashtbl.find node_table var
      with Not_found ->
        let node = G.V.create var in
        Hashtbl.add node_table var node;
        node
    in
    Stdlib.List.iter (fun c ->
      let lhs_node = get_node (triple_to_nat c.lhs_var1) in
      (if not (G.mem_vertex g lhs_node) then
        G.add_vertex g lhs_node);
      
      Stdlib.List.iter (fun (_, rhs_var) ->
        let rhs_node = get_node (triple_to_nat rhs_var) in
        G.add_edge g lhs_node rhs_node
      ) c.rhs_terms1;

      Stdlib.List.iter (fun (_, rhs_var) ->
        let rhs_node = get_node (triple_to_nat rhs_var) in
        G.add_edge g lhs_node rhs_node
      ) c.rhs_power
    ) constraints;
    g

(*let print_graph g =
  Printf.printf "Nodes: [";
  G.iter_vertex (fun v -> Printf.printf "%d; " (G.V.label v)) g;
  Printf.printf "]\n";

  Printf.printf "Edges:\n";
  G.iter_edges (fun src dst ->
    Printf.printf "%d -> %d\n" 
      (G.V.label src) 
      (G.V.label dst)
  ) g*)