open Extraction.InferWidths_multimod
open Graph

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
    
    List.iter (fun (_, rhs_var) ->
      let rhs_node = get_node rhs_var in
      G.add_edge g lhs_node rhs_node
    ) (c.rhs_terms1 @ c.rhs_power)
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