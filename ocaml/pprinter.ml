open Extraction
open Printf
open Extraction.Simple_cycle
open Extraction.Graph
open Extraction.Kosaraju
open Extraction.Constraints
open List

(*let () =*)
  (* test case 1 : simple cycle done *) 
  (*
  Stdlib.List.iter (fun y -> Stdlib.List.iter (fun x -> printf "%d" (Obj.magic x); printf "; ") y; printf "\n") res0;
  Stdlib.List.iter (fun x -> printf "%b" x; printf "; ") (Stdlib.List.map (is_simple_cycle coq_V g0) (Stdlib.List.map Stdlib.List.rev res0)); printf "\n";
  Stdlib.List.iter (fun y -> Stdlib.List.iter (fun x -> printf "%d" (Obj.magic x); printf "; ") y; printf "\n") (Stdlib.List.filter (fun x -> is_simple_cycle coq_V g0 (Stdlib.List.rev x)) res0);

  printf "%b\n" solved_sc0;
  match solve_sc0 with
  | Some vs -> 
    Stdlib.List.iter (fun x -> printf "%d : %d\n" (Obj.magic x) (vs x)) sc0
  | None -> printf "unsolved.\n"
  *)

  (* test case 2 : 不是simple cycle *)
  (*
  let g1 = build_dependency_graph coq_V cs1 in 
  let res1 = kosaraju coq_V g1 in

  Stdlib.List.iter (fun y -> Stdlib.List.iter (fun x -> printf "%d" (Obj.magic x); printf "; ") y; printf "\n") res1;
  Stdlib.List.iter (fun x -> printf "%b" x; printf "; ") (Stdlib.List.map (is_simple_cycle coq_V g1) (Stdlib.List.map Stdlib.List.rev res1)); printf "\n";
  Stdlib.List.iter (fun y -> Stdlib.List.iter (fun x -> printf "%d" (Obj.magic x); printf "; ") y; printf "\n") (Stdlib.List.filter (fun x -> is_simple_cycle coq_V g1 (Stdlib.List.rev x)) res1);

  let sc1 =
    hd [] (List.filter (fun x -> is_simple_cycle coq_V g1 (rev x)) res1) in  
  let solve_sc1 =
    solve_simple_cycle coq_V sc1 cs1 (initial_valuation coq_V) in
  match solve_sc1 with
  | Some vs -> printf "%b\n" (check_sc coq_V sc1 [] cs1 vs);
    Stdlib.List.iter (fun x -> printf "%d : %d\n" (Obj.magic x) (vs x)) sc1
  | None -> printf "unsolved.\n"
  *)

  (* test case 3 : 简单环+有向无环 done *)
  (*let g2 = build_dependency_graph coq_V cs2 in 
  let res2 = kosaraju coq_V g2 in

  Stdlib.List.iter (fun y -> Stdlib.List.iter (fun x -> printf "%d" (Obj.magic x); printf "; ") y; printf "\n") res2;
  Stdlib.List.iter (fun x -> printf "%b" x; printf "; ") (Stdlib.List.map (is_simple_cycle coq_V g2) res2); printf "\n";
  Stdlib.List.iter (fun y -> Stdlib.List.iter (fun x -> printf "%d" (Obj.magic x); printf "; ") y; printf "\n") (Stdlib.List.filter (fun x -> is_simple_cycle coq_V g2 x) res2);
  
  let solve_sc2 = solve_ac_and_sc (Stdlib.List.rev res2) [] (initial_valuation coq_V) cs2 in 
  match solve_sc2 with
  | Some vs -> 
    Stdlib.List.iter (fun x -> printf "%d : %d\n" (Obj.magic x) (vs x)) (Stdlib.List.flatten res2)
  | None -> printf "unsolved.\n"
  *)

  (* test case 4 : 有向无环+简单环 *)
  (*let g3 = build_dependency_graph coq_V (fst (split_constraints coq_V cs3)) in 
  let res3 = kosaraju coq_V g3 in

  Stdlib.List.iter (fun y -> Stdlib.List.iter (fun x -> printf "%d" (Obj.magic x); printf "; ") y; printf "\n") res3;
  Stdlib.List.iter (fun x -> printf "%b" x; printf "; ") (Stdlib.List.map (is_simple_cycle coq_V g3) (Stdlib.List.map Stdlib.List.rev res3)); printf "\n";
  Stdlib.List.iter (fun y -> Stdlib.List.iter (fun x -> printf "%d" (Obj.magic x); printf "; ") y; printf "\n") (Stdlib.List.filter (fun x -> is_simple_cycle coq_V g3 (Stdlib.List.rev x)) res3);
  
  let solve_sc3 = solve_ac_and_sc (Stdlib.List.rev res3) [] (initial_valuation coq_V) cs3 in
  match solve_sc3 with
  | Some vs -> 
    Stdlib.List.iter (fun x -> printf "%d : %d\n" (Obj.magic x) (vs x)) (Stdlib.List.flatten res3)
  | None -> printf "unsolved.\n"
  *)

  (* test scc substitute *)
  (*Stdlib.List.iter (fun (x, y) -> printf "%d, %d" (Obj.magic x) (Obj.magic y); printf "; ") Scc.res2; printf "\n";
  match Scc.ub3' with 
  | Some ub -> printf "%d\n" ub
  | None -> printf "%d\n" 0
  *)

  (* test bnb *)
  (*match Branch_and_bound.res with
  | (Some vs, _) -> Stdlib.List.iter (fun x -> printf "%d : %d\n" x (vs (Obj.magic x))) [1;2;3]
  | _ -> printf "unsolved.\n"*)

  (* test solve_scc *)

  (*let cs1 = fst (split_constraints coq_V ((Phi1 Branch_and_bound.c0) :: ((Phi1 Branch_and_bound.c1) :: ((Phi1 Branch_and_bound.c2) :: ((Phi2 Branch_and_bound.c3) :: ((Phi2
  Branch_and_bound.c4) :: [])))))) in
  let cs2 = snd (split_constraints coq_V ((Phi1 Branch_and_bound.c0) :: ((Phi1 Branch_and_bound.c1) :: ((Phi1 Branch_and_bound.c2) :: ((Phi2 Branch_and_bound.c3) :: ((Phi2
  Branch_and_bound.c4) :: [])))))) in
  let ubs = Scc.solve_ubs coq_V ((n_V (Stdlib.Int.succ 0)) :: ((n_V (Stdlib.Int.succ (Stdlib.Int.succ 0))) :: (
    (n_V (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))) :: []))) cs1 in
  Stdlib.List.iter (fun x -> printf "%d : %d\n" x (ubs (Obj.magic x))) [1;2;3]
  *)

  (* test new upperbounds *)
  (*match Branch_and_bound.res0 with 
  | Some ub0 -> printf "%d\n" ub0; 
    (match Branch_and_bound.res1 with 
    | Some ub1 -> printf "%d\n" ub1; 
      (match Branch_and_bound.res2 with 
      | Some ub2 -> printf "%d\n" ub2; 
    (match Branch_and_bound.res0' with
    | Some vs -> Stdlib.List.iter (fun x -> printf "%d : %d\n" x (vs (Obj.magic x))) [1;2;3]
    | None -> printf "unsolved.")
      | None -> printf "%d\n" 0)
    | None -> printf "%d\n" 0)
  | None -> printf "%d\n" 0
  *)
