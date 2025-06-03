(* This module defines an algorithm to topologically sort a graph.
   In contrast to fingraph.v, we do not require the underlying type
   of vertices to be intrinsically finite.  The set of vertices
   is given as a (finite) sequence, and that is sufficient for us.
   The module also provides a correctness theorem. *)

   From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.

   Module TopoSort.
   
   Section TopoSortS.
   
   (* general parameters of the functions in this file:
      the nodes are an eqType,
      the vertices are a finite set (the order of the sequence does not matter),
      and g describes the adjacency relation: for every vertex v,
      the sequence (g v) contains the successors of v
      (again, the order of the sequence does not matter). *)
   Context {node : eqType}.
   Variable vertices : seq node.
   Variable g : node -> seq node.
   
   (* We want our notion of subset, based on sequences. *)
   Fixpoint subset (s1 s2 : seq node) : bool :=
   match s1 with
   | [::] => true
   | a :: tail1 => (a \in s2) && subset tail1 s2
   end.
   
   Fixpoint path_from (r : node) (p : seq node) : bool :=
   match p with
   | [::] => true
   | a :: tail => (r \in g a) && ~~(a \in tail) && path_from a tail
   end.
   
   (* We assume that every graph is closed, but perhaps not every graph is acyclic.
      In the relevant theorems we will add graph_acyclic as a precondition. *)
   Hypothesis graph_closed : forall v : node, v \in vertices -> subset (g v) vertices.
   
   Definition graph_acyclic :=
      forall (r : node) (p : seq node),
         r \in vertices -> subset p vertices ->
            path_from r p -> r \notin p.
   
   (* a type to present results or error messages from topological sorting *)
   Inductive result_type : Type :=
      | Sorted : seq node -> result_type
      | Cycle : seq node -> result_type
      | N_too_small : result_type
      .
   
   Fixpoint topo_tree (n : nat) (gray_nodes : seq node)
                      (root : node) (maybe_already_found: result_type) : result_type :=
   match maybe_already_found with
   | Cycle _ | N_too_small => maybe_already_found (* propagate earlier error *)
   | Sorted already_found =>
   if root \in gray_nodes then Cycle (root :: gray_nodes) (* error: there is a cycle *)
   else if root \in already_found then maybe_already_found
   else match n with
        | 0 => N_too_small (* error: n was too small *)
        | S n' => match foldr (topo_tree n' (root :: gray_nodes)) maybe_already_found (g root) with
                  | Sorted result => Sorted (root :: result)
                  | e => e (* propagate resursive error *)
                  end
        end
   end.
   
   Definition topo_sort : result_type :=
      foldr (topo_tree (size vertices) [::]) (Sorted [::]) vertices.
   
   (* Now we start to work on the correctness proof of topo_sort. We first want to express
   an inductive property on topo_tree that will allow us to prove the correctness of
   topo_sort. Basically, we request the following:
   - if topo_tree returns Cycle _, then the graph is not acyclic.
   - if topo_tree returns N_too_small, then n was smaller than size vertices - size gray_nodes.
   - if topo_tree return Sorted _, then the result contains the successors of root in addition
     to what had been already found earlier.
   
   Then we can request on topo_sort that it never returns N_too_small,
   and that it *only* returns Cycle _ if the graph is not acyclic. *)
   
   Fixpoint respects_topological_order (v : seq node) : bool :=
   match v with
   | [::] => true
   | a :: tail => subset (g a) tail && (a \notin tail) && respects_topological_order tail
   end.
   
   Local Lemma subset_cat : forall (s t : seq node), subset s (t ++ s) = true.
   Proof.
   elim => [|a l IHs t].
   * simpl subset ; reflexivity.
   * rewrite /subset mem_cat mem_head orbT andTb -cat1s catA.
     apply IHs.
   Qed.
   
   Lemma subset_cons_cons : forall (s t : seq node) (x : node), subset s t -> subset (x :: s) (x :: t).
   Proof.
   elim => [t x _|a l IHs t x /andP [Ha Hs]].
   + rewrite /subset mem_head //.
   + rewrite /subset (in_cons x t a) Ha orbT andTb.
     apply IHs, Hs.
   Qed.
   
   Lemma subset_refl : forall (s : seq node), subset s s = true.
   Proof.
   move => s.
   rewrite -{2}(cat0s s) subset_cat //.
   Qed.
   
   Lemma subset_nil : forall (s : seq node), subset s [::] -> s = [::].
   Proof.
   elim => [s|a l _].
   * reflexivity.
   * rewrite /subset in_nil andFb //.
   Qed.
   
   Lemma in_subset_trans : forall (s : seq node) (x : node) (t : seq node),
      x \in s -> subset s t -> x \in t.
   Proof.
   elim => [x|a l IHs x].
   * rewrite in_nil //.
   * rewrite in_cons.
     move =>> /orP [/eqP H|H] /andP [Ha Hl].
     + rewrite H Ha //.
     + rewrite IHs //.
   Qed.
   
   Lemma subset_trans : forall (t s u : seq node),
      subset s t -> subset t u -> subset s u.
   Proof.
   induction s.
   * rewrite /subset //.
   * move => u /andP [Ha Hs] H0.
     simpl subset.
     rewrite (in_subset_trans t) // andTb IHs //.
   Qed.
   
   Local Lemma respects_topological_order_gx :
      forall (v : seq node) (x : node),
         respects_topological_order v -> x \in v -> subset (g x) v.
   Proof.
   elim => [x _|a v IHv x].
   * rewrite in_nil //.
   * rewrite in_cons.
     move => /andP [/andP [H H1] H2] H0.
     apply (subset_trans v).
     + destruct (eqVneq x a).
       - rewrite e H //.
       - rewrite IHv //.
     + rewrite -cat1s subset_cat //.
   Qed.
   
   Definition disjoint (s t : seq node) :=
      forall (x : node), (x \notin s) || (x \notin t).
   
   Theorem topo_tree_correct :
      forall (n : nat) (gray_nodes already_found : seq node) (root : node),
         size vertices <= size gray_nodes + n ->
         subset gray_nodes vertices ->
         subset already_found vertices ->
         disjoint gray_nodes already_found ->
         root \in vertices ->
         path_from root gray_nodes ->
         respects_topological_order already_found ->
            match topo_tree n gray_nodes root (Sorted already_found) with
            | Sorted result => subset already_found result /\
                             disjoint gray_nodes result /\
                             root \in result /\
                             subset result vertices /\
                             respects_topological_order result
            | Cycle _ => ~graph_acyclic
            | _ => False
            end.
   Proof.
   induction n.
   * intros gray_nodes already_found root Hn Hgray_nodes_closed Halready_found_closed Hdisjoint Hroot_ok Hpath_ok Halready_found_ok.
     rewrite addn0 in Hn.
     simpl topo_tree.
     (* we prove that root \in gray_nodes, through the following steps:
        1. uniq gray_nodes (because of path_from root gray_nodes
        2. subset vertices gray_nodes (because there are at least as many gray nodes as
                                       vertices, as per precondition, and because of 1.)
     *)
     assert (Hgray_nodes_uniq : uniq gray_nodes).
           clear -Hpath_ok.
           move : root Hpath_ok.
           induction gray_nodes.
           + rewrite /uniq //.
           + simpl path_from.
             intros.
             simpl uniq.
             move /andP : Hpath_ok => [/andP [_ Ha_ni_p] Hpf].
             rewrite Ha_ni_p andTb.
             apply IHgray_nodes with (root := a) ; exact Hpf.
   (*assert (forall (p : seq node) (a : node), uniq p -> a \notin rem a p).
           clear.
           induction p.
           + intros ; rewrite /rem in_nil //.
           + intros b Hu.
             rewrite cons_uniq in Hu ; move /andP : Hu => Hu.
             destruct (eqVneq a b).
             - rewrite -e /rem eq_refl ; apply Hu.
             - apply negbTE in i.
               rewrite rem_cons i in_cons eq_sym i orFb.
               apply IHp, Hu. *)
     assert (subset_remr : forall (p q : seq node) (a : node), a \notin p -> subset p q -> subset p (rem a q)).
           clear.
           induction p.
           + rewrite {2}/subset //.
           + simpl subset.
             intros q b H H0.
             rewrite in_cons negb_or in H ; move /andP : H => [H H1].
             apply (@rwP (a \in rem b q /\ subset p (rem b q))) ; try exact andP.
             move /andP : H0 => [H0 H2].
             split.
             - clear -H H0.
               induction q.
               * rewrite in_nil in H0 ; done.
               * rewrite in_cons in H0.
                 move /orP : H0 => [H0|H0].
                 + move /eqP : H0 => H0.
                   apply negbTE in H.
                   rewrite rem_cons eq_sym -H0 H mem_head //.
                 + rewrite rem_cons.
                   destruct (a0 == b) ; try exact H0.
                   rewrite in_cons.
                   apply (@rwP (a == a0 \/ a \in rem b q)) ; try apply orP.
                   right ; rewrite IHq //.
             - rewrite IHp //.
     assert (subset_reml : forall (q p : seq node) (a : node), subset (rem a q) p -> subset q (a :: p)).
           clear.
           elim => [p a _|a q IHq p b].
           + rewrite /subset //.
           + rewrite rem_cons.
             destruct (eqVneq a b).
             - rewrite e.
               apply subset_cons_cons.
             - apply negbTE in i.
               move /andP => [Ha Hb].
               rewrite /subset in_cons i orFb Ha andTb.
               apply IHq, Hb.
     assert (Hroot_in_gray_nodes : root \in gray_nodes).
           apply (in_subset_trans vertices) ; try trivial.
           clear -Hn Hgray_nodes_closed Hgray_nodes_uniq subset_reml subset_remr.
           move : vertices Hn Hgray_nodes_closed Hgray_nodes_uniq.
           induction gray_nodes.
           + unfold size at 2.
             intros.
             rewrite leqn0 in Hn ; move /nilP : Hn => Hn ; rewrite Hn.
             apply subset_refl.
           + intros.
             simpl size at 2 in Hn.
             simpl subset in Hgray_nodes_closed ; move /andP : Hgray_nodes_closed => Hgray_nodes_closed.
             simpl uniq in Hgray_nodes_uniq ; move /andP : Hgray_nodes_uniq => Hgray_nodes_uniq.
             apply subset_reml, IHgray_nodes.
             - rewrite size_rem ; try apply Hgray_nodes_closed.
               rewrite leqNgt ltn_predRL -leqNgt Hn //.
             - apply subset_remr ; try apply Hgray_nodes_uniq ; apply Hgray_nodes_closed.
             - apply Hgray_nodes_uniq.
     rewrite Hroot_in_gray_nodes /graph_acyclic.
     rewrite <- negbK in Hroot_in_gray_nodes.
     move /negP : Hroot_in_gray_nodes => Hroot_in_gray_nodes.
     contradict Hroot_in_gray_nodes ; rename Hroot_in_gray_nodes into Hgraph_acyclic.
     apply Hgraph_acyclic ; trivial.
   * intros gray_nodes already_found root Hn Hgray_nodes_closed Halready_found_closed Hdisjoint Hroot_ok Hpath_ok Halready_found_ok.
     simpl topo_tree.
     destruct (root \in gray_nodes) eqn: Hroot_in_gray_nodes.
     + unfold graph_acyclic.
       rewrite <- negbK in Hroot_in_gray_nodes.
       move /negP : Hroot_in_gray_nodes => Hroot_in_gray_nodes.
       contradict Hroot_in_gray_nodes ; rename Hroot_in_gray_nodes into Hgraph_acyclic.
       apply Hgraph_acyclic ; trivial.
     + destruct (root \in already_found) eqn: Hroot_in_already_found.
       - split ; try apply subset_refl.
         split ; try apply Hdisjoint.
         rewrite Hroot_in_already_found Halready_found_closed Halready_found_ok //.
       - assert (foldr_topo_tree_correct :
            forall (adjacents : seq node), subset adjacents (g root) ->
                  match foldr (topo_tree n (root :: gray_nodes)) (Sorted already_found) adjacents with
                  | Sorted result => subset already_found result /\
                                   disjoint (root :: gray_nodes) result /\
                                   subset adjacents result /\
                                   subset result vertices /\
                                   respects_topological_order result
                  | Cycle _ => ~graph_acyclic
                  | _ => False
                  end).
             induction adjacents.
             * intro.
               unfold foldr.
               split ; try apply subset_refl.
               split.
               + unfold disjoint ; intro.
                 rewrite in_cons.
                 destruct (eqVneq x root).
                 - rewrite orTb orFb e Hroot_in_already_found //.
                 - rewrite orFb ; apply Hdisjoint.
               + simpl subset ; rewrite Halready_found_closed Halready_found_ok //.
             * simpl foldr.
               move /andP => [Ha Hadjacents].
               destruct (foldr (topo_tree n (root :: gray_nodes)) (Sorted already_found) adjacents) ;
                     try (simpl topo_tree ; destruct n ; simpl subset ;
                          apply IHadjacents, Hadjacents).
               assert (IHn' : match topo_tree n (root :: gray_nodes) a (Sorted l) with
                              | Sorted result =>
                                   subset l result /\
                                   disjoint (root :: gray_nodes) result /\
                                   a \in result /\
                                   subset result vertices /\
                                   respects_topological_order result
                              | Cycle _ => ~ graph_acyclic
                              | N_too_small => False
                              end).
                     apply IHn ; try apply IHadjacents, Hadjacents.
                     + rewrite {2}/size addSnnS ; exact Hn.
                     + simpl subset ; rewrite Hroot_ok Hgray_nodes_closed //.
                     + apply (in_subset_trans (g root)) ; try apply Ha.
                       apply graph_closed, Hroot_ok.
                     + simpl path_from ; rewrite Ha Hroot_in_gray_nodes Hpath_ok //.
               clear IHn.
               destruct (topo_tree n (root :: gray_nodes) a (Sorted l)) ;
                     try exact IHn'.
               split.
               + apply (subset_trans l) ; try apply IHn'.
                 apply IHadjacents, Hadjacents.
               split.
               + apply IHn'.
               split.
               + simpl subset at 1.
                 apply (@rwP (a \in l0 /\ subset adjacents l0)) ; try exact andP.
                 split ; try apply IHn'.
                 apply (subset_trans l) ; try apply IHn'.
                 apply IHadjacents, Hadjacents.
               + apply IHn'.
         specialize foldr_topo_tree_correct with (adjacents := g root).
         destruct (foldr (topo_tree n (root :: gray_nodes)) 
                         (Sorted already_found) (g root)) eqn: Hfoldr_topo_tree ;
               try (apply foldr_topo_tree_correct, subset_refl).
         assert (disjoint (root :: gray_nodes) l) by (apply foldr_topo_tree_correct, subset_refl).
         split.
         * apply (subset_trans l) ; try (apply foldr_topo_tree_correct, subset_refl).
           rewrite -cat1s subset_cat //.
         split.
         * unfold disjoint ; intro.
           rewrite in_cons negb_or.
           destruct (eqVneq x root).
           + rewrite andFb orbF e Hroot_in_gray_nodes //.
           + unfold disjoint in H ; specialize H with (x := x).
             rewrite in_cons negb_or i andTb in H.
             rewrite andTb H //.
         split.
         * apply mem_head.
         split.
         * rewrite /subset Hroot_ok andTb.
           apply foldr_topo_tree_correct, subset_refl.
         * simpl respects_topological_order.
           apply (@rwP (subset (g root) l && (root \notin l) /\ respects_topological_order l)) ; try exact andP.
           split ; try (apply foldr_topo_tree_correct, subset_refl).
           apply (@rwP (subset (g root) l /\ root \notin l)) ; try exact andP.
           split ; try (apply foldr_topo_tree_correct, subset_refl).
           unfold disjoint in H ; specialize H with (x := root).
           rewrite mem_head orFb in H.
           exact H.
   Qed.
   
   Lemma index_behead :
      forall (x y : node) (s : seq node), x != y -> index x (y :: s) = (index x s).+1.
   Proof.
   move => x y s /negbTE Hx_ne_y.
   rewrite {1}/index -cat1s find_cat /has orbF pred1E Hx_ne_y.
   done.
   Qed.
   
   Theorem topo_sort_correct :
      match topo_sort with
      | Sorted result => graph_acyclic /\
                       subset vertices result /\
                       subset result vertices /\
                       respects_topological_order result
      | Cycle _ => ~graph_acyclic
      | _ => False
      end.
   Proof.
   (* mainly use topo_tree_correct. *)
   unfold topo_sort.
   assert (foldr_topo_sort_correct : forall v : seq node,
      subset v vertices ->
         match foldr (topo_tree (size vertices) [::]) (Sorted [::]) v with
         | Sorted result => subset v result /\
                          subset result vertices /\
                          respects_topological_order result
         | Cycle _ => ~ graph_acyclic
         | N_too_small => False
         end).
         induction v.
         * intro ; unfold foldr.
           split ; try apply subset_refl.
           split ; trivial.
         * move /andP => [Ha_in_vertices Hv_in_vertices].
           simpl foldr.
           destruct (foldr (topo_tree (size vertices) [::]) (Sorted [::]) v) ;
                 try (simpl topo_tree ; destruct (size vertices) ;
                      apply IHv, Hv_in_vertices).
           assert (match topo_tree (size vertices) [::] a (Sorted l) with
                   | Sorted result => subset l result /\
                                    disjoint [::] result /\
                                    a \in result /\
                                    subset result vertices /\
                                    respects_topological_order result
                   | Cycle _ => ~graph_acyclic
                   | _ => False
                   end).
                 apply topo_tree_correct ; try done ; apply IHv, Hv_in_vertices.
           destruct (topo_tree (size vertices) [::] a (Sorted l)) ; try exact H.
           split ; try apply H.
           simpl subset.
           apply (@rwP (a \in l0 /\ subset v l0)) ; try exact andP.
           split ; try apply H.
           apply (subset_trans l) ; try apply H.
           apply IHv, Hv_in_vertices.
   specialize foldr_topo_sort_correct with (v := vertices).
   destruct (foldr (topo_tree (size vertices) [::]) (Sorted [::]) vertices) ;
         try (apply foldr_topo_sort_correct, subset_refl).
   split ; try (apply foldr_topo_sort_correct, subset_refl).
   unfold graph_acyclic.
   intros.
   assert (Huniq : uniq l).
         assert (respects_topological_order l) by (apply foldr_topo_sort_correct, subset_refl).
         clear -H2.
         induction l.
         * rewrite /uniq //.
         * simpl uniq.
           simpl respects_topological_order in H2.
           move /andP : H2 => [/andP [_ Ha_notin_l] Hrespects_topological_order].
           rewrite Ha_notin_l andTb.
           apply IHl, Hrespects_topological_order.
   assert (forall (x y : node), x \in l -> y \in l -> y \in g x -> index x l < index y l).
         assert (respects_topological_order l) by (apply foldr_topo_sort_correct, subset_refl).
         clear -Huniq H2.
         induction l.
         * intro ; rewrite in_nil //.
         * intros x y.
           simpl uniq in Huniq.
           move /andP : Huniq => [Ha_notin_l Huniq].
           destruct (eqVneq x a).
           + rewrite !e ; intros.
             simpl respects_topological_order in H2 ;
             move /andP : H2 => [/andP [Hg_a_l _] Hrespects_topological_order_l].
             rewrite index_head index_behead.
             - apply ltn0Sn.
             - revert Ha_notin_l ; apply contra ; move /eqP => Hy_eq_a ; rewrite -Hy_eq_a.
               apply (in_subset_trans (g a)) ; trivial.
           + rewrite index_behead ; try (exact i).
             intros.
             apply negbTE in i.
             rewrite in_cons in H ; rewrite i in H ; rewrite orFb in H.
             move /andP : H2 => [_ H2].
             assert (y != a).
                   revert Ha_notin_l ; apply contra ; move /eqP => Hy_eq_a ; rewrite -Hy_eq_a.
                   apply (in_subset_trans (g x)) ; try exact H1.
                   apply respects_topological_order_gx ; done.
             rewrite index_behead ; try exact H3.
             apply negbTE in H3.
             rewrite in_cons in H0 ; rewrite H3 in H0 ; rewrite orFb in H0.
             rewrite ltnS.
             apply IHl ; done.
   assert (subset p (take (index r l) l)).
         move : r H0 H H1.
         induction p.
         * intros ; rewrite /subset //.
         * intros.
           specialize IHp with (r := a).
           simpl path_from in H1 ;
           move : H1 => /andP [/andP [Hr_in_ga Ha_notin_p] Hpath_from].
           simpl subset.
           apply (@rwP (a \in take (index r l) l /\ subset p (take (index r l) l))) ; try exact andP.
           move /andP : H0 => H0.
           assert (index a l < index r l).
                 apply H2 ; try done.
                 + apply (in_subset_trans vertices) ; try apply H0.
                   apply foldr_topo_sort_correct, subset_refl.
                 + apply (in_subset_trans vertices) ; try apply H.
                   apply foldr_topo_sort_correct, subset_refl.
           split.
           + rewrite in_take_leq ; try exact H1.
             apply index_size.
           + apply (subset_trans (take (index a l) l)).
             - apply IHp ; try done ; apply H0.
             - clear -H1.
               induction l.
               * rewrite /take /subset //.
               * destruct (eqVneq a a0).
                 + rewrite -!e index_head take0 /subset //.
                 + assert (r != a0).
                         revert H1 ; apply contraL ; move /eqP => H1.
                         rewrite H1 index_head ltn0 //.
                   rewrite (index_behead _ _ _ i) take_cons
                           (index_behead _ _ _ H) take_cons.
                   apply subset_cons_cons, IHl.
                   rewrite -ltnS -(index_behead _ a0 _ i) -(index_behead _ a0 _ H) //.
   move : (ltnn (index r l)) ; apply contraFN ; intro.
   rewrite -has_take.
   + rewrite has_find index_mem (in_subset_trans p) //.
   + rewrite has_find index_mem (in_subset_trans vertices) //.
     apply foldr_topo_sort_correct, subset_refl.
   Qed.
   End TopoSortS.
   End TopoSort.
   