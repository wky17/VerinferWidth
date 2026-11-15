From Coq Require Import NArith ZArith.
From mathcomp Require Import all_ssreflect.
From firrtl Require Import Env HiEnv HiFirrtl.
From firrtl Require Import HiEnv_with_implicit_widths Env_with_implicit_widths.
From Solver Require Import constraints floyd_sc extract_cs extract_cswithmin graph inferWidths inferWidths_exp.
From Semantics Require Import Width_solution_bridge.
From Semantics Require Import Width_bridge_proofs.

Delimit Scope N_scope with nvar.

Definition reset_example : common_module :=
  {| common_module_name := 0%nvar;
     common_ports := [:: CClock 0%nvar; CInput 1%nvar (UIntExplicit 1)];
     common_stmts :=
       [:: CReg 2%nvar UIntImplicit 0%nvar
             (CReset 1%nvar (CUInt 8 [::]))] |}.

Definition reset_solver_map :=
  SolverSyntax.circuit_tmap (solver_circuit 0%nvar reset_example).

Example reset_example_controls_valid :
  match reset_solver_map with
  | Some tmap => valid_controls reset_example tmap
  | None => False
  end.
Proof. vm_compute. eauto. Qed.

Example reset_example_semantic_result :
  match Semantics.circuit_tmap_uninferred (sem_circuit reset_example),
        Semantics.circuit_tmap_implicits (sem_circuit reset_example) 1 with
  | Some initial, Some result =>
      original_implicit initial 0%nvar 2%nvar /\
      semantic_width result 0%nvar 2%nvar = Some 8
  | _, _ => False
  end.
Proof. vm_compute. auto. Qed.

Definition reset_example_constraints :=
  match reset_solver_map with
  | Some tmap =>
      match extract_constraint_m (solver_module reset_example) tmap with
      | Some (c1map, _, _) => SolverSyntax.PVM.find (2%nvar, N0) c1map
      | None => None
      end
  | None => None
  end.

Example reset_example_extracted_width :
  option_map (map rhs_const1) reset_example_constraints = Some [:: 8%Z].
Proof. vm_compute. reflexivity. Qed.

Example reset_example_circuit_extraction_bridge :
  match reset_solver_map with
  | Some tmap =>
      extract_constraints_c (solver_circuit 0%nvar reset_example) tmap =
        option_map (fun next => ([:: next], [::]))
          (common_extract_steps tmap (SolverSyntax.PVM.empty _)
            (rev (common_stmts reset_example)))
  | None => False
  end.
Proof.
  vm_compute. reflexivity.
Qed.

Example reset_example_initial_tmaps_related :
  match reset_solver_map,
        Semantics.circuit_tmap_uninferred (sem_circuit reset_example) with
  | Some solver_map, Some initial =>
      exists sem_map,
        SemSyntax.VM.find 0%nvar initial = Some sem_map /\
        scalar_maps_related solver_map sem_map
  | _, _ => False
  end.
Proof.
  have Hsolver : exists solver_map, reset_solver_map = Some solver_map by
    vm_compute; eauto.
  have Hsem : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit reset_example) = Some initial
    by vm_compute; eauto.
  destruct Hsolver as [solver_map Hsolver].
  destruct Hsem as [initial Hsem].
  rewrite Hsolver Hsem.
  change (exists sem_map,
    SemSyntax.VM.find (common_module_name reset_example) initial = Some sem_map /\
    scalar_maps_related solver_map sem_map).
  apply: (initial_circuit_tmaps_related (m := reset_example) (circuit_name := 0%nvar)).
  - exact Hsolver.
  - exact Hsem.
Qed.

Example reset_example_all_semantic_bounds :
  match reset_solver_map,
        Semantics.circuit_tmap_implicits (sem_circuit reset_example) 1 with
  | Some solver_map, Some result =>
      match SemSyntax.VM.find 0%nvar result with
      | Some sem_map =>
          List.Forall (common_step_semantic_bound sem_map solver_map)
            (rev (common_stmts reset_example))
      | None => False
      end
  | _, _ => False
  end.
Proof. vm_compute. eauto 12. Qed.

Example reset_example_constraint_requires_eight :
  let rhs := make_rhs [::] [::] 8%Z in
  let too_small := SolverSyntax.PVM.add (2%nvar, N0) 7 (SolverSyntax.PVM.empty _) in
  let enough := SolverSyntax.PVM.add (2%nvar, N0) 8 (SolverSyntax.PVM.empty _) in
  satisfies_constraint1 too_small (common_constraint 2%nvar rhs) = false /\
  satisfies_constraint1 enough (common_constraint 2%nvar rhs) = true.
Proof. vm_compute. split; reflexivity. Qed.

Example duplicate_ports_are_rejected_by_both_maps :
  let m := {| common_module_name := 0%nvar;
              common_ports := [:: CInput 7%nvar UIntImplicit;
                                  COutput 7%nvar (SIntExplicit 2)];
              common_stmts := [::] |} in
  SolverSyntax.circuit_tmap (solver_circuit 0%nvar m) = None /\
  Semantics.circuit_tmap_uninferred (sem_circuit m) = None.
Proof. vm_compute. split; reflexivity. Qed.

Example self_reference_preserves_width_and_kind :
  let tmap := SemSyntax.VM.add 9%nvar
    (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit 5),
     HiEnv_with_implicit_widths.Wire) (SemSyntax.VM.empty _) in
  match Semantics.width_iter_one tmap (sem_stmt (CConnect 9%nvar (CRef 9%nvar))) with
  | Some updated => SemSyntax.VM.find 9%nvar updated
  | None => None
  end =
    Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit 5),
          HiEnv_with_implicit_widths.Wire).
Proof. vm_compute. reflexivity. Qed.

Example signed_reference_grows_destination_only :
  let tmap := SemSyntax.VM.add 9%nvar
    (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit 2),
     HiEnv_with_implicit_widths.Wire)
    (SemSyntax.VM.add 10%nvar
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit 6),
       HiEnv_with_implicit_widths.In_port) (SemSyntax.VM.empty _)) in
  match Semantics.width_iter_one tmap (sem_stmt (CConnect 9%nvar (CRef 10%nvar))) with
  | Some updated =>
      (SemSyntax.VM.find 9%nvar updated, SemSyntax.VM.find 10%nvar updated)
  | None => (None, None)
  end =
    (Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit 6),
           HiEnv_with_implicit_widths.Wire),
     Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit 6),
           HiEnv_with_implicit_widths.In_port)).
Proof. vm_compute. reflexivity. Qed.

Example explicit_destination_width_stays_fixed :
  let tmap := SemSyntax.VM.add 9%nvar
    (sem_type (UIntExplicit 2), HiEnv_with_implicit_widths.Wire) (SemSyntax.VM.empty _) in
  match Semantics.width_iter_one tmap (sem_stmt (CConnect 9%nvar (CUInt 8 [::]))) with
  | Some updated => SemSyntax.VM.find 9%nvar updated
  | None => None
  end = Some (sem_type (UIntExplicit 2), HiEnv_with_implicit_widths.Wire).
Proof. vm_compute. reflexivity. Qed.

Definition reference_example : common_module :=
  {| common_module_name := 0%nvar;
     common_ports := [:: CClock 0%nvar; CInput 1%nvar (UIntExplicit 1)];
     common_stmts :=
       [:: CReg 3%nvar UIntImplicit 0%nvar (CReset 1%nvar (CRef 2%nvar));
           CWire 2%nvar UIntImplicit;
           CConnect 2%nvar (CUInt 6 [::])] |}.

Example reference_example_semantic_result :
  match Semantics.circuit_tmap_uninferred (sem_circuit reference_example),
        Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 with
  | Some initial, Some result =>
      original_implicit initial 0%nvar 2%nvar /\
      original_implicit initial 0%nvar 3%nvar /\
      semantic_width result 0%nvar 2%nvar = Some 6 /\
      semantic_width result 0%nvar 3%nvar = Some 6
  | _, _ => False
  end.
Proof. vm_compute. auto. Qed.

Example reference_example_iteration_growth :
  match SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example),
        Semantics.circuit_tmap_uninferred (sem_circuit reference_example),
        Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 with
  | Some solver_map, Some initial, Some result =>
      exists before after,
        SemSyntax.VM.find 0%nvar initial = Some before /\
        SemSyntax.VM.find 0%nvar result = Some after /\
        semantic_map_growth before after /\
        scalar_maps_related solver_map after
  | _, _, _ => False
  end.
Proof.
  have [solver_map Hsolver] : exists solver_map,
      SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) = Some solver_map
    by vm_compute; eauto.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit reference_example) = Some initial
    by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 = Some result
    by vm_compute; eauto.
  rewrite Hsolver Hinitial Hresult.
  change (exists before after,
    SemSyntax.VM.find (common_module_name reference_example) initial = Some before /\
    SemSyntax.VM.find (common_module_name reference_example) result = Some after /\
    semantic_map_growth before after /\ scalar_maps_related solver_map after).
  exact: (common_successful_result_growth Hsolver Hinitial Hresult).
Qed.

Example reference_example_initial_and_result_operands_ready :
  match SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example),
        Semantics.circuit_tmap_uninferred (sem_circuit reference_example),
        Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 with
  | Some solver_map, Some initial, Some result =>
      exists before after,
        SemSyntax.VM.find 0%nvar initial = Some before /\
        SemSyntax.VM.find 0%nvar result = Some after /\
        semantic_map_growth before after /\
        scalar_maps_related solver_map after /\
        List.Forall (common_step_semantic_ready before solver_map)
          (rev (common_stmts reference_example)) /\
        List.Forall (common_step_semantic_ready after solver_map)
          (rev (common_stmts reference_example))
  | _, _, _ => False
  end.
Proof.
  have [solver_map Hsolver] : exists solver_map,
      SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) = Some solver_map
    by vm_compute; eauto.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit reference_example) = Some initial
    by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 = Some result
    by vm_compute; eauto.
  rewrite Hsolver Hinitial Hresult.
  change (exists before after,
    SemSyntax.VM.find (common_module_name reference_example) initial = Some before /\
    SemSyntax.VM.find (common_module_name reference_example) result = Some after /\
    semantic_map_growth before after /\ scalar_maps_related solver_map after /\
    List.Forall (common_step_semantic_ready before solver_map)
      (rev (common_stmts reference_example)) /\
    List.Forall (common_step_semantic_ready after solver_map)
      (rev (common_stmts reference_example))).
  exact: (successful_circuit_initial_operands_ready Hsolver Hinitial Hresult).
Qed.

Definition zero_iteration_example : common_module :=
  {| common_module_name := 0%nvar;
     common_ports := [:: CClock 0%nvar; CInput 1%nvar (UIntExplicit 1)];
     common_stmts := [:: CReg 2%nvar UIntImplicit 0%nvar
       (CReset 1%nvar (CUInt 0 [::]))] |}.

Example reference_example_fixed_round_has_stable_middle_step :
  exists solver_map initial result sem_map next before after,
    SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) =
      Some solver_map /\
    Semantics.circuit_tmap_uninferred (sem_circuit reference_example) = Some initial /\
    Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 = Some result /\
    SemSyntax.VM.find 0%nvar result = Some sem_map /\
    Semantics.width_iter sem_map (sem_stmts
      [:: CReg 3%nvar UIntImplicit 0%nvar (CReset 1%nvar (CRef 2%nvar));
          CWire 2%nvar UIntImplicit]) = Some before /\
    Semantics.width_iter_one before (sem_stmt (CConnect 2%nvar (CUInt 6 [::]))) =
      Some after /\
    (forall id, SemSyntax.VM.find id sem_map = SemSyntax.VM.find id before) /\
    (forall id, SemSyntax.VM.find id before = SemSyntax.VM.find id after) /\
    Semantics.width_iter after (sem_stmts [::]) = Some next.
Proof.
  have [solver_map Hsolver] : exists solver_map,
      SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) = Some solver_map
    by vm_compute; eauto.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit reference_example) = Some initial
    by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 = Some result
    by vm_compute; eauto.
  have [sem_map [next [Hfind [_ [_ [_ Htrace]]]]]] :=
    successful_circuit_result_stable_width_trace Hsolver Hinitial Hresult.
  have Hsplit : common_stable_width_trace sem_map sem_map
      ([:: CReg 3%nvar UIntImplicit 0%nvar (CReset 1%nvar (CRef 2%nvar));
           CWire 2%nvar UIntImplicit] ++
       CConnect 2%nvar (CUInt 6 [::]) :: [::]) next := Htrace.
  have [before [after [Hprefix [Hstep [Hbefore [Hafter Hsuffix]]]]]] :=
    common_stable_width_trace_split Hsplit.
  by exists solver_map, initial, result, sem_map, next, before, after.
Qed.

Example reference_example_one_round_is_not_yet_fixed :
  Semantics.circuit_tmap_implicits (sem_circuit reference_example) 1 = None.
Proof. vm_compute. reflexivity. Qed.

Definition self_reference_example : common_module :=
  {| common_module_name := 0%nvar;
     common_ports := [::];
     common_stmts := [:: CWire 9%nvar UIntImplicit;
                         CConnect 9%nvar (CRef 9%nvar)] |}.

Example self_reference_example_has_stable_trace :
  exists solver_map initial result sem_map next,
    SolverSyntax.circuit_tmap (solver_circuit 0%nvar self_reference_example) =
      Some solver_map /\
    Semantics.circuit_tmap_uninferred (sem_circuit self_reference_example) = Some initial /\
    Semantics.circuit_tmap_implicits (sem_circuit self_reference_example) 0 = Some result /\
    SemSyntax.VM.find 0%nvar result = Some sem_map /\
    common_stable_width_trace sem_map sem_map (common_stmts self_reference_example) next.
Proof.
  have [solver_map Hsolver] : exists solver_map,
      SolverSyntax.circuit_tmap (solver_circuit 0%nvar self_reference_example) =
        Some solver_map by vm_compute; eauto.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit self_reference_example) =
        Some initial by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit self_reference_example) 0 =
        Some result by vm_compute; eauto.
  have [sem_map [next [Hfind [_ [_ [_ Htrace]]]]]] :=
    successful_circuit_result_stable_width_trace Hsolver Hinitial Hresult.
  by exists solver_map, initial, result, sem_map, next.
Qed.

Example reference_example_fixed_result_has_all_bounds :
  exists solver_map initial result sem_map,
    SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) =
      Some solver_map /\
    Semantics.circuit_tmap_uninferred (sem_circuit reference_example) = Some initial /\
    Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 = Some result /\
    SemSyntax.VM.find 0%nvar result = Some sem_map /\
    List.Forall (common_step_semantic_bound sem_map solver_map)
      (common_stmts reference_example) /\
    List.Forall (common_step_semantic_bound sem_map solver_map)
      (rev (common_stmts reference_example)).
Proof.
  have [solver_map Hsolver] : exists solver_map,
      SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) =
        Some solver_map by vm_compute; eauto.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit reference_example) =
        Some initial by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 =
        Some result by vm_compute; eauto.
  have [sem_map [Hfind [_ [Hforward Hreverse]]]] :=
    successful_result_semantic_bounds Hsolver Hinitial Hresult.
  by exists solver_map, initial, result, sem_map.
Qed.

Example reference_example_matching_values_satisfy_extracted_constraints value :
  exists solver_map initial result cmap sem_map,
    SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) =
      Some solver_map /\
    Semantics.circuit_tmap_uninferred (sem_circuit reference_example) = Some initial /\
    Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 = Some result /\
    extract_constraints_c (solver_circuit 0%nvar reference_example) solver_map =
      Some ([:: cmap], [::]) /\
    SemSyntax.VM.find 0%nvar result = Some sem_map /\
    (valuation_matches_sem_map value sem_map ->
      List.forallb (satisfies_constraint1 value)
        (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true).
Proof.
  have [solver_map Hsolver] : exists solver_map,
      SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) =
        Some solver_map by vm_compute; eauto.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit reference_example) =
        Some initial by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 =
        Some result by vm_compute; eauto.
  have [cmap Hextract] : exists cmap,
      extract_constraints_c (solver_circuit 0%nvar reference_example) solver_map =
        Some ([:: cmap], [::]).
  { vm_compute in Hsolver. inversion Hsolver; subst solver_map.
    by vm_compute; eauto. }
  have [sem_map [Hfind Hsatisfies]] :=
    successful_result_matching_valuation_satisfies_constraints value
      Hsolver Hinitial Hresult Hextract.
  by exists solver_map, initial, result, cmap, sem_map.
Qed.

Example self_reference_fixed_result_has_all_bounds :
  exists solver_map initial result sem_map,
    SolverSyntax.circuit_tmap (solver_circuit 0%nvar self_reference_example) =
      Some solver_map /\
    Semantics.circuit_tmap_uninferred (sem_circuit self_reference_example) = Some initial /\
    Semantics.circuit_tmap_implicits (sem_circuit self_reference_example) 0 = Some result /\
    SemSyntax.VM.find 0%nvar result = Some sem_map /\
    List.Forall (common_step_semantic_bound sem_map solver_map)
      (common_stmts self_reference_example).
Proof.
  have [solver_map Hsolver] : exists solver_map,
      SolverSyntax.circuit_tmap (solver_circuit 0%nvar self_reference_example) =
        Some solver_map by vm_compute; eauto.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit self_reference_example) =
        Some initial by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit self_reference_example) 0 =
        Some result by vm_compute; eauto.
  have [sem_map [Hfind [_ [Hbounds _]]]] :=
    successful_result_semantic_bounds Hsolver Hinitial Hresult.
  by exists solver_map, initial, result, sem_map.
Qed.

Definition signed_bounds_example : common_module :=
  {| common_module_name := 0%nvar;
     common_ports := [:: CClock 0%nvar; CInput 1%nvar (UIntExplicit 1)];
     common_stmts := [:: CReg 2%nvar SIntImplicit 0%nvar
       (CReset 1%nvar (CSInt 5 [::]));
       CWire 3%nvar SIntImplicit;
       CConnect 3%nvar (CRef 2%nvar)] |}.

Example signed_bounds_example_result_widths :
  match Semantics.circuit_tmap_implicits (sem_circuit signed_bounds_example) 1 with
  | Some result =>
      (semantic_width result 0%nvar 2%nvar, semantic_width result 0%nvar 3%nvar)
  | None => (None, None)
  end = (Some 5, Some 5).
Proof. vm_compute. reflexivity. Qed.

Example signed_fixed_result_has_all_bounds :
  exists solver_map initial result sem_map,
    SolverSyntax.circuit_tmap (solver_circuit 0%nvar signed_bounds_example) =
      Some solver_map /\
    Semantics.circuit_tmap_uninferred (sem_circuit signed_bounds_example) = Some initial /\
    Semantics.circuit_tmap_implicits (sem_circuit signed_bounds_example) 1 = Some result /\
    SemSyntax.VM.find 0%nvar result = Some sem_map /\
    List.Forall (common_step_semantic_bound sem_map solver_map)
      (common_stmts signed_bounds_example).
Proof.
  have [solver_map Hsolver] : exists solver_map,
      SolverSyntax.circuit_tmap (solver_circuit 0%nvar signed_bounds_example) =
        Some solver_map by vm_compute; eauto.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit signed_bounds_example) =
        Some initial by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit signed_bounds_example) 1 =
        Some result by vm_compute; eauto.
  have [sem_map [Hfind [_ [Hbounds _]]]] :=
    successful_result_semantic_bounds Hsolver Hinitial Hresult.
  by exists solver_map, initial, result, sem_map.
Qed.

Definition unused_implicit_example : common_module :=
  {| common_module_name := 0%nvar;
     common_ports := [:: CInput 10%nvar UIntImplicit;
                         COutput 11%nvar SIntImplicit;
                         CInput 12%nvar (UIntExplicit 4)];
     common_stmts := [::] |}.

Example semantic_valuation_keeps_unconstrained_implicit_positions :
  match Semantics.circuit_tmap_implicits (sem_circuit unused_implicit_example) 0 with
  | Some result =>
      match SemSyntax.VM.find 0%nvar result with
      | Some sem_map =>
          (solver_width (semantic_valuation sem_map) 10%nvar,
           solver_width (semantic_valuation sem_map) 11%nvar,
           solver_width (semantic_valuation sem_map) 12%nvar,
           solver_width (semantic_valuation sem_map) 99%nvar,
           SolverSyntax.PVM.find (10%nvar, 1%nvar) (semantic_valuation sem_map))
      | None => (None, None, None, None, None)
      end
  | None => (None, None, None, None, None)
  end = (Some 0, Some 0, None, None, None).
Proof. vm_compute. reflexivity. Qed.

Example explicit_solver_key_cannot_be_compared_to_implicit_only_valuation :
  let sem_map := SemSyntax.VM.add 12%nvar
    (sem_type (UIntExplicit 4), HiEnv_with_implicit_widths.In_port)
    (SemSyntax.VM.empty _) in
  let solver_value := SolverSyntax.PVM.add (12%nvar, N0) 0 (SolverSyntax.PVM.empty _) in
  ~ constraints.le solver_value (semantic_valuation sem_map).
Proof.
  move=> sem_map solver_value Hle.
  have Hfind : SolverSyntax.PVM.find (12%nvar, N0) solver_value = Some 0
    by vm_compute.
  have [w [Hmissing _]] := Hle (12%nvar, N0) 0 Hfind.
  vm_compute in Hmissing. discriminate.
Qed.

Example empty_valuation_does_not_cover_unused_implicit :
  match Semantics.circuit_tmap_uninferred (sem_circuit unused_implicit_example) with
  | Some initial => ~ covered (SolverSyntax.PVM.empty _) initial 0%nvar
  | None => False
  end.
Proof.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit unused_implicit_example) =
        Some initial by vm_compute; eauto.
  rewrite Hinitial.
  move=> Hcover.
  have Horiginal : original_implicit initial 0%nvar 10%nvar.
  { vm_compute in Hinitial. inversion Hinitial; subst initial. by vm_compute. }
  have [w Hmissing] := Hcover 10%nvar Horiginal.
  by rewrite /solver_width SolverSyntax.PVM.Lemmas.F.empty_o in Hmissing.
Qed.

Example empty_valuation_satisfies_unconstrained_circuit :
  match SolverSyntax.circuit_tmap (solver_circuit 0%nvar unused_implicit_example) with
  | Some solver_map =>
      match extract_constraints_c (solver_circuit 0%nvar unused_implicit_example) solver_map with
      | Some ([:: cmap], [::]) =>
          List.forallb (satisfies_constraint1 (SolverSyntax.PVM.empty _))
            (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true
      | _ => False
      end
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example reference_constraints_accept_larger_widths_and_reject_smaller :
  let larger := SolverSyntax.PVM.add (3%nvar, N0) 9
    (SolverSyntax.PVM.add (2%nvar, N0) 7 (SolverSyntax.PVM.empty _)) in
  let too_small := SolverSyntax.PVM.add (3%nvar, N0) 9
    (SolverSyntax.PVM.add (2%nvar, N0) 5 (SolverSyntax.PVM.empty _)) in
  match SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) with
  | Some solver_map =>
      match extract_constraints_c (solver_circuit 0%nvar reference_example) solver_map with
      | Some ([:: cmap], [::]) =>
          let cs := List.concat (snd (List.split (SolverSyntax.PVM.elements cmap))) in
          List.forallb (satisfies_constraint1 larger) cs = true /\
          List.forallb (satisfies_constraint1 too_small) cs = false
      | _ => False
      end
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Example reference_constructed_valuation_satisfies_and_bounds :
  exists solver_map initial result cmap sem_map,
    SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) =
      Some solver_map /\
    Semantics.circuit_tmap_uninferred (sem_circuit reference_example) = Some initial /\
    Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 = Some result /\
    extract_constraints_c (solver_circuit 0%nvar reference_example) solver_map =
      Some ([:: cmap], [::]) /\
    SemSyntax.VM.find 0%nvar result = Some sem_map /\
    covered (semantic_valuation sem_map) initial 0%nvar /\
    List.forallb (satisfies_constraint1 (semantic_valuation sem_map))
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true /\
    (forall id, original_implicit initial 0%nvar id ->
      exists width bound,
        semantic_width result 0%nvar id = Some width /\
        solver_width (semantic_valuation sem_map) id = Some bound /\
        (width <= bound)%coq_nat).
Proof.
  have [solver_map Hsolver] : exists solver_map,
      SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) =
        Some solver_map by vm_compute; eauto.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit reference_example) =
        Some initial by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 =
        Some result by vm_compute; eauto.
  have [cmap Hextract] : exists cmap,
      extract_constraints_c (solver_circuit 0%nvar reference_example) solver_map =
        Some ([:: cmap], [::]).
  { vm_compute in Hsolver. inversion Hsolver; subst solver_map.
    by vm_compute; eauto. }
  have [sem_map [Hfind [Hcover Hsat]]] :=
    semantic_result_valuation_satisfies_constraints Hsolver Hinitial Hresult Hextract.
  have [other [Hother [_ Hupper]]] :=
    satisfying_valuation_bounds_successful_semantic_result
      Hsolver Hinitial Hresult Hextract Hcover Hsat.
  rewrite Hfind in Hother. inversion Hother; subst other.
  by exists solver_map, initial, result, cmap, sem_map.
Qed.

Example extended_semantic_valuation_preserves_other_positions :
  let sem_map := SemSyntax.VM.add 10%nvar
    (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit 3),
      HiEnv_with_implicit_widths.Wire)
    (SemSyntax.VM.add 12%nvar
      (sem_type (UIntExplicit 4), HiEnv_with_implicit_widths.In_port) (SemSyntax.VM.empty _)) in
  let base := SolverSyntax.PVM.add (10%nvar, N0) 8
    (SolverSyntax.PVM.add (12%nvar, N0) 7
      (SolverSyntax.PVM.add (10%nvar, 1%nvar) 9
        (SolverSyntax.PVM.add (99%nvar, N0) 11 (SolverSyntax.PVM.empty _)))) in
  let extended := extended_semantic_valuation sem_map base in
  (solver_width extended 10%nvar, solver_width extended 12%nvar,
   SolverSyntax.PVM.find (10%nvar, 1%nvar) extended,
   solver_width extended 99%nvar, solver_width extended 100%nvar) =
    (Some 3, Some 7, Some 9, Some 11, None).
Proof. vm_compute. reflexivity. Qed.

Definition unused_zero_solution : Valuation :=
  SolverSyntax.PVM.add (10%nvar, N0) 0
    (SolverSyntax.PVM.add (11%nvar, N0) 0
      (SolverSyntax.PVM.add (12%nvar, N0) 0 (SolverSyntax.PVM.empty _))).

Lemma unused_zero_solution_values key w :
  SolverSyntax.PVM.find key unused_zero_solution = Some w -> w = 0.
Proof.
  move=> Hfind.
  apply find_in_elements in Hfind.
  vm_compute in Hfind.
  destruct Hfind as [H|[H|[H|[]]]]; by inversion H.
Qed.

Example unused_zero_solution_minimal_contract :
  exists solver_map initial result cmap,
    SolverSyntax.circuit_tmap (solver_circuit 0%nvar unused_implicit_example) =
      Some solver_map /\
    Semantics.circuit_tmap_uninferred (sem_circuit unused_implicit_example) = Some initial /\
    Semantics.circuit_tmap_implicits (sem_circuit unused_implicit_example) 0 = Some result /\
    extract_constraints_c (solver_circuit 0%nvar unused_implicit_example) solver_map =
      Some ([:: cmap], [::]) /\
    covered unused_zero_solution initial 0%nvar /\
    solver_solution_contract initial 0%nvar cmap unused_zero_solution /\
    forall id, original_implicit initial 0%nvar id ->
      exists w, solver_width unused_zero_solution id = Some w /\
        semantic_width result 0%nvar id = Some w.
Proof.
  have [solver_map Hsolver] : exists solver_map,
      SolverSyntax.circuit_tmap (solver_circuit 0%nvar unused_implicit_example) =
        Some solver_map by vm_compute; eauto.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit unused_implicit_example) =
        Some initial by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit unused_implicit_example) 0 =
        Some result by vm_compute; eauto.
  have [cmap Hextract] : exists cmap,
      extract_constraints_c (solver_circuit 0%nvar unused_implicit_example) solver_map =
        Some ([:: cmap], [::]).
  { vm_compute in Hsolver. inversion Hsolver; subst solver_map.
    by vm_compute; eauto. }
  have [sem_map [Hsem [_ Hsemcovered]]] :=
    semantic_result_valuation_covers_original Hsolver Hinitial Hresult.
  have Hextendedcovered : covered
      (extended_semantic_valuation sem_map
        (SolverSyntax.PVM.add (12%nvar, N0) 0 (SolverSyntax.PVM.empty _)))
      initial 0%nvar.
  { exact: extended_semantic_valuation_covered Hsemcovered. }
  have Hsolution : extended_semantic_valuation sem_map
      (SolverSyntax.PVM.add (12%nvar, N0) 0 (SolverSyntax.PVM.empty _)) =
        unused_zero_solution.
  { vm_compute in Hresult. inversion Hresult; subst result.
    vm_compute in Hsem. inversion Hsem; subst sem_map.
    by vm_compute. }
  have Hcover : covered unused_zero_solution initial 0%nvar.
  { by rewrite -Hsolution. }
  have Hcontract : solver_solution_contract initial 0%nvar cmap unused_zero_solution.
  { split.
    - vm_compute in Hsolver. inversion Hsolver; subst solver_map.
      vm_compute in Hextract. inversion Hextract; subst cmap.
      by vm_compute.
    - move=> candidate _ Hdomain _ key w Hfind.
      have [bound Hbound] := Hdomain key w Hfind.
      exists bound; split; first exact Hbound.
      by rewrite (unused_zero_solution_values key w Hfind).
  }
  have Hequal := conditional_single_module_min_solution_matches_fixed_point
    Hsolver Hinitial Hresult Hextract Hcover Hcontract.
  by exists solver_map, initial, result, cmap.
Qed.

Example unconstrained_sccs_assign_every_position :
  exists solution,
    inferWidths.solve_alg
      [:: [:: (10%nvar, N0)]; [:: (11%nvar, N0)]; [:: (12%nvar, N0)]]
      initial_valuation (SolverSyntax.PVM.empty _) = Some solution /\
    SolverSyntax.PVM.find (10%nvar, N0) solution = Some 0 /\
    SolverSyntax.PVM.find (11%nvar, N0) solution = Some 0 /\
    SolverSyntax.PVM.find (12%nvar, N0) solution = Some 0 /\
    SolverSyntax.PVM.find (99%nvar, N0) solution = None.
Proof.
  eexists; split; first by vm_compute.
  by vm_compute.
Qed.

Example successful_unused_solver_has_exact_domain solution :
  forall solver_map,
    SolverSyntax.circuit_tmap (solver_circuit 0%nvar unused_implicit_example) =
      Some solver_map ->
    inferWidths.solve_fun (solver_circuit 0%nvar unused_implicit_example) solver_map =
      Some solution ->
    SolverSyntax.PVM.mem (10%nvar, N0) solution /\
    SolverSyntax.PVM.mem (11%nvar, N0) solution /\
    SolverSyntax.PVM.mem (12%nvar, N0) solution /\
    ~ SolverSyntax.PVM.mem (99%nvar, N0) solution.
Proof.
  move=> solver_map Hsolver Hsolve.
  have [cmap Hextract] : exists cmap,
      extract_constraints_c (solver_circuit 0%nvar unused_implicit_example) solver_map =
        Some ([:: cmap], [::]).
  { vm_compute in Hsolver. inversion Hsolver; subst solver_map.
    by vm_compute; eauto. }
  have Hdomain := successful_single_module_solver_domain Hextract Hsolve.
  rewrite !Hdomain. by vm_compute.
Qed.

Example reference_scc_extraction_bridge solver_map initial cmap solution :
  SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit reference_example) = Some initial ->
  extract_constraints_c (solver_circuit 0%nvar reference_example) solver_map =
    Some ([:: cmap], [::]) ->
  inferWidths.solve_fun (solver_circuit 0%nvar reference_example) solver_map = Some solution ->
  exists g : graph.Graph (solver_circuit 0%nvar reference_example), forall value,
    List.forallb (satisfies_constraint1 value)
      (extract_cs (List.concat (solver_sccs g)) cmap) =
    List.forallb (satisfies_constraint1 value)
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))).
Proof.
  move=> Hsolver Hinitial Hextract Hsolve.
  have [g [_ [_ Hbridge]]] :=
    successful_common_solver_extraction_bridge Hsolver Hinitial Hextract Hsolve.
  by exists g.
Qed.

Example reference_conditional_theorem_with_minimal_valuation :
  exists solver_map initial result cmap sem_map,
    SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) =
      Some solver_map /\
    Semantics.circuit_tmap_uninferred (sem_circuit reference_example) = Some initial /\
    Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 = Some result /\
    extract_constraints_c (solver_circuit 0%nvar reference_example) solver_map =
      Some ([:: cmap], [::]) /\
    SemSyntax.VM.find 0%nvar result = Some sem_map /\
    solver_solution_contract initial 0%nvar cmap (semantic_valuation sem_map) /\
    solver_width (semantic_valuation sem_map) 2%nvar = Some 6 /\
    solver_width (semantic_valuation sem_map) 3%nvar = Some 6 /\
    (forall id, original_implicit initial 0%nvar id ->
      exists w, solver_width (semantic_valuation sem_map) id = Some w /\
        semantic_width result 0%nvar id = Some w).
Proof.
  have [solver_map Hsolver] : exists solver_map,
      SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) =
        Some solver_map by vm_compute; eauto.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit reference_example) =
        Some initial by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 =
        Some result by vm_compute; eauto.
  have [cmap Hextract] : exists cmap,
      extract_constraints_c (solver_circuit 0%nvar reference_example) solver_map =
        Some ([:: cmap], [::]).
  { vm_compute in Hsolver. inversion Hsolver; subst solver_map.
    by vm_compute; eauto. }
  have [sem_map [Hfind [Hcover Hsat]]] :=
    semantic_result_valuation_satisfies_constraints Hsolver Hinitial Hresult Hextract.
  have Hcontract : solver_solution_contract initial 0%nvar cmap (semantic_valuation sem_map).
  { split; first exact Hsat.
    move=> candidate Hcandidate _ Hcandidate_sat.
    have [other [Hother Hle]] :=
      semantic_result_valuation_le_satisfying_valuation
        Hsolver Hinitial Hresult Hextract Hcandidate Hcandidate_sat.
    rewrite Hfind in Hother. by inversion Hother; subst other.
  }
  have Hequal := conditional_single_module_min_solution_matches_fixed_point
    Hsolver Hinitial Hresult Hextract Hcover Hcontract.
  have Hwidths : solver_width (semantic_valuation sem_map) 2%nvar = Some 6 /\
                 solver_width (semantic_valuation sem_map) 3%nvar = Some 6.
  { vm_compute in Hresult. inversion Hresult; subst result.
    vm_compute in Hfind. inversion Hfind; subst sem_map.
    by vm_compute. }
  destruct Hwidths as [Hwidth2 Hwidth3].
  by exists solver_map, initial, result, cmap, sem_map.
Qed.

Example zero_iteration_example_has_stable_trace :
  exists solver_map initial result sem_map next,
    SolverSyntax.circuit_tmap (solver_circuit 0%nvar zero_iteration_example) =
      Some solver_map /\
    Semantics.circuit_tmap_uninferred (sem_circuit zero_iteration_example) = Some initial /\
    Semantics.circuit_tmap_implicits (sem_circuit zero_iteration_example) 0 = Some result /\
    SemSyntax.VM.find 0%nvar result = Some sem_map /\
    common_stable_width_trace sem_map sem_map (common_stmts zero_iteration_example) next.
Proof.
  have [solver_map Hsolver] : exists solver_map,
      SolverSyntax.circuit_tmap (solver_circuit 0%nvar zero_iteration_example) =
        Some solver_map by vm_compute; eauto.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit zero_iteration_example) =
        Some initial by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit zero_iteration_example) 0 =
        Some result by vm_compute; eauto.
  have [sem_map [next [Hfind [_ [_ [_ Htrace]]]]]] :=
    successful_circuit_result_stable_width_trace Hsolver Hinitial Hresult.
  by exists solver_map, initial, result, sem_map, next.
Qed.

Example zero_iteration_fixed_point_has_ready_operands :
  match SolverSyntax.circuit_tmap (solver_circuit 0%nvar zero_iteration_example),
        Semantics.circuit_tmap_implicits (sem_circuit zero_iteration_example) 0 with
  | Some solver_map, Some result =>
      match SemSyntax.VM.find 0%nvar result with
      | Some sem_map =>
          List.Forall (common_step_semantic_ready sem_map solver_map)
            (rev (common_stmts zero_iteration_example))
      | None => False
      end
  | _, _ => False
  end.
Proof. vm_compute. eauto 12. Qed.

Example missing_reset_reference_rejects_semantic_iteration :
  let m := {| common_module_name := 0%nvar;
              common_ports := [:: CClock 0%nvar; CInput 1%nvar (UIntExplicit 1)];
              common_stmts := [:: CReg 2%nvar UIntImplicit 0%nvar
                (CReset 1%nvar (CRef 99%nvar))] |} in
  Semantics.circuit_tmap_implicits (sem_circuit m) 0 = None.
Proof. vm_compute. reflexivity. Qed.

Example missing_reset_reference_initial_map_can_succeed :
  let m := {| common_module_name := 0%nvar;
              common_ports := [:: CClock 0%nvar; CInput 1%nvar (UIntExplicit 1)];
              common_stmts := [:: CReg 2%nvar UIntImplicit 0%nvar
                (CReset 1%nvar (CRef 99%nvar))] |} in
  match Semantics.circuit_tmap_uninferred (sem_circuit m) with
  | Some _ => true
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example invalid_reset_literal_rejects_semantic_iteration :
  let m := {| common_module_name := 0%nvar;
              common_ports := [:: CClock 0%nvar; CInput 1%nvar (UIntExplicit 1)];
              common_stmts := [:: CReg 2%nvar UIntImplicit 0%nvar
                (CReset 1%nvar (CUInt 0 [:: true]))] |} in
  Semantics.circuit_tmap_implicits (sem_circuit m) 0 = None.
Proof. vm_compute. reflexivity. Qed.

Definition reference_example_constraints :=
  match SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) with
  | Some tmap => extract_constraint_m (solver_module reference_example) tmap
  | None => None
  end.

Example reference_example_extracted_dependency :
  match reference_example_constraints with
  | Some (c1map, _, _) =>
      option_map (map rhs_terms1) (SolverSyntax.PVM.find (3%nvar, N0) c1map)
  | None => None
  end = Some [:: [:: (1, (2%nvar, N0))]].
Proof. vm_compute. reflexivity. Qed.

Example reference_example_circuit_extraction_bridge :
  match SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) with
  | Some tmap =>
      extract_constraints_c (solver_circuit 0%nvar reference_example) tmap =
        option_map (fun next => ([:: next], [::]))
          (common_extract_steps tmap (SolverSyntax.PVM.empty _)
            (rev (common_stmts reference_example)))
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example reference_example_scc_order_solution :
  match reference_example_constraints with
  | Some (c1map, cs2, _) =>
      match inferWidths.solve_alg_check
        [:: [:: (2%nvar, N0)]; [:: (3%nvar, N0)]] c1map cs2 with
      | Some solution => (solver_width solution 2%nvar, solver_width solution 3%nvar)
      | None => (None, None)
      end
  | None => (None, None)
  end = (Some 6, Some 6).
Proof. vm_compute. reflexivity. Qed.

Example reset_example_scc_solution :
  match reset_example_constraints with
  | Some cs =>
      match inferWidths.solve_scc [:: (2%nvar, N0)] cs with
      | Some solution => solver_width solution 2%nvar
      | None => None
      end
  | None => None
  end = Some 8.
Proof. vm_compute. reflexivity. Qed.

Definition risk_const (id : Lib.Var.var) (w : nat) : Constraint1 :=
  common_constraint id (make_rhs [::] [::] (Z.of_nat w)).

Definition risk_ref (dest source : Lib.Var.var) : Constraint1 :=
  common_constraint dest (make_rhs [:: (1, (source, N0))] [::] 0%Z).

Definition risk_cycle_constraints : list Constraint1 :=
  [:: risk_const 1%nvar 6; risk_ref 1%nvar 2%nvar; risk_ref 2%nvar 1%nvar].

Example risk_initial_distance_preserves_same_lhs_constraints :
  let nodes := [:: (1%nvar, N0); (2%nvar, N0)] in
  let constant_first := floyd_sc.init_dist_map' nodes
    [:: risk_const 1%nvar 6; risk_ref 1%nvar 2%nvar] in
  let reference_first := floyd_sc.init_dist_map' nodes
    [:: risk_ref 1%nvar 2%nvar; risk_const 1%nvar 6] in
  floyd_sc.get_weight (1%nvar, N0) (floyd_sc.Node (2%nvar, N0)) constant_first = Some 0%Z /\
  floyd_sc.get_weight (1%nvar, N0) floyd_sc.Zero constant_first = Some 6%Z /\
  floyd_sc.get_weight (1%nvar, N0) (floyd_sc.Node (2%nvar, N0)) reference_first = Some 0%Z /\
  floyd_sc.get_weight (1%nvar, N0) floyd_sc.Zero reference_first = Some 6%Z.
Proof. vm_compute; auto. Qed.

Example risk_initial_distance_maxima_and_unsupported_constraints :
  let x := (1%nvar, N0) in
  let y := (2%nvar, N0) in
  let nodes := [:: x; y] in
  let cs :=
    [:: common_constraint 1%nvar (make_rhs [::] [::] (-4)%Z);
        common_constraint 1%nvar (make_rhs [::] [::] 9%Z);
        common_constraint 1%nvar (make_rhs [::] [::] 3%Z);
        common_constraint 1%nvar (make_rhs [:: (1, x)] [::] (-2)%Z);
        common_constraint 2%nvar (make_rhs [:: (1, y)] [::] 4%Z);
        common_constraint 1%nvar (make_rhs [:: (2, y)] [::] 99%Z);
        common_constraint 3%nvar (make_rhs [::] [::] 99%Z)] in
  let m := floyd_sc.init_dist_map' nodes cs in
  let reversed := floyd_sc.init_dist_map' nodes (List.rev cs) in
  floyd_sc.get_weight x floyd_sc.Zero m = Some 9%Z /\
  floyd_sc.get_weight x (floyd_sc.Node x) m = Some 0%Z /\
  floyd_sc.get_weight y (floyd_sc.Node y) m = Some 4%Z /\
  floyd_sc.get_weight x (floyd_sc.Node y) m = None /\
  floyd_sc.get_weight (3%nvar, N0) floyd_sc.Zero m = None /\
  floyd_sc.get_weight x floyd_sc.Zero reversed = Some 9%Z /\
  floyd_sc.get_weight x (floyd_sc.Node x) reversed = Some 0%Z /\
  floyd_sc.get_weight y (floyd_sc.Node y) reversed = Some 4%Z.
Proof. vm_compute; repeat split; reflexivity. Qed.

Example risk_initial_distance_maxima_on_reference_edges :
  let x := (1%nvar, N0) in
  let y := (2%nvar, N0) in
  let cs :=
    [:: common_constraint 1%nvar (make_rhs [:: (1, y)] [::] (-5)%Z);
        common_constraint 1%nvar (make_rhs [:: (1, y)] [::] 4%Z);
        common_constraint 1%nvar (make_rhs [:: (1, y)] [::] 2%Z);
        common_constraint 2%nvar (make_rhs [:: (1, x)] [::] (-7)%Z)] in
  let m := floyd_sc.init_dist_map' [:: x; y] cs in
  let reversed := floyd_sc.init_dist_map' [:: x; y] (List.rev cs) in
  floyd_sc.get_weight x (floyd_sc.Node y) m = Some 4%Z /\
  floyd_sc.get_weight y (floyd_sc.Node x) m = Some (-7)%Z /\
  floyd_sc.get_weight x (floyd_sc.Node y) reversed = Some 4%Z /\
  floyd_sc.get_weight y (floyd_sc.Node x) reversed = Some (-7)%Z.
Proof. vm_compute; repeat split; reflexivity. Qed.

Example risk_initial_distance_empty_inputs :
  floyd_sc.get_weight (1%nvar, N0) floyd_sc.Zero
    (floyd_sc.init_dist_map' [::] [:: risk_const 1%nvar 6]) = None /\
  floyd_sc.get_weight (1%nvar, N0) (floyd_sc.Node (1%nvar, N0))
    (floyd_sc.init_dist_map' [:: (1%nvar, N0)] [::]) = Some 0%Z /\
  floyd_sc.get_weight (1%nvar, N0) floyd_sc.Zero
    (floyd_sc.init_dist_map' [:: (1%nvar, N0)] [::]) = None.
Proof. vm_compute; auto. Qed.

Example risk_anchored_cycle_independent_of_node_order :
  let forward := inferWidths.solve_scc [:: (1%nvar, N0); (2%nvar, N0)]
    risk_cycle_constraints in
  let backward := inferWidths.solve_scc [:: (2%nvar, N0); (1%nvar, N0)]
    risk_cycle_constraints in
  option_map (fun v => (solver_width v 1%nvar, solver_width v 2%nvar,
    constraints.satisfies_all_constraint1 v risk_cycle_constraints)) forward =
    Some (Some 6, Some 6, true) /\
  option_map (fun v => (solver_width v 1%nvar, solver_width v 2%nvar,
    constraints.satisfies_all_constraint1 v risk_cycle_constraints)) backward =
    Some (Some 6, Some 6, true).
Proof. vm_compute; split; reflexivity. Qed.

Example risk_unanchored_cycle_and_self_reference :
  option_map (fun v => (solver_width v 1%nvar, solver_width v 2%nvar))
    (inferWidths.solve_scc [:: (1%nvar, N0); (2%nvar, N0)]
      [:: risk_ref 1%nvar 2%nvar; risk_ref 2%nvar 1%nvar]) =
      Some (Some 0, Some 0) /\
  option_map (fun v => solver_width v 1%nvar)
    (inferWidths.solve_scc [:: (1%nvar, N0)]
      [:: risk_const 1%nvar 3; risk_ref 1%nvar 1%nvar]) = Some (Some 3).
Proof. vm_compute; auto. Qed.

Fixpoint risk_subsets (cs : list Constraint1) : list (list Constraint1) :=
  match cs with
  | [::] => [:: [::]]
  | c :: rest =>
      let tails := risk_subsets rest in tails ++ map (cons c) tails
  end.

Definition risk_candidate (x y : nat) : Valuation :=
  SolverSyntax.PVM.add (1%nvar, N0) x
    (SolverSyntax.PVM.add (2%nvar, N0) y (SolverSyntax.PVM.empty _)).

Definition risk_small_candidates : list Valuation :=
  List.flat_map (fun x => map (risk_candidate x) [:: 0; 1; 2; 3]) [:: 0; 1; 2; 3].

Definition risk_cycle_check (nodes : list ProdVar.t) (cs : list Constraint1) : bool :=
  match inferWidths.solve_scc nodes cs with
  | None => false
  | Some result =>
      constraints.satisfies_all_constraint1 result cs &&
      all (fun candidate =>
        ~~ constraints.satisfies_all_constraint1 candidate cs ||
        inferWidths.le_bool result candidate) risk_small_candidates
  end.

Example risk_bounded_two_variable_simple_cycles_no_failures :
  count (fun cs =>
    ~~ (risk_cycle_check [:: (1%nvar, N0); (2%nvar, N0)] cs &&
        risk_cycle_check [:: (2%nvar, N0); (1%nvar, N0)] cs &&
        risk_cycle_check [:: (1%nvar, N0); (2%nvar, N0)] (List.rev cs) &&
        risk_cycle_check [:: (2%nvar, N0); (1%nvar, N0)] (List.rev cs)))
    (map (fun cs => [:: risk_ref 1%nvar 2%nvar; risk_ref 2%nvar 1%nvar] ++ cs)
      (risk_subsets [:: risk_const 1%nvar 2; risk_const 2%nvar 3;
        risk_ref 1%nvar 1%nvar; risk_ref 2%nvar 2%nvar])) = 0.
Proof. vm_compute. reflexivity. Qed.

Definition floyd_weighted_ref (dest source : Lib.Var.var) (weight : Z) :=
  common_constraint dest (make_rhs [:: (1, (source, N0))] [::] weight).

Definition floyd_three_nodes :=
  [:: (1%nvar, N0); (2%nvar, N0); (3%nvar, N0)].

Definition floyd_three_permutations :=
  [:: [:: (1%nvar, N0); (2%nvar, N0); (3%nvar, N0)];
      [:: (1%nvar, N0); (3%nvar, N0); (2%nvar, N0)];
      [:: (2%nvar, N0); (1%nvar, N0); (3%nvar, N0)];
      [:: (2%nvar, N0); (3%nvar, N0); (1%nvar, N0)];
      [:: (3%nvar, N0); (1%nvar, N0); (2%nvar, N0)];
      [:: (3%nvar, N0); (2%nvar, N0); (1%nvar, N0)]].

Definition floyd_three_constraints :=
  [:: risk_const 1%nvar 4;
      floyd_weighted_ref 2%nvar 1%nvar 2%Z;
      floyd_weighted_ref 3%nvar 2%nvar (-1)%Z;
      floyd_weighted_ref 1%nvar 3%nvar (-1)%Z].

Example floyd_three_node_solver_contract solution :
  floyd_sc.solve_simple_cycle floyd_three_nodes floyd_three_constraints = Some solution ->
  constraints.satisfies_all_constraint1 solution floyd_three_constraints /\
  (forall x, SolverSyntax.PVM.mem x solution <-> List.In x floyd_three_nodes) /\
  (forall candidate,
    constraints.satisfies_all_constraint1 candidate floyd_three_constraints ->
    (forall x, List.In x floyd_three_nodes -> SolverSyntax.PVM.mem x candidate) ->
    constraints.le solution candidate).
Proof.
  intro Hsolve.
  apply: (@inferWidths_exp.simple_cycle_solver_correct
    floyd_three_nodes floyd_three_constraints solution).
  - by vm_compute.
  - vm_compute; intuition subst; simpl in *; intuition.
  - exact Hsolve.
Qed.

Definition floyd_positive_constraints :=
  [:: floyd_weighted_ref 1%nvar 2%nvar 2%Z;
      floyd_weighted_ref 2%nvar 3%nvar (-1)%Z;
      floyd_weighted_ref 3%nvar 1%nvar 0%Z].

Example floyd_positive_cycle_is_unsatisfiable :
  forall candidate, constraints.satisfies_all_constraint1 candidate
    floyd_positive_constraints = false.
Proof.
  apply: (proj1 (@inferWidths.simple_cycle_solver_none_iff_unsatisfiable
    floyd_three_nodes floyd_positive_constraints _ _ _)).
  - by vm_compute.
  - vm_compute; intuition subst; reflexivity.
  - vm_compute; intuition subst; simpl in *; intuition.
  - by vm_compute.
Qed.

Example floyd_unconstrained_nodes_require_candidate_coverage :
  match floyd_sc.solve_simple_cycle floyd_three_nodes [::] with
  | Some solution =>
      SolverSyntax.PVM.mem (1%nvar, N0) solution &&
      SolverSyntax.PVM.mem (2%nvar, N0) solution &&
      SolverSyntax.PVM.mem (3%nvar, N0) solution &&
      ~~ inferWidths.le_bool solution (SolverSyntax.PVM.empty _)
  | None => false
  end = true.
Proof. by vm_compute. Qed.

Example singleton_unconstrained_scc_minimal candidate :
  SolverSyntax.PVM.mem (1%nvar, N0) candidate ->
  match inferWidths.solve_scc [:: (1%nvar, N0)] [::] with
  | Some solution => constraints.le solution candidate
  | None => False
  end.
Proof.
  move=> Hcoverage.
  have Hsolve : inferWidths.solve_scc [:: (1%nvar, N0)] [::] =
      Some (SolverSyntax.PVM.add (1%nvar, N0) 0 initial_valuation) by vm_compute.
  rewrite Hsolve.
  apply: (@inferWidths.solve_simple_scc_smallest [:: (1%nvar, N0)] [::]
    (SolverSyntax.PVM.add (1%nvar, N0) 0 initial_valuation) candidate).
  - discriminate.
  - constructor; first by move=> [].
    constructor.
  - by vm_compute.
  - by move=> c [].
  - by move=> c [].
  - by move=> c [].
  - exact Hsolve.
  - by vm_compute.
  - move=> x [<-|[]]. exact Hcoverage.
Qed.

Example empty_constraint_map_entries_correct :
  inferWidths.extract_entries_correctness (SolverSyntax.PVM.empty _).
Proof.
  move=> key cs Hfind. by rewrite SolverSyntax.PVM.Lemmas.F.empty_o in Hfind.
Qed.

Example old_extract_correctness_excludes_unconstrained_node :
  ~ inferWidths.extract_correctness (SolverSyntax.PVM.empty _)
    [:: [:: (1%nvar, N0)]].
Proof.
  move=> Hcorrect.
  have Hin : List.In (1%nvar, N0)
      (List.concat [:: [:: (1%nvar, N0)]]) by left.
  have [cs [Hfind _]] := Hcorrect _ Hin.
  by rewrite SolverSyntax.PVM.Lemmas.F.empty_o in Hfind.
Qed.

Example recursive_minimum_handles_unconstrained_node solution candidate :
  inferWidths.scc_schedule_correctness initial_valuation
    [:: [:: (1%nvar, N0)]] (SolverSyntax.PVM.empty _) ->
  inferWidths.solve_alg [:: [:: (1%nvar, N0)]] initial_valuation
    (SolverSyntax.PVM.empty _) = Some solution ->
  SolverSyntax.PVM.mem (1%nvar, N0) candidate ->
  constraints.le solution candidate.
Proof.
  move=> Hschedule Hsolve Hcoverage.
  apply: (@inferWidths.solve_alg_simple_smallest [:: [:: (1%nvar, N0)]]
    (SolverSyntax.PVM.empty _) solution candidate Hschedule
    empty_constraint_map_entries_correct _ Hsolve).
  - elim=> [|key keys IH] //=.
  - by vm_compute.
  - move=> x [<-|[]]. exact Hcoverage.
Qed.

Example substitution_preserves_simple_cycle_shape :
  inferWidths.is_simple_cycle
    (List.map (remove_solved_c (SolverSyntax.PVM.add (1%nvar, N0) 7 initial_valuation))
      risk_cycle_constraints) = true.
Proof.
  apply: inferWidths.remove_solved_simple.
  - vm_compute; intuition subst; reflexivity.
  - by vm_compute.
Qed.

Example floyd_three_node_all_orders :
  all (fun nodes =>
    match inferWidths.solve_scc nodes floyd_three_constraints with
    | Some v =>
        (solver_width v 1%nvar == Some 4) &&
        (solver_width v 2%nvar == Some 6) &&
        (solver_width v 3%nvar == Some 5) &&
        constraints.satisfies_all_constraint1 v floyd_three_constraints
    | None => false
    end) floyd_three_permutations = true.
Proof. by vm_compute. Qed.

Example floyd_positive_cycle_detected_in_all_orders :
  let cs := [:: floyd_weighted_ref 1%nvar 2%nvar 2%Z;
                floyd_weighted_ref 2%nvar 3%nvar (-1)%Z;
                floyd_weighted_ref 3%nvar 1%nvar 0%Z] in
  all (fun nodes =>
    match inferWidths.solve_scc nodes cs with None => true | Some _ => false end)
    floyd_three_permutations = true.
Proof. by vm_compute. Qed.

Example floyd_negative_cycle_minimum :
  let cs := [:: risk_const 1%nvar 4;
                floyd_weighted_ref 2%nvar 1%nvar 2%Z;
                floyd_weighted_ref 3%nvar 2%nvar (-3)%Z;
                floyd_weighted_ref 1%nvar 3%nvar 0%Z] in
  all (fun nodes =>
    match inferWidths.solve_scc nodes cs with
    | Some v =>
        (solver_width v 1%nvar == Some 4) &&
        (solver_width v 2%nvar == Some 6) &&
        (solver_width v 3%nvar == Some 3) &&
        constraints.satisfies_all_constraint1 v cs
    | None => false
    end) floyd_three_permutations = true.
Proof. by vm_compute. Qed.

Example floyd_external_destination_requires_scope_premise :
  let x := (1%nvar, N0) in
  let y := (2%nvar, N0) in
  let z := (3%nvar, N0) in
  let cs := [:: risk_ref 1%nvar 3%nvar; risk_ref 2%nvar 1%nvar] in
  let m := floyd_sc.floyd_loop_map' [:: x; y] cs in
  floyd_sc.get_weight y (floyd_sc.Node x) m = Some 0%Z /\
  floyd_sc.get_weight x (floyd_sc.Node z) m = Some 0%Z /\
  floyd_sc.get_weight y (floyd_sc.Node z) m = None.
Proof. vm_compute; repeat split; reflexivity. Qed.

Definition risk_cycle_module : common_module :=
  {| common_module_name := 0%nvar;
     common_ports := [:: CInput 1%nvar UIntImplicit; COutput 2%nvar UIntImplicit];
     common_stmts := [:: CConnect 1%nvar (CUInt 6 [::]);
                         CConnect 1%nvar (CRef 2%nvar);
                         CConnect 2%nvar (CRef 1%nvar)] |}.

Example risk_cycle_extracted_scc_order_satisfies_constraints :
  let c := solver_circuit 0%nvar risk_cycle_module in
  match SolverSyntax.circuit_tmap c with
  | Some tmap =>
      match extract_constraints_c c tmap with
      | Some ([:: cmap], [::]) =>
          match inferWidths.solve_alg [:: [:: (2%nvar, N0); (1%nvar, N0)]]
            initial_valuation cmap with
          | Some value =>
              (solver_width value 1%nvar, solver_width value 2%nvar,
                List.forallb (satisfies_constraint1 value)
                  (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))))
          | None => (None, None, false)
          end
      | _ => (None, None, false)
      end
  | None => (None, None, false)
  end = (Some 6, Some 6, true).
Proof. by vm_compute. Qed.

Example risk_cycle_semantics_propagates_both_widths :
  match Semantics.circuit_tmap_implicits (sem_circuit risk_cycle_module) 2 with
  | Some result =>
      (semantic_width result 0%nvar 1%nvar, semantic_width result 0%nvar 2%nvar)
  | None => (None, None)
  end = (Some 6, Some 6).
Proof. by vm_compute. Qed.

Example reference_dependency_is_not_scheduled_after_target
    (g : graph.Graph (solver_circuit 0%nvar reference_example)) prefix block suffix :
  build_dependency_graph (solver_circuit 0%nvar reference_example)
    [:: risk_ref 3%nvar 2%nvar] = Some g ->
  solver_sccs g = prefix ++ block :: suffix ->
  List.In (3%nvar, N0) block ->
  List.In (2%nvar, N0) (List.concat prefix ++ block).
Proof.
  move=> Hgraph Horder Htarget.
  have Hsource_valid : (2%nvar, N0) \in
      SolverSyntax.finProdVar_list (solver_circuit 0%nvar reference_example)
    by vm_compute.
  have Htarget_valid : (3%nvar, N0) \in
      SolverSyntax.finProdVar_list (solver_circuit 0%nvar reference_example)
    by vm_compute.
  pose source : SolverSyntax.finProdVar (solver_circuit 0%nvar reference_example) :=
    @Sub _ (fun x => x \in SolverSyntax.finProdVar_list
      (solver_circuit 0%nvar reference_example)) _ _ Hsource_valid.
  pose target : SolverSyntax.finProdVar (solver_circuit 0%nvar reference_example) :=
    @Sub _ (fun x => x \in SolverSyntax.finProdVar_list
      (solver_circuit 0%nvar reference_example)) _ _ Htarget_valid.
  have Hedge : g source target.
  { apply: (dependency_graph_contains_edge Hgraph
      (constraint := risk_ref 3%nvar 2%nvar) (coeff := 1)).
    - by left.
    - reflexivity.
    - by left. }
  exact: (@solver_sccs_edge_order _ g prefix block suffix source target
    Horder Hedge Htarget).
Qed.

Example risk_cycle_actual_solver_correct_if_scc_order solver_map cmap
    (g : graph.Graph (solver_circuit 0%nvar risk_cycle_module)) :
  SolverSyntax.circuit_tmap (solver_circuit 0%nvar risk_cycle_module) = Some solver_map ->
  extract_constraints_c (solver_circuit 0%nvar risk_cycle_module) solver_map =
    Some ([:: cmap], [::]) ->
  build_dependency_graph (solver_circuit 0%nvar risk_cycle_module)
    (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = Some g ->
  solver_sccs g = [:: [:: (2%nvar, N0); (1%nvar, N0)]] ->
  exists solution,
    inferWidths.solve_fun (solver_circuit 0%nvar risk_cycle_module) solver_map =
      Some solution /\
    solver_width solution 1%nvar = Some 6 /\
    solver_width solution 2%nvar = Some 6 /\
    List.forallb (satisfies_constraint1 solution)
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true.
Proof.
  move=> Htmap Hextract Hgraph Horder.
  have Hextract0 := Hextract.
  vm_compute in Htmap. inversion Htmap; subst solver_map.
  vm_compute in Hextract. inversion Hextract; subst cmap.
  rewrite /inferWidths.solve_fun.
  eexists; split.
  - rewrite Hextract0 /=.
    rewrite /inferWidths.solve_helper Hgraph.
    rewrite /solver_sccs in Horder.
    rewrite Horder. by vm_compute.
  - by vm_compute.
Qed.

Definition reset_example_full_solver :=
  match reset_solver_map with
  | Some tmap =>
      match inferWidths.solve_fun (solver_circuit 0%nvar reset_example) tmap with
      | Some solution => solver_width solution 2%nvar
      | None => None
      end
  | None => None
  end.

Definition reference_example_full_solver :=
  match SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) with
  | Some tmap =>
      match inferWidths.solve_fun (solver_circuit 0%nvar reference_example) tmap with
      | Some solution => (solver_width solution 2%nvar, solver_width solution 3%nvar)
      | None => (None, None)
      end
  | None => (None, None)
  end.

Example reference_example_successful_solver_matches_semantics solver_map solution :
  SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) = Some solver_map ->
  inferWidths.solve_fun (solver_circuit 0%nvar reference_example) solver_map =
    Some solution ->
  solver_width solution 2%nvar = Some 6 /\
  solver_width solution 3%nvar = Some 6.
Proof.
  move=> Hsolver Hsolve.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit reference_example) = Some initial
    by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit reference_example) 2 = Some result
    by vm_compute; eauto.
  have Himplicit2 : original_implicit initial 0%nvar 2%nvar.
  { vm_compute in Hinitial. inversion Hinitial; subst initial. by vm_compute. }
  have Himplicit3 : original_implicit initial 0%nvar 3%nvar.
  { vm_compute in Hinitial. inversion Hinitial; subst initial. by vm_compute. }
  have Hwidth2 : semantic_width result 0%nvar 2%nvar = Some 6.
  { vm_compute in Hresult. inversion Hresult; subst result. by vm_compute. }
  have Hwidth3 : semantic_width result 0%nvar 3%nvar = Some 6.
  { vm_compute in Hresult. inversion Hresult; subst result. by vm_compute. }
  have [w2 [Hsolve2 Hsem2]] :=
    solve_fun_matches_fixed_point Hsolver Hsolve Hinitial Hresult Himplicit2.
  have [w3 [Hsolve3 Hsem3]] :=
    solve_fun_matches_fixed_point Hsolver Hsolve Hinitial Hresult Himplicit3.
  rewrite Hwidth2 in Hsem2. inversion Hsem2; subst w2.
  rewrite Hwidth3 in Hsem3. inversion Hsem3; subst w3.
  by split.
Qed.

Example unused_implicit_successful_solver_matches_semantics solver_map solution :
  SolverSyntax.circuit_tmap (solver_circuit 0%nvar unused_implicit_example) =
    Some solver_map ->
  inferWidths.solve_fun (solver_circuit 0%nvar unused_implicit_example) solver_map =
    Some solution ->
  solver_width solution 10%nvar = Some 0 /\
  solver_width solution 11%nvar = Some 0.
Proof.
  move=> Hsolver Hsolve.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit unused_implicit_example) =
        Some initial by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit unused_implicit_example) 0 =
        Some result by vm_compute; eauto.
  have Himplicit10 : original_implicit initial 0%nvar 10%nvar.
  { vm_compute in Hinitial. inversion Hinitial; subst initial. by vm_compute. }
  have Himplicit11 : original_implicit initial 0%nvar 11%nvar.
  { vm_compute in Hinitial. inversion Hinitial; subst initial. by vm_compute. }
  have Hwidth10 : semantic_width result 0%nvar 10%nvar = Some 0.
  { vm_compute in Hresult. inversion Hresult; subst result. by vm_compute. }
  have Hwidth11 : semantic_width result 0%nvar 11%nvar = Some 0.
  { vm_compute in Hresult. inversion Hresult; subst result. by vm_compute. }
  have [w10 [Hsolve10 Hsem10]] :=
    solve_fun_matches_fixed_point Hsolver Hsolve Hinitial Hresult Himplicit10.
  have [w11 [Hsolve11 Hsem11]] :=
    solve_fun_matches_fixed_point Hsolver Hsolve Hinitial Hresult Himplicit11.
  rewrite Hwidth10 in Hsem10. inversion Hsem10; subst w10.
  rewrite Hwidth11 in Hsem11. inversion Hsem11; subst w11.
  by split.
Qed.

Example risk_cycle_successful_solver_matches_semantics solver_map solution :
  SolverSyntax.circuit_tmap (solver_circuit 0%nvar risk_cycle_module) =
    Some solver_map ->
  inferWidths.solve_fun (solver_circuit 0%nvar risk_cycle_module) solver_map =
    Some solution ->
  solver_width solution 1%nvar = Some 6 /\
  solver_width solution 2%nvar = Some 6.
Proof.
  move=> Hsolver Hsolve.
  have [initial Hinitial] : exists initial,
      Semantics.circuit_tmap_uninferred (sem_circuit risk_cycle_module) =
        Some initial by vm_compute; eauto.
  have [result Hresult] : exists result,
      Semantics.circuit_tmap_implicits (sem_circuit risk_cycle_module) 2 =
        Some result by vm_compute; eauto.
  have Himplicit1 : original_implicit initial 0%nvar 1%nvar.
  { vm_compute in Hinitial. inversion Hinitial; subst initial. by vm_compute. }
  have Himplicit2 : original_implicit initial 0%nvar 2%nvar.
  { vm_compute in Hinitial. inversion Hinitial; subst initial. by vm_compute. }
  have Hwidth1 : semantic_width result 0%nvar 1%nvar = Some 6.
  { vm_compute in Hresult. inversion Hresult; subst result. by vm_compute. }
  have Hwidth2 : semantic_width result 0%nvar 2%nvar = Some 6.
  { vm_compute in Hresult. inversion Hresult; subst result. by vm_compute. }
  have [w1 [Hsolve1 Hsem1]] :=
    solve_fun_matches_fixed_point Hsolver Hsolve Hinitial Hresult Himplicit1.
  have [w2 [Hsolve2 Hsem2]] :=
    solve_fun_matches_fixed_point Hsolver Hsolve Hinitial Hresult Himplicit2.
  rewrite Hwidth1 in Hsem1. inversion Hsem1; subst w1.
  rewrite Hwidth2 in Hsem2. inversion Hsem2; subst w2.
  by split.
Qed.

Definition reference_example_full_exponential_solver :=
  match SolverSyntax.circuit_tmap (solver_circuit 0%nvar reference_example) with
  | Some tmap =>
      match inferWidths_exp.solve_fun (solver_circuit 0%nvar reference_example) tmap with
      | Some solution => (solver_width solution 2%nvar, solver_width solution 3%nvar)
      | None => (None, None)
      end
  | None => (None, None)
  end.

Definition bad_constraint :=
  {| lhs_var1 := (2%nvar, N0); rhs_const1 := 0%Z;
     rhs_terms1 := [:: (1, (99%nvar, N0))]; rhs_power := [::] |}.

Example missing_constraint_variable_is_rejected :
  match build_dependency_graph (solver_circuit 0%nvar reset_example) [:: bad_constraint] with
  | Some _ => false
  | None => true
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example invalid_constraint_rejected_by_both_solvers :
  let c1map := SolverSyntax.PVM.add (2%nvar, N0) [:: bad_constraint]
    (SolverSyntax.PVM.empty _) in
  inferWidths.solve_helper (solver_circuit 0%nvar reset_example) c1map [::] = None /\
  inferWidths_exp.solve_helper (solver_circuit 0%nvar reset_example) c1map [::] = None.
Proof. vm_compute. split; reflexivity. Qed.

Example finite_variables_accept_all_declared_types :
  SolverSyntax.finProdVar_list (solver_circuit 0%nvar reset_example) =
    [:: (0%nvar, N0); (1%nvar, N0); (2%nvar, N0)].
Proof. vm_compute. reflexivity. Qed.

Example finite_variables_do_not_bound_component_ids :
  let m := {| common_module_name := 0%nvar;
              common_ports := [:: CInput 99%nvar UIntImplicit];
              common_stmts := [::] |} in
  SolverSyntax.finProdVar_list (solver_circuit 0%nvar m) = [:: (99%nvar, N0)].
Proof. vm_compute. reflexivity. Qed.

Example finite_variable_conversion_checks_membership :
  match SolverSyntax.ProdVar2finProdVar (solver_circuit 0%nvar reset_example) (2%nvar, N0),
        SolverSyntax.ProdVar2finProdVar (solver_circuit 0%nvar reset_example) (99%nvar, N0) with
  | Some v, None => SolverSyntax.finProdVar2ProdVar v = (2%nvar, N0)
  | _, _ => False
  end.
Proof.
  have Htarget : (2%nvar, N0) \in SolverSyntax.finProdVar_list
    (solver_circuit 0%nvar reset_example) by vm_compute.
  have Hmissing : (99%nvar, N0) \notin SolverSyntax.finProdVar_list
    (solver_circuit 0%nvar reset_example) by vm_compute.
  by rewrite /SolverSyntax.ProdVar2finProdVar
    (insubT (fun v => v \in SolverSyntax.finProdVar_list
      (solver_circuit 0%nvar reset_example)) Htarget)
    (insubN (seq_sub (SolverSyntax.finProdVar_list
      (solver_circuit 0%nvar reset_example))) Hmissing).
Qed.

Example finite_aggregate_offsets :
  SolverSyntax.all_vars_of_ftype 99%nvar 0
    (HiEnv.Btyp (HiEnv.Fflips 4%nvar HiEnv.Nflip
      (HiEnv.Atyp (HiEnv.Gtyp (Env.Fuint_implicit 0)) 3)
      (HiEnv.Fflips 5%nvar HiEnv.Nflip (HiEnv.Gtyp (Env.Fsint 2)) HiEnv.Fnil))) =
    [:: (99%nvar, N0); (99%nvar, 3%nvar)].
Proof. vm_compute. reflexivity. Qed.

Definition power_dependency :=
  {| lhs_var1 := (2%nvar, N0); rhs_const1 := 0%Z;
     rhs_terms1 := [::]; rhs_power := [:: (1, (1%nvar, N0))] |}.

Example power_dependency_edge_characterization
    (g : graph.Graph (solver_circuit 0%nvar reset_example)) from dest :
  build_dependency_graph (solver_circuit 0%nvar reset_example)
    [:: power_dependency] = Some g ->
  (g from dest <->
    SolverSyntax.finProdVar2ProdVar from = (1%nvar, N0) /\
    SolverSyntax.finProdVar2ProdVar dest = (2%nvar, N0)).
Proof.
  move=> Hgraph; split.
  - move=> Hedge.
    have [constraint [coeff [Hin [Hlhs Hterm]]]] :=
      dependency_graph_edge_origin Hgraph Hedge.
    destruct Hin as [Heq|[]]; subst constraint.
    simpl in Hlhs, Hterm.
    destruct Hterm as [Heq|[]]. inversion Heq; subst.
    by split.
  - move=> [Hfrom Hdest].
    apply: (dependency_graph_contains_edge Hgraph (constraint := power_dependency)
      (coeff := 1)).
    + by left.
    + by rewrite /= Hdest.
    + by rewrite /= Hfrom; left.
Qed.

Example power_dependency_is_an_edge :
  let c := solver_circuit 0%nvar reset_example in
  match build_dependency_graph c [:: power_dependency],
        SolverSyntax.ProdVar2finProdVar c (1%nvar, N0),
        SolverSyntax.ProdVar2finProdVar c (2%nvar, N0) with
  | Some g, Some from, Some dest => g from dest
  | _, _, _ => false
  end = true.
Proof.
  have Hfrom : (1%nvar, N0) \in SolverSyntax.finProdVar_list
    (solver_circuit 0%nvar reset_example) by vm_compute.
  have Hdest : (2%nvar, N0) \in SolverSyntax.finProdVar_list
    (solver_circuit 0%nvar reset_example) by vm_compute.
  rewrite /SolverSyntax.ProdVar2finProdVar
    (insubT (fun v => v \in SolverSyntax.finProdVar_list
      (solver_circuit 0%nvar reset_example)) Hfrom)
    (insubT (fun v => v \in SolverSyntax.finProdVar_list
      (solver_circuit 0%nvar reset_example)) Hdest).
  vm_compute. reflexivity.
Qed.

Example missing_power_variable_is_rejected :
  let invalid :=
    {| lhs_var1 := (2%nvar, N0); rhs_const1 := 0%Z;
       rhs_terms1 := [::]; rhs_power := [:: (1, (99%nvar, N0))] |} in
  match build_dependency_graph (solver_circuit 0%nvar reset_example) [:: invalid] with
  | Some _ => false
  | None => true
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example missing_constraint_target_is_rejected :
  let invalid :=
    {| lhs_var1 := (99%nvar, N0); rhs_const1 := 3%Z;
       rhs_terms1 := [::]; rhs_power := [::] |} in
  match build_dependency_graph (solver_circuit 0%nvar reset_example) [:: invalid] with
  | Some _ => false
  | None => true
  end = true.
Proof. vm_compute. reflexivity. Qed.
