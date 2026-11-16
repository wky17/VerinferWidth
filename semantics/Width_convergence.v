From mathcomp Require Import all_ssreflect.
From Lib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths.
From Solver Require Import inferWidths.
From Semantics Require Import Width_solution_bridge Width_bridge_proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Any number of declarations and unsigned literals may feed one
   implicit-width destination, including literal resets of that register.
   Checks only inspect source syntax and the uninferred map. *)
Definition uint_literal_stmt (dest : var) (kind : fcomponent)
    (s : common_stmt) : bool :=
  match s with
  | CSkip | CWire _ _ | CReg _ _ _ CNoReset => true
  | CReg id _ _ (CReset _ (CUInt w bits)) =>
      (id == dest) && (kind == Register) && (size bits <= w)
  | CConnect id (CUInt w bits) => (id == dest) && (size bits <= w)
  | _ => false
  end.

Definition literal_width (s : common_stmt) : nat :=
  match s with
  | CConnect _ (CUInt w _) | CReg _ _ _ (CReset _ (CUInt w _)) => w
  | _ => 0
  end.

Fixpoint literal_width_bound (ss : seq common_stmt) : nat :=
  match ss with
  | [::] => 0
  | s :: rest => maxn (literal_width s) (literal_width_bound rest)
  end.

Definition uint_implicit_type (w : nat) : ftype :=
  Gtyp (Fuint_implicit w).

Lemma uint_literal_step dest s before old kind :
  uint_literal_stmt dest kind s ->
  SemSyntax.VM.find dest before = Some (uint_implicit_type old, kind) ->
  exists after,
    Semantics.width_iter_one before (sem_stmt s) = Some after /\
    SemSyntax.VM.find dest after =
      Some (uint_implicit_type (maxn old (literal_width s)), kind) /\
    forall id, id != dest ->
      SemSyntax.VM.find id after = SemSyntax.VM.find id before.
Proof.
  case: s => [|id ty|id ty clock rst|id e] /= Hvalid Hfind.
  - exists before. by rewrite maxn0.
  - exists before. by rewrite maxn0.
  - case: rst Hvalid => [|trigger e] //=.
    + move=> _. exists before. by rewrite maxn0.
    + case: e => [src|w bits|w bits] //=.
      move/andP=> [/andP [/eqP Hid /eqP Hkind] Hbits].
      subst id kind.
      exists (SemSyntax.VM.add dest
        (uint_implicit_type (maxn old w), Register) before).
      split.
      * rewrite /= Hfind /Semantics.type_of_expr /=.
        rewrite (leqNgt (size bits) w) in Hbits.
        rewrite (negbTE Hbits) /uint_implicit_type /=.
        clear Hfind. by case: old => [|[|old]].
      * split.
        -- by rewrite SemSyntax.VM.Lemmas.find_add_eq // eqxx.
        -- move=> x /negP Hneq.
           by rewrite SemSyntax.VM.Lemmas.find_add_neq.
  - case: e Hvalid => [src|w bits|w bits] //=.
    move/andP=> [/eqP -> Hbits].
    exists (SemSyntax.VM.add dest
      (uint_implicit_type (maxn old w), kind) before).
    split.
    + rewrite /= /Semantics.type_of_expr /= Hfind.
      rewrite (leqNgt (size bits) w) in Hbits.
      rewrite (negbTE Hbits).
      rewrite /uint_implicit_type /=. clear Hfind. by case: old => [|[|old]].
    + split.
      * by rewrite SemSyntax.VM.Lemmas.find_add_eq // eqxx.
      * move=> x /negP Hneq.
        by rewrite SemSyntax.VM.Lemmas.find_add_neq.
Qed.

Lemma uint_literal_sweep dest ss before old kind :
  all (uint_literal_stmt dest kind) ss ->
  SemSyntax.VM.find dest before = Some (uint_implicit_type old, kind) ->
  exists after,
    Semantics.width_iter before (sem_stmts ss) = Some after /\
    SemSyntax.VM.find dest after =
      Some (uint_implicit_type (maxn old (literal_width_bound ss)), kind) /\
    forall id, id != dest ->
      SemSyntax.VM.find id after = SemSyntax.VM.find id before.
Proof.
  move: before old.
  elim: ss => [|s ss IH] before old /= Hall Hfind.
  - exists before. by rewrite maxn0.
  - move/andP: Hall => [Hs Hss].
    have [middle [Hstep [Hmiddle Hother]]] := uint_literal_step Hs Hfind.
    have [after [Hrest [Hafter Hothers]]] := IH middle _ Hss Hmiddle.
    exists after. split; first by rewrite Hstep Hrest.
    split.
    + by rewrite -maxnA in Hafter.
    + move=> id Hneq. by rewrite (Hothers id Hneq) (Hother id Hneq).
Qed.

Lemma uint_literal_two_sweeps dest ss before old kind :
  all (uint_literal_stmt dest kind) ss ->
  SemSyntax.VM.find dest before = Some (uint_implicit_type old, kind) ->
  exists first second,
    Semantics.width_iter before (sem_stmts ss) = Some first /\
    Semantics.width_iter first (sem_stmts ss) = Some second /\
    (forall id, SemSyntax.VM.find id first = SemSyntax.VM.find id second) /\
    SemSyntax.VM.find dest first =
      Some (uint_implicit_type (maxn old (literal_width_bound ss)), kind).
Proof.
  move=> Hall Hfind.
  have [first [Hfirst [Hwidth Hother1]]] := uint_literal_sweep Hall Hfind.
  have [second [Hsecond [Hwidth2 Hother2]]] := uint_literal_sweep Hall Hwidth.
  exists first, second. split; first exact Hfirst.
  split; first exact Hsecond.
  split; last exact Hwidth.
  move=> id. case Heq: (id == dest).
  - move/eqP: Heq => ->.
    by rewrite Hwidth Hwidth2 -maxnA maxnn.
  - have Hneq : id != dest by rewrite Heq.
    by rewrite (Hother2 id Hneq).
Qed.

Definition uint_literal_well_formed (m : common_module)
    (initial : sem_circuit_map) (dest : var) : Prop :=
  exists components width kind,
    SemSyntax.VM.find (common_module_name m) initial = Some components /\
    SemSyntax.VM.find dest components = Some (uint_implicit_type width, kind) /\
    all (uint_literal_stmt dest kind) (common_stmts m).

Definition uint_literal_well_formedb (m : common_module)
    (initial : sem_circuit_map) (dest : var) : bool :=
  match SemSyntax.VM.find (common_module_name m) initial with
  | Some components =>
      match SemSyntax.VM.find dest components with
      | Some (Gtyp (Fuint_implicit _), kind) =>
          all (uint_literal_stmt dest kind) (common_stmts m)
      | _ => false
      end
  | None => false
  end.

Definition uint_literal_module_check (m : common_module) (dest : var) : bool :=
  match Semantics.circuit_tmap_uninferred (sem_circuit m) with
  | Some initial => uint_literal_well_formedb m initial dest
  | None => false
  end.

Lemma uint_literal_check_sound m initial dest :
  uint_literal_well_formedb m initial dest ->
  uint_literal_well_formed m initial dest.
Proof.
  rewrite /uint_literal_well_formedb /uint_literal_well_formed.
  case Hmodule: (SemSyntax.VM.find (common_module_name m) initial)
    => [components|] //=.
  case Hfind: (SemSyntax.VM.find dest components)
    => [[ty kind]|] //=.
  case: ty Hfind => [gt|elt n|fields] Hfind //=.
  case: gt Hfind => [w|w|w|w| | | |] Hfind //= Hall.
  exists components, w, kind. by repeat split.
Qed.

Lemma uint_literal_check_spec m initial dest :
  uint_literal_well_formedb m initial dest = true <->
  uint_literal_well_formed m initial dest.
Proof.
  split; first exact: uint_literal_check_sound.
  move=> [components [width [kind [Hmodule [Hfind Hall]]]]].
  by rewrite /uint_literal_well_formedb Hmodule Hfind /uint_implicit_type /= Hall.
Qed.

(* Widths are bounded by the maximum of the original width and the literal
   widths.  The first sweep reaches that bound; the second is observationally
   unchanged, so one circuit iteration always suffices. *)
Theorem uint_literal_module_converges_with_width m initial dest components width kind :
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  SemSyntax.VM.find (common_module_name m) initial = Some components ->
  SemSyntax.VM.find dest components = Some (uint_implicit_type width, kind) ->
  all (uint_literal_stmt dest kind) (common_stmts m) ->
  exists result,
    Semantics.circuit_tmap_implicits (sem_circuit m) 1 = Some result /\
    semantic_width result (common_module_name m) dest =
      Some (maxn width (literal_width_bound (common_stmts m))).
Proof.
  move=> Hinitial Hmodule Hfind Hall.
  have [first [second [Hfirst [Hsecond [Hsame Hwidth]]]]] :=
    uint_literal_two_sweeps Hall Hfind.
  set circuit1 := SemSyntax.VM.add (common_module_name m) first initial.
  set circuit2 := SemSyntax.VM.add (common_module_name m) second circuit1.
  have Hstep1 :
      Semantics.circuit_width_iter (sem_circuit m) initial = Some circuit1.
  { rewrite /Semantics.circuit_width_iter /sem_circuit /sem_module /= Hmodule.
    by rewrite common_unify_width_down Hfirst common_unify_width_up. }
  have Hstep2 :
      Semantics.circuit_width_iter (sem_circuit m) circuit1 = Some circuit2.
  { rewrite /Semantics.circuit_width_iter /sem_circuit /sem_module /=.
    rewrite /circuit1 SemSyntax.VM.Lemmas.find_add_eq //.
    by rewrite common_unify_width_down Hsecond common_unify_width_up. }
  have Hequal : SemSyntax.VM.equal (SemSyntax.VM.equal pair_eq)
      circuit1 circuit2 = true.
  { apply (proj2 (Semantics.circuit_tmap_equal_find_iff circuit1 circuit2)).
    move=> mi.
    case Hmi: (mi == common_module_name m).
    - move/eqP: Hmi => ->.
      by rewrite /circuit2 /circuit1 !SemSyntax.VM.Lemmas.find_add_eq //.
    - have Hneq : ~ (mi == common_module_name m) by move/negP: Hmi.
      rewrite /circuit2 /circuit1 !SemSyntax.VM.Lemmas.find_add_neq //.
      by case: (SemSyntax.VM.find mi initial) => [tmap|] //= id. }
  exists circuit1.
  split.
  - by rewrite /Semantics.circuit_tmap_implicits Hinitial /= Hstep1 Hstep2 Hequal.
  - by rewrite /semantic_width /circuit1
      SemSyntax.VM.Lemmas.find_add_eq // Hwidth.
Qed.

Theorem uint_literal_module_converges m initial dest :
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  uint_literal_well_formed m initial dest ->
  exists result,
    Semantics.circuit_tmap_implicits (sem_circuit m) 1 = Some result.
Proof.
  move=> Hinitial [components [width [kind [Hmodule [Hfind Hall]]]]].
  have [result [Hresult _]] :=
    uint_literal_module_converges_with_width Hinitial Hmodule Hfind Hall.
  by exists result.
Qed.

Corollary uint_literal_checked_module_converges m dest :
  uint_literal_module_check m dest ->
  exists result,
    Semantics.circuit_tmap_implicits (sem_circuit m) 1 = Some result.
Proof.
  rewrite /uint_literal_module_check.
  case Hinitial: (Semantics.circuit_tmap_uninferred (sem_circuit m))
    => [initial|] //= Hcheck.
  exact: (uint_literal_module_converges Hinitial (uint_literal_check_sound Hcheck)).
Qed.

Corollary uint_literal_checked_finite_convergence m dest :
  uint_literal_module_check m dest ->
  exists n result,
    Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result.
Proof.
  move=> Hcheck.
  have [result Hresult] := uint_literal_checked_module_converges Hcheck.
  by exists 1, result.
Qed.

Theorem uint_literal_checked_solver_matches_fixed_point
    m circuit_name solver_map solution dest :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  inferWidths.solve_fun (solver_circuit circuit_name m) solver_map = Some solution ->
  uint_literal_module_check m dest ->
  exists initial result,
    Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial /\
    Semantics.circuit_tmap_implicits (sem_circuit m) 1 = Some result /\
    forall id, original_implicit initial (common_module_name m) id ->
      exists w,
        solver_width solution id = Some w /\
        semantic_width result (common_module_name m) id = Some w.
Proof.
  move=> Hsolver Hsolve Hcheck.
  have [result Hresult] := uint_literal_checked_module_converges Hcheck.
  have [initial [Hinitial Hequal]] :=
    solve_fun_matches_fixed_point_without_initial Hsolver Hsolve Hresult.
  by exists initial, result.
Qed.
