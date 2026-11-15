From Coq Require Import NArith.
From mathcomp Require Import all_ssreflect.
From Lib Require Import Var.
From firrtl Require Import Env HiEnv HiFirrtl
  Env_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths.
From Solver Require Import constraints inferWidths.
From Semantics Require Import Semantics_with_implicit_widths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module SolverSyntax := HiFirrtl.
Module SemSyntax := HiFirrtl_with_implicit_widths.
Module Semantics := Semantics_with_implicit_widths.

(* A common scalar syntax: implicit widths start at zero. *)
Inductive scalar_type :=
| UIntImplicit
| SIntImplicit
| UIntExplicit (width : nat)
| SIntExplicit (width : nat).

Inductive common_expr :=
| CRef (id : var)
| CUInt (width : nat) (bits : bitseq)
| CSInt (width : nat) (bits : bitseq).

Inductive common_reset :=
| CNoReset
| CReset (trigger : var) (value : common_expr).

Inductive common_port :=
| CInput (id : var) (ty : scalar_type)
| COutput (id : var) (ty : scalar_type)
| CClock (id : var).

Inductive common_stmt :=
| CSkip
| CWire (id : var) (ty : scalar_type)
| CReg (id : var) (ty : scalar_type) (clock : var) (rst : common_reset)
| CConnect (id : var) (value : common_expr).

Record common_module := {
  common_module_name : var;
  common_ports : seq common_port;
  common_stmts : seq common_stmt
}.

Definition solver_type (t : scalar_type) : HiEnv.ftype :=
  HiEnv.Gtyp
    (match t with
     | UIntImplicit => Env.Fuint_implicit 0
     | SIntImplicit => Env.Fsint_implicit 0
     | UIntExplicit w => Env.Fuint w
     | SIntExplicit w => Env.Fsint w
     end).

Definition sem_type (t : scalar_type) : HiEnv_with_implicit_widths.ftype :=
  HiEnv_with_implicit_widths.Gtyp
    (match t with
     | UIntImplicit => Env_with_implicit_widths.Fuint_implicit 0
     | SIntImplicit => Env_with_implicit_widths.Fsint_implicit 0
     | UIntExplicit w => Env_with_implicit_widths.Fuint w
     | SIntExplicit w => Env_with_implicit_widths.Fsint w
     end).

Definition solver_expr (e : common_expr) : SolverSyntax.HiF.hfexpr :=
  match e with
  | CRef v => HiFirrtl.Eref (HiFirrtl.Eid v)
  | CUInt w bits => HiFirrtl.Econst VarOrder.T (Env.Fuint w) bits
  | CSInt w bits => HiFirrtl.Econst VarOrder.T (Env.Fsint w) bits
  end.

Definition sem_expr (e : common_expr) : SemSyntax.HiF.hfexpr :=
  match e with
  | CRef v => SemSyntax.Eref (SemSyntax.Eid v)
  | CUInt w bits =>
      SemSyntax.Econst VarOrder.T (Env_with_implicit_widths.Fuint w) bits
  | CSInt w bits =>
      SemSyntax.Econst VarOrder.T (Env_with_implicit_widths.Fsint w) bits
  end.

Definition solver_reset (r : common_reset) : SolverSyntax.HiF.rst :=
  match r with
  | CNoReset => HiFirrtl.NRst VarOrder.T
  | CReset trigger value =>
      HiFirrtl.Rst (solver_expr (CRef trigger)) (solver_expr value)
  end.

Definition sem_reset (r : common_reset) : SemSyntax.HiF.rst :=
  match r with
  | CNoReset => SemSyntax.NRst VarOrder.T
  | CReset trigger value =>
      SemSyntax.Rst (sem_expr (CRef trigger)) (sem_expr value)
  end.

Definition solver_port (p : common_port) : SolverSyntax.HiF.hfport :=
  match p with
  | CInput id t => HiFirrtl.Finput id (solver_type t)
  | COutput id t => HiFirrtl.Foutput id (solver_type t)
  | CClock id => HiFirrtl.Finput id (HiEnv.Gtyp Env.Fclock)
  end.

Definition sem_port (p : common_port) : SemSyntax.HiF.hfport :=
  match p with
  | CInput id t => SemSyntax.Finput id (sem_type t)
  | COutput id t => SemSyntax.Foutput id (sem_type t)
  | CClock id =>
      SemSyntax.Finput id (HiEnv_with_implicit_widths.Gtyp
        Env_with_implicit_widths.Fclock)
  end.

Definition solver_stmt (s : common_stmt) : SolverSyntax.HiF.hfstmt :=
  match s with
  | CSkip => HiFirrtl.Sskip VarOrder.T
  | CWire id t => HiFirrtl.Swire id (solver_type t)
  | CReg id t clock rst =>
      HiFirrtl.Sreg id (HiFirrtl.mk_freg (solver_type t)
        (solver_expr (CRef clock)) (solver_reset rst))
  | CConnect id value =>
      HiFirrtl.Sfcnct (HiFirrtl.Eid id) (solver_expr value)
  end.

Definition sem_stmt (s : common_stmt) : SemSyntax.HiF.hfstmt :=
  match s with
  | CSkip => SemSyntax.Sskip VarOrder.T
  | CWire id t => SemSyntax.Swire id (sem_type t)
  | CReg id t clock rst =>
      SemSyntax.Sreg id (SemSyntax.mk_freg (sem_type t)
        (sem_expr (CRef clock)) (sem_reset rst))
  | CConnect id value =>
      SemSyntax.Sfcnct (SemSyntax.Eid id) (sem_expr value)
  end.

Fixpoint solver_stmts (ss : seq common_stmt) : SolverSyntax.HiF.hfstmt_seq :=
  match ss with
  | [::] => HiFirrtl.Qnil VarOrder.T
  | s :: rest => HiFirrtl.Qcons (solver_stmt s) (solver_stmts rest)
  end.

Fixpoint sem_stmts (ss : seq common_stmt) : SemSyntax.HiF.hfstmt_seq :=
  match ss with
  | [::] => SemSyntax.Qnil VarOrder.T
  | s :: rest => SemSyntax.Qcons (sem_stmt s) (sem_stmts rest)
  end.

Definition solver_module (m : common_module) : SolverSyntax.HiF.hfmodule :=
  HiFirrtl.FInmod (common_module_name m)
    (map solver_port (common_ports m)) (solver_stmts (common_stmts m)).

Definition sem_module (m : common_module) : SemSyntax.HiF.hfmodule :=
  SemSyntax.FInmod (common_module_name m)
    (map sem_port (common_ports m)) (sem_stmts (common_stmts m)).

Definition solver_circuit (circuit_name : var) (m : common_module)
    : SolverSyntax.HiF.hfcircuit :=
  HiFirrtl.Fcircuit circuit_name [:: solver_module m].

Definition sem_circuit (m : common_module) : seq SemSyntax.HiF.hfmodule :=
  [:: sem_module m].

Definition solver_type_map :=
  SolverSyntax.VM.t (HiEnv.ftype * SolverSyntax.forient).
Definition sem_component_map :=
  SemSyntax.VM.t
    (HiEnv_with_implicit_widths.ftype * HiEnv_with_implicit_widths.fcomponent).
Definition sem_circuit_map := SemSyntax.VM.t sem_component_map.

Definition valid_controls (m : common_module) (tmap : solver_type_map) : Prop :=
  List.Forall
    (fun s =>
       match s with
       | CReg _ _ clock rst =>
           (exists orient,
               SolverSyntax.VM.find clock tmap =
                 Some (HiEnv.Gtyp Env.Fclock, orient)) /\
           match rst with
           | CNoReset => True
           | CReset trigger _ =>
               exists orient,
                 SolverSyntax.VM.find trigger tmap =
                   Some (HiEnv.Gtyp (Env.Fuint 1), orient)
           end
       | _ => True
       end)
    (common_stmts m).

Definition original_implicit (initial : sem_circuit_map) (module_name id : var) : Prop :=
  match SemSyntax.VM.find module_name initial with
  | Some components =>
      match SemSyntax.VM.find id components with
      | Some (HiEnv_with_implicit_widths.Gtyp
          (Env_with_implicit_widths.Fuint_implicit _), _)
      | Some (HiEnv_with_implicit_widths.Gtyp
          (Env_with_implicit_widths.Fsint_implicit _), _) => True
      | _ => False
      end
  | None => False
  end.

Definition semantic_width (result : sem_circuit_map) (module_name id : var)
    : option nat :=
  match SemSyntax.VM.find module_name result with
  | Some components =>
      match SemSyntax.VM.find id components with
      | Some (HiEnv_with_implicit_widths.Gtyp
          (Env_with_implicit_widths.Fuint_implicit w), _)
      | Some (HiEnv_with_implicit_widths.Gtyp
          (Env_with_implicit_widths.Fsint_implicit w), _) => Some w
      | _ => None
      end
  | None => None
  end.

Definition solver_width (solution : constraints.Valuation) (id : var) : option nat :=
  SolverSyntax.PVM.find (id, N0) solution.

Definition covered (solution : constraints.Valuation) (initial : sem_circuit_map)
    (module_name : var) : Prop :=
  forall id, original_implicit initial module_name id ->
    exists w, solver_width solution id = Some w.

(* This statement is a proof obligation, not a proved equivalence. *)
Theorem single_module_min_solution_matches_fixed_point :
  forall (m : common_module) (circuit_name : var)
         (solver_tmap : solver_type_map) (solution : constraints.Valuation)
         (initial result : sem_circuit_map) (n : nat),
    SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_tmap ->
    valid_controls m solver_tmap ->
    inferWidths.solve_fun (solver_circuit circuit_name m) solver_tmap = Some solution ->
    Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
    Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
    covered solution initial (common_module_name m) ->
    forall id, original_implicit initial (common_module_name m) id ->
      exists w,
        solver_width solution id = Some w /\
        semantic_width result (common_module_name m) id = Some w.
Admitted.
