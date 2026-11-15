From Coq Require Import NArith.
From mathcomp Require Import all_ssreflect.
From Lib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths
  HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths.
From Semantics Require Import Semantics_with_implicit_widths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Arguments Econst {var} _ _.
Arguments NRst {var}.
Arguments Qnil {var}.
Delimit Scope N_scope with nvar.

Definition uint_implicit (n : nat) := Gtyp (Fuint_implicit n).
Definition uint_explicit (n : nat) := Gtyp (Fuint n).
Definition uint_const (n : nat) : HiF.hfexpr := Econst (Fuint n) [::].
Definition ref_expr (v : var) : HiF.hfexpr := Eref (Eid v).
Definition reg_stmt (v : var) (t : ftype) (rst : HiF.rst) : HiF.hfstmt :=
  Sreg v (mk_freg t (uint_const 1) rst).
Definition reset_stmt (v : var) (t : ftype) (value : HiF.hfexpr) : HiF.hfstmt :=
  reg_stmt v t (Rst (uint_const 1) value).
Definition one_reg (t : ftype) : VM.t (ftype * fcomponent) :=
  VM.add 1%nvar (t, Register) (VM.empty _).
Definition result_type (result : option (VM.t (ftype * fcomponent))) (v : var) :=
  match result with
  | Some tmap => VM.find v tmap
  | None => None
  end.

Example reset_expands_implicit :
  result_type (width_iter_one (one_reg (uint_implicit 2))
    (reset_stmt 1%nvar (uint_implicit 2) (uint_const 8))) 1%nvar =
  Some (uint_implicit 8, Register).
Proof. vm_compute. reflexivity. Qed.

Example reset_does_not_shrink_implicit :
  result_type (width_iter_one (one_reg (uint_implicit 8))
    (reset_stmt 1%nvar (uint_implicit 8) (uint_const 2))) 1%nvar =
  Some (uint_implicit 8, Register).
Proof. vm_compute. reflexivity. Qed.

Example reset_preserves_explicit :
  result_type (width_iter_one (one_reg (uint_explicit 2))
    (reset_stmt 1%nvar (uint_explicit 2) (uint_const 8))) 1%nvar =
  Some (uint_explicit 2, Register).
Proof. vm_compute. reflexivity. Qed.

Example no_reset_unchanged :
  result_type (width_iter_one (one_reg (uint_implicit 2))
    (reg_stmt 1%nvar (uint_implicit 2) NRst)) 1%nvar =
  Some (uint_implicit 2, Register).
Proof. vm_compute. reflexivity. Qed.

Definition with_source :=
  VM.add 2%nvar (uint_implicit 8, Wire) (one_reg (uint_implicit 2)).

Example reset_reference_updates_only_register :
  let result := width_iter_one with_source
    (reset_stmt 1%nvar (uint_implicit 2) (ref_expr 2%nvar)) in
  (result_type result 1%nvar, result_type result 2%nvar) =
  (Some (uint_implicit 8, Register), Some (uint_implicit 8, Wire)).
Proof. vm_compute. reflexivity. Qed.

Example reset_does_not_expand_source :
  let tmap := VM.add 2%nvar (uint_implicit 2, Wire) (one_reg (uint_implicit 8)) in
  let result := width_iter_one tmap
    (reset_stmt 1%nvar (uint_implicit 8) (ref_expr 2%nvar)) in
  (result_type result 1%nvar, result_type result 2%nvar) =
  (Some (uint_implicit 8, Register), Some (uint_implicit 2, Wire)).
Proof. vm_compute. reflexivity. Qed.

Example reset_signed_width :
  result_type (width_iter_one (one_reg (Gtyp (Fsint_implicit 1)))
    (reset_stmt 1%nvar (Gtyp (Fsint_implicit 1)) (Econst (Fsint 5) [::]))) 1%nvar =
  Some (Gtyp (Fsint_implicit 5), Register).
Proof. vm_compute. reflexivity. Qed.

Example reset_value_concretizes_abstract_register :
  let tmap := VM.add 2%nvar (Gtyp Fasyncreset, Wire) (one_reg (Gtyp Freset)) in
  result_type (width_iter_one tmap
    (reset_stmt 1%nvar (Gtyp Freset) (ref_expr 2%nvar))) 1%nvar =
  Some (Gtyp Fasyncreset, Register).
Proof. vm_compute. reflexivity. Qed.

Example reset_trigger_is_not_reset_value :
  result_type (width_iter_one (one_reg (uint_implicit 0))
    (reg_stmt 1%nvar (uint_implicit 0) (Rst (uint_const 9) (uint_const 3)))) 1%nvar =
  Some (uint_implicit 3, Register).
Proof. vm_compute. reflexivity. Qed.

Example reset_and_connection_both_contribute :
  let stmts := Qcons (reset_stmt 1%nvar (uint_implicit 0) (uint_const 5))
    (Qcons (Sfcnct (Eid 1%nvar) (uint_const 9)) Qnil) in
  result_type (width_iter (one_reg (uint_implicit 0)) stmts) 1%nvar =
  Some (uint_implicit 9, Register).
Proof. vm_compute. reflexivity. Qed.

Example self_reset_is_stable :
  result_type (width_iter_one (one_reg (uint_implicit 2))
    (reset_stmt 1%nvar (uint_implicit 2) (ref_expr 1%nvar))) 1%nvar =
  Some (uint_implicit 2, Register).
Proof. vm_compute. reflexivity. Qed.

Example reset_missing_register :
  width_iter_one (VM.empty _)
    (reset_stmt 1%nvar (uint_implicit 0) (uint_const 4)) = None.
Proof. vm_compute. reflexivity. Qed.

Example reset_wrong_component_kind :
  width_iter_one (VM.add 1%nvar (uint_implicit 0, Wire) (VM.empty _))
    (reset_stmt 1%nvar (uint_implicit 0) (uint_const 4)) = None.
Proof. vm_compute. reflexivity. Qed.

Example reset_missing_reference :
  width_iter_one (one_reg (uint_implicit 0))
    (reset_stmt 1%nvar (uint_implicit 0) (ref_expr 2%nvar)) = None.
Proof. vm_compute. reflexivity. Qed.

Example reset_incompatible_type :
  width_iter_one (one_reg (uint_implicit 0))
    (reset_stmt 1%nvar (uint_implicit 0) (Econst (Fsint 4) [::])) = None.
Proof. vm_compute. reflexivity. Qed.

Example reset_invalid_literal :
  width_iter_one (one_reg (uint_implicit 0))
    (reset_stmt 1%nvar (uint_implicit 0) (Econst (Fuint 1) [:: true; true])) = None.
Proof. vm_compute. reflexivity. Qed.

Definition bundle (flip : fflip) (n : nat) :=
  Btyp (Fflips 3%nvar flip (Atyp (uint_implicit n) 2) Fnil).

Example reset_passive_aggregate :
  let tmap := VM.add 2%nvar (bundle Nflip 7, Wire) (one_reg (bundle Nflip 1)) in
  result_type (width_iter_one tmap
    (reset_stmt 1%nvar (bundle Nflip 1) (ref_expr 2%nvar))) 1%nvar =
  Some (bundle Nflip 7, Register).
Proof. vm_compute. reflexivity. Qed.

Example reset_nonpassive_rejected :
  let tmap := VM.add 2%nvar (bundle Flipped 7, Wire) (one_reg (bundle Flipped 1)) in
  width_iter_one tmap (reset_stmt 1%nvar (bundle Flipped 1) (ref_expr 2%nvar)) = None.
Proof. vm_compute. reflexivity. Qed.

Example reset_mismatched_array_lengths :
  let tmap := VM.add 2%nvar (Atyp (uint_implicit 7) 3, Wire)
    (one_reg (Atyp (uint_implicit 1) 2)) in
  width_iter_one tmap
    (reset_stmt 1%nvar (Atyp (uint_implicit 1) 2) (ref_expr 2%nvar)) = None.
Proof. vm_compute. reflexivity. Qed.

Definition reset_circuit : seq HiF.hfmodule :=
  [:: FInmod 10%nvar [::]
    (Qcons (reg_stmt 1%nvar (uint_implicit 0) (Rst (uint_const 1) (ref_expr 2%nvar)))
      (Qcons (Swire 2%nvar (uint_implicit 0))
        (Qcons (Sfcnct (Eid 2%nvar) (uint_const 6)) Qnil)))].

Definition circuit_reg_type (n : nat) :=
  match circuit_tmap_implicits reset_circuit n with
  | Some circuit_map =>
      match VM.find 10%nvar circuit_map with
      | Some module_map => VM.find 1%nvar module_map
      | None => None
      end
  | None => None
  end.

Example reset_circuit_requires_multiple_iterations :
  circuit_reg_type 0 = None /\ circuit_reg_type 1 = None /\
  circuit_reg_type 2 = Some (uint_implicit 6, Register).
Proof. vm_compute. repeat split; reflexivity. Qed.
