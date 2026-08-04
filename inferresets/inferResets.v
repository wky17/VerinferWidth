From HB Require Import structures.
From Coq Require Import ZArith Arith List Ascii String Lia FMaps.
From mathcomp Require Import all_ssreflect.
From Lib Require Import SsrOrder Var.
From firrtl Require Import Env LoFirrtl HiEnv HiFirrtl.
From Solver Require Import extract_cs_multimod inferWidths_multimod.
From mathcomp.tarjan Require Import kosaraju.
From Semantics Require Import Semantics.
Import ListNotations.

Section finTripVar.
Variable c : HiF.hfcircuit.

Definition tripvar_is_fintype (tv : TripVar.t * fgtyp) : Prop :=
  pv_is_fintype (snd (fst tv)) c.  
Lemma tripvar_is_fintypeP tv : tripvar_is_fintype tv.
Proof.
Admitted.

Definition finTripVar : Type := { tv : (TripVar.t * fgtyp) | tripvar_is_fintype tv}.

(* 投影函数 *)
Definition finTripVar2TripVar (ftv : finTripVar) : TripVar.t * fgtyp := proj1_sig ftv.
Definition TripVar2finTripVar (pv : TripVar.t * fgtyp) : finTripVar :=
  exist _ pv (tripvar_is_fintypeP pv).

Fixpoint list_finTripVar (modnum : N) (v : N) (offset : nat) (t : ftype) (flag : nat) : list (finTripVar * nat) * nat * nat :=
  match t with 
  | Gtyp gt => ([(TripVar2finTripVar ((modnum, (v, N.of_nat offset)), gt), flag)], flag+1, offset+1)
  | Atyp atyp _ => list_finTripVar modnum v offset atyp flag
  | Btyp ff => list_finTripVar_f modnum v offset ff flag
  end
with list_finTripVar_f (modnum : N) (v : N) (offset : nat) (ff : ffield) (flag : nat) : list (finTripVar * nat) * nat * nat :=
  match ff with
  | Fnil => (nil, flag, offset)
  | Fflips _ _ t fs => let '(ls, flag0, offset0) := list_finTripVar modnum v offset t flag in 
                       let '(ls0, flag1, offset1) := list_finTripVar_f modnum v offset0 fs flag0 in
                       (ls ++ ls0, flag1, offset1)
  end.

Definition list_finTripVar_circuit : list (finTripVar * nat) * nat :=
  (* number implicit ground types by nat *)
  match circuit_tmap c with 
  | Some tmap => List.fold_left (fun '(ls0, flag0) '(modnum, modtmap) =>
    List.fold_left (fun '(ls1, flag1) '(key, (ft, _)) => 
                  let '(ls2, flag2, _) := list_finTripVar modnum key 0 ft flag1 in (ls1 ++ ls2, flag2)
                  ) (VM.elements modtmap) (ls0, flag0)
    ) (VM.elements tmap) (nil, 1)
  | _ => (nil, 0)
  end.

Definition finTripVar_pickle (v : finTripVar) : nat :=
  let '(fin_list, _) := list_finTripVar_circuit in
  match List.find (fun '(pv, _) => (finTripVar2TripVar pv) == (finTripVar2TripVar v)) fin_list with
  | Some (_, n) => n 
  | _ => 0
  end.

Definition finTripVar_unpickle (n : nat) : option finTripVar :=
  let '(fin_list, _) := list_finTripVar_circuit in
  match List.find (fun '(_, n') => n == n') fin_list with
  | Some (pv, n) => Some pv 
  | _ => None
  end.

Lemma finTripVar_pickleK : pcancel finTripVar_pickle finTripVar_unpickle.
Proof.
Admitted.
HB.instance Definition _ := isCountable.Build finTripVar finTripVar_pickleK.

Definition finTripVar_enum_subdef : seq finTripVar :=
  let '(fin_list, _) := list_finTripVar_circuit in map fst fin_list.

Lemma finTripVar_enumP_subdef : Finite.axiom finTripVar_enum_subdef.
Proof.
Admitted.

HB.instance Definition _ := isFinite.Build finTripVar finTripVar_enumP_subdef.

End finTripVar.

Section solve_reset.

Variable (c : HiF.hfcircuit).

Definition Graph : Type := finTripVar c -> finTripVar c -> bool.
Definition empty_Graph (x y : finTripVar c) : bool :=
  false.
Definition res_r := kosaraju empty_Graph. 

Definition add_dependency (g : Graph) (from to : finTripVar c) : Graph :=
  fun x y => g x y || (((finTripVar2TripVar c x) == (finTripVar2TripVar c from)) && ((finTripVar2TripVar c y) == (finTripVar2TripVar c to))).

Fixpoint reset_graph_fcnct (tv0 tv1 : TripVar.t) (offset : nat) 
                          (ft0 ft1 : ftype) (g : Graph) : Graph :=
  match ft0, ft1 with
  | Gtyp Freset, Gtyp gt =>
    let tv0' := (fst tv0, (fst (snd tv0), N.add (snd (snd tv0)) (N.of_nat offset))) in
    let tv1' := (fst tv1, (fst (snd tv1), N.add (snd (snd tv1)) (N.of_nat offset))) in
    let g' := add_dependency g (TripVar2finTripVar c (tv0', Freset)) (TripVar2finTripVar c (tv1', gt)) in 
    add_dependency g' (TripVar2finTripVar c (tv1', gt)) (TripVar2finTripVar c (tv0', Freset)) 
  | Gtyp gt, Gtyp Freset => 
    let tv0' := (fst tv0, (fst (snd tv0), N.add (snd (snd tv0)) (N.of_nat offset))) in
    let tv1' := (fst tv1, (fst (snd tv1), N.add (snd (snd tv1)) (N.of_nat offset))) in
    let g' := add_dependency g (TripVar2finTripVar c (tv0', gt)) (TripVar2finTripVar c (tv1', Freset)) in 
    add_dependency g' (TripVar2finTripVar c (tv1', Freset)) (TripVar2finTripVar c (tv0', gt)) 
  | Gtyp _, Gtyp _ => g
  | Atyp atyp0 n0 , Atyp atyp1 n1 => if n0 == n1 then
      let fix reset_graph_array_aux (n' : nat) (off : nat) (g0 : Graph) :=
        match n' with
        | 0 => g0
        | S n'' =>
            let g' := reset_graph_fcnct tv0 tv1 off atyp0 atyp1 g0 in
            reset_graph_array_aux n'' (off + size_of_ftype atyp0) g'
        end in reset_graph_array_aux n0 offset g 
    else g
  | Btyp btyp0, Btyp btyp1 =>
    reset_graph_btyp_aux tv0 tv1 offset btyp0 btyp1 g
  | _, _ => g
  end
with reset_graph_btyp_aux (tv0 tv1 : TripVar.t) (offset : nat) 
                          (btyp0 btyp1 : ffield) (g : Graph) : Graph :=
  match btyp0, btyp1 with
  | Fflips _ _ ft0 ff0, Fflips _ _ ft1 ff1 => 
    let g' := reset_graph_fcnct tv0 tv1 offset ft0 ft1 g in
    reset_graph_btyp_aux tv0 tv1 (offset + size_of_ftype ft0) ff0 ff1 g'
  | _, _ => g 
    end.

Fixpoint reset_graph_ss (mv : VM.key) (ss : HiF.hfstmt_seq) (mod_tmap : VM.t (ftype * forient)) (tmap : VM.t (VM.t (ftype * forient)))
  (instmap : VM.t VM.key) (g : Graph) : (VM.t VM.key) * Graph :=
  match ss with
  | Qnil => (instmap, g) 
  | Qcons s st => let (instmap', g') := reset_graph_s mv s mod_tmap tmap instmap g in
    reset_graph_ss mv st mod_tmap tmap instmap' g'
  end
with reset_graph_s (mv : VM.key) (s : HiF.hfstmt) (mod_tmap : VM.t (ftype * forient)) (tmap : VM.t (VM.t (ftype * forient)))
  (instmap : VM.t VM.key) (g : Graph) : (VM.t VM.key) * Graph :=
  match s with
  | Sinst inst_v inst_mv => (VM.add inst_v inst_mv instmap, g)
  | Sfcnct r (Eref ref) => match ref2pv_mod r mv instmap tmap, ref2pv_mod ref mv instmap tmap
    , type_of_ref r mod_tmap, type_of_ref ref mod_tmap with
      | Some tv0, Some tv1, Some ft0, Some ft1 => (instmap, reset_graph_fcnct tv0 tv1 0 ft0 ft1 g)
      | _, _, _, _ => (instmap, g) 
      end
  | Swhen c ss_true ss_false => let (instmap', g') := reset_graph_ss mv ss_true mod_tmap tmap instmap g in
    reset_graph_ss mv ss_true mod_tmap tmap instmap' g'
  | _ => (instmap, g) 
  end.

Fixpoint reset_graph_ml (ml : list HiF.hfmodule) (tmap : VM.t (VM.t (ftype * forient))) (g : Graph) : Graph :=
  match ml with
  | nil => g
  | FInmod mv _ ss :: tl => match VM.find mv tmap with
    | Some mod_tmap => 
      let (_, g') := reset_graph_ss mv ss mod_tmap tmap (VM.empty VM.key) g in
      reset_graph_ml tl tmap g'
    | _ => g
    end
  | _ :: tl => reset_graph_ml tl tmap g
  end.

Definition reset_graph_c (c : HiF.hfcircuit) (tmap : VM.t (VM.t (ftype * forient))) : Graph :=
  match c with
  | Fcircuit _ ml => reset_graph_ml ml tmap empty_Graph
  end.

(*Definition InferResets_fun : option HiF.hfcircuit :=
  match circuit_tmap c with
  | Some tmap =>
    let dpdcg := reset_graph_c c tmap in 
    let res := rev (map rev (kosaraju dpdcg)) in
    let res' := map (map (@finTripVar2TripVar c)) res in
    match solve_rst res' tmap with
    | Some newtm => InferWidths_trans_c c newtm
    | _ => None
    end
  | _, _ => None
  end.
*)
End solve_reset.