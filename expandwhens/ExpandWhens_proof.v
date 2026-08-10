From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From firrtl Require Import Env HiEnv LoFirrtl HiFirrtl.
From Lib Require Import Nbits Var.
From Semantics Require Import Semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Definition unique_node_dclr (ss : HiFP.hfstmt_seq) : Prop :=
  forall v e, Qin (Snode v e) ss -> (forall v' e', Qin (Snode v' e') (Qremove (Snode v e) ss) -> v <> v') /\ (forall e', ~ Qin (Sfcnct (Eid v) e') ss) /\ (forall v', Qin (Sinvalid (Eid v')) ss -> v <> v').

Definition unique_node_dclr_when (ss : HiFP.hfstmt_seq) : Prop :=
  forall v e, Qin_when (Snode v e) ss -> 
  (forall v' e', Qin_when (Snode v' e') (Qremove_when (Snode v e) ss) -> v <> v') /\ (forall e', ~ Qin_when (Sfcnct (Eid v) e') ss) /\ (forall v', Qin_when (Sinvalid (Eid v')) ss -> v <> v').

(* This axiom states that evaluating an invalidation is always allowed
   and do not care about the value it takes. They are just unspecified values that can be chosen nondeterministically. *)
Axiom eval_invalid_is_allowed : forall gt s tmap val, Sem_HiFP.eval_hfexpr (Sem_HiFP.indeterminate_cst gt) s tmap = Some val.
(* Statement evaluation preserves the shape imposed by [tmap]. non-writable kinds and undeclared names remain absent, registers are
   absent from the current-state map, and non-registers are absent from the register-update map. *)
Axiom eval_hfstmts_find_none_cases : forall ss init_s tmap rs s v, Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
  match PVM.find v tmap with
  | Some (_, In_port) => PVM.find v s = None /\ PVM.find v rs = None
  | Some (_, Instanceof) => PVM.find v s = None /\ PVM.find v rs = None
  | Some (_, Memory) => PVM.find v s = None /\ PVM.find v rs = None
  | Some (_, Fmodule) => PVM.find v s = None /\ PVM.find v rs = None
  | Some (_, Register) => PVM.find v s = None
  | None => PVM.find v s = None /\ PVM.find v rs = None
  | _ => PVM.find v rs = None
  end.
Axiom well_formedness : forall (ss : HiFP.hfstmt_seq) (tmap : PVM.t (fgtyp * fcomponent)), 
  unique_node_dclr_when ss /\ unique_node_dclr ss /\
  (forall v v' e' gt, (PVM.find v tmap = Some (gt, Out_port) \/ PVM.find v tmap = Some (gt, Wire)) -> Qin (Snode v' e') ss -> v <> v') /\
  (forall v conn_map, Qin (Sfcnct (Eid v) (Eref (Eid v))) (convert_to_connect_stmts conn_map) \/
  (exists e : hfexpr ProdVarOrder.T, Qin (Sfcnct (Eid v) e) (convert_to_connect_stmts conn_map))) /\
  (forall v, ~ exists r, Qin (Sreg v r) ss) /\
  (forall v, ~ exists e, Qin (Snode v e) ss).

Definition func_type : Type := PVM.t bits -> PVM.t bits -> PVM.t bits -> PVM.t (fgtyp * fcomponent) -> option (PVM.t bits * PVM.t bits).
Definition func_type_included (fun1 fun2 : func_type) (tmap : PVM.t (fgtyp * fcomponent)) : Prop := forall (init_s1 init_s2 : PVM.t bits) (s1 s2 rs1 rs2 : PVM.t bits),
  pvm_included init_s1 init_s2 -> fun1 (PVM.empty bits) (PVM.empty bits) init_s1 tmap = Some (rs1, s1) -> fun2 (PVM.empty bits) (PVM.empty bits) init_s2 tmap = Some (rs2, s2) -> 
  (pvm_included s1 s2) /\ (pvm_included rs1 rs2).

Lemma iterate_func_included n fun1 fun2 init_s1 init_s2 tmap sem sem_new : 
  func_type_included fun1 fun2 tmap -> pvm_included init_s1 init_s2 -> Sem_HiFP.iterate n fun1 init_s1 tmap = Some sem -> Sem_HiFP.iterate n fun2 init_s2 tmap = Some sem_new -> 
  pvm_included sem sem_new.
Proof.
  intros Hfun_included. move : init_s1 init_s2 sem sem_new. 
  induction n as [|n IH]; intros init_s1 init_s2 sem sem_new Hinit_eq Hiter1 Hiter2.
  - (* Case n = 0 *)
    simpl in Hiter1, Hiter2.
    inversion Hiter1; inversion Hiter2. subst sem sem_new; done.
  - (* Case n = S n' *)
    simpl in Hiter1, Hiter2.
    destruct (fun1 (PVM.empty bitseq) (PVM.empty bitseq) init_s1 tmap) as [[rs1 ns1]|] eqn:Hcall1;
      [|discriminate].
    destruct (fun2 (PVM.empty bitseq) (PVM.empty bitseq) init_s2 tmap) as [[rs2 ns2]|] eqn:Hcall2;
      [|discriminate].
    unfold func_type_included in Hfun_included. specialize (Hfun_included init_s1 init_s2 ns1 ns2 rs1 rs2).
    specialize (Hfun_included Hinit_eq Hcall1 Hcall2). move : Hfun_included => [Hfun_included _]. 
    move : Hiter1 Hiter2; apply IH.
    move : Hinit_eq Hfun_included; apply included_update_values_included.
Qed.

Lemma eval_hfstmts_unique_ss_find_eq ss rs0 ns0 init_s tmap rs s v : 
  (forall v' e', Qin (Snode v' e') ss -> v <> v') -> (forall e', ~ Qin (Sfcnct (Eid v) e') ss) -> (forall v', Qin (Sinvalid (Eid v')) ss -> v <> v') ->
  (forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) ss) ->
  Sem_HiFP.eval_hfstmts ss rs0 ns0 init_s tmap = Some (rs, s) -> PVM.find v s = PVM.find v ns0
with eval_hfstmt_unique_ss_find_eq st rs0 ns0 init_s tmap rs s v : match st with
  | Snode v' _ => v <> v'
  | Sfcnct (Eid v') _ => v <> v'
  | Sinvalid (Eid v') => v <> v'
  | Swhen _ _ _ => false
  | _ => True
  end ->
  Sem_HiFP.eval_hfstmt st rs0 ns0 init_s tmap = Some (rs, s) -> PVM.find v s = PVM.find v ns0.
Proof.
  clear eval_hfstmts_unique_ss_find_eq. move : ss rs0 ns0. elim. simpl; intros. inversion H3; subst s; done.
  intros hd tl IH. simpl; intros rs0 ns0 Hnode Hcnct Hinvalid Hwhen Hevals. destruct (Sem_HiFP.eval_hfstmt hd rs0 ns0 init_s tmap) as [[rs1 ns1]|] eqn : Heval; try discriminate.
  apply IH in Hevals; clear IH. rewrite Hevals. move : Heval; apply eval_hfstmt_unique_ss_find_eq.
  case Hst : hd => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst hd; try done.
  - (* node *) move : Hnode; clear. intro. apply (Hnode _ node_e). simpl. rewrite eq_refl. rewrite eq_refl //.
  - (* cnct *) move : Hcnct; clear. intros. specialize (Hcnct e). destruct ref; try done. move : Hcnct; apply contra_not. intro; subst v. 
    simpl. rewrite eq_refl. rewrite eq_refl //.
  - (* invalid *) move : Hinvalid; clear. intro. destruct ref; try done. apply Hinvalid. simpl. rewrite eq_refl orb_true_l //.
  - (* when *) specialize (Hwhen cond ss_true ss_false); simpl in Hwhen. rewrite eq_refl in Hwhen; simpl in Hwhen. 
    specialize (hfstmt_seq_eqn_refl ss_true) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_true ss_true) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq in Hwhen; simpl in Hwhen. clear Heq Heq'.
    specialize (hfstmt_seq_eqn_refl ss_false) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_false ss_false) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq in Hwhen; simpl in Hwhen. done.
  - (* node *) move : Hnode; clear. intros. apply (Hnode _ e'). rewrite H orb_true_r //.
  - (* cnct *) move : Hcnct; clear. intros. specialize (Hcnct e'). move : Hcnct; apply contra_not. intro. rewrite H orb_true_r //. 
  - (* invalid *) move : Hinvalid; clear. intros. apply Hinvalid. rewrite H orb_true_r //.
  - (* when *) intros. specialize (Hwhen c ss1 ss2). move : Hwhen; apply contra_not; intro. rewrite H orb_true_r //.

  clear eval_hfstmt_unique_ss_find_eq. case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st. 
  (* skip, wire *) 
  1,2,4,5 : simpl; intros _ Heval; inversion Heval; subst rs s; done.
  (* reg *)
  simpl; intros _ Heval. destruct (PVM.find var init_s); try discriminate. inversion Heval; subst rs s; done.
  (* node *)
  simpl; intros Hneq Heval. destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate. inversion Heval; subst rs s.
  rewrite PVM.Lemmas.find_add_neq //. move : Hneq; apply contra_not; intro;
  move: H => [/eqP H1 /eqP H2]; destruct v; destruct var; simpl in H1, H2; subst s s0; done.
  (* cnct *)
  simpl; intros Hneq Heval. destruct ref; try (inversion Heval; subst rs s; done).
  destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate. 
  destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr e init_s tmap); try discriminate; try (inversion Heval; subst rs s; try done).
  1-7 : rewrite PVM.Lemmas.find_add_neq //.
  1-7 : move : Hneq; apply contra_not; intro;
  move: H => [/eqP H1 /eqP H2]; destruct v; destruct s0; simpl in H1, H2; subst s s1; done.
  (* invalid *)
  simpl; intros Hneq Heval. destruct ref; try (inversion Heval; subst rs s; done).
  destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate. 
  destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val); try (inversion Heval; subst rs s; try done).
  1-14 : rewrite PVM.Lemmas.find_add_neq //. 1-14 : move : Hneq; apply contra_not; intro;
  move: H => [/eqP H1 /eqP H2]; destruct v; destruct s0; simpl in H1, H2; subst s s1; done.
  (* when *) intro; done.
Qed.

(*Lemma eval_hfstmts_for_unique_node' ss v e : 
  Qin (Snode v e) ss -> unique_node_dclr ss -> (forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) ss) ->
  forall init_s tmap rs s, Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) -> PVM.find v s = Sem_HiFP.eval_hfexpr e init_s tmap.
Proof.
  intros Hin Hunique Hwhen init_s tmap.
  assert (Hhelper : forall rs0 ns0, PVM.find v ns0 = None -> forall rs s : PVM.t bits,
    Sem_HiFP.eval_hfstmts ss rs0 ns0 init_s tmap = Some (rs, s) ->
    PVM.find v s = Sem_HiFP.eval_hfexpr e init_s tmap). {
    induction ss as [|s ss IH].
    - (* nil *)
      simpl in Hin. done.
    - simpl; intros rs0 ns0 Hnone rs s0 Heval. simpl in Hin. destruct (hfstmt_eqn s (Snode v e)) eqn : Hs.
      + clear Hin. clear IH. destruct (Sem_HiFP.eval_hfstmt s rs0 ns0 init_s tmap) as [[rs1 ns1]|] eqn : Heval_node; try discriminate.
        case Hst : s => [||var reg|||var node_e||ref|cond ss_true ss_false]; subst s; simpl in Hs; try done. simpl in Heval_node.
        destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap) as [val|] eqn : Hnode_e; try discriminate. inversion Heval_node; subst rs1 ns1. clear Heval_node.
        move /andP : Hs => [Hv He]. move /eqP : Hv => Hv. move /eqP : He => He. subst var node_e. rewrite Hnode_e; clear Hnode_e.
        unfold unique_node_dclr in Hunique. assert (Hin : Qin (Snode v e) (Qcons (Snode v e) ss)) by (simpl; rewrite eq_refl; rewrite eq_refl //).
        apply Hunique in Hin; clear Hunique. move : Hin => [Hnode [Hcnct Hinvalid]]. 
        apply eval_hfstmts_unique_ss_find_eq with (v := v) in Heval. rewrite PVM.Lemmas.find_add_eq in Heval. done. apply PVM.M.SE.eq_refl.
        (* node *) simpl in Hnode. intros; apply (Hnode _ e'). rewrite eq_refl; simpl. rewrite eq_refl; simpl; done.
        (* cnct *) intro. specialize (Hcnct e'). move : Hcnct; apply contra_not. intro. simpl; rewrite H //.
        (* invalid *) intros; apply Hinvalid. simpl. done.
        (* when *) intros. specialize (Hwhen c ss1 ss2). move : Hwhen; apply contra_not; intro. simpl; done.
      + rewrite orb_false_l in Hin. 
        destruct (Sem_HiFP.eval_hfstmt s rs0 ns0 init_s tmap) as [[rs1 ns1]|] eqn : Hevals; try discriminate.
        move : Heval. apply (IH Hin). 
        move : Hunique Hs; clear.
        { unfold unique_node_dclr in *; intros.
          assert (Qin (Snode v0 e0) (Qcons s ss)). simpl. rewrite H orb_true_r //.
          specialize (Hunique _ _ H0). move : Hunique => [Hunique0 [Hunique1 Hunique2]]. split.
          intros. apply (Hunique0 _ e'). simpl. destruct (hfstmt_eqn s (Snode v0 e0)). move : H1; apply in_qremove. simpl; rewrite H1 orb_true_r //. split.
          intros. specialize (Hunique1 e'). move : Hunique1; apply contra_not.
          simpl; intros. rewrite H1 orb_true_r //.
          intros. apply Hunique2. simpl. rewrite H1 orb_true_r //. }
        { intros. specialize (Hwhen c ss1 ss2). move : Hwhen; apply contra_not; intro. simpl. rewrite H orb_true_r //. }
        { unfold unique_node_dclr in Hunique. 
          assert (Qin (Snode v e) (Qcons s ss)). simpl. rewrite Hin orb_true_r //.
          specialize (Hunique v e H).
          assert (Hwhen' : forall c ss1 ss2, ~ hfstmt_eqn s (Swhen c ss1 ss2)).
          intros. specialize (Hwhen c ss1 ss2). move : Hwhen; apply contra_not; intro. simpl. rewrite H0 orb_true_l //.
          move : Hevals Hnone Hs Hunique Hwhen'; clear; intros. destruct s as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c ss1 ss2] eqn : Hstmt; subst s; simpl in Hevals.
          * (* skip, wire, mem, inst *)
            1,2,4,5 : inversion Hevals; subst rs1 ns1; done.
          * (* reg *)
            destruct (PVM.find v0 init_s); try discriminate.
            inversion Hevals; subst rs1 ns1; done.
          * (* node *)
            move : Hunique => [Hunique _].
            destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate.
            inversion Hevals; subst rs1 ns1; rewrite PVM.Lemmas.find_add_neq //.
            assert (Qin (Snode v0 e0) (Qremove (Snode v e) (Qcons (Snode v0 e0) ss))). simpl; simpl in Hs; rewrite Hs. simpl. rewrite eq_refl. rewrite eq_refl. simpl; done.
            specialize (Hunique _ _ H).
            unfold PVM.M.SE.eq. move : Hunique; apply contra_not. intro. move /eqP : H0 => H0; done.
          * (* cnct *)
            move : Hunique => [_ [Hunique _]].
            destruct v0 as [ref|a|a|a] eqn : Href; try (inversion Hevals; subst rs1 ns1; done).
            destruct (PVM.find ref tmap) as [[gt cmpnt]|] eqn : Hfind; try discriminate.
            specialize (Hunique e0). assert (Hnoteq : ~ hfstmt_eqn (Sfcnct (Eid ref) e0) (Sfcnct (Eid v) e0)). 
              move : Hunique; apply contra_not. simpl; intro. rewrite H orb_true_l //.
            assert (Hneq : ~ PVM.M.SE.eq v ref). simpl in Hnoteq. rewrite eq_refl andb_true_r in Hnoteq.
              move : Hnoteq; apply contra_not. intro. unfold PVM.M.SE.eq in H. move /eqP : H => H; subst v; done.
            destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate.
            1-5,7-8 : inversion Hevals; subst rs1 ns1; rewrite PVM.Lemmas.find_add_neq //.
            inversion Hevals; subst rs1 ns1; done.
          * (* invalid *)
            move : Hunique => [_ [_ Hunique]].
            destruct v0 as [ref|a|a|a] eqn : Href; try (inversion Hevals; subst rs1 ns1; done).
            destruct (PVM.find ref tmap) as [[gt cmpnt]|] eqn : Hfind; try discriminate. subst v0. clear Hs.
            assert (Hnoteq : v <> ref). apply Hunique. simpl. rewrite eq_refl orb_true_l //.
            destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val); inversion Hevals; subst rs1 ns1; try done.
            1-14 : rewrite PVM.Lemmas.find_add_neq //. 1-14 : unfold PVM.M.SE.eq; move : Hnoteq; apply contra_not; intro; move /eqP : H => H; done.
          * (* when *) specialize (Hwhen' c ss1 ss2); simpl in Hwhen'. rewrite eq_refl in Hwhen'; simpl in Hwhen'. 
            specialize (hfstmt_seq_eqn_refl ss1) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss1 ss1) as Heq'. apply reflect_iff in Heq'.
            apply Heq' in Heq. rewrite Heq in Hwhen'; simpl in Hwhen'. clear Heq Heq'.
            specialize (hfstmt_seq_eqn_refl ss2) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss2 ss2) as Heq'. apply reflect_iff in Heq'.
            apply Heq' in Heq. rewrite Heq in Hwhen'; simpl in Hwhen'. done. }
  }
  apply Hhelper. done.
Qed.

Lemma eval_hfstmts_unique_when_ss_find_eq ss rs0 ns0 init_s tmap rs s v : 
  (forall v' e', Qin_when (Snode v' e') ss -> v <> v') -> (forall e', ~ Qin_when (Sfcnct (Eid v) e') ss) -> (forall v', Qin_when (Sinvalid (Eid v')) ss -> v <> v') ->
  Sem_HiFP.eval_hfstmts ss rs0 ns0 init_s tmap = Some (rs, s) -> PVM.find v s = PVM.find v ns0
with eval_hfstmt_unique_when_ss_find_eq st rs0 ns0 init_s tmap rs s v : match st with
  | Snode v' _ => v <> v'
  | Sfcnct (Eid v') _ => v <> v'
  | Sinvalid (Eid v') => v <> v'
  | Swhen _ ss1 ss2 => 
    (forall v' e', Qin_when (Snode v' e') ss1 -> v <> v') /\ (forall e', ~ Qin_when (Sfcnct (Eid v) e') ss1) /\ (forall v', Qin_when (Sinvalid (Eid v')) ss1 -> v <> v') /\
    (forall v' e', Qin_when (Snode v' e') ss2 -> v <> v') /\ (forall e', ~ Qin_when (Sfcnct (Eid v) e') ss2) /\ (forall v', Qin_when (Sinvalid (Eid v')) ss2 -> v <> v') 
  | _ => True
  end ->
  Sem_HiFP.eval_hfstmt st rs0 ns0 init_s tmap = Some (rs, s) -> PVM.find v s = PVM.find v ns0.
Proof.
  clear eval_hfstmts_unique_when_ss_find_eq. move : ss rs0 ns0. elim. simpl; intros. inversion H2; subst s; done.
  intros hd tl IH. simpl; intros rs0 ns0 Hnode Hcnct Hinvalid Hevals. destruct (Sem_HiFP.eval_hfstmt hd rs0 ns0 init_s tmap) as [[rs1 ns1]|] eqn : Heval; try discriminate.
  apply IH in Hevals; clear IH. rewrite Hevals. move : Heval; apply eval_hfstmt_unique_when_ss_find_eq.
  case Hst : hd => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst hd; try done.
  - (* node *) move : Hnode; clear. intro. apply (Hnode _ node_e). simpl. rewrite eq_refl. rewrite eq_refl //.
  - (* cnct *) move : Hcnct; clear. intros. specialize (Hcnct e). destruct ref; try done. move : Hcnct; apply contra_not. intro; subst v. 
    simpl. rewrite eq_refl. rewrite eq_refl //.
  - (* invalid *) move : Hinvalid; clear. intro. destruct ref; try done. apply Hinvalid. simpl. rewrite eq_refl orb_true_l //.
  - (* when *) split. intros; apply (Hnode _ e'). rewrite H //. split.
    intro. specialize (Hcnct e'). move : Hcnct; apply contra_not; intro. rewrite H //. split.
    intros; apply Hinvalid. rewrite H //. split.
    intros; apply (Hnode v' e'). rewrite H orb_true_r orb_true_l //. split.
    intro. specialize (Hcnct e'). move : Hcnct; apply contra_not; intro. rewrite H orb_true_r orb_true_l //.
    intros; apply Hinvalid. rewrite H orb_true_r orb_true_l //. 
    intros. apply (Hnode v' e'). rewrite H; destruct hd; try (rewrite orb_true_r; done); try (rewrite orb_true_r orb_true_l; done).
    intros. specialize (Hcnct e'). move : Hcnct; apply contra_not; intro. 
      rewrite H; destruct hd; try (rewrite orb_true_r; done); try (rewrite orb_true_r orb_true_l; done).
    intros; apply Hinvalid. rewrite H; destruct hd; try (rewrite orb_true_r; done); try (rewrite orb_true_r orb_true_l; done).

  clear eval_hfstmt_unique_when_ss_find_eq. case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st. 
  (* skip, wire *) 
  1,2,4,5 : simpl; intros _ Heval; inversion Heval; subst rs s; done.
  (* reg *)
  simpl; intros _ Heval. destruct (PVM.find var init_s); try discriminate. inversion Heval; subst rs s; done.
  (* node *)
  simpl; intros Hneq Heval. destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate. inversion Heval; subst rs s.
  rewrite PVM.Lemmas.find_add_neq //. unfold PVM.M.SE.eq. move : Hneq; apply contra_not. intro. move /eqP : H => H. done.
  (* cnct *)
  simpl; intros Hneq Heval. destruct ref; try (inversion Heval; subst rs s; done).
  destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate. 
  destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr e init_s tmap); try discriminate; try (inversion Heval; subst rs s; try done).
  1-7 : rewrite PVM.Lemmas.find_add_neq //. 1-7 : unfold PVM.M.SE.eq; move : Hneq; apply contra_not; intro; move /eqP : H => H; done.
  (* invalid *)
  simpl; intros Hneq Heval. destruct ref; try (inversion Heval; subst rs s; done).
  destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate. 
  destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val); try (inversion Heval; subst rs s; try done).
  1-14 : rewrite PVM.Lemmas.find_add_neq //. 1-14 : unfold PVM.M.SE.eq; move : Hneq; apply contra_not; intro; move /eqP : H => H; done.
  (* when *) intros [Hnode_true [Hcnct_true [Hinvalid_true [Hnode_false [Hcnct_false Hinvalid_false]]]]] Heval. simpl in Heval.
  destruct (Sem_HiFP.eval_hfexpr cond init_s tmap) as [valc|]; try discriminate. destruct (~~ is_zero valc).
  1,2 :move : Heval; apply eval_hfstmts_unique_when_ss_find_eq; try done.
Qed.

Lemma unique_node_dclr_when_subseq s ss : unique_node_dclr_when (Qcons s ss) -> unique_node_dclr_when ss.
Proof.
  unfold unique_node_dclr_when; intros. assert (Hin : Qin_when (Snode v e) (Qcons s ss)). simpl. rewrite H0.
  destruct s; try (rewrite orb_true_r; done); try (rewrite orb_true_r orb_true_l; done).
  apply H in Hin. move : Hin => [Hnode [Hcnct Hinvalid]]. split.
  intros; apply (Hnode v' e'). simpl. destruct s; simpl; try done. destruct ((s == v) && (h == e)); try done.
  move : H1; apply Qremove_when_Qin_when. simpl; rewrite H1 orb_true_r //.
  destruct (Qin_when (Snode v e) h0). apply Qremove_when_Qin_when in H1. move : H1; apply Qin_when_Qcons.
  destruct (Qin_when (Snode v e) h1). apply Qremove_when_Qin_when in H1. move : H1; apply Qin_when_Qcons.
  move : H1; apply Qin_when_Qcons.
  split. intros. specialize (Hcnct e'). move : Hcnct; apply contra_not; intro; simpl. rewrite H1.
  destruct s; try (rewrite orb_true_r; done); try (rewrite orb_true_r orb_true_l; done).
  intros. apply Hinvalid. simpl. rewrite H1.
  destruct s; try (rewrite orb_true_r; done); try (rewrite orb_true_r orb_true_l; done).
Qed.

Lemma unique_node_dclr_when_branches c ss1 ss2 ss : unique_node_dclr_when (Qcons (Swhen c ss1 ss2) ss) -> unique_node_dclr_when ss1 /\ unique_node_dclr_when ss2.
Proof. 
  unfold unique_node_dclr_when; intros. split.
  intros. assert (Hin : Qin_when (Snode v e) (Qcons (Swhen c ss1 ss2) ss)). simpl. rewrite H0 //.
  apply H in Hin; clear H. move : Hin => [Hnode [Hcnct Hinvalid]]. split.
  intros; apply (Hnode v' e'). simpl.
  destruct (Qin_when (Snode v e) ss1). simpl. rewrite H //.
  destruct (Qin_when (Snode v e) ss2). simpl. apply Qremove_when_Qin_when in H. rewrite H //.
  simpl. apply Qremove_when_Qin_when in H. rewrite H //. split.
  intros. specialize (Hcnct e'). move : Hcnct; apply contra_not; intro; simpl. rewrite H //.
  intros. apply Hinvalid. simpl. rewrite H //.

  intros. assert (Hin : Qin_when (Snode v e) (Qcons (Swhen c ss1 ss2) ss)). simpl. rewrite H0 orb_true_r //.
  apply H in Hin; clear H. move : Hin => [Hnode [Hcnct Hinvalid]]. split.
  intros; apply (Hnode v' e'). simpl.
  destruct (Qin_when (Snode v e) ss1). simpl. apply Qremove_when_Qin_when in H. rewrite H orb_true_r //.
  destruct (Qin_when (Snode v e) ss2). simpl. rewrite H orb_true_r //.
  simpl. apply Qremove_when_Qin_when in H. rewrite H orb_true_r //. split.
  intros. specialize (Hcnct e'). move : Hcnct; apply contra_not; intro; simpl. rewrite H orb_true_r //.
  intros. apply Hinvalid. simpl. rewrite H orb_true_r //.
Qed.

Lemma eval_hfstmts_for_unique_node_helper ss v e init_s tmap : 
  Qin_with_cond (Snode v e) ss init_s tmap -> unique_node_dclr_when ss -> 
  forall rs0 ns0, PVM.find v ns0 = None -> forall rs s,
  Sem_HiFP.eval_hfstmts ss rs0 ns0 init_s tmap = Some (rs, s) ->
  PVM.find v s = Sem_HiFP.eval_hfexpr e init_s tmap
with eval_hfstmt_for_unique_node s v e init_s tmap : 
  forall rs0 ns0, PVM.find v ns0 = None -> forall rs ns,
  Sem_HiFP.eval_hfstmt s rs0 ns0 init_s tmap = Some (rs, ns) ->
  match s with
  | Swhen c ss1 ss2 => match Sem_HiFP.eval_hfexpr c init_s tmap with
    | Some valc => unique_node_dclr_when ss1 /\ unique_node_dclr_when ss2 /\
      if (~~ is_zero valc) then Qin_with_cond (Snode v e) ss1 init_s tmap
      else Qin_with_cond (Snode v e) ss2 init_s tmap 
    | _ => True
    end
  | Snode v0 e0 => (v == v0) && (e == e0)
  | _ => False
  end -> PVM.find v ns = Sem_HiFP.eval_hfexpr e init_s tmap.
Proof.
  clear eval_hfstmts_for_unique_node_helper. move : ss; elim. simpl; intros; done.
  intros s ss IH Hin Hunique rs0 ns0 Hfind rs ns Hevals.
  simpl in Hevals. destruct (Sem_HiFP.eval_hfstmt s rs0 ns0 init_s tmap) as [[rs1 ns1]|] eqn : Heval; try discriminate. 
  simpl in Hin.
  case Hst : s => [||var reg|||var node_e|var cnct_e|var|cond ss_true ss_false]; subst s.
  + (* skip *) simpl in Heval; inversion Heval; subst rs0 ns0. move : Hevals; apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq); try done.
  + (* wire *) simpl in Heval; inversion Heval; subst rs0 ns0. move : Hevals; apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq); try done.
  + (* reg *) simpl in Heval. destruct (PVM.find var init_s); try discriminate.
    inversion Heval; subst rs1 ns1. move : Hevals; apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq); try done.
  + (* mem *) simpl in Heval; inversion Heval; subst rs0 ns0. move : Hevals; apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq); try done.
  + (* inst *) simpl in Heval; inversion Heval; subst rs0 ns0. move : Hevals; apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq); try done.
  + (* node *) destruct (hfstmt_eqn (Snode var node_e) (Snode v e)) eqn : Hs. 
    - (* s is node *) clear Hin IH eval_hfstmt_for_unique_node. simpl in Hs. 
      move /andP : Hs => [Hvar Hnode_e]; move /eqP : Hvar => Hvar; move /eqP : Hnode_e => Hnode_e. subst var node_e.
      unfold unique_node_dclr_when in Hunique. assert (Hin : Qin_when (Snode v e) (Qcons (Snode v e) ss)) by (simpl; rewrite eq_refl; rewrite eq_refl //).
      apply Hunique in Hin; clear Hunique. move : Hin => [Hnode [Hcnct Hinvalid]]. 
      simpl in Hcnct. simpl in Hinvalid. simpl in Hnode; rewrite eq_refl in Hnode; simpl in Hnode. rewrite eq_refl in Hnode; simpl in Hnode.
      apply (eval_hfstmts_unique_when_ss_find_eq Hnode Hcnct Hinvalid) in Hevals.
      rewrite Hevals. simpl in Heval. destruct (Sem_HiFP.eval_hfexpr e init_s tmap); try discriminate.
      inversion Heval; subst rs1 ns1. apply PVM.Lemmas.find_add_eq; apply PVM.M.SE.eq_refl.
    - (* s is in ss *) rewrite orb_false_l in Hin.
      move : Hevals. apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq). move : Hunique Hs Hin Heval Hfind; clear; intros.
      unfold unique_node_dclr_when in Hunique. apply Qin_with_cond2Qin_when in Hin. assert (Qin_when (Snode v e) (Qcons (Snode var node_e) ss)) by (simpl; rewrite Hin orb_true_r //).
      specialize (Hunique v e H).
      move : Hunique => [Hunique _]. specialize (Hunique var node_e). simpl in Heval.
      destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate.
      inversion Heval; subst rs1 ns1; rewrite PVM.Lemmas.find_add_neq //.
      simpl in Hunique; simpl in Hs; rewrite Hs in Hunique. simpl in Hunique. 
      rewrite eq_refl in Hunique; simpl in Hunique. rewrite eq_refl in Hunique; simpl in Hunique.
      assert (true) by done. apply Hunique in H0.
      unfold PVM.M.SE.eq. move : H0; apply contra_not. intro. move /eqP : H0 => H0; done.
  + (* cnct *) simpl in Hin.
      move : Hevals. apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq). 
      move : Hunique Hin Heval Hfind; clear; intros.
      unfold unique_node_dclr_when in Hunique. apply Qin_with_cond2Qin_when in Hin. assert (Qin_when (Snode v e) (Qcons (Sfcnct var cnct_e) ss)) by (simpl; done).
      specialize (Hunique v e H). simpl in Heval. destruct var as [ref|a|a|a] eqn : Href; try (inversion Heval; subst rs1 ns1; done).
      destruct (PVM.find ref tmap) as [[gt cmpnt]|] eqn : Hgt; try discriminate.
      move : Hunique => [_ [Hunique _]]. specialize (Hunique cnct_e). simpl in Hunique. rewrite eq_refl in Hunique; simpl in Hunique.
      destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr cnct_e init_s tmap); try discriminate; 
      inversion Heval; subst rs1 ns1; try done. 1-7 : rewrite PVM.Lemmas.find_add_neq //.
      1-7 : unfold PVM.M.SE.eq; move : Hunique; apply contra_not; intro; move /eqP : H0 => H0; subst v; rewrite eq_refl; simpl; done.
  + (* invalid *) simpl in Hin.
      move : Hevals. apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq). 
      move : Hunique Hin Heval Hfind; clear; intros.
      unfold unique_node_dclr_when in Hunique. apply Qin_with_cond2Qin_when in Hin. assert (Qin_when (Snode v e) (Qcons (Sinvalid var) ss)) by (simpl; done).
      specialize (Hunique v e H). simpl in Heval. destruct var as [ref|a|a|a] eqn : Href; try (inversion Heval; subst rs1 ns1; done).
      destruct (PVM.find ref tmap) as [[gt cmpnt]|] eqn : Hgt; try discriminate.
      move : Hunique => [_ [_ Hunique]]. specialize (Hunique ref). simpl in Hunique. rewrite eq_refl in Hunique; simpl in Hunique.
      destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val); 
      try (inversion Heval; subst rs1 ns1; try done). 1-14 : rewrite PVM.Lemmas.find_add_neq //. 
      1-14 : assert (true) by done; apply Hunique in H0.
      1-14 : unfold PVM.M.SE.eq; move : H0; apply contra_not; intro; move /eqP : H0 => H0; subst v; done.
  + (* when *) specialize (eval_hfstmt_for_unique_node _ _ e _ _ _ _ Hfind _ _ Heval); simpl in eval_hfstmt_for_unique_node.
    simpl in Heval; destruct (Sem_HiFP.eval_hfexpr cond init_s tmap) as [valc|] eqn : Hc; try discriminate. 
    destruct (~~ is_zero valc) eqn : Hcond. 
    - (* go to true *)
      destruct (Qin_with_cond (Snode v e) ss_true init_s tmap) eqn : Hin_true.
      * (* node in true, not in ss *)
        clear IH Hin. rewrite -eval_hfstmt_for_unique_node; try done.
        unfold unique_node_dclr_when in Hunique. assert (Qin_when (Snode v e) (Qcons (Swhen cond ss_true ss_false) ss)). 
        apply Qin_with_cond2Qin_when in Hin_true. simpl; rewrite Hin_true orb_true_l //. apply Hunique in H. move : H => [Hnode [Hcnct Hinvalid]].
        move : Hevals; apply eval_hfstmts_unique_when_ss_find_eq.
        move : Hnode Hin_true; clear; intros. apply (Hnode v' e'). simpl. apply Qin_with_cond2Qin_when in Hin_true. rewrite Hin_true. apply Qin_when_Qcons; done.
        intros. move : (Hcnct e'); clear. apply contra_not. apply Qin_when_Qcons; done.
        intros. apply (Hinvalid v'). move : H; apply Qin_when_Qcons; done.
        apply unique_node_dclr_when_branches in Hunique. move : Hunique => [Hunique0 Hunique1]. split; try done.
      * (* in ss *) rewrite orb_false_l in Hin. move : Hevals; apply (IH Hin).
        move : Hunique; apply unique_node_dclr_when_subseq.
        unfold unique_node_dclr_when in Hunique. assert (Qin_when (Snode v e) (Qcons (Swhen cond ss_true ss_false) ss)). 
        apply Qin_with_cond2Qin_when in Hin. apply Qin_when_Qcons; done. apply Hunique in H. move : H => [Hnode [Hcnct Hinvalid]].
        rewrite -Hfind. move : Heval; apply eval_hfstmts_unique_when_ss_find_eq.
        move : Hnode Hin; clear; intros. intro; subst v'. apply Qin_with_cond2Qin_when in Hin. 
        assert (Qin_when (Snode v e') ss_true \/ Qin_when (Snode v e') ss_false) by (left; done).
        apply (Qin_when_uniqie_False Hnode Hin H0).
        intros. move : (Hcnct e'); clear. apply contra_not. intro; simpl. rewrite H //.
        intros. apply (Hinvalid v'). simpl. rewrite H //.
    - (* go to false *)
      destruct (Qin_with_cond (Snode v e) ss_false init_s tmap) eqn : Hin_false.
      * (* node in false, not in ss *)
        clear IH Hin. rewrite -eval_hfstmt_for_unique_node; try done.
        unfold unique_node_dclr_when in Hunique. assert (Qin_when (Snode v e) (Qcons (Swhen cond ss_true ss_false) ss)). 
        apply Qin_with_cond2Qin_when in Hin_false. simpl; rewrite Hin_false orb_true_r //. apply Hunique in H. move : H => [Hnode [Hcnct Hinvalid]].
        move : Hevals; apply eval_hfstmts_unique_when_ss_find_eq.
        move : Hnode Hin_false; clear; intros. apply (Hnode v' e'). simpl. apply Qin_with_cond2Qin_when in Hin_false. rewrite Hin_false. 
        destruct (Qin_when (Snode v e) ss_true); apply Qin_when_Qcons; done.
        intros. move : (Hcnct e'); clear. apply contra_not. apply Qin_when_Qcons; done.
        intros. apply (Hinvalid v'). move : H; apply Qin_when_Qcons; done.
        apply unique_node_dclr_when_branches in Hunique. move : Hunique => [Hunique0 Hunique1]. split; try done.
        * (* in ss *) rewrite orb_false_l in Hin. move : Hevals; apply (IH Hin).
        move : Hunique; apply unique_node_dclr_when_subseq.
        unfold unique_node_dclr_when in Hunique. assert (Qin_when (Snode v e) (Qcons (Swhen cond ss_true ss_false) ss)). 
        apply Qin_with_cond2Qin_when in Hin. apply Qin_when_Qcons; done. apply Hunique in H. move : H => [Hnode [Hcnct Hinvalid]].
        rewrite -Hfind. move : Heval; apply eval_hfstmts_unique_when_ss_find_eq.
        move : Hnode Hin; clear; intros. intro; subst v'. apply Qin_with_cond2Qin_when in Hin. 
        assert (Qin_when (Snode v e') ss_true \/ Qin_when (Snode v e') ss_false) by (right; done).
        apply (Qin_when_uniqie_False Hnode Hin H0).
        intros. move : (Hcnct e'); clear. apply contra_not. intro; simpl. rewrite H orb_true_r //.
        intros. apply (Hinvalid v'). simpl. rewrite H orb_true_r //.
  clear eval_hfstmt_for_unique_node.
  intros rs0 ns0 Hfind rs ns Heval. induction s as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|cond ss_true ss_false]; intros; simpl in Heval; try done.
  move /andP : H => [Hv He]; move /eqP : Hv => Hv; move /eqP : He => He; subst v; subst e. destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate.
    inversion Heval; subst rs ns. rewrite PVM.Lemmas.find_add_eq //. apply PVM.M.SE.eq_refl.
  destruct (Sem_HiFP.eval_hfexpr cond init_s tmap) as [valc|] eqn : Hcond; try discriminate. move : H => [Hunique_true [Hunique_false Hin]].
  destruct (~~ is_zero valc). 
  1,2 : move : Heval; apply (eval_hfstmts_for_unique_node_helper _ _ _ _ _ Hin); try done.
Admitted.

Lemma eval_hfstmts_for_unique_node ss v e init_s tmap : Qin_with_cond (Snode v e) ss init_s tmap -> unique_node_dclr_when ss -> 
  forall rs s, Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
  PVM.find v s = Sem_HiFP.eval_hfexpr e init_s tmap.
Proof.
  intro. intro. apply eval_hfstmts_for_unique_node_helper; try done.
Qed.

Lemma eval_hfstmt_find_eq2find_eq temp_rs temp_s temp_rs' temp_s' init_s tmap rs' s' rs s stmt v : 
  Sem_HiFP.eval_hfstmt stmt temp_rs temp_s init_s tmap = Some (rs, s) ->
  Sem_HiFP.eval_hfstmt stmt temp_rs' temp_s' init_s tmap = Some (rs', s') ->
  (PVM.find v temp_rs' = PVM.find v temp_rs -> PVM.find v rs' = PVM.find v rs) /\
  (PVM.find v temp_s' = PVM.find v temp_s -> PVM.find v s' = PVM.find v s)
with eval_hfstmts_find_eq2find_eq temp_rs temp_s temp_rs' temp_s' init_s tmap rs' s' rs s connect_stmts v : 
  Sem_HiFP.eval_hfstmts connect_stmts temp_rs temp_s init_s tmap = Some (rs, s) ->
  Sem_HiFP.eval_hfstmts connect_stmts temp_rs' temp_s' init_s tmap = Some (rs', s') ->
  (PVM.find v temp_rs' = PVM.find v temp_rs -> PVM.find v rs' = PVM.find v rs) /\
  (PVM.find v temp_s' = PVM.find v temp_s -> PVM.find v s' = PVM.find v s).
Proof.
  clear eval_hfstmt_find_eq2find_eq.
  destruct stmt as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt.
  - (* skip, wire, mem, inst *)
    1,2,4,5 : simpl; intros; inversion H; inversion H0; subst rs s rs' s'; split; try done.
  - (* reg *)
    simpl; intros. destruct (PVM.find v0 init_s) as [val|]; try discriminate.
    inversion H; inversion H0; subst rs s rs' s'. split; try done. destruct (v == v0) eqn : Heq.
    move /eqP : Heq => Heq; subst v. rewrite PVM.Lemmas.find_add_eq. rewrite PVM.Lemmas.find_add_eq //. 1,2 : apply PVM.M.SE.eq_refl.
    rewrite PVM.Lemmas.find_add_neq. rewrite PVM.Lemmas.find_add_neq. try done. 
    1,2 : unfold PVM.M.SE.eq; rewrite Heq //. 
  - (* node *)
    simpl; intros. destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap) as [val|]; try discriminate.
    inversion H; inversion H0; subst rs s rs' s'. split; try done. destruct (v == v0) eqn : Heq.
    move /eqP : Heq => Heq; subst v. rewrite PVM.Lemmas.find_add_eq. rewrite PVM.Lemmas.find_add_eq //. 1,2 : apply PVM.M.SE.eq_refl.
    rewrite PVM.Lemmas.find_add_neq. rewrite PVM.Lemmas.find_add_neq. try done. 
    1,2 : unfold PVM.M.SE.eq; rewrite Heq //. 
  - (* cnct *)
    simpl; intros. destruct v0; try (inversion H; inversion H0; subst rs s rs' s'; split; try done).
    destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate. destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate;
    inversion H; inversion H0; subst rs s rs' s'; clear H H0; try (split; try done).
    1-8 : destruct (v == s0) eqn : Heq.
    1,3,5,7,9,11,13,15 : move /eqP : Heq => Heq; subst v; rewrite PVM.Lemmas.find_add_eq; try apply PVM.M.SE.eq_refl; rewrite PVM.Lemmas.find_add_eq //; try apply PVM.M.SE.eq_refl.
    1-8 : rewrite PVM.Lemmas.find_add_neq; unfold PVM.M.SE.eq; try rewrite Heq; try done; rewrite PVM.Lemmas.find_add_neq; unfold PVM.M.SE.eq; try rewrite Heq; try done.
  - (* invalid *)
    simpl; intros. destruct v0; try (inversion H; inversion H0; subst rs s rs' s'; split; try done).
    destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate. destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val);
    inversion H; inversion H0; subst rs s rs' s'; clear H H0; try (split; try done).
    1-16 : destruct (v == s0) eqn : Heq.
    1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31 : move /eqP : Heq => Heq; subst v; rewrite PVM.Lemmas.find_add_eq; try apply PVM.M.SE.eq_refl; rewrite PVM.Lemmas.find_add_eq //; try apply PVM.M.SE.eq_refl.
    1-16 : rewrite PVM.Lemmas.find_add_neq; unfold PVM.M.SE.eq; try rewrite Heq; try done; rewrite PVM.Lemmas.find_add_neq; unfold PVM.M.SE.eq; try rewrite Heq; try done.
  - (* when *)
    simpl; intros. destruct (Sem_HiFP.eval_hfexpr c init_s tmap); try discriminate. destruct (~~ is_zero b).
    1,2 : move : H H0; apply eval_hfstmts_find_eq2find_eq.

  clear eval_hfstmts_find_eq2find_eq.
  move : connect_stmts temp_rs temp_s temp_rs' temp_s'. elim. simpl. intros. inversion H; inversion H0. subst rs s rs' s'. split; try done.
  intros hd tl IH. simpl; intros temp_rs temp_s temp_rs' temp_s' Hevals Hevals'.
  destruct (Sem_HiFP.eval_hfstmt hd temp_rs temp_s init_s tmap) as [[rs0 ns0]|] eqn : Heval; try discriminate.
  destruct (Sem_HiFP.eval_hfstmt hd temp_rs' temp_s' init_s tmap) as [[rs'0 ns'0]|] eqn : Heval'; try discriminate.
  apply (IH _ _ _ _ Hevals) in Hevals'. move : Hevals' => [Hrs Hns]. clear IH Hevals. 
  specialize (eval_hfstmt_find_eq2find_eq _ _ _ _ _ _ _ _ _ _ _ v Heval Heval') as Hhelper. move : Hhelper => [Hhelper1 Hhelper2].
  split.
  intros; apply Hrs. apply Hhelper1; done.
  intros; apply Hns. apply Hhelper2; done.
Qed.

Lemma eval_hfstmts_for_comb_only_cnct init_s tmap v component_stmts connect_stmts:
  (forall s, Qin s component_stmts -> is_declaration s) ->
  match PVM.find v tmap with
  | Some (gt, Out_port) => (forall v' e', Qin (Snode v' e') component_stmts -> v <> v') -> 
      (forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat component_stmts connect_stmts)) ->
      forall rs s, Sem_HiFP.eval_hfstmts (Qcat component_stmts connect_stmts) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
      forall rs' s', Sem_HiFP.eval_hfstmts connect_stmts (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs', s') -> PVM.find v s' = PVM.find v s
  | Some (gt, Wire) => (forall v' e', Qin (Snode v' e') component_stmts -> v <> v') -> 
      (forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat component_stmts connect_stmts)) ->
      forall rs s, Sem_HiFP.eval_hfstmts (Qcat component_stmts connect_stmts) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
      forall rs' s', Sem_HiFP.eval_hfstmts connect_stmts (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs', s') -> PVM.find v s' = PVM.find v s
  | _ => True
  end.
Proof.
  intro Hdclr. destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt; try done. destruct cmpnt; try done.
  (* outport *) 
  assert (Hhelper : forall temp_rs temp_s rs s : PVM.t bits,
    (forall v' e', Qin (Snode v' e') component_stmts -> v <> v') ->
    (forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat component_stmts connect_stmts)) ->
    Sem_HiFP.eval_hfstmts (Qcat component_stmts connect_stmts)
    temp_rs temp_s init_s tmap = 
    Some (rs, s) ->
    forall temp_rs' temp_s' rs' s' : PVM.t bits,
    PVM.find v temp_s' = PVM.find v temp_s ->
    Sem_HiFP.eval_hfstmts connect_stmts temp_rs' temp_s' init_s tmap = Some (rs', s') ->
    PVM.find v s' = PVM.find v s). {
    move : component_stmts Hdclr. elim.
    intros Hdclr temp_rs temp_s rs s Hneq Hwhen Heval temp_rs' temp_s' rs' s' Htemp Heval'. simpl in Heval. apply (eval_hfstmts_find_eq2find_eq v Heval) in Heval'.
      move : Heval' => [_ Heval']. apply Heval'; done.
    intros st ss IH Hdclr temp_rs temp_s rs s Hneq Hwhen Heval temp_rs' temp_s' rs' s' Htemp Heval'. simpl in Heval.
    case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st; simpl in Heval.
    1,2,4,5 : move : Heval temp_rs' temp_s' rs' s' Htemp Heval'; apply IH. 
    1,4,7,10 : intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    1,3,5,7 : intros; apply (Hneq v' e'); simpl; done.
    1-4 : intros; specialize (Hwhen c ss1 ss2); move : Hwhen; apply contra_not; intro; try done.
    (* reg *)
    destruct (PVM.find var init_s); try discriminate.
    move : Heval temp_rs' temp_s' rs' s' Htemp Heval'; apply IH. intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    intros; apply (Hneq v' e'); simpl; done.
    intros; specialize (Hwhen c ss1 ss2); move : Hwhen; apply contra_not; intro; try done.
    (* node *)
    destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate.
    move : Heval'; apply IH with (temp_rs := temp_rs) (temp_s := PVM.add var b temp_s) (rs := rs); try done. intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    intros; apply (Hneq v' e'); simpl; rewrite H orb_true_r; done.
    rewrite Htemp HiFP.PCELemmas.find_add_neq //. assert (v <> var). specialize (Hneq var node_e). apply Hneq. simpl. rewrite eq_refl. rewrite eq_refl. simpl; done.
    unfold PVM.M.SE.eq. move : H; apply contra_not. intro. move /eqP : H => H. done.
    (* cnct *)
    assert (Qin (Sfcnct ref e) (Qcons (Sfcnct ref e) ss)). simpl. rewrite eq_refl. rewrite eq_refl //. apply Hdclr in H. simpl in H. done.
    (* invalid *)
    assert (Qin (Sinvalid ref) (Qcons (Sinvalid ref) ss)). simpl. rewrite eq_refl //. apply Hdclr in H. simpl in H. done.
    (* when *)
    specialize (Hwhen cond ss_true ss_false). simpl in Hwhen. rewrite eq_refl in Hwhen; simpl in Hwhen. 
    specialize (hfstmt_seq_eqn_refl ss_true) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_true ss_true) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq in Hwhen; simpl in Hwhen. clear Heq Heq'.
    specialize (hfstmt_seq_eqn_refl ss_false) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_false ss_false) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq in Hwhen; simpl in Hwhen. done.
    }
  intros. move : H2. apply (Hhelper _ _ _ _ H H0 H1). done.
  (* wire *)
  assert (Hhelper : forall temp_rs temp_s rs s : PVM.t bits,
    (forall v' e', Qin (Snode v' e') component_stmts -> v <> v') ->
    (forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat component_stmts connect_stmts)) ->
    Sem_HiFP.eval_hfstmts (Qcat component_stmts connect_stmts)
    temp_rs temp_s init_s tmap = 
    Some (rs, s) ->
    forall temp_rs' temp_s' rs' s' : PVM.t bits,
    PVM.find v temp_s' = PVM.find v temp_s ->
    Sem_HiFP.eval_hfstmts connect_stmts temp_rs' temp_s' init_s tmap = Some (rs', s') ->
    PVM.find v s' = PVM.find v s). {
    move : component_stmts Hdclr. elim.
    intros Hdclr temp_rs temp_s rs s Hneq Hwhen Heval temp_rs' temp_s' rs' s' Htemp Heval'. simpl in Heval. apply (eval_hfstmts_find_eq2find_eq v Heval) in Heval'.
      move : Heval' => [_ Heval']. apply Heval'; done.
    intros st ss IH Hdclr temp_rs temp_s rs s Hneq Hwhen Heval temp_rs' temp_s' rs' s' Htemp Heval'. simpl in Heval.
    case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st; simpl in Heval.
    1,2,4,5 : move : Heval temp_rs' temp_s' rs' s' Htemp Heval'; apply IH. 
    1,4,7,10 : intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    1,3,5,7 : intros; apply (Hneq v' e'); simpl; done.
    1-4 : intros; specialize (Hwhen c ss1 ss2); move : Hwhen; apply contra_not; intro; try done.
    (* reg *)
    destruct (PVM.find var init_s); try discriminate.
    move : Heval temp_rs' temp_s' rs' s' Htemp Heval'; apply IH. intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    intros; apply (Hneq v' e'); simpl; done.
    intros; specialize (Hwhen c ss1 ss2); move : Hwhen; apply contra_not; intro; try done.
    (* node *)
    destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate.
    move : Heval'; apply IH with (temp_rs := temp_rs) (temp_s := PVM.add var b temp_s) (rs := rs); try done. intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    intros; apply (Hneq v' e'); simpl; rewrite H orb_true_r; done.
    rewrite Htemp HiFP.PCELemmas.find_add_neq //. assert (v <> var). specialize (Hneq var node_e). apply Hneq. simpl. rewrite eq_refl. rewrite eq_refl. simpl; done.
    unfold PVM.M.SE.eq. move : H; apply contra_not. intro. move /eqP : H => H. done.
    (* cnct *)
    assert (Qin (Sfcnct ref e) (Qcons (Sfcnct ref e) ss)). simpl. rewrite eq_refl. rewrite eq_refl //. apply Hdclr in H. simpl in H. done.
    (* invalid *)
    assert (Qin (Sinvalid ref) (Qcons (Sinvalid ref) ss)). simpl. rewrite eq_refl //. apply Hdclr in H. simpl in H. done.
    (* when *)
    specialize (Hwhen cond ss_true ss_false). simpl in Hwhen. rewrite eq_refl in Hwhen; simpl in Hwhen. 
    specialize (hfstmt_seq_eqn_refl ss_true) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_true ss_true) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq in Hwhen; simpl in Hwhen. clear Heq Heq'.
    specialize (hfstmt_seq_eqn_refl ss_false) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_false ss_false) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq in Hwhen; simpl in Hwhen. done.
    }
  intros. move : H2. apply (Hhelper _ _ _ _ H H0 H1). done.
Qed.

Lemma eval_hfstmts_Qcat_exists s0 rs0 init_s tmap rs s l1 l2 : Sem_HiFP.eval_hfstmts (Qcat l1 l2) rs0 s0 init_s tmap = Some (rs, s)
  -> exists temp_s temp_rs, Sem_HiFP.eval_hfstmts l1 rs0 s0 init_s tmap = Some (temp_rs, temp_s) /\  Sem_HiFP.eval_hfstmts l2 temp_rs temp_s init_s tmap = Some (rs, s).
Proof.
  move : l1 s0 rs0. elim. simpl. intros. exists s0; exists rs0. split; simpl; try done.
  intros hd tl IH s0 rs0 Heval; simpl. simpl in Heval. destruct (Sem_HiFP.eval_hfstmt hd rs0 s0 init_s tmap) as [[rs1 s1]|]; try discriminate.
  apply IH in Heval. done.
Qed.

Lemma eval_hfstmt_exists s rs0 ns0 init_s tmap rs ns : Sem_HiFP.eval_hfstmt s rs0 ns0 init_s tmap = Some (rs, ns) ->
  forall rs1 ns1, exists rs' ns', Sem_HiFP.eval_hfstmt s rs1 ns1 init_s tmap = Some (rs', ns')
with eval_hfstmts_exists ss rs0 ns0 init_s tmap rs ns : Sem_HiFP.eval_hfstmts ss rs0 ns0 init_s tmap = Some (rs, ns) ->
  forall rs1 ns1, exists rs' ns', Sem_HiFP.eval_hfstmts ss rs1 ns1 init_s tmap = Some (rs', ns').
Proof.
  clear eval_hfstmt_exists.
  destruct s as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt; subst s; simpl; intros Heval rs1 ns1.
  1,2,4,5 : exists rs1; exists ns1; done.
  (* reg *)
  destruct (PVM.find v0 init_s); try discriminate.
  exists (PVM.add v0 b rs1); exists ns1; done.
  (* node *)
  destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate.
  exists rs1; exists (PVM.add v0 b ns1); done.
  (* cnct *)
  destruct v0; try (exists rs1; exists ns1; done).
  destruct (PVM.find s tmap) as [[gt cmpnt]|]; try discriminate.
  destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate.
  6 : exists (PVM.add s b rs1); exists ns1; done.
  1-7 : exists rs1; exists (PVM.add s b ns1); done.
  (* invalid *)
  destruct v0; try (exists rs1; exists ns1; done).
  destruct (PVM.find s tmap) as [[gt cmpnt]|]; try discriminate.
  destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val).
  1,3,5,7,9,13,15 : exists rs1; exists (PVM.add s (take (sizeof_fgtyp gt) indeterminate_val) ns1); try done.
  6 : exists (PVM.add s (take (sizeof_fgtyp gt) indeterminate_val) rs1); exists ns1; done.
  6 : exists (PVM.add s (zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val) rs1); exists ns1; done.
  1-7 : exists rs1; exists (PVM.add s (zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val) ns1); done.
  (* when *)
  destruct (Sem_HiFP.eval_hfexpr c init_s tmap); try discriminate.
  destruct ( ~~ is_zero b). move : Heval rs1 ns1; apply eval_hfstmts_exists.
  move : Heval rs1 ns1; apply eval_hfstmts_exists.

  clear eval_hfstmts_exists. move : ss rs0 ns0. elim.
  simpl; intros. exists rs1; exists ns1; done.
  simpl; intros hd tl IH rs0 ns0 Hevals; intros. destruct (Sem_HiFP.eval_hfstmt hd rs0 ns0 init_s tmap) as [[rs0' ns0']|] eqn : Heval; try discriminate.
  specialize (eval_hfstmt_exists _ _ _ _ _ _ _ Heval rs1 ns1). destruct eval_hfstmt_exists as [rs' [ns' Hexists]].
  rewrite Hexists. apply (IH _ _ Hevals).
Qed.

Lemma eval_hfstmt_cnct_no_order s1 s2 rs0 ns0 rs1 ns1 rs2 ns2 init_s tmap rs ns rs' ns' : 
  match s1, s2 with
  | Sinvalid v1, Sinvalid v2 
  | Sinvalid v1, Sfcnct v2 _
  | Sfcnct v1 _, Sinvalid v2
  | Sfcnct v1 _, Sfcnct v2 _ => v1 <> v2
  | _, _ => False
  end ->
  Sem_HiFP.eval_hfstmt s1 rs0 ns0 init_s tmap = Some (rs1, ns1) -> Sem_HiFP.eval_hfstmt s2 rs1 ns1 init_s tmap = Some (rs, ns) -> 
  Sem_HiFP.eval_hfstmt s2 rs0 ns0 init_s tmap = Some (rs2, ns2) -> Sem_HiFP.eval_hfstmt s1 rs2 ns2 init_s tmap = Some (rs', ns') -> 
  forall v : PVM.key, PVM.find v rs' = PVM.find v rs /\ PVM.find v ns' = PVM.find v ns.
Proof.
  intros Hneq. 
  case Hs1 : s1 => [||||||v1 e1|v1|c1 true_ss1 false_ss1]; subst s1; try done;
  case Hs2 : s2 => [||||||v2 e2|v2|c2 true_ss2 false_ss2]; subst s2; try done; simpl in *; intros Heval11 Heval12 Heval21 Heval22 v.
  destruct v1; destruct v2; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done).
  assert (Hneq' : ~ PVM.SE.eq s s0) by (move : Hneq; apply contra_not; intro; unfold PVM.SE.eq in H; move /eqP : H => H; subst s; done).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate; destruct (PVM.find s0 tmap) as [[gt1 cmpnt1]|]; try discriminate.
    destruct cmpnt0; destruct cmpnt1; destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
    36 : specialize (CEP.Lemmas.add_comm b b0 rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
    1-49 : specialize (CEP.Lemmas.add_comm b b0 ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0;destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s0 tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  
  destruct v1; destruct v2; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done).
  assert (Hneq' : ~ PVM.SE.eq s s0) by (move : Hneq; apply contra_not; intro; unfold PVM.SE.eq in H; move /eqP : H => H; subst s; done).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate; destruct (PVM.find s0 tmap) as [[gt1 cmpnt1]|]; try discriminate.
    destruct cmpnt0; destruct cmpnt1; destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); destruct (sizeof_fgtyp gt1 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done));
    try (specialize (CEP.Lemmas.add_comm b (take (sizeof_fgtyp gt1) indeterminate_val) ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm));
    try (specialize (CEP.Lemmas.add_comm b (zext (sizeof_fgtyp gt1 - length indeterminate_val) indeterminate_val) ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm)).
    specialize (CEP.Lemmas.add_comm b (take (sizeof_fgtyp gt1) indeterminate_val) rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
    specialize (CEP.Lemmas.add_comm b (zext (sizeof_fgtyp gt1 - length indeterminate_val) indeterminate_val) rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0;destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s0 tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  
  destruct v1; destruct v2; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done).
  assert (Hneq' : ~ PVM.SE.eq s s0) by (move : Hneq; apply contra_not; intro; unfold PVM.SE.eq in H; move /eqP : H => H; subst s; done).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate; destruct (PVM.find s0 tmap) as [[gt1 cmpnt1]|]; try discriminate.
    destruct cmpnt0; destruct cmpnt1; destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done));
    try (specialize (CEP.Lemmas.add_comm (take (sizeof_fgtyp gt0) indeterminate_val) b ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm));
    try (specialize (CEP.Lemmas.add_comm (zext (sizeof_fgtyp gt0 - length indeterminate_val) indeterminate_val) b ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm)).
    specialize (CEP.Lemmas.add_comm (take (sizeof_fgtyp gt0) indeterminate_val) b rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
    specialize (CEP.Lemmas.add_comm (zext (sizeof_fgtyp gt0 - length indeterminate_val) indeterminate_val) b rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s0 tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0;destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  
  destruct v1; destruct v2; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done).
  assert (Hneq' : ~ PVM.SE.eq s s0) by (move : Hneq; apply contra_not; intro; unfold PVM.SE.eq in H; move /eqP : H => H; subst s; done).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate; destruct (PVM.find s0 tmap) as [[gt1 cmpnt1]|]; try discriminate.
    destruct cmpnt0; destruct cmpnt1; destruct (sizeof_fgtyp gt1 < length indeterminate_val); destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done));
    try (specialize (CEP.Lemmas.add_comm (take (sizeof_fgtyp gt0) indeterminate_val) (take (sizeof_fgtyp gt1) indeterminate_val) ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm));
    try (specialize (CEP.Lemmas.add_comm (zext (sizeof_fgtyp gt0 - length indeterminate_val) indeterminate_val) (take (sizeof_fgtyp gt1) indeterminate_val) ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm));
    try (specialize (CEP.Lemmas.add_comm (take (sizeof_fgtyp gt0) indeterminate_val) (zext (sizeof_fgtyp gt1 - length indeterminate_val) indeterminate_val) ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm));
    try (specialize (CEP.Lemmas.add_comm (zext (sizeof_fgtyp gt0 - length indeterminate_val) indeterminate_val) (zext (sizeof_fgtyp gt1 - length indeterminate_val) indeterminate_val) ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm)).
    specialize (CEP.Lemmas.add_comm (take (sizeof_fgtyp gt0) indeterminate_val) (take (sizeof_fgtyp gt1) indeterminate_val) rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
    specialize (CEP.Lemmas.add_comm (zext (sizeof_fgtyp gt0 - length indeterminate_val) indeterminate_val) (take (sizeof_fgtyp gt1) indeterminate_val) rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
    specialize (CEP.Lemmas.add_comm (take (sizeof_fgtyp gt0) indeterminate_val) (zext (sizeof_fgtyp gt1 - length indeterminate_val) indeterminate_val) rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
    specialize (CEP.Lemmas.add_comm (zext (sizeof_fgtyp gt0 - length indeterminate_val) indeterminate_val) (zext (sizeof_fgtyp gt1 - length indeterminate_val) indeterminate_val) rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s0 tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0;destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
Qed.

Definition unique_connect_stmts (ss : HiFP.hfstmt_seq) : Prop :=
  (forall v e, Qin (Sfcnct v e) ss -> (forall e', ~ Qin (Sfcnct v e') (Qremove (Sfcnct v e) ss)) /\ (~ Qin (Sinvalid v) (Qremove (Sfcnct v e) ss))) /\
  (forall v, Qin (Sinvalid v) ss -> (forall e', ~ Qin (Sfcnct v e') (Qremove (Sinvalid v) ss)) /\ (~ Qin (Sinvalid v) (Qremove (Sinvalid v) ss))).

Lemma eval_hfstmts_cnct_no_order connect_stmts rs0 ns0 init_s tmap rs ns : 
  Sem_HiFP.eval_hfstmts connect_stmts rs0 ns0 init_s tmap = Some (rs, ns) ->
  (forall s, Qin s connect_stmts -> is_connection s) ->
  unique_connect_stmts connect_stmts ->
  forall s, Qin s connect_stmts -> 
  exists rs' ns', Sem_HiFP.eval_hfstmts (Qcons s (Qremove s connect_stmts)) rs0 ns0 init_s tmap = Some (rs', ns') /\
  forall v, PVM.find v rs' = PVM.find v rs /\ PVM.find v ns' = PVM.find v ns.
Proof.
  move : connect_stmts rs0 ns0. elim. 
  simpl; intros; done.
  intros hd tl IH. simpl; intros rs0 ns0 Hevals His Hunique s Hin.
  destruct (Sem_HiFP.eval_hfstmt hd rs0 ns0 init_s tmap) as [[rs1 ns1]|] eqn : Heval; try discriminate. destruct (hfstmt_eqn hd s) eqn : Heqs.
  - (* eq s *)
    clear Hin IH. assert (hd = s).  specialize (hfstmt_eqP hd s) as Heq'. apply reflect_iff in Heq'. apply Heq' in Heqs. done.
    subst hd. clear Heqs. rewrite Heval. exists rs; exists ns. rewrite Hevals. split; try done.
  - (* in *)
    rewrite orb_false_l in Hin. 
    assert (His_hd : is_connection hd). apply His. specialize (hfstmt_eqn_refl hd) as Heq. move/eqP : Heq => Heq. 
      specialize (hfstmt_eqP hd hd) as Heq'. apply reflect_iff in Heq'. apply Heq' in Heq. rewrite Heq orb_true_l //.
    assert (His_s : is_connection s). apply His. rewrite Hin orb_true_r //. generalize Hin; intro Heq.
    apply (IH _ _ Hevals) in Heq. clear IH. destruct Heq as [rs' [ns' [Hevals' Heq]]]. simpl in Hevals'.
    destruct (Sem_HiFP.eval_hfstmt s rs1 ns1 init_s tmap) as [[rs2 ns2]|] eqn : Heval_s; try discriminate.
    specialize (eval_hfstmt_exists Heval_s rs0 ns0) as Heval3. destruct Heval3 as [rs3 [ns3 Heval3]]. rewrite Heval3. simpl.
    specialize (eval_hfstmt_exists Heval rs3 ns3) as Heval4. destruct Heval4 as [rs4 [ns4 Heval4]]. rewrite Heval4. 
    specialize (eval_hfstmts_exists Hevals' rs4 ns4) as Hexists. destruct Hexists as [rs'0 [ns'0 Hevals'0]]. 
    rewrite Hevals'0; exists rs'0; exists ns'0. split; try done. intro. specialize (Heq v). destruct Heq as [Heq0 Heq1].
    rewrite -Heq0 -Heq1; clear Heq0 Heq1 Hevals rs ns. 
    specialize (eval_hfstmts_find_eq2find_eq v Hevals' Hevals'0) as Hfindeq. move : Hfindeq => [Hfindeq0 Hfindeq1].
    assert (Hhelper : match hd, s with
      | Sinvalid v1, Sinvalid v2 
      | Sinvalid v1, Sfcnct v2 _
      | Sfcnct v1 _, Sinvalid v2
      | Sfcnct v1 _, Sfcnct v2 _ => v1 <> v2
      | _, _ => False
      end). {
      move : His_hd His_s Hunique Hin; clear; unfold unique_connect_stmts; intros. destruct hd eqn : Hhd; destruct s eqn : Hs; simpl in *; try done.
      - (* cnct cnct *)
        move : Hunique => [Hunique _]. assert ((h == h) && (h0 == h0) || Qin (Sfcnct h h0) tl). rewrite eq_refl; rewrite eq_refl; simpl; done.
        apply Hunique in H; clear Hunique. move : H => [H _]. rewrite eq_refl in H; rewrite eq_refl in H; simpl in H. move : (H h2); apply contra_not.
        intro; subst h; done.
      - (* cnct invalid *)
        move : Hunique => [Hunique _]. assert ((h == h) && (h0 == h0) || Qin (Sfcnct h h0) tl). rewrite eq_refl; rewrite eq_refl; simpl; done.
        apply Hunique in H; clear Hunique. move : H => [_ H]. rewrite eq_refl in H; rewrite eq_refl in H; simpl in H. move : H; apply contra_not.
        intro; subst h; done.
      - (* invalid cnct *)
        move : Hunique => [_ Hunique]. assert ((h == h) || Qin (Sinvalid h) tl). rewrite eq_refl; simpl; done.
        apply Hunique in H; clear Hunique. move : H => [H _]. rewrite eq_refl in H; simpl in H. move : (H h1); apply contra_not.
        intro; subst h; done.
      - (* invalid invalid *)
        move : Hunique => [_ Hunique]. assert ((h == h) || Qin (Sinvalid h) tl). rewrite eq_refl; simpl; done.
        apply Hunique in H; clear Hunique. move : H => [_ H]. rewrite eq_refl in H; simpl in H. move : H; apply contra_not.
        intro; subst h; done.
      }
    specialize (eval_hfstmt_cnct_no_order Hhelper Heval Heval_s Heval3 Heval4 v) as Hfindeq. move : Hfindeq => [Hfindeq Hfindeq'].
    split; try (apply Hfindeq0; done); try (apply Hfindeq1; done).
    intros; apply His. rewrite H orb_true_r //.
    move : Hunique; clear; unfold unique_connect_stmts; intros. move : Hunique => [Hunique0 Hunique1]. split; intros.
    - (* no cnct *) 
      assert (Qin (Sfcnct v e) (Qcons hd tl)). simpl. rewrite H orb_true_r //. apply Hunique0 in H0. move : H0 => [H0 H1].
      split. intros. move : (H0 e'). apply contra_not. clear; simpl; intros. 
      destruct (hfstmt_eqn hd (Sfcnct v e)). move : H; apply in_qremove. simpl; rewrite H orb_true_r //.
      move : H1; apply contra_not. clear; simpl; intros. 
      destruct (hfstmt_eqn hd (Sfcnct v e)). move : H; apply in_qremove. simpl; rewrite H orb_true_r //.
    - (* no invalid *)
      assert (Qin (Sinvalid v) (Qcons hd tl)). simpl. rewrite H orb_true_r //. apply Hunique1 in H0. move : H0 => [H0 H1].
      split. intros. move : (H0 e'). apply contra_not. clear; simpl; intros. 
      destruct (hfstmt_eqn hd (Sinvalid v)). move : H; apply in_qremove. simpl; rewrite H orb_true_r //.
      move : H1; apply contra_not. clear; simpl; intros. 
      destruct (hfstmt_eqn hd (Sinvalid v)). move : H; apply in_qremove. simpl; rewrite H orb_true_r //.
Qed.

Lemma unique_connect_stmts_convert_to_connect_stmt ss (v : ProdVarOrder.t) d_expr: 
  (~ Qin (Sinvalid (Eid v)) ss /\ forall e, ~ Qin (Sfcnct (Eid v) e) ss) ->
  unique_connect_stmts ss -> unique_connect_stmts (convert_to_connect_stmt v d_expr ss).
Proof.
  intros [Hnot_invalid Hnot_cnct] Hss; unfold unique_connect_stmts in *. move : Hss => [Hcnct Hinvalid]. split.
  - (* cnct in *)
    intros v0 e0 Hin. destruct d_expr as [gt|de]; simpl in *. 
    * specialize (Hnot_cnct e0). destruct (Eid v == v0) eqn : Hneq. move /eqP : Hneq => Hneq; subst v0; done.
      apply Hcnct in Hin as Hcnct'; clear Hcnct. move : Hcnct' => [Hcnct' Hinvalid']; split; try done.
    * destruct (Eid v == v0) eqn : Hneq. move /eqP : Hneq => Hneq; subst v0. simpl in *. destruct (de == e0) eqn : Heqe.
      + (* eq v, eq e *)
        move /eqP : Heqe => Heqe; subst de; clear Hin. split; try done.
      + (* eq v, neq e *)
        rewrite orb_false_l in Hin. specialize (Hnot_cnct e0); done.
      + (* neqv *)
        simpl in *. rewrite Hneq. simpl. apply Hcnct; done.
  - (* invalid in *) 
    intros v0 Hin. destruct d_expr as [gt|de]; simpl in *. 
    * destruct (Eid v == v0) eqn : Hneq. move /eqP : Hneq => Hneq; subst v0; done.
      rewrite orb_false_l in Hin. simpl. rewrite Hneq; simpl.
      apply Hinvalid in Hin as Hinvalid'; clear Hinvalid. move : Hinvalid' => [Hcnct' Hinvalid']; split; try done.
    * destruct (Eid v == v0) eqn : Hneq. move /eqP : Hneq => Hneq; subst v0; done. simpl in *.
      apply Hinvalid; done.
Qed.

Lemma qin_convert_to_connect_stmt_invalid v0 ss v d_expr : v <> v0 -> Qin (Sinvalid (Eid v0)) (convert_to_connect_stmt v d_expr ss) -> Qin (Sinvalid (Eid v0)) ss.
Proof.
  destruct d_expr; simpl; try done.
  intros. destruct (Eid v == Eid v0) eqn : Heq. move /eqP : Heq => Heq. inversion Heq; subst v; done.
  rewrite orb_false_l in H0; done. 
Qed.

Lemma qin_convert_to_connect_stmt_cnct v0 e0 ss v d_expr : v <> v0 -> Qin (Sfcnct (Eid v0) e0) (convert_to_connect_stmt v d_expr ss) -> Qin (Sfcnct (Eid v0) e0) ss.
Proof.
  destruct d_expr; simpl; try done.
  intros. destruct (Eid v == Eid v0) eqn : Heq. move /eqP : Heq => Heq. inversion Heq; subst v; done.
  rewrite orb_false_l in H0; done. 
Qed.

Lemma convert_to_connect_stmts_unique_connect_stmts conn_map : unique_connect_stmts (convert_to_connect_stmts conn_map).
Proof.
  unfold convert_to_connect_stmts.
  rewrite PVM.M.fold_1.
  specialize (PVM.elements_3w conn_map) as Hnodup.
  remember (PVM.M.elements conn_map) as elements. 
  assert (Hhelper : forall res, unique_connect_stmts res -> 
    (forall p, In p elements -> ~ Qin (Sinvalid (Eid (fst p))) res /\ forall e, ~ Qin (Sfcnct (Eid (fst p)) e) res) ->
    unique_connect_stmts (fold_left
    (fun (a : HiFP.hfstmt_seq) (p : PVM.M.key * def_expr) =>
    convert_to_connect_stmt (fst p) (snd p) a) elements 
    res)). { clear Heqelements; move : elements Hnodup.
    elim. simpl; done. 
    simpl; intros hd tl IH Hnodup res Hres Hnotin. apply IH; clear IH. 
    assert (hd :: tl = nil ++ (hd :: tl)) by (simpl; done). rewrite H in Hnodup. apply NoDupA_split in Hnodup. simpl in Hnodup; done.
    apply unique_connect_stmts_convert_to_connect_stmt; try done.
    apply Hnotin. left; done.
    (* hypo *)
    intros. assert (hd = p \/ In p tl) by (right; done). specialize (Hnotin _ H0). clear H0.
    move : Hnotin => [Hnot_invalid Hnot_cnct]; split.
    move : Hnot_invalid; apply contra_not. apply qin_convert_to_connect_stmt_invalid. destruct hd as [hd_v hd_e]; simpl.
      assert ((hd_v, hd_e) :: tl = nil ++ (hd_v, hd_e) :: tl) by (simpl; done). rewrite H0 in Hnodup; clear H0. 
      specialize (NoDupA_notin Hnodup) as [_ Hnotin]. move : Hnotin; apply contra_not. intro; subst hd_v.
      apply in_split_l; done.
    intro. move : (Hnot_cnct e); apply contra_not. apply qin_convert_to_connect_stmt_cnct. destruct hd as [hd_v hd_e]; simpl.
      assert ((hd_v, hd_e) :: tl = nil ++ (hd_v, hd_e) :: tl) by (simpl; done). rewrite H0 in Hnodup; clear H0. 
      specialize (NoDupA_notin Hnodup) as [_ Hnotin]. move : Hnotin; apply contra_not. intro; subst hd_v.
      apply in_split_l; done.
  }
  apply Hhelper. unfold unique_connect_stmts.
  split; simpl; try done. intros; split; try done.
Qed.

Lemma eval_hfstmts_for_sequ_only_cnct v tmap ss init_s conn_map : 
  (forall s, Qin s (component_stmts_of ss) -> is_declaration s) ->
  match PVM.find v tmap with
  | Some (gt, Register) => ExpandBranches_funs ss (PVM.empty def_expr) tmap = Some conn_map -> 
      Qin (Sfcnct (Eid v) (Eref (Eid v))) (convert_to_connect_stmts conn_map) \/
        (exists e : hfexpr ProdVarOrder.T, Qin (Sfcnct (Eid v) e) (convert_to_connect_stmts conn_map)) ->
      forall rs s, Sem_HiFP.eval_hfstmts (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map)) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
      forall rs' s', Sem_HiFP.eval_hfstmts (convert_to_connect_stmts conn_map) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs', s') -> PVM.find v rs' = PVM.find v rs
  | _ => True
  end.
Proof.
  intro Hdclr. destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt; try done. destruct cmpnt; try done.
  assert (Hhelper : forall connect_stmts component_stmts, 
    (forall s, Qin s component_stmts -> is_declaration s) ->
    (forall s, Qin s connect_stmts -> is_connection s) -> 
    (Qin (Sfcnct (Eid v) (Eref (Eid v))) connect_stmts \/ exists e, Qin (Sfcnct (Eid v) e) connect_stmts) -> 
    unique_connect_stmts connect_stmts ->
    forall temp_rs temp_s rs s : PVM.t bits,
    Sem_HiFP.eval_hfstmts (Qcat component_stmts connect_stmts)
    temp_rs temp_s init_s tmap = Some (rs, s) ->
    forall temp_rs' temp_s' rs' s' : PVM.t bits,
    PVM.find v temp_rs' = PVM.find v temp_rs ->
    Sem_HiFP.eval_hfstmts connect_stmts temp_rs' temp_s' init_s tmap = Some (rs', s') ->
    PVM.find v rs' = PVM.find v rs). { move : Hcmpnt; clear. intro; intro; elim.
  - intros Hdclr _ _ _ temp_rs temp_s rs s Heval temp_rs' temp_s' rs' s' Htemp Heval'. simpl in Heval. 
    apply (eval_hfstmts_find_eq2find_eq v Heval) in Heval'. move : Heval' => [Heval' _]. apply Heval'; done.
  - intros st ss IH Hdclr Hhelper1 Hexpand_branches Hhelper2 temp_rs temp_s rs s Heval temp_rs' temp_s' rs' s' Htemp Heval'. simpl in Heval.
    case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st; simpl in Heval.
    1,2,4,5 : move : temp_rs temp_s rs s Heval temp_rs' temp_s' rs' s' Htemp Heval'; apply IH; try done; intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    (* reg *)
    destruct (PVM.find var init_s) as [val|] eqn : Hfind; try discriminate.
    destruct (var == v) eqn : Heq. 
    - (* eq *)
      move /eqP : Heq => Heq; subst var. clear IH. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [ss_s [ss_rs [Hss Heval]]].
      (*assert (Hexpand_branches : Qin (Sfcnct (Eid v) (Eref (Eid v))) connect_stmts \/ exists e, Qin (Sfcnct (Eid v) e) connect_stmts). admit. 
      assert (Hhelper1 : forall s, Qin s connect_stmts -> is_connection s). admit. 
      assert (Hhelper2 : unique_connect_stmts connect_stmts). admit. *)
      destruct Hexpand_branches as [Hcase1|Hcase2].
      - (* reg <= reg *)
        specialize (eval_hfstmts_cnct_no_order Heval' Hhelper1 Hhelper2 Hcase1) as Heval'_order. destruct Heval'_order as [rs'0 [ns'0 [Heval'_order Hfind'_order]]].
        specialize (eval_hfstmts_cnct_no_order Heval Hhelper1 Hhelper2 Hcase1) as Heval_order. destruct Heval_order as [rs0 [ns0 [Heval_order Hfind_order]]].
        clear Heval' Heval. clear Hhelper1 Hhelper2. 
        specialize (Hfind'_order v); move : Hfind'_order => [Hfind'_order _].
        specialize (Hfind_order v); move : Hfind_order => [Hfind_order _]. 
        rewrite -Hfind_order -Hfind'_order; clear Hfind_order Hfind'_order.
        simpl in Heval'_order; simpl in Heval_order. rewrite Hcmpnt Hfind in Heval_order Heval'_order.
        apply (eval_hfstmts_find_eq2find_eq v Heval_order) in Heval'_order. move : Heval'_order => [Hfind' _].
        apply Hfind'. rewrite PVM.Lemmas.find_add_eq. rewrite PVM.Lemmas.find_add_eq //. 1,2 : apply PVM.M.SE.eq_refl.
      - (* reg <= e *)
        destruct Hcase2 as [e Hcase1].
        specialize (eval_hfstmts_cnct_no_order Heval' Hhelper1 Hhelper2 Hcase1) as Heval'_order. destruct Heval'_order as [rs'0 [ns'0 [Heval'_order Hfind'_order]]].
        specialize (eval_hfstmts_cnct_no_order Heval Hhelper1 Hhelper2 Hcase1) as Heval_order. destruct Heval_order as [rs0 [ns0 [Heval_order Hfind_order]]].
        clear Heval' Heval. clear Hhelper1 Hhelper2. 
        specialize (Hfind'_order v); move : Hfind'_order => [Hfind'_order _].
        specialize (Hfind_order v); move : Hfind_order => [Hfind_order _]. 
        rewrite -Hfind_order -Hfind'_order; clear Hfind_order Hfind'_order.
        simpl in Heval'_order; simpl in Heval_order. rewrite Hcmpnt in Heval_order Heval'_order.
        destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val_e|]; try discriminate.
        apply (eval_hfstmts_find_eq2find_eq v Heval_order) in Heval'_order. move : Heval'_order => [Hfind' _].
        apply Hfind'. rewrite PVM.Lemmas.find_add_eq. rewrite PVM.Lemmas.find_add_eq //. 1,2 : apply PVM.M.SE.eq_refl.
    - (* neq *)
      assert (Htemp' : PVM.find v temp_rs' = PVM.find v (PVM.add var val temp_rs)). rewrite PVM.Lemmas.find_add_neq //. move /eqP : Heq => Heq. move : Heq; apply contra_not.
        intro. rewrite /PVM.M.SE.eq in H. move /eqP : H => H; subst v; done.
      move : Htemp' Heval'. apply IH with (temp_s := temp_s) (s := s); try done. intros. apply Hdclr. simpl; rewrite H orb_true_r //.
    (* node *)
    destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate.
    move : Heval'; apply IH with (temp_rs := temp_rs) (temp_s := PVM.add var b temp_s) (s := s); try done. intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    (* cnct *)
    assert (Qin (Sfcnct ref e) (Qcons (Sfcnct ref e) ss)). simpl. rewrite eq_refl; rewrite eq_refl; simpl; done. apply Hdclr in H. simpl in H. done.
    (* invalid *)
    assert (Qin (Sinvalid ref) (Qcons (Sinvalid ref) ss)). simpl. rewrite eq_refl; simpl; done. apply Hdclr in H. simpl in H. done.
    (* when *)
    assert (Qin (Swhen cond ss_true ss_false) (Qcons (Swhen cond ss_true ss_false) ss)). simpl. rewrite eq_refl; simpl.
    specialize (hfstmt_seq_eqn_refl ss_true) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_true ss_true) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq; simpl. clear Heq Heq'.
    specialize (hfstmt_seq_eqn_refl ss_false) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_false ss_false) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq //.
    apply Hdclr in H. simpl in H. done.
    }
  intros H Hr_cnct rs s H0 rs' s' H1. move : H1; apply (Hhelper _ _ Hdclr) with (temp_rs := PVM.empty bits) (temp_s := PVM.empty bits) (s := s); try done.
  apply convert_to_connect_stmts_is_connection. 
  apply convert_to_connect_stmts_unique_connect_stmts.
Qed.

Lemma eval_hfstmts_Qcat_some' s1 s2 rs0 ns0 rs1 ns1 s tmap res : Sem_HiFP.eval_hfstmts (Qcat s1 s2) rs0 ns0 s tmap = Some res ->
  exists res', Sem_HiFP.eval_hfstmts s2 rs1 ns1 s tmap = Some res'.
Proof.
  move : s1 rs0 ns0 rs1 ns1. elim; simpl; intros.
  - (* s1 = Qnil *) destruct res as [rs ns].
    apply eval_hfstmts_exists with (rs1 := rs1) (ns1 := ns1) in H. destruct H as [rs' [ns' H]].
    exists (rs', ns'); done.
  - (* s1 = Qcons st sts *)
    destruct (Sem_HiFP.eval_hfstmt h rs0 ns0 s tmap) as [[rs2 ns2]|] eqn:E; try discriminate.
    apply (H rs2 ns2); done.
Qed.

Lemma convert_to_connect_stmt_qrcons k d acc hd : 
  convert_to_connect_stmt k d (Qrcons acc hd) = Qrcons (convert_to_connect_stmt k d acc) hd.
Proof.
  destruct d; simpl; try done.
Qed.

Lemma fold_left_qrcons l new acc : fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
  convert_to_connect_stmt (fst p) (snd p) a) l (Qrcons acc new) = Qrcons (fold_left (fun (a : HiFP.hfstmt_seq)
  (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l acc) new.
Proof.
  move : l acc. elim; simpl. done.
  intros hd tl IH acc. rewrite convert_to_connect_stmt_qrcons IH //.
Qed.

Lemma fold_left_qcat res l acc : fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
  convert_to_connect_stmt (fst p) (snd p) a) l (Qcat acc res) = Qcat (fold_left (fun (a : HiFP.hfstmt_seq)
  (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l acc) res.
Proof.
  move : res acc. elim; simpl.
  - intro; rewrite Qcats0. rewrite Qcats0 //.
  - intros hd tl IH acc. simpl. rewrite -Qcat_rcons. rewrite IH; clear IH.
    rewrite -Qcat_rcons. rewrite fold_left_qrcons //.
Qed.

Lemma eval_hfstmts_notin_none v ns0 rs0 init_s tmap : 
  forall l ss rs s,
  Sem_HiFP.eval_hfstmts ss rs0 ns0 init_s tmap = Some (rs, s) -> 
  (~ In v (fst (List.split l))) -> forall temp_rs temp_s, 
  Sem_HiFP.eval_hfstmts
  (fold_left
    (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
      convert_to_connect_stmt (fst p) (snd p) a) l ss)
  rs0 ns0 init_s tmap = Some (temp_rs, temp_s) -> 
  (PVM.find v s = None -> PVM.find v temp_s = None) /\ (PVM.find v rs = None -> PVM.find v temp_rs = None).
Proof.
  elim; simpl. intros. rewrite H in H1. inversion H1; subst temp_s temp_rs; done.
  intros [v_hd de_hd] tl IH ss rs s Hss Hnotin temp_rs temp_s Heval. destruct (List.split tl) as [tl_left tl_right] eqn : Hsplit; simpl in *.
  apply Decidable.not_or in Hnotin; move : Hnotin => [Hneq Hnotin].
  assert (convert_to_connect_stmt v_hd de_hd ss = Qcat (Qnil ProdVarOrder.T) (convert_to_connect_stmt v_hd de_hd ss)). simpl; done. 
  generalize Heval; intro Heval'. rewrite H in Heval; clear H. rewrite fold_left_qcat in Heval. specialize (eval_hfstmts_Qcat_exists Heval) as Hexists.
  destruct Hexists as [s_hd [rs_hd [_ Heval_hd]]]. apply eval_hfstmts_exists with (rs1 := rs0) (ns1 := ns0) in Heval_hd.
  destruct Heval_hd as [rs' [ns' Heval_hd]]. 
  specialize (IH _ _ _ Heval_hd Hnotin temp_rs temp_s Heval') as [IH0 IH1]. split.
  (* comb *) intro Hnone.
  assert (Hnone_hd : PVM.find v ns' = None). {
    move : Hneq Hss Hnone Heval_hd; clear.
    destruct de_hd; simpl in *; intros.
    - (* invalid *)
    destruct (PVM.find v_hd tmap) as [[gt cmpnt]|]; try discriminate. rewrite -Hnone.
    destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val). 
    11-12 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind1; done.
    1-14 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind1; rewrite PVM.Lemmas.find_add_neq //;
    unfold PVM.M.SE.eq; intro; move /eqP : H => H; subst v; done.
    - (* cnct *)
    destruct (PVM.find v_hd tmap) as [[gt cmpnt]|]; try discriminate. rewrite -Hnone.
    destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr h init_s tmap); try discriminate. 
    6 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind1; done.
    1-7 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind1; rewrite PVM.Lemmas.find_add_neq //;
    unfold PVM.M.SE.eq; intro; move /eqP : H => H; subst v; done.
  } apply IH0; done.
  (* sequ *) intro Hnone.
  assert (Hnone_hd : PVM.find v rs' = None). {
    move : Hneq Hss Hnone Heval_hd; clear.
    destruct de_hd; simpl in *; intros. 
    - (* invalid *)
    destruct (PVM.find v_hd tmap) as [[gt cmpnt]|]; try discriminate. rewrite -Hnone.
    destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val). 
    1-10,13-16 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind0; done.
    1-2 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind0; rewrite PVM.Lemmas.find_add_neq //;
    unfold PVM.M.SE.eq; intro; move /eqP : H => H; subst v; done.
    - (* cnct *)
    destruct (PVM.find v_hd tmap) as [[gt cmpnt]|]; try discriminate. rewrite -Hnone.
    destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr h init_s tmap); try discriminate. 
    1-5,7,8 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind0; done.
    specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind0; rewrite PVM.Lemmas.find_add_neq //;
    unfold PVM.M.SE.eq; intro; move /eqP : H => H; subst v; done.
  } apply IH1; done.
Qed.

Lemma eval_hfstmts_notinss_findeq tmap init_s ss temp_rs temp_s rs s v : (forall st, Qin st ss ->
  match st with 
  | Snode _ _ 
  | Sreg _ _ 
  | Swhen _ _ _ => False
  | Sfcnct v0 _ 
  | Sinvalid v0 => v0 <> Eid v
  | _ => True
  end) ->
  Sem_HiFP.eval_hfstmts ss temp_rs temp_s init_s tmap = Some (rs, s) ->
  PVM.find v s = PVM.find v temp_s /\ PVM.find v rs = PVM.find v temp_rs
with eval_hfstmt_notinss_findeq tmap init_s st temp_rs temp_s rs s v : 
  match st with 
  | Snode _ _ 
  | Sreg _ _ 
  | Swhen _ _ _ => False
  | Sfcnct v0 _ 
  | Sinvalid v0 => v0 <> Eid v
  | _ => True
  end ->
  Sem_HiFP.eval_hfstmt st temp_rs temp_s init_s tmap = Some (rs, s) ->
  PVM.find v s = PVM.find v temp_s /\ PVM.find v rs = PVM.find v temp_rs.
Proof.
  clear eval_hfstmts_notinss_findeq. move : ss temp_rs temp_s rs s. elim; simpl. intros temp_rs temp_s rs s Hnotin Hevals. inversion Hevals; subst s; done.
  intros hd tl IH temp_rs temp_s rs s Hnotin Hevals. destruct (Sem_HiFP.eval_hfstmt hd temp_rs temp_s init_s tmap) as [[rs0 ns0]|] eqn : Heval; try discriminate.
  assert (forall st : hfstmt ProdVarOrder.T,
    Qin st tl ->
    match st with
    | Snode _ _ 
    | Sreg _ _ 
    | Swhen _ _ _ => False
    | Sfcnct v0 _ | Sinvalid v0 => v0 <> Eid v
    | _ => True
    end). intros; apply Hnotin. rewrite H orb_true_r //.
  apply (IH _ _ _ _ H) in Hevals as [Hevals0 Hevals1]. rewrite Hevals0 Hevals1. clear H. 
  assert (match hd with
  | Snode _ _
  | Sreg _ _ 
  | Swhen _ _ _ => False
  | Sfcnct v0 _ | Sinvalid v0 => v0 <> Eid v
  | _ => True
  end). apply Hnotin. specialize (hfstmt_eqn_refl hd) as Heq. move/eqP : Heq => Heq. 
  specialize (hfstmt_eqP hd hd) as Heq'. apply reflect_iff in Heq'. apply Heq' in Heq. rewrite Heq orb_true_l //.
  move : H Heval; apply eval_hfstmt_notinss_findeq.

  clear eval_hfstmt_notinss_findeq. intros Hneq Heval. destruct st as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt; subst st; simpl in *; try done.
  1-4 : inversion Heval; subst s; done.
  (* cnct *) destruct v0; try (inversion Heval; subst s; done). destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate.
  destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate; try (inversion Heval; subst rs s; split); try done.
  1-8 : rewrite PVM.Lemmas.find_add_neq //. 1-8 : unfold PVM.M.SE.eq; intro; move /eqP : H => H; subst v; done.
  (* invalid *) destruct v0; try (inversion Heval; subst s rs; done). destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate.
  destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val); try (inversion Heval; subst s rs; split); try done.
  1-16 : rewrite PVM.Lemmas.find_add_neq //. 1-16 : unfold PVM.M.SE.eq; intro; move /eqP : H => H; subst v; done.
Qed.

Lemma convert_to_connect_stmt_qcat k d l tl : convert_to_connect_stmt k d (Qcat l tl) =
  Qcat (convert_to_connect_stmt k d l) tl.
Proof. 
  destruct d; simpl; done.
Qed.

Lemma eval_hfstmts_convert_to_connect_stmts_for_comb_helper v l1: 
  (~ In v (fst (List.split l1))) -> forall ss, (forall st : hfstmt ProdVarOrder.T,
      Qin st ss ->
      match st with
      | Snode _ _ 
      | Sreg _ _ 
      | Swhen _ _ _ => False
      | Sfcnct v0 _ | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end) ->
      forall st : hfstmt ProdVarOrder.T,
        Qin st
          (fold_left
            (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
              convert_to_connect_stmt (fst p) (snd p) a) l1 
            ss) ->
        match st with
        | Snode _ _ 
        | Sreg _ _ 
        | Swhen _ _ _ => False
        | Sfcnct v0 _ | Sinvalid v0 => v0 <> Eid v
        | _ => True
        end.
Proof.
  move : l1. elim; simpl. intros _ ss Hss st Hin. apply Hss; done.
  intros [hd_key hd_de] tl IH Hnotin ss Hss st. apply IH. move : Hnotin; apply contra_not; clear; intro.
    destruct (List.split tl) as [left right]; simpl in *. right; done.
  simpl; clear IH. rewrite -(qcat0s ss).
  rewrite convert_to_connect_stmt_qcat. destruct hd_de; simpl; try done.
  (* invalid *)
  intros. destruct (Qin st0 ss) eqn : Hin. apply Hss; done. clear Hin. rewrite orb_false_r in H.
  destruct st0; try done. move : Hnotin; apply contra_not; intro. subst h. move /eqP : H => H; inversion H; subst v.
  destruct (List.split tl); simpl. left; done.
  (* cnct *)
  intros. destruct (Qin st0 ss) eqn : Hin. apply Hss; done. clear Hin. rewrite orb_false_r in H.
  destruct st0; try done. move : Hnotin; apply contra_not; intro. subst h0. move /andP : H => [H _]. 
  move /eqP : H => H; inversion H; subst v. destruct (List.split tl); simpl. left; done.
Qed.

Lemma eval_hfstmts_convert_to_connect_stmts_for_comb conn_map init_s tmap rs s v : 
  match PVM.find v tmap with
  | Some (gt, Out_port) 
  | Some (gt, Wire) => Sem_HiFP.eval_hfstmts (convert_to_connect_stmts conn_map) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) -> 
      match PVM.find v conn_map with
      | Some (D_fexpr e) => Sem_HiFP.eval_hfexpr e init_s tmap = PVM.find v s
      | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then Some (take (sizeof_fgtyp gt) indeterminate_val) = PVM.find v s
          else Some (zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val) = PVM.find v s
      | _ => True
      end
  | _ => True
  end.
Proof. 
  case Hcmpnt : (PVM.find v tmap) => [[gt cmpnt]|]; try done. destruct cmpnt; try done.
  - (* outport *)
    intros Heval. destruct (PVM.find v conn_map) as [de|] eqn : Hcm; try done. destruct de as [gt_e|e].
    + (* invalid *) 
    remember (convert_to_connect_stmts conn_map) as cmlist.
    rewrite /convert_to_connect_stmts PVM.fold_1 in Heqcmlist. 
    apply CEP.Lemmas.find_some_mapsto in Hcm. apply CEP.Lemmas.F.elements_mapsto_iff in Hcm.
    remember (PVM.elements conn_map) as elements. apply InA_alt in Hcm. destruct Hcm as [[v' e'] [Heq Hin]].
    destruct Heq as [Heq0 Heq1]. simpl in Heq0; simpl in Heq1. move /eqP : Heq0 => Heq0; subst v' e'.
    destruct (in_split _ _ Hin) as [l1 [l2 Helements]]. subst elements.
    rewrite Helements in Heqcmlist. rewrite fold_left_app in Heqcmlist. simpl in Heqcmlist.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l1 (Qnil _)) as ss_prefix.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l2 (Qcons (Sinvalid (Eid v)) ss_prefix)) as ss_suffix.
    subst cmlist.
    assert (Heqss_suffix' : ss_suffix = Qcat (fold_left
                 (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
                  convert_to_connect_stmt (fst p) (snd p) a) l2 (Qnil ProdVarOrder.T)) (Qcons (Sinvalid (Eid v)) ss_prefix)). {
      move : Heqss_suffix; clear; intro. remember (Qcons (Sinvalid (Eid v)) ss_prefix) as res. clear Heqres. subst ss_suffix; clear.
      rewrite -fold_left_qcat. simpl. done. }
    clear Heqss_suffix.
    rewrite Heqss_suffix' in Heval. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [temp_s [temp_rs [Heval2 Heval1]]].
    assert (Htemp : PVM.find v temp_s = None). { 
      assert (Hnodup : ~ In v (fst (List.split l2))). {
        specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro.
        specialize (NoDupA_notin Hnodup) as [_ Hnotin]; done. }
      clear Heval1. assert (Sem_HiFP.eval_hfstmts (Qnil ProdVarOrder.T) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (PVM.empty bits, PVM.empty bits)) by (simpl; done).
      specialize (eval_hfstmts_notin_none H Hnodup Heval2) as [Hhelper _]. apply Hhelper; done.
    }
    clear Heval2 Heqss_suffix'. simpl in Heval1. rewrite Hcmpnt in Heval1. destruct (sizeof_fgtyp gt < length indeterminate_val).
    (* take *)
    remember (take (sizeof_fgtyp gt) indeterminate_val) as val; clear Heqval.
    assert (Hprefix : PVM.find v s = PVM.find v (PVM.add v val temp_s)).
      assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end).
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [Hhelper _]; done.
    rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
    (* ext *)
    remember (zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val) as val; clear Heqval.
    assert (Hprefix : PVM.find v s = PVM.find v (PVM.add v val temp_s)).
      assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end).
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [Hhelper _]; done.
    rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
    + (* cnct *)
    remember (convert_to_connect_stmts conn_map) as cmlist.
    rewrite /convert_to_connect_stmts PVM.fold_1 in Heqcmlist. 
    apply CEP.Lemmas.find_some_mapsto in Hcm. apply CEP.Lemmas.F.elements_mapsto_iff in Hcm.
    remember (PVM.elements conn_map) as elements. apply InA_alt in Hcm. destruct Hcm as [[v' e'] [Heq Hin]].
    destruct Heq as [Heq0 Heq1]. simpl in Heq0; simpl in Heq1. move /eqP : Heq0 => Heq0; subst v' e'.
    destruct (in_split _ _ Hin) as [l1 [l2 Helements]]. subst elements.
    rewrite Helements in Heqcmlist. rewrite fold_left_app in Heqcmlist. simpl in Heqcmlist.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l1 (Qnil _)) as ss_prefix.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l2 (Qcons (Sfcnct (Eid v) e) ss_prefix)) as ss_suffix.
    subst cmlist.
    assert (Heqss_suffix' : ss_suffix = Qcat (fold_left
                 (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
                  convert_to_connect_stmt (fst p) (snd p) a) l2 (Qnil ProdVarOrder.T)) (Qcons (Sfcnct (Eid v) e) ss_prefix)). {
      move : Heqss_suffix; clear; intro. remember (Qcons (Sfcnct (Eid v) e) ss_prefix) as res. clear Heqres. subst ss_suffix; clear.
      rewrite -fold_left_qcat. simpl. done. }
    clear Heqss_suffix.
    rewrite Heqss_suffix' in Heval. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [temp_s [temp_rs [Heval2 Heval1]]].
    assert (Htemp : PVM.find v temp_s = None). { 
      assert (Hnodup : ~ In v (fst (List.split l2))). {
        specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro.
        specialize (NoDupA_notin Hnodup) as [_ Hnotin]; done. }
      clear Heval1. assert (Sem_HiFP.eval_hfstmts (Qnil ProdVarOrder.T) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (PVM.empty bits, PVM.empty bits)) by (simpl; done).
      specialize (eval_hfstmts_notin_none H Hnodup Heval2) as [Hhelper _]. apply Hhelper; done.
    }
    clear Heval2 Heqss_suffix'. simpl in Heval1. rewrite Hcmpnt in Heval1. destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val|]; try discriminate.
    assert (Hprefix : PVM.find v s = PVM.find v (PVM.add v val temp_s)).
      assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end).
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [Hhelper _]; done.
    rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
  - (* wire 同上 *)
    intros Heval. destruct (PVM.find v conn_map) as [de|] eqn : Hcm; try done. destruct de as [gt_e|e].
    + (* invalid *) 
    remember (convert_to_connect_stmts conn_map) as cmlist.
    rewrite /convert_to_connect_stmts PVM.fold_1 in Heqcmlist. 
    apply CEP.Lemmas.find_some_mapsto in Hcm. apply CEP.Lemmas.F.elements_mapsto_iff in Hcm.
    remember (PVM.elements conn_map) as elements. apply InA_alt in Hcm. destruct Hcm as [[v' e'] [Heq Hin]].
    destruct Heq as [Heq0 Heq1]. simpl in Heq0; simpl in Heq1. move /eqP : Heq0 => Heq0; subst v' e'.
    destruct (in_split _ _ Hin) as [l1 [l2 Helements]]. subst elements.
    rewrite Helements in Heqcmlist. rewrite fold_left_app in Heqcmlist. simpl in Heqcmlist.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l1 (Qnil _)) as ss_prefix.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l2 (Qcons (Sinvalid (Eid v)) ss_prefix)) as ss_suffix.
    subst cmlist.
    assert (Heqss_suffix' : ss_suffix = Qcat (fold_left
                 (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
                  convert_to_connect_stmt (fst p) (snd p) a) l2 (Qnil ProdVarOrder.T)) (Qcons (Sinvalid (Eid v)) ss_prefix)). {
      move : Heqss_suffix; clear; intro. remember (Qcons (Sinvalid (Eid v)) ss_prefix) as res. clear Heqres. subst ss_suffix; clear.
      rewrite -fold_left_qcat. simpl. done. }
    clear Heqss_suffix.
    rewrite Heqss_suffix' in Heval. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [temp_s [temp_rs [Heval2 Heval1]]].
    assert (Htemp : PVM.find v temp_s = None). { 
      assert (Hnodup : ~ In v (fst (List.split l2))). {
        specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro.
        specialize (NoDupA_notin Hnodup) as [_ Hnotin]; done. }
      clear Heval1. assert (Sem_HiFP.eval_hfstmts (Qnil ProdVarOrder.T) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (PVM.empty bits, PVM.empty bits)) by (simpl; done).
      specialize (eval_hfstmts_notin_none H Hnodup Heval2) as [Hhelper _]. apply Hhelper; done.
    }
    clear Heval2 Heqss_suffix'. simpl in Heval1. rewrite Hcmpnt in Heval1. destruct (sizeof_fgtyp gt < length indeterminate_val).
    (* take *)
    remember (take (sizeof_fgtyp gt) indeterminate_val) as val; clear Heqval.
    assert (Hprefix : PVM.find v s = PVM.find v (PVM.add v val temp_s)).
      assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end).
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [Hhelper _]; done.
    rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
    (* ext *)
    remember (zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val) as val; clear Heqval.
    assert (Hprefix : PVM.find v s = PVM.find v (PVM.add v val temp_s)).
      assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end).
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [Hhelper _]; done.
    rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
    + (* cnct *)
    remember (convert_to_connect_stmts conn_map) as cmlist.
    rewrite /convert_to_connect_stmts PVM.fold_1 in Heqcmlist. 
    apply CEP.Lemmas.find_some_mapsto in Hcm. apply CEP.Lemmas.F.elements_mapsto_iff in Hcm.
    remember (PVM.elements conn_map) as elements. apply InA_alt in Hcm. destruct Hcm as [[v' e'] [Heq Hin]].
    destruct Heq as [Heq0 Heq1]. simpl in Heq0; simpl in Heq1. move /eqP : Heq0 => Heq0; subst v' e'.
    destruct (in_split _ _ Hin) as [l1 [l2 Helements]]. subst elements.
    rewrite Helements in Heqcmlist. rewrite fold_left_app in Heqcmlist. simpl in Heqcmlist.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l1 (Qnil _)) as ss_prefix.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l2 (Qcons (Sfcnct (Eid v) e) ss_prefix)) as ss_suffix.
    subst cmlist.
    assert (Heqss_suffix' : ss_suffix = Qcat (fold_left
                 (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
                  convert_to_connect_stmt (fst p) (snd p) a) l2 (Qnil ProdVarOrder.T)) (Qcons (Sfcnct (Eid v) e) ss_prefix)). {
      move : Heqss_suffix; clear; intro. remember (Qcons (Sfcnct (Eid v) e) ss_prefix) as res. clear Heqres. subst ss_suffix; clear.
      rewrite -fold_left_qcat. simpl. done. }
    clear Heqss_suffix.
    rewrite Heqss_suffix' in Heval. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [temp_s [temp_rs [Heval2 Heval1]]].
    assert (Htemp : PVM.find v temp_s = None). { 
      assert (Hnodup : ~ In v (fst (List.split l2))). {
        specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro.
        specialize (NoDupA_notin Hnodup) as [_ Hnotin]; done. }
      clear Heval1. assert (Sem_HiFP.eval_hfstmts (Qnil ProdVarOrder.T) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (PVM.empty bits, PVM.empty bits)) by (simpl; done).
      specialize (eval_hfstmts_notin_none H Hnodup Heval2) as [Hhelper _]. apply Hhelper; done.
    }
    clear Heval2 Heqss_suffix'. simpl in Heval1. rewrite Hcmpnt in Heval1. destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val|]; try discriminate.
    assert (Hprefix : PVM.find v s = PVM.find v (PVM.add v val temp_s)).
      assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end).
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [Hhelper _]; done.
    rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
Qed. 

Lemma eval_hfstmts_convert_to_connect_stmts_for_sequ conn_map init_s tmap rs s v : 
  match PVM.find v tmap with
  | Some (gt, Register) => Sem_HiFP.eval_hfstmts (convert_to_connect_stmts conn_map) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) -> 
      match PVM.find v conn_map with
      | Some (D_fexpr e) => Sem_HiFP.eval_hfexpr e init_s tmap = PVM.find v rs
      | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then Some (take (sizeof_fgtyp gt) indeterminate_val) = PVM.find v rs
          else Some (zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val) = PVM.find v rs
      | _ => True
      end
  | _ => True
  end.
Proof. 
  destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt; try done. destruct cmpnt; try done.
  intros Heval. destruct (PVM.find v conn_map) as [de|] eqn : Hcm; try done. destruct de as [gt_e|e].
  + (* invalid *) 
  remember (convert_to_connect_stmts conn_map) as cmlist.
  rewrite /convert_to_connect_stmts PVM.fold_1 in Heqcmlist. 
  apply CEP.Lemmas.find_some_mapsto in Hcm. apply CEP.Lemmas.F.elements_mapsto_iff in Hcm.
  remember (PVM.elements conn_map) as elements. apply InA_alt in Hcm. destruct Hcm as [[v' e'] [Heq Hin]].
  destruct Heq as [Heq0 Heq1]. simpl in Heq0; simpl in Heq1. move /eqP : Heq0 => Heq0; subst v' e'.
  destruct (in_split _ _ Hin) as [l1 [l2 Helements]]. subst elements.
  rewrite Helements in Heqcmlist. rewrite fold_left_app in Heqcmlist. simpl in Heqcmlist.
  remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l1 (Qnil _)) as ss_prefix.
  remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l2 (Qcons (Sinvalid (Eid v)) ss_prefix)) as ss_suffix.
  subst cmlist.
  assert (Heqss_suffix' : ss_suffix = Qcat (fold_left
                 (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
                  convert_to_connect_stmt (fst p) (snd p) a) l2 (Qnil ProdVarOrder.T)) (Qcons (Sinvalid (Eid v)) ss_prefix)). rewrite -fold_left_qcat qcat0s //. clear Heqss_suffix.
  rewrite Heqss_suffix' in Heval. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [temp_s [temp_rs [Heval2 Heval1]]].
  assert (Htemp : PVM.find v temp_rs = None). { 
    assert (Hnodup : ~ In v (fst (List.split l2))). {
      specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro.
      specialize (NoDupA_notin Hnodup) as [_ Hnotin]; done. }
    clear Heval1. assert (Sem_HiFP.eval_hfstmts (Qnil ProdVarOrder.T) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (PVM.empty bits, PVM.empty bits)) by (simpl; done).
    specialize (eval_hfstmts_notin_none H Hnodup Heval2) as [_ Hhelper]. apply Hhelper; done.
  }
  clear Heval2 Heqss_suffix'. simpl in Heval1. rewrite Hcmpnt in Heval1. destruct (sizeof_fgtyp gt < length indeterminate_val).
  (* take *)
  remember (take (sizeof_fgtyp gt) indeterminate_val) as val; clear Heqval.
  assert (Hprefix : PVM.find v rs = PVM.find v (PVM.add v val temp_rs)). 
    assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _ 
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end). 
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [_ Hhelper]; done.
  rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
  (* ext *)
  remember (zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val) as val; clear Heqval.
  assert (Hprefix : PVM.find v rs = PVM.find v (PVM.add v val temp_rs)). 
    assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _ 
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end). 
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [_ Hhelper]; done.
  rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
  + (* cnct *) 
  remember (convert_to_connect_stmts conn_map) as cmlist.
  rewrite /convert_to_connect_stmts PVM.fold_1 in Heqcmlist. 
  apply CEP.Lemmas.find_some_mapsto in Hcm. apply CEP.Lemmas.F.elements_mapsto_iff in Hcm.
  remember (PVM.elements conn_map) as elements. apply InA_alt in Hcm. destruct Hcm as [[v' e'] [Heq Hin]].
  destruct Heq as [Heq0 Heq1]. simpl in Heq0; simpl in Heq1. move /eqP : Heq0 => Heq0; subst v' e'.
  destruct (in_split _ _ Hin) as [l1 [l2 Helements]]. subst elements.
  rewrite Helements in Heqcmlist. rewrite fold_left_app in Heqcmlist. simpl in Heqcmlist.
  remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l1 (Qnil _)) as ss_prefix.
  remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l2 (Qcons (Sfcnct (Eid v) e) ss_prefix)) as ss_suffix.
  subst cmlist.
  assert (Heqss_suffix' : ss_suffix = Qcat (fold_left
                 (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
                  convert_to_connect_stmt (fst p) (snd p) a) l2 (Qnil ProdVarOrder.T)) (Qcons (Sfcnct (Eid v) e) ss_prefix)). rewrite -fold_left_qcat qcat0s //. clear Heqss_suffix.
  rewrite Heqss_suffix' in Heval. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [temp_s [temp_rs [Heval2 Heval1]]].
  assert (Htemp : PVM.find v temp_rs = None). { 
    assert (Hnodup : ~ In v (fst (List.split l2))). {
      specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro.
      specialize (NoDupA_notin Hnodup) as [_ Hnotin]; done. }
    clear Heval1. assert (Sem_HiFP.eval_hfstmts (Qnil ProdVarOrder.T) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (PVM.empty bits, PVM.empty bits)) by (simpl; done).
    specialize (eval_hfstmts_notin_none H Hnodup Heval2) as [_ Hhelper]. apply Hhelper; done.
  }
  clear Heval2 Heqss_suffix'. simpl in Heval1. rewrite Hcmpnt in Heval1. destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val|]; try discriminate.
  assert (Hprefix : PVM.find v rs = PVM.find v (PVM.add v val temp_rs)). 
    assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _ 
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end). 
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [_ Hhelper]; done.
  rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
Qed.

Lemma eval_fexpr_PVM_included_eq e init_s1 init_s2 tmap bs : pvm_included init_s1 init_s2 -> Sem_HiFP.eval_hfexpr e init_s1 tmap = Some bs ->
  Sem_HiFP.eval_hfexpr e init_s2 tmap = Some bs.
Proof. 
  unfold pvm_included. intro Heq. move : e bs; elim.
  simpl; done.
  (* cast *)
  simpl; intros. destruct u; try (apply H; done). 
  1,2 : destruct (Sem_HiFP.eval_hfexpr h init_s1 tmap); try discriminate; inversion H0; subst bs; rewrite (H b) //.
  (* unop *)
  simpl; intros. destruct (Sem_HiFP.eval_hfexpr h init_s1 tmap); try discriminate.
  destruct (Sem_HiFP.type_of_hfexpr h tmap); try discriminate. rewrite (H b) //.
  (* binop *)
  simpl; intros. destruct (Sem_HiFP.eval_hfexpr h init_s1 tmap); try discriminate.
  destruct (Sem_HiFP.eval_hfexpr h0 init_s1 tmap); try discriminate.
  destruct (Sem_HiFP.type_of_hfexpr h tmap); try discriminate. 
  destruct (Sem_HiFP.type_of_hfexpr h0 tmap); try discriminate. rewrite (H b). rewrite (H0 b0) //. done.
  (* mux *)
  simpl; intros.
  destruct (Sem_HiFP.eval_hfexpr h init_s1 tmap); try discriminate.
  rewrite (H b); try done. destruct (~~ is_zero b); try apply H0; try apply H1; try done.
  (*destruct (Sem_HiFP.type_of_hfexpr h0 tmap); try discriminate. destruct f; try discriminate. 
    destruct (Sem_HiFP.type_of_hfexpr h1 tmap); try discriminate. destruct f; try discriminate. 
    destruct (Sem_HiFP.eval_hfexpr h0 init_s1 tmap); try discriminate.
    destruct (Sem_HiFP.eval_hfexpr h1 init_s1 tmap); try discriminate.
    rewrite (H b); try done. rewrite (H0 b0); try done. rewrite (H1 b1); try done.
    (* same *)
    destruct (Sem_HiFP.type_of_hfexpr h1 tmap); try discriminate. destruct f; try discriminate. 
    destruct (Sem_HiFP.eval_hfexpr h0 init_s1 tmap); try discriminate.
    destruct (Sem_HiFP.eval_hfexpr h1 init_s1 tmap); try discriminate.
    rewrite (H b); try done. rewrite (H0 b0); try done. rewrite (H1 b1); try done.*)
  (* ref *)
  simpl; intros. destruct h; try discriminate. move : H; apply Heq.
Qed.

Lemma eval_hfexpr_Emux_eq_true_false cond init_s tmap: match Sem_HiFP.eval_hfexpr cond init_s tmap with
  | Some valc => forall e1 e2, if (~~ is_zero valc) then Sem_HiFP.eval_hfexpr (Emux cond e1 e2) init_s tmap = Sem_HiFP.eval_hfexpr e1 init_s tmap
                 else Sem_HiFP.eval_hfexpr (Emux cond e1 e2) init_s tmap = Sem_HiFP.eval_hfexpr e2 init_s tmap
  | _ => True
  end.
Proof. 
  destruct (Sem_HiFP.eval_hfexpr cond init_s tmap) as [valc|] eqn : Hcond; try done. 
  intros; destruct(~~ is_zero valc) as [|] eqn : Htrue; simpl; rewrite Hcond Htrue //. 
Qed.

Lemma eval_hfstmts_ExpandBranches_funs_find_for_comb_helper v gt init_s tmap :
  PVM.find v tmap = Some (gt, Out_port) \/ PVM.find v tmap = Some (gt, Wire) ->
  forall (ss : HiFP.hfstmt_seq) (rs s rs0 s0 : PVM.t bits),
    (~ exists r, Qin (Sreg v r) ss) /\ (~ exists e, Qin (Snode v e) ss) -> 
    Sem_HiFP.eval_hfstmts ss rs0 s0 init_s tmap = Some (rs, s) ->
    forall val, PVM.find v s = Some val ->
    forall (old_conn_map : PVM.t def_expr), (forall val0, PVM.find v s0 = Some val0 ->
    match PVM.find v old_conn_map with
    | Some (D_fexpr e') => Sem_HiFP.eval_hfexpr e' init_s tmap = Some val0
    | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val0
          else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val0
    | _ => False
    end) ->
    forall conn_map : PVM.t def_expr,
    ExpandBranches_funs ss old_conn_map tmap = Some conn_map ->
    match PVM.find v conn_map with
    | Some (D_fexpr e) => Sem_HiFP.eval_hfexpr e init_s tmap = Some val 
    | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val
          else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val
    | _ => False
    end
with eval_hfstmt_ExpandBranches_funs_find_for_comb_helper st v gt init_s tmap :
  PVM.find v tmap = Some (gt, Out_port) \/ PVM.find v tmap = Some (gt, Wire) ->
  forall (rs_temp s_temp rs0 s0 : PVM.t bits),
  Sem_HiFP.eval_hfstmt st rs0 s0 init_s tmap = Some (rs_temp, s_temp) ->
  forall (old_conn_map : PVM.t def_expr), (forall val0, PVM.find v s0 = Some val0 ->
    match PVM.find v old_conn_map with
    | Some (D_fexpr e') => Sem_HiFP.eval_hfexpr e' init_s tmap = Some val0
    | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val0
          else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val0
    | _ => False
    end) ->
    match st with
    | Swhen cond ss_true ss_false => forall true_conn_map false_conn_map,
                        ExpandBranches_funs ss_true old_conn_map tmap = Some true_conn_map -> 
                        ExpandBranches_funs ss_false old_conn_map tmap = Some false_conn_map ->
                        forall val, PVM.find v s_temp = Some val ->
                        match PVM.find v (combine_when_connections cond true_conn_map false_conn_map) with
                        | Some (D_invalidated _) =>
                                if sizeof_fgtyp gt < length indeterminate_val
                                then take (sizeof_fgtyp gt) indeterminate_val = val
                                else
                                zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val = val
                        | Some (D_fexpr e') => Sem_HiFP.eval_hfexpr e' init_s tmap = Some val
                        | None => False
                        end
    | _ => True
    end. 
Proof. clear eval_hfstmts_ExpandBranches_funs_find_for_comb_helper. intro Hcmpnt.
  elim. 
  - simpl; intros rs s rs0 s0 Hnotin Heval val Hval old_conn_map Hinit conn_map Hexpand_branches.
    inversion Heval; subst rs s; clear Heval. inversion Hexpand_branches; subst conn_map; clear Hexpand_branches. apply Hinit; done.
  - intros st sts IH rs s rs0 s0 Hnotin Heval val Hval old_conn_map Hinit conn_map Hexpand_branches.
    simpl in Heval. destruct (Sem_HiFP.eval_hfstmt st rs0 s0 init_s tmap) as [[rs_temp s_temp]|] eqn : Heval_temp; try discriminate.
    simpl in Hexpand_branches. destruct (ExpandBranch_fun st old_conn_map) as [temp_conn_map|] eqn : Hexpand_branches_temp; try discriminate.
    move : conn_map Hexpand_branches. apply IH with (rs := rs) (s := s) (rs0 := rs_temp) (s0 := s_temp); try done. split; move : Hnotin => [Hnotin0 Hnotin1].
    (* not in *)
    move : Hnotin0; apply contra_not; intro. destruct H as [r H]; exists r; simpl. rewrite H orb_true_r //.
    move : Hnotin1; apply contra_not; intro. destruct H as [e H]; exists e; simpl. rewrite H orb_true_r //.
    (* find temp *)
    assert ((~ exists r, hfstmt_eqn st (Sreg v r)) /\ (~ exists e, hfstmt_eqn st (Snode v e))). {
      split; move : Hnotin => [Hnotin0 Hnotin1].
      move : Hnotin0; apply contra_not; intro. destruct H as [r H]; exists r; simpl. rewrite H orb_true_l //.
      move : Hnotin1; apply contra_not; intro. destruct H as [e H]; exists e; simpl. rewrite H orb_true_l //. }
    move : H; clear IH Hnotin Heval sts rs. intros Hnotin val_temp Hval_temp.
    case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st.
    + (* skip, wire *)
      1,2,4,5 : simpl in Hexpand_branches_temp; inversion Hexpand_branches_temp; subst old_conn_map; clear Hexpand_branches_temp;
      simpl in Heval_temp; inversion Heval_temp; subst rs0 s0; clear Heval_temp; apply Hinit in Hval_temp; done.
    + (* reg *) 
      simpl in Hexpand_branches_temp. destruct (type reg); try discriminate. inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      rewrite HiFP.PCELemmas.find_add_neq.
      simpl in Heval_temp. destruct (PVM.find var init_s); try discriminate. inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. apply Hinit in Hval_temp; done.
      move : Hnotin => [Hnotin _]. move : Hnotin; apply contra_not; intro. exists reg; simpl. move /eqP : H => H; subst v. rewrite eq_refl; rewrite eq_refl; simpl; done.
    + (* node *) 
      simpl in Hexpand_branches_temp. inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      simpl in Heval_temp. destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate. inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. 
      rewrite HiFP.PCELemmas.find_add_neq in Hval_temp. apply Hinit in Hval_temp; done.
      move : Hnotin => [_ Hnotin]. move : Hnotin; apply contra_not; intro. exists node_e; simpl. move /eqP : H => H; subst v. rewrite eq_refl; rewrite eq_refl; simpl; done.
    + (* fcnct *) 
      simpl in Hexpand_branches_temp. case Href : ref => [var|||]; subst ref; try discriminate. inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      destruct (v == var) eqn : Heq.
      * move /eqP : Heq => Heq; subst var. rewrite HiFP.PCELemmas.find_add_eq; try apply CEP.SE.eq_refl.
        simpl in Heval_temp. destruct Hcmpnt as [Hcmpnt|Hcmpnt].
        (* outport *)
        rewrite Hcmpnt in Heval_temp. destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val_e|]; try discriminate.
        inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq in Hval_temp. done.
        apply CEP.SE.eq_refl.
        (* wire *)
        rewrite Hcmpnt in Heval_temp. destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val_e|]; try discriminate.
        inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq in Hval_temp. done.
        apply CEP.SE.eq_refl.
      * rewrite HiFP.PCELemmas.find_add_neq. 
        simpl in Heval_temp. destruct (PVM.find var tmap) as [[gt_var cmpnt_var]|]; try discriminate.
        destruct cmpnt_var; destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val_e|]; try discriminate; inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp;
        try rewrite HiFP.PCELemmas.find_add_neq in Hval_temp; try (apply Hinit; done). 1-8 : move /eqP : Heq => Heq; move : Heq; apply contra_not; intro; unfold CEP.SE.eq in H; move /eqP : H => H; subst v; done.
    + (* invalid *) 
      simpl in Hexpand_branches_temp. case Href : ref => [var|||]; subst ref; try discriminate. destruct (PVM.find var tmap) as [[gt' cmpnt]|]; try discriminate.
      inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp Hnotin. 
      destruct (v == var) eqn : Heq.
      * move /eqP : Heq => Heq; subst var. rewrite HiFP.PCELemmas.find_add_eq; try apply CEP.SE.eq_refl.
        simpl in Heval_temp. destruct Hcmpnt as [Hcmpnt|Hcmpnt].
        (* outport *)
        rewrite Hcmpnt in Heval_temp. destruct (sizeof_fgtyp gt < length indeterminate_val).
        - (* take *)
          inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp; rewrite HiFP.PCELemmas.find_add_eq in Hval_temp.
          inversion Hval_temp; done. apply CEP.SE.eq_refl.
        - (* ext *)
          inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq in Hval_temp.
          inversion Hval_temp; done. apply CEP.SE.eq_refl.
        (* wire *)
        rewrite Hcmpnt in Heval_temp. destruct (sizeof_fgtyp gt < length indeterminate_val).
        - (* take *)
          inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp; rewrite HiFP.PCELemmas.find_add_eq in Hval_temp.
          inversion Hval_temp; done. apply CEP.SE.eq_refl.
        - (* ext *)
          inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq in Hval_temp.
          inversion Hval_temp; done. apply CEP.SE.eq_refl.
      * rewrite HiFP.PCELemmas.find_add_neq. 
        simpl in Heval_temp. destruct (PVM.find var tmap) as [[gt_var cmpnt_var]|]; try discriminate.
        destruct cmpnt_var; destruct (sizeof_fgtyp gt_var < length indeterminate_val); inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp;
        try rewrite HiFP.PCELemmas.find_add_neq in Hval_temp; try (apply Hinit; done). 1-15 : move /eqP : Heq => Heq; move : Heq; apply contra_not; intro; unfold CEP.SE.eq in H; move /eqP : H => H; subst v; done. 
    + (* when *)
      simpl in Hexpand_branches_temp. destruct (ExpandBranches_funs ss_true old_conn_map tmap) as [true_conn_map|] eqn : Hexpand_true; try discriminate.
      destruct (ExpandBranches_funs ss_false old_conn_map tmap) as [false_conn_map|] eqn : Hexpand_false; try discriminate. 
      inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      specialize (eval_hfstmt_ExpandBranches_funs_find_for_comb_helper _ _ _ _ _ Hcmpnt _ _ _ _ Heval_temp _ Hinit) as Hwhen; simpl in Hwhen;
        clear eval_hfstmt_ExpandBranches_funs_find_for_comb_helper. specialize (Hwhen _ _ Hexpand_true Hexpand_false _ Hval_temp). done.

  clear eval_hfstmt_ExpandBranches_funs_find_for_comb_helper.
  intros Hcmpnt rs_temp s_temp rs0 s0 Heval old_conn_map Hinit.
  case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st; try done. intros true_conn_map false_conn_map Hexpand_true Hexpand_false val Hval.
  simpl in Heval. destruct (Sem_HiFP.eval_hfexpr cond init_s tmap) as [valc|] eqn : Hvalc; try discriminate. destruct (~~ is_zero valc) eqn : Hcond.
  - (* when go to true *)
    clear Hexpand_false. 
    assert ((~ exists r, Qin (Sreg v r) ss_true) /\ (~ exists e, Qin (Snode v e) ss_true)). 
      specialize (well_formedness ss_true tmap) as [_ [_ [_ [_ [H]]]]]. split; try apply H; try apply H0.
    specialize (eval_hfstmts_ExpandBranches_funs_find_for_comb_helper _ _ _ _ Hcmpnt _ _ _ _ _ H Heval _ Hval _ Hinit _ Hexpand_true) as Htrue; 
      clear eval_hfstmts_ExpandBranches_funs_find_for_comb_helper. unfold combine_when_connections. rewrite PVM.Lemmas.F.map2_1bis; try done.
    destruct (PVM.find v true_conn_map) as [de_true|] eqn : Hde_true; try done. destruct de_true as [gt_e_true|e_true].
    + (* true is invlid *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false.
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        apply eval_invalid_is_allowed.
      * (* false is cnct *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        apply eval_invalid_is_allowed.
    + (* true is cnct *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false as [gt_e_false|e_false].
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
      * (* false is cnct *) destruct (e_true == e_false) eqn : Heq; try done.
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
  - (* when go to false *)
    clear Hexpand_true. 
    assert ((~ exists r, Qin (Sreg v r) ss_false) /\ (~ exists e, Qin (Snode v e) ss_false)). 
      specialize (well_formedness ss_false tmap) as [_ [_ [_ [_ [H]]]]]. split; try apply H; try apply H0.
    specialize (eval_hfstmts_ExpandBranches_funs_find_for_comb_helper _ _ _ _ Hcmpnt _ _ _ _ _ H Heval _ Hval _ Hinit _ Hexpand_false) as Hfalse; 
      clear eval_hfstmts_ExpandBranches_funs_find_for_comb_helper. unfold combine_when_connections. rewrite PVM.Lemmas.F.map2_1bis; try done.
    destruct (PVM.find v true_conn_map) as [de_true|] eqn : Hde_true; try done. destruct de_true as [gt_e_true|e_true].
    + (* true is invlid *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false.
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        apply eval_invalid_is_allowed.
      * (* false is cnct *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
    + (* true is cnct *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false as [gt_e_false|e_false].
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        apply eval_invalid_is_allowed.
      * (* false is cnct *) destruct (e_true == e_false) eqn : Heq. move /eqP : Heq => Heq; subst e_true. done.
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
Admitted.

Lemma eval_hfstmts_ExpandBranches_funs_find_for_comb ss init_s tmap rs s v : 
  match PVM.find v tmap with
  | Some (gt, Out_port) 
  | Some (gt, Wire) => (~ exists r, Qin (Sreg v r) ss) /\ (~ exists e, Qin (Snode v e) ss) ->
  Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
  forall val, PVM.find v s = Some val ->
  forall conn_map, ExpandBranches_funs ss (PVM.empty def_expr) tmap = Some conn_map -> 
      match PVM.find v conn_map with
      | Some (D_fexpr e) => Sem_HiFP.eval_hfexpr e init_s tmap = Some val
      | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val
          else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val
      | _ => False
      end
  | _ => True
  end.
Proof. 
  destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt; try done. destruct cmpnt; try done.
  assert (Hcmpnt' : PVM.find v tmap = Some (gt, Out_port) \/ PVM.find v tmap = Some (gt, Wire)) by (left; done).
  intros; move : conn_map H2. apply (eval_hfstmts_ExpandBranches_funs_find_for_comb_helper Hcmpnt' H H0 H1); try done.
  assert (Hcmpnt' : PVM.find v tmap = Some (gt, Out_port) \/ PVM.find v tmap = Some (gt, Wire)) by (right; done).
  intros; move : conn_map H2. apply (eval_hfstmts_ExpandBranches_funs_find_for_comb_helper Hcmpnt' H H0 H1); try done.
Qed. 

Lemma ExpandBranch_fun_none st old_conn_map tmap temp_conn_map v : ExpandBranch_fun st old_conn_map tmap = Some temp_conn_map -> PVM.find v temp_conn_map = None
  -> PVM.find v old_conn_map = None
with ExpandBranches_fun_none ss old_conn_map tmap temp_conn_map v : ExpandBranches_funs ss old_conn_map tmap = Some temp_conn_map -> PVM.find v temp_conn_map = None
  -> PVM.find v old_conn_map = None.
Proof. 
  destruct st; simpl.
  1,2,4,5,6 : intros; inversion H; subst old_conn_map; done.
  (* reg *)
  intros. destruct (type h); try discriminate. inversion H; subst temp_conn_map; clear H.
  apply CEP.Lemmas.not_in_find_none. apply CEP.Lemmas.find_none_not_in in H0. move : H0; apply contra_not.
  intro. apply CEP.Lemmas.F.add_in_iff; right; done.
  (* cnct *)
  intros. destruct h; try discriminate. inversion H; subst temp_conn_map; clear H.
  apply CEP.Lemmas.not_in_find_none. apply CEP.Lemmas.find_none_not_in in H0. move : H0; apply contra_not.
  intro. apply CEP.Lemmas.F.add_in_iff; right; done.
  (* invalid *)
  intros. destruct h; try discriminate. destruct (PVM.find s tmap) as [[gt cmpnt]|]; try discriminate.
  inversion H; subst temp_conn_map; clear H.
  apply CEP.Lemmas.not_in_find_none. apply CEP.Lemmas.find_none_not_in in H0. move : H0; apply contra_not.
  intro. apply CEP.Lemmas.F.add_in_iff; right; done.
  (* when *)
  intros. destruct (ExpandBranches_funs h0 old_conn_map tmap) as [true_conn_map|] eqn : Htrue; try discriminate.
  destruct (ExpandBranches_funs h1 old_conn_map tmap) as [false_conn_map|] eqn : Hfalse; try discriminate.
  inversion H; subst temp_conn_map; clear H. unfold combine_when_connections in H0. 
  rewrite CEP.Lemmas.map2_1bis in H0; try done. destruct (PVM.find v true_conn_map) as [de_true|] eqn : Hfind_true.
  destruct de_true; destruct (PVM.find v false_conn_map) as [de_false|]; try destruct de_false; try destruct (h2 == h3); try discriminate.
  move : Hfalse H0; apply ExpandBranches_fun_none.

  clear ExpandBranches_fun_none. move : ss old_conn_map temp_conn_map. elim. 
  simpl; intros. inversion H; subst temp_conn_map; done.
  simpl; intros hd tl IH; intros. destruct (ExpandBranch_fun hd old_conn_map tmap) eqn : Hexpand; try discriminate.
  apply (IH _ _ H) in H0; clear IH. move : Hexpand H0; apply ExpandBranch_fun_none.
Qed.

Lemma eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper v gt init_s tmap :
  PVM.find v tmap = Some (gt, Register) -> 
  forall (ss : HiFP.hfstmt_seq) (rs s rs0 s0 : PVM.t bits),
    Sem_HiFP.eval_hfstmts ss rs0 s0 init_s tmap = Some (rs, s) ->
    forall val, PVM.find v rs = Some val ->
    forall (old_conn_map : PVM.t def_expr), (forall val0, PVM.find v rs0 = Some val0 ->
    match PVM.find v old_conn_map with
      | Some (D_fexpr e') => Sem_HiFP.eval_hfexpr e' init_s tmap = Some val0
      | Some (D_invalidated _) => 
            if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val0
            else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val0
      | _ => False
      end) ->
    forall conn_map : PVM.t def_expr,
    ExpandBranches_funs ss old_conn_map tmap = Some conn_map ->
      match PVM.find v conn_map with
      | Some (D_fexpr e) => Sem_HiFP.eval_hfexpr e init_s tmap = Some val 
      | Some (D_invalidated _) => 
            if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val
            else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val
      | _ => False
      end
with eval_hfstmt_ExpandBranches_funs_find_for_sequ_helper st v gt init_s tmap :
  PVM.find v tmap = Some (gt, Register) -> 
  forall (rs_temp s_temp rs0 s0 : PVM.t bits),
  Sem_HiFP.eval_hfstmt st rs0 s0 init_s tmap = Some (rs_temp, s_temp) ->
  forall (old_conn_map : PVM.t def_expr), (forall val0, PVM.find v rs0 = Some val0 ->
  match PVM.find v old_conn_map with
    | Some (D_fexpr e') => Sem_HiFP.eval_hfexpr e' init_s tmap = Some val0
    | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val0
          else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val0
    | _ => False
    end) ->
    match st with
    | Swhen cond ss_true ss_false => forall true_conn_map false_conn_map,
                        ExpandBranches_funs ss_true old_conn_map tmap = Some true_conn_map -> 
                        ExpandBranches_funs ss_false old_conn_map tmap = Some false_conn_map ->
                        forall val, PVM.find v rs_temp = Some val ->
                        match PVM.find v (combine_when_connections cond true_conn_map false_conn_map) with
                          | Some (D_invalidated _) =>
                                  if sizeof_fgtyp gt < length indeterminate_val
                                  then take (sizeof_fgtyp gt) indeterminate_val = val
                                  else
                                  zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val = val
                          | Some (D_fexpr e') => Sem_HiFP.eval_hfexpr e' init_s tmap = Some val
                          | None => False
                          end
    | _ => True
    end. 
Proof. intro Hcmpnt.
  elim. clear eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper.
  - simpl; intros rs s rs0 s0 Heval val Hval old_conn_map Hinit conn_map Hexpand_branches.
    inversion Heval; subst rs s; clear Heval. inversion Hexpand_branches; subst conn_map; clear Hexpand_branches. apply Hinit; done.
  - intros st sts IH rs s rs0 s0 Heval val Hval old_conn_map Hinit conn_map Hexpand_branches.
    simpl in Heval. destruct (Sem_HiFP.eval_hfstmt st rs0 s0 init_s tmap) as [[rs_temp s_temp]|] eqn : Heval_temp; try discriminate.
    simpl in Hexpand_branches. destruct (ExpandBranch_fun st old_conn_map) as [temp_conn_map|] eqn : Hexpand_branches_temp; try discriminate.
    move : Hexpand_branches; apply IH with (rs := rs) (s := s) (rs0 := rs_temp) (s0 := s_temp); try done.
    (* find temp *)
    clear IH Heval conn_map sts s. 
    case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st.
    + (* skip, wire *) 1,2,4,5 : 
      simpl in Hexpand_branches_temp; inversion Hexpand_branches_temp; subst old_conn_map; clear Hexpand_branches_temp;
      simpl in Heval_temp; inversion Heval_temp; subst rs0 s0; clear Heval_temp; apply Hinit; done.
    + (* reg *) 
      simpl in Hexpand_branches_temp. destruct (type reg); try discriminate. inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      simpl in Heval_temp. destruct (PVM.find var init_s) as [val_temp|] eqn : Hval_temp; try discriminate. inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. intros bs Hfind.
      destruct (v == var) eqn : Heq.
      move /eqP : Heq => Heq; subst v. rewrite PVM.Lemmas.find_add_eq. rewrite PVM.Lemmas.find_add_eq in Hfind. inversion Hfind; subst bs. simpl; done. 1,2 : apply PVM.M.SE.eq_refl.
      rewrite PVM.Lemmas.find_add_neq. rewrite PVM.Lemmas.find_add_neq in Hfind. apply Hinit; done.
      1,2 : move /eqP : Heq => Heq; move : Heq; apply contra_not; intro; unfold CEP.SE.eq in H; move /eqP : H => H; done.
    + (* node *) 
      simpl in Hexpand_branches_temp. inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      simpl in Heval_temp. destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate. inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. done. 
    + (* fcnct *) 
      simpl in Hexpand_branches_temp. case Href : ref => [var|||]; subst ref; try discriminate. inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      destruct (v == var) eqn : Heq.
      * move /eqP : Heq => Heq; subst var. rewrite HiFP.PCELemmas.find_add_eq.
        simpl in Heval_temp. rewrite Hcmpnt in Heval_temp. destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val_e|]; try discriminate.
        inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq //.
        1,2 : apply CEP.SE.eq_refl.
      * rewrite HiFP.PCELemmas.find_add_neq. 
        simpl in Heval_temp. destruct (PVM.find var tmap) as [[gt_var cmpnt_var]|]; try discriminate.
        destruct cmpnt_var; destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val_e|]; try discriminate; inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp;
        try rewrite HiFP.PCELemmas.find_add_neq; try done. 1-2 : move /eqP : Heq => Heq; move : Heq; apply contra_not; intro; unfold CEP.SE.eq in H; move /eqP : H => H; subst v; done.
    + (* invalid *) 
      simpl in Hexpand_branches_temp. case Href : ref => [var|||]; subst ref; try discriminate. destruct (PVM.find var tmap) as [[gt' cmpnt]|]; try discriminate.
      inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp. 
      destruct (v == var) eqn : Heq.
      * move /eqP : Heq => Heq; subst var. rewrite HiFP.PCELemmas.find_add_eq; try apply CEP.SE.eq_refl.
        simpl in Heval_temp. rewrite Hcmpnt in Heval_temp. destruct (sizeof_fgtyp gt < length indeterminate_val).
        - (* take *)
          inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq.
          intros. inversion H; done. apply CEP.SE.eq_refl.
        - (* ext *)
          inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq.
          intros. inversion H; done. apply CEP.SE.eq_refl.
      * rewrite HiFP.PCELemmas.find_add_neq. 
        simpl in Heval_temp. destruct (PVM.find var tmap) as [[gt_var cmpnt_var]|]; try discriminate.
        destruct cmpnt_var; destruct (sizeof_fgtyp gt_var < length indeterminate_val); inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp; try done.
        1,2 : rewrite HiFP.PCELemmas.find_add_neq; try done.
        1-3 : move /eqP : Heq => Heq; move : Heq; apply contra_not; intro; unfold CEP.SE.eq in H; move /eqP : H => H; subst v; done. 
    + (* when *)
      simpl in Hexpand_branches_temp. destruct (ExpandBranches_funs ss_true old_conn_map tmap) as [true_conn_map|] eqn : Hexpand_true; try discriminate.
      destruct (ExpandBranches_funs ss_false old_conn_map tmap) as [false_conn_map|] eqn : Hexpand_false; try discriminate. 
      inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp. 
      specialize (eval_hfstmt_ExpandBranches_funs_find_for_sequ_helper _ _ _ _ _ Hcmpnt _ _ _ _ Heval_temp _ Hinit) as Hwhen; simpl in Hwhen;
        clear eval_hfstmt_ExpandBranches_funs_find_for_sequ_helper. specialize (Hwhen _ _ Hexpand_true Hexpand_false). done.

  clear eval_hfstmt_ExpandBranches_funs_find_for_sequ_helper. intro Hcmpnt.
  intros rs_temp s_temp rs0 s0 Heval old_conn_map Hinit.
  case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st; try done. intros true_conn_map false_conn_map Hexpand_true Hexpand_false val Hval.
  simpl in Heval. destruct (Sem_HiFP.eval_hfexpr cond init_s tmap) as [valc|] eqn : Hvalc; try discriminate. destruct (~~ is_zero valc) eqn : Hcond.
  - (* when go to true *)
    clear Hexpand_false. 
    specialize (eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper _ _ _ _ Hcmpnt _ _ _ _ _ Heval _ Hval _ Hinit _ Hexpand_true) as Htrue; 
      clear eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper. unfold combine_when_connections. rewrite PVM.Lemmas.F.map2_1bis; try done.
    destruct (PVM.find v true_conn_map) as [de_true|] eqn : Hde_true; try done. destruct de_true as [gt_e_true|e_true].
    + (* true is invlid *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false.
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        apply eval_invalid_is_allowed.
      * (* false is cnct *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        apply eval_invalid_is_allowed.
    + (* true is cnct *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false as [gt_e_false|e_false].
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
      * (* false is cnct *) destruct (e_true == e_false) eqn : Heq; try done.
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
  - (* when go to false *)
    clear Hexpand_true. 
    specialize (eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper _ _ _ _ Hcmpnt _ _ _ _ _ Heval _ Hval _ Hinit _ Hexpand_false) as Hfalse; 
      clear eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper. unfold combine_when_connections. rewrite PVM.Lemmas.F.map2_1bis; try done.
    destruct (PVM.find v true_conn_map) as [de_true|] eqn : Hde_true; try done. destruct de_true as [gt_e_true|e_true].
    + (* true is invlid *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false.
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        apply eval_invalid_is_allowed.
      * (* false is cnct *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
    + (* true is cnct *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false as [gt_e_false|e_false].
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        apply eval_invalid_is_allowed.
      * (* false is cnct *) destruct (e_true == e_false) eqn : Heq. move /eqP : Heq => Heq; subst e_true. done.
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
Admitted.

Lemma eval_hfstmts_ExpandBranches_funs_find_for_sequ ss init_s tmap rs s v : 
  match PVM.find v tmap with
  | Some (gt, Register) => 
  Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
  forall val, PVM.find v rs = Some val ->
  forall conn_map, ExpandBranches_funs ss (PVM.empty def_expr) tmap = Some conn_map -> 
      match PVM.find v conn_map with
      | Some (D_fexpr e) => Sem_HiFP.eval_hfexpr e init_s tmap = Some val
      | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val
          else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val
      | _ => False
      end
  | _ => True
  end.
Proof.
  destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt; try done. destruct cmpnt; try done.
  intros. move : conn_map H1; apply (eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper Hcmpnt H H0).
  try done.
Qed. 

Lemma pvm_included_refl valmap : pvm_included valmap valmap.
Proof. 
  unfold pvm_included. intros; done.
Qed.

Lemma func_type_included_eval_hfstmts mv pp ss conn_map tmap : Sem_HiFP.module_tmap (PVM.empty (fgtyp * fcomponent))
  (FInmod mv pp ss) = Some tmap -> ExpandBranches_funs ss (PVM.empty def_expr) tmap = Some conn_map -> 
  func_type_included (Sem_HiFP.eval_hfstmts ss) (Sem_HiFP.eval_hfstmts (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))) tmap.
Proof.
  intros Htmap Hexpand_branches.
  unfold func_type_included. intros init_s1 init_s2 s1 s2 rs1 rs2 Hinit_eq Hevalss1 Hevalss2. split.
  - (* combinational part *)
    move : Hevalss1 Hevalss2 Hexpand_branches Htmap Hinit_eq; clear. intros Hevalss1 Hevalss2 Hexpand_branches Htmap Hinit_eq v.
    destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt. destruct cmpnt.
    * (* inport *) 
      specialize (eval_hfstmts_find_none_cases v Hevalss1) as Hfind1; rewrite Hcmpnt in Hfind1; move : Hfind1 => [Hfind1 _].
      intros; rewrite Hfind1 in H; discriminate.
    * (* instance of *) 
      specialize (eval_hfstmts_find_none_cases v Hevalss1) as Hfind1; rewrite Hcmpnt in Hfind1; move : Hfind1 => [Hfind1 _].
      intros; rewrite Hfind1 in H; discriminate.
    * (* memory *) 
      specialize (eval_hfstmts_find_none_cases v Hevalss1) as Hfind1; rewrite Hcmpnt in Hfind1; move : Hfind1 => [Hfind1 _].
      intros; rewrite Hfind1 in H; discriminate.
    * (* node : v的值在 component_stmts_of 中 *) intros bs Hfind1.
      specialize (find_node_qin_with_cond Htmap Hcmpnt Hevalss1 Hfind1) as He. destruct He as [e He].
      assert (Hunique : unique_node_dclr_when ss). specialize (well_formedness ss) with (tmap := tmap) as [Hwell_formed _]; done.
      assert (He' : Qin (Snode v e) (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))). 
      specialize (qin_with_cond_node_qin_cmpnt He) as Hin. apply Qin_Qcat; left; done.
      assert (Hunique' : unique_node_dclr (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))). 
      specialize (well_formedness (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))) with (tmap := tmap) as [_ [Hwell_formed _]]; done.
      rewrite (eval_hfstmts_for_unique_node He Hunique Hevalss1) in Hfind1.
      assert (Hwhen : forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))).
        intros. intro. apply Qin_Qcat in H. destruct H. specialize (component_stmts_of_is_declaration H); simpl; done.
        specialize (convert_to_connect_stmts_is_connection H); simpl; done.
      rewrite (eval_hfstmts_for_unique_node' He' Hunique' Hwhen Hevalss2).
      move : Hinit_eq Hfind1; apply eval_fexpr_PVM_included_eq.
    * (* outport *) 
      specialize (eval_hfstmts_Qcat_some' (PVM.empty bits) (PVM.empty bits) Hevalss2) as Hexists. destruct Hexists as [[rs s] Hexists].
      specialize eval_hfstmts_for_comb_only_cnct with (v := v) (tmap := tmap) as Hcnct. rewrite Hcmpnt in Hcnct.
      assert (Hin : forall s, Qin s (component_stmts_of ss) -> is_declaration s) by (apply component_stmts_of_is_declaration).
      assert (Hneq : forall v' e', Qin (Snode v' e') (component_stmts_of ss) -> v <> v'). 
      specialize (well_formedness (component_stmts_of ss)) with (tmap := tmap) as [_ [_ Hwell_formed]]. 
      intros v' e'; apply Hwell_formed with (gt := gt). left; done.
      assert (Hwhen : forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))). 
        intros. intro. apply Qin_Qcat in H. destruct H. specialize (component_stmts_of_is_declaration H); simpl; done.
        specialize (convert_to_connect_stmts_is_connection H); simpl; done.
      specialize (Hcnct _ _ _ Hin Hneq Hwhen _ _ Hevalss2 _ _ Hexists). rewrite -Hcnct; clear Hcnct Hevalss2.
      specialize eval_hfstmts_convert_to_connect_stmts_for_comb with (v := v) (tmap := tmap) as Hconvert. rewrite Hcmpnt in Hconvert.
      specialize (Hconvert _ _ _ _ Hexists). clear Hexists.
      specialize eval_hfstmts_ExpandBranches_funs_find_for_comb with (v := v) (tmap := tmap) as Hhelper.
      rewrite Hcmpnt in Hhelper. 
      assert (Hnotin : ~ (exists r : hfreg ProdVarOrder.T, Qin (Sreg v r) ss) /\ ~ (exists e : hfexpr ProdVarOrder.T, Qin (Snode v e) ss)). 
        specialize (well_formedness ss tmap) as [_ [_ [_ [_ [H]]]]]. split; try apply H; try apply H0.
      intros val Hval; specialize (Hhelper _ _ _ _ Hnotin Hevalss1 _ Hval _ Hexpand_branches). 
      destruct (PVM.find v conn_map) as [dexpr|] eqn : Hcm; try done. destruct dexpr as [gt_e|e] eqn : Hde; subst dexpr.
      (* invalid *)
      destruct (sizeof_fgtyp gt < length indeterminate_val).
      1,2 : rewrite -Hconvert Hhelper //.
      (* cnct *)
      rewrite -Hconvert. move : Hhelper; apply eval_fexpr_PVM_included_eq; done.
    * (* register *) 
      specialize (eval_hfstmts_find_none_cases v Hevalss1) as Hfind1; rewrite Hcmpnt in Hfind1.
      intros; rewrite Hfind1 in H; discriminate.
    * (* wire : 同 outport *) 
      specialize (eval_hfstmts_Qcat_some' (PVM.empty bits) (PVM.empty bits) Hevalss2) as Hexists. destruct Hexists as [[rs s] Hexists].
      specialize eval_hfstmts_for_comb_only_cnct with (v := v) (tmap := tmap) as Hcnct. rewrite Hcmpnt in Hcnct.
      assert (Hin : forall s, Qin s (component_stmts_of ss) -> is_declaration s) by (apply component_stmts_of_is_declaration).
      assert (Hneq : forall v' e', Qin (Snode v' e') (component_stmts_of ss) -> v <> v'). 
        specialize (well_formedness (component_stmts_of ss) tmap) as [_ [_ [H _]]].
        intros v' e'; apply H with (gt := gt). right; done.
      assert (Hwhen : forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))). 
        intros. intro. apply Qin_Qcat in H. destruct H. specialize (component_stmts_of_is_declaration H); simpl; done.
        specialize (convert_to_connect_stmts_is_connection H); simpl; done.
      specialize (Hcnct _ _ _ Hin Hneq Hwhen _ _ Hevalss2 _ _ Hexists). rewrite -Hcnct; clear Hcnct Hevalss2.
      specialize eval_hfstmts_convert_to_connect_stmts_for_comb with (v := v) (tmap := tmap) as Hconvert. rewrite Hcmpnt in Hconvert.
      specialize (Hconvert _ _ _ _ Hexists). clear Hexists.
      specialize eval_hfstmts_ExpandBranches_funs_find_for_comb with (v := v) (tmap := tmap) as Hhelper.
      rewrite Hcmpnt in Hhelper. 
      assert (Hnotin : ~ (exists r : hfreg ProdVarOrder.T, Qin (Sreg v r) ss) /\ ~ (exists e : hfexpr ProdVarOrder.T, Qin (Snode v e) ss)). 
        specialize (well_formedness ss tmap) as [_ [_ [_ [_ [H]]]]].
        split; try apply H; try apply H0; try done.
      intros val Hval; specialize (Hhelper _ _ _ _ Hnotin Hevalss1 _ Hval _ Hexpand_branches). 
      destruct (PVM.find v conn_map) as [dexpr|] eqn : Hcm; try done. destruct dexpr as [gt_e|e] eqn : Hde; subst dexpr.
      (* invalid *)
      destruct (sizeof_fgtyp gt < length indeterminate_val).
      1,2 : rewrite -Hconvert Hhelper //.
      (* cnct *)
      rewrite -Hconvert. move : Hhelper; apply eval_fexpr_PVM_included_eq; done.
    * (* module *) 
      specialize (eval_hfstmts_find_none_cases v Hevalss1) as Hfind1; rewrite Hcmpnt in Hfind1; move : Hfind1 => [Hfind1 _].
      intros; rewrite Hfind1 in H; discriminate.
    * (* None *) 
      specialize (eval_hfstmts_find_none_cases v Hevalss1) as Hfind1; rewrite Hcmpnt in Hfind1; move : Hfind1 => [Hfind1 _].
      intros; rewrite Hfind1 in H; discriminate.

  - (* sequential part *)
    move : Hevalss1 Hevalss2 Hexpand_branches Htmap Hinit_eq; clear. intros Hevalss1 Hevalss2 Hexpand_branches Htmap Hinit_eq v.
    destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt. destruct cmpnt.
    * (* inport, instance of, memory, node, output, wire, module, none *) 
      1,2,3,8,9 : 
      specialize (eval_hfstmts_find_none_cases v Hevalss1) as Hfind1; rewrite Hcmpnt in Hfind1; move : Hfind1 => [_ Hfind1];
      intros; rewrite Hfind1 in H; discriminate.
      1,2,4 : specialize (eval_hfstmts_find_none_cases v Hevalss1) as Hfind1; rewrite Hcmpnt in Hfind1;
      intros; rewrite Hfind1 in H; discriminate.
    * (* register *) 
      specialize (eval_hfstmts_Qcat_some' (PVM.empty bits) (PVM.empty bits) Hevalss2) as Hexists. destruct Hexists as [[rs s] Hexists].
      specialize eval_hfstmts_for_sequ_only_cnct with (v := v) (tmap := tmap) as Hcnct. rewrite Hcmpnt in Hcnct.
      assert (Hdclr : forall s, Qin s (component_stmts_of ss) -> is_declaration s) by (apply component_stmts_of_is_declaration).
      assert (Hin : Qin (Sfcnct (Eid v) (Eref (Eid v))) (convert_to_connect_stmts conn_map) \/
        (exists e : hfexpr ProdVarOrder.T, Qin (Sfcnct (Eid v) e) (convert_to_connect_stmts conn_map))).
        specialize (well_formedness ss tmap) as [_ [_ [_ [H _]]]]. apply H.
      specialize (Hcnct _ _ _ Hdclr Hexpand_branches Hin _ _ Hevalss2 _ _ Hexists). rewrite -Hcnct; clear Hcnct Hevalss2.
      specialize eval_hfstmts_convert_to_connect_stmts_for_sequ with (v := v) (tmap := tmap) as Hconvert. rewrite Hcmpnt in Hconvert.
      specialize (Hconvert _ _ _ _ Hexists). clear Hexists.
      specialize eval_hfstmts_ExpandBranches_funs_find_for_sequ with (v := v) (tmap := tmap) as Hhelper.
      rewrite Hcmpnt in Hhelper. 
      intros val Hval; specialize (Hhelper _ _ _ _ Hevalss1 _ Hval _ Hexpand_branches). 
      destruct (PVM.find v conn_map) as [dexpr|] eqn : Hcm; try done. destruct dexpr as [gt_e|e] eqn : Hde; subst dexpr.
      (* invalid *)
      destruct (sizeof_fgtyp gt < length indeterminate_val).
      1,2 : rewrite -Hconvert Hhelper //.
      (* cnct *)
      rewrite -Hconvert. move : Hhelper; apply eval_fexpr_PVM_included_eq; done.
Qed.

Theorem Sem_preservation_expandWhens : 
(* Proves pass expandWhens preserves the semantics *)
  forall (c : HiFP.hfcircuit) (inputs reg_init : PVM.t bits),
  match Sem_HiFP.compute_Sem c inputs reg_init with
  | Some (sem, regval) =>
      forall (newc : HiFP.hfcircuit),
      expandWhens c = Some newc ->
      match Sem_HiFP.compute_Sem newc inputs reg_init with
      | Some (sem_new, regval_new) => pvm_included sem sem_new /\
                                      pvm_included regval regval_new
      | _ => true
      end
  | _ => true
  end.
Proof.
  intros. destruct (Sem_HiFP.compute_Sem c inputs) as [[sem regval]|] eqn : Hsem; try done.
  intros. destruct (Sem_HiFP.compute_Sem newc inputs) as [[sem_new regval_new]|] eqn : Hsem_new; try done.
  unfold Sem_HiFP.compute_Sem in *. unfold expandWhens in *. unfold Sem_HiFP.circuit_tmap in *.
  destruct c as [cv ml] eqn : Hcir; subst c.
  destruct ml as [|m ml0]; try discriminate. destruct ml0; try discriminate. simpl in *.
  destruct (Sem_HiFP.module_tmap (PVM.empty (fgtyp * fcomponent)) m) as [tmap|] eqn : Htmap; try discriminate.
  destruct (ExpandWhens_fun m) as [fm|] eqn: Hpass; try discriminate. inversion H; subst newc. clear H.
  rewrite /Sem_HiFP.modules_tmap in Hsem_new.
  specialize (ExpandWhens_fun_tmap_eq Htmap) as Htmap_new. rewrite (Htmap_new _ Hpass) in Hsem_new. clear Htmap_new.
  unfold ExpandWhens_fun in *. destruct m as [mv pp ss|] eqn : Hm; try discriminate.
  destruct (ExpandBranches_funs ss (PVM.empty def_expr)) as [conn_map|] eqn : Hexpand_branches; try discriminate.
  inversion Hpass; subst fm. clear Hpass.
  rewrite component_stmts_of_init_dclrs_eq in Hsem_new.
  destruct (Sem_HiFP.init_dclrs ss (Sem_HiFP.update_values reg_init inputs) tmap) as [init_s|] eqn : Hinit_s; try discriminate.
  destruct (Sem_HiFP.iterate n (Sem_HiFP.eval_hfstmts ss) init_s tmap) as [s0|] eqn : Hiter; try discriminate.
  destruct (Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) s0 tmap) as [[rs ns]|] eqn : Hregval; try discriminate. inversion Hsem; subst s0 rs; clear Hsem.
  destruct (Sem_HiFP.iterate n
               (Sem_HiFP.eval_hfstmts (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map)))
               init_s tmap) as [s0|] eqn : Hiter_new; try discriminate.
  destruct (Sem_HiFP.eval_hfstmts (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))
               (PVM.empty bits) (PVM.empty bits) s0 tmap) as [[rs ns_new]|] eqn : Hregval_new; try discriminate. inversion Hsem_new; subst s0 rs; clear Hsem_new.
  clear Hinit_s.
  assert (Hfst_do_this : pvm_included sem sem_new). { 
    move : Hiter Hiter_new; apply iterate_func_included.
    apply func_type_included_eval_hfstmts with (mv := mv) (pp := pp); try done. apply pvm_included_refl. }
  (* proof the equivalence of registers' next state values *)
  split; try done.
  specialize func_type_included_eval_hfstmts as Hhelper. apply Hhelper with (tmap := tmap) (mv := mv) (pp := pp) in Hexpand_branches; try done. clear Hhelper.
  unfold func_type_included in Hexpand_branches. apply (Hexpand_branches _ _ _ _ _ _ Hfst_do_this Hregval) in Hregval_new.
  move : Hregval_new => [_ Hregval_new]. done.
Qed.*)