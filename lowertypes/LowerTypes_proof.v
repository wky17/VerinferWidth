From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From firrtl Require Import Env HiEnv LoFirrtl HiFirrtl.
From Lib Require Import Nbits Var.
From Semantics Require Import Semantics.


Fixpoint qall (f : HiFP.hfstmt -> bool) (sts: HiFP.hfstmt_seq) : bool :=
  match sts with
  | Qnil => true
  | Qcons s ss => f s && qall f ss
  end.


Lemma qcat_qcons:
  forall s1 (x :  HiFP.hfstmt) s2,
    Qcat (Qcons x s1) s2 = Qcons x (Qcat s1 s2).
Proof.
  elim => [| s1 ss1 IH1].
  - rewrite /=//.
  - move => x s2. rewrite IH1//.
Qed.
                        
Lemma qall_qcons : forall (f : HiFP.hfstmt -> bool) s ss,
    f s /\ qall f ss <-> qall f (Qcons s ss) .
Proof.
  move => f s ss. split.
  - move => [Hs Hss] /=. rewrite Hs Hss//.
  - rewrite /= => /andP //.
Qed.

Lemma qall_qcat : forall ss1 (f : HiFP.hfstmt -> bool) ss2,
    qall f (Qcat ss1 ss2)  <-> qall f ss1 /\ qall f ss2.
Proof.
  elim => [| s1 ss1 IH1]. split.
  - rewrite /= => Hss2. rewrite Hss2//.
  - rewrite /=. move => [_ Hss2] //.
    split.
  - rewrite qcat_qcons/= => /andP [Hs Hss].
    rewrite Hs andTb. by apply IH1.
  - rewrite qcat_qcons/=. move => [/andP [Hs1 Hss1] H2].
    rewrite Hs1 andTb. by apply IH1.
Qed.    

Lemma qall_qrcons : forall (f : HiFP.hfstmt -> bool) s ss,
    f s /\ qall f ss <-> qall f (Qrcons ss s) .
Proof.
  move => f s ss. rewrite -Qcats1 qall_qcat/=. split.
  - move => [Hs Hss]. rewrite  Hs Hss //.
  - rewrite andbT// and_comm//.
Qed.

Fixpoint iter_acc (n : nat) (f : nat -> HiFP.hfstmt_seq -> HiFP.hfstmt_seq) (offset' acc : nat) (l' : HiFP.hfstmt_seq) :=
        match n with
        | 0 => l'
        | n'.+1 => iter_acc n' f (offset' + acc) acc (f offset' l')
        end .

Lemma iter_acc_Sr: forall n f o a l,
    iter_acc n.+1 f o a l = iter_acc n f (o+a) a (f o l).
Proof.
  elim => [| ns IHn] f o a l;
  rewrite/=//.
Qed.

Inductive hvalue2bits : option (VM.t hvalue * VM.t hvalue) -> option (PVM.t bits * PVM.t bits) -> Prop :=
| nonev : forall bs, hvalue2bits None bs
| noneb : forall vs, hvalue2bits vs None
| somev_someb : forall v b,
    
    hvalue2bits (Some v) (Some b).

Inductive flatten_sem_rel : PVM.t bits -> PVM.t bits -> Prop :=
| flatten_rs : forall hv rs1 bs1 rs2 bs2, hvalue2bits (Some hv) (Some (rs1, bs1)) -> hvalue2bits (Some hv) (Some (rs2, bs2)) -> flatten_sem_rel rs1 rs2
| flatten_bs : forall hv rs1 bs1 rs2 bs2, hvalue2bits (Some hv) (Some (rs1, bs1)) -> hvalue2bits (Some hv) (Some (rs2, bs2)) -> flatten_sem_rel bs1 bs2.

Fixpoint expand_wire' (v : VarOrder.t) (ft : ftype) (offset : nat) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  match ft with 
  | Gtyp _ => HiFP.qrcons sts (HiFP.swire (v, N.of_nat offset) ft)
  | Atyp atyp n => 
      iter_acc n (expand_wire' v atyp) offset (size_of_ftype atyp) sts
  | Btyp btyp => expand_wire_btyp' v offset btyp sts
  end
with expand_wire_btyp' (v : VarOrder.t) (offset : nat) (btyp : ffield) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  match btyp with
  | Fnil => sts
  | Fflips _ _ ft ff => expand_wire_btyp' v (offset + (size_of_ftype ft)) ff (expand_wire' v ft offset sts)
  end.

Fixpoint expand_invalid' (n : nat) (pv : ProdVarOrder.t) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  match n with
  | 0 => sts
  | S n' => expand_invalid' n' (fst pv, N.add (snd pv) 1%num) (HiFP.qrcons sts (HiFP.sinvalid (Eid pv)))
  end.

Fixpoint lowertypes_stmt' (s : HiF.hfstmt) (tmap : VM.t (ftype * fcomponent)) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match s with
  | Sskip 
  | Smem _ _ => Some (HiFP.qrcons sts HiFP.sskip) (* TBD *)
  | Sinst v mv => Some (HiFP.qrcons sts (HiFP.sinst (v, N0) (mv, N0)))
  | Swire v t => Some (expand_wire' v t 0 sts)
  | Sreg v r => expand_reg v r tmap sts
  | Sinvalid ref => match Sem_HiF.type_of_ref ref tmap, ref2pv ref tmap with
      | Some ft, Some pv => Some (expand_invalid' (size_of_ftype ft) pv sts)
      | _, _ => None
      end
  | Snode v e => match list_expr e tmap with
      | Some el => expand_node v 0 (rev el) sts
      | _ => None
      end
  | Sfcnct ref0 (Eref ref1) => match ref2pv ref0 tmap, ref2pv ref1 tmap, Sem_HiF.type_of_ref ref0 tmap with
      | Some pv0, Some pv1, Some ft => expand_fcnct pv0 pv1 0 false ft sts 
      | _, _, _ => None
      end
  | Sfcnct ref e => match ref2pv ref tmap, list_expr e tmap with
      | Some pv, Some el => expand_fcnct_nflip pv (rev el) sts
      | _,_ => None
      end
  | Swhen c ss1 ss2 => match expand_ground_expr c tmap, lowertypes_stmts' ss1 tmap HiFP.qnil, lowertypes_stmts' ss2 tmap HiFP.qnil with
      | Some c', Some ss1', Some ss2' => Some (HiFP.qrcons sts (Swhen c' ss1' ss2'))
      | _, _, _ => None
      end
  end
with lowertypes_stmts' (ss : HiF.hfstmt_seq) (tmap : VM.t (ftype * fcomponent)) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match ss with
  | Qnil => Some sts
  | Qcons s ss =>
    match lowertypes_stmt' s tmap sts with
    | Some sts' => lowertypes_stmts' ss tmap sts'
    | None => None
    end
  end.

    
Definition all_invs := qall (fun x => match x with | Sinvalid _ => true | _ => false end).

Lemma all_inv_expand_inv  : forall n pv sts,
    all_invs sts ->
    all_invs (expand_invalid' n pv sts).
Proof.
  elim => [| ns IHn].
  - rewrite /=//.
  - move => pv sts Hsts/=.
    apply IHn. rewrite -qall_qrcons/= -/all_invs Hsts//.
Qed.

(* Lemma expand_inv_comp : forall r tmap gt c sts sts', *)
(*     VM.find (r) tmap = Some (gt, c) -> *)
(*     lowertypes_stmt' (HiF.sinvalid (Eid r)) tmap sts = Some sts' -> *)
                          

Lemma eval_expand_inv : forall v rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match (lowertypes_stmt' (Sinvalid v) tmp HiFP.qnil) with
    | Some r => 
        hvalue2bits (Sem_HiF.eval_hfstmt (Sinvalid v) rs ns s tmp) (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end.
Proof.
  move => v rs ns s rs' ns' s' tmp tmp' Hhvtb/=.
  case Htypv : (Sem_HiF.type_of_ref v tmp) => [typv|]; rewrite//.
  case Hr2pv : (ref2pv v tmp) => [vr|]; rewrite//.
  case Hexp : (expand_invalid (size_of_ftype typv) vr HiFP.qnil) => [r|]; rewrite//.
  case Hosrv : (Sem_HiF.offset_ref v tmp 0) => [off|]; last apply nonev.
  case Hfdvt : (VM.find (HiF.base_ref v) tmp) => [[x f]|]; last apply nonev.
  case Hf : f;
  case Hfdvs : (VM.find (HiF.base_ref v) s) => [val|]; last apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                     (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|]; last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                     (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|]; last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                     (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|]; last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                     (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|]; last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                     (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|]; last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                     (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|]; last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                     (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|]; last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                     (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|]; last by apply nonev.
    + apply somev_someb. + apply noneb. 
case Hosrv : (Sem_HiF.offset_ref v tmp 0) => [off|]; last apply nonev.
  case Hfdvt : (VM.find (HiF.base_ref v) tmp) => [[x f]|]; last apply nonev.
  case Hf : f;
  case Hfdvs : (VM.find (HiF.base_ref v) s) => [val|]; last apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                         (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|];
                                                                                                 last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                     (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|]; last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                     (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|]; last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                         (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|];
                                                                                                 last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                     (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|]; last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                     (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|]; last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                         (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|];
                                                                                                 last by apply nonev.
    + apply somev_someb. + apply noneb. + apply nonev.
  - case Hupdhof: (Sem_HiF.update_hvalue_by_offset val off (Sem_HiF.invalidate_ft typv)) => [val'|]; 
    first case Hev : ((Sem_HiFP.eval_hfstmts
                         (expand_invalid' (size_of_ftype typv) vr HiFP.qnil) rs' ns' s' tmp')) =>[evrs'|];
                                                                                                 last by apply nonev.
    + apply somev_someb. + apply noneb.
Qed.

Lemma eval_wire_same : forall v t rs' ns' s' tmp',
    Sem_HiFP.eval_hfstmt (Swire v t) rs' ns' s' tmp' = Some (rs', ns').
Proof.
  rewrite //.
Qed.

Definition all_wires := qall (fun x => match x with | Swire _ _ => true | _ => false end).

Lemma eval_wires_same : forall (sts: HiFP.hfstmt_seq) rs ns s tmp,
    all_wires sts ->
    Sem_HiFP.eval_hfstmts sts rs ns s tmp = Some (rs, ns).
Proof.
  elim => [| s ss IHs] rs ns bs tmp.
  - rewrite //.
  - case s ; rewrite // /=.
    move => v t. apply IHs.
Qed.

Lemma all_wires_expand_wire' : forall f v o sts,
    all_wires sts ->
    all_wires (expand_wire' v f o sts)
with all_wires_expand_btyp_wire' : forall b v o sts,
    all_wires sts ->
    all_wires (expand_wire_btyp' v o b sts).
Proof.
  - elim.
    + rewrite /=//. move => f v o sts Hss.
      rewrite -qall_qrcons/= -/all_wires Hss//.
    + move => f IHt n /=.
      set a := (size_of_ftype f). move : a.
      elim n => [| ns IHn] v o a sts Hsts.
      * rewrite //.
      * rewrite iter_acc_Sr. apply IHn. by apply IHt.
      * rewrite /=. move => f v o sts. apply all_wires_expand_btyp_wire'.
  - elim.
    + rewrite //.
    + move => v f f0 f1 IHn v0 o sts Hsts/=.
      apply IHn.
      by apply all_wires_expand_wire'.
Qed.

(* Lemma expand_wire_all_wires : forall v t tmp r, *)
(*   (lowertypes_stmt' (Swire v t) tmp HiFP.qnil) = Some r -> *)
(*   all_wires r. *)
(* Proof. *)
(*   move => v t tmp r. rewrite /= => Hinj. *)
(*   injection Hinj => Hr. rewrite -Hr. *)
(*   by apply all_wires_expand_wire'.  *)
(* Qed. *)

Lemma eval_expand_wire : forall v t rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match (lowertypes_stmt' (Swire v t) tmp HiFP.qnil) with
    | Some r => 
        hvalue2bits (Sem_HiF.eval_hfstmt (Swire v t) rs ns s tmp) (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end.
Proof.
  move => v t rs ns s rs' ns' s' tmp tmp' Hhvbt/=.
  rewrite eval_wires_same//.
  by apply all_wires_expand_wire'.
Qed.


Lemma eval_expand_skip : forall rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match (lowertypes_stmt' (HiF.sskip) tmp HiFP.qnil) with
    | Some r => 
        hvalue2bits (Sem_HiF.eval_hfstmt HiF.sskip rs ns s tmp) (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end.
Proof.
  move => rs ns s rs' ns' s' tmp tmp' Hhvbt/=//.
Qed.

Lemma eval_expand_mem : forall v t rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match (lowertypes_stmt' (Smem v t) tmp HiFP.qnil) with
    | Some r => 
        hvalue2bits (Sem_HiF.eval_hfstmt (Smem v t) rs ns s tmp) (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end.
Proof.
  move => v t rs ns s rs' ns' s' tmp tmp' Hhvbt/=//.
Qed.

Lemma eval_expand_inst : forall v t rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match (lowertypes_stmt' (Sinst v t) tmp HiFP.qnil) with
    | Some r => 
        hvalue2bits (Sem_HiF.eval_hfstmt (Sinst v t) rs ns s tmp) (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end.
Proof.
  move => v t rs ns s rs' ns' s' tmp tmp' Hhvbt/=//.
Qed.


Lemma eval_expand_reg : forall v rg rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match (lowertypes_stmt' (Sreg v rg) tmp HiFP.qnil) with
    | Some r => 
        hvalue2bits (Sem_HiF.eval_hfstmt (Sreg v rg) rs ns s tmp) (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end.
Proof.
  move => v rg rs ns s rs' ns' s' tmp tmp' Hhvtb/=.
  case Htypv : (expand_reg v rg tmp HiFP.qnil) => [typv|]; rewrite/=//.
  case Hevst : (Sem_HiFP.eval_hfstmts typv rs' ns' s' tmp') => [val'|].
  - apply somev_someb.
  - apply noneb.
Qed.


Lemma eval_expand_node : forall v e rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match (lowertypes_stmt' (Snode v e) tmp HiFP.qnil) with
    | Some r => 
        hvalue2bits (Sem_HiF.eval_hfstmt (Snode v e) rs ns s tmp) (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end.
Proof.
  move => v e rs ns s rs' ns' s' tmp tmp' Hhvtb/=.
  case Hlexp : (list_expr e tmp) => [el|];
   last rewrite//.
  case Hexnd : (expand_node v 0 (rev el) HiFP.qnil) => [r|];
   last rewrite //.
  case Hevex : (Sem_HiF.eval_hfexpr e s tmp) => [val|];
   last apply nonev.
  case Hevst : (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp') => [a|].
  apply somev_someb. apply noneb.
Qed.                                                            

Lemma eval_expand_fcnctesub : forall esf f h1 rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match lowertypes_stmt' (Sfcnct (Esubfield esf f) h1) tmp HiFP.qnil with
    | Some r =>
        hvalue2bits (Sem_HiF.eval_hfstmt (Sfcnct (Esubfield esf f) h1) rs ns s tmp)
          (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end.
Proof.
  move => esf f h1 rs ns s rs' ns' s' tmp tmp' Hhvtb/=.
  case Hh1 : h1 => [fty b|u h|e h|e e1 e2|e e1 e2|h].
  - case Hrf2pv : (ref2pv (Esubfield esf f) tmp) => [pv|];
   last rewrite //.
    case Hlexp : (list_expr (Econst VarOrder.T fty b) tmp) => [el|] ;
   last rewrite //.
    case Hexcn : (expand_fcnct_nflip pv (rev el) HiFP.qnil) => [expd|];
   last rewrite //.
    case Hofref : (Sem_HiF.offset_ref esf tmp 0) => [os|];
   last apply nonev.
    case Htpref : (Sem_HiF.type_of_ref esf tmp) => [fs|];
   last apply nonev.
    case Hfs : fs => [gft||bft];
   try apply nonev.
    case Hauxbo : ((fix aux (fx : ffield) (acc : nat) {struct fx} : option nat :=
         match fx with
         | Fnil => None
         | Fflips v' _ ty fxs => if v' == f then Some (acc + 1) else aux fxs (acc + Sem_HiF.elements_of_ftype ty)
         end) bft os) => [a|];
   last apply nonev.
    case Hevex : (Sem_HiF.eval_hfexpr (Econst VarOrder.T fty b) s tmp) => [nv|];
   last apply nonev.
    case Hfdt : (VM.find (HiF.base_ref esf) tmp) => [[ft c]|];
   last apply nonev.
    case Hc : c;
  
    case Hfds : (VM.find (HiF.base_ref esf) s) => [val|];
   try apply nonev;
  
    case Hupd : (Sem_HiF.update_hvalue_by_offset val a nv) => [val'|];
   try apply nonev;
  
    case Hevst : ((Sem_HiFP.eval_hfstmts expd rs' ns' s' tmp')) => [evr|];
  
    (apply somev_someb|| apply noneb).
  - case Hrf2pv : (ref2pv (Esubfield esf f) tmp) => [pv|];
   last rewrite //.
    case Hlex : (list_expr (Ecast u h) tmp) => [el|];
   last rewrite //.
    case Hexpd : (expand_fcnct_nflip pv (rev el) HiFP.qnil)=> [expd|];
   last rewrite //.
    case Hofsr : (Sem_HiF.offset_ref esf tmp 0) => [os|];
   last apply nonev.
    case Htor : (Sem_HiF.type_of_ref esf tmp) => [ftyp|];
   last apply nonev.
    case Hftyp : ftyp => [gft||bft];
   try apply nonev.
    case Haux : ((fix aux (fx : ffield) (acc : nat) {struct fx} : option nat :=
         match fx with
         | Fnil => None
         | Fflips v' _ ty fxs =>
             if v' == f
             then Some (acc + 1)
             else aux fxs (acc + Sem_HiF.elements_of_ftype ty)
         end) bft os) => [a|];
   last apply nonev.
    case Hevex : (Sem_HiF.eval_hfexpr (Ecast u h) s tmp)=> [nv|];
   last apply nonev.
    case Hfdt : (VM.find (HiF.base_ref esf) tmp) => [[ft c]|];
   last apply nonev.
    case Hc : c;
  
    case Hfds : (VM.find (HiF.base_ref esf) s) => [val|];
   try apply nonev;
  
    case Hupd : (Sem_HiF.update_hvalue_by_offset val a nv) => [val'|];
   try apply nonev;
  
    case Hevst : ((Sem_HiFP.eval_hfstmts expd rs' ns' s' tmp')) => [evr|];
  
    (apply somev_someb|| apply noneb).
  - case Hrf2pv : (ref2pv (Esubfield esf f) tmp) => [pv|];
   last rewrite //.
    case Hlex : (list_expr (Eprim_unop e h) tmp) => [el|];
   last rewrite //.
    case Hexpd : (expand_fcnct_nflip pv (rev el) HiFP.qnil)=> [expd|];
   last rewrite //.
    case Hofsr : (Sem_HiF.offset_ref esf tmp 0) => [os|];
   last apply nonev.
    case Htor : (Sem_HiF.type_of_ref esf tmp) => [ftyp|];
   last apply nonev.
    case Hftyp : ftyp => [gft||bft];
   try apply nonev.
    case Haux : ((fix aux (fx : ffield) (acc : nat) {struct fx} : option nat :=
         match fx with
         | Fnil => None
         | Fflips v' _ ty fxs =>
             if v' == f
             then Some (acc + 1)
             else aux fxs (acc + Sem_HiF.elements_of_ftype ty)
         end) bft os) => [a|];
   last apply nonev.
    case Hevex : (Sem_HiF.eval_hfexpr (Eprim_unop e h) s tmp)=> [nv|];
   last apply nonev.
    case Hfdt : (VM.find (HiF.base_ref esf) tmp) => [[ft c]|];
   last apply nonev.
    case Hc : c;
  
    case Hfds : (VM.find (HiF.base_ref esf) s) => [val|];
   try apply nonev;
  
    case Hupd : (Sem_HiF.update_hvalue_by_offset val a nv) => [val'|];
   try apply nonev;
    case Hevst : ((Sem_HiFP.eval_hfstmts expd rs' ns' s' tmp')) => [evr|];
  
                                                                   (apply somev_someb|| apply noneb).
  - case Hrf2pv : (ref2pv (Esubfield esf f) tmp) => [pv|];
   last rewrite //.
    case Hlex : (list_expr (Eprim_binop e e1 e2) tmp) => [el|];
   last rewrite //.
    case Hexpd : (expand_fcnct_nflip pv (rev el) HiFP.qnil)=> [expd|];
   last rewrite //.
    case Hofsr : (Sem_HiF.offset_ref esf tmp 0) => [os|];
   last apply nonev.
    case Htor : (Sem_HiF.type_of_ref esf tmp) => [ftyp|];
   last apply nonev.
    case Hftyp : ftyp => [gft||bft];
   try apply nonev.
    case Haux : ((fix aux (fx : ffield) (acc : nat) {struct fx} : option nat :=
         match fx with
         | Fnil => None
         | Fflips v' _ ty fxs =>
             if v' == f
             then Some (acc + 1)
             else aux fxs (acc + Sem_HiF.elements_of_ftype ty)
         end) bft os) => [a|];
   last apply nonev.
    case Hevex : (Sem_HiF.eval_hfexpr (Eprim_binop e e1 e2) s tmp)=> [nv|];
   last apply nonev.
    case Hfdt : (VM.find (HiF.base_ref esf) tmp) => [[ft c]|];
   last apply nonev.
    case Hc : c;
    case Hfds : (VM.find (HiF.base_ref esf) s) => [val|];
   try apply nonev;
    case Hupd : (Sem_HiF.update_hvalue_by_offset val a nv) => [val'|];
   try apply nonev;
    case Hevst : ((Sem_HiFP.eval_hfstmts expd rs' ns' s' tmp')) => [evr|];
                                                                   (apply somev_someb|| apply noneb).
  - case Hrf2pv : (ref2pv (Esubfield esf f) tmp) => [pv|];
   last rewrite //.
    case Hlex : (list_expr (Emux e e1 e2) tmp) => [el|];
   last rewrite //.
    case Hexpd : (expand_fcnct_nflip pv (rev el) HiFP.qnil)=> [expd|];
   last rewrite //.
    case Hofsr : (Sem_HiF.offset_ref esf tmp 0) => [os|];
   last apply nonev.
    case Htor : (Sem_HiF.type_of_ref esf tmp) => [ftyp|];
   last apply nonev.
    case Hftyp : ftyp => [gft||bft];
   try apply nonev.
    case Haux : ((fix aux (fx : ffield) (acc : nat) {struct fx} : option nat :=
         match fx with
         | Fnil => None
         | Fflips v' _ ty fxs =>
             if v' == f
             then Some (acc + 1)
             else aux fxs (acc + Sem_HiF.elements_of_ftype ty)
         end) bft os) => [a|];
   last apply nonev.
    case Hevex : (Sem_HiF.eval_hfexpr (Emux e e1 e2) s tmp)=> [nv|];
   last apply nonev.
    case Hfdt : (VM.find (HiF.base_ref esf) tmp) => [[ft c]|];
   last apply nonev.
    case Hc : c;
    case Hfds : (VM.find (HiF.base_ref esf) s) => [val|];
   try apply nonev;
    case Hupd : (Sem_HiF.update_hvalue_by_offset val a nv) => [val'|];
   try apply nonev;
    case Hevst : ((Sem_HiFP.eval_hfstmts expd rs' ns' s' tmp')) => [evr|];
                                                                   (apply somev_someb|| apply noneb).
  - case Hrf2pv : (ref2pv (Esubfield esf f) tmp) => [pv|];
   last rewrite //.
    case Hrf2pvh : (ref2pv h tmp) => [pv1|];
   last rewrite //.
    case Htor : (Sem_HiF.type_of_ref esf tmp) => [ftyp|];
   last rewrite //.
    case Hftyp : ftyp => [gft||bft];
   rewrite //.
    case Haux : (      (fix aux (fx : ffield) : option ftype :=
         match fx with
         | Fnil => None
         | Fflips v' _ t fxs => if f == v' then Some t else aux fxs
         end) bft) => [a|];
   last rewrite //.
    case Hexpfc : (expand_fcnct pv pv1 0 false a HiFP.qnil) => [r|];
   rewrite //.
    case Hofsrf : (Sem_HiF.offset_ref esf tmp 0) => [os|];
   last apply nonev.
    case Haux2 : ((fix aux (fx : ffield) (acc : nat) {struct fx} : option nat :=
         match fx with
         | Fnil => None
         | Fflips v' _ ty fxs =>
             if v' == f
             then Some (acc + 1)
             else aux fxs (acc + Sem_HiF.elements_of_ftype ty)
         end) bft os) => [ofsr|];
   last apply nonev.
    case Hofsrh : (Sem_HiF.offset_ref h tmp 0 ) => [ofstr|];
   last apply nonev.
    case Heqbs : (HiF.base_ref esf == HiF.base_ref h).
    + case Hfdt : (VM.find (HiF.base_ref esf) tmp) => [[ft c]|].
      * case Hfds : (VM.find (HiF.base_ref esf) s) => [val|];
   try apply nonev.
        case Hupd : (Sem_HiF.eval_ref_connection1 a val ofsr ofstr) => [val'|];
   last apply nonev.
        case Hc : c;
        case Hevst : ((Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')) => [evr|];
                                                                    (apply somev_someb|| apply noneb).
      * case Hfds : (VM.find (HiF.base_ref esf) s) => [val|];
   try apply nonev.
        case Hupd : (Sem_HiF.eval_ref_connection1 a val ofsr ofstr) => [val'|];
   apply nonev.
    + case Hfdt : (VM.find (HiF.base_ref esf) tmp) => [[ft c]|].
      * case Hfds : (VM.find (HiF.base_ref esf) s) => [val|];
   try apply nonev.
        case Hfdbs : (VM.find (HiF.base_ref h) s) => [valbr|];
   last apply nonev.
        case Hevrf : ( Sem_HiF.eval_ref_connection a val valbr ofsr ofstr) => [[valbr' valbrf]|];
   last apply nonev.
        case Hc : c;
        case Hevst : (VM.find (HiF.base_ref h) tmp) => [[evr evf]|]; try apply nonev;
        case Hevf : evf;
        case Hevsts : ((Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')) => [evr'|];
                                                                     (apply somev_someb|| apply noneb).
      * case Hfds : (VM.find (HiF.base_ref esf) s) => [val|];
   try apply nonev.
        case Hfdbr : (VM.find (HiF.base_ref h) s) => [valbr|];
   last apply nonev.
        case Hevrc : (Sem_HiF.eval_ref_connection a val valbr ofsr ofstr) => [[val1 val2]|];
   apply nonev.
Qed.

Lemma eval_expand_fcnctesubind : forall eind n h1 rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match lowertypes_stmt' (Sfcnct (Esubindex eind n) h1) tmp HiFP.qnil with
    | Some r =>
        hvalue2bits (Sem_HiF.eval_hfstmt (Sfcnct (Esubindex eind n) h1) rs ns s tmp)
          (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end.
Proof.
  move => eind n h1 rs ns s rs' ns' s' tmp tmp' Hhvtb/=.
  case Hh1 : h1 => [fty b|u h|e h|e e1 e2|e e1 e2|h].
  - case Hrf2pv : (ref2pv (Esubindex eind n) tmp) => [pv|];
   last rewrite //.
    case Hlexp : (list_expr (Econst VarOrder.T fty b) tmp) => [el|] ;
   last rewrite //.
    case Hexcn : (expand_fcnct_nflip pv (rev el) HiFP.qnil) => [expd|];
   last rewrite //.
    case Hofref : (Sem_HiF.offset_ref eind tmp 0) => [os|];
   last apply nonev.
    case Htpref : (Sem_HiF.type_of_ref eind tmp) => [fs|];
   last apply nonev.
    case Hfs : fs => [gft|ty na|bft];
   try apply nonev.
    case Hevex : (Sem_HiF.eval_hfexpr (Econst VarOrder.T fty b) s tmp) => [nv|];
   last apply nonev.
    case Hfdt : (VM.find (HiF.base_ref eind) tmp) => [[ft c]|];
   last apply nonev.
    case Hc : c;
    case Hfds : (VM.find (HiF.base_ref eind) s) => [val|];
   try apply nonev;
    case Hupd : (Sem_HiF.update_hvalue_by_offset val (os + n * Sem_HiF.elements_of_ftype ty + 1) nv) => [val'|];
   try apply nonev;
    case Hevst : ((Sem_HiFP.eval_hfstmts expd rs' ns' s' tmp')) => [evr|];
    (apply somev_someb|| apply noneb).
  - case Hrf2pv : (ref2pv (Esubindex eind n) tmp) => [pv|];
   last rewrite //.
    case Hlex : (list_expr (Ecast u h) tmp) => [el|];
   last rewrite //.
    case Hexpd : (expand_fcnct_nflip pv (rev el) HiFP.qnil)=> [expd|];
   last rewrite //.
    case Hofsr : (Sem_HiF.offset_ref eind tmp 0) => [os|];
   last apply nonev.
    case Htor : (Sem_HiF.type_of_ref eind tmp) => [ftyp|];
   last apply nonev.
    case Hftyp : ftyp => [gft|aty na|bft];
   try apply nonev.
    case Hevex : (Sem_HiF.eval_hfexpr (Ecast u h) s tmp)=> [nv|];
   last apply nonev.
    case Hfdt : (VM.find (HiF.base_ref eind) tmp) => [[ft c]|];
   last apply nonev.
    case Hc : c;
    case Hfds : (VM.find (HiF.base_ref eind) s) => [val|];
   try apply nonev;
    case Hupd : (Sem_HiF.update_hvalue_by_offset val (os + n * Sem_HiF.elements_of_ftype aty + 1) nv) => [val'|];
   try apply nonev;
    case Hevst : ((Sem_HiFP.eval_hfstmts expd rs' ns' s' tmp')) => [evr|];
    (apply somev_someb|| apply noneb).
  - case Hrf2pv : (ref2pv (Esubindex eind n) tmp) => [pv|];
   last rewrite //.
    case Hlex : (list_expr (Eprim_unop e h) tmp) => [el|];
   last rewrite //.
    case Hexpd : (expand_fcnct_nflip pv (rev el) HiFP.qnil)=> [expd|];
   last rewrite //.
    case Hofsr : (Sem_HiF.offset_ref eind tmp 0) => [os|];
   last apply nonev.
    case Htor : (Sem_HiF.type_of_ref eind tmp) => [ftyp|];
   last apply nonev.
    case Hftyp : ftyp => [gft|aty na|bft];
   try apply nonev.
    case Hevex : (Sem_HiF.eval_hfexpr (Eprim_unop e h) s tmp)=> [nv|];
   last apply nonev.
    case Hfdt : (VM.find (HiF.base_ref eind) tmp) => [[ft c]|];
   last apply nonev.
    case Hc : c;
    case Hfds : (VM.find (HiF.base_ref eind) s) => [val|];
   try apply nonev;
    case Hupd : (Sem_HiF.update_hvalue_by_offset val ((os + n * Sem_HiF.elements_of_ftype aty + 1)) nv) => [val'|];
   try apply nonev;
    case Hevst : ((Sem_HiFP.eval_hfstmts expd rs' ns' s' tmp')) => [evr|];
                                                                   (apply somev_someb|| apply noneb).
  - case Hrf2pv : (ref2pv (Esubindex eind n) tmp) => [pv|];
   last rewrite //.
    case Hlex : (list_expr (Eprim_binop e e1 e2) tmp) => [el|];
   last rewrite //.
    case Hexpd : (expand_fcnct_nflip pv (rev el) HiFP.qnil)=> [expd|];
   last rewrite //.
    case Hofsr : (Sem_HiF.offset_ref eind tmp 0) => [os|];
   last apply nonev.
    case Htor : (Sem_HiF.type_of_ref eind tmp) => [ftyp|];
   last apply nonev.
    case Hftyp : ftyp => [gft|aty na|bft];
   try apply nonev.
    case Hevex : (Sem_HiF.eval_hfexpr (Eprim_binop e e1 e2) s tmp)=> [nv|];
   last apply nonev.
    case Hfdt : (VM.find (HiF.base_ref eind) tmp) => [[ft c]|];
   last apply nonev.
    case Hc : c;
    case Hfds : (VM.find (HiF.base_ref eind) s) => [val|];
   try apply nonev;
    case Hupd : (Sem_HiF.update_hvalue_by_offset val (os + n * Sem_HiF.elements_of_ftype aty + 1) nv) => [val'|];
   try apply nonev;
    case Hevst : ((Sem_HiFP.eval_hfstmts expd rs' ns' s' tmp')) => [evr|];
                                                                   (apply somev_someb|| apply noneb).
  - case Hrf2pv : (ref2pv (Esubindex eind n) tmp) => [pv|];
   last rewrite //.
    case Hlex : (list_expr (Emux e e1 e2) tmp) => [el|];
   last rewrite //.
    case Hexpd : (expand_fcnct_nflip pv (rev el) HiFP.qnil)=> [expd|];
   last rewrite //.
    case Hofsr : (Sem_HiF.offset_ref eind tmp 0) => [os|];
   last apply nonev.
    case Htor : (Sem_HiF.type_of_ref eind tmp) => [ftyp|];
   last apply nonev.
    case Hftyp : ftyp => [gft|aty na|bft];
   try apply nonev.
    case Hevex : (Sem_HiF.eval_hfexpr (Emux e e1 e2) s tmp)=> [nv|];
   last apply nonev.
    case Hfdt : (VM.find (HiF.base_ref eind) tmp) => [[ft c]|];
   last apply nonev.
    case Hc : c;
  
    case Hfds : (VM.find (HiF.base_ref eind) s) => [val|];
   try apply nonev;
    case Hupd : (Sem_HiF.update_hvalue_by_offset val (os + n * Sem_HiF.elements_of_ftype aty + 1) nv) => [val'|];
   try apply nonev;
    case Hevst : ((Sem_HiFP.eval_hfstmts expd rs' ns' s' tmp')) => [evr|];
                                                                   (apply somev_someb|| apply noneb).
  - case Hrf2pv : (ref2pv (Esubindex eind n) tmp) => [pv|];
   last rewrite //.
    case Hrf2pvh : (ref2pv h tmp) => [pv1|];
   last rewrite //.
    case Htor : (Sem_HiF.type_of_ref eind tmp) => [ftyp|];
   last rewrite //.
    case Hftyp : ftyp => [gft|aty na|bft];
   rewrite //.
    case Hexpfc : (expand_fcnct pv pv1 0 false aty HiFP.qnil) => [r|];
   rewrite //.
    case Hofsrf : (Sem_HiF.offset_ref eind tmp 0) => [os|];
   last apply nonev.
    case Hofsrh : (Sem_HiF.offset_ref h tmp 0 ) => [ofstr|];
   last apply nonev.
    case Heqbs : (HiF.base_ref eind == HiF.base_ref h).
    + case Hfdt : (VM.find (HiF.base_ref eind) tmp) => [[ft c]|].
      * case Hfds : (VM.find (HiF.base_ref eind) s) => [val|];
   try apply nonev.
        case Hupd : (Sem_HiF.eval_ref_connection1 aty val (os + n * Sem_HiF.elements_of_ftype aty + 1) ofstr) => [val'|];
   last apply nonev.
        case Hc : c;
        case Hevst : ((Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')) => [evr|];
                                                                    (apply somev_someb|| apply noneb).
      * case Hfds : (VM.find (HiF.base_ref eind) s) => [val|];
   try apply nonev.
        case Hupd : (Sem_HiF.eval_ref_connection1 aty val (os + n * Sem_HiF.elements_of_ftype aty + 1) ofstr) => [val'|];
   apply nonev.
    + case Hfdt : (VM.find (HiF.base_ref eind) tmp) => [[ft c]|].
      * case Hfds : (VM.find (HiF.base_ref eind) s) => [val|];
   try apply nonev.
        case Hfdbs : (VM.find (HiF.base_ref h) s) => [valbr|];
   last apply nonev.
        case Hevrf : ( Sem_HiF.eval_ref_connection aty val valbr (os + n * Sem_HiF.elements_of_ftype aty + 1) ofstr) => [[valbr' valbrf]|]; last apply nonev.
        case Hc : c;
        case Hevst : (VM.find (HiF.base_ref h) tmp) => [[evr evf]|];
   try apply nonev;
        case Hevf : evf;
        case Hevsts : ((Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')) => [evr'|];
                                                                     (apply somev_someb|| apply noneb).
      * case Hfds : (VM.find (HiF.base_ref eind) s) => [val|];
   try apply nonev.
        case Hfdbr : (VM.find (HiF.base_ref h) s) => [valbr|];
   last apply nonev.
        case Hevrc : (Sem_HiF.eval_ref_connection aty val valbr (os + n * Sem_HiF.elements_of_ftype aty + 1) ofstr) => [[val1 val2]|];
   apply nonev.
Qed.

Lemma eval_expand_fcnctesubacc : forall es ea h1 rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match (lowertypes_stmt' (Sfcnct (Esubaccess es ea) h1) tmp HiFP.qnil) with
    | Some r => 
        hvalue2bits (Sem_HiF.eval_hfstmt (Sfcnct (Esubaccess es ea) h1) rs ns s tmp) (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end.
Proof.
  move => eind n h1 rs ns s rs' ns' s' tmp tmp' Hhvtb/=.
  case Hh1 : h1 => [fty b|u h|e h|e e1 e2|e e1 e2|h]; rewrite //.
Qed.  

(* goal 3 (ID 708) is: *)
(*  match lowertypes_stmt' (Sfcnct (Esubaccess es ea) h1) tmp HiFP.qnil with *)
(*  | Some r => *)
(*      hvalue2bits (Sem_HiF.eval_hfstmt (Sfcnct (Esubaccess es ea) h1) rs ns s tmp) *)
(*        (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp') *)
(*  | None => True *)
(*  end *)

Lemma eval_expand_fcncteid : forall v e rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match (lowertypes_stmt' (Sfcnct (Eid v) e) tmp HiFP.qnil) with
    | Some r => 
        hvalue2bits (Sem_HiF.eval_hfstmt (Sfcnct (Eid v) e) rs ns s tmp) (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end.
Proof.
  move => v e rs ns s rs' ns' s' tmp tmp' Hhvtb/=.
  case He : e => [ref1 b|y h|e' h|e' h1 h2|c h1 h2|h].
  - case Hlex : (list_expr (Econst VarOrder.T ref1 b) tmp) => [el|];
      last rewrite //.
    case Hexfnf : (expand_fcnct_nflip (v, 0%num) (rev el) HiFP.qnil) => [rv|];
      last rewrite //.
    case Hevex : (Sem_HiF.eval_hfexpr (Econst VarOrder.T ref1 b) s tmp) => [new_val|];
      last apply nonev.
    case Hfdvt : (VM.find v tmp) => [[r ty]|];
      last apply nonev.
    case Hty : ty;
      case Hfdvs : (VM.find v s) => [a|] ;
                                    try apply nonev;
                                    case Hupd : (Sem_HiF.update_hvalue_by_offset a 0 new_val) => [a'|];
                                                                                                 (apply somev_someb || apply nonev|| rewrite /=);
                                                                                                 case Hev : (Sem_HiFP.eval_hfstmts rv rs' ns' s' tmp') => [v'|];
                                                                                                                                                          (apply somev_someb ||  apply noneb).
  - case Hlex : (list_expr (Ecast y h) tmp) => [el|];
      last rewrite //.
    case Hexfnf : (expand_fcnct_nflip (v, 0%num) (rev el) HiFP.qnil) => [rv|];
      last rewrite //.
    case Hevex : (Sem_HiF.eval_hfexpr (Ecast y h) s tmp) => [new_val|]; 
      last apply nonev.
    case Hfdvt : (VM.find v tmp) => [[r ty]|]; 
      last apply nonev.
    case Hty : ty; 
      case Hfdvs : (VM.find v s) => [a|] ; 
      try apply nonev; case Hupd : (Sem_HiF.update_hvalue_by_offset a 0 new_val) => [a'|]; 
      (apply somev_someb || apply nonev|| rewrite /=); 
      case Hev : (Sem_HiFP.eval_hfstmts rv rs' ns' s' tmp') => [v'|]; 
      (apply somev_someb ||  apply noneb).
  - case Hlex : (list_expr (Eprim_unop e' h) tmp) => [el|]; 
      last rewrite //.
    case Hexfnf : (expand_fcnct_nflip (v, 0%num) (rev el) HiFP.qnil) => [rv|]; 
      last rewrite //.
    case Hevex : (Sem_HiF.eval_hfexpr (Eprim_unop e' h) s tmp) => [new_val|]; 
      last apply nonev.
    case Hfdvt : (VM.find v tmp) => [[r ty]|]; 
      last apply nonev.
    case Hty : ty; case Hfdvs : (VM.find v s) => [a|] ; 
      try apply nonev; 
      case Hupd : (Sem_HiF.update_hvalue_by_offset a 0 new_val) => [a'|]; 
      (apply somev_someb || apply nonev|| rewrite /=); 
      case Hev : (Sem_HiFP.eval_hfstmts rv rs' ns' s' tmp') => [v'|]; 
      (apply somev_someb ||  apply noneb).
  - case Hlex : (list_expr (Eprim_binop e' h1 h2) tmp) => [el|];
                                                          last rewrite //.
    case Hexfnf : (expand_fcnct_nflip (v, 0%num) (rev el) HiFP.qnil) => [rv|];
                                                                        last rewrite //.
    case Hevex : (Sem_HiF.eval_hfexpr (Eprim_binop e' h1 h2) s tmp) => [new_val|]; 
      last apply nonev.
    case Hfdvt : (VM.find v tmp) => [[r ty]|]; last apply nonev.
    case Hty : ty; case Hfdvs : (VM.find v s) => [a|] ; 
      try apply nonev; 
      case Hupd : (Sem_HiF.update_hvalue_by_offset a 0 new_val) => [a'|]; 
      (apply somev_someb || apply nonev|| rewrite /=); 
                                                                   case Hev : (Sem_HiFP.eval_hfstmts rv rs' ns' s' tmp') => [v'|];
                                                                                                                            (apply somev_someb ||  apply noneb).
  - case Hlex : (list_expr (Emux c h1 h2) tmp) => [el|];
                                                  last rewrite //.
    case Hexfnf : (expand_fcnct_nflip (v, 0%num) (rev el) HiFP.qnil) => [rv|];
       last rewrite //.
    case Hevex : (Sem_HiF.eval_hfexpr (Emux c h1 h2) s tmp) => [new_val|];
       last apply nonev.
    case Hfdvt : (VM.find v tmp) => [[r ty]|];
                                    last apply nonev.
    case Hty : ty; 
      case Hfdvs : (VM.find v s) => [a|] ; 
      try apply nonev; 
      case Hupd : (Sem_HiF.update_hvalue_by_offset a 0 new_val) => [a'|]; 
      (apply somev_someb || apply nonev|| rewrite /=); 
      case Hev : (Sem_HiFP.eval_hfstmts rv rs' ns' s' tmp') => [v'|]; 
      (apply somev_someb ||  apply noneb).
  - case Hrpv : (ref2pv h tmp ) => [pv|];
                                   last rewrite //.
    case Hfdvt : (VM.find v tmp) => [[ft comp]|];
                                    last rewrite //.
    case Hexpfc : (expand_fcnct (v, 0%num) pv 0 false ft HiFP.qnil) => [r|];
                                                                       last rewrite //.
    case Hofrf : (Sem_HiF.offset_ref h tmp 0) => [ofs|];
                                                 last apply nonev.
    case Heqbrh : (v == HiF.base_ref h).
    + case Hfdvs : (VM.find v s) => [vbr|];
                                    last apply nonev.
      case Hevrc : (Sem_HiF.eval_ref_connection1 ft vbr 0 ofs) => [vbr'|];
                                                                  last apply nonev.
      case Hcomp : comp ; 
      case Hevstm : (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp'); 
      (apply somev_someb|| apply noneb).
    + case Hfdvs : (VM.find v s) => [vbr|];
                                    last apply nonev.
      case Hfdbrs : (VM.find (HiF.base_ref h) s) => [vbr'|];
                                                    last apply nonev.
      case Hevrc : (Sem_HiF.eval_ref_connection ft vbr vbr' 0 ofs) => [[valbr valbrf]|];
                                                                      last apply nonev.
      case Hcomp : comp ; 
      case Hevstm : (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp') => [a'|]; 
      (apply somev_someb|| rewrite /=); 
      case Hfdht : (VM.find (HiF.base_ref h) tmp) => [[f com]|]; 
      (apply nonev|| rewrite /=); 
                                                     case Hc: com;
                                                     (apply somev_someb|| apply noneb).
Qed.

Lemma eval_expand_stmt : forall st rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match (lowertypes_stmt' st tmp HiFP.qnil) with
    | Some r => 
        hvalue2bits (Sem_HiF.eval_hfstmt st rs ns s tmp) (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end
with eval_expand_stmts : forall sts rs ns s rs' ns' s' tmp tmp',
    hvalue2bits (Some (rs, ns)) (Some (rs', ns')) ->
    match (lowertypes_stmts' sts tmp HiFP.qnil) with
    | Some r => 
        hvalue2bits (Sem_HiF.eval_hfstmts sts rs ns s tmp) (Sem_HiFP.eval_hfstmts r rs' ns' s' tmp')
    | None => True
    end      .
Proof.
  move => st rs ns s rs' ns' s' tmp tmp' Hss.
  case Hst : st => [||||||h h1||h h1 h2].
  - by apply eval_expand_skip.
  - by apply eval_expand_wire.
  - by apply eval_expand_reg.
  - by apply eval_expand_mem.
  - by apply eval_expand_inst.
  - by apply eval_expand_node.
  - case Hh : h => [eid| esf| eind|es ea].
    + by apply eval_expand_fcncteid.
    + by apply eval_expand_fcnctesub.
    + by apply eval_expand_fcnctesubind.
    + by apply eval_expand_fcnctesubacc.
    + by apply eval_expand_inv.
    + rewrite /=.
      case Hexgex : (expand_ground_expr h tmp) => [c'|];
                                                  last rewrite //.
      case Hepdsts1 : (lowertypes_stmts' h1 tmp HiFP.qnil) => [ss1|];
                                                                  last rewrite //.
      case Hepdsts2 : (lowertypes_stmts' h2 tmp HiFP.qnil) => [ss2|];
                                                                  last rewrite //.
      case Hevalh : (Sem_HiF.eval_hfexpr h s tmp) => [a|];
                                                     last apply nonev.
      case Ha : a => [valc||];
                     try apply noneb;
                     try apply nonev;
                     case Hisz : (is_zero valc);
                     rewrite /=;
                       case evalh' : (Sem_HiFP.eval_hfexpr c' s' tmp') => [a'|];
                                                                          try apply noneb;
                                                                          case Hisz' : (is_zero a'); rewrite /=;
                                                                                                       case Hevsts2: (Sem_HiFP.eval_hfstmts ss2 rs' ns' s' tmp') => [[rs0 ns0]|];
                                                                                                                                                                    try apply noneb;
      case Hevsts2s : (Sem_HiF.eval_hfstmts h2 rs ns s tmp) => [[rs1 ns1]|];
                                                               try (apply somev_someb|| apply nonev);
      case Hevsts1 : (Sem_HiFP.eval_hfstmts ss1 rs' ns' s' tmp') => [[rs2 ns2]|];
                                                               try (apply somev_someb|| apply noneb);
      case Hevalh1 : (Sem_HiF.eval_hfstmts h1 rs ns s tmp)=> [ha|];
                                                               try (apply somev_someb|| apply nonev).
      move => sts rs ns s rs' ns' s' tmp tmp' Hss.
      case H : (lowertypes_stmts' sts tmp HiFP.qnil) => [a|];
                                                            last rewrite //.
      case Hevals1 : (Sem_HiF.eval_hfstmts sts rs ns s tmp) => [ev1|];
                                                               last apply nonev.
      case Hevals2 : (Sem_HiFP.eval_hfstmts a rs' ns' s' tmp') => [ev2|];
                                                                  last apply noneb.
      apply somev_someb.
Qed.

Theorem Sem_preservation_lowerTypes : 
(* Proves pass lowerTypes preserves the semantics *)
  forall (c : HiF.hfcircuit) (inputs reg_init : VM.t hvalue),
  match Sem_HiF.compute_Sem c inputs reg_init, Sem_HiF.circuit_tmap c with
  | Some (sem, regval), Some tmap =>
      forall (newc : HiFP.hfcircuit),
      expandconnects c = Some newc ->
      let flatten_inputs := flat_valmap inputs tmap in
      let flatten_reg_init := flat_valmap reg_init tmap in
      let flatten_sem := flat_valmap sem tmap in
      let flatten_regval := flat_valmap regval tmap in
      match Sem_HiFP.compute_Sem newc flatten_inputs flatten_reg_init with
      | Some (sem_new, regval_new) => flatten_sem_rel flatten_sem sem_new /\ 
                                      flatten_sem_rel flatten_regval regval_new
                                      (* we need to proof that 1) the stable state is equivalence,
                                                               2) the new values that registers will be updated to is equivalence. *)
      | _ => true
      end
  | _, _ => true
  end.
Proof.
  move => c inp inrg.
  case Hsem : (Sem_HiF.compute_Sem c inp inrg)=> [[sem regval]|];
                                                 last rewrite//.
  case Hsemc : (Sem_HiF.circuit_tmap c) => [tmp|];
                                           last rewrite //.
  move => newc Hexpnewc/=.
  case Hcomsem : (Sem_HiFP.compute_Sem newc (flat_valmap inp tmp)
                    (flat_valmap inrg tmp)) => [[sem_new regval_new]|];
                                               last rewrite //.
  split.
  apply (flatten_rs (sem, regval) _ (flat_valmap regval tmp) _ regval_new);
    apply somev_someb.
  apply (flatten_bs (sem, regval) (flat_valmap sem tmp) _ sem_new _);
    apply somev_someb.
Qed.