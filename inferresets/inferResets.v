From HB Require Import structures.
From Coq Require Import ZArith Arith List Ascii String Lia FMaps.
From mathcomp Require Import all_ssreflect.
From Lib Require Import SsrOrder Var.
From firrtl Require Import Env HiEnv LoFirrtl HiFirrtl.
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

Fixpoint reduce_subindex (r : HiF.href) : HiF.href :=
  match r with
  | Eid _ => r
  | Esubfield ref f => Esubfield (reduce_subindex ref) f
  | Esubindex ref _
  | Esubaccess ref _ => Esubindex ref 0
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
  | Sfcnct r (Eref ref) => let reduced_r := reduce_subindex r in let reduced_ref := reduce_subindex ref in
    match ref2pv_mod reduced_r mv instmap tmap, ref2pv_mod reduced_ref mv instmap tmap
    , type_of_ref reduced_r mod_tmap, type_of_ref reduced_ref mod_tmap with
      | Some tv0, Some tv1, Some ft0, Some ft1 => (instmap, reset_graph_fcnct tv0 tv1 0 ft0 ft1 g)
      | _, _, _, _ => (instmap, g) 
      end
  | Swhen c ss_true ss_false => let (instmap', g') := reset_graph_ss mv ss_true mod_tmap tmap instmap g in
    reset_graph_ss mv ss_false mod_tmap tmap instmap' g'
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

Fixpoint find_common_reset (ls : list (TripVar.t * fgtyp)) (rst : option fgtyp) : option fgtyp :=
  match ls with
  | nil => rst
  | (_, hd) :: tl => match rst, hd with
          | Some Fasyncreset, Fasyncreset 
          | Some Freset, Fasyncreset
          | None, Fasyncreset => find_common_reset tl (Some Fasyncreset)
          | Some (Fuint 1), Fuint 1
          | Some Freset, Fuint 1
          | None, Fuint 1 => find_common_reset tl (Some (Fuint 1))
          | _, Freset => find_common_reset tl rst
          | _, _ => None
          end
  end.

Fixpoint update_rst_ftype (offset : nat) (new_rst : fgtyp) (ft : ftype) : option ftype :=
  match ft with
  | Gtyp gt => if offset == 0 then Some (Gtyp new_rst)
               else None
  | Atyp atyp n => if offset < size_of_ftype atyp then
              match update_rst_ftype offset new_rst atyp with
              | Some newt => Some (Atyp newt n)
              | _ => None
              end else None
  | Btyp ff => match update_rst_ftype_f offset new_rst ff with
              | Some newf => Some (Btyp newf)
              | _ => None
              end
  end
with update_rst_ftype_f (offset : nat) (new_rst : fgtyp) (ff : ffield) : option ffield :=
  match ff with
  | Fnil => None
  | Fflips v0 fl ft ff' => if offset < (size_of_ftype ft) then
              match update_rst_ftype offset new_rst ft with
              | Some newt => Some (Fflips v0 fl newt ff')
              | _ => None
              end else
              match update_rst_ftype_f (offset - (size_of_ftype ft)) new_rst ff' with
              | Some newf => Some (Fflips v0 fl ft newf)
              | _ => None
              end
  end.

Fixpoint find_fgtyp_by_offset (ft : ftype) (offset : nat) : option fgtyp :=
  match ft with
  | Gtyp gt => if offset == 0 then Some gt else None
  | Atyp atyp _ => if offset < size_of_ftype atyp then 
              find_fgtyp_by_offset atyp offset else None
  | Btyp btyp => find_bundle_fgtyp_by_offset btyp offset
  end 
with find_bundle_fgtyp_by_offset (ff : ffield) (offset : nat) : option fgtyp := 
  match ff with
  | Fnil => None
  | Fflips v0 fl ft ff' => if offset < (size_of_ftype ft) then
              find_fgtyp_by_offset ft offset else
              find_bundle_fgtyp_by_offset ff' (offset - (size_of_ftype ft)) 
  end.

Definition find_tv_tmap (tv : TripVar.t) (tmap : VM.t (VM.t (ftype * forient))) : option fgtyp :=
  match VM.find tv.1 tmap with (* 找到对应moule的tmap *)
  | Some mod_tmap => match VM.find tv.2.1 mod_tmap with
                  | Some (ft, _) => find_fgtyp_by_offset ft (N.to_nat tv.2.2)
                  | _ => None
                  end
  | _ => None
  end.

Fixpoint update_rst_tmap (hd : list (TripVar.t * fgtyp)) (rst : fgtyp) (tmap : VM.t (VM.t (ftype * forient))) : option (VM.t (VM.t (ftype * forient))) :=
  match hd with
  | nil => Some tmap
  | (pv, _) :: tl => match VM.find pv.1 tmap with (* 找到对应moule的tmap *)
                    | Some mod_tmap => 
                        match VM.find pv.2.1 mod_tmap with
                        | Some (ft, ori) => match update_rst_ftype (N.to_nat pv.2.2) rst ft with 
                                | Some nft => update_rst_tmap tl rst (VM.add pv.1 (VM.add pv.2.1 (nft, ori) mod_tmap) tmap)
                                | _ => None
                                end
                        | _ => None
                        end
                    | _ => None
                    end
  end.

Definition solve_reset_scc (hd : list (TripVar.t * fgtyp)) (tmap : VM.t (VM.t (ftype * forient))) : option (VM.t (VM.t (ftype * forient))) := 
match hd with
| nil => None
| [:: v] => Some tmap
| _ => match find_common_reset hd None with
      | Some rst => (* 把hd中的ref都改为类型为Gtyp rst *)
        update_rst_tmap hd rst tmap
      | _ => None
      end
end.

Fixpoint solve_reset_alg (res : list (list (TripVar.t * fgtyp))) (tmap : VM.t (VM.t (ftype * forient))) : option (VM.t (VM.t (ftype * forient))) := 
match res with
| nil => Some tmap
| hd :: tl => 
    match solve_reset_scc hd tmap with
    | Some nv => solve_reset_alg tl nv
    | None => None
    end
end.

Definition InferResets_fun : option (HiF.hfcircuit * VM.t (VM.t (ftype * forient))) :=
  match circuit_tmap c with
  | Some tmap =>
    let dpdcg := reset_graph_c c tmap in 
    let res := rev (map rev (kosaraju dpdcg)) in
    let res' := map (map (@finTripVar2TripVar c)) res in
    match solve_reset_alg res' tmap with
    | Some newtm => match InferWidths_trans_c c newtm with
        | Some newc => Some (newc, newtm)
        | _ => None
        end
    | _ => None
    end
  | _ => None
  end.

End solve_reset.

(*Definition same_fgtyp (ls : list (TripVar.t * fgtyp)) newtm : Prop := 
  forall (hd : TripVar.t) (gt gt0 : fgtyp), List.hd_error ls = Some (hd, gt0) -> find_tv_tmap hd newtm = Some gt -> 
  forall tv gt1, List.In (tv, gt1) ls -> find_tv_tmap tv newtm = Some gt.

Lemma same_fgtyp_trans ls newtm ntm : same_fgtyp ls ntm ->
  (forall tv gt, List.In (tv, gt) ls -> find_tv_tmap tv newtm = find_tv_tmap tv ntm) ->
  same_fgtyp ls newtm.
Proof.
  unfold same_fgtyp. intros Hold Heq hd gt gt0 Hhd Hfind tv gt1 Hin.
  assert (Hfind' : find_tv_tmap hd ntm = Some gt). rewrite -(Heq hd gt0) //.
    destruct ls; simpl; try done. left. simpl in Hhd. inversion Hhd; done.
  specialize (Heq _ _ Hin). rewrite Heq; clear Heq.
  apply (Hold _ _ _ Hhd Hfind' _ _ Hin).
Qed.

Lemma update_rst_ftype_size_eq :
  forall offset gt ft nft,
    update_rst_ftype offset gt ft = Some nft ->
    size_of_ftype nft = size_of_ftype ft
with update_rst_ftype_f_size_eq :
  forall offset gt ff nff,
    update_rst_ftype_f offset gt ff = Some nff ->
    size_of_fields nff = size_of_fields ff.
Proof.
  - intros offset gt ft nft H.
    destruct ft as [gt0 | t n | ff].
    + (* Gtyp *) simpl in H. destruct offset; try discriminate; injection H as <-; reflexivity.
    + (* Atyp *) simpl in H. destruct (offset < size_of_ftype t); try discriminate.
      destruct (update_rst_ftype offset gt t) eqn:Hup; try discriminate.
      injection H as <-; simpl; f_equal.
      move : Hup; apply update_rst_ftype_size_eq.
    + (* Btyp *) simpl in H.
      destruct (update_rst_ftype_f offset gt ff) eqn:Hup; try discriminate.
      injection H as <-; simpl.
      move : Hup; apply update_rst_ftype_f_size_eq.
  - intros offset gt ff nff H.
    destruct ff as [ | v f t ff'].
    + (* Fnil *) simpl in H; discriminate.
    + (* Fflips *) simpl in H.
      destruct (offset < size_of_ftype t) eqn : Hlt.
      * (* offset < size_of_ftype t *)
        destruct (update_rst_ftype offset gt t) eqn:Hup; try discriminate.
        injection H as <-; simpl; f_equal.
        move : Hup; apply update_rst_ftype_size_eq.
      * (* offset >= size_of_ftype t *)
        destruct (update_rst_ftype_f (offset - size_of_ftype t) gt ff') eqn:Hup; try discriminate.
        injection H as <-; simpl; f_equal.
        move: Hup; apply update_rst_ftype_f_size_eq.
Qed.

Lemma update_rst_ftype_find_eq :
  forall offset gt ft nft,
    update_rst_ftype offset gt ft = Some nft ->
    find_fgtyp_by_offset nft offset = Some gt
with update_rst_ftype_f_find_eq :
  forall offset gt ff nff,
    update_rst_ftype_f offset gt ff = Some nff ->
    find_bundle_fgtyp_by_offset nff offset = Some gt.
Proof.
  - intros offset gt ft nft H.
    destruct ft as [gt0 | t n | ff].
    + (* Gtyp *) simpl in H. destruct offset; try discriminate; injection H as <-; simpl; reflexivity.
    + (* Atyp *) simpl in H.
      destruct (offset < size_of_ftype t) eqn : Hlt; try discriminate.
      destruct (update_rst_ftype offset gt t) eqn:Hup; try discriminate.
      apply update_rst_ftype_size_eq in Hup as Heq.
      injection H as <-; simpl. 
      apply update_rst_ftype_find_eq with (offset:=offset) (nft:=f) in Hup.
      rewrite Heq Hlt Hup //.
    + (* Btyp *) simpl in H.
      destruct (update_rst_ftype_f offset gt ff) eqn:Hup; try discriminate.
      injection H as <-; simpl.
      apply update_rst_ftype_f_find_eq with (ff := ff) (gt:=gt) (nff:=f); assumption.
  - intros offset gt ff nff H.
    destruct ff as [ | v f t ff'].
    + (* Fnil *) simpl in H; discriminate.
    + (* Fflips *) simpl in H.
      destruct (offset < size_of_ftype t) eqn : Hlt.
      * (* offset < size_of_ftype t *)
        destruct (update_rst_ftype offset gt t) eqn:Hup; try discriminate.
        injection H as <-; simpl.
        apply update_rst_ftype_size_eq in Hup as Heq.
        rewrite Heq Hlt.
        move : Hup; apply update_rst_ftype_find_eq.
      * (* offset >= size_of_ftype t *)
        destruct (update_rst_ftype_f (offset - size_of_ftype t) gt ff') eqn:Hup; try discriminate.
        injection H as <-; simpl. rewrite Hlt.
        move : Hup; apply update_rst_ftype_f_find_eq.
Qed.

Lemma update_rst_ftype_other_offset :
  forall (offset : nat) gt ft nft (o' : nat),
    update_rst_ftype offset gt ft = Some nft ->
    o' <> offset ->
    find_fgtyp_by_offset nft o' = find_fgtyp_by_offset ft o'
with update_rst_ftype_f_other_offset :
  forall (offset : nat) gt ff nff (o' : nat),
    update_rst_ftype_f offset gt ff = Some nff ->
    o' <> offset ->
    find_bundle_fgtyp_by_offset nff o' = find_bundle_fgtyp_by_offset ff o'.
Proof.
  - intros offset gt ft nft o' Hupd Hneq.
    destruct ft as [gt0 | atyp n | ff].
    + (* Gtyp *) simpl in Hupd.
      destruct (offset == 0) eqn:Heq; try discriminate.
      move /eqP : Heq => Heq; subst offset.
      injection Hupd as <-.
      simpl.
      destruct (o' == 0) eqn:Hoo.
      * move /eqP : Hoo => Hoo; subst o'; contradiction.
      * reflexivity.
    + (* Atyp *) simpl in Hupd.
      destruct (offset < size_of_ftype atyp) eqn:Hlt; try discriminate.
      destruct (update_rst_ftype offset gt atyp) eqn:Hupd_atyp; try discriminate.
      injection Hupd as <-.
      simpl.
      destruct (o' < size_of_ftype atyp) eqn:Hlt_o.
      * apply update_rst_ftype_size_eq in Hupd_atyp as Heq.
        rewrite Heq Hlt_o.
        apply update_rst_ftype_other_offset with (offset:=offset) (gt:=gt) (ft:=atyp) (nft:=f) (o':=o'); try done.
      * apply update_rst_ftype_size_eq in Hupd_atyp as Heq.
        rewrite Heq Hlt_o.
        reflexivity.
    + (* Btyp *) simpl in Hupd.
      destruct (update_rst_ftype_f offset gt ff) eqn:Hupd_f; try discriminate.
      injection Hupd as <-.
      simpl.
      apply update_rst_ftype_f_other_offset with (offset:=offset) (gt:=gt) (ff:=ff) (nff:=f) (o':=o').
      - assumption.
      - assumption.
  - intros offset gt ff nff o' Hupd Hneq.
    destruct ff as [ | v fl ft ff'].
    + (* Fnil *) simpl in Hupd; discriminate.
    + (* Fflips *) simpl in Hupd.
      destruct (offset < size_of_ftype ft) eqn:Hlt_off.
      * (* offset < size_of_ftype ft *)
        destruct (update_rst_ftype offset gt ft) eqn:Hupd_ft; try discriminate.
        injection Hupd as <-.
        simpl. apply update_rst_ftype_size_eq in Hupd_ft as Heq.
        destruct (o' < size_of_ftype ft) eqn:Hlt_o.
        - rewrite Heq Hlt_o.
          apply update_rst_ftype_other_offset with (offset:=offset) (gt:=gt) (ft:=ft) (nft:=f) (o':=o'); try done.
        - rewrite Heq Hlt_o.
          reflexivity.
      * (* offset >= size_of_ftype ft *)
        destruct (update_rst_ftype_f (offset - size_of_ftype ft) gt ff') eqn:Hupd_ff'; try discriminate.
        injection Hupd as <-.
        simpl. apply update_rst_ftype_f_size_eq in Hupd_ff' as Heq.
        destruct (o' < size_of_ftype ft) eqn:Hlt_o.
        - reflexivity.
        - assert (Hneq_sub: o' - size_of_ftype ft <> offset - size_of_ftype ft).
          { intro Heq_sub. apply Hneq. specialize (leqVgt (size_of_ftype ft) offset) as Hge. rewrite Hlt_off in Hge.
            rewrite orb_false_r in Hge.
            specialize (leqVgt (size_of_ftype ft) o') as Hge'. rewrite Hlt_o in Hge'.
            rewrite orb_false_r in Hge'.
            apply (Nat.add_cancel_r (o' - size_of_ftype ft) (offset - size_of_ftype ft) (size_of_ftype ft)) in Heq_sub.
            change ((o' - size_of_ftype ft + size_of_ftype ft)%coq_nat) with (o' - size_of_ftype ft + size_of_ftype ft) in Heq_sub.
            change ((offset - size_of_ftype ft + size_of_ftype ft)%coq_nat) with (offset - size_of_ftype ft + size_of_ftype ft) in Heq_sub.
            rewrite subnK in Heq_sub; try done. rewrite subnK in Heq_sub; try done. }
          apply update_rst_ftype_f_other_offset
            with (offset:=offset - size_of_ftype ft) (gt:=gt) (ff:=ff') (nff:=f) (o':=o' - size_of_ftype ft); try done.
Qed.

Lemma update_rst_ftype_find_tv_tmap_eq (hd_tv hd_tv' : TripVar.t) gt ft ori mod_tmap nft newtm tmap : 
  VM.find hd_tv.1 tmap = Some mod_tmap -> VM.find hd_tv.2.1 mod_tmap = Some (ft, ori) ->
  update_rst_ftype (N.to_nat hd_tv.2.2) gt ft = Some nft -> newtm = VM.add hd_tv.1 (VM.add hd_tv.2.1 (nft, ori) mod_tmap) tmap -> 
  hd_tv' <> hd_tv -> find_tv_tmap hd_tv' newtm = find_tv_tmap hd_tv' tmap.
Proof.
  intros Hmod Hfind_mod Hupd Hnew Hneq.
  unfold find_tv_tmap.
  (* 区分模块标识是否相同 *)
  case (eqVneq hd_tv'.1 hd_tv.1) as [Heq_mod | Hneq_mod].
  - (* 模块标识相同 *)
    rewrite Heq_mod.
    rewrite Hnew.
    rewrite VM.Lemmas.add_eq_o; try done.
    rewrite Hmod.
    (* 现在比较内部映射 *)
    case (eqVneq hd_tv'.2.1 hd_tv.2.1) as [Heq_var | Hneq_var].
    + (* 变量标识相同 *)
      assert (Hdiff_offset : hd_tv'.2.2 <> hd_tv.2.2).
      { intro Heq_off.
        apply Hneq.
        destruct hd_tv as [m [v off]], hd_tv' as [m' [v' off']].
        simpl in *. 
        subst m' v' off'.        (* 由 Heq_mod, Heq_var, Heq_off 全部替换 *)
        reflexivity.
      } 
      rewrite Heq_var.
      rewrite VM.Lemmas.add_eq_o; try done. 
      rewrite Hfind_mod.
      simpl.
      (* 现在调用辅助引理，因为偏移量不同，更新不影响该偏移的查找 *)
      apply (update_rst_ftype_other_offset _ _ _ _ _ Hupd). intro. 
      apply Nnat.N2Nat.inj in H. done.
    + (* 变量标识不同 *)
      rewrite VM.Lemmas.add_neq_o; try done. intro. move /eqP : H => H. rewrite H in Hneq_var.
      unfold "!=" in Hneq_var. rewrite eq_refl in Hneq_var. done.
  - (* 模块标识不同 *)
    rewrite Hnew.
    rewrite VM.Lemmas.add_neq_o; try done. intro. move /eqP : H => H. rewrite H in Hneq_mod.
    unfold "!=" in Hneq_mod. rewrite eq_refl in Hneq_mod. done.
Qed.

Lemma update_rst_tmap_notin_find_eq hd ls gt tmap newtm : update_rst_tmap ls gt tmap = Some newtm ->
  (forall gt0, ~List.In (hd, gt0) ls) -> find_tv_tmap hd newtm = find_tv_tmap hd tmap.
Proof. 
  move : ls tmap newtm. elim. simpl; intros. inversion H; subst tmap. done.
  intros [tv gt0] tl IH tmap newtm Hupdate Hnotin. simpl in Hupdate.
  destruct (VM.find tv.1 tmap) as [mod_tmap|] eqn : Hmod; try discriminate.
  destruct (VM.find tv.2.1 mod_tmap) as [[ft ori]|] eqn : Hvar; try discriminate.
  destruct (update_rst_ftype (N.to_nat tv.2.2) gt ft) as [nft|] eqn : Hnft; try discriminate.
  remember (VM.add tv.1 (VM.add tv.2.1 (nft, ori) mod_tmap) tmap) as ntm.
  rewrite (IH _ _ Hupdate). clear IH Hupdate. apply (update_rst_ftype_find_tv_tmap_eq _ _ _ _ _ _ _ _ _ Hmod Hvar Hnft Heqntm).
  specialize (Hnotin gt0); simpl in Hnotin. apply Decidable.not_or in Hnotin. move : Hnotin => [Hnotin _].
  move : Hnotin; apply contra_not. intro; subst hd; done.
  intro. specialize (Hnotin gt1). move : Hnotin; apply contra_not. intro; simpl. right; done.
Qed.

Lemma update_rst_tmap_find_tv_tmap_eq hd_tv gt0 gt tl rst tmap ntm : 
  NoDup (List.split ((hd_tv, gt0) :: tl)).1 ->
  update_rst_tmap ((hd_tv, gt0) :: tl) rst tmap = Some ntm -> find_tv_tmap hd_tv ntm = Some gt ->
  forall tv gt1, List.In (tv, gt1) tl -> find_tv_tmap tv ntm = Some gt.
Proof.
  move : tl hd_tv gt0 gt tmap ntm; elim. simpl; try done.
  intros [hd_tv gt0] tl IH hd_tv' gt0' gt tmap ntm Hnodup Hupdate Hfind tv gt1 Hin. simpl in Hin. destruct Hin as [|Hin].
  - inversion H; subst tv gt0; clear H IH. remember ((hd_tv, gt1) :: tl) as tl'. simpl in Hupdate.
    destruct (VM.find hd_tv'.1 tmap) as [mod_tmap'|] eqn : Hmod'; try discriminate.
    destruct (VM.find hd_tv'.2.1 mod_tmap') as [[ft' ori']|] eqn : Hvar'; try discriminate.
    destruct (update_rst_ftype (N.to_nat hd_tv'.2.2) rst ft') as [nft'|] eqn : Hnft'; try discriminate.
    remember (VM.add hd_tv'.1
               (VM.add hd_tv'.2.1 (nft', ori') mod_tmap')
               tmap) as ntm'.
    subst tl'. simpl in Hupdate.
    destruct (VM.find hd_tv.1 ntm') as [mod_tmap|] eqn : Hmod; try discriminate.
    destruct (VM.find hd_tv.2.1 mod_tmap) as [[ft ori]|] eqn : Hvar; try discriminate.
    destruct (update_rst_ftype (N.to_nat hd_tv.2.2) rst ft) as [nft|] eqn : Hnft; try discriminate.
    remember (VM.add hd_tv.1
               (VM.add hd_tv.2.1 (nft, ori) mod_tmap)
               ntm') as newtm.
    assert (Heq0 : find_tv_tmap hd_tv' ntm = find_tv_tmap hd_tv' newtm). 
      apply (update_rst_tmap_notin_find_eq _ _ _ _ _ Hupdate). move : Hnodup; clear; intros. intro.
      apply in_split_l in H; simpl in H. simpl in Hnodup. destruct (List.split tl) as [left right]. simpl in Hnodup; simpl in H.
      apply NoDup_cons_iff in Hnodup. move : Hnodup => [Hnodup _]. simpl in Hnodup. apply Decidable.not_or in Hnodup.
      move : Hnodup => [_ Hnodup]. done.
    assert (Heq1 : find_tv_tmap hd_tv ntm = find_tv_tmap hd_tv newtm). 
      apply (update_rst_tmap_notin_find_eq _ _ _ _ _ Hupdate). move : Hnodup; clear; intros. intro.
      apply in_split_l in H; simpl in H. simpl in Hnodup. destruct (List.split tl) as [left right]. simpl in Hnodup; simpl in H.
      apply NoDup_cons_iff in Hnodup. move : Hnodup => [_ Hnodup].
      apply NoDup_cons_iff in Hnodup. move : Hnodup => [Hnodup _]. done.
    rewrite Heq1; clear Heq1. rewrite Heq0 in Hfind; clear Heq0 Hupdate ntm.
    assert (Heq : find_tv_tmap hd_tv' newtm = find_tv_tmap hd_tv' ntm'). 
      apply (update_rst_ftype_find_tv_tmap_eq _ _ _ _ _ _ _ _ _ Hmod Hvar Hnft Heqnewtm).
      simpl in Hnodup. destruct (List.split tl) as [left right]. simpl in Hnodup.
      apply NoDup_cons_iff in Hnodup. move : Hnodup => [Hnodup _]. move : Hnodup; apply contra_not.
      simpl. left;done.
    rewrite Heq in Hfind; clear Heq.
    unfold find_tv_tmap. subst newtm. 
    rewrite VM.Lemmas.add_eq_o; try done. rewrite VM.Lemmas.add_eq_o; try done.
    apply update_rst_ftype_find_eq in Hnft. rewrite Hnft; clear Hnft.
    unfold find_tv_tmap in Hfind; subst ntm'.
    rewrite VM.Lemmas.add_eq_o in Hfind; try done. rewrite VM.Lemmas.add_eq_o in Hfind; try done.
    apply update_rst_ftype_find_eq in Hnft'. rewrite Hnft' in Hfind. done. 
  - remember ((hd_tv, gt0) :: tl) as tl'. simpl in Hupdate.
    destruct (VM.find hd_tv'.1 tmap) as [mod_tmap'|]; try discriminate.
    destruct (VM.find hd_tv'.2.1 mod_tmap') as [[ft' ori']|]; try discriminate.
    destruct (update_rst_ftype (N.to_nat hd_tv'.2.2) rst ft') as [nft'|] eqn : Hnft'; try discriminate.
    remember (VM.add hd_tv'.1
               (VM.add hd_tv'.2.1 (nft', ori') mod_tmap')
               tmap) as ntm'.
    assert (Heq0 : find_tv_tmap hd_tv' ntm = find_tv_tmap hd_tv' ntm'). 
    apply (update_rst_tmap_notin_find_eq _ _ _ _ _ Hupdate). move : Hnodup; clear; intros. intro.
      apply in_split_l in H; simpl in H. simpl in Hnodup. destruct (List.split tl') as [left right]. simpl in Hnodup; simpl in H.
      apply NoDup_cons_iff in Hnodup. move : Hnodup => [Hnodup _]. done.
    rewrite Heq0 in Hfind; clear Heq0. rewrite Heqntm' /find_tv_tmap in Hfind.
    rewrite VM.Lemmas.add_eq_o in Hfind; try done. rewrite VM.Lemmas.add_eq_o in Hfind; try done.
    apply update_rst_ftype_find_eq in Hnft'. rewrite Hnft' in Hfind; clear Hnft'. inversion Hfind; subst rst; clear Hfind.
    subst tl'. 
    assert (Hnodup' : NoDup (List.split ((hd_tv, gt0) :: tl)).1). 
      simpl in Hnodup; simpl. destruct (List.split tl) as [left right]. simpl in Hnodup; simpl.
      apply NoDup_cons_iff in Hnodup. move : Hnodup => [_ Hnodup]. done.
    specialize (IH _ _ gt _ _ Hnodup' Hupdate). move : tv gt1 Hin; apply IH.
    simpl in Hupdate. 
    destruct (VM.find hd_tv.1 ntm') as [mod_tmap|]; try discriminate.
    destruct (VM.find hd_tv.2.1 mod_tmap) as [[ft ori]|]; try discriminate.
    destruct (update_rst_ftype (N.to_nat hd_tv.2.2) gt ft) as [nft|] eqn : Hnft; try discriminate.
    remember (VM.add hd_tv.1 (VM.add hd_tv.2.1 (nft, ori) mod_tmap) ntm') as ntm''.
    assert (Heq1 : find_tv_tmap hd_tv ntm = find_tv_tmap hd_tv ntm''). 
      apply (update_rst_tmap_notin_find_eq _ _ _ _ _ Hupdate). move : Hnodup; clear; intros. intro.
      apply in_split_l in H; simpl in H. simpl in Hnodup. destruct (List.split tl) as [left right]. simpl in Hnodup; simpl in H.
      apply NoDup_cons_iff in Hnodup. move : Hnodup => [_ Hnodup].
      apply NoDup_cons_iff in Hnodup. move : Hnodup => [Hnodup _]. done.
    rewrite Heq1; clear Heq1. subst ntm''. unfold find_tv_tmap.
    rewrite VM.Lemmas.add_eq_o; try done. rewrite VM.Lemmas.add_eq_o; try done.
    move : Hnft; apply update_rst_ftype_find_eq.
Qed.

Lemma solve_reset_scc_same_fgtyp hd tmap ntm : NoDup (List.split hd).1 -> solve_reset_scc hd tmap = Some ntm -> same_fgtyp hd ntm.
Proof.
  move : hd tmap ntm; elim. simpl; try done.
  intros [hd_tv gt0] tl IH tmap ntm Hnodup Hscc. unfold same_fgtyp. intros hd0 gt gt1 Hhd.
  simpl in Hhd. inversion Hhd; subst hd0 gt1; clear Hhd.
  intros Hfind tv gt1 Hin. simpl in Hin. destruct Hin as [|Hin].
  - inversion H; subst tv gt1; done.
  - unfold solve_reset_scc in Hscc. destruct tl as [|hd_tv' tl'] eqn : Htl; try discriminate.
    rewrite -Htl in IH Hin Hscc Hnodup.
    destruct (find_common_reset ((hd_tv, gt0) :: tl) None) as [rst|]; try discriminate.
    move : Hscc Hfind tv gt1 Hin. apply update_rst_tmap_find_tv_tmap_eq; try done.
Qed.

Lemma solve_reset_alg_notin_find_eq ls tmap newtm : solve_reset_alg ls tmap = Some newtm -> forall tv, ~In tv (List.split (concat ls)).1 ->
  find_tv_tmap tv newtm = find_tv_tmap tv tmap.
Proof.
  move : ls tmap newtm. induction ls as [| hd tl IH].
  - simpl; intros; inversion H; subst; reflexivity.
  - intros tmap newtm Hsol tv Hnotin.
    simpl in Hsol.
    destruct (solve_reset_scc hd tmap) as [mid | ] eqn:Hmid; try discriminate.
    apply IH with (tmap:=mid) (tv := tv) in Hsol.
    + rewrite Hsol. clear Hsol IH newtm. 
      assert (~ In tv (List.split hd).1). simpl in Hnotin. rewrite constraints.split_app in Hnotin; simpl in Hnotin.
        move : Hnotin; apply contra_not. intro. apply in_or_app. left; done.
      clear Hnotin tl.
      unfold solve_reset_scc in Hmid. destruct hd as [|[hd' gt'] tl] eqn : Htl; try discriminate.
      rewrite -Htl in H Hmid. destruct tl; try discriminate.
      destruct (find_common_reset hd None); try discriminate.
      apply (update_rst_tmap_notin_find_eq _ _ _ _ _ Hmid). 
      intro. move : H; apply contra_not; intro. destruct (List.split hd) as [left right] eqn : Hsplit. simpl. 
      apply split_combine in Hsplit. rewrite -Hsplit in H. apply in_combine_l in H; done.
    + move : Hnotin; apply contra_not. clear. intro. simpl.
      rewrite constraints.split_app; simpl. apply in_or_app. right; done.
Qed.

Theorem InferResets_correstness res tmap newtm : NoDup (List.split (concat res)).1 -> solve_reset_alg res tmap = Some newtm -> forall hd, List.In hd res ->
  same_fgtyp hd newtm.
Proof.
  move : res tmap newtm; elim. simpl; try done.
  intros ls tl IH tmap newtm Hnodup Hinfer hd Hin. simpl in Hin. destruct Hin as [Heq|Hin]. subst ls. 
  - simpl in Hinfer. destruct (solve_reset_scc hd tmap) as [ntm|] eqn : Hscc; try discriminate.
    assert (Hnotin : forall tv gt, List.In (tv, gt) hd -> find_tv_tmap tv newtm = find_tv_tmap tv ntm). 
      intros; apply (solve_reset_alg_notin_find_eq _ _ _ Hinfer tv). 
      simpl in Hnodup. rewrite constraints.split_app in Hnodup; simpl in Hnodup.
      apply constraints.NoDup_app_notin_r with (var := tv) in Hnodup; try done.
      destruct (List.split hd) as [left right] eqn : Hsplit. simpl. 
      apply split_combine in Hsplit. subst hd. apply in_combine_l in H; done.
    move : Hnotin; apply same_fgtyp_trans. clear Hinfer IH.
    move : Hscc; apply solve_reset_scc_same_fgtyp; try done.
      simpl in Hnodup. rewrite constraints.split_app in Hnodup; simpl in Hnodup.
      apply constraints.NoDup_app_remove_r in Hnodup; done.
  - simpl in Hinfer. destruct (solve_reset_scc ls tmap) as [ntm|] eqn : Hscc; try discriminate.
    move : Hinfer hd Hin; apply IH. 
      simpl in Hnodup. rewrite constraints.split_app in Hnodup; simpl in Hnodup.
      apply constraints.NoDup_app_remove_l in Hnodup; done.
Qed.*)