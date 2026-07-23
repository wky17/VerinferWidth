From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From firrtl Require Import Env HiEnv LoFirrtl HiFirrtl.
From Lib Require Import Nbits Var.
From Semantics Require Import Semantics.

Fixpoint pl2btyp (pl : seq HiF.hfport) : ffield := 
  match pl with
  | nil => Fnil
  | Finput v t :: tl => Fflips v Nflip t (pl2btyp tl)
  | Foutput v t :: tl => Fflips v Flipped t (pl2btyp tl)
  end.

(* functions used to record ftype and component type *)
Fixpoint stmts_tmap (modplmap : VM.t (seq HiF.hfport)) (tmap : VM.t (ftype * fcomponent)) (ss : HiF.hfstmt_seq): option (VM.t (ftype * fcomponent)) :=
  match ss with
  | Qnil => Some tmap
  | Qcons s ss' => match stmt_tmap modplmap tmap s with
      | Some tmap' => stmts_tmap modplmap tmap' ss'
      | None => None
      end
  end
with stmt_tmap (modplmap : VM.t (seq HiF.hfport)) (tmap : VM.t (ftype * fcomponent)) (s : HiF.hfstmt) : option (VM.t (ftype * fcomponent)) :=
  match s with
  | Sskip => Some tmap
  | Sfcnct _ _ => Some tmap
  | Sinvalid _ => Some tmap
  | Smem v m => Some (VM.add v (data_type m, Memory) tmap)
  | Sinst v mv => match VM.find mv modplmap with
      | Some pl => let t := Btyp (pl2btyp pl) in
                  Some (VM.add v (t, Instanceof) tmap)
      | _ => None
      end
  | Swire v t => match VM.find v tmap with
      | None => Some (VM.add v (t, Wire) tmap)
      | _ => None
      end
  | Sreg v reg => match VM.find v tmap, Sem_HiF.type_of_hfexpr (clock reg) tmap with
      | None, Some _ => Some (VM.add v ((type reg), Register) tmap)
      | _, _ => None
      end
  | Snode v expr => match VM.find v tmap, Sem_HiF.type_of_hfexpr expr tmap with
                  | None, Some ft => Some (VM.add v (ft, Node) tmap)
                  | _, _ => None
                  end
  | Swhen cond ss_true ss_false =>
      match Sem_HiF.type_of_hfexpr cond tmap, stmts_tmap modplmap tmap ss_true with
      | Some (Gtyp _), Some tmap_true => stmts_tmap modplmap tmap_true ss_false 
      | _, _ => None
      end
  end.

Fixpoint modules_tmap (modplmap : VM.t (seq HiF.hfport)) (tmap : VM.t (VM.t (ftype * fcomponent))) (ml : seq HiF.hfmodule) : option (VM.t (VM.t (ftype * fcomponent))) :=
  match ml with
  | nil => Some tmap
  | FInmod mv ps ss :: tl => match Sem_HiF.ports_tmap' (VM.empty (ftype * fcomponent)) ps with
              | Some pmap => match stmts_tmap modplmap pmap ss with
                  | Some tmap' => modules_tmap modplmap (VM.add mv tmap' tmap) tl
                  | None => None
                  end
              | None => None
              end 
  | _ :: tl => modules_tmap modplmap tmap tl
  end.

Definition circuit_tmap (c : HiF.hfcircuit) : option (VM.t (VM.t (ftype * fcomponent))) :=
  match c with
  | Fcircuit v ml => let modplmap := List.fold_left (fun acc m => 
      match m with
      | FInmod mv ps _ => VM.add mv ps acc
      | FExmod mv ps _ => VM.add mv ps acc
      end) ml (VM.empty (seq HiF.hfport)) in
    modules_tmap modplmap (VM.empty (VM.t (ftype * fcomponent))) ml
  end.

(*Fixpoint list_ref_subaccess (r : HiF.href) (tmap : VM.t (ftype * fcomponent)) : option (list HiF.href) :=
  match r with
  | Eid v => Some [::r]
  | Esubindex v i => match list_ref_subaccess v tmap with
                    | Some ref_list => Some (map (fun ref => Esubindex v i) ref_list)
                    | _ => None
                    end
  | Esubfield v f => match list_ref_subaccess v tmap with
                    | Some ref_list => Some (map (fun ref => Esubfield v f) ref_list)
                    | _ => None
                    end
  | Esubaccess v e => match Sem_HiF.type_of_ref v tmap, list_ref_subaccess v tmap with
                    | Some (Atyp _ n), Some ref_list =>
                      let fix aux ref m ls := match m with
                                          | m'.+1 => aux ref m' ((Esubindex ref m') :: ls)
                                          | 0 => ls
                                          end
                                  in
                      Some (flat_map (fun ref => aux ref n nil) ref_list)
                    | _, _ => None
                    end
  end.*)

Definition rev_tr {A} (l : list A) : list A :=
  let fix rev_aux l acc :=
    match l with
    | nil => acc
    | h :: t => rev_aux t (h :: acc)
    end
  in rev_aux l nil.

(* 尾递归 map，使用累加器，最终 rev 保持顺序 *)
Fixpoint map_tailrec {A B} (f : A -> B) (l : list A) (acc : list B) : list B :=
  match l with
  | nil => rev_tr acc
  | hd :: tl => map_tailrec f tl (f hd :: acc)
  end.

Definition map_tr {A B} (f : A -> B) (l : list A) : list B :=
  map_tailrec f l nil.

(* 尾递归 flat_map，同样使用累加器 + rev_append（尾递归） *)
Fixpoint flat_map_tailrec {A B} (g : A -> list B) (l : list A) (acc : list B) : list B :=
  match l with
  | nil => acc
  | hd :: tl => flat_map_tailrec g tl (rev_append (g hd) acc)
  end.

Definition flat_map_tr {A B} (g : A -> list B) (l : list A) : list B :=
  flat_map_tailrec g l nil.

Fixpoint list_ref_subaccess_cps (r : HiF.href) (tmap : VM.t (ftype * fcomponent))
                                 (k : option (list HiF.href) -> option (list HiF.href))
                                 : option (list HiF.href) :=
  match r with
  | Eid v => k (Some [::r])
  | Esubfield v f =>
      list_ref_subaccess_cps v tmap (fun res =>
        match res with
        | Some ref_list => k (Some (map_tr (fun ref => Esubfield ref f) ref_list))
        | None => k None
        end)
  | Esubindex v i =>
      list_ref_subaccess_cps v tmap (fun res =>
        match res with
        | Some ref_list => k (Some (map_tr (fun ref => Esubindex ref i) ref_list))
        | None => k None
        end)
  | Esubaccess v e =>
      match Sem_HiF.type_of_ref v tmap with
      | Some (Atyp _ n) =>
          list_ref_subaccess_cps v tmap (fun res =>
            match res with
            | Some ref_list =>
                let fix aux ref m acc :=
                  match m with
                  | 0 => acc
                  | S m' => aux ref m' (Esubindex ref m' :: acc)
                  end
                in
                let expanded := flat_map_tr (fun ref => aux ref n nil) ref_list in
                k (Some expanded)
            | None => k None
            end)
      | _ => k None
      end
  end.

(* 对外接口：初始 continuation 为恒等函数 *)
Definition list_ref_subaccess (r : HiF.href) (tmap : VM.t (ftype * fcomponent)) : option (list HiF.href) :=
  list_ref_subaccess_cps r tmap (fun x => x).

Fixpoint generate_cond (r ref : HiF.href) (cond : option HiF.hfexpr) (tmap : VM.t (ftype * fcomponent)) : option HiF.hfexpr :=
  match r, ref with
  | Eid _, Eid _ => cond
  | Esubindex v0 _, Esubindex v1 _ => generate_cond v0 v1 cond tmap
  | Esubfield v0 _, Esubfield v1 _ => generate_cond v0 v1 cond tmap
  | Esubaccess v0 e, Esubindex v1 i => match cond, Sem_HiF.type_of_ref v1 tmap with
                    | Some c, Some (Atyp _ n) => let bv_length := Nat.log2 (n-1) + 1 in (* 假设n不为0 *)
                      let cond' := Some (Eprim_binop Band c (Eprim_binop (Bcomp Beq) e (HiF.econst (Fuint bv_length) (rev_tr (from_nat bv_length i))))) in
                      generate_cond v0 v1 cond' tmap
                    | None, Some (Atyp _ n) => let bv_length := Nat.log2 (n-1) + 1 in (* 假设n不为0 *)
                      let cond' := Some (Eprim_binop (Bcomp Beq) e (HiF.econst (Fuint bv_length) (rev_tr (from_nat bv_length i)))) in
                      generate_cond v0 v1 cond' tmap
                    | _, _ => None
                    end
  | _, _ => None
  end.

Fixpoint preprocess_subaccess_ref (r : HiF.href) (ref_tl : list HiF.href) (e : HiF.hfexpr) (tmap : VM.t (ftype * fcomponent)) : option HiF.hfexpr :=
  match ref_tl with
  | nil => Some e 
  | hd :: tl => match generate_cond r hd None tmap with
                | Some cond => preprocess_subaccess_ref r tl (Emux cond (Eref hd) e) tmap
                | _ => None
                end
  end.

Fixpoint preprocess_subaccess_expr (e : HiF.hfexpr) (tmap : VM.t (ftype * fcomponent)) : option HiF.hfexpr :=
  match e with
  | Econst _ _ => Some e
  | Eref ref => match list_ref_subaccess ref tmap with
                | Some (ref_hd :: ref_tl) => preprocess_subaccess_ref ref ref_tl (Eref ref_hd) tmap
                | _ => None
                end
  | Ecast c e0 => match preprocess_subaccess_expr e0 tmap with
                | Some e' => Some (Ecast c e')
                | _ => None
                end
  | Eprim_unop op e0 => match preprocess_subaccess_expr e0 tmap with
                | Some e' => Some (Eprim_unop op e')
                | _ => None
                end
  | Eprim_binop op e0 e1 => match preprocess_subaccess_expr e0 tmap, preprocess_subaccess_expr e1 tmap with
                | Some e', Some e'' => Some (Eprim_binop op e' e'')
                | _, _ => None
                end
  | Emux c e0 e1 => match preprocess_subaccess_expr c tmap, preprocess_subaccess_expr e0 tmap, preprocess_subaccess_expr e1 tmap with
                | Some c', Some e', Some e'' => Some (Emux c' e' e'')
                | _, _, _ => None
                end
end.

(*Fixpoint preprocess_subaccess_expr_cps
    (e : HiF.hfexpr) (tmap : VM.t (ftype * fcomponent))
    (k : option HiF.hfexpr -> option HiF.hfexpr) : option HiF.hfexpr :=
  match e with
  | Econst _ _ => k (Some e)
  | Eref ref => 
      match list_ref_subaccess ref tmap with
      | Some (ref_hd :: ref_tl) =>
          (* preprocess_subaccess_ref 已经是尾递归，直接调用并用 k 延续 *)
          let res := preprocess_subaccess_ref ref ref_tl (Eref ref_hd) tmap in
          k res
      | _ => k None
      end
  | Ecast c e0 =>
      preprocess_subaccess_expr_cps e0 tmap (fun res =>
        match res with
        | Some e' => k (Some (Ecast c e'))
        | None => k None
        end)
  | Eprim_unop op e0 =>
      preprocess_subaccess_expr_cps e0 tmap (fun res =>
        match res with
        | Some e' => k (Some (Eprim_unop op e'))
        | None => k None
        end)
  | Eprim_binop op e0 e1 =>
      preprocess_subaccess_expr_cps e0 tmap (fun res0 =>
        match res0 with
        | Some e0' =>
            preprocess_subaccess_expr_cps e1 tmap (fun res1 =>
              match res1 with
              | Some e1' => k (Some (Eprim_binop op e0' e1'))
              | None => k None
              end)
        | None => k None
        end)
  | Emux c e0 e1 =>
      preprocess_subaccess_expr_cps c tmap (fun resc =>
        match resc with
        | Some c' =>
            preprocess_subaccess_expr_cps e0 tmap (fun res0 =>
              match res0 with
              | Some e0' =>
                  preprocess_subaccess_expr_cps e1 tmap (fun res1 =>
                    match res1 with
                    | Some e1' => k (Some (Emux c' e0' e1'))
                    | None => k None
                    end)
              | None => k None
              end)
        | None => k None
        end)
  end.

Definition preprocess_subaccess_expr e tmap :=
  preprocess_subaccess_expr_cps e tmap (fun x => x).*)

Fixpoint iter_preprocess_subaccess_expr n e tmap :=
  match n, preprocess_subaccess_expr e tmap with
  | 0, Some exp 
  | 1, Some exp => Some exp
  | S m, Some exp => iter_preprocess_subaccess_expr m exp tmap
  | _, _ => None
  end.

Fixpoint depth_subaccess_ref (r : HiF.href) (n : nat) : nat :=
  match r with
  | Eid _ => n
  | Esubindex v0 _ 
  | Esubfield v0 _ => depth_subaccess_ref v0 n
  | Esubaccess v0 e => depth_subaccess e (n+1)
  end
with depth_subaccess (e : HiF.hfexpr) (n : nat) : nat :=
  match e with
  | Econst _ _ => n
  | Eref ref => depth_subaccess_ref ref n
  | Ecast _ e0 
  | Eprim_unop _ e0 => depth_subaccess e0 n
  | Eprim_binop _ e0 e1 => max (depth_subaccess e0 n) (depth_subaccess e1 n)
  | Emux c e0 e1 => max (depth_subaccess c n) (max (depth_subaccess e0 n) (depth_subaccess e1 n))
end.

Fixpoint preprocess_subaccess_stmt (s : HiF.hfstmt) (sts : HiF.hfstmt_seq) (tmap : VM.t (ftype * fcomponent)) : option HiF.hfstmt_seq :=
  match s with
  | Sskip 
  | Sinvalid _ 
  | Smem _ _
  | Sinst _ _
  | Swire _ _
  | Sreg _ _ => Some (Qcons s sts)
  | Snode v expr => let depth := depth_subaccess expr 0 in
                  match iter_preprocess_subaccess_expr depth expr tmap with
                  | Some e => Some (Qcons (Snode v e) sts)
                  | _ => None
                  end
  | Sfcnct ref expr => let depth := depth_subaccess expr 0 in
                  match list_ref_subaccess ref tmap, iter_preprocess_subaccess_expr depth expr tmap with
                  | Some ref_list, Some e => let fix aux ls acc := match acc, ls with
                                          | Some acc', hd :: tl => match generate_cond ref hd None tmap with
                                                  | Some cond => let depth_cond := depth_subaccess cond 0 in 
                                                      match iter_preprocess_subaccess_expr depth_cond cond tmap with
                                                      | Some cond' => 
                                                        aux tl (Some (Qcons (Sfcnct hd (Emux cond' e (Eref hd))) acc'))
                                                      | _ => None
                                                      end
                                                  | _ => aux tl (Some (Qcons (Sfcnct hd e) acc'))
                                                  end
                                          | _, _ => acc
                                          end
                                  in aux ref_list (Some sts)
                  | _, _ => None
                  end
  | Swhen cond ss_true ss_false => let depth := depth_subaccess cond 0 in
                  match iter_preprocess_subaccess_expr depth cond tmap, 
                  preprocess_subaccess_stmts ss_true HiF.qnil tmap, preprocess_subaccess_stmts ss_false HiF.qnil tmap with
                  | Some cond', Some ss_true', Some ss_false' => Some (Qcons (Swhen cond' ss_true' ss_false') sts)
                  | _, _, _ => None
                  end
  end
with preprocess_subaccess_stmts (ss : HiF.hfstmt_seq) (sts : HiF.hfstmt_seq) (tmap : VM.t (ftype * fcomponent)) : option HiF.hfstmt_seq :=
  match ss with
  | Qnil => Some (Qrev sts)
  | Qcons s ss' => match preprocess_subaccess_stmt s sts tmap with
      | Some sts' => preprocess_subaccess_stmts ss' sts' tmap
      | None => None
      end
  end.

Fixpoint preprocess_subaccess_fml (ml : list HiF.hfmodule) (tmap : VM.t (VM.t (ftype * fcomponent))) : option (list HiF.hfmodule) :=
  match ml with
  | nil => Some nil
  | (FInmod mv ps ss) :: tl => match VM.find mv tmap with
                          | Some tmap_mod => match preprocess_subaccess_stmts ss HiF.qnil tmap_mod, preprocess_subaccess_fml tl tmap with
                              | Some ss', Some fml => Some ((FInmod mv ps ss') :: fml)
                              | _, _ => None
                              end
                          | _ => None
                          end
  | _ :: tl => preprocess_subaccess_fml tl tmap
  end.

Definition preprocess_subaccess (c : HiF.hfcircuit) : option HiF.hfcircuit :=
  match c, circuit_tmap c with
  | Fcircuit v ml, Some tmap => match preprocess_subaccess_fml ml tmap with
    | Some fml => Some (Fcircuit v fml)
    | _ => None
    end
  | _, _ => None
  end.

Fixpoint expand_wire_aux (v : VarOrder.t) (offset : nat) (ft : ftype)
                         (acc : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  match ft with
  | Gtyp _ =>
      HiFP.qcons (HiFP.swire (v, N.of_nat offset) ft) acc  
  | Atyp atyp n =>
      let fix expand_wire_array_aux (n' : nat) (off : nat) (acc' : HiFP.hfstmt_seq) :=
        match n' with
        | 0 => acc'
        | S n'' =>
            expand_wire_array_aux n''
              (off + size_of_ftype atyp)
              (expand_wire_aux v off atyp acc')
        end
      in expand_wire_array_aux n offset acc
  | Btyp btyp =>
      expand_wire_btyp_aux v offset btyp acc
  end

with expand_wire_btyp_aux (v : VarOrder.t) (offset : nat) (btyp : ffield)
                          (acc : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  match btyp with
  | Fnil => acc
  | Fflips _ _ ft ff =>
      expand_wire_btyp_aux v
        (offset + size_of_ftype ft)
        ff
        (expand_wire_aux v offset ft acc)  
  end.

Definition expand_wire (v : VarOrder.t) (offset : nat) (ft : ftype)
                       (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  HiFP.qcatrev (expand_wire_aux v offset ft HiFP.qnil) sts.

Fixpoint expand_reg_nrst_aux (v : VarOrder.t) (offset : nat) (ft : ftype)
                             (clk : hfexpr ProdVarOrder.T)
                             (tmap : VM.t (ftype * fcomponent))
                             (acc : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match ft with
  | Gtyp _ =>
      Some (Qcons (HiFP.sreg (v, N.of_nat offset)
                              (mk_freg ft clk (NRst _))) acc)   (* 左附加 *)
  | Atyp atyp n =>
      let fix expand_reg_nrst_array_aux (n' : nat) (off : nat) (acc' : HiFP.hfstmt_seq) :=
        match n' with
        | 0 => Some acc'
        | S n'' =>
            match expand_reg_nrst_aux v off atyp clk tmap acc' with
            | Some acc'' =>
                expand_reg_nrst_array_aux n'' (off + size_of_ftype atyp) acc''
            | None => None
            end
        end
      in expand_reg_nrst_array_aux n offset acc
  | Btyp btyp =>
      expand_reg_nrst_btyp_aux v offset btyp clk tmap acc
  end

with expand_reg_nrst_btyp_aux (v : VarOrder.t) (offset : nat) (btyp : ffield)
                              (clk : hfexpr ProdVarOrder.T)
                              (tmap : VM.t (ftype * fcomponent))
                              (acc : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match btyp with
  | Fnil => Some acc
  | Fflips _ _ ft ff =>
      match expand_reg_nrst_aux v offset ft clk tmap acc with
      | Some acc' =>
          expand_reg_nrst_btyp_aux v (offset + size_of_ftype ft) ff clk tmap acc'
      | None => None
      end
  end.

Definition expand_reg_nrst (v : VarOrder.t) (offset : nat) (ft : ftype)
                           (clk : hfexpr ProdVarOrder.T)
                           (tmap : VM.t (ftype * fcomponent))
                           (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match expand_reg_nrst_aux v offset ft clk tmap HiFP.qnil with
  | Some acc => Some (HiFP.qcatrev acc sts)
  | None => None
  end.

Fixpoint expand_reg_rst (n : nat) (v : VarOrder.t) (clk rst_sig : hfexpr ProdVarOrder.T)
                        (rst_val : seq (hfexpr ProdVarOrder.T)) (ft_l : seq ftype)
                        (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match n, rst_val, ft_l with
  | 0, nil, nil => Some sts
  | S n', hd :: tl, ft :: ft_l' =>
      expand_reg_rst n' v clk rst_sig tl ft_l'
        (Qcons (HiFP.sreg (v, N.of_nat n') (mk_freg ft clk (Rst rst_sig hd))) sts)
  | _, _, _ => None
  end.

Definition expand_reg_aux (v : VarOrder.t) (r : hfreg VarOrder.T)
                          (tmap : VM.t (ftype * fcomponent))
                          (acc : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match r with
  | mk_freg ft clk NRst =>
      match expand_ground_expr clk tmap with
      | Some clk_p => expand_reg_nrst_aux v 0 ft clk_p tmap acc
      | _ => None
      end

  | mk_freg (Gtyp gt) clk (Rst rst_sig rst_val) =>
      match expand_ground_expr clk tmap,
            expand_ground_expr rst_sig tmap,
            expand_ground_expr rst_val tmap with
      | Some clk_p, Some rst_sig_p, Some rst_val_p =>
          Some (Qcons (HiFP.sreg (v, 0%num)
                       (mk_freg (Gtyp gt) clk_p (Rst rst_sig_p rst_val_p)))
                      acc)
      | _, _, _ => None
      end

  | mk_freg ft clk (Rst rst_sig rst_val) =>
      match expand_ground_expr clk tmap,
            expand_ground_expr rst_sig tmap,
            list_expr rst_val tmap with
      | Some clk_p, Some rst_sig_p, Some rst_val_l =>
          expand_reg_rst (size_of_ftype ft) v clk_p rst_sig_p
                         rst_val_l (list_ftype ft nil) acc
      | _, _, _ => None
      end
  end.

Definition expand_reg (v : VarOrder.t) (r : hfreg VarOrder.T)
                      (tmap : VM.t (ftype * fcomponent))
                      (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match expand_reg_aux v r tmap HiFP.qnil with
  | Some acc => Some (Qcatrev acc sts)
  | None => None
  end.

Fixpoint expand_invalid_aux (n : nat) (pv : ProdVarOrder.t)
                            (acc : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  match n with
  | 0 => acc
  | S n' =>
      expand_invalid_aux n'
        (fst pv, N.add (snd pv) 1%num)
        (Qcons (HiFP.sinvalid (Eid pv)) acc)
  end.

Definition expand_invalid (n : nat) (pv : ProdVarOrder.t)
                          (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  Some (HiFP.qcatrev (expand_invalid_aux n pv HiFP.qnil) sts).

Fixpoint expand_node_aux (v : VarOrder.t) (offset : nat) (el : seq HiFP.hfexpr)
                         (acc : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  match el with
  | nil => acc
  | hd :: tl =>
      expand_node_aux v (offset + 1) tl
        (Qcons (HiFP.snode (v, N.of_nat offset) hd) acc)
  end.

Definition expand_node (v : VarOrder.t) (offset : nat) (el : seq HiFP.hfexpr)
                       (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  Some (HiFP.qcatrev (expand_node_aux v offset el HiFP.qnil) sts).

Fixpoint expand_fcnct_nflip_aux (pv : ProdVarOrder.t) (el : seq HiFP.hfexpr)
                                (acc : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match el with
  | nil => Some acc
  | hd :: tl =>
      expand_fcnct_nflip_aux (fst pv, N.add (snd pv) 1%num) tl
        (Qcons (HiFP.sfcnct (Eid pv) hd) acc)
  end.

Definition expand_fcnct_nflip (pv : ProdVarOrder.t) (el : seq HiFP.hfexpr)
                              (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match expand_fcnct_nflip_aux pv el HiFP.qnil with
  | Some acc => Some (Qcatrev acc sts)
  | None => None
  end.

Fixpoint expand_fcnct_aux (pv0 pv1 : ProdVarOrder.t) (offset : nat) (flip : bool)
                          (ft : ftype) (acc : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match ft with
  | Gtyp _ =>
      let stmt :=
        if flip then
          HiFP.sfcnct (HiFP.eid (fst pv1, N.add (snd pv1) (N.of_nat offset)))
                      (Eref (HiFP.eid (fst pv0, N.add (snd pv0) (N.of_nat offset))))
        else
          HiFP.sfcnct (HiFP.eid (fst pv0, N.add (snd pv0) (N.of_nat offset)))
                      (Eref (HiFP.eid (fst pv1, N.add (snd pv1) (N.of_nat offset))))
      in
      Some (Qcons stmt acc)  
  | Atyp atyp n =>
      let fix expand_fcnct_array_aux (n' : nat) (off : nat) (acc' : HiFP.hfstmt_seq) :=
        match n' with
        | 0 => Some acc'
        | S n'' =>
            match expand_fcnct_aux pv0 pv1 off flip atyp acc' with
            | Some acc'' =>
                expand_fcnct_array_aux n'' (off + size_of_ftype atyp) acc''
            | None => None
            end
        end
      in expand_fcnct_array_aux n offset acc
  | Btyp btyp =>
      expand_fcnct_btyp_aux pv0 pv1 offset flip btyp acc
  end

with expand_fcnct_btyp_aux (pv0 pv1 : ProdVarOrder.t) (offset : nat) (flip : bool)
                           (btyp : ffield) (acc : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match btyp with
  | Fnil => Some acc
  | Fflips _ Nflip ft ff =>
      match expand_fcnct_aux pv0 pv1 offset flip ft acc with
      | Some acc' =>
          expand_fcnct_btyp_aux pv0 pv1 (offset + size_of_ftype ft) flip ff acc'
      | None => None
      end
  | Fflips _ Flipped ft ff =>
      match expand_fcnct_aux pv0 pv1 (negb flip) flip ft acc with
      | Some acc' =>
          expand_fcnct_btyp_aux pv0 pv1 (offset + size_of_ftype ft) flip ff acc'
      | None => None
      end
  end.

Definition expand_fcnct (pv0 pv1 : ProdVarOrder.t) (offset : nat) (flip : bool)
                        (ft : ftype) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match expand_fcnct_aux pv0 pv1 offset flip ft HiFP.qnil with
  | Some acc => Some (Qcatrev acc sts)
  | None => None
  end.

Fixpoint expandconnects_stmt_aux (s : HiF.hfstmt) (tmap : VM.t (ftype * fcomponent))
                                 (acc : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match s with
  | Sskip
  | Smem _ _ => Some (Qcons HiFP.sskip acc)  

  | Sinst v mv => Some (Qcons (HiFP.sinst (v, N0) (mv, N0)) acc)

  | Swire v t => Some (expand_wire_aux v 0 t acc)

  | Sreg v r => expand_reg_aux v r tmap acc  

  | Sinvalid ref =>
      match Sem_HiF.type_of_ref ref tmap, ref2pv ref tmap with
      | Some ft, Some pv => Some (expand_invalid_aux (size_of_ftype ft) pv acc)
      | _, _ => None
      end

  | Snode v e =>
      match list_expr e tmap with
      | Some el => Some (expand_node_aux v 0 (rev el) acc)
      | _ => None
      end

  | Sfcnct ref0 (Eref ref1) =>
      match ref2pv ref0 tmap, ref2pv ref1 tmap, Sem_HiF.type_of_ref ref0 tmap with
      | Some pv0, Some pv1, Some ft => expand_fcnct_aux pv0 pv1 0 false ft acc
      | _, _, _ => None
      end

  | Sfcnct ref e =>
      match ref2pv ref tmap, list_expr e tmap with
      | Some pv, Some el => expand_fcnct_nflip_aux pv (rev el) acc
      | _, _ => None
      end

  | Swhen c ss1 ss2 =>
      match expand_ground_expr c tmap with
      | Some c' =>
          match expandconnects_stmts_aux ss1 tmap HiFP.qnil,
                expandconnects_stmts_aux ss2 tmap HiFP.qnil with
          | Some acc1, Some acc2 =>
              let stmt := Swhen c' (Qcatrev acc1 HiFP.qnil) (Qcatrev acc2 HiFP.qnil) in
              Some (Qcons stmt acc)
          | _, _ => None
          end
      | None => None
      end
  end

with expandconnects_stmts_aux (ss : HiF.hfstmt_seq) (tmap : VM.t (ftype * fcomponent))
                              (acc : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match ss with
  | Qnil => Some acc
  | Qcons s ss' =>
      match expandconnects_stmt_aux s tmap acc with
      | Some acc' => expandconnects_stmts_aux ss' tmap acc'
      | None => None
      end
  end.

Definition expandconnects_stmt (s : HiF.hfstmt) (tmap : VM.t (ftype * fcomponent))
                               (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match expandconnects_stmt_aux s tmap HiFP.qnil with
  | Some acc => Some (Qcatrev acc sts)
  | None => None
  end.

Definition expandconnects_stmts (ss : HiF.hfstmt_seq) (tmap : VM.t (ftype * fcomponent))
                                (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match expandconnects_stmts_aux ss tmap HiFP.qnil with
  | Some acc => Some (Qcatrev acc sts)
  | None => None
  end.

Fixpoint expandconnects_fml (ml : list HiF.hfmodule) (tmap : VM.t (VM.t (ftype * fcomponent))) : option (list HiFP.hfmodule) :=
  match ml with
  | nil => Some nil
  | (FInmod mv ps ss) :: tl => match VM.find mv tmap with
                          | Some tmap_mod => let ps' := expand_ports ps nil in
                              (*match preprocess_subaccess_stmts ss HiFP.qnil with
                              | Some ss' =>
                                *)match expandconnects_stmts ss tmap_mod HiFP.qnil, expandconnects_fml tl tmap with
                                | Some sts, Some fml => Some ((HiFP.hfinmod (mv, N0) (rev ps') sts) :: fml)
                                | _, _ => None
                                end
                              (*| _ => None
                              end*)
                          | _ => None
                          end
  | _ :: tl => expandconnects_fml tl tmap
  end.

Definition expandconnects (c : HiF.hfcircuit) : option HiFP.hfcircuit :=
  match c, circuit_tmap c with
  | Fcircuit v ml, Some tmap => match expandconnects_fml ml tmap with
    | Some fml => Some (HiFP.fcircuit (v,N0) fml)
    | _ => None
    end
  | _, _ => None
  end.