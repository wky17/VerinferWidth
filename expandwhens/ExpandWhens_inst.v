From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From firrtl Require Import Env HiEnv LoFirrtl HiFirrtl.
From Lib Require Import Nbits Var.
From Semantics Require Import Semantics.

Definition merge_expr (cond : HiFP.hfexpr) (v1 v2 : def_expr) : def_expr :=
  match v1, v2 with
  | D_invalidated gt1, D_invalidated gt2 =>
      if gt1 == gt2
      then (D_fexpr (Sem_HiFP.indeterminate_cst gt1))
      else (D_fexpr (Emux cond (Sem_HiFP.indeterminate_cst gt1) (Sem_HiFP.indeterminate_cst gt2)))
  | D_invalidated gt, D_fexpr fe =>
      if (Sem_HiFP.indeterminate_cst gt) == fe
      then (D_fexpr fe)
      else (D_fexpr (Emux cond (Sem_HiFP.indeterminate_cst gt) fe)) 
  | D_fexpr te, D_invalidated gt =>
      if te == (Sem_HiFP.indeterminate_cst gt)
      then (D_fexpr te)
      else (D_fexpr (Emux cond te (Sem_HiFP.indeterminate_cst gt))) 
  | D_fexpr te, D_fexpr fe =>
      if te == fe
      then (D_fexpr te) 
      else (D_fexpr (Emux cond te fe))
  end.

Definition combine_true_connections cond big small : PVM.t def_expr :=
  PVM.fold (fun k v acc =>
    match PVM.find k big with
    | None => PVM.add k v acc               
    | Some v' => PVM.add k (merge_expr cond v v') acc
    end
  ) small big.

Definition combine_false_connections cond big small : PVM.t def_expr :=
  PVM.fold (fun k v acc =>
    match PVM.find k big with
    | None => PVM.add k v acc               
    | Some v' => PVM.add k (merge_expr cond v' v) acc
    end
  ) small big.

Definition combine_branches cond true_conn_map false_conn_map old_conn_map : PVM.t def_expr :=
  let combined := PVM.fold (fun k v acc =>
    match PVM.find k false_conn_map, PVM.find k old_conn_map with
    | Some v', _ => PVM.add k (merge_expr cond v v') acc
    | None, Some v' => PVM.add k (merge_expr cond v v') acc     
    | None, None => PVM.add k v acc     
    end
  ) true_conn_map (PVM.empty def_expr) in
  PVM.fold (fun k v acc =>
    match PVM.find k true_conn_map, PVM.find k old_conn_map with
    | None, Some v' => PVM.add k (merge_expr cond v' v) acc     
    | _, _ => acc
    end
  ) false_conn_map combined.

Fixpoint ExpandBranches_funs
(* split a statement sequence (possibly containing when
   statements) into a connection map.  The output does not contain when statements. *)
(ss           : HiFP.hfstmt_seq)   (* sequence of statements being translated *)
(old_conn_map : PVM.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
(scope_conn_map : PVM.t def_expr)
(tmap : PVM.t (fgtyp * fcomponent))
:   option ((PVM.t def_expr) * (PVM.t def_expr))
(* old_conn_map, extended with the connection statements in ss *)
:=  match ss with
| Qnil => Some (old_conn_map, scope_conn_map)
| Qcons s ss =>
    match ExpandBranch_fun s old_conn_map scope_conn_map tmap with
    | Some (temp_conn_map, temp_scope_conn_map) =>
        ExpandBranches_funs ss temp_conn_map temp_scope_conn_map tmap
    | None => None
    end
end
with ExpandBranch_fun
(* split a single statement (possibly consisting of a when
   statement) into a connection map.  The output does not contain when statements. *)
(s            : HiFP.hfstmt)       (* a single statement being translated *)
(old_conn_map : PVM.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
(scope_conn_map : PVM.t def_expr)
(tmap : PVM.t (fgtyp * fcomponent))
:   option ((PVM.t def_expr) * (PVM.t def_expr))
(* old_conn_map, extended with the connection statements in s *)
:=  match s with
| Sskip => Some (old_conn_map, scope_conn_map)
| Sreg var reg =>
    match type reg with
    | Gtyp gt => Some (PVM.add var (D_fexpr (Eref (Eid var))) old_conn_map, PVM.add var (D_fexpr (Eref (Eid var))) scope_conn_map)
    | _ => None
    end
| Sfcnct (Eid var) expr => Some (PVM.add var (D_fexpr expr) old_conn_map, PVM.add var (D_fexpr expr) scope_conn_map)
| Sfcnct _ expr => None
| Sinvalid (Eid var) => match PVM.find var tmap with
  | Some (gt, _) => Some (PVM.add var (D_invalidated gt) old_conn_map, PVM.add var (D_invalidated gt) scope_conn_map)
  | _ => None
  end
| Sinvalid _ => None
| Swhen cond ss_true ss_false =>
    match ExpandBranches_funs ss_true old_conn_map (PVM.empty def_expr) tmap with
    | Some (_, true_conn_map) =>
        match ExpandBranches_funs ss_false old_conn_map (PVM.empty def_expr) tmap with
        | Some (_, false_conn_map) =>
            let combined := combine_branches cond true_conn_map false_conn_map old_conn_map in 
            let new_scope := PVM.fold (fun k v acc => PVM.add k v acc) combined scope_conn_map in
            Some (PVM.fold (fun k v acc => PVM.add k v acc) combined old_conn_map, new_scope)
        | _ => None
        end
    | _ => None
    end
| _ => Some (old_conn_map, scope_conn_map) (* wire, mem, inst, node *)
end.

Fixpoint component_stmts_of_rev (ss : HiFP.hfstmt_seq) (acc : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  match ss with
  | Qnil => acc
  | Qcons s ss' =>
      let rev_s := component_stmt_of_rev s acc in
      component_stmts_of_rev ss' rev_s
  end

with component_stmt_of_rev (s : HiFP.hfstmt) (acc : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  match s with
  | Sskip
  | Sfcnct _ _
  | Sinvalid _ => acc
  | Swire _ _
  | Sreg _ _
  | Snode _ _
  | Smem _ _
  | Sinst _ _ => Qcons s acc
  | Swhen c ss_true ss_false =>
      let rev_s := component_stmts_of_rev ss_true acc in
      component_stmts_of_rev ss_false rev_s
  end.

Definition component_stmts_of (ss : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  Qcatrev (component_stmts_of_rev ss HiFP.qnil) HiFP.qnil.

Definition component_stmt_of (s : HiFP.hfstmt) : HiFP.hfstmt_seq :=
  Qcatrev (component_stmt_of_rev s HiFP.qnil) HiFP.qnil.

Fixpoint ExpandWhens_fun
    (ml : list HiFP.hfmodule) (tmap : (PVM.t (PVM.t (fgtyp * fcomponent)))) 
    (fml : list HiFP.hfmodule) (conn_map : PVM.t (PVM.t def_expr))
:   option ((list HiFP.hfmodule) * (PVM.t (PVM.t def_expr))) 
:=  match ml with
    | nil => Some (fml, conn_map)
    | (FInmod mv pp ss) :: tl => match PVM.find mv tmap with
        | Some tmap' => match ExpandBranches_funs ss (PVM.empty def_expr) (PVM.empty def_expr) tmap' with
            | Some (conn_map', _) =>
                let list1 := component_stmts_of_rev ss HiFP.qnil in
                let list2 := convert_to_connect_stmts conn_map' in
                let combined := Qcatrev list1 list2 in
                let fm := FInmod mv pp combined in
                ExpandWhens_fun tl tmap (fm :: fml) (PVM.add mv conn_map' conn_map)
            | None => None
            end
        | _ => None
        end
    | m :: tl => ExpandWhens_fun tl tmap (m :: fml) conn_map
    end.

Fixpoint addplaswire (instv : VarOrder.t) (offset : nat) (pl : seq HiFP.hfport) (tmap : PVM.t (fgtyp * fcomponent)) (vl : list ProdVarOrder.t) : option ((PVM.t (fgtyp * fcomponent)) * (list ProdVarOrder.t)) :=
  match pl with
  | nil => Some (tmap, vl)
  | Finput v (Gtyp t) :: tl => let pv := (instv, N.of_nat offset) in
      addplaswire instv (offset + 1) tl (PVM.add pv (t, Wire) tmap) (pv :: vl)
  | Foutput v (Gtyp t) :: tl => let pv := (instv, N.of_nat offset) in
      addplaswire instv (offset + 1) tl (PVM.add pv (t, Wire) tmap) (pv :: vl)
  | _ => None
  end.

(* functions used to record ftype and component type *)
Fixpoint stmts_tmap (modplmap : PVM.t (seq HiFP.hfport)) (tmap : PVM.t (fgtyp * fcomponent)) (vl : list ProdVarOrder.t) (ss : HiFP.hfstmt_seq): option ((PVM.t (fgtyp * fcomponent)) * (list ProdVarOrder.t)) :=
  match ss with
  | Qnil => Some (tmap, vl)
  | Qcons s ss' => match stmt_tmap modplmap tmap vl s with
      | Some (tmap', vl') => stmts_tmap modplmap tmap' vl' ss'
      | None => None
      end
  end
with stmt_tmap (modplmap : PVM.t (seq HiFP.hfport)) (tmap : PVM.t (fgtyp * fcomponent)) (vl : list ProdVarOrder.t) (s : HiFP.hfstmt) : option ((PVM.t (fgtyp * fcomponent)) * (list ProdVarOrder.t)) :=
  match s with
  | Sskip => Some (tmap, vl)
  | Sfcnct _ _ => Some (tmap, vl)
  | Sinvalid _ => Some (tmap, vl)
  | Smem v m => Some (tmap, vl) (* TBD *)
  | Sinst v mv => match PVM.find mv modplmap with
      | Some pl => addplaswire (fst v) 0 pl tmap vl
      | _ => None
      end
  | Swire v (Gtyp t) => match PVM.find v tmap with
      | None => Some (PVM.add v (t, Wire) tmap, v :: vl)
      | _ => None
      end
  | Swire v _ => None
  | Sreg v reg => match PVM.find v tmap, Sem_HiFP.type_of_hfexpr (clock reg) tmap, type reg with
      | None, Some _, Gtyp gt => Some (PVM.add v (gt, Register) tmap, v :: vl)
      | _, _, _ => None
      end
  | Snode v expr => match PVM.find v tmap, Sem_HiFP.type_of_hfexpr expr tmap with
                  | None, Some ft => Some (PVM.add v (ft, Node) tmap, vl)
                  | _, _ => None
                  end
  | Swhen _ ss_true ss_false =>
      match stmts_tmap modplmap tmap vl ss_true with
      | Some (tmap_true, vl_true) => stmts_tmap modplmap tmap_true vl_true ss_false 
      | _ => None
      end
  end.

Fixpoint modules_tmap (modplmap : PVM.t (seq HiFP.hfport)) (tmap : PVM.t (PVM.t (fgtyp * fcomponent))) 
  (whitelist_map : PVM.t (list ProdVarOrder.t)) (ml : seq HiFP.hfmodule) : option ((PVM.t (PVM.t (fgtyp * fcomponent))) * (PVM.t (list ProdVarOrder.t))):=
  match ml with
  | nil => Some (tmap, whitelist_map)
  | (FInmod mv ps ss) :: tl => match Sem_HiFP.ports_tmap' (PVM.empty (fgtyp * fcomponent)) ps with
              | Some pmap => match stmts_tmap modplmap pmap (fst (List.split (PVM.elements pmap))) ss with
                  | Some (tmap', whitelist) => modules_tmap modplmap (PVM.add mv tmap' tmap) (PVM.add mv whitelist whitelist_map) tl
                  | None => None
                  end
              | None => None
              end 
  | _ :: tl => modules_tmap modplmap tmap whitelist_map tl
  end.

Definition circuit_tmap (c : HiFP.hfcircuit) : option ((PVM.t (PVM.t (fgtyp * fcomponent))) * (PVM.t (list ProdVarOrder.t))) :=
  match c with
  | Fcircuit v ml => let modplmap := List.fold_left (fun acc m => 
      match m with
      | FInmod mv ps _ => PVM.add mv ps acc
      | FExmod mv ps _ => PVM.add mv ps acc
      end) ml (PVM.empty (seq HiFP.hfport)) in
    modules_tmap modplmap (PVM.empty (PVM.t (fgtyp * fcomponent))) (PVM.empty (list ProdVarOrder.t)) ml
  end.

Fixpoint ss_add_node_in_cm (ss : HiFP.hfstmt_seq) (mod_cm : PVM.t def_expr) : PVM.t def_expr :=
  match ss with
  | Qnil => mod_cm
  | Qcons (Snode v expr) ss' => ss_add_node_in_cm ss' (PVM.add v (D_fexpr expr) mod_cm)
  | Qcons (Swhen _ ss_true ss_false) ss' => ss_add_node_in_cm ss' (ss_add_node_in_cm ss_false (ss_add_node_in_cm ss_true mod_cm))
  | Qcons _ ss' => ss_add_node_in_cm ss' mod_cm
  end.

Fixpoint modules_add_node_in_cm (ml : seq HiFP.hfmodule) (conn_map : PVM.t (PVM.t def_expr)) : PVM.t (PVM.t def_expr) :=
  match ml with
  | nil => conn_map
  | (FInmod mv ps ss) :: tl => match PVM.find mv conn_map with
                              | Some mod_cm => modules_add_node_in_cm tl (PVM.add mv (ss_add_node_in_cm ss mod_cm) conn_map)
                              | None => modules_add_node_in_cm tl conn_map
                              end
  | _ :: tl => modules_add_node_in_cm tl conn_map
  end.

Definition expandWhens (c : HiFP.hfcircuit) : option (HiFP.hfcircuit * (PVM.t (PVM.t def_expr)) * (PVM.t (list ProdVarOrder.t))) :=
  match c, circuit_tmap c with
  | Fcircuit v ml, Some (tmap, vl_map) => match ExpandWhens_fun ml tmap nil (PVM.empty (PVM.t def_expr)) with
    | Some (fml, conn_map) => let conn_map' := modules_add_node_in_cm ml conn_map in
                              Some (Fcircuit v (List.rev fml), conn_map', vl_map)
    | _ => None
    end
  | _, _ => None
  end.
