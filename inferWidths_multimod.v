From HB Require Import structures.
From Coq Require Import ZArith Arith List Ascii String Lia FMaps.
From mathcomp Require Import all_ssreflect.
From Solver Require Import Env LoFirrtl HiEnv HiFirrtl constraints extract_cs extract_cswithmin extract_cs_multimod inferWidths.
Import ListNotations.

Module TripVar <: OrderedType.

  Definition t := (OrderedVarType.t * ProdVar.t)%type.
  Definition eq (x y : t) : Prop := (x.1 == y.1) /\ (x.2 == y.2).
  Lemma eq_refl (x : t) : eq x x.
  Proof. by split; apply eq_refl. Qed.

  Lemma eq_sym (x y : t) : eq x y -> eq y x.
  Proof. 
    move=> [H1 H2]. 
    split; rewrite eq_sym //. 
  Qed.

  Lemma eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof.
    move=> [Hxy1 Hxy2] [Hyz1 Hyz2].
    split;
    move /eqP : Hxy1 => Hxy1;
    move /eqP : Hxy2 => Hxy2;
    move /eqP : Hyz1 => Hyz1;
    move /eqP : Hyz2 => Hyz2.
    rewrite Hxy1 Hyz1 //.
    rewrite Hxy2 Hyz2 //.
  Qed.

  Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    move=> [x1 x2] [y1 y2].
    case Hx1y1: (OrderedVarType.eq_dec x1 y1) => [H1|H1].
    case Hx2y2: (ProdVar.eq_dec x2 y2) => [H2|H2].
    + left; split. simpl; assumption. simpl.
      specialize (eq_from_prodvar_eq x2 y2); intro.
      assert (x2 = y2). apply H. assumption. subst x2; done.
    + right; move=> [H3 H4]. 
      apply H2. apply eq_from_prodvar_eq. simpl in H4. 
      move /eqP : H4 => H4; done. 
    - right; move=> [H2 H3]. 
      apply H1. apply H2.
  Qed.

  Definition lt (x y : t) : Prop :=
    N.lt x.1 y.1 \/ ((fst x) == (fst y) /\ ProdVar.lt (snd x) (snd y)).
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros [x1 x2] [y1 y2] [z1 z2] [Hxy|Hxy] [Hyz|Hyz].
    - (* Case 1: x1 < y1 ∧ y1 < z1 *)
      left. apply N.lt_trans with y1; assumption.
    - (* Case 2: x1 < y1 ∧ y1 = z1 ∧ y2 < z2 *)
      left. simpl in Hxy; simpl in Hyz. move : Hyz => [Hyz1 _]. simpl. 
      move /eqP : Hyz1 => Hyz1.
      rewrite -Hyz1 //.
    - (* Case 3: x1 = y1 ∧ x2 < y2 ∧ y1 < z1 *)
      left. 
      move /eqP : Hxy.1 => Hxy1; simpl; simpl in Hxy1; simpl in Hyz.
      rewrite Hxy1 //.
    - (* Case 4: x1 = y1 ∧ x2 < y2 ∧ y1 = z1 ∧ y2 < z2 *)
      right. split; simpl;
      simpl in Hxy; move : Hxy => [Hxy1 Hxy2];
      simpl in Hyz; move : Hyz => [Hyz1 Hyz2].
      + move /eqP : Hyz1 => Hyz1.
        move /eqP : Hxy1 => Hxy1.
        rewrite Hxy1 Hyz1 //.
        apply ProdVar.lt_trans with y2; assumption.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros [x1 x2] [y1 y2] [Hlt|Hlt] [Heq1 Heq2].
    - (* Case 1: x1 < y1 ∧ x == y *)
      apply (OrderedVarType.lt_not_eq Hlt). apply Heq1.
    - (* Case 2: x1 = y1 ∧ x2 < y2 ∧ x == y *)
      apply (ProdVar.lt_not_eq Hlt.2). 
      simpl. apply eq_from_prodvar_eq. simpl in Heq2. 
      move /eqP : Heq2 => H4; done. 
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros [x1 x2] [y1 y2].
    case (OrderedVarType.compare x1 y1).
    - (* x1 < y1 *)
      intros; apply LT. left. assumption.
    - (* x1 = y1 *)
      case (ProdVar.compare x2 y2).
      + (* x2 < y2 *)
        intros; apply LT. right. split; simpl.
        rewrite e //. done.
      + (* x2 = y2 *)
        intros; apply EQ. split; simpl.
        assumption.
        assert (x2 = y2). apply eq_from_prodvar_eq.
        assumption. subst x2; done.
      + (* x2 > y2 *)
        intros; apply GT. right. split; simpl.
        move /eqP : e => e.
        rewrite e //. done.
    - (* x1 > y1 *)
      intros; apply GT. left. assumption.
  Defined.

Definition eqn (x y : t) : bool := (x.1 == y.1) && (x.2 == y.2).
Lemma eqP : Equality.axiom eqn.
Proof.
  rewrite /Equality.axiom /eqn.
  move => [x1 x2] [y1 y2].
    apply: (iffP idP).
    - simpl. move/andP => [/eqP -> /eqP ->]. by [].
    - by move=> [-> ->]; rewrite !eqxx.
Qed.

End TripVar.

HB.instance Definition _ := hasDecEq.Build TripVar.t TripVar.eqP.

Module TVM := VarMap TripVar.

Section constraint.

Definition term : Type := nat * TripVar.t.

Lemma eq_from_tripvar_eq : forall p1 p2 : TripVar.t, TripVar.eq p1 p2 <-> p1 = p2.
Proof.
  split; move : p1 p2.
  intros [x1 y1] [x2 y2] [H1 H2].
  simpl in H1; simpl in H2.
  move /eqP : H1 => H1.
  move /eqP : H2 => H2.
  rewrite H1 H2. 
  reflexivity. 
  intros [x1 y1] [x2 y2] Heq.
  injection Heq; intros.
  subst.
  split; (apply TripVar.eq_refl).
Qed.

Lemma term_dec : forall (x y : term), { eq x y } + { ~ eq x y }.
Proof. 
  intros [n1 p1] [n2 p2].
  destruct (Nat.eq_dec n1 n2) as [Hn | Hn].
  destruct (TripVar.eq_dec p1 p2) as [Hp | Hp].
  - left.
    + apply eq_from_tripvar_eq in Hp.
      rewrite Hn.
      rewrite Hp.
      reflexivity.
    + right.
      unfold not.
      intros H.
      injection H; intros.
      apply eq_from_tripvar_eq in H0.
      unfold not in Hp; apply Hp in H0.
      done.
  - right.
    unfold not.
    intros H.
    injection H; intros; subst.
    done.
Qed.

Definition term_eqn (x y : term) : bool :=
  (x.1 == y.1) && (x.2 == y.2).
Lemma term_eqP : Equality.axiom term_eqn.
Proof.
  unfold Equality.axiom, term_eqn.
  destruct x as [coe0 var0];
  destruct y as [coe1 var1]; simpl.
  destruct (coe0 == coe1) eqn: Hc ; move /eqP : Hc => Hc ;
        last by (apply ReflectF ; contradict Hc ; injection Hc ; done).
  rewrite Hc andTb.
  destruct (var0 == var1) eqn: Hv ; move /eqP : Hv => Hv ;
        last by (apply ReflectF ; contradict Hv ; injection Hv ; done).
  rewrite Hv. apply ReflectT; done.
Qed.

HB.instance Definition _ := hasDecEq.Build term term_eqP.

Definition terms := list term.
Fixpoint terms_eqn (x y : terms) : bool :=
  match x,y with
  | nil, nil => true
  | t0 :: tl0, t1 :: tl1 => (t0 == t1) && (terms_eqn tl0 tl1)
  | _, _ => false
  end.

Lemma terms_eqP : Equality.axiom terms_eqn.
Proof.
  unfold Equality.axiom.
  move=> x y.
  elim: x y => [|x xs IHx] y /=.
  - (* x = nil *)
    case: y => [|y ys] /=.
    + (* y = nil *)
      apply ReflectT; reflexivity.
    + (* y = y::ys *)
      apply ReflectF; discriminate.
  
  - (* x = x::xs *)
    case: y => [|y ys] /=.
    + (* y = nil *)
      apply ReflectF; discriminate.
    + (* y = y::ys *)
      move: (term_eqP x y) => [Hxy_eq|Hxy_neq].
      * (* x == y *)
        rewrite Hxy_eq /=.
        move: (IHx ys) => [Hxsys_eq|Hxsys_neq].
        -- (* xs 和 ys *)
          rewrite Hxsys_eq eq_refl. apply ReflectT. done.
        -- (* xs 和 ys *)
          rewrite eq_refl. simpl. apply ReflectF.
          contradict Hxsys_neq. inversion Hxsys_neq. done.
      * (* x != y *)
        assert ((x==y)=false). apply not_true_iff_false. intro. move /eqP : H => H; subst x; done. rewrite H. simpl. apply ReflectF.
        contradict Hxy_neq. inversion Hxy_neq. done.
Qed.

HB.instance Definition _ := hasDecEq.Build terms terms_eqP.

Record regular_rhs : Type := {
  regular_const : Z.t;
  regular_terms : list (nat * TripVar.t); 
  regular_power : list (nat * TripVar.t) 
}.

Definition make_rhs a b c : regular_rhs :=
  {|regular_const := c;
    regular_terms := a;
    regular_power := b|}.

Definition split_rhs a : list term * list term * Z.t :=
  (regular_terms a, regular_power a, regular_const a).

Inductive min_rhs : Type :=
  | Expr : regular_rhs -> min_rhs
  | Min : min_rhs -> min_rhs -> min_rhs.

Definition terms_value (v : TVM.t nat) (terms : list (nat * TripVar.t)) (init : Z.t) : Z.t :=
  fold_left (fun acc ax => 
                            let vi := match TVM.find ax.2 v with
                            | Some val => val
                            | None => 0
                            end in
                            Z.add acc (Z.of_nat (ax.1 * vi))) terms init.

Definition power_value (v : TVM.t nat) (terms : list (nat * TripVar.t)) : Z.t :=
  match terms with
  | nil => 0
  | _ => let n := terms_value v terms 0 in Z.pow 2 n
  end.

Fixpoint min_rhs_value (v : TVM.t nat) (rhs : min_rhs) : Z.t :=
  match rhs with
  | Expr r => terms_value v (regular_terms r) (regular_const r) + power_value v (regular_power r)
  | Min e1 e2 => Z.min (min_rhs_value v e1) (min_rhs_value v e2)
  end.
  
(* inequality of form: lhs_ >= min(fr1_ + const1_, fr2_ + const2_)
This is introduced to indicate the "rem" operation
  e.g. z <= rem(x,y) indicates lhs_(w_z), fr1_(w_x), const1_(0), fr2_(w_y),
  const2_(0)
The use of "const" here is to take into account the case where the expression
is a constant. However, it is not actually utilized because in MLIR,
constants are also declared with variable names. *)
Record Constraint_Min : Type := {
  lhs_var_min : TripVar.t;
  rhs_expr_min : min_rhs
}.
  
Fixpoint min_rhs_add_cst (temp_e : min_rhs) (cst : Z.t) :=
  match temp_e with
  | Expr e => Expr (make_rhs (regular_terms e) (regular_power e) (Z.add (regular_const e) cst))
  | Min e1 e2 => Min (min_rhs_add_cst e1 cst) (min_rhs_add_cst e2 cst)
  end.

Fixpoint list_min_rhs (temp_e : min_rhs) res : list regular_rhs :=
  match temp_e with
  | Expr e => e :: res
  | Min e1 e2 => list_min_rhs e2 (list_min_rhs e1 res)
  end.

Definition combine_term (t1 : term) (t2 : list term) : list term := 
  match List.find (fun p : term => snd p == t1.2) t2 with
  | None => t1 :: t2 
  | Some t =>
      (t.1 + t1.1, t1.2) :: (List.remove term_dec t t2)
  end.

Definition combine_terms (t1 t2 : (list term * list term * Z.t)) : list term * list term * Z.t := 
  let '(terms1, _, cst1) := t1 in
  let '(terms2, _, cst2) := t2 in
  let new_terms := fold_left (fun acc term =>
    combine_term term acc) terms2 terms1 in
  (new_terms, nil, Z.add cst1 cst2). 

Definition default_min : min_rhs := Expr {|regular_const := 0%Z;
  regular_terms := nil;
  regular_power := nil|}.

Fixpoint regulars2min (el : list regular_rhs) : min_rhs :=
  match el with
  | nil => default_min
  | [hd] => Expr hd
  | hd :: tl => Min (Expr hd) (regulars2min tl)
  end.

Definition combine_min_rhs (e1 e2 : min_rhs) : min_rhs :=
  let el1 := list_min_rhs e1 [] in
  let el2 := list_min_rhs e2 [] in
  let nel := map (fun '(temp_e1, temp_e2) => let '(a, b, c) := combine_terms (split_rhs temp_e1) (split_rhs temp_e2) in
                                  make_rhs a b c) (cartesian el1 el2) in 
  regulars2min nel.

Fixpoint min_rhs_add_power (temp_e : min_rhs) (pv : TripVar.t) :=
  match temp_e with
  | Expr e => Expr (make_rhs (regular_terms e) [(1, pv)] (Z.sub (regular_const e) 1%Z))
  | Min e1 e2 => Min (min_rhs_add_power e1 pv) (min_rhs_add_power e2 pv)
  end.

Record Constraint1 : Type := {
  lhs_var1 : TripVar.t;  
  rhs_const1 : Z.t;
  rhs_terms1 : terms; 
  rhs_power : terms 
}.

Fixpoint seperate_min (pv : TripVar.t) (el : list min_rhs) (res : list Constraint1 * list Constraint_Min) : list Constraint1 * list Constraint_Min :=
  match el with
  | nil => res
  | Expr e :: tl => let '(a, b, c) := split_rhs e in
                    let nc := {|
                      lhs_var1 := pv;
                      rhs_const1 := c;
                      rhs_power := b;
                      rhs_terms1 := a
                    |} in
                    seperate_min pv tl (nc :: res.1, res.2)
  | hd :: tl => let nc := {|
                      lhs_var_min := pv;
                      rhs_expr_min := hd
                    |} in
                    seperate_min pv tl (res.1, nc :: res.2)
  end.

Definition list_Constraint_Min (minc : Constraint_Min) : list Constraint1 :=
  let rhs_ls := list_min_rhs (rhs_expr_min minc) nil in
  map (fun r => let '(a,b,c) := split_rhs r in
                {|lhs_var1 := lhs_var_min minc;
                  rhs_terms1 := a;
                  rhs_power := b;
                  rhs_const1 := c|}) rhs_ls.

Fixpoint add_cs1_2_c1map (cs : list Constraint1) (c1map : TVM.t (list Constraint1)) : TVM.t (list Constraint1) :=
  match cs with
  | nil => c1map
  | hd :: tl => let nmap := match TVM.find (lhs_var1 hd) c1map with
                            | Some cs1 => TVM.add (lhs_var1 hd) (hd :: cs1) c1map
                            | _ => TVM.add (lhs_var1 hd) [hd] c1map
                            end
                          in add_cs1_2_c1map tl nmap
  end.

Definition rhs_value1 (v: TVM.t nat) (c : Constraint1) : Z.t :=
  terms_value v c.(rhs_terms1) c.(rhs_const1) + power_value v c.(rhs_power).

Definition satisfies_constraint1 (v: TVM.t nat) (c: Constraint1) : bool :=
  match TVM.find c.(lhs_var1) v with
  | Some val => Z.leb (rhs_value1 v c) (Z.of_nat val)
  | None => false
  end.

Record Constraint2 : Type := {
  lhs_const2 : nat; 
  rhs_terms2 : terms 
}.

Definition satisfies_constraint2 (v: TVM.t nat) (c: Constraint2) : bool :=
  let total := List.fold_left (fun acc '(bi, xi) => 
                            let vi := match TVM.find xi v with
                            | Some val => val
                            | None => 0 
                            end in
                            acc + (bi * vi)) 
                         c.(rhs_terms2) 0
  in Nat.leb total c.(lhs_const2).

Definition rhs_vars (c : Constraint1) : list TripVar.t :=
  map snd (rhs_terms1 c) ++ map snd (rhs_power c).

Definition remove_power1 (value : TVM.t nat) (c : Constraint1) : Constraint1 :=
  {|
    lhs_var1 := lhs_var1 c;
    rhs_terms1 := rhs_terms1 c;
    rhs_power := nil;
    rhs_const1 := Z.add (rhs_const1 c) (power_value value (rhs_power c))
  |}.

Definition remove_power_regular (value : TVM.t nat) (r : regular_rhs) : regular_rhs :=
  {|
    regular_terms := regular_terms r;
    regular_power := nil;
    regular_const := Z.add (regular_const r) (power_value value (regular_power r))
  |}.

Fixpoint remove_power_min_rhs (value : TVM.t nat) (rhs : min_rhs) : min_rhs :=
  match rhs with
  | Expr r => Expr (remove_power_regular value r)
  | Min min1 min2 => Min (remove_power_min_rhs value min1) (remove_power_min_rhs value min2)
  end.

Definition remove_power_min (value : TVM.t nat) (c : Constraint_Min) : Constraint_Min :=
  {|
    lhs_var_min := lhs_var_min c;
    rhs_expr_min := remove_power_min_rhs value (rhs_expr_min c)
  |}.

End constraint.

Section Extract_Constraints_for_multimod.

Fixpoint find_ref_inside (instv : VM.key) (r : href) : option href :=
  match r with
  | Eid v => None
  | Esubfield (Eid instv) v => Some (Eid v)
  | Esubfield ref v => match find_ref_inside instv ref with
                      | Some subref => Some (Esubfield subref v)
                      | _ => None
                      end
  | Esubindex ref n => match find_ref_inside instv ref with
                      | Some subref => Some (Esubindex subref n)
                      | _ => None
                      end
  | Esubaccess ref e => match find_ref_inside instv ref with
                      | Some subref => Some (Esubaccess subref e)
                      | _ => None
                      end
  end.

Compute (find_ref_inside (N.of_nat 4) (Esubfield (Eid (N.of_nat 4)) (N.of_nat 1))).
Compute (find_ref_inside (N.of_nat 4) (Esubfield (Esubfield (Eid (N.of_nat 4)) (N.of_nat 0)) (N.of_nat 1))).

Definition ref2pv_mod (r : href) (mv : VM.key) (instmap : VM.t VM.key)(* mapping known instance name to module name *) 
  (tmap : VM.t (VM.t (ftype * forient))) : option TripVar.t :=
  let base_ref := base_id r in
  match VM.find base_ref instmap with
  | Some inst_mv => (* base_ref 是inst名，inst_mv 是对应module名 *)
      match find_ref_inside base_ref r, VM.find inst_mv tmap with
      | Some inst_ref, Some inst_tmap => match ref2pv inst_ref inst_tmap with
          | Some pv => Some (inst_mv, pv)
          | _ => None
          end
      | _, _ => None
      end
  | _ => (* r是本mod中的普通cmpnt *)
      match VM.find mv tmap with
      | Some mod_tmap => match ref2pv r mod_tmap with
          | Some pv => Some (mv, pv)
          | _ => None
          end
      | _ => None
      end
  end.

Fixpoint extract_constraint_expr_mod (mv : VM.key) (e : hfexpr) (mod_tmap : VM.t (ftype * forient)) (tmap : VM.t (VM.t (ftype * forient))) (instmap : VM.t VM.key) 
  : option ((list min_rhs) * (list min_rhs)) :=
  (* min_rhs 的 Expr case 是一条phi1约束的一次项，指数项和常数项。rem产生min_rhs 中的 Min case
     mux 直接生成 list of min_rhs
     constraint2 来自 mux的condition*)
  match e with
  | Eref r => match type_of_ref r mod_tmap, ref2pv_mod r mv instmap tmap with
                            | Some (Gtyp (Fuint_implicit _)), Some pv 
                            | Some (Gtyp (Fsint_implicit _)), Some pv => Some ([Expr (make_rhs [(1, pv)] nil 0%Z)], nil)
                            | Some (Gtyp gt), _ => Some ([Expr (make_rhs nil nil (Z.of_nat (sizeof_fgtyp gt)))], nil)
                            | _, _ => None
                            end
  | Econst t bs => match t with
                            | Fuint_implicit _ 
                            | Fsint_implicit _ => Some ([Expr (make_rhs nil nil (Z.of_nat (size bs)))], nil)
                            | t => Some ([Expr (make_rhs nil nil (Z.of_nat (sizeof_fgtyp t)))], nil)
                            end
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                            extract_constraint_expr_mod mv e1 mod_tmap tmap instmap, extract_constraint_expr_mod mv e2 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (map (fun '(a,b) => Min a b) (cartesian el1 el2), cs1 ++ cs2)
                            | _, _, _, _ => None 
                            end
  | Ecast AsUInt e1 
  | Ecast AsSInt e1 => match type_of_hfexpr e1 mod_tmap with
                            | Some (exist (Gtyp _) _) => extract_constraint_expr_mod mv e1 mod_tmap tmap instmap
                            | _ => None
                            end
  | Eprim_unop Unot e1 => match type_of_hfexpr e1 mod_tmap with
                            | Some (exist (Gtyp (Fsint w)) _)
                            | Some (exist (Gtyp (Fuint w)) _) => extract_constraint_expr_mod mv e1 mod_tmap tmap instmap
                            | _ => None
                            end
  | Ecast AsClock e1 
  | Ecast AsAsync e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                            | Some (exist (Gtyp _) _), Some (_, cs) => Some ([Expr (make_rhs nil nil 1%Z)], cs)
                            | _, _ => None
                            end
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => Some (Expr (make_rhs nil nil (Z.of_nat n)) :: el, cs)
                            | _, _ => None
                            end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs) 
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.of_nat n)) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs) => 
                              let nexp := map (fun temp_e => min_rhs_add_cst temp_e (Z.opp (Z.of_nat n))) el in
                                Some (Expr (make_rhs nil nil 1%Z) :: nexp, cs) 
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => 
                                Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.opp (Z.of_nat n))) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (el, cs) => Some (el, cs)
                            | Some (exist (Gtyp (Fuint _)) _), Some (el, cs) => 
                                Some (map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop Uneg e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (el, cs) 
                            | Some (exist (Gtyp (Fuint _)) _), Some (el, cs) => 
                                Some (map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el, cs)
                            | _, _ => None
                            end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => (*if (n2 <= n1) && (n1 < w) then *)
                                Some ([Expr (make_rhs nil nil (Z.of_nat (n1 - n2 + 1)))], cs) (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => (*if n <= w then *)
                                Some ([Expr (make_rhs nil nil (Z.of_nat n))], cs) (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fsint w)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint w)) _), Some (el, cs) => (*if n <= w then *)
                                Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.opp (Z.of_nat n))) el, cs)
                              (*else None*)
                            | _, _ => None
                            end
  | Eprim_unop _ e1 => match type_of_hfexpr e1 mod_tmap, extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (el, cs)
                            | Some (exist (Gtyp (Fuint _)) _), Some (el, cs) => 
                              Some ([Expr (make_rhs nil nil 1%Z)], cs)
                            | _, _ => None
                            end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 mod_tmap tmap instmap, extract_constraint_expr_mod mv e2 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _), Some (el1, cs1), Some (el2, cs2)
                            | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _), Some (el1, cs1), Some (el2, cs2) => 
                                Some ([Expr (make_rhs nil nil 1%Z)], cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 mod_tmap tmap instmap, extract_constraint_expr_mod mv e2 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                                let nexp1 := map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el1 in
                                let nexp2 := map (fun temp_e => min_rhs_add_cst temp_e 1%Z) el2 in
                                Some (nexp1 ++ nexp2, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 mod_tmap tmap instmap, extract_constraint_expr_mod mv e2 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (map (fun '(e1, e2) => combine_min_rhs e1 e2) (cartesian el1 el2), cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 mod_tmap tmap instmap, extract_constraint_expr_mod mv e2 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1, cs1 ++ cs2)
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.opp 1%Z)) el1, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1) =>
                                match e2 with
                                | Eref r => match type_of_ref r mod_tmap, ref2pv_mod r mv instmap tmap with
                                          | Some (Gtyp (Fuint_implicit _)), Some pv => Some (map (fun temp_e => min_rhs_add_power temp_e pv) el1, cs1)
                                          | Some (Gtyp (Fuint w)), _ => 
                                            Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.sub (Z.pow 2 (Z.of_nat w)) 1)) el1, cs1)
                                          | _, _ => None
                                          end
                                | Econst t bs => match t with
                                          | Fuint_implicit _ 
                                          | Fsint_implicit _ => Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.sub (Z.pow 2 (Z.of_nat (size bs))) 1)) el1, cs1)
                                          | t => Some (map (fun temp_e => min_rhs_add_cst temp_e (Z.sub (Z.pow 2 (Z.of_nat (sizeof_fgtyp t))) 1)) el1, cs1)
                                          end
                                | _ => None
                                end
                            | _, _, _ => None
                            end
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 mod_tmap tmap instmap, extract_constraint_expr_mod mv e2 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2)
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 mod_tmap tmap instmap, extract_constraint_expr_mod mv e2 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                                Some (map (fun '(e1, e2) => combine_min_rhs e1 e2) (cartesian el1 el2), cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 mod_tmap, type_of_hfexpr e2 mod_tmap,
                                    extract_constraint_expr_mod mv e1 mod_tmap tmap instmap, extract_constraint_expr_mod mv e2 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _), Some (el1, cs1), Some (el2, cs2) 
                            | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1 ++ el2, cs1 ++ cs2)
                            | _, _, _, _ => None
                            end
  | Emux c e1 e2 => match type_of_hfexpr c mod_tmap, extract_constraint_expr_mod mv c mod_tmap tmap instmap,
                                    extract_constraint_expr_mod mv e1 mod_tmap tmap instmap, extract_constraint_expr_mod mv e2 mod_tmap tmap instmap with
                            | Some (exist (Gtyp (Fuint _)) _), Some (ec, cs0), Some (el1, cs1), Some (el2, cs2) => 
                              Some (el1 ++ el2, ec ++ cs0 ++ cs1 ++ cs2)
                            | _, _, _, _ => None
                            end (* condition c 只能是 0/1位宽 *)
end.

Fixpoint extract_mux_mod (mv : VM.key) (instmap : VM.t VM.key) (e : hfexpr) (mod_tmap : VM.t (ftype * forient)) (tmap : VM.t (VM.t (ftype * forient))) : option (list href * list min_rhs) := 
match VM.find mv tmap with
| Some mod_tmap => 
  match e with
  | Eref r => Some ([r], nil)
  | Emux c e1 e2 => match type_of_hfexpr c mod_tmap, extract_constraint_expr_mod mv c mod_tmap tmap instmap, 
                          extract_mux_mod mv instmap e1 mod_tmap tmap, extract_mux_mod mv instmap e2 mod_tmap tmap with
                  | Some (exist (Gtyp (Fuint _)) _), Some (ec, cs0), Some (r1, cs1), Some (r2, cs2) => 
                    Some (r1 ++ r2, ec ++ cs0 ++ cs1 ++ cs2)
                  | _, _, _, _ => None
                  end
  | _ => None
  end
| _ => None
end.

Fixpoint extract_constraint_passive (ft ft_ref : ftype) (pv pvar : TripVar.t) (c1map : TVM.t (list Constraint1)) : TVM.t (list Constraint1) :=
  match ft, ft_ref with 
  | Gtyp (Fuint_implicit _), Gtyp (Fuint_implicit _)
  | Gtyp (Fsint_implicit _), Gtyp (Fsint_implicit _) => 
                                let nc := {|
                                 lhs_var1 := pv;
                                 rhs_const1 := 0;
                                 rhs_power := nil;
                                 rhs_terms1 := [(1, pvar)]
                               |} in
                               match TVM.find pv c1map with
                               | Some cs1 => TVM.add pv (nc :: cs1) c1map
                               | _ => TVM.add pv [nc] c1map
                               end
  | Gtyp (Fuint_implicit _), Gtyp (Fuint w)
  | Gtyp (Fsint_implicit _), Gtyp (Fsint w) => 
                                let nc := {|
                                 lhs_var1 := pv;
                                 rhs_const1 := Z.of_nat w;
                                 rhs_power := nil;
                                 rhs_terms1 := []
                               |} in
                               match TVM.find pv c1map with
                               | Some cs1 => TVM.add pv (nc :: cs1) c1map
                               | _ => TVM.add pv [nc] c1map
                               end
  | Atyp atyp _, Atyp atyp_ref _ => extract_constraint_passive atyp atyp_ref pv pvar c1map
  | Btyp ff, Btyp ff_ref => extract_constraint_passive_f ff ff_ref pv pvar c1map
  | _, _ => c1map
  end
with extract_constraint_passive_f (ff ff_ref : ffield) (pv pvar : TripVar.t) (c1map : TVM.t (list Constraint1)) : TVM.t (list Constraint1) :=
  match ff, ff_ref with
  | Fnil, Fnil => c1map
  | Fflips _ Nflip t fs, Fflips _ Nflip t_ref fs_ref => let nmap := extract_constraint_passive t t_ref pv pvar c1map in 
                           extract_constraint_passive_f fs fs_ref (pv.1, (pv.2.1, N.add pv.2.2 (N.of_nat (size_of_ftype t)))) (pvar.1, (pvar.2.1, N.add pvar.2.2 (N.of_nat (size_of_ftype t)))) nmap
  | _, _ => c1map
  end.

Fixpoint extract_constraint_non_passive (ft ft_ref : ftype) (flip : bool) (pv pvar : TripVar.t) (c1map : TVM.t (list Constraint1)): TVM.t (list Constraint1) :=
  match ft, ft_ref with 
  | Gtyp (Fuint_implicit _), Gtyp (Fuint_implicit _)
  | Gtyp (Fsint_implicit _), Gtyp (Fsint_implicit _) => if flip == false then
                                let nc := {|
                                 lhs_var1 := pv;
                                 rhs_power := nil;
                                 rhs_const1 := 0;
                                 rhs_terms1 := [(1, pvar)]
                               |} in
                               match TVM.find pv c1map with
                               | Some cs1 => TVM.add pv (nc :: cs1) c1map
                               | _ => TVM.add pv [nc] c1map
                               end else 
                               let nc := {|
                                 lhs_var1 := pvar;
                                 rhs_power := nil;
                                 rhs_const1 := 0;
                                 rhs_terms1 := [(1, pv)]
                               |} in
                               match TVM.find pvar c1map with
                               | Some cs1 => TVM.add pvar (nc :: cs1) c1map
                               | _ => TVM.add pvar [nc] c1map
                               end
  | Gtyp (Fuint_implicit _), Gtyp (Fuint w)
  | Gtyp (Fsint_implicit _), Gtyp (Fsint w) => if flip == false then
                                let nc := {|
                                 lhs_var1 := pv;
                                 rhs_const1 := Z.of_nat w;
                                 rhs_power := nil;
                                 rhs_terms1 := []
                               |} in
                               match TVM.find pv c1map with
                               | Some cs1 => TVM.add pv (nc :: cs1) c1map
                               | _ => TVM.add pv [nc] c1map
                               end else c1map
  | Gtyp (Fuint w), Gtyp (Fuint_implicit _)
  | Gtyp (Fsint w), Gtyp (Fsint_implicit _) => if flip == false then c1map else
                                let nc := {|
                                 lhs_var1 := pvar;
                                 rhs_const1 := Z.of_nat w;
                                 rhs_power := nil;
                                 rhs_terms1 := []
                               |} in
                               match TVM.find pvar c1map with
                               | Some cs1 => TVM.add pvar (nc :: cs1) c1map
                               | _ => TVM.add pvar [nc] c1map
                               end
  | Atyp atyp _, Atyp atyp_ref _ => extract_constraint_non_passive atyp atyp_ref flip pv pvar c1map
  | Btyp ff, Btyp ff_ref => extract_constraint_non_passive_f ff ff_ref flip pv pvar c1map
  | _, _ => c1map
  end
with extract_constraint_non_passive_f (ff ff_ref : ffield) (flip : bool) (pv pvar : TripVar.t) (c1map : TVM.t (list Constraint1)) : TVM.t (list Constraint1) :=
  match ff, ff_ref with
  | Fnil, Fnil => c1map
  | Fflips _ Nflip t fs, Fflips _ Nflip t_ref fs_ref => let nmap := extract_constraint_non_passive t t_ref flip pv pvar c1map in 
                           extract_constraint_non_passive_f fs fs_ref flip (pv.1, (pv.2.1, N.add pv.2.2 (N.of_nat (size_of_ftype t)))) (pvar.1, (pvar.2.1, N.add pvar.2.2 (N.of_nat (size_of_ftype t)))) nmap
  | Fflips _ Flipped t fs, Fflips _ Flipped t_ref fs_ref => let nmap := extract_constraint_non_passive t t_ref (~~flip) pv pvar c1map in
                           extract_constraint_non_passive_f fs fs_ref flip (pv.1, (pv.2.1, N.add pv.2.2 (N.of_nat (size_of_ftype t)))) (pvar.1, (pvar.2.1, N.add pvar.2.2 (N.of_nat (size_of_ftype t)))) nmap
  | _, _ => c1map
  end.

Fixpoint extract_constraint_ss (mv : VM.key) (ss : hfstmt_seq) (mod_tmap : VM.t (ftype * forient)) (tmap : VM.t (VM.t (ftype * forient))) (c1map : TVM.t (list Constraint1)) 
  (cs2 : list min_rhs) (cs_min : list Constraint_Min) (instmap : VM.t VM.key) 
  : option (TVM.t (list Constraint1) * list min_rhs * list Constraint_Min * VM.t VM.key) :=
  match ss with
  | Qnil => Some (c1map, cs2, cs_min, instmap)
  | Qcons s st => 
    match extract_constraint_s mv s mod_tmap tmap c1map cs2 cs_min instmap with
    | Some (c1map', cs2', cs_min', instmap') => extract_constraint_ss mv st mod_tmap tmap c1map' cs2' cs_min' instmap'
    | _ => None
    end
  end
with extract_constraint_s (mv : VM.key) (s : hfstmt) (mod_tmap : VM.t (ftype * forient)) (tmap : VM.t (VM.t (ftype * forient))) (c1map : TVM.t (list Constraint1)) 
  (cs2 : list min_rhs) (cs_min : list Constraint_Min) (instmap : VM.t VM.key) 
  : option (TVM.t (list Constraint1) * list min_rhs * list Constraint_Min * VM.t VM.key) :=
  match s with
  | Sinst inst_v inst_mv => Some (c1map, cs2, cs_min, VM.add inst_v inst_mv instmap)
  | Sfcnct r expr => match type_of_ref r mod_tmap with
                    | Some (Gtyp gt) => if not_implicit gt then Some (c1map, cs2, cs_min, instmap)
                        else match ref2pv_mod r mv instmap tmap, extract_constraint_expr_mod mv expr mod_tmap tmap instmap with
                            | Some pv, Some (exprs, cs2') =>
                              let (regular_cs, cs_min') := seperate_min pv exprs (nil, nil) in
                              let nmap := match TVM.find pv c1map with
                                | Some cs1 => TVM.add pv (regular_cs ++ cs1) c1map
                                | _ => TVM.add pv regular_cs c1map
                                end
                              in Some (nmap, cs2 ++ cs2', cs_min ++ cs_min', instmap)
                            | _, _ => None
                            end
                    | Some ft => match expr with
                            | Eref ref => match ref2pv_mod r mv instmap tmap, ref2pv_mod ref mv instmap tmap, 
                                                type_of_ref ref mod_tmap with
                                        | Some pv, Some pvar, Some ft_ref => 
                                          let nmap := extract_constraint_non_passive ft ft_ref false pv pvar c1map in 
                                          Some (nmap, cs2, cs_min, instmap)
                                        | _, _, _ => None
                                        end
                            | Emux c e0 e1 => match ref2pv_mod r mv instmap tmap, extract_mux_mod mv instmap expr mod_tmap tmap with
                                        | Some pv, Some (rhsl, cs2') => 
                                            let nmap := fold_left (fun temp_map ref0 => 
                                                match ref2pv_mod ref0 mv instmap tmap, type_of_ref ref0 mod_tmap with
                                                | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref pv pvar temp_map
                                                | _, _ => temp_map
                                                end) rhsl c1map in Some (nmap, cs2 ++ cs2', cs_min, instmap)
                                        | _, _ => None
                                        end
                            | _ => None
                            end
                    | _ => None
                    end
  | Sreg v reg => let pv_reg := (mv, (v, N0)) in
                match type reg with
                | Gtyp gt => if not_implicit gt then Some (c1map, cs2, cs_min, instmap)
                    else match reset reg with
                    | NRst => Some (c1map, cs2, cs_min, instmap)
                    | Rst _ rst_val => match extract_constraint_expr_mod mv rst_val mod_tmap tmap instmap with
                                      | Some (exprs, cs2') => 
                                        let (regular_cs, cs_min') := seperate_min pv_reg exprs (nil, nil) in
                                        let nmap := match TVM.find pv_reg c1map with
                                          | Some cs1 => TVM.add pv_reg (regular_cs ++ cs1) c1map
                                          | _ => TVM.add pv_reg regular_cs c1map
                                          end
                                        in Some (nmap, cs2 ++ cs2', cs_min ++ cs_min', instmap)
                                      | _ => None
                                      end
                    end
                | ft => (* reg 只能passive *)
                        match reset reg with
                        | NRst => Some (c1map, cs2, cs_min, instmap)
                        | Rst _ rst_val => match rst_val with
                                      | Eref ref => match ref2pv_mod ref mv instmap tmap, type_of_ref ref mod_tmap with
                                                  | Some pvar, Some ft_ref => 
                                                    let nmap := extract_constraint_passive ft ft_ref pv_reg pvar c1map in 
                                                    Some (nmap, cs2, cs_min, instmap)
                                                  | _, _ => None
                                                  end
                                      | Emux c e0 e1 => match extract_mux_mod mv instmap rst_val mod_tmap tmap with
                                                  | Some (rhsl, cs2') => 
                                                      let nmap := fold_left (fun temp_map ref0 => 
                                                          match ref2pv_mod ref0 mv instmap tmap, type_of_ref ref0 mod_tmap with
                                                          | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref pv_reg pvar temp_map
                                                          | _, _ => temp_map
                                                          end) rhsl c1map in Some (nmap, cs2 ++ cs2', cs_min, instmap)
                                                  | _ => None
                                                  end
                                      | _ => None
                                      end
                        end
                end
  | Snode v e => let pv_node := (mv, (v, N0)) in 
                match VM.find mv tmap with
                | Some mod_tmap => match VM.find v mod_tmap with
                    | Some (Gtyp gt, _) => match extract_constraint_expr_mod mv e mod_tmap tmap instmap with
                                  | Some (exprs, cs2') => 
                                      let (regular_cs, cs_min') := seperate_min pv_node exprs (nil, nil) in
                                      let nmap := match TVM.find pv_node c1map with
                                        | Some cs1 => TVM.add pv_node (regular_cs ++ cs1) c1map
                                        | _ => TVM.add pv_node regular_cs c1map
                                        end
                                      in Some (nmap, cs2 ++ cs2', cs_min ++ cs_min', instmap)
                                  | _ => None
                                  end
                    | Some (ft, _) => match e with
                            | Eref ref => match ref2pv_mod ref mv instmap tmap, type_of_ref ref mod_tmap with
                                        | Some pvar, Some ft_ref => 
                                          let nmap := extract_constraint_passive ft ft_ref pv_node pvar c1map in 
                                          Some (nmap, cs2, cs_min, instmap)
                                        | _, _ => None
                                        end
                            | Emux c e0 e1 => match extract_mux_mod mv instmap e mod_tmap tmap with
                                        | Some (rhsl, cs2') => 
                                            let nmap := fold_left (fun temp_map ref0 => 
                                                        match ref2pv_mod ref0 mv instmap tmap, type_of_ref ref0 mod_tmap with
                                                        | Some pvar, Some ft_ref => extract_constraint_passive ft ft_ref pv_node pvar temp_map
                                                        | _, _ => temp_map
                                                        end) rhsl c1map in Some (nmap, cs2 ++ cs2', cs_min, instmap)
                                        | _ => None
                                        end
                            | _ => None
                            end
                    | _ => None
                    end
                | _ => None
                end
  | Smem _ _ 
  | Sinvalid _ 
  | Swire _ _ 
  | Sskip => Some (c1map, cs2, cs_min, instmap)
  | Swhen c ss_true ss_false => match extract_constraint_expr_mod mv c mod_tmap tmap instmap with
                | Some (ce0, ce1) => match extract_constraint_ss mv ss_true mod_tmap tmap c1map (cs2 ++ ce0 ++ ce1) cs_min instmap with
                    | Some (c1map', cs2', cs_min', instmap') => extract_constraint_ss mv ss_false mod_tmap tmap c1map' cs2' cs_min' instmap'
                    | _ => None
                    end
                | _ => None
                end
end.

Fixpoint extract_constraint_ml ml (tmap : VM.t (VM.t (ftype * forient))) (c1map : TVM.t (list Constraint1)) (cs2 : list min_rhs) 
  (cs_min : list Constraint_Min) : option (TVM.t (list Constraint1) * list min_rhs * list Constraint_Min) :=
  match ml with
  | nil => Some (c1map, cs2, cs_min)
  | FInmod mv _ ss :: tl => match VM.find mv tmap with
    | Some mod_tmap => match extract_constraint_ss mv ss mod_tmap tmap c1map cs2 cs_min (VM.empty VM.key) with
      | Some (c1map', cs2', cs_min', _) => extract_constraint_ml tl tmap c1map' cs2' cs_min'
      | _ => None
      end
    | _ => None
    end
  | _ :: tl => extract_constraint_ml tl tmap c1map cs2 cs_min
  end.

Definition extract_constraints_c (c : hfcircuit) (tmap : VM.t (VM.t (ftype * forient))) : option (list (TVM.t (list Constraint1)) * list min_rhs) :=
  match c with
  | Fcircuit _ ml => match extract_constraint_ml ml tmap (TVM.empty (list Constraint1)) nil nil with
                    | Some (c1map, cs2, cs_min) => let group_of_mins := map list_Constraint_Min cs_min in
                      let group_of_cs1 := cartesian_product group_of_mins in
                      match group_of_cs1 with
                      | nil => Some ([c1map], cs2) (* 不存在min *)
                      | _ => Some (map (fun new_cs1 => add_cs1_2_c1map new_cs1 c1map) group_of_cs1, cs2)
                      end
                    | _ => None
                    end
  end.

End Extract_Constraints_for_multimod.

Inductive node : Type :=
| Zero
| Node : TripVar.t -> node. 

Module NodeVar <: OrderedType.

  Definition t := node.
  Definition eq (x y : t) : Prop :=
    match x, y with
    | Zero, Zero => true
    | Node p1, Node p2 => TripVar.eq p1 p2
    | _, _ => false
    end.

  Lemma eq_refl (x : t) : eq x x.
  Proof.
    destruct x; simpl.
    - reflexivity.
    - apply TripVar.eq_refl.
  Qed.

  Lemma eq_sym (x y : t) : eq x y -> eq y x.
  Proof.
    destruct x, y; simpl; auto.
    apply TripVar.eq_sym.
  Qed.

  Lemma eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof.
    destruct x, y, z; simpl; auto; try done.
    intros H1 H2.
    eapply TripVar.eq_trans; eauto.
  Qed.

  Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    destruct x, y; simpl; try done.
    - left; reflexivity.
    - right; congruence.
    - right; congruence.
    - destruct (TripVar.eq_dec t0 t1).
      + left; assumption.
      + right; congruence.
  Defined.

  Definition lt (x y : t) : Prop :=
    match x, y with
    | Zero, Node _ => true
    | Node p1, Node p2 => TripVar.lt p1 p2
    | _, _ => false
    end.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    destruct x, y, z; simpl; auto; try done.
    intros Hlt1 Hlt2. eapply TripVar.lt_trans; eauto.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    destruct x, y; simpl; auto.
    apply TripVar.lt_not_eq.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    destruct x, y; simpl.
    - apply EQ. reflexivity.
    - apply LT. reflexivity.
    - apply GT. reflexivity.
    - destruct (TripVar.compare t0 t1).
      + apply LT. assumption.
      + apply EQ. assumption.
      + apply GT. assumption.
  Defined.

  Definition eqn (x y : t) : bool :=
    match x, y with
    | Zero, Zero => true
    | Node p1, Node p2 => TripVar.eqn p1 p2
    | _, _ => false
    end.

  Lemma eqP : Equality.axiom eqn.
  Proof.
    intros x y. unfold eqn, eq.
    destruct x, y; simpl; try solve [constructor; congruence].
    - destruct (TripVar.eqP t0 t1) as [Heq|Hneq].
      + rewrite Heq. constructor; auto.
      + constructor. congruence.
  Qed.

End NodeVar.

Module NVM := VarMap NodeVar.

Section solve_fun. 

Fixpoint extract_cs (ls : list TripVar.t) (cs1 : TVM.t (list Constraint1)) : list Constraint1 := 
  match ls with
  | nil => []
  | hd :: tl => match TVM.find hd cs1 with
      | Some c => c ++ (extract_cs tl cs1)
      | _ => extract_cs tl cs1
      end
  end.

Fixpoint remove_solved (values : TVM.t nat) (terms : list term) : list term * Z.t :=
match terms with
| nil => (nil, 0%Z)
| (coe, var) :: tl => match TVM.find var values, remove_solved values tl with
  | Some val, (terms', cst) => (terms', Z.add cst (Z.of_nat (coe * val)))
  | _, (terms', cst) => ((coe, var) :: terms', cst)
  end
end.

Definition remove_solved_c (values : TVM.t nat) (c : Constraint1) : Constraint1 :=
  let '(new_terms, new_cst) := remove_solved values (rhs_terms1 c) in
  match rhs_power c with
  | nil => 
      {| lhs_var1 := lhs_var1 c;
        rhs_const1 := Z.add (rhs_const1 c) new_cst;
        rhs_power := nil;
        rhs_terms1 := new_terms |}
  | (_, var) :: _ =>
    match TVM.find var values with
    | Some val => 
      {| lhs_var1 := lhs_var1 c;
        rhs_const1 := Z.add (Z.add (rhs_const1 c) new_cst) (Z.pow 2 (Z.of_nat val));
        rhs_power := nil;
        rhs_terms1 := new_terms |}
    | None => 
      {| lhs_var1 := lhs_var1 c;
        rhs_const1 := Z.add (rhs_const1 c) new_cst;
        rhs_power := rhs_power c;
        rhs_terms1 := new_terms |}
    end
  end.

Definition adj_matrix := TVM.t (NVM.t Z.t).

Definition add_edge_of_c (c : Constraint1) (m : adj_matrix) : adj_matrix :=
  match TVM.find (lhs_var1 c) m, (rhs_terms1 c) with 
  | Some dst_map, nil =>
      match NVM.find Zero dst_map with 
      | Some dist =>
          let new_dst_map := NVM.add Zero (Z.max dist (rhs_const1 c)) dst_map in
          TVM.add (lhs_var1 c) new_dst_map m
      | None =>
          let new_dst_map := NVM.add Zero (rhs_const1 c) dst_map in
          TVM.add (lhs_var1 c) new_dst_map m
      end
  | Some dst_map, [(1,v)] =>
      match NVM.find (Node v) dst_map with 
      | Some dist =>
          let new_dst_map := NVM.add (Node v) (Z.max dist (rhs_const1 c)) dst_map in
          TVM.add (lhs_var1 c) new_dst_map m
      | None =>
          let new_dst_map := NVM.add (Node v) (rhs_const1 c) dst_map in
          TVM.add (lhs_var1 c) new_dst_map m
      end
  | _, _ => m 
  end .

Fixpoint add_edge_of_c_s cs m :=
  match cs with
  |nil => m
  | h ::t => add_edge_of_c h (add_edge_of_c_s t m)
  end.
          
Fixpoint add_edge_of_cs (cs : list Constraint1) (m : adj_matrix) : adj_matrix :=
  match cs with
  | nil => m
  | hd :: tl => let new_m := match TVM.find (lhs_var1 hd) m, (rhs_terms1 hd) with 
            | Some dst_map, nil => match NVM.find Zero dst_map with 
                            | Some dist => let new_dst_map := NVM.add Zero (Z.max dist (rhs_const1 hd)) dst_map in
                                    TVM.add (lhs_var1 hd) new_dst_map m
                            | None => let new_dst_map := NVM.add Zero (rhs_const1 hd) dst_map in
                                    TVM.add (lhs_var1 hd) new_dst_map m
                            end
            | Some dst_map, [(1,v)] => match NVM.find (Node v) dst_map with 
                            | Some dist => let new_dst_map := NVM.add (Node v) (Z.max dist (rhs_const1 hd)) dst_map in
                                    TVM.add (lhs_var1 hd) new_dst_map m
                            | None => let new_dst_map := NVM.add (Node v) (rhs_const1 hd) dst_map in
                                    TVM.add (lhs_var1 hd) new_dst_map m
                            end
            | _, _ => m 
            end in add_edge_of_cs tl new_m
  end.

Definition init_dist_map (nodes : list TripVar.t) (cs : list Constraint1) : adj_matrix :=
  let map0 := List.fold_left (fun temp_matrix v => let temp_dst_map := NVM.add (Node v) 0%Z (NVM.empty Z.t) in(* v到v距离为0 *)
                                TVM.add v temp_dst_map temp_matrix) nodes (TVM.empty (NVM.t Z.t)) in
  add_edge_of_cs cs map0.

Definition get_weight (src : TripVar.t) (dst : NodeVar.t) (m : adj_matrix) : option Z.t :=
  match TVM.find src m with
  | Some dst_map => NVM.find dst dst_map
  | None => None
  end.

Definition floyd_update (k i: TripVar.t) (nodes : list NodeVar.t) (m : adj_matrix) : adj_matrix :=
  match TVM.find i m with
  | None => m
  | Some dst_map => let new_dst_map := 
      List.fold_left (fun acc j => 
        match NVM.find j acc, get_weight i (Node k) m, get_weight k j m with
        | Some w, Some w1, Some w2 => let new_w := Z.max w (Z.add w1 w2) in
                              NVM.add j new_w acc
        | _, Some w1, Some w2 => let new_w := Z.add w1 w2 in
                              NVM.add j new_w acc
        | _, _, _ => acc
        end
      ) nodes dst_map in TVM.add i new_dst_map m
  end.

Definition floyd_loop_map (nodes: list TripVar.t) (cs : list Constraint1) : adj_matrix :=
  List.fold_left (fun dist k =>
    List.fold_left (fun dist' i =>
      floyd_update k i (Zero :: map (fun p => Node p) nodes) dist'
    ) nodes dist
    ) nodes (init_dist_map nodes cs).

Fixpoint maxz_list (l : list Z.t) : Z.t :=
  match l with
  | nil => 0%Z
  | t :: tl => Z.max t (maxz_list tl)
  end.

Fixpoint save_longest_dist (simple_cycle : list TripVar.t) (m : adj_matrix) (values : TVM.t nat) : option (TVM.t nat) :=
  match simple_cycle with
  | nil => Some values
  | hd :: tl => match TVM.find hd m with
    | Some dst_map => let (_, dists) := List.split (NVM.elements dst_map) in 
                      let new_values := TVM.add hd (Z.to_nat (maxz_list dists)) values in
                      save_longest_dist tl m new_values
    | None => None
    end
  end.

Definition solve_simple_cycle (simple_cycle : list TripVar.t) (cs : list Constraint1) : option (TVM.t nat) :=
  let m := floyd_loop_map simple_cycle cs in
  if (forallb (fun c => match get_weight c (Node c) m with
                          None => false
                        | Some w => Z.eqb w 0%Z end) simple_cycle)
  then
    save_longest_dist simple_cycle m (TVM.empty nat)
  else None.

Definition relax_power (c : Constraint1) : Constraint1 :=
  let relaxed_terms := map (fun '(coe, var) => (2 * coe, var)) (rhs_power c) in
  let combined_terms := fold_left (fun acc term => combine_term term acc) relaxed_terms (rhs_terms1 c) in
  {| 
      lhs_var1 := lhs_var1 c; 
      rhs_const1 := rhs_const1 c; 
      rhs_terms1 := combined_terms; 
      rhs_power := nil 
  |}.

Definition G := TVM.t (list TripVar.t).
Definition Adj := TVM.t (TVM.t (list Constraint1)).

Definition find_adj_matrix (from to : TripVar.t) (m : Adj) : option (list Constraint1) :=
  match TVM.find from m with
  | Some m' => TVM.find to m'
  | None => None
  end.

Definition add_edge graph adj_matrix (from to : TripVar.t) (c : Constraint1) : G * Adj :=
  let new_graph := match TVM.find from graph with
    | Some children => TVM.add from (to :: children) graph
    | _ => TVM.add from [::to] graph
  end in
  let new_adj := match TVM.find from adj_matrix with
    | Some adj' => match TVM.find to adj' with
                  | Some cs1 => TVM.add from (TVM.add to (c :: cs1) adj') adj_matrix
                  | None => TVM.add from (TVM.add to [::c] adj') adj_matrix
                  end
    | _ => TVM.add from (TVM.add to [::c] (TVM.empty (list Constraint1))) adj_matrix
  end in (new_graph, new_adj).

Fixpoint build_graph (constraints : list Constraint1) : G * Adj :=
  match constraints with
  | [] => (TVM.empty (list TripVar.t), TVM.empty (TVM.t (list Constraint1)))
  | c0 :: cs =>
      fold_left (fun '(graph, adj_matrix) (xi : TripVar.t) =>
                   add_edge graph adj_matrix xi (lhs_var1 c0) c0)
                (List.split (rhs_terms1 c0)).2 (build_graph cs)
  end. 

Fixpoint find_path (g : G) (y : TripVar.t) n (v : list TripVar.t) (x : TripVar.t) res : option (list TripVar.t) :=
  match res with
  | Some p => res
  | None =>
  if x == y then Some (y :: v) else
  if n is n'.+1 then match TVM.find x g with
    | Some children =>
    foldl (fun r child => match r with
      | Some p => r
      | None => find_path g y n' (x :: v) child None
      end) res children
    | None => None
    end else None
  end.

Fixpoint find_constraints_of_path (adj : Adj) (p_hd : TripVar.t) (p_tl : list TripVar.t) : option (list Constraint1) :=
  match p_tl with
  | [] => Some nil
  | hd :: tl => match find_adj_matrix hd p_hd adj, find_constraints_of_path adj hd tl with
              | Some (c :: _), Some cs => Some (c :: cs)
              | _, _ => None
              end
  end.

Definition substitute_constraint (c : Constraint1) (v : TripVar.t) (terms : list (nat * TripVar.t)) (cst : Z.t) : Constraint1 :=
  match List.find (fun p : term => snd p == v) (rhs_terms1 c) with
  | Some (coe, _) =>
    let new_terms := 
        fold_right (fun '(coe', var) (acc : list term) =>
            match List.find (fun p : term => snd p == var) acc with
            | None => (coe * coe', var) :: acc 
            | Some (existing_coef, _) =>
                (existing_coef + coe * coe', var) :: (List.remove term_dec (existing_coef, var) acc)
            end
        ) (List.remove term_dec (coe, v) (rhs_terms1 c)) terms in
      {| lhs_var1 := lhs_var1 c;
        rhs_const1 := Z.add (rhs_const1 c) ((Z.of_nat coe) * cst);
        rhs_power := nil;
        rhs_terms1 := new_terms |}
  | None => c
  end.

Definition substitute_c (c1 c2 : Constraint1) : Constraint1 :=
  substitute_constraint c1 (lhs_var1 c2) (rhs_terms1 c2) (rhs_const1 c2).

Fixpoint substitute_cs (cs : list Constraint1) : option Constraint1 :=
  match cs with
  | [] => None
  | hd :: tl => match substitute_cs tl with
                | Some c => Some (substitute_c hd c)
                | None => Some hd
                end
  end.

Definition compute_ub (c : Constraint1) : option nat :=
  match List.find (fun (p : term) => snd p == (lhs_var1 c)) (rhs_terms1 c) with
  | None => None
  | Some (coe, _) => if coe > 1 then Some (Z.to_nat (Z.div (Z.abs (rhs_const1 c)) (Z.of_nat (coe - 1)))) else None
  end.

Definition solve_ub_case1 (x : TripVar.t) (c : Constraint1) (var : TripVar.t) (g : G) (adj : Adj) (n : nat) : option nat :=
  match find_path g x n nil (lhs_var1 c) None, find_path g var n nil x None with
  | Some (p0_hd :: p0_tl), Some (p1_hd :: p1_tl) => 
          match find_constraints_of_path adj p0_hd p0_tl, find_constraints_of_path adj p1_hd p1_tl with
          | Some cs0, Some cs1 => let new_c := match substitute_cs cs0, substitute_cs cs1 with
                                | Some c0, Some c1 => substitute_c c0 (substitute_c c c1)
                                | None, Some c1 => substitute_c c c1
                                | Some c0, None => substitute_c c0 c
                                | None, None => c end in
                                  compute_ub new_c 
          | _, _ => None
          end
  | _, _ => None
  end.

Fixpoint solve_ubs_case1 (tbsolved : list TripVar.t) (c : Constraint1) (var : TripVar.t) (g : G) (adj : Adj) (n : nat) (v : TVM.t nat) : option (TVM.t nat) :=
  match tbsolved with
  | [] => Some v
  | hd :: tl => match solve_ub_case1 hd c var g adj n with
              | Some ub => solve_ubs_case1 tl c var g adj n (TVM.add hd ub v)
              | _ => None
              end
  end.

Definition solve_ub_case2 (x : TripVar.t) (c : Constraint1) (var0 var1 : TripVar.t) (g : G) (adj : Adj) (n : nat) : option nat :=
  match find_path g x n nil (lhs_var1 c) None, find_path g var0 n nil x None, find_path g var1 n nil x None with
  | Some (p0_hd :: p0_tl), Some (p1_hd :: p1_tl), Some (p2_hd :: p2_tl) => 
        match find_constraints_of_path adj p0_hd p0_tl, find_constraints_of_path adj p1_hd p1_tl, find_constraints_of_path adj p2_hd p2_tl with
        | Some cs0, Some cs1, Some cs2 => let new_c := match substitute_cs cs0, substitute_cs cs1, substitute_cs cs2 with
                                | Some c0, Some c1, Some c2 => substitute_c c0 (substitute_c (substitute_c c c1) c2)
                                | None, Some c1, Some c2 => substitute_c (substitute_c c c1) c2
                                | Some c0, None, Some c2 => substitute_c c0 (substitute_c c c2)
                                | None, None, Some c2 => substitute_c c c2
                                | Some c0, Some c1, None => substitute_c c0 (substitute_c c c1)
                                | None, Some c1, None => substitute_c c c1
                                | Some c0, None, None => substitute_c c0 c
                                | None, None, None => c end in
                                  compute_ub new_c 
        | _, _, _ => None
        end
| _, _, _ => None
end.

Fixpoint solve_ubs_case2 (tbsolved : list TripVar.t) (c : Constraint1) (var0 var1 : TripVar.t) (g : G) (adj : Adj) (n : nat) (v : TVM.t nat) : option (TVM.t nat) :=
  match tbsolved with
  | [] => Some v
  | hd :: tl => match solve_ub_case2 hd c var0 var1 g adj n with
              | Some ub => solve_ubs_case2 tl c var0 var1 g adj n (TVM.add hd ub v)
              | _ => None
              end
  end.

Definition solve_ubs_aux (tbsolved : list TripVar.t) (cs1 : list Constraint1) : option (TVM.t nat) :=
  let (g, adj) := build_graph cs1 in
  let n := List.length tbsolved in
  match List.find (fun c => List.existsb (fun t => t.1 > 1) (rhs_terms1 c)) cs1 with
  | Some c => (* lhs >= coe * var + ... + cst c *) 
              match List.find (fun t => t.1 > 1) (rhs_terms1 c) with
              | Some (_, var) => solve_ubs_case1 tbsolved c var g adj n (TVM.empty nat)
              | _ => None
              end
  | None => match List.find (fun c => List.length (rhs_terms1 c) > 1) cs1 with
            | Some c => (* lhs >= coe0 * var0 + coe1 * var1 + ... + cst c *)
                        match rhs_terms1 c with
                        | (_, var0) :: (_, var1) :: _ => solve_ubs_case2 tbsolved c var0 var1 g adj n (TVM.empty nat)
                        | _ => None
                        end
            | None => None
            end
  end.

Fixpoint add_bs (ls : list (TripVar.t * nat)) (bs : TVM.t (nat * nat)) : TVM.t (nat * nat) :=
  match ls with
  | nil => bs
  | (hd, ub) :: tl => add_bs tl (TVM.add hd (0, ub) bs)
  end.

Definition mergeBounds (v2 : TVM.t nat) : TVM.t (nat * nat) :=
  let eles := TVM.elements v2 in
  add_bs eles (TVM.empty (nat * nat)).

Definition key_value (s : TVM.t (nat * nat)) : TVM.t nat :=
  TVM.map (fun '(lb,ub) => (lb + ub)/2) s.

Definition product_bounds (bounds : TVM.t (nat * nat)) : nat :=
  let eles := TVM.elements bounds in
  fold_left (fun acc '(v, bs) =>
               let '(lb, ub) := bs in
               acc + (ub - lb))
            eles 0.

Definition halve (bds : TVM.t (nat * nat)) : TVM.t (nat * nat) :=
  TVM.map (fun '(lb,ub) => (lb, (lb + ub)/2)) bds.

Definition prioritize_fst (v v' : option (TVM.t nat)) : option (TVM.t nat) :=
  match v with
  | None => v'
  | Some s => Some s
  end.

Definition update_ub (s : TVM.t (nat * nat)) (x : TripVar.t) (v : nat) :=
  match TVM.find x s with
  | Some (lb, _) => TVM.add x (lb, v) s 
  | _ => s 
  end.

Definition update_lb (s : TVM.t (nat * nat)) (x : TripVar.t) (v : nat) :=
  match TVM.find x s with
  | Some (_, ub) => TVM.add x (v, ub) s 
  | _ => s 
  end.

Definition length (x : TripVar.t) (bds : TVM.t (nat * nat)) : nat :=
  match TVM.find x bds with
  | Some (lb, ub) => (ub - lb) 
  | None => 0
  end.


(* =================== termination proofs =================== *)

Lemma product_bounds_helper : forall (l1 : list (ProdVar.t * (nat * nat))) init0 init1, init0 < init1 -> fold_left
  (fun (acc : nat) '(_, bs) => let '(lb0, ub0) := bs in (acc + (ub0 - lb0))) l1
  init0 <
  fold_left
  (fun (acc : nat) '(_, bs) => let '(lb0, ub0) := bs in (acc + (ub0 - lb0))) l1
  init1.
Proof.
  elim. simpl; intros; done.
  simpl; intros. apply H. destruct a as [v [lb0 ub0]]. rewrite (ltn_add2r _ init0 init1) //.
Qed.

Axiom elements_add : forall [A : Type] bounds, forall v (a b : A), TVM.find v bounds = Some a -> 
  exists l0 l1, l0 ++ (v, a) :: l1 = TVM.elements bounds /\ l0 ++ (v, b) :: l1 = TVM.elements (TVM.add v b bounds).

Lemma bab_bin_g1 :
  seq TripVar.t ->
  forall (bounds : TVM.t (nat * nat)) (cs1 : seq Constraint1),
  seq Constraint2 ->
  forall c1 : Constraint1,
  List.find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = Some c1 ->
  (product_bounds bounds == 0) = false ->
  forall v : TripVar.t,
  List.find (fun x : TripVar.t => length x bounds != 0) (rhs_vars c1) = Some v ->
  forall (p : nat * nat) (lb ub : nat),
  p = (lb, ub) ->
  TVM.find (elt:=nat * nat) v bounds = Some (lb, ub) ->
  (product_bounds (update_lb bounds v ((lb + ub) / 2).+1) < product_bounds bounds)%coq_nat.
Proof.
Admitted.

Lemma bab_bin_g2 :
  seq TripVar.t ->
  forall (bounds : TVM.t (nat * nat)) (cs1 : seq Constraint1),
  seq Constraint2 ->
  forall c1 : Constraint1,
  List.find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = Some c1 ->
  (product_bounds bounds == 0) = false ->
  forall v : TripVar.t,
  List.find (fun x : TripVar.t => length x bounds != 0) (rhs_vars c1) = Some v ->
  forall (p : nat * nat) (lb ub : nat),
  p = (lb, ub) ->
  TVM.find (elt:=nat * nat) v bounds = Some (lb, ub) ->
  (product_bounds (update_ub bounds v ((lb + ub) / 2)) < product_bounds bounds)%coq_nat.
Proof.
Admitted.

Lemma bab_bin_g3 :
  seq TripVar.t ->
  forall (bounds : TVM.t (nat * nat)) (cs1 : seq Constraint1),
  seq Constraint2 ->
  forall c1 : Constraint1,
  List.find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = Some c1 ->
  (product_bounds bounds == 0) = false ->
  List.find (fun x : TripVar.t => length x bounds != 0) (rhs_vars c1) = None ->
  (length (lhs_var1 c1) bounds == 0) = false ->
  forall (p : nat * nat) (lb ub : nat),
  p = (lb, ub) ->
  TVM.find (elt:=nat * nat) (lhs_var1 c1) bounds = Some (lb, ub) ->
  (product_bounds (update_ub bounds (lhs_var1 c1) ((lb + ub) / 2)) < product_bounds bounds)%coq_nat.
Proof.
Admitted.

Lemma bab_bin_g4 :
  seq TripVar.t ->
  forall (bounds : TVM.t (nat * nat)) (cs1 : seq Constraint1),
  seq Constraint2 ->
  forall c1 : Constraint1,
  List.find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = Some c1 ->
  (product_bounds bounds == 0) = false ->
  List.find (fun x : TripVar.t => length x bounds != 0) (rhs_vars c1) = None ->
  (length (lhs_var1 c1) bounds == 0) = false ->
  forall (p : nat * nat) (lb ub : nat),
  p = (lb, ub) ->
  TVM.find (elt:=nat * nat) (lhs_var1 c1) bounds = Some (lb, ub) ->
  (product_bounds (update_lb bounds (lhs_var1 c1) ((lb + ub) / 2).+1) < product_bounds bounds)%coq_nat.
Proof.
Admitted.
  
Lemma bab_bin_g5 :
  seq TripVar.t ->
  forall (bounds : TVM.t (nat * nat)) (cs1 : seq Constraint1) (cs2 : seq Constraint2),
  List.find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = None ->
  forall c2 : Constraint2,
  List.find (fun c : Constraint2 => ~~ satisfies_constraint2 (key_value bounds) c) cs2 = Some c2 ->
  (product_bounds bounds == 0) = false ->
  forall v : TripVar.t,
  List.find (fun x : TripVar.t => length x bounds != 0) [seq i.2 | i <- rhs_terms2 c2] = Some v ->
  forall (p : nat * nat) (lb ub : nat),
  p = (lb, ub) ->
  TVM.find (elt:=nat * nat) v bounds = Some (lb, ub) ->
  (product_bounds (update_lb bounds v ((lb + ub) / 2).+1) < product_bounds bounds)%coq_nat.
Proof.
Admitted.

Lemma bab_bin_g6 :
  seq TripVar.t ->
  forall (bounds : TVM.t (nat * nat)) (cs1 : seq Constraint1) (cs2 : seq Constraint2),
  List.find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = None ->
  forall c2 : Constraint2,
  List.find (fun c : Constraint2 => ~~ satisfies_constraint2 (key_value bounds) c) cs2 = Some c2 ->
  (product_bounds bounds == 0) = false ->
  forall v : TripVar.t,
  List.find (fun x : TripVar.t => length x bounds != 0) [seq i.2 | i <- rhs_terms2 c2] = Some v ->
  forall (p : nat * nat) (lb ub : nat),
  p = (lb, ub) ->
  TVM.find (elt:=nat * nat) v bounds = Some (lb, ub) ->
  (product_bounds (update_ub bounds v ((lb + ub) / 2)) < product_bounds bounds)%coq_nat.
Proof.
Admitted.

Lemma bab_bin_g7 :
  seq TripVar.t ->
  forall (bounds : TVM.t (nat * nat)) (cs1 : seq Constraint1) (cs2 : seq Constraint2),
  List.find (fun c : Constraint1 => ~~ satisfies_constraint1 (key_value bounds) c) cs1 = None ->
  List.find (fun c : Constraint2 => ~~ satisfies_constraint2 (key_value bounds) c) cs2 = None ->
  (product_bounds bounds == 0) = false -> (product_bounds (halve bounds) < product_bounds bounds)%coq_nat.
Proof.
Admitted.

Function bab_bin (scc : list TripVar.t) (bounds : TVM.t (nat * nat))
                 (cs1 : list Constraint1) (cs2 : list Constraint2)
  { measure product_bounds bounds } : option (TVM.t nat) :=
  let current_node := key_value bounds in 
  let unsat1 := List.find (fun c => negb (satisfies_constraint1 current_node c)) cs1 in
  let unsat2 := List.find (fun c => negb (satisfies_constraint2 current_node c)) cs2 in
  match unsat1, unsat2 with
  | None, None => 
      if (product_bounds bounds == 0) 
      then (Some current_node)
      else 
        bab_bin scc (halve bounds) cs1 cs2
  | Some c1, _ => 
      if (product_bounds bounds == 0) 
      then None 
      else 
        match List.find (fun x => length x bounds != 0) (rhs_vars c1) with
        (* pick a splittable var in rhs *)
        | Some v =>
            match TVM.find v bounds with
            | Some (lb, ub) =>
                prioritize_fst
                  (* find a best solution in the lower half *)
                  (bab_bin scc (update_ub bounds v ((lb+ub)/2)) cs1 cs2)
                  (* no solution in lower half, then search the upper half *)
                  (bab_bin scc (update_lb bounds v ((lb+ub)/2).+1) cs1 cs2)
            | None => None (* IMPOSSIBLE *)
            end
        | None => (* should ONLY search the upper half of the lhs variable, since the lower half must contain no solution *)
            if length c1.(lhs_var1) bounds == 0 then None
            else
              match TVM.find c1.(lhs_var1) bounds with
              | Some (lb, ub) =>
                  (* bab_bin scc (update_lb bounds (c1.(lhs_var1)) ((lb+ub)/2).+1) cs1 cs2 *)
                  (* to ease the proof: *)
                  prioritize_fst
                    (bab_bin scc (update_lb bounds (c1.(lhs_var1)) ((lb+ub)/2).+1) cs1 cs2)
                    (bab_bin scc (update_ub bounds (c1.(lhs_var1)) ((lb+ub)/2)) cs1 cs2)
              | None => None (* IMPOSSIBLE *)
              end
        end
  | None, Some c2 => 
      if (product_bounds bounds == 0) 
      then None 
      else 
        match List.find (fun x => length x bounds != 0) (map snd (rhs_terms2 c2)) with
        (* pick a splittable var in rhs *)
        | Some v =>
            match TVM.find v bounds with
            | Some (lb, ub) =>
                (* match bab_bin scc (update_ub bounds v val) cs1 cs2 with *)
                (* (* find a best solution in the lower half *) *)
                (* | Some sol => Some sol *)
                (* (* no solution in the lower half, then search the upper half *) *)
                (* | None => bab_bin scc (update_lb bounds v val.+1) cs1 cs2 *)
                (* end *)
                prioritize_fst
                  (* find a best solution in the lower half *)
                  (bab_bin scc (update_ub bounds v ((lb+ub)/2)) cs1 cs2)
                  (* no solution in lower half, then search the upper half *)
                  (bab_bin scc (update_lb bounds v ((lb+ub)/2).+1) cs1 cs2)
            | None => None (* IMPOSSIBLE *)
            end
        | None => None (* no solution *)
        end
  end.
Proof.
  - exact: bab_bin_g1.
  - exact: bab_bin_g2.
  - exact: bab_bin_g3.
  - exact: bab_bin_g4.
  - exact: bab_bin_g5.
  - exact: bab_bin_g6.
  - exact: bab_bin_g7.
Defined.

Definition is_simple_cycle (cs : list Constraint1) : bool :=
  forallb (fun c => match rhs_terms1 c, rhs_power c with
                  | nil, nil
                  | [::(1,_)], nil => true
                  | _, _ => false
                  end) cs.

Definition solve_scc (hd : list TripVar.t) (constraints : list Constraint1) : option (TVM.t nat) := 
match hd with
| [:: v] => let (cs, cs_have_v) := List.partition (fun c => ((rhs_terms1 c) == nil) && ((rhs_power c) == nil)) constraints in
            let nval := max_nl (List.map (fun c => rhs_const1 c) cs) 0 in
            let nv := TVM.add v nval (TVM.empty nat) in
            if forallb (fun c => satisfies_constraint1 nv c) cs_have_v then
                Some nv else None
| _ => if is_simple_cycle constraints then solve_simple_cycle hd constraints 
    else let remove_power := List.map (fun c => relax_power c) constraints in
         let remove_only_const := List.filter (fun c => List.length (rhs_terms1 c) != 0) remove_power in
        match solve_ubs_aux hd remove_only_const with
        | Some ubs => let bs := mergeBounds ubs in bab_bin hd bs constraints []
        | _ => None
        end 
end.

Fixpoint merge_solution (tbsolved : list TripVar.t) (initial solution_of_tbsolved : TVM.t nat) : option (TVM.t nat) := 
match tbsolved with
| nil => Some initial
| hd :: tl => match TVM.find hd solution_of_tbsolved with
  | Some val => merge_solution tl (TVM.add hd val initial) solution_of_tbsolved
  | _ => None
  end
end.

Fixpoint solve_alg (res : list (list TripVar.t)) (values : TVM.t nat) (cs1 : TVM.t (list Constraint1)) : option (TVM.t nat) :=
match res with
| nil => Some values
| hd :: tl => 
    let tbsolved_cs := extract_cs hd cs1 in 
    let tbsolved_cs' := List.map (remove_solved_c values) tbsolved_cs in
    match solve_scc hd tbsolved_cs' with
    | Some nv => match merge_solution hd values nv with
        | Some new_values => solve_alg tl new_values cs1 
        | _ => None
        end
    | None => None
    end
end.

Definition solve_alg_check (res : list (list TripVar.t)) (cs1 : TVM.t (list Constraint1)) (cs2 : list min_rhs) : option (TVM.t nat) :=
  match solve_alg res (TVM.empty nat) cs1 with
  | Some value => if (forallb (fun c => Z.leb (min_rhs_value value c) 1%Z) cs2) then Some value else None
  | _ => None
  end.

Definition smaller_valuation (v1 v2 : TVM.t nat) : TVM.t nat :=
  TVM.map2 (fun v v' => match v, v' with
                        | Some n , Some n' => Some (minn n n')
                        | _, _ => None
                        end) v1 v2.

End solve_fun. 

Section update_cir.

Fixpoint update_tmap (tmap : VM.t (VM.t (ftype * forient))) (new_widths : list (TripVar.t * nat)) : option (VM.t (VM.t (ftype * forient))) :=
  match new_widths with
  | nil => Some tmap
  | (pv, w) :: tl => match VM.find pv.1 tmap with (* 找到对应moule的tmap *)
                    | Some mod_tmap => 
                        match VM.find pv.2.1 mod_tmap with
                        | Some (ft, ori) => match update_ftype pv.2.2 w ft with 
                                | Some nft => update_tmap (VM.add pv.1 (VM.add pv.2.1 (nft, ori) mod_tmap) tmap) tl
                                | _ => None
                                end
                        | _ => None
                        end
                    | _ => None
                    end
  end.

Definition InferWidths_trans_m m (tmap : VM.t (VM.t (ftype * forient))) : option hfmodule :=
  match m with
  | FInmod mv ps ss => match VM.find mv tmap with
          | Some mod_tmap => match InferWidths_transps ps mod_tmap, InferWidths_transss ss mod_tmap with
                  | Some nps, Some nss => Some (FInmod mv nps nss)
                  | _, _ => None
                  end
          | _ => None
          end
  | FExmod _ _ _ => Some m 
  end.

Fixpoint InferWidths_trans_ml ml (tmap : VM.t (VM.t (ftype * forient))) : option (seq hfmodule) :=
  match ml with
  | nil => Some nil
  | hd :: tl => match InferWidths_trans_m hd tmap, InferWidths_trans_ml tl tmap with
      | Some nhd, Some ntl => Some (nhd :: ntl)
      | _, _ => None
      end
  end.

Definition InferWidths_trans_c c (tmap : VM.t (VM.t (ftype * forient))) : option hfcircuit :=
  match c with
  | Fcircuit c ml => match InferWidths_trans_ml ml tmap with
      | Some nml => Some (Fcircuit c nml)
      | _ => None
      end
  end.

End update_cir.