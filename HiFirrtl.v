From Coq Require Import FMaps ZArith FunInd FMapAVL OrderedType.
From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
From Solver Require Import Env LoFirrtl HiEnv.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section HiFirrtl.

  (****** Syntax ******)

  (****** Expressions ******)

  Inductive sign := Unsigned | Signed.

  Inductive hfexpr : Type :=
  | Econst : fgtyp -> bitseq -> hfexpr
  | Ecast : ucast -> hfexpr -> hfexpr
  | Eprim_unop : eunop -> hfexpr -> hfexpr
  | Eprim_binop : ebinop -> hfexpr -> hfexpr -> hfexpr
  | Emux : hfexpr -> hfexpr -> hfexpr -> hfexpr
  (*| Evalidif : hfexpr -> hfexpr -> hfexpr  This is no longer part of the HiFIRRTL standard, but we leave it because removing it would break some proofs;
                                             changing the proofs would be simple but it is not important. *)
  | Eref : href -> hfexpr
  with href : Type :=
  | Eid : var -> href
  | Esubfield : href -> var -> href (* HiFirrtl *)
  | Esubindex : href -> nat -> href (* HiFirrtl *)
  | Esubaccess : href -> hfexpr -> href (* HiFirrtl *)
  .

  (** equality of hfexpr and href are decidable *)
  
  Fixpoint hfexpr_eqn (x y : hfexpr) : bool :=
  match x, y with
  | Econst tx bx, Econst ty by_ => (tx == ty) && (bx == by_)
  | Ecast ux ex, Ecast uy ey => (ux == uy) && hfexpr_eqn ex ey
  | Eprim_unop ux ex, Eprim_unop uy ey => (ux == uy) && hfexpr_eqn ex ey
  | Eprim_binop bx ex fx, Eprim_binop by_ ey fy => (bx == by_) && hfexpr_eqn ex ey && hfexpr_eqn fx fy
  | Emux ex fx gx, Emux ey fy gy => hfexpr_eqn ex ey && hfexpr_eqn fx fy && hfexpr_eqn gx gy
  (*| Evalidif ex fx, Evalidif ey fy => hfexpr_eqn ex ey && hfexpr_eqn fx fy*)
  | Eref rx, Eref ry => href_eqn rx ry
  | _, _ => false
  end
  with href_eqn (x y : href) : bool :=
  match x, y with
  | Eid vx, Eid vy => vx == vy
  | Esubfield rx vx, Esubfield ry vy => href_eqn rx ry && (vx == vy)
  | Esubindex rx nx, Esubindex ry ny => href_eqn rx ry && (nx == ny)
  | Esubaccess rx ex, Esubaccess ry ey => href_eqn rx ry && hfexpr_eqn ex ey
  | _, _ => false
  end.

Lemma hfexpr_eqP : (*Equality.axiom hfexpr_eqn*)
forall x y : hfexpr, reflect (x = y) (hfexpr_eqn x y)
with href_eqP : (*Equality.axiom href_eqn*)
forall x y : href, reflect (x = y) (href_eqn x y).
Proof. 
  * clear hfexpr_eqP.
    induction x, y ; simpl ;
          try (apply ReflectF ; discriminate).
    + destruct (f == f0) eqn: Hf ; move /eqP : Hf => Hf ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hf andTb.
      destruct (b == b0) eqn: Hb ; move /eqP : Hb => Hb ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hb.
      apply ReflectT ; reflexivity.
    + destruct (u == u0) eqn: Hu ; move /eqP : Hu => Hu ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hu andTb.
      specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (hfexpr_eqn x y) ;
            last by (apply ReflectF ; injection ; intro ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      apply ReflectT ; reflexivity.
    + destruct (e == e0) eqn: He ; move /eqP : He => He ;
            last by (apply ReflectF ; injection ; done).
      rewrite He andTb.
      specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (hfexpr_eqn x y) ;
            last by (apply ReflectF ; injection ; intro ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      apply ReflectT ; reflexivity.
    + destruct (e == e0) eqn: He ; move /eqP : He => He ;
            last by (apply ReflectF ; injection ; done).
      rewrite He andTb.
      specialize (IHx1 y1) ; apply reflect_iff in IHx1.
      destruct (hfexpr_eqn x1 y1) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     destruct IHx1 as [IHx1 _] ; apply IHx1 in H0 ; done).
      destruct IHx1 as [_ IHx1] ; rewrite IHx1 //.
      specialize (IHx2 y2) ; apply reflect_iff in IHx2.
      destruct (hfexpr_eqn x2 y2) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHx2 as [IHx2 _] ; apply IHx2 in H0 ; done).
      destruct IHx2 as [_ IHx2] ; rewrite IHx2 //.
      apply ReflectT ; reflexivity.
    + specialize (IHx1 y1) ; apply reflect_iff in IHx1.
      destruct (hfexpr_eqn x1 y1) ;
            last by (apply ReflectF ; injection ; intros _ _ H0 ;
                     destruct IHx1 as [IHx1 _] ; apply IHx1 in H0 ; done).
      destruct IHx1 as [_ IHx1] ; rewrite IHx1 //.
      specialize (IHx2 y2) ; apply reflect_iff in IHx2.
      destruct (hfexpr_eqn x2 y2) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     destruct IHx2 as [IHx2 _] ; apply IHx2 in H0 ; done).
      destruct IHx2 as [_ IHx2] ; rewrite IHx2 //.
      specialize (IHx3 y3) ; apply reflect_iff in IHx3.
      destruct (hfexpr_eqn x3 y3) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHx3 as [IHx3 _] ; apply IHx3 in H0 ; done).
      destruct IHx3 as [_ IHx3] ; rewrite IHx3 //.
      apply ReflectT ; reflexivity.
    (*+ specialize (IHx1 y1) ; apply reflect_iff in IHx1.
      destruct (hfexpr_eqn x1 y1) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     destruct IHx1 as [IHx1 _] ; apply IHx1 in H0 ; done).
      destruct IHx1 as [_ IHx1] ; rewrite IHx1 //.
      specialize (IHx2 y2) ; apply reflect_iff in IHx2.
      destruct (hfexpr_eqn x2 y2) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHx2 as [IHx2 _] ; apply IHx2 in H0 ; done).
      destruct IHx2 as [_ IHx2] ; rewrite IHx2 //.
      apply ReflectT ; reflexivity.*)
    + specialize (href_eqP h h0) ; apply reflect_iff in href_eqP.
      destruct (href_eqn h h0) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct href_eqP as [href_eqP _] ; apply href_eqP in H0 ; done).
      destruct href_eqP as [_ href_eqP] ; rewrite href_eqP //.
      apply ReflectT ; reflexivity.
  * clear href_eqP.
    induction x, y ; simpl ;
          try (apply ReflectF ; discriminate).
    + destruct (v == v0) eqn: Hs ; move /eqP : Hs => Hs ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hs.
      apply ReflectT ; reflexivity.
    + specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (href_eqn x y) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      destruct (v == v0) eqn: Hv ; move /eqP : Hv => Hv ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hv.
      apply ReflectT ; reflexivity.
    + specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (href_eqn x y) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      destruct (n == n0) eqn: Hn ; move /eqP : Hn => Hn ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hn.
      apply ReflectT ; reflexivity.
    + specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (href_eqn x y) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      specialize (hfexpr_eqP h h0) ; apply reflect_iff in hfexpr_eqP.
      destruct (hfexpr_eqn h h0) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct hfexpr_eqP as [hfexpr_eqP _] ; apply hfexpr_eqP in H0 ; done).
      destruct hfexpr_eqP as [_ hfexpr_eqP] ; rewrite hfexpr_eqP //.
      apply ReflectT ; reflexivity.
Qed.

Lemma hfexpr_eqP' : Equality.axiom hfexpr_eqn.
Proof. 
  rewrite /Equality.axiom.
  apply hfexpr_eqP.
Qed.
Lemma href_eqP' : Equality.axiom href_eqn.
Proof.
  rewrite /Equality.axiom.
  apply href_eqP.
Qed.

HB.instance Definition _ := hasDecEq.Build hfexpr hfexpr_eqP'.
HB.instance Definition _ := hasDecEq.Build href href_eqP'.

(****** Statements ******)

Record mem_port : Type :=
    mk_mem_port
      {
        id : var;
        addr : var;
        en : var;
        clk : var;
        mask : var
      }.

Parameter mem_port_eqn : forall (x y : mem_port), bool.
Axiom mem_port_eqP : Equality.axiom mem_port_eqn.

HB.instance Definition _ := hasDecEq.Build mem_port mem_port_eqP.

Record hfmem : Type :=
  mk_fmem
    {
      data_type : ftype;
      depth : nat;
      reader : seq mem_port;
      writer : seq mem_port;
      read_latency : nat;
      write_latency : nat;
      read_write : ruw
    }.

Definition hfmem_eqn (x y : hfmem) : bool :=
  (data_type x == data_type y) && (depth x == depth y) &&
  (reader x == reader y) && (writer x == writer y) &&
  (read_latency x == read_latency y) && (write_latency x == write_latency y) &&
  (read_write x == read_write y).

Lemma hfmem_eqP : Equality.axiom hfmem_eqn.
  Proof.
  unfold Equality.axiom, hfmem_eqn.
  destruct x, y ; simpl.
  destruct (data_type0 == data_type1) eqn: Hdt ; move /eqP : Hdt => Hdt ;
        last by (apply ReflectF ; contradict Hdt ; injection Hdt ; done).
  rewrite Hdt andTb.
  destruct (depth0 == depth1) eqn: Hdp ; move /eqP : Hdp => Hdp ;
        last by (apply ReflectF ; contradict Hdp ; injection Hdp ; done).
  rewrite Hdp andTb.
  destruct (reader0 == reader1) eqn: Hrd ; move /eqP : Hrd => Hrd ;
        last by (apply ReflectF ; contradict Hrd ; injection Hrd ; done).
  rewrite Hrd andTb.
  destruct (writer0 == writer1) eqn: Hwr ; move /eqP : Hwr => Hwr ;
        last by (apply ReflectF ; contradict Hwr ; injection Hwr ; done).
  rewrite Hwr andTb.
  destruct (read_latency0 == read_latency1) eqn: Hrl ; move /eqP : Hrl => Hrl ;
        last by (apply ReflectF ; contradict Hrl ; injection Hrl ; done).
  rewrite Hrl andTb.
  destruct (write_latency0 == write_latency1) eqn: Hwl ; move /eqP : Hwl => Hwl ;
        last by (apply ReflectF ; contradict Hwl ; injection Hwl ; done).
  rewrite Hwl andTb.
  destruct (read_write0 == read_write1) eqn: Hrw ; move /eqP : Hrw => Hrw ;
        last by (apply ReflectF ; contradict Hrw ; injection Hrw ; done).
  rewrite Hrw.
  apply ReflectT ; reflexivity.
  Qed.

HB.instance Definition _ := hasDecEq.Build hfmem hfmem_eqP.

  Inductive rst : Type :=
  | NRst : rst
  | Rst : hfexpr (* reset trigger signal *) -> hfexpr (* reset value *) -> rst.

  Definition rst_eqn (x y : rst) : bool :=
  match x, y with
  | NRst, NRst => true
  | Rst t1 r1, Rst t2 r2 => (t1 == t2) && (r1 == r2)
  | _, _ => false
  end.

  Lemma rst_eqP : Equality.axiom rst_eqn.
  Proof.
  unfold Equality.axiom, rst_eqn ; intros.
  destruct x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
  destruct (h == h1) eqn: H1 ; move /eqP : H1 => H1.
  * rewrite andTb ; destruct (h0 == h2) eqn: H2 ; move /eqP : H2 => H2.
    + apply ReflectT ; rewrite H1 H2 ; reflexivity.
    + apply ReflectF ; contradict H2 ; injection H2 ; done.
  * rewrite andFb ; apply ReflectF.
    contradict H1 ; injection H1 ; done.
  Qed.

HB.instance Definition _ := hasDecEq.Build rst rst_eqP.

  Record hfreg : Type :=
    mk_freg
      {
        (* rid : var; *)
        type : ftype;
        clock : hfexpr;
        reset : rst
      }.

  Definition hfreg_eqn (x y : hfreg) : bool :=
  (type x == type y) && (clock x == clock y) && (reset x == reset y).
  
  Lemma hfreg_eqP : Equality.axiom hfreg_eqn.
  Proof.
  unfold Equality.axiom, hfreg_eqn.
  destruct x, y ; simpl.
  destruct (type0 == type1) eqn: Ht ; move /eqP : Ht => Ht ;
        last by (apply ReflectF ; contradict Ht ; injection Ht ; done).
  rewrite Ht andTb.
  destruct (clock0 == clock1) eqn: Hc ; move /eqP : Hc => Hc ;
        last by (apply ReflectF ; contradict Hc ; injection Hc ; done).
  rewrite Hc andTb.
  destruct (reset0 == reset1) eqn: Hr ; move /eqP : Hr => Hr ;
        last by (apply ReflectF ; contradict Hr ; injection Hr ; done).
  rewrite Hr.
  apply ReflectT ; reflexivity.
  Qed.

HB.instance Definition _ := hasDecEq.Build hfreg hfreg_eqP.

  Definition inst_ports : Type := seq var.

  Inductive hfstmt : Type :=
  | Sskip
  | Swire : var -> ftype -> hfstmt
  | Sreg : var -> hfreg -> hfstmt
  | Smem : var -> hfmem -> hfstmt
  | Sinst : var -> var -> hfstmt
  | Snode : var -> hfexpr -> hfstmt
  | Sfcnct : href -> hfexpr -> hfstmt
  (* | Spcnct : href -> hfexpr -> hfstmt *)
  | Sinvalid : href -> hfstmt
  (* | Sattach : seq var -> fstmt *)
  | Swhen : hfexpr -> hfstmt_seq -> hfstmt_seq -> hfstmt
  (* | Sstop : hfexpr -> hfexpr -> nat -> hfstmt *)
  (* | Sprintf (* TBD *) *)
  (* | Sassert (* TBD *) *)
  (* | Sassume (* TBD *) *)
  (* | Sdefname : var -> fstmt *) (* TBD *)
  (* | Sparam : var -> fexpr -> fstmt *) (* TBD *)
  with hfstmt_seq : Type :=
       | Qnil
       | Qcons : hfstmt -> hfstmt_seq -> hfstmt_seq.

   Scheme hfstmt_seq_hfstmt_ind := Induction for hfstmt_seq Sort Prop
   with hfstmt_hfstmt_seq_ind := Induction for hfstmt Sort Prop.

   (** equality of hfstmt and hfstmt_seq are decidable *)

  Fixpoint hfstmt_eqn (x y : hfstmt) : bool :=
  match x, y with
  | Sskip, Sskip => true
  | Swire vx tx, Swire vy ty => (vx == vy) && (tx == ty)
  | Sreg vx rx, Sreg vy ry => (vx == vy) && (rx == ry)
  | Smem vx mx, Smem vy my => (vx == vy) && (mx == my)
  | Sinst vx wx, Sinst vy wy => (vx == vy) && (wx == wy)
  | Snode vx ex, Snode vy ey => (vx == vy) && (ex == ey)
  | Sfcnct rx ex, Sfcnct ry ey => (rx == ry) && (ex == ey)
  (* | Spcnct : href -> hfexpr -> hfstmt *)
  | Sinvalid rx, Sinvalid ry => rx == ry
  (* | Sattach : seq var -> fstmt *)
  | Swhen ex tx fx, Swhen ey ty fy => (ex == ey) && hfstmt_seq_eqn tx ty && hfstmt_seq_eqn fx fy
  (* | Sstop : hfexpr -> hfexpr -> nat -> hfstmt *)
  (* | Sprintf (* TBD *) *)
  (* | Sassert (* TBD *) *)
  (* | Sassume (* TBD *) *)
  (* | Sdefname : var -> fstmt *) (* TBD *)
  (* | Sparam : var -> fexpr -> fstmt *) (* TBD *)
  | _, _ => false
  end
  with hfstmt_seq_eqn (x y : hfstmt_seq) : bool :=
  match x, y with
  | Qnil, Qnil => true
  | Qcons sx qx, Qcons sy qy => hfstmt_eqn sx sy && hfstmt_seq_eqn qx qy
  | _, _ => false
  end.

  Lemma hfstmt_eqP : (*Equality.axiom hfstmt_eqn*)
              forall x y : hfstmt, reflect (x = y) (hfstmt_eqn x y)
  with hfstmt_seq_eqP : (*Equality.axiom hfstmt_seq_eqn*)
              forall x y : hfstmt_seq, reflect (x = y) (hfstmt_seq_eqn x y).
  Proof.
  * clear hfstmt_eqP.
    induction x, y ; simpl ; try (apply ReflectF ; discriminate).
    + apply ReflectT ; reflexivity.
    1-3,5: destruct (v == v0) eqn: Hs ; move /eqP : Hs => Hs ;
               last (by apply ReflectF ; injection ; done) ;
         rewrite Hs andTb.
    + destruct (f == f0) eqn: Hf ; move /eqP : Hf => Hf ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hf.
      apply ReflectT ; reflexivity.
    1-3,6: destruct (h == h0) eqn: Hh ; move /eqP : Hh => Hh ;
               last (by apply ReflectF ; injection ; done) ;
         rewrite Hh ;
         apply ReflectT ; reflexivity.
    + destruct (v == v1) eqn: Hs ; move /eqP : Hs => Hs ;
               last (by apply ReflectF ; injection ; done) ;
            rewrite Hs andTb.
      destruct (v0 == v2) eqn: Hs0 ; move /eqP : Hs0 => Hs0 ;
               last (by apply ReflectF ; injection ; done) ;
            rewrite Hs0.
      apply ReflectT ; reflexivity.
    + destruct (h == h1) eqn: Hh ; move /eqP : Hh => Hh ;
               last (by apply ReflectF ; injection ; done) ;
            rewrite Hh andTb.
      destruct (h0 == h2) eqn: Hh0 ; move /eqP : Hh0 => Hh0 ;
               last (by apply ReflectF ; injection ; done) ;
            rewrite Hh0.
      apply ReflectT ; reflexivity.
    + destruct (h == h2) eqn: Hh ; move /eqP : Hh => Hh ;
               last (by apply ReflectF ; injection ; done) ;
            rewrite Hh andTb.
      generalize (hfstmt_seq_eqP h0 h3) ; intro.
      apply reflect_iff in H.
      destruct (hfstmt_seq_eqn h0 h3) ;
            last by (apply ReflectF ; injection ; intros _ H1 ;
                     apply H in H1 ; done).
      destruct H as [_ H] ; rewrite H // andTb.
      specialize (hfstmt_seq_eqP h1 h4).
      apply reflect_iff in hfstmt_seq_eqP.
      destruct (hfstmt_seq_eqn h1 h4) ;
            last by (apply ReflectF ; injection ; intros H1 ;
                     apply hfstmt_seq_eqP in H1 ; done).
      destruct hfstmt_seq_eqP as [_ hfstmt_seq_eqP] ; rewrite hfstmt_seq_eqP //.
      apply ReflectT ; reflexivity.
  * clear hfstmt_seq_eqP.
    induction x, y ; simpl ; try (apply ReflectF ; discriminate).
    + apply ReflectT ; reflexivity.
    + specialize (hfstmt_eqP h h0) ; apply reflect_iff in hfstmt_eqP.
      destruct (hfstmt_eqn h h0) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     apply hfstmt_eqP in H0 ; done).
      destruct hfstmt_eqP as [_ hfstmt_eqP] ; rewrite hfstmt_eqP //.
      specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (hfstmt_seq_eqn x y) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      apply ReflectT ; reflexivity.
  Qed.

Lemma hfstmt_eqP' : Equality.axiom hfstmt_eqn.
Proof.
  rewrite /Equality.axiom.
  apply hfstmt_eqP.
Qed.
Lemma hfstmt_seq_eqP' : Equality.axiom hfstmt_seq_eqn.
Proof.
  rewrite /Equality.axiom.
  apply hfstmt_seq_eqP.
Qed.

HB.instance Definition _ := hasDecEq.Build hfstmt hfstmt_eqP'.
HB.instance Definition _ := hasDecEq.Build hfstmt_seq hfstmt_seq_eqP'.

   (** hfstmt_seq is an equivalence relation *)

   Definition Qhead (default : hfstmt) (s : hfstmt_seq) : hfstmt :=
   match s with Qnil => default
              | Qcons h tl => h end.

   Fixpoint Qcat (s1 s2 : hfstmt_seq) : hfstmt_seq :=
   match s1 with Qnil => s2
               | Qcons h1 tl1 => Qcons h1 (Qcat tl1 s2) end.

   Lemma Qcats0 : forall (ss : hfstmt_seq),
      Qcat ss Qnil = ss.
   Proof.
   induction ss.
   * by unfold Qcat ; reflexivity.
   * by simpl Qcat ; rewrite IHss ; reflexivity.
   Qed.

   Lemma Qcat_nil : forall (ss1 ss2 : hfstmt_seq),
       Qcat ss1 ss2 = Qnil -> ss1 = Qnil /\ ss2 = Qnil.
   Proof.
   induction ss1.
   * induction ss2 ; first by intros ; split ; reflexivity.
     simpl Qcat ; discriminate.
   * intro ; simpl Qcat ; discriminate.
   Qed.

   Lemma Qcat_assoc : forall (ss1 ss2 ss3 : hfstmt_seq),
      Qcat (Qcat ss1 ss2) ss3 = Qcat ss1 (Qcat ss2 ss3).
   Proof.
   induction ss1.
   * simpl Qcat ; by reflexivity.
   * intros ; simpl Qcat ; rewrite IHss1 ; reflexivity.
   Qed.

   Fixpoint Qcatrev (s1 s2 : hfstmt_seq) : hfstmt_seq := (* calculates the reversal of s1, followed by s2 *)
   match s1 with Qnil => s2
               | Qcons h1 tl1 => Qcatrev tl1 (Qcons h1 s2) end.

   Definition Qrev (s : hfstmt_seq) : hfstmt_seq := Qcatrev s Qnil.

   Fixpoint Qin (s : hfstmt) (ss : hfstmt_seq) : bool :=
    match ss with Qnil => false
                | Qcons h tl => (hfstmt_eqn h s) || (Qin s tl)
    end.

   Fixpoint Qrcons (ss : hfstmt_seq) (s : hfstmt) : hfstmt_seq :=
   match ss with
   | Qnil => Qcons s Qnil
   | Qcons h tl => Qcons h (Qrcons tl s)
   end.

   Lemma Qcat_rcons : forall (ss1 : hfstmt_seq) (s : hfstmt) (ss2 : hfstmt_seq),
      Qcat (Qrcons ss1 s) ss2 = Qcat ss1 (Qcons s ss2).
   Proof.
   induction ss1.
   * unfold Qrcons ; simpl Qcat ; reflexivity.
   * simpl Qrcons ; simpl Qcat.
     intros.
     rewrite IHss1 ; reflexivity.
   Qed.

   Lemma Qcats1 : forall (ss : hfstmt_seq) (s : hfstmt),
       Qcat ss (Qcons s Qnil) = Qrcons ss s.
   Proof.
   induction ss.
   * simpl ; reflexivity.
   * simpl.
     intro ; rewrite -IHss //.
   Qed.

Fixpoint Qcatrev_rec (ss1 ss2 : hfstmt_seq) : hfstmt_seq :=
(* calculates the recursive reversal of ss1, followed by ss2 *)
  match ss1 with
    Qnil => ss2
  | Qcons h1 tl1 =>
      Qcatrev_rec tl1 (Qcons (Qrev_rec h1) ss2) end
with Qrev_rec (s : hfstmt) : hfstmt :=
       match s with
         Swhen c sst ssf =>
           Swhen c (Qcatrev_rec sst Qnil) (Qcatrev_rec ssf Qnil)
       | s => s end.
   
Lemma qcatrev_rec0s s : Qcatrev_rec Qnil s = s.
Proof. by []. Qed.

Lemma qcat0s s : Qcat Qnil s = s.
Proof. by []. Qed.

Lemma qcats0 s : Qcat s Qnil = s.
Proof.
  elim : s => // h h0 /= ->//. 
Qed.

Variable n0 : nat.  (* numerical parameter for take, drop et al *)
Variable T : Type.  (* must come before the implicit Type     *)
Variable x0 : T.    (* default for head/nth *)

Implicit Types x y z : T.
Implicit Types m n : nat.
Implicit Type s : seq T.
Lemma last_ind P :
  P [::] -> (forall s x, P s -> P (rcons s x)) -> forall s, P s.
Proof.
move=> Hnil Hlast s. rewrite -(cat0s s).
elim : s nil Hnil => [|x s2 IHs] s1 Hs1.
by rewrite cats0.
by rewrite -cat_rcons; apply/IHs /Hlast.
Qed.

Lemma Qrcons_ind' :
   forall (P : hfstmt_seq -> Prop) (P0 : hfstmt -> Prop),
       P Qnil ->
       (forall h : hfstmt, P0 h -> forall h0 : hfstmt_seq, P h0 -> P (Qrcons h0 h)) ->
       P0 Sskip ->
       (forall (s : var) (f2 : ftype), P0 (Swire s f2)) ->
       (forall (s : var) (h : hfreg), P0 (Sreg s h)) ->
       (forall (s : var) (h : hfmem), P0 (Smem s h)) ->
       (forall s s0 : var, P0 (Sinst s s0)) ->
       (forall (s : var) (h : hfexpr), P0 (Snode s h)) ->
       (forall (h : href) (h0 : hfexpr), P0 (Sfcnct h h0)) ->
       (forall h : href, P0 (Sinvalid h)) ->
       (forall (h : hfexpr) (h0 : hfstmt_seq),
        P h0 -> forall h1 : hfstmt_seq, P h1 -> P0 (Swhen h h0 h1)) ->
       forall h : hfstmt, P0 h

with Qrcons_seq_ind' :
forall (P : hfstmt_seq -> Prop) (P0 : hfstmt -> Prop),
       P Qnil ->
       (forall h : hfstmt, P0 h -> forall h0 : hfstmt_seq, P h0 -> P (Qrcons h0 h)) ->
       P0 Sskip ->
       (forall (s : var) (f2 : ftype), P0 (Swire s f2)) ->
       (forall (s : var) (h : hfreg), P0 (Sreg s h)) ->
       (forall (s : var) (h : hfmem), P0 (Smem s h)) ->
       (forall s s0 : var, P0 (Sinst s s0)) ->
       (forall (s : var) (h : hfexpr), P0 (Snode s h)) ->
       (forall (h : href) (h0 : hfexpr), P0 (Sfcnct h h0)) ->
       (forall h : href, P0 (Sinvalid h)) ->
       (forall (h : hfexpr) (h0 : hfstmt_seq),
        P h0 -> forall h1 : hfstmt_seq, P h1 -> P0 (Swhen h h0 h1)) ->
       forall h : hfstmt_seq, P h.
Proof.
  intros. move : h.
  elim; try done. 
  intros. apply H9;
    by apply (Qrcons_seq_ind' P P0).

  intros. rewrite-(qcat0s h). generalize H. move => Hnil.
  elim : h Qnil H => [|x s2 IHs] s1 Hs1.
  by rewrite qcats0.
  rewrite -Qcat_rcons. apply IHs. apply H0; last done.
  apply (Qrcons_ind' P); try done. 
Qed.
  
Lemma Qrcons_ind :
forall (Ps : hfstmt -> Prop) (Pss : hfstmt_seq -> Prop),
(Ps Sskip) ->
(forall (v : var) (ft : ftype), Ps (Swire v ft)) ->
(forall (v : var) (r : hfreg),  Ps (Sreg v r)) ->
(forall (v : var) (m : hfmem),  Ps (Smem v m)) ->
(forall (v1 v2 : var),          Ps (Sinst v1 v2)) ->
(forall (v : var) (e : hfexpr), Ps (Snode v e)) ->
(forall (r : href) (e : hfexpr), Ps (Sfcnct r e)) ->
(forall (f : href),             Ps (Sinvalid f)) ->
(forall (cond : hfexpr) (sst : hfstmt_seq), Pss sst -> forall (ssf : hfstmt_seq), Pss ssf -> Ps (Swhen cond sst ssf)) ->
(Pss Qnil) ->
(forall (s : hfstmt), Ps s -> forall (ss : hfstmt_seq), Pss ss -> Pss (Qrcons ss s)) ->
(forall s : hfstmt, Ps s) /\ (forall ss : hfstmt_seq, Pss ss).
Proof.
  intros. split.
  apply Qrcons_ind' with Pss; try done.
  apply Qrcons_seq_ind' with Ps; try done.
Qed.

   Lemma Qeqseq_cons : forall (s : hfstmt) (ss1 ss2 : hfstmt_seq), (Qcons s ss1 == Qcons s ss2) = (ss1 == ss2).
   Proof.
   intros.
   destruct (ss1 == ss2) eqn: H ; move /eqP : H => H ;
         first by rewrite -H eq_refl //.
   apply negbTE.
   apply rwP with (P := ~ (Qcons s ss1 == Qcons s ss2)) ; first by apply negP.
   contradict H.
   move /eqP : H => H ; injection H ; done.
   Qed.

   Lemma Qeqseqr_cat : forall (ss1 ss2 ss3 : hfstmt_seq), (Qcat ss1 ss2 == Qcat ss1 ss3) = (ss2 == ss3).
   Proof.
   induction ss1.
   * simpl Qcat ; reflexivity.
   * simpl Qcat ; intros.
     rewrite Qeqseq_cons IHss1 //.
   Qed.

  (* Fixpoint Qfoldl {R : Type} (f : R -> hfstmt -> R) (s : hfstmt_seq) (default : R) :=
   match s with Qnil => default
              | Qcons h tl => Qfoldl f tl (f default h) end.
   Fixpoint Qfoldr {R : Type} (f : hfstmt -> R -> R) (default : R) (s : hfstmt_seq) :=
   match s with Qnil => default
              | Qcons h tl => f h (Qfoldr f default tl) end. *)

  Inductive hfport : Type :=
  | Finput : var -> ftype -> hfport
  | Foutput : var -> ftype -> hfport
  .

  Definition hfport_eqn (x y : hfport) : bool :=
  match x, y with
  | Finput vx fx, Finput vy fy
  | Foutput vx fx, Foutput vy fy => (vx == vy) && (fx == fy)
  | _, _ => false
  end.

  Lemma hfport_eqP : Equality.axiom hfport_eqn.
  Proof.
  rewrite /Equality.axiom /hfport_eqn.
  intros.
  destruct x, y ; try (apply ReflectF ; discriminate).
  1,2: destruct (v == v0) eqn: Hs.
  2,4: move /eqP : Hs => Hs ; apply ReflectF ; injection ; done.
  1,2: move /eqP : Hs => Hs ; rewrite -Hs andTb ; clear Hs v0 ;
       destruct (f == f0) eqn: Hf.
  2,4: move /eqP : Hf => Hf ; apply ReflectF ; injection ; done.
  1,2: move /eqP : Hf => Hf ; rewrite -Hf ; clear Hf f0 ;
       apply ReflectT ; reflexivity.
  Qed.

HB.instance Definition _ := hasDecEq.Build hfport hfport_eqP.

  Inductive hfmodule : Type :=
  | FInmod : var -> seq hfport -> hfstmt_seq -> hfmodule
  | FExmod : var -> seq hfport -> hfstmt_seq -> hfmodule
(* DNJ: External modules do not contain statements but only an interface.
They may contain the following special statements:
one “defname = ...” (to set the Verilog name)
zero, one, or multiple “parameter <variable> = <constant> (to pass parameters to the Verilog design that implements this module)
XM : TO BE DESIGNED , how to present the parameters
Discussion result: Because we concentrate on correctness,
and external modules are black boxes whose behaviour is unknown,
it does not make sense to put effort in external modules.
*)
  .

  Inductive hfcircuit : Type := Fcircuit : var -> seq hfmodule -> hfcircuit.

  Inductive forient : Type :=
  | Source | Sink | Duplex | Passive | Other.

  Definition forient_eqn (x y : forient) : bool :=
  match x, y with Source, Source | Sink, Sink | Duplex, Duplex | Passive, Passive | Other, Other => true
                | _, _ => false end.
  Lemma forient_eqP : Equality.axiom forient_eqn.
  Proof. unfold Equality.axiom, forient_eqn. induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity). Qed.
  HB.instance Definition _ := hasDecEq.Build forient forient_eqP.
  
  Definition orient_of_comp c :=
    match c with
    | In_port | Instanceof | Memory | Node => Source
    (* DNJ: Not sure whether a memory should be a source. It is written like that
    in the specificiation, but actually the data type of a memory port is a bundle
    defined as a sink (with some fields flipped). *)
    | Out_port => Sink
    | Register | Wire => Duplex
    | Fmodule => Other
    end.

  Definition valid_lhs_orient o :=
    match o with
    | Sink | Duplex => true
    | _ => false
    end.

  Definition valid_rhs_orient o :=
    match o with
    | Source | Duplex | Passive => true
    | _ => false
    end.

End HiFirrtl.

Fixpoint fcomponent_amount_s (s : hfstmt) : nat :=
match s with
  | Sskip => 0
  | Sfcnct _ _ => 0
  | Sinvalid _ => 0
  | Swire _ _ => 1
  | Sreg v reg => 1
  | Snode _ _ => 1
  | Smem _ _ => 1
  | Sinst _ _ => 1
  | Swhen _ ss_true ss_false =>
    fcomponent_amount_ss ss_true + fcomponent_amount_ss ss_false
  end
with fcomponent_amount_ss (ss : hfstmt_seq) : nat :=
  match ss with
  | Qnil => 0
  | Qcons s st => fcomponent_amount_s s + fcomponent_amount_ss st
  end.

Definition fcomponent_amount_m (m : hfmodule) : nat :=
  match m with
  | FInmod _ ps ss => List.length ps + fcomponent_amount_ss ss
  | _ => 0
  end.

Fixpoint fcomponent_amount_ml (ml : seq hfmodule) : nat :=
  match ml with
  | nil => 0
  | hd :: tl => fcomponent_amount_m hd + fcomponent_amount_ml tl
  end.

Definition fcomponent_amount (c : hfcircuit) : nat :=
  match c with
  | Fcircuit v ml => fcomponent_amount_ml ml
  end.

  (* ground type equivalence *)
  Definition fgtyp_equiv t1 t2 :=
    match t1, t2 with
    | Fuint _, Fuint _
    | Fuint_implicit _, Fuint _
    | Fuint _, Fuint_implicit _
    | Fuint_implicit _, Fuint_implicit _
    | Fsint _, Fsint _
    | Fsint_implicit _, Fsint _
    | Fsint _, Fsint_implicit _
    | Fsint_implicit _, Fsint_implicit _
    | Fclock, Fclock
    | Freset, Freset
    (* | Freset, Fuint 1 *)
    | Fasyncreset, Fasyncreset => true
    | _, _ => false
    end.

  (* type equivalence *)
  Fixpoint ftype_equiv (t1 t2 : ftype) : bool :=
    match t1, t2 with
    | Gtyp gt1, Gtyp gt2 => fgtyp_equiv gt1 gt2
    | Atyp t1 n1, Atyp t2 n2 => (n1 == n2) && ftype_equiv t1 t2
    | Btyp bt1, Btyp bt2 => fbtyp_equiv bt1 bt2
    | _, _ => false
    end
  with fbtyp_equiv (bt1 bt2 : ffield) : bool :=
         match bt1, bt2 with
         | Fnil, Fnil => true
         | Fflips v1 Flipped t1 fs1, Fflips v2 Flipped t2 fs2 =>
           (v1 == v2) && ftype_equiv t1 t2 && fbtyp_equiv fs1 fs2
         | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2 =>
           (v1 == v2) && ftype_equiv t1 t2 && fbtyp_equiv fs1 fs2
         | _, _ => false
         end.

  Lemma fgtyp_equiv_refl t1 : fgtyp_equiv t1 t1.
  Proof.
  case : t1; intros; try done.
  Qed.

  Lemma ftype_equiv_refl t1 : ftype_equiv t1 t1
  with fbtyp_equiv_refl f1 : fbtyp_equiv f1 f1.
  Proof.
    induction t1; simpl; try apply fgtyp_equiv_refl.
    rewrite eq_refl IHt1; done.
    apply fbtyp_equiv_refl.
    induction f1; simpl; try done.
    case : f; rewrite eq_refl IHf1 ftype_equiv_refl; done.
  Qed.

  Lemma fgtyp_equiv_comm t1 t2 : fgtyp_equiv t1 t2 -> fgtyp_equiv t2 t1.
  Proof.
    case : t1; intros; try done.
  Qed.

  Lemma ftype_equiv_comm : forall t1 t2, ftype_equiv t1 t2 -> ftype_equiv t2 t1
  with fbtyp_equiv_comm : forall f1 f2, fbtyp_equiv f1 f2 -> fbtyp_equiv f2 f1.
  Proof.
    elim; intro t1.
    elim; intro t2; simpl; try discriminate; try apply fgtyp_equiv_comm.
    intros IH n t2.
    case Ht2 : t2 => [|t2' n'|]; simpl; try discriminate.
    intro; move /andP : H => [H1 H2]; move /eqP : H1 => H1; rewrite H1; apply IH in H2.
    rewrite eq_refl H2; done.
    intro t2.
    case Ht2 : t2 => [||t2']; simpl; try discriminate; try apply fbtyp_equiv_comm.
    elim.
    intro t2.
    case Ht2 : t2; simpl; try discriminate; try done.
    intros v f f0 f1 IH.
    intro t2; case Ht2 : t2 => [|v' f' f0' f1']; simpl; case Hf : f; try discriminate.
    1,2: case Hf' : f'; try discriminate.
    1,2: intro.
    1,2: move /andP : H => [H1 H2]; move /andP : H1 => [H1 H]; move /eqP : H1 => H1; rewrite H1 eq_refl.
    1,2: apply IH in H2; apply ftype_equiv_comm in H; rewrite H H2; done.
  Qed.

Lemma fgtyp_equiv_dlvr : forall t1 t2 t3, fgtyp_equiv t1 t2 -> fgtyp_equiv t2 t3 -> fgtyp_equiv t1 t3.
Proof.
  intros.
  case Ht1 : t1; case Ht2 : t2; case Ht3 : t3; rewrite Ht1 Ht2 in H; rewrite Ht2 Ht3 in H0; simpl in H; simpl in H0; simpl; try done; try discriminate.
Qed.

Lemma ftype_equiv_dlvr : forall t1 t2 t3, ftype_equiv t1 t2 -> ftype_equiv t2 t3 -> ftype_equiv t1 t3
with ftype_equiv_dlvr_f : forall t1 t2 t3, fbtyp_equiv t1 t2 -> fbtyp_equiv t2 t3 -> fbtyp_equiv t1 t3.
Proof.
  elim.
  intros gt1 t2 t3 H H0.
  case Ht2 : t2 => [gt2|atyp2 n2|btyp2]; rewrite Ht2 in H H0; simpl in H; try discriminate.
  case Ht3 : t3 => [gt3|atyp3 n3|btyp3]; rewrite Ht3 in H H0; simpl in H0; simpl; try done; try discriminate.
  move : H H0; apply fgtyp_equiv_dlvr.

  intros atyp1 IH n1 t2 t3 H H0.
  case Ht2 : t2 => [gt2|atyp2 n2|btyp2]; rewrite Ht2 in H H0; simpl in H; try discriminate.
  case Ht3 : t3 => [gt3|atyp3 n3|btyp3]; rewrite Ht3 in H H0; simpl in H0; simpl; try done; try discriminate.
  move /andP : H => [H1 H].
  move /andP : H0 => [H2 H0].
  move /eqP : H1 => H1.
  move /eqP : H2 => H2.
  apply rwP with (P := (n1 == n3) /\ ftype_equiv atyp1 atyp3).
  apply andP.
  split.
  rewrite H1 -H2; try done.
  move : H H0; apply IH.

  intros btyp t2 t3 H H0.
  case Ht2 : t2 => [gt2|atyp2 n2|btyp2]; rewrite Ht2 in H H0; simpl in H; try discriminate.
  case Ht3 : t3 => [gt3|atyp3 n3|btyp3]; rewrite Ht3 in H H0; simpl in H0; simpl; try done; try discriminate.
  move : H H0; apply ftype_equiv_dlvr_f.

  elim.
  intros t2 t3 H H0.
  case Ht2 : t2 => [|v2 fl2 ft2 f2]; rewrite Ht2 in H H0; simpl in H; try discriminate.
  case Ht3 : t3 => [|v3 fl3 ft3 f3]; rewrite Ht3 in H0; simpl in H0; try discriminate.
  simpl; done.
  intros v1 fl1 ft1 f1 IH t2 t3 H H0.
  case Ht2 : t2 => [|v2 fl2 ft2 f2]; rewrite Ht2 in H H0; simpl in H; case Hf1 : fl1; rewrite Hf1 in H; try discriminate.
  case Hf2 : fl2; rewrite Hf2 in H; try discriminate.
  case Ht3 : t3 => [|v3 fl3 ft3 f3]; rewrite Ht3 Hf2 in H0; simpl in H0; try discriminate.
  case Hf3 : fl3; rewrite Hf3 in H0; try discriminate.
  simpl.
  move /andP : H => [H H1].
  move /andP : H => [H H']. 
  move /andP : H0 => [H0 H2].
  move /andP : H0 => [H0 H3].
  move /eqP : H => H.
  move /eqP : H0 => H0.
  apply rwP with (P := (v1 == v3) && ftype_equiv ft1 ft3 /\ fbtyp_equiv f1 f3).
  apply andP.
  split.
  apply rwP with (P := (v1 == v3) /\ ftype_equiv ft1 ft3).
  apply andP.
  split.
  rewrite H -H0; done.
  move : H' H3; apply ftype_equiv_dlvr.
  move : H1 H2; apply IH.
  case Hf2 : fl2; rewrite Hf2 in H; try discriminate.
  case Ht3 : t3 => [|v3 fl3 ft3 f3]; rewrite Ht3 Hf2 in H0; simpl in H0; try discriminate.
  case Hf3 : fl3; rewrite Hf3 in H0; try discriminate.
  simpl.
  move /andP : H => [H H1].
  move /andP : H => [H H']. 
  move /andP : H0 => [H0 H2].
  move /andP : H0 => [H0 H3].
  move /eqP : H => H.
  move /eqP : H0 => H0.
  apply rwP with (P := (v1 == v3) && ftype_equiv ft1 ft3 /\ fbtyp_equiv f1 f3).
  apply andP.
  split.
  apply rwP with (P := (v1 == v3) /\ ftype_equiv ft1 ft3).
  apply andP.
  split.
  rewrite H -H0; done.
  move : H' H3; apply ftype_equiv_dlvr.
  move : H1 H2; apply IH.
Qed.

(* old 
Module VarType <: DecidableType.
  Definition t : Type := N.
  Definition eq : t -> t -> Prop := fun x y => x == y.
  Lemma eq_refl (x : t) : eq x x.
  Proof. exact: eqxx. Qed.

  Lemma eq_sym (x y : t) : eq x y -> eq y x.
  Proof. by rewrite /eq eq_sym. Qed.

  Lemma eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof. move=> Hxy Hyz. rewrite (eqP Hxy). exact: Hyz. Qed.

  Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    move=> x y.
    case Hxy: (x == y).
    - left; exact: Hxy.
    - right; move=> Heq.
      apply/negPf: Hxy.
      exact: Heq.
  Qed.
End VarType.

Module MakeProdVar (O1 : DecidableType) <: DecidableType.
  Definition t := (O1.t * O1.t)%type.
  Definition eq (x y : t) : Prop := (O1.eq x.1 y.1) /\ (O1.eq x.2 y.2).
  Lemma eq_refl (x : t) : eq x x.
  Proof. by split; apply O1.eq_refl. Qed.

  Lemma eq_sym (x y : t) : eq x y -> eq y x.
  Proof. 
    move=> [H1 H2]. 
    by split; apply O1.eq_sym. 
  Qed.

  Lemma eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof.
    move=> [Hxy1 Hxy2] [Hyz1 Hyz2].
    split; [apply O1.eq_trans with y.1 | apply O1.eq_trans with y.2]; auto.
  Qed.

  Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    move=> [x1 x2] [y1 y2].
    case Hx1y1: (O1.eq_dec x1 y1) => [H1|H1].
    case Hx2y2: (O1.eq_dec x2 y2) => [H2|H2].
    + left; split; assumption.
    + right; move=> [H3 H4]. 
      apply H2. apply H4. 
    - right; move=> [H2 H3]. 
      apply H1. apply H2. 
  Qed.

End MakeProdVar.

Module ProdVar := MakeProdVar VarType.

Module VarMap (X : DecidableType) <: FMapInterface.WS.
  Include FMapWeakList.Make X.
End VarMap.

Module VM := VarMap VarType.
Module PVM := VarMap ProdVar.*)

Module Type VarType <: DecidableType.
  Definition t : Type := N.
  Definition eq : t -> t -> Prop := fun x y => x == y.
  Lemma eq_refl (x : t) : eq x x.
  Proof. exact: eqxx. Qed.

  Lemma eq_sym (x y : t) : eq x y -> eq y x.
  Proof. by rewrite /eq eq_sym. Qed.

  Lemma eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof. move=> Hxy Hyz. rewrite (eqP Hxy). exact: Hyz. Qed.

  Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    move=> x y.
    case Hxy: (x == y).
    - left; exact: Hxy.
    - right; move=> Heq.
      apply/negPf: Hxy.
      exact: Heq.
  Qed.
End VarType.

Module OrderedVarType <: OrderedType.
  Include VarType. 

  Definition lt : t -> t -> Prop := fun x y => N.lt x y.
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z Hxy Hyz.
    unfold lt in *.
    move : Hxy Hyz; apply N.lt_trans.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y Hlt Heq.
    unfold lt, eq in *.
    move /eqP : Heq => Heq; subst.
    apply N.lt_irrefl in Hlt.
    contradiction.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros x y.
    case_eq (N.compare x y);
      intros Hcomp.
    - apply EQ.
      unfold eq.
      apply N.compare_eq in Hcomp; subst.
      apply eq_refl.
    - apply LT.
      unfold lt.
      apply N.compare_lt_iff in Hcomp.
      assumption.
    - apply GT.
      unfold lt.
      apply N.compare_gt_iff in Hcomp.
      assumption.
  Defined.

End OrderedVarType.

Module ProdVar <: OrderedType.

  Definition t := (OrderedVarType.t * OrderedVarType.t)%type.
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
    case Hx2y2: (OrderedVarType.eq_dec x2 y2) => [H2|H2].
    + left; split; assumption.
    + right; move=> [H3 H4]. 
      apply H2. apply H4. 
    - right; move=> [H2 H3]. 
      apply H1. apply H2. 
  Qed.

  Definition lt (x y : t) : Prop :=
    N.lt x.1 y.1 \/ ((fst x) == (fst y) /\ N.lt (snd x) (snd y)).
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
      + move : Hxy2 Hyz2; apply N.lt_trans.
  Qed.

  (* 严格小于蕴含不等 *)
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros [x1 x2] [y1 y2] [Hlt|Hlt] [Heq1 Heq2].
    - (* Case 1: x1 < y1 ∧ x == y *)
      apply (OrderedVarType.lt_not_eq Hlt). apply Heq1.
    - (* Case 2: x1 = y1 ∧ x2 < y2 ∧ x == y *)
      apply (OrderedVarType.lt_not_eq Hlt.2). apply Heq2.
  Qed.

  (* 字典序比较函数 *)
  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros [x1 x2] [y1 y2].
    case (OrderedVarType.compare x1 y1).
    - (* x1 < y1 *)
      intros; apply LT. left. assumption.
    - (* x1 = y1 *)
      case (OrderedVarType.compare x2 y2).
      + (* x2 < y2 *)
        intros; apply LT. right. split; simpl.
        rewrite e //. done.
      + (* x2 = y2 *)
        intros; apply EQ. split; assumption.
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

End ProdVar.

HB.instance Definition _ := hasDecEq.Build ProdVar.t ProdVar.eqP.

(* Extra lemmas for Coq finite maps *)

Module FMapLemmas (M : FMapInterface.S).

  Module F := Facts(M).
  Module OP := OrdProperties(M).
  Include F.
  Include OP.

  Section FMapLemmas.

    Variable elt elt' : Type.

    Lemma memP k (m : M.t elt) : reflect (M.In k m) (M.mem k m).
    Proof.
      case H: (M.mem k m).
      - apply: ReflectT. exact: (M.mem_2 H).
      - apply: ReflectF. move=> Hin; move: (M.mem_1 Hin). rewrite H; discriminate.
    Qed.

    Lemma find_some_mapsto (m : M.t elt) x e : M.find x m = Some e -> M.MapsTo x e m.
    Proof.
      exact: (proj2 (F.find_mapsto_iff m x e)).
    Qed.

    Lemma mapsto_find_some (m : M.t elt) x e : M.MapsTo x e m -> M.find x m = Some e.
    Proof.
      exact: (proj1 (F.find_mapsto_iff m x e)).
    Qed.

    Lemma find_none_not_in (m : M.t elt) x : M.find x m = None -> ~ M.In x m.
    Proof.
      exact: (proj2 (F.not_find_in_iff m x)).
    Qed.

    Lemma not_in_find_none (m : M.t elt) x : ~ M.In x m -> M.find x m = None.
    Proof.
      exact: (proj1 (F.not_find_in_iff m x)).
    Qed.

    Lemma find_some_in (m : M.t elt) x e : M.find x m = Some e -> M.In x m.
    Proof.
      move=> H; exists e. exact: (find_some_mapsto H).
    Qed.

    Lemma in_find_some (m : M.t elt) x : M.In x m -> exists e, M.find x m = Some e.
    Proof.
      move=> [e H]. exists e. exact: (mapsto_find_some H).
    Qed.

    Lemma find_none_not_mem (m : M.t elt) x : M.find x m = None -> M.mem x m = false.
    Proof.
      move=> H. apply/memP. exact: (find_none_not_in H).
    Qed.

    Lemma not_mem_find_none (m : M.t elt) x : ~~ M.mem x m -> M.find x m = None.
    Proof.
      move/memP=> H. exact: (not_in_find_none H).
    Qed.

    Lemma find_some_mem (m : M.t elt) x e : M.find x m = Some e -> M.mem x m.
    Proof.
      move=> H. apply/memP. exact: (find_some_in H).
    Qed.

    Lemma mem_find_some (m : M.t elt) x : M.mem x m -> exists e, M.find x m = Some e.
    Proof.
      move/memP=> H. exact: (in_find_some H).
    Qed.



    Lemma find_add_eq {m : M.t elt} {x y : M.key} {e : elt} :
      M.E.eq x y -> M.find x (M.add y e m) = Some e.
    Proof.
      move=> Hxy. apply: F.add_eq_o. apply: M.E.eq_sym. exact: Hxy.
    Qed.

    Lemma find_add_neq {m : M.t elt} {x y : M.key} {e : elt} :
      ~(M.E.eq x y) -> M.find x (M.add y e m) = M.find x m.
    Proof.
      move=> Hne. apply: F.add_neq_o. move=> Heq; apply: Hne; apply: M.E.eq_sym.
      exact: Heq.
    Qed.

    Lemma mem_add_eq {m : M.t elt} {x y : M.key} {e : elt} :
      M.E.eq x y -> M.mem x (M.add y e m).
    Proof.
      move=> Hxy. apply: F.add_eq_b. apply: M.E.eq_sym. exact: Hxy.
    Qed.

    Lemma mem_add_neq {m : M.t elt} {x y : M.key} {e : elt} :
      ~(M.E.eq x y) -> M.mem x (M.add y e m) = M.mem x m.
    Proof.
      move=> Hne. apply: F.add_neq_b. move=> Heq; apply: Hne; apply: M.E.eq_sym.
      exact: Heq.
    Qed.

    Lemma find_some_map {f : elt -> elt'} {m : M.t elt} {x : M.key} {e : elt} :
      M.find x m = Some e ->
      M.find x (M.map f m) = Some (f e).
    Proof.
      move=> H. rewrite F.map_o. rewrite /option_map. rewrite H. reflexivity.
    Qed.

    Lemma find_none_map {f : elt -> elt'} {m : M.t elt} {x : M.key} :
      M.find x m = None ->
      M.find x (M.map f m) = None.
    Proof.
      move=> H. rewrite F.map_o. rewrite /option_map. rewrite H. reflexivity.
    Qed.

    Lemma find_map_some (f : elt -> elt') (m : M.t elt) (x : M.key) (e : elt') :
      M.find x (M.map f m) = Some e ->
      exists a, e = f a /\ M.find x m = Some a.
    Proof.
      move=> H. move: (M.find_2 H) => {H} H. case: (F.map_mapsto_iff m x e f) => Hf _.
      move: (Hf H) => {H Hf} [] => a [Hea Hxa]. exists a. split.
      - assumption.
      - apply: M.find_1. assumption.
    Qed.

    Lemma find_map_none (f : elt -> elt') (m : M.t elt) (x : M.key) :
      M.find x (M.map f m) = None ->
      M.find x m = None.
    Proof.
      rewrite F.map_o. rewrite /option_map. case: (M.find x m).
      - discriminate.
      - reflexivity.
    Qed.

    Lemma mem_map (f : elt -> elt') (m : M.t elt) (x : M.key) :
      M.mem x (M.map f m) = M.mem x m.
    Proof.
      exact: F.map_b.
    Qed.

    Lemma empty_mem (m : M.t elt) (x : M.key) :
      M.Empty m -> M.mem x m -> False.
    Proof.
      move=> Hempty Hmem. move/memP: Hmem => [e Hmapsto]. move: (Hempty x e); apply.
      exact: Hmapsto.
    Qed.

    Lemma find_eq_mem_eq (m1 m2 : M.t elt) (x1 x2 : M.key) :
      M.find x1 m1 = M.find x2 m2 -> M.mem x1 m1 = M.mem x2 m2.
    Proof.
      case Hfind1: (M.find x1 m1); move=> Hfind2;
      rewrite mem_find_b mem_find_b Hfind1 -Hfind2; reflexivity.
    Qed.

    Lemma Empty_in (m : M.t elt) (x : M.key) :
      M.Empty m -> ~ (M.In x m).
    Proof.
      move=> Hemp Hin. case: Hin => [v Hmapsto]. exact: (Hemp x v Hmapsto).
    Qed.

    Lemma Empty_mem (m : M.t elt) (x : M.key) :
      M.Empty m -> ~~ M.mem x m.
    Proof.
      move=> Hemp. apply/negP => Hmem. move/memP: Hmem. exact: Empty_in.
    Qed.

    Lemma Empty_find (m : M.t elt) (x : M.key) :
      M.Empty m -> M.find x m = None.
    Proof.
      move=> Hemp. move: (not_find_in_iff m x) => [H _]. apply: H => H.
      exact: (Empty_in Hemp H).
    Qed.

    Lemma find_some_none_neq (m : M.t elt) (x y : M.key) (v : elt) :
      M.find x m = Some v -> M.find y m = None ->
      ~ (M.E.eq x y).
    Proof.
      move=> Hx Hy Heq. rewrite (F.find_o _ Heq) in Hx. rewrite Hx in Hy. discriminate.
    Qed.

    Lemma Add_mem_add x k e (m m' : M.t elt) :
      OP.P.Add k e m m' ->
      M.mem x m' = M.mem x (M.add k e m).
    Proof.
      move=> Hadd. move: (Hadd x). rewrite 2!mem_find_b.
      move=> ->. reflexivity.
    Qed.

    Lemma Add_in k e (m m' : M.t elt) :
      OP.P.Add k e m m' -> M.In k m'.
    Proof.
      move=> Hadd. move: (Hadd k). rewrite (add_eq_o _ _ (M.E.eq_refl k)).
      exact: find_some_in.
    Qed.

    Lemma in_Add_in k e k' (m m' : M.t elt) :
      M.In k' m -> OP.P.Add k e m m' -> M.In k' m'.
    Proof.
      move=> Hin Hadd. case: (M.E.eq_dec k k').
      - move=> Heq. rewrite -Heq. exact: (Add_in Hadd).
      - move=> Hneq. apply/memP. rewrite (Add_mem_add k' Hadd).
        rewrite (add_neq_b _ _ Hneq). apply/memP. exact: Hin.
    Qed.

    Lemma mem_combine_cons (x : M.key) k (keys : list M.key) v (vals : list elt) :
      (M.mem x (OP.P.of_list (List.combine (k::keys) (v::vals)))) =
       ((eqb k x) || (M.mem x (OP.P.of_list (List.combine keys vals)))).
    Proof.
      rewrite /= /OP.P.uncurry /=. rewrite /eqb. case: (M.E.eq_dec k x).
      - move=> Heq. rewrite (F.add_eq_b _ _ Heq) orTb. reflexivity.
      - move=> Hneq. rewrite (F.add_neq_b _ _ Hneq) orFb. reflexivity.
    Qed.

    Lemma mem_combine_in (x : M.key) (keys : list M.key) (vals : list elt) :
      M.mem x (OP.P.of_list (List.combine keys vals)) ->
      SetoidList.InA M.E.eq x keys.
    Proof.
      elim: keys vals.
      - move=> /= vals Hmem. rewrite empty_a in Hmem. discriminate.
      - move=> key_hd key_tl IH. case.
        + move=> /= Hmem. rewrite empty_a in Hmem. discriminate.
        + move=> val_hd val_tl Hmem. rewrite mem_combine_cons in Hmem.
          move/orP: Hmem; case.
          * rewrite /eqb /=. case: (P.F.eq_dec key_hd x); last by discriminate.
            move=> H _. apply: InA_cons_hd. apply: M.E.eq_sym. exact: H.
          * move=> H. apply: InA_cons_tl. exact: (IH _ H).
    Qed.

    Lemma add_diag (x : M.key) (e : elt) (m : M.t elt) :
      M.Equal (M.add x e (M.add x e m)) (M.add x e m).
    Proof.
      move=> y. case: (M.E.eq_dec y x).
      - move=> Hyx. rewrite !(find_add_eq Hyx). reflexivity.
      - move=> Hyx. rewrite !(find_add_neq Hyx). reflexivity.
    Qed.

    Lemma add_same (x : M.key) (e : elt) (m : M.t elt) :
      M.find x m = Some e -> M.Equal (M.add x e m) m.
    Proof.
      move=> Hfind y. case: (M.E.eq_dec y x) => Hyx.
      - rewrite (find_add_eq Hyx). rewrite -Hfind Hyx. reflexivity.
      - rewrite (find_add_neq Hyx). reflexivity.
    Qed.

    Lemma add_comm (x1 x2 : M.key) (e1 e2 : elt) (m : M.t elt) :
      ~ M.E.eq x1 x2 ->
      M.Equal (M.add x1 e1 (M.add x2 e2 m)) (M.add x2 e2 (M.add x1 e1 m)).
    Proof.
      move=> Hne y. case: (M.E.eq_dec y x1); case: (M.E.eq_dec y x2).
      - move=> Heq2 Heq1. apply: False_ind. apply: Hne. rewrite -Heq1 -Heq2.
        reflexivity.
      - move=> Hne2 Heq1. rewrite (find_add_eq Heq1) (find_add_neq Hne2).
        rewrite (find_add_eq Heq1). reflexivity.
      - move=> Heq2 Hne1. rewrite (find_add_neq Hne1) !(find_add_eq Heq2).
        reflexivity.
      - move=> Hne2 Hne1. rewrite (find_add_neq Hne1) !(find_add_neq Hne2).
        rewrite (find_add_neq Hne1). reflexivity.
    Qed.

  End FMapLemmas.

  Section Proper.

    Variable elt elt' : Type.

    Variable f : elt -> elt'.

    Instance add_f_proper :
      Proper (M.E.eq ==> eq ==> M.Equal ==> M.Equal)
             (fun (k : M.key) (e : elt) (m : M.t elt') => M.add k (f e) m).
    Proof.
      move=> x1 x2 Heqx. move=> y1 y2 Heqy. move=> m1 m2 Heqm.
      have Heq: (f y1 = f y2) by rewrite Heqy. exact: (F.add_m Heqx Heq Heqm).
    Qed.

    Lemma add_f_transpose_neqkey :
      OP.P.transpose_neqkey
        M.Equal
        (fun (k : M.key) (e : elt) (m : M.t elt') => M.add k (f e) m).
    Proof.
      move=> k1 k2 e1 e2 m Hneq x. rewrite 4!add_o.
      case: (M.E.eq_dec k1 x); case: (M.E.eq_dec k2 x); try reflexivity.
      move=> Heq2 Heq1. move: (M.E.eq_sym Heq2) => {Heq2} Heq2.
      move: (M.E.eq_trans Heq1 Heq2) => Heq. apply: False_ind; apply: Hneq.
      exact: Heq.
    Qed.

  End Proper.

  Section Split.

    Variable elt elt' : Type.

    Definition split (m : M.t (elt * elt')) : M.t elt * M.t elt' :=
      (M.fold (fun k e m1 => M.add k (fst e) m1) m (M.empty elt),
       M.fold (fun k e m2 => M.add k (snd e) m2) m (M.empty elt')).

    Lemma mem_split1 (m : M.t (elt * elt')) (x : M.key) :
      M.mem x m = M.mem x (fst (split m)).
    Proof.
      rewrite /split /=. move: m. eapply OP.P.map_induction.
      - move=> m Hemp. rewrite (OP.P.fold_Empty (Equal_ST elt) _ _ Hemp).
        rewrite empty_a. rewrite (negbTE (Empty_mem x Hemp)). reflexivity.
      - move=> m m' IH y e Hin Hadd. rewrite (Add_mem_add _ Hadd).
        rewrite (OP.P.fold_Add (Equal_ST elt)
                               (add_f_proper fst)
                               (add_f_transpose_neqkey fst) _ Hin Hadd).
        case: (M.E.eq_dec y x).
        + move=> Heq. rewrite 2!(add_eq_b _ _ Heq). reflexivity.
        + move=> Hneq. rewrite 2!(add_neq_b _ _ Hneq). exact: IH.
    Qed.

    Lemma mem_split2 (m : M.t (elt * elt')) (x : M.key) :
      M.mem x m = M.mem x (snd (split m)).
    Proof.
      rewrite /split /=. move: m. eapply OP.P.map_induction.
      - move=> m Hemp. rewrite (OP.P.fold_Empty (Equal_ST elt') _ _ Hemp).
        rewrite empty_a. rewrite (negbTE (Empty_mem x Hemp)). reflexivity.
      - move=> m m' IH y e Hin Hadd. rewrite (Add_mem_add _ Hadd).
        rewrite (OP.P.fold_Add (Equal_ST elt')
                               (add_f_proper snd)
                               (add_f_transpose_neqkey snd) _ Hin Hadd).
        case: (M.E.eq_dec y x).
        + move=> Heq. rewrite 2!(add_eq_b _ _ Heq). reflexivity.
        + move=> Hneq. rewrite 2!(add_neq_b _ _ Hneq). exact: IH.
    Qed.

    Lemma find_split1_none (m : M.t (elt * elt')) (x : M.key) :
      M.find x m = None ->
      M.find x (fst (split m)) = None.
    Proof.
      rewrite /split /=. move: m. apply: OP.P.map_induction.
      - move=> m Hemp. rewrite (OP.P.fold_Empty (Equal_ST elt) _ _ Hemp).
        rewrite empty_o. reflexivity.
      - move=> m m' IH y e Hin Hadd. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt)
                               (add_f_proper fst)
                               (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + discriminate.
        + move=> _ H. exact: (IH H).
    Qed.

    Lemma find_split2_none (m : M.t (elt * elt')) (x : M.key) :
      M.find x m = None ->
      M.find x (snd (split m)) = None.
    Proof.
      rewrite /split /=. move: m. apply: OP.P.map_induction.
      - move=> m Hemp. rewrite (OP.P.fold_Empty (Equal_ST elt') _ _ Hemp).
        rewrite empty_o. reflexivity.
      - move=> m m' IH y e Hin Hadd. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt')
                               (add_f_proper snd)
                               (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + discriminate.
        + move=> _ H. exact: (IH H).
    Qed.

    Lemma find_split1_some (m : M.t (elt * elt')) (x : M.key) e1 e2 :
      M.find x m = Some (e1, e2) ->
      M.find x (fst (split m)) = Some e1.
    Proof.
      rewrite /split /=. move: m e1 e2. apply: OP.P.map_induction.
      - move=> m Hemp e1 e2. rewrite (Empty_find _ Hemp). discriminate.
      - move=> m m' IH y e Hin Hadd e1 e2. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt)
                               (add_f_proper fst)
                               (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + move=> Heq [] He. by rewrite He.
        + move=> Hneq H. exact: (IH _ _ H).
    Qed.

    Lemma find_split2_some (m : M.t (elt * elt')) (x : M.key) e1 e2 :
      M.find x m = Some (e1, e2) ->
      M.find x (snd (split m)) = Some e2.
    Proof.
      rewrite /split /=. move: m e1 e2. apply: OP.P.map_induction.
      - move=> m Hemp e1 e2. rewrite (Empty_find _ Hemp). discriminate.
      - move=> m m' IH y e Hin Hadd e1 e2. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt')
                               (add_f_proper snd)
                               (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + move=> Heq [] He. by rewrite He.
        + move=> Hneq H. exact: (IH _ _ H).
    Qed.

    Lemma split1_find_none (m : M.t (elt * elt')) (x : M.key) :
      M.find x (fst (split m)) = None ->
      M.find x m = None.
    Proof.
      rewrite /split /=. move: m. apply: OP.P.map_induction.
      - move=> m Hemp _. exact: (Empty_find _ Hemp).
      - move=> m m' IH y e Hin Hadd. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt)
                               (add_f_proper fst)
                               (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + discriminate.
        + move=> _ H. exact: (IH H).
    Qed.

    Lemma split2_find_none (m : M.t (elt * elt')) (x : M.key) :
      M.find x (snd (split m)) = None ->
      M.find x m = None.
    Proof.
      rewrite /split /=. move: m. apply: OP.P.map_induction.
      - move=> m Hemp _. exact: (Empty_find _ Hemp).
      - move=> m m' IH y e Hin Hadd. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt')
                               (add_f_proper snd)
                               (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + discriminate.
        + move=> _ H. exact: (IH H).
    Qed.

    Lemma split1_find_some (m : M.t (elt * elt')) (x : M.key) e1 :
      M.find x (fst (split m)) = Some e1 ->
      exists e2, M.find x m = Some (e1, e2).
    Proof.
      rewrite /split /=. move: m e1. apply: OP.P.map_induction.
      - move=> m Hemp e1. rewrite (OP.P.fold_Empty (Equal_ST elt) _ _ Hemp).
        rewrite empty_o. discriminate.
      - move=> m m' IH y e Hin Hadd e1. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt)
                               (add_f_proper fst)
                               (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + move=> Heq [] He. exists (snd e). rewrite -He -surjective_pairing.
          reflexivity.
        + move=> Hneq H. exact: (IH _ H).
    Qed.

    Lemma split2_find_some (m : M.t (elt * elt')) (x : M.key) e2 :
      M.find x (snd (split m)) = Some e2 ->
      exists e1, M.find x m = Some (e1, e2).
    Proof.
      rewrite /split /=. move: m e2. apply: OP.P.map_induction.
      - move=> m Hemp e2. rewrite (OP.P.fold_Empty (Equal_ST elt') _ _ Hemp).
        rewrite empty_o. discriminate.
      - move=> m m' IH y e Hin Hadd e2. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt')
                               (add_f_proper snd)
                               (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + move=> Heq [] He. exists (fst e). rewrite -He -surjective_pairing.
          reflexivity.
        + move=> Hneq H. exact: (IH _ H).
    Qed.

    Lemma split_find_some (m : M.t (elt * elt')) (x : M.key) e1 e2 :
      M.find x (fst (split m)) = Some e1 ->
      M.find x (snd (split m)) = Some e2 ->
      M.find x m = Some (e1, e2).
    Proof.
      rewrite /split /=. move: m e1 e2. apply: OP.P.map_induction.
      - move=> m Hemp e1 e2. rewrite (OP.P.fold_Empty (Equal_ST elt) _ _ Hemp).
        rewrite empty_o. discriminate.
      - move=> m m' IH y e Hin Hadd e1 e2. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt)
                               (add_f_proper fst)
                               (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite (OP.P.fold_Add (Equal_ST elt')
                               (add_f_proper snd)
                               (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 3!add_o. case: (M.E.eq_dec y x).
        + move=> Heq [] He1 [] He2. rewrite -He1 -He2 -surjective_pairing.
          reflexivity.
        + move=> Hneq H1 H2. exact: (IH _ _ H1 H2).
    Qed.

  End Split.

  Section Submap.

    Unset Implicit Arguments.

    Context {elt : Type}.

    Definition submap (m m' : M.t elt) :=
      forall {k v}, M.find k m = Some v -> M.find k m' = Some v.

    Lemma submap_refl (m : M.t elt) : submap m m.
    Proof. move=> k v Hfind. exact: Hfind. Qed.

    Lemma submap_trans {m2 m1 m3 : M.t elt} :
      submap m1 m2 -> submap m2 m3 -> submap m1 m3.
    Proof.
      move=> H12 H23 k v Hf1. apply: H23. apply: H12. exact: Hf1.
    Qed.

    Lemma submap_none_add {m1 m2 : M.t elt} {k : M.key} (e : elt) :
      submap m1 m2 -> M.find k m1 = None -> submap m1 (M.add k e m2).
    Proof.
      move=> Hsub Hfind k' v' Hfind'. rewrite add_o. case: (P.F.eq_dec k k').
      - move=> Heq. rewrite (F.find_o m1 Heq) in Hfind. rewrite Hfind in Hfind'.
        discriminate.
      - move=> Hneq. exact: (Hsub k' v' Hfind').
    Qed.

    Lemma submap_not_mem_add {m1 m2 : M.t elt} {k : M.key} (e : elt) :
      submap m1 m2 -> ~~ M.mem k m1 -> submap m1 (M.add k e m2).
    Proof.
      move=> Hsub Hmem. exact: (submap_none_add _ Hsub (not_mem_find_none Hmem)).
    Qed.

    Lemma submap_some_add {m1 m2 : M.t elt} {k : M.key} {e : elt} :
      submap m1 m2 -> M.find k m1 = Some e -> submap m1 (M.add k e m2).
    Proof.
      move=> Hsub Hfind k' v' Hfind'. rewrite add_o. case: (P.F.eq_dec k k').
      - move=> Heq. rewrite (F.find_o m1 Heq) in Hfind. rewrite Hfind in Hfind'.
        exact: Hfind'.
      - move=> Hneq. exact: (Hsub k' v' Hfind').
    Qed.

    Lemma submap_add_diag {m : M.t elt} {k : M.key} (e : elt) :
      ~~ M.mem k m -> submap m (M.add k e m).
    Proof.
      move=> Hmem. apply: (submap_not_mem_add _ _ Hmem). exact: submap_refl.
    Qed.

    Lemma submap_mem {m1 m2 : M.t elt} {k : M.key} :
      submap m1 m2 -> M.mem k m1 -> M.mem k m2.
    Proof.
      move=> Hsub Hmem1. move: (mem_find_some Hmem1) => {Hmem1} [e Hfind1].
      move: (Hsub k e Hfind1) => Hfind2. exact: (find_some_mem Hfind2).
    Qed.

    Lemma submap_add_find {m1 m2 : M.t elt} {k : M.key} {e : elt} :
      submap (M.add k e m1) m2 -> M.find k m2 = Some e.
    Proof.
      move=> H. apply: (H k e). rewrite (find_add_eq (M.E.eq_refl k)). reflexivity.
    Qed.

    Lemma submap_add_find_none {m1 m2 : M.t elt} {k : M.key} {e : elt} :
      submap (M.add k e m1) m2 -> M.find k m1 = None -> submap m1 m2.
    Proof.
      move=> H Hfindk1 x ex Hfindx1. apply: H. case: (M.E.eq_dec x k).
      - move=> Heq. apply: False_ind. rewrite (F.find_o _ Heq) Hfindk1 in Hfindx1.
        discriminate.
      - move=> Hne. rewrite (find_add_neq Hne). assumption.
    Qed.

    Lemma submap_add_not_mem {m1 m2 : M.t elt} {k : M.key} {e : elt} :
      submap (M.add k e m1) m2 -> ~~ M.mem k m1 -> submap m1 m2.
    Proof.
      move=> H Hmem. move: (not_mem_find_none Hmem) => Hfind.
      exact: (submap_add_find_none H Hfind).
    Qed.

    Lemma submap_Equal {m1 m2 : M.t elt} :
      submap m1 m2 -> submap m2 m1 -> M.Equal m1 m2.
    Proof.
      move=> Hsub12 Hsub21. move=> x. case Hfind1: (M.find x m1).
      - rewrite (Hsub12 _ _ Hfind1). reflexivity.
      - case Hfind2: (M.find x m2).
        + rewrite (Hsub21 _ _ Hfind2) in Hfind1. discriminate.
        + reflexivity.
    Qed.

    Lemma Equal_submap {m1 m2 : M.t elt} : M.Equal m1 m2 -> submap m1 m2.
    Proof.
      move=> Heq x v Hfind. rewrite (Heq x) in Hfind. exact: Hfind.
    Qed.

    Set Implicit Arguments.

  End Submap.

End FMapLemmas.

Module VarMap (X : OrderedType) <: FMapInterface.S.
  Include FMapAVL.Make X. (* FMapAVL *)
End VarMap.

(*Module VarMap (X : OrderedType) <: FMapInterface.S.
  Module M := VarMap' X.
  Module Lemmas := FMapLemmas M.
  Include M.
End VarMap.*)

Print Module VarMap.

Module VM := VarMap OrderedVarType.
Module PVM := VarMap ProdVar.
Print VM.key.
Print PVM.key.
Print PVM.find.

  (* type of ref expressions *)
  Fixpoint type_of_ref (r : href) (tmap : VM.t (ftype * forient)) : option ftype :=
    match r with
    | Eid v => match VM.find v tmap with
              | Some (ft, _) => Some ft
              | None => None
              end
    | Esubfield r v => match type_of_ref r tmap with
              | Some (Btyp fs) => let fix aux fx := (
                                          match fx with
                                          | Fflips v' f t fxs =>
                                            if (v == v') then Some t
                                            else aux fxs
                                          | Fnil => None
                                          end )
                                  in aux fs
              | _ => None
              end
    | Esubindex r n => match type_of_ref r tmap with
              | Some (Atyp ty _) => Some ty
              | _ => None
              end
    | Esubaccess r e => None
    end.

(* offset of sub-elements *)
Fixpoint size_of_ftype ft :=
  match ft with
  | Gtyp t => 1
  | Atyp t n => (size_of_ftype t) * n
  | Btyp b => size_of_fields b
  end
with size_of_fields b :=
       match b with
       | Fnil => 0
       | Fflips v fl t fs => (size_of_ftype t) + size_of_fields fs
       end.

Fixpoint offset_of_subfield_b ft fid n : option nat :=
  match ft with
  | Fnil => None
  | Fflips v fl t fs => if fid == v then Some n else offset_of_subfield_b fs fid (n + size_of_ftype t)
  end.

  (* offset of subfield/subindex recursive to the base ref *)
  Fixpoint offset_ref r tmap : option nat :=
    match r with
    | Eid v => Some 0
    | Esubindex v i => (* array[i] 的 offset 只考虑 array[0]。用于inferwidth只考虑gtyp，保持一致 *)
      offset_ref v tmap
    | Esubfield v f => match offset_ref v tmap, type_of_ref v tmap with
      | Some n, Some (Btyp ft) => offset_of_subfield_b ft f n
      | _, _ => None
      end
    | Esubaccess v e => 
      offset_ref v tmap
    end.

Fixpoint base_id (r : href) : var :=
  match r with
  | Eid v => v 
  | Esubindex v i => base_id v 
  | Esubfield v f => base_id v 
  | Esubaccess v e => base_id v 
  end.

Definition ref2pv (r : href) (tmap : VM.t (ftype * forient)) : option ProdVar.t :=
  let base_v := base_id r in
  match offset_ref r tmap with
  | Some os => Some (base_v, N.of_nat os)
  | None => None
  end.

Fixpoint pv2ref' (base_ref : href) (offset : nat) (ft :ftype) : option href :=
match ft with
  | Gtyp gt => if offset == 0 then Some base_ref
              else None
  | Atyp atyp n => if offset > (size_of_ftype atyp) then None
              else pv2ref' (Esubindex base_ref 0) offset atyp
  | Btyp ff => pv2ref_f base_ref offset ff
  end
with pv2ref_f (base_ref : href) (offset : nat) (ff : ffield) : option href :=
  match ff with
  | Fnil => None
  | Fflips v0 fl ft ff' => if offset < (size_of_ftype ft) then
              pv2ref' (Esubfield base_ref v0) offset ft else
              pv2ref_f base_ref (offset - (size_of_ftype ft)) ff'
  end.

Definition pv2ref (pv : ProdVar.t) (tmap : VM.t (ftype * forient)) : option href :=
  match VM.find pv.1 tmap with
  | Some (ft, _) => pv2ref' (Eid pv.1) (N.to_nat pv.2) ft
  | _ => None
  end.

Fixpoint update_ftype (offset : nat) (new_width : nat) (ft : ftype) : option ftype :=
  match ft with
  | Gtyp gt => if offset == 0 then match gt with
              | Fuint_implicit w => Some (Gtyp (Fuint (maxn w new_width)))
              | Fsint_implicit w => Some (Gtyp (Fsint (maxn w new_width)))
              | gt' => Some (Gtyp gt')
              end else None
  | Atyp atyp n => if offset > (size_of_ftype atyp) then None
              else match update_ftype offset new_width atyp with
              | Some newt => Some (Atyp newt n)
              | _ => None
              end
  | Btyp ff => match update_ftype_f offset new_width ff with
              | Some newf => Some (Btyp newf)
              | _ => None
              end
  end
with update_ftype_f (offset : nat) (new_width : nat) (ff : ffield) : option ffield :=
  match ff with
  | Fnil => None
  | Fflips v0 fl ft ff' => if offset < (size_of_ftype ft) then
              match update_ftype offset new_width ft with
              | Some newt => Some (Fflips v0 fl newt ff')
              | _ => None
              end else
              match update_ftype_f (offset - (size_of_ftype ft)) new_width ff' with
              | Some newf => Some (Fflips v0 fl ft newf)
              | _ => None
              end
  end.

(*Fixpoint num_ref (ft : ftype) : nat :=
   match ft with
   | Gtyp _ => 1
   | Atyp atyp n => (num_ref atyp) * n + 1
   | Btyp ff => num_ff ff + 1
   end
with num_ff (ff : ffield) : nat :=
   match ff with
   | Fnil => 0
   | Fflips _ _ ft ff' => (num_ref ft) + num_ff ff'
end.

Fixpoint ft_find_sub (checkt : ftype) (num : N) (ori : bool) : option (ftype * bool) :=
  match checkt with
  | Gtyp gt => if num == N0 then Some (checkt, ori) else None
  | Atyp atyp n => if num == N0 then Some (checkt, ori)
                   else if (((N.to_nat num) - 1) >= (num_ref atyp) * n) then None
                   else if (((N.to_nat num) - 1) mod (num_ref atyp)) == 0 (* 对应标号是atyp，可能agg *)
                   then Some (atyp, ori)
                   else 
                    ft_find_sub atyp (N.of_nat (((N.to_nat num) - 1) mod (num_ref atyp))) ori
  | Btyp ff => if num == N0 then Some (checkt, ori)
               else ft_find_sub_f ff num ori
  end
with ft_find_sub_f (ff : ffield) (num : N) (ori : bool) : option ((ftype) * bool) :=
  match ff with
  | Fflips _ Nflip ft ff' => if num == 1%num (* 找到被更新的标号, 所对应的field *)
                              then Some (ft, ori)
                              else if (N.to_nat num) > (num_ref ft) (* 不在该field中, 找下一个field *)
                                  then ft_find_sub_f ff' (N.of_nat ((N.to_nat num) - (num_ref ft))) ori
                              else (* 在field v0中 *)
                                  ft_find_sub ft (N.sub num 1%num) ori
   | Fflips _ Flipped ft ff' => if num == 1%num (* 找到被更新的标号, 所对应的field *)
                              then Some (ft, (~~ori))
                              else if (N.to_nat num) > (num_ref ft) (* 不在该field中, 找下一个field *)
                                  then ft_find_sub_f ff' (N.of_nat ((N.to_nat num) - (num_ref ft))) ori
                              else (* 在field v0中 *)
                                  ft_find_sub ft (N.sub num 1%num) (~~ori)
   | _ => None
  end.

Fixpoint ft_set_sub (checkt : ftype) (newt : fgtyp) (num : N) : option ftype :=
  match checkt with
  | Gtyp _ => if num == N0 then Some (Gtyp newt) else None
  | Atyp atyp n => if num == N0 then None (* 不用agg type更新 *)
                    else if (((N.to_nat num) - 1) >= (num_ref atyp) * n) then None
                    else (* 继续找atyp中的结构 *)
                      match ft_set_sub atyp newt (N.of_nat (((N.to_nat num) - 1) mod (num_ref atyp))) with
                      | Some natyp => Some (Atyp natyp n)
                      | None => None
                      end
  | Btyp ff => if num == N0 then None
                else match ft_set_sub_f ff newt num with
                | Some newf => Some (Btyp newf)
                | None => None
                end
  end
with ft_set_sub_f (ff : ffield) (newt : fgtyp) (num : N) : option ffield :=
  match ff with
  | Fflips v0 fl ft ff' => if (N.to_nat num) > (num_ref ft) (* 不在该field中, 找下一个field *)
                                then match ft_set_sub_f ff' newt (N.of_nat ((N.to_nat num) - (num_ref ft))) with
                                    | Some newf => Some (Fflips v0 fl ft newf)
                                    | None => None
                                    end
                                else (* 在field v0中 *)
                                   match ft_set_sub ft newt (N.sub num 1%num) with
                                   | Some newt' => Some (Fflips v0 fl newt' ff')
                                   | None => None
                                   end
  | _ => None
  end.

Definition type_of_ref (v : ProdVar.t) (tmap : PVM.t (ftype * forient)) : option (ftype * bool) :=
  match VM.find (fst v, N0) tmap with
  | Some (checkt, _) => ft_find_sub checkt (snd v) false
  | None => None
  end.*)

Definition fgtyp_mux (x y : fgtyp_explicit) : option fgtyp_explicit :=
(* Find the type of a multiplexer whose two inputs have types x and y, for ground types *)
    match x, y with
    | exist (Fuint wx) _, exist (Fuint wy) _ =>  Some (exist not_implicit_width (Fuint (maxn wx wy)) I)
    | exist (Fsint wx) _, exist (Fsint wy) _ => Some (exist not_implicit_width (Fsint (maxn wx wy)) I)
    | exist Fclock _, exist Fclock _ => Some (exist not_implicit_width Fclock I)
  (*| exist Freset _, exist Freset _ => Some Freset_exp*)
    | exist Fasyncreset _, exist Fasyncreset _ => Some (exist not_implicit_width Fasyncreset I)
    | _, _ => None
    end.

Fixpoint ftype_mux' (x : ftype) (px : ftype_not_implicit_width x) (y : ftype) (py : ftype_not_implicit_width y) : option ftype_explicit :=
  match x, px, y, py with
  | Gtyp tx, px, Gtyp ty, py =>
       match fgtyp_mux (exist not_implicit_width tx px) (exist not_implicit_width ty py) with
       | Some (exist fgt p) => Some (exist ftype_not_implicit_width (Gtyp fgt) p)
       | None => None
       end
  | Atyp tx nx, px, Atyp ty ny, py =>
       if (nx == ny) then match @ftype_mux' tx px ty py with
                          | Some (exist fat p) => Some (exist ftype_not_implicit_width (Atyp fat nx) p)
                          | None => None
                          end
                     else None
  | Btyp fx, px, Btyp fy, py =>
       match @ffield_mux' fx px fy py with
       | Some (exist ff pf) => Some (exist ftype_not_implicit_width (Btyp ff) pf)
       | _ => None
       end
  | _, _, _, _ => None
  end
with ffield_mux' (f1 : ffield) (p1 : ffield_not_implicit_width f1) (f2 : ffield) (p2 : ffield_not_implicit_width f2) : option ffield_explicit :=
       match f1, p1, f2, p2 with
       | Fnil, _, Fnil, _ => Some (exist ffield_not_implicit_width Fnil I)
       | Fflips v1 Nflip t1 fs1, p1, Fflips v2 Nflip t2 fs2, p2
         => if v1 == v2 then
               match @ftype_mux'  t1  (proj1 p1) t2  (proj1 p2),
                     @ffield_mux' fs1 (proj2 p1) fs2 (proj2 p2) with
               | Some (exist ft pt), Some (exist bf pf) =>
                   Some (exist ffield_not_implicit_width (Fflips v1 Nflip ft bf) (conj pt pf))
               | _, _ => None
               end
            else None
       | _, _, _, _ => None
       end.

Definition ftype_mux (x : ftype_explicit) (y : ftype_explicit) : option ftype_explicit :=
(* return the type of mux expression on ftypes

   Similar to mux_types in InferWidths *)
   @ftype_mux' (proj1_sig x) (proj2_sig x) (proj1_sig y) (proj2_sig y).

Fixpoint type_of_hfexpr (e : hfexpr) (tmap: VM.t (ftype * forient)) : option ftype_explicit :=
  match e with
  | Econst t bs => match t with
                  | Fuint_implicit _ => Some (exist ftype_not_implicit_width (Gtyp (Fuint (size bs))) I)
                  | Fsint_implicit _ => Some (exist ftype_not_implicit_width (Gtyp (Fsint (size bs))) I)
                  | t => Some (exist ftype_not_implicit_width (Gtyp t) I)
                  end
  | Eref r => match type_of_ref r tmap with
            | Some ft => Some (make_ftype_explicit ft)
            | _ => None
            end
  | Ecast AsUInt e1 => match type_of_hfexpr e1 tmap with
                        | Some (exist (Gtyp (Fsint w)) _)
                        | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                        | Some (exist (Gtyp Fclock) _)
                        | Some (exist (Gtyp Freset) _)
                        | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                        | _ => None
                        end
  | Ecast AsSInt e1 => match type_of_hfexpr e1 tmap with
                        | Some (exist (Gtyp (Fsint w)) _)
                        | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                        | Some (exist (Gtyp Fclock) _)
                        | Some (exist (Gtyp Freset) _)
                        | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint 1)) I)
                        | _ => None
                        end
  | Ecast AsClock e1 => match type_of_hfexpr e1 tmap with
                        | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fclock) I)
                        | _ => None
                        end
  | Ecast AsAsync e1 => match type_of_hfexpr e1 tmap with
                        | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fasyncreset) I)
                        | _ => None
                        end
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w n))) I)
                              | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w n))) I)
                              | _ => None
                              end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + n))) I)
                              | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w + n))) I)
                              | _ => None
                              end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn (w - n) 1))) I)
                              | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn (w - n) 0))) I)
                              | _ => None
                              end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr e1 tmap with
                          | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                          | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                          | _ => None
                          end
  | Eprim_unop Uneg e1 => match type_of_hfexpr e1 tmap with
                          | Some (exist (Gtyp (Fsint w)) _)
                          | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                          | _ => None
                          end
  | Eprim_unop Unot e1 => match type_of_hfexpr e1 tmap with
                          | Some (exist (Gtyp (Fsint w)) _)
                          | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                          | _ => None
                          end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 tmap with
                                    | Some (exist (Gtyp (Fsint w)) _)
                                    | Some (exist (Gtyp (Fuint w)) _) =>
                                        (*if (n2 <= n1) && (n1 < w) then*) Some (exist ftype_not_implicit_width (Gtyp (Fuint (n1 - n2 + 1))) I)
                                                                  (*else None*)
                                    | _ => None
                                    end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _)
                                | Some (exist (Gtyp (Fuint w)) _) =>
                                    (*if n <= w then*) Some (exist ftype_not_implicit_width (Gtyp (Fuint n)) I)
                                              (*else None*)
                                | _ => None
                                end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _)
                                | Some (exist (Gtyp (Fuint w)) _) =>
                                    (*if n <= w then*) Some (exist ftype_not_implicit_width (Gtyp (Fuint (w - n))) I)
                                              (*else None*)
                                | _ => None
                                end
  | Eprim_unop _ e1 => match type_of_hfexpr e1 tmap with
                        | Some (exist (Gtyp (Fsint _)) _)
                        | Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                        | _ => None
                        end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                    | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _)
                                    | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                                    | _, _ => None
                                    end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2 + 1))) I)
                              | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w1 w2 + 1))) I)
                              | _, _ => None
                              end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                              | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + w2))) I)
                              | _, _ => None
                              end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + 1))) I)
                                | _, _ => None
                                end
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (minn w1 w2))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (minn w1 w2))) I)
                                | _, _ => None
                                end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (2 ^ w2 + w1 - 1))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (2 ^ w2 + w1 - 1))) I)
                                | _, _ => None
                                end
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w1)) I)
                                | _, _ => None
                                end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                              | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                              | _, _ => None
                              end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                              | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2))) I)
                              | _, _ => None
                              end
  | Emux c e1 e2 => match type_of_hfexpr c tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                    | Some (exist (Gtyp (Fuint _)) _), Some t1, Some t2 => ftype_mux t1 t2
                    | _, _, _ => None
                    end
  (*| Evalidif c e1 => match type_of_hfexpr c tmap with
                    | Some (exist (Gtyp (Fuint 1)) _) => type_of_hfexpr e1 tmap
                    | _ => None
                    end*)
  end.
  
Fixpoint stmts_tmap' (tmap : VM.t (ftype * forient)) (ss : hfstmt_seq): option (VM.t (ftype * forient)) :=
  match ss with
  | Qnil => Some tmap
  | Qcons s ss' => match stmt_tmap' tmap s with
      | Some tmap' => stmts_tmap' tmap' ss'
      | None => None
      end
  end
  with stmt_tmap' (tmap : VM.t (ftype * forient)) (s : hfstmt) : option (VM.t (ftype * forient)) :=
  match s with
  | Sskip => Some tmap
  | Sfcnct _ _ => Some tmap
  | Sinvalid _ => Some tmap
  | Swire v t => match VM.find v tmap with
      | None => Some (VM.add v (t, Duplex) tmap)
      | _ => None
      end
  | Sreg v reg => match VM.find v tmap, type_of_hfexpr (clock reg) tmap with
      | None, Some _ => Some (VM.add v ((type reg), Duplex) tmap)
      | _, _ => None
      end
  | Snode v expr => match VM.find v tmap, type_of_hfexpr expr tmap with
                  | None, Some (exist newt _) => Some (VM.add v (make_ftype_implicit newt, Source) tmap)
                  | _, _ => None
                  end
  | Smem _ _ => None
  | Sinst _ _ => None
  | Swhen cond ss_true ss_false =>
      match type_of_hfexpr cond tmap, stmts_tmap' tmap ss_true with
      | Some (exist (Gtyp (Fuint 1)) _), Some tmap_true => stmts_tmap' tmap_true ss_false 
      | _, _ => None
      end
  end.

Fixpoint ports_tmap' (tmap : VM.t (ftype * forient)) (pp : seq hfport) : option (VM.t (ftype * forient)) :=
(* creates a tmap that contains exactly the types of the ports in pp. *)
  match pp with
  | [::] => Some tmap
  | Finput v t :: pp' => match VM.find v tmap with
          | Some _ => None
          | None => ports_tmap' (VM.add v (t, Source) tmap) pp'
          end
  | Foutput v t :: pp' => match VM.find v tmap with
          | Some _ => None
          | None => ports_tmap' (VM.add v (t, Duplex) tmap) pp'
          end
  end.    

Definition module_tmap (tmap : VM.t (ftype * forient)) (m : hfmodule) : option (VM.t (ftype * forient)) :=
  match m with
  | FInmod _ ps ss => match ports_tmap' tmap ps with
              | Some pmap => stmts_tmap' pmap ss
              | None => None
              end
  | _ => None
  end.

Fixpoint modules_tmap (tmap : VM.t (ftype * forient)) (ml : seq hfmodule) : option (VM.t (ftype * forient)) :=
  match ml with
  | nil => Some tmap
  | hd :: tl => match module_tmap tmap hd with
              | Some tmap' => modules_tmap tmap' tl
              | _ => None
              end
  end.

Definition circuit_tmap (c : hfcircuit) : option (VM.t (ftype * forient)) :=
  match c with
  | Fcircuit v ml => modules_tmap (VM.empty (ftype * forient)) ml
  end.

Definition test_ports0 := [:: Finput 0%num (Gtyp (Fuint 2)) ;
                              Foutput 1%num (Gtyp (Fuint_implicit 0));
                              Finput 2%num (Gtyp Fclock); 
                              Finput 3%num (Gtyp (Fuint 1))].
Definition pmap0 := ports_tmap' (VM.empty (ftype * forient)) test_ports0.

Definition tmap0' := match pmap0 with
                    | Some pmap => stmt_tmap' pmap (Sreg 4%num (mk_freg (Gtyp (Fuint 8)) (Eref (Eid 2%num))
                            (Rst (Eref (Eid 3%num))
                            (Econst (Fuint 8) [:: false]))))
                    | _ => None
                    end.
                    
Definition test_stmts0 := Qcons (Sfcnct (Eid 1%num) (Eref (Eid 0%num))) 
                         (Qcons (Sreg 4%num (mk_freg (Gtyp (Fuint 8)) (Eref (Eid 2%num))
                            (Rst (Eref (Eid 3%num))
                            (Econst (Fuint 8) [:: false])))) 
                         (Qcons (Sfcnct (Eid 4%num) (Eref (Eid 0%num))) Qnil)). 
Definition test_mod0 := FInmod 5%num test_ports0 test_stmts0.
Definition test_cir0 := Fcircuit 5%num [test_mod0].
Definition tmap0 := circuit_tmap test_cir0.


(*Fixpoint list_gtypref (v : ProdVar.t) (ft : ftype) (ori : bool) : seq (ProdVar.t * fgtyp * bool) :=
  match ft with
  | Gtyp gt => [(v, gt, ori)]
  | Atyp atyp n => list_gtypref (v.1, N.add v.2 1%num) atyp ori
  | Btyp ff => list_gtypref_ff v ff ori
  end
with list_gtypref_ff (v : ProdVar.t) (ff : ffield) (ori : bool) : seq (ProdVar.t * fgtyp * bool) :=
  match ff with
  | Fnil => [::]
  | Fflips _ fl ft ff' => match fl with
                        | Nflip => list_gtypref (v.1, N.add v.2 1%num) ft ori ++ list_gtypref_ff (v.1, N.add v.2 (N.of_nat (num_ref ft))) ff' ori
                        | Flipped => list_gtypref (v.1, N.add v.2 1%num) ft (~~ori) ++ list_gtypref_ff (v.1, N.add v.2 (N.of_nat (num_ref ft))) ff' ori
                        end
  end.

*)
HB.about finType.
HB.howto finType.
HB.howto eqType.
HB.about isCountable.Build.
HB.about hasDecEq.Build.
HB.about isFinite.Build.

Section finProdVar.

Variable (c : hfcircuit).

Definition pv_is_fintype (pv : ProdVar.t) (c : hfcircuit) : Prop :=
  match circuit_tmap c with
  | Some tmap =>
    match VM.find pv.1 tmap with
    | Some (ft, _) => ((N.to_nat pv.1) <? (fcomponent_amount c)) /\ ((N.to_nat pv.2) <? (size_of_ftype ft))
    | None => False
    end
  | _ => False
  end.

Definition finProdVar : Type := {pv : ProdVar.t | pv_is_fintype pv c}.

Lemma pv_is_fintypeP pv : pv_is_fintype pv c.
Proof.
  (* 在这里进行你需要的证明，可能涉及到对 circuit_tmap 和 type_of_ref 的分析 *)
  (* 你需要提供 c 的具体信息，以及满足 pv_is_fintype 的条件 *)
  Admitted.

Definition ProdVar2finProdVar (pv : ProdVar.t) : finProdVar :=
  exist _ pv (pv_is_fintypeP pv).

Definition finProdVar2ProdVar (fin_v : finProdVar) : ProdVar.t :=
  proj1_sig fin_v.

Fixpoint list_finProdVar (v : N) (offset : nat) (t : ftype) (flag : nat) : list (finProdVar * nat) * nat * nat :=
  match t with 
  | Gtyp (Fuint_implicit _) 
  | Gtyp (Fsint_implicit _) => ([(ProdVar2finProdVar (v, N.of_nat offset), flag)], flag+1, offset+1)
  | Gtyp _ => (nil, flag, offset+1)
  | Atyp atyp _ => list_finProdVar v offset atyp flag
  | Btyp ff => list_finProdVar_f v offset ff flag
  end
with list_finProdVar_f (v : N) (offset : nat) (ff : ffield) (flag : nat) : list (finProdVar * nat) * nat * nat :=
  match ff with
  | Fnil => (nil, flag, offset)
  | Fflips _ _ t fs => let '(ls, flag0, offset0) := list_finProdVar v offset t flag in 
                       let '(ls0, flag1, offset1) := list_finProdVar_f v offset0 fs flag0 in
                       (ls ++ ls0, flag1, offset1)
  end.

Definition list_finProdVar_circuit : list (finProdVar * nat) * nat :=
  (* number implicit ground types by nat *)
  match circuit_tmap c with 
  | Some tmap => List.fold_left (fun '(ls, flag) '(key, (ft, _)) => 
                  let '(ls0, flag0, _) := list_finProdVar key 0 ft flag in (ls ++ ls0, flag0)
  ) (VM.elements tmap) (nil, 1)
  | _ => (nil, 0)
  end.

(*Fixpoint list_finProdVar_pp (pp : seq hfport) (flag : nat) : list (finProdVar * nat) * nat :=
  match pp with
  | [::] => (nil, flag)
  | Foutput v t :: pp' 
  | Finput v t :: pp' => let '(ls, flag0, _) := list_finProdVar v 0 t 0 in
                         let '(ls0, flag1) := list_finProdVar_pp pp' flag0 in (ls ++ ls0, flag1)
  end.    

Fixpoint list_finProdVar_s (s : hfstmt) (flag : nat) (tmap : VM.t (ftype * forient)) : list (finProdVar * nat) * nat :=
  match s with
  | Swire v t => list_finProdVar v 0 t flag
  | Sreg v reg => list_finProdVar v 0 (type reg) flag
  | Snode v e => match type_of_hfexpr e tmap with
                | Some t => list_finProdVar v 0 t flag
  | Swhen _ ss_true ss_false =>
  | _ => (nil, flag)
  end
with list_finProdVar_ss (ss : hfstmt_seq) (flag : nat) (tmap : VM.t (ftype * forient)) : list (finProdVar * nat) * nat :=
  match ss with
  | Qnil => (nil, flag)
  | Qcons s st => let '(ls, flag0) := list_finProdVar_s flag tmap in
                  let '(ls0, flag1) := list_finProdVar_ss ss flag0 tmap in (ls ++ ls0, flag1)
  end.

Definition list_finProdVar_m (m : hfmodule) (flag : nat) : list (finProdVar * nat) * nat :=
  match m with
  | FInmod _ pp ss => let '(ls, flag0) := list_finProdVar_pp pp flag in
                      let '(ls0, flag1) := list_finProdVar_ss ss flag0 in (ls ++ ls0, flag1)
  | _ => (nil, flag)
  end.

Fixpoint list_finProdVar_ml (ml : seq hfmodule) (flag : nat) : list (finProdVar * nat) * nat :=
  match ml with
  | nil => (nil, flag)
  | hd :: tl => let '(ls, flag0) := list_finProdVar_m hd flag in
                let '(ls0, flag1) := list_finProdVar_ml tl flag0 in (ls ++ ls0, flag1)
  end.

Definition list_finProdVar_circuit (c : hfcircuit) : list (finProdVar * nat) * nat :=
  (* number implicit ground types by nat *)
  match c with 
  | Fcircuit _ ml => list_finProdVar_ml ml 0
  end.*)

Definition finProdVar_pickle (v : finProdVar) : nat := 
  let '(fin_list, _) := list_finProdVar_circuit in
  match List.find (fun '(pv, _) => (finProdVar2ProdVar pv) == (finProdVar2ProdVar v)) fin_list with
  | Some (_, n) => n 
  | _ => 0
  end.

Definition finProdVar_unpickle (n : nat) : option finProdVar := 
  let '(fin_list, _) := list_finProdVar_circuit in
  match List.find (fun '(_, n') => n == n') fin_list with
  | Some (pv, n) => Some pv 
  | _ => None
  end.

(*Parameter finProdVar_pickle : forall (x : finProdVar), nat.
Parameter finProdVar_unpickle : forall (n : nat), option finProdVar.*)
Lemma finProdVar_pickleK : pcancel finProdVar_pickle finProdVar_unpickle.
Admitted.
HB.instance Definition _ := isCountable.Build finProdVar finProdVar_pickleK.

Definition finProdVar_enum_subdef : seq finProdVar := 
  let '(fin_list, _) := list_finProdVar_circuit in map fst fin_list.
Lemma finProdVar_enumP_subdef : Finite.axiom finProdVar_enum_subdef.
Admitted.
HB.instance Definition _ := isFinite.Build finProdVar finProdVar_enumP_subdef.

Definition a : ProdVar.t := (N0, N0).

From mathcomp.tarjan Require Import kosaraju.

Definition r (x y : finProdVar) : bool :=
  false.
Definition res_r := kosaraju r. 

End finProdVar.


Section PVMLemmas.

  Lemma find_some_map {elt elt' : Type} {f : elt -> elt'} {m : PVM.t elt} {x : PVM.key} {e : elt} :
    PVM.find x m = Some e ->
    PVM.find x (PVM.map f m) = Some (f e).
  Proof.
  (*   move=> H. rewrite F.map_o. rewrite /option_map. rewrite H. reflexivity. *)
  (* Qed. *)
  Admitted.
  
  Lemma find_none_map {elt elt' : Type} {f : elt -> elt'} {m : PVM.t elt} {x : PVM.key} :
    PVM.find x m = None ->
    PVM.find x (PVM.map f m) = None.
  Proof.
  (*   move=> H. rewrite F.map_o. rewrite /option_map. rewrite H. reflexivity. *)
  (* Qed. *)
  Admitted.

  Lemma find_map_some {elt elt' : Type} {f : elt -> elt'} {m : PVM.t elt} {x : PVM.key} {e : elt'} :
    PVM.find x (PVM.map f m) = Some e ->
    exists a, e = f a /\ PVM.find x m = Some a.
  Proof.
  (*   move=> H. move: (PVM.find_2 H) => {H} H. case: (F.map_mapsto_iff m x e f) => Hf _. *)
  (*   move: (Hf H) => {H Hf} [] => a [Hea Hxa]. exists a. split. *)
  (*   - assumption. *)
  (*   - apply: PVM.find_1. assumption. *)
  (* Qed. *)
  Admitted.

  Lemma find_map_none {elt elt' : Type} {f : elt -> elt'} {m : PVM.t elt} {x : PVM.key} :
    PVM.find x (PVM.map f m) = None ->
    PVM.find x m = None.
  Proof.
  (*   rewrite F.map_o. rewrite /option_map. case: (PVM.find x m). *)
  (*   - discriminate. *)
  (*   - reflexivity. *)
  (* Qed. *)
  Admitted.

  Lemma find_add_eq {elt : Type} {m : PVM.t elt} {x : PVM.key} {e : elt} :
    PVM.find x (PVM.add x e m) = Some e.
    (* PVM.E.eq x y -> PVM.find x (PVM.add y e m) = Some e. *)
  Proof.
  (*   move=> Hxy. apply: F.add_eq_o. apply: PVM.E.eq_sym. exact: Hxy. *)
  (* Qed. *)
  Admitted.

  Lemma find_add_neq {elt : Type} {m : PVM.t elt} {x y : PVM.key} {e : elt} :
    x <> y -> PVM.find x (PVM.add y e m) = PVM.find x m.
    (* ~(PVM.E.eq x y) -> PVM.find x (PVM.add y e m) = PVM.find x m. *)
  Proof.
  (*   move=> Hne. apply: F.add_neq_o. move=> Heq; apply: Hne; apply: PVM.E.eq_sym. *)
  (*   exact: Heq. *)
  (* Qed. *)
  Admitted.

  Lemma find_some_in {elt : Type} {m : PVM.t elt} x e : PVM.find x m = Some e -> PVM.In x m.
  Proof.
  (*   move=> H; exists e. exact: (find_some_mapsto H). *)
  (* Qed. *)
  Admitted.
  
End PVMLemmas.
