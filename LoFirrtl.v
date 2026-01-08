From Coq Require Import FMaps ZArith (*FunInd FMapAVL OrderedType*).
From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
From Solver Require Import Env.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope firrtl with firrtl.

Section LoFirrtl.

  (****** Syntax ******)

  (****** Expressions ******)

  Inductive ucast : Set :=
  | AsUInt | AsSInt | AsClock | AsAsync .

  Definition ucast_eqn (x y : ucast) : bool :=
  match x, y with
  | AsUInt, AsUInt | AsSInt, AsSInt | AsClock, AsClock
  | AsAsync, AsAsync => true
  | _, _ => false
  end.

  Lemma ucast_eqP : Equality.axiom ucast_eqn.
  Proof.
  unfold Equality.axiom, ucast_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        by apply ReflectT ; reflexivity.
  Qed.

  HB.instance Definition _ := hasDecEq.Build ucast ucast_eqP.
Compute (AsUInt == AsUInt).

  Inductive eunop : Set :=
  | Upad : nat -> eunop
  | Ushl : nat -> eunop
  | Ushr : nat -> eunop
  | Ucvt
  | Uneg
  | Unot
  | Uandr
  | Uorr
  | Uxorr
  | Uextr : nat -> nat -> eunop
  | Uhead : nat -> eunop
  | Utail : nat -> eunop.

  Definition eunop_eqn (x y : eunop) : bool :=
  match x, y with
  | Upad n, Upad m | Ushl n, Ushl m | Ushr n, Ushr m | Uhead n, Uhead m | Utail n, Utail m =>
        n == m
  | Ucvt, Ucvt | Uneg, Uneg | Unot, Unot | Uandr, Uandr | Uorr, Uorr | Uxorr, Uxorr => true
  | Uextr n n0, Uextr m m0 => (n == m) && (n0 == m0)
  | _, _ => false
  end.

  Lemma eunop_eqP : Equality.axiom eunop_eqn.
  Proof.
  unfold Equality.axiom, eunop_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        try (by apply ReflectT ; reflexivity).
  1,2,3,5,6: destruct (n == n0) eqn: Hn ; move /eqP : Hn => Hn ;
        first (by rewrite Hn ; apply ReflectT ; reflexivity) ;
        last  (by apply ReflectF ; contradict Hn ; injection Hn ; done).
  destruct (n == n1) eqn: Hn ; move /eqP : Hn => Hn ;
        last (by apply ReflectF ; contradict Hn ; injection Hn ; done).
  rewrite Hn andTb.
  destruct (n0 == n2) eqn: Hn0 ; move /eqP : Hn0 => Hn0 ;
        last (by apply ReflectF ; contradict Hn0 ; injection Hn0 ; done).
  rewrite Hn0 ; apply ReflectT ; reflexivity.
  Qed.

  HB.instance Definition _ := hasDecEq.Build eunop eunop_eqP.
Compute (Upad 1 == Upad 2).

  Inductive bcmp : Set :=
  | Blt | Bleq | Bgt | Bgeq | Beq | Bneq.

  Definition bcmp_eqn (x y : bcmp) : bool :=
  match x, y with
  | Blt, Blt | Bleq, Bleq | Bgt, Bgt | Bgeq, Bgeq | Beq, Beq | Bneq, Bneq => true
  | _, _ => false
  end.

  Lemma bcmp_eqP : Equality.axiom bcmp_eqn.
  Proof.
  unfold Equality.axiom, bcmp_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        by apply ReflectT ; reflexivity.
  Qed.

  HB.instance Definition _ := hasDecEq.Build bcmp bcmp_eqP.
  Compute (Blt == Bleq).

  Inductive ebinop : Set :=
  | Badd
  | Bsub
  | Bmul
  | Bdiv
  | Brem
  | Bcomp: bcmp -> ebinop
  | Bdshl
  | Bdshr
  | Band
  | Bor
  | Bxor
  | Bcat .

  Definition ebinop_eqn (x y : ebinop) : bool :=
  match x, y with
  | Badd, Badd | Bsub, Bsub | Bmul, Bmul | Bdiv, Bdiv | Brem, Brem
  | Bdshl, Bdshl | Bdshr, Bdshr | Band, Band | Bor, Bor | Bxor, Bxor | Bcat, Bcat => true
  | Bcomp b, Bcomp c => b == c
  | _, _ => false
  end.

  Lemma ebinop_eqP : Equality.axiom ebinop_eqn.
  Proof.
  unfold Equality.axiom, ebinop_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        try (by apply ReflectT ; reflexivity).
  destruct (b == b0) eqn: Hb ; move /eqP : Hb => Hb ;
        first (by apply ReflectT ; rewrite Hb ; reflexivity) ;
        last  (by apply ReflectF ; injection ; done).
  Qed.

  HB.instance Definition _ := hasDecEq.Build ebinop ebinop_eqP.
Compute (Badd == Bsub).

  Variable var : eqType.

  Inductive fexpr : Type :=
  | Econst : fgtyp -> bitseq -> fexpr
  | Ecast : ucast -> fexpr -> fexpr
  | Eprim_unop : eunop -> fexpr -> fexpr
  | Eprim_binop : ebinop -> fexpr -> fexpr -> fexpr
  | Emux : fexpr -> fexpr -> fexpr -> fexpr
  | Eref : var -> fexpr
  .

  Fixpoint fexpr_eqn (x y : fexpr) : bool :=
  match x, y with
  | Econst tx sx, Econst ty sy => (tx == ty) && (sx == sy)
  | Ecast  cx ex, Ecast  cy ey => (cx == cy) && fexpr_eqn ex ey
  | Eprim_unop ux ex, Eprim_unop uy ey => (ux == uy) && fexpr_eqn ex ey
  | Eprim_binop ox ex fx, Eprim_binop oy ey fy => (ox == oy) && fexpr_eqn ex ey && fexpr_eqn fx fy
  | Emux ex fx gx, Emux ey fy gy => fexpr_eqn ex ey && fexpr_eqn fx fy && fexpr_eqn gx gy
  | Eref vx, Eref vy => vx == vy
  | _, _ => false
  end.

  Lemma fexpr_eqP : Equality.axiom fexpr_eqn.
  Proof.
  unfold Equality.axiom, fexpr_eqn.
  induction x, y ;
        try (by apply ReflectF ; discriminate).
  * destruct (f == f0) eqn: Hf ; move /eqP : Hf => Hf ;
          last by (apply ReflectF ; contradict Hf ; injection Hf ; done).
    rewrite Hf andTb.
    destruct (b == b0) eqn: Hb ; move /eqP : Hb => Hb ;
          last by (apply ReflectF ; contradict Hb ; injection Hb ; done).
    rewrite Hb ; apply ReflectT ; reflexivity.
  * fold fexpr_eqn in IHx ; fold fexpr_eqn.
    destruct (u == u0) eqn: Hu ; move /eqP : Hu => Hu ;
          last by (apply ReflectF ; contradict Hu ; injection Hu ; done).
    rewrite Hu andTb.
    specialize (IHx y) ; apply reflect_iff in IHx.
    destruct (fexpr_eqn x y) eqn: Hx.
    + apply ReflectT.
      destruct IHx as [_ IHx] ; specialize (IHx Logic.eq_refl).
      rewrite IHx ; reflexivity.
    + apply ReflectF ; injection ; intro.
      destruct IHx as [IHx _].
      apply IHx in H0 ; done.
  * fold fexpr_eqn in IHx ; fold fexpr_eqn.
    destruct (e == e0) eqn: He ; move /eqP : He => He ;
          last by (apply ReflectF ; contradict He ; injection He ; done).
    rewrite He andTb.
    specialize (IHx y) ; apply reflect_iff in IHx.
    destruct (fexpr_eqn x y).
    + apply ReflectT.
      destruct IHx as [_ IHx] ; specialize (IHx Logic.eq_refl).
      rewrite IHx ; reflexivity.
    + apply ReflectF ; injection ; intro.
      destruct IHx as [IHx _].
      apply IHx in H0 ; done.
  * fold fexpr_eqn in IHx1 ; fold fexpr_eqn in IHx2 ; fold fexpr_eqn.
    destruct (e == e0) eqn: He ; move /eqP : He => He ;
          last by (apply ReflectF ; contradict He ; injection He ; done).
    rewrite He andTb.
    specialize (IHx1 y1) ; apply reflect_iff in IHx1.
    destruct (fexpr_eqn x1 y1) ;
          last by (apply ReflectF ; injection ; intros _ H0 ;
                   destruct IHx1 as [IHx1 _] ;
                   apply IHx1 in H0 ; done).
    destruct IHx1 as [_ IHx1] ; specialize (IHx1 Logic.eq_refl).
    rewrite IHx1 andTb.
    specialize (IHx2 y2) ; apply reflect_iff in IHx2.
    destruct (fexpr_eqn x2 y2) ;
          last by (apply ReflectF ; injection ; intros H0 ;
                   destruct IHx2 as [IHx2 _] ;
                   apply IHx2 in H0 ; done).
    destruct IHx2 as [_ IHx2] ; specialize (IHx2 Logic.eq_refl).
    rewrite IHx2.
    apply ReflectT ; reflexivity.
  * fold fexpr_eqn in IHx1 ; fold fexpr_eqn in IHx2 ; fold fexpr_eqn in IHx3 ; fold fexpr_eqn.
    specialize (IHx1 y1) ; apply reflect_iff in IHx1.
    destruct (fexpr_eqn x1 y1) ;
          last by (apply ReflectF ; injection ; intros _ _ H0 ;
                   destruct IHx1 as [IHx1 _] ;
                   apply IHx1 in H0 ; done).
    destruct IHx1 as [_ IHx1] ; specialize (IHx1 Logic.eq_refl).
    rewrite IHx1 andTb.
    specialize (IHx2 y2) ; apply reflect_iff in IHx2.
    destruct (fexpr_eqn x2 y2) ;
          last by (apply ReflectF ; injection ; intros _ H0 ;
                   destruct IHx2 as [IHx2 _] ;
                   apply IHx2 in H0 ; done).
    destruct IHx2 as [_ IHx2] ; specialize (IHx2 Logic.eq_refl).
    rewrite IHx2 andTb.
    specialize (IHx3 y3) ; apply reflect_iff in IHx3.
    destruct (fexpr_eqn x3 y3) ;
          last by (apply ReflectF ; injection ; intros H0 ;
                   destruct IHx3 as [IHx3 _] ;
                   apply IHx3 in H0 ; done).
    destruct IHx3 as [_ IHx3] ; specialize (IHx3 Logic.eq_refl).
    rewrite IHx3.
    apply ReflectT ; reflexivity.
  * destruct (s == s0) eqn: Hs ; move /eqP : Hs => Hs ;
          last by (apply ReflectF ; contradict Hs ; injection Hs ; done).
    rewrite Hs.
    apply ReflectT ; reflexivity.
  Qed.

  HB.instance Definition _ := hasDecEq.Build fexpr fexpr_eqP.
Compute (Econst (Fuint 1) [true] == Econst (Fuint 1) [false]).

  (****** Statements ******)
  Inductive ruw : Set :=
  | old | new | undefined.

  Definition ruw_eqn (x y : ruw) : bool :=
  match x, y with
  | old, old | new, new | undefined, undefined => true
  | _, _ => false
  end.

  Lemma ruw_eqP : Equality.axiom ruw_eqn.
  Proof.
  unfold Equality.axiom, ruw_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        by apply ReflectT ; reflexivity.
  Qed.

  HB.instance Definition _ := hasDecEq.Build ruw ruw_eqP.
  
  Record freader_port : Type :=
    mk_freader_port
      {
        addr : var;
        data : var;
        en : var;
        clk : var
      }.

Record fwriter_port : Type :=
    mk_fwriter_port
      {
        addr0 : var;
        data0 : var;
        en0 : var;
        clk0 : var;
        mask : var
      }.

  Record fmem : Type :=
    mk_fmem
      {
        mid : var;
        data_type : fgtyp;
        depth : nat;
        reader : seq freader_port;
        writer : seq fwriter_port;
        read_latency : nat;
        write_latency : nat;
        read_write : ruw
      }.

  Inductive rst : Type :=
  | NRst : rst
  | Rst : fexpr -> fexpr -> rst.
  
  Record freg : Type :=
    mk_freg
      {
        rid : var;
        type : fgtyp;
        clock : var;
        reset : rst
      }.

  Inductive fport : Type :=
  | Finput : var -> fgtyp -> fport
  | Foutput : var -> fgtyp -> fport
  .

  Record finst : Type :=
    mk_finst
      {
        iid : var;
        imid : var;
        iports : seq fport
      }.

  Inductive fstmt : Type :=
  | Sskip
  | Swire : var -> fgtyp -> fstmt
  | Sreg : freg -> fstmt
  | Smem : fmem -> fstmt
  | Sinst : finst -> fstmt
  | Snode : var -> fexpr -> fstmt
  | Sfcnct : var -> fexpr -> fstmt
  | Sinvalid : var -> fstmt
  | Swhen : fexpr -> fstmt -> fstmt -> fstmt
  | Sstop : fexpr -> fexpr -> nat -> fstmt
  .

  Inductive fmodule : Type :=
  | FInmod : var -> seq fport -> seq fstmt -> fmodule
  | FExmod : var -> seq fport -> seq fstmt -> fmodule
  .

  Inductive fcircuit : Type := Fcircuit : var -> seq fmodule -> fcircuit.

End LoFirrtl.

