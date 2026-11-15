From Coq Require Import FMaps ZArith FunInd FMapAVL OrderedType.
From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
From firrtl Require Import Env LoFirrtl HiEnv.
From Lib Require Import SsrOrder Var.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* LowerMatches: lower match statements to when statements.

   Corresponds to CIRCT's LowerMatches.cpp pass:

     match input, cases
       case v0: s0
       case v1: s1
       ...
       case vn-1: sn-1

   is lowered into a right-nested chain of when statements:

     when is-tag(input, 0):
       s0[v0 := subtag(input, 0)]
     else:
       when is-tag(input, 1):
         s1[v1 := subtag(input, 1)]
       else:
         ...
           sn-1[vn-1 := subtag(input, n-1)]

   The last case is not guarded by a when (enum tags are exhaustive
   and mutually exclusive), and its body is spliced into the innermost
   else branch.  An empty match is simply erased.

   TODO:
   - extend the syntax with match statements / is-tag / subtag
     expressions (or define them locally in this file),
   - define substitution of a case variable by subtag(input, i),
   - define the lowering function on statements / statement
     sequences / modules / circuits,
   - state and prove correctness w.r.t. Semantics. *)

(****** Aggregate type ******)

Section Ftype.

(*Variable var : eqType.*)

Inductive fflip : Type := Flipped | Nflip.

(* flipped direction type equality is decidable *)
Lemma fflip_eq_dec (x y : fflip) : {x = y} + {x <> y}.
  Proof. decide equality. Qed.

(* equality of fflip is decidable *)
Definition fflip_eqn (x y : fflip) : bool :=
  match x, y with
  | Flipped, Flipped => true
  | Nflip, Nflip => true
  | _, _ => false
  end.
Lemma fflip_eqP : Equality.axiom fflip_eqn.
Proof.
rewrite /Equality.axiom /fflip_eqn.
destruct x, y ; try (apply ReflectT ; reflexivity) ;
apply ReflectF ; discriminate.
Qed.

HB.instance Definition _ := hasDecEq.Build fflip fflip_eqP.

(*Definition var : Set := N.*)

Inductive ftype : Type :=
| Gtyp : fgtyp -> ftype
| Atyp : ftype -> nat -> ftype
| Btyp : ffield -> ftype
| Etyp : fenum -> ftype 

with ffield : Type :=
| Fnil : ffield
| Fflips : var -> fflip -> ftype -> ffield -> ffield

with fenum : Type :=
| Fenil : fenum
| Fesome : var -> ftype -> fenum -> fenum 
| Fenone : var -> fenum -> fenum 
.

Scheme ftype_ffield_ind := Induction for ftype Sort Prop
  with ffield_ftype_ind := Induction for ffield Sort Prop
  with fenum_ffield_ind := Induction for fenum Sort Prop.

Fixpoint ftype_eqn (x y : ftype) : bool :=
  match x, y with
  | Gtyp tx, Gtyp ty => fgtyp_eqn tx ty
  | Atyp tx nx, Atyp ty ny => ftype_eqn tx ty && (nx == ny)
  | Btyp fx, Btyp fy => ffield_eqn fx fy
  | Etyp ex, Etyp ey => fenum_eqn ex ey
  | _, _ => false
  end
with ffield_eqn (f1 f2 : ffield) : bool :=
  match f1, f2 with
  | Fnil, Fnil => true
  | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2
    => (v1 == v2) && ftype_eqn t1 t2 && ffield_eqn fs1 fs2
  | Fflips v1 Flipped t1 fs1, Fflips v2 Flipped t2 fs2
    => (v1 == v2) && ftype_eqn t1 t2 && ffield_eqn fs1 fs2
  | _, _ => false
  end
with fenum_eqn (e1 e2 : fenum) : bool :=
  match e1, e2 with
  | Fenil, Fenil => true
  | Fesome v1 t1 fs1, Fesome v2 t2 fs2
    => (v1 == v2) && ftype_eqn t1 t2 && fenum_eqn fs1 fs2
  | Fenone v1 fs1, Fenone v2 fs2
    => (v1 == v2) && fenum_eqn fs1 fs2
  | _, _ => false
  end.

Notation "x =? y" := (ftype_eqn x y).

Lemma ftype_eq_dec (x y : ftype) : {x = y} + {x <> y}
with ffield_eq_dec (fx fy : ffield) : {fx = fy} + {fx <> fy}
with fenum_eq_dec (ex ey : fenum) : {ex = ey} + {ex <> ey}.
Proof.
* decide equality; [apply fgtyp_eq_dec | apply Nat.eq_dec].
* decide equality; auto using fflip_eq_dec, N.eq_dec.
* decide equality; auto using N.eq_dec.
Qed.

Lemma ftype_eqn_refl (x : ftype) : x =? x
with ffield_eqn_refl (fx : ffield) : ffield_eqn fx fx
with fenum_eqn_refl (ex : fenum) : fenum_eqn ex ex.
Proof.
* clear ftype_eqn_refl.
  induction x ; simpl ; try done.
  + apply fgtyp_eqn_refl.
  + rewrite IHx andTb eq_refl //.
* clear ffield_eqn_refl.
  induction fx ; simpl ; try done.
  destruct f.
  + rewrite IHfx andbT (ftype_eqn_refl f0) eq_refl //.
  + rewrite IHfx andbT (ftype_eqn_refl f0) andbT eq_refl //.
* clear fenum_eqn_refl.
  induction ex ; simpl ; try done.
  + rewrite IHex andbT (ftype_eqn_refl f) eq_refl //.
  + rewrite IHex andbT eq_refl //.
Qed.

Lemma ftype_eqn_eq (x y : ftype) : x =? y <-> x = y
with ffield_eqn_eq (fx fy : ffield) : ffield_eqn fx fy <-> fx = fy
with fenum_eqn_eq (ex ey : fenum) : fenum_eqn ex ey <-> ex = ey.
Proof.
* clear ftype_eqn_eq.
  split ; last by (intro ; rewrite H ; apply ftype_eqn_refl).
  revert x y ; induction x, y ; simpl ; try done.
  + generalize (fgtyp_eq_dec f f0) ; intro.
    destruct H ; first by (rewrite e ; intro ; reflexivity).
    intro ; apply fgtyp_eqn_eq in H ; contradiction.
  + intro ; move /andP : H => [H /eqP H0].
    apply IHx in H.
    rewrite H H0 ; by reflexivity.
  + intro ; apply ffield_eqn_eq in H.
    rewrite H ; by reflexivity.
  + intro ; apply fenum_eqn_eq in H.
    rewrite H ; by reflexivity.
* clear ffield_eqn_eq.
  split ; last by (intro ; rewrite H ; apply ffield_eqn_refl).
  revert fx fy ; induction fx, fy ; simpl ; try done.
  + destruct f ; done.
  + destruct f, f1 ; try done.
    1,2: destruct (v == v0) eqn: Hv ; last by rewrite andFb ; done.
    1,2: move /eqP : Hv => Hv ; rewrite andTb Hv.
    1,2: destruct (f0 =? f2) eqn: Hf ; last by rewrite andFb ; done.
    1,2: apply ftype_eqn_eq in Hf ; rewrite andTb Hf.
    1,2: intro ; apply IHfx in H.
    1,2: rewrite H //.
* clear fenum_eqn_eq.
  split ; last by move=> -> ; apply fenum_eqn_refl.
  revert ex ey ; induction ex, ey ; simpl ; try done.
  + intro H.
    destruct (v == v0) eqn: Hv ; last by rewrite andFb in H.
    move /eqP : Hv => Hv ; rewrite andTb in H.
    destruct (f =? f0) eqn: Hf ; last by rewrite andFb in H.
    apply ftype_eqn_eq in Hf. rewrite andTb in H.
    apply IHex in H.
    rewrite H Hf Hv ; reflexivity.
  + intro H.
    destruct (v == v0) eqn: Hv ; last by rewrite andFb in H.
    move /eqP : Hv => Hv ; rewrite andTb in H.
    apply IHex in H.
    rewrite H Hv ; reflexivity.
Qed.

Lemma ffield_eqP : Equality.axiom ffield_eqn.
Proof.
  (*rewrite /Equality.axiom.
  intros fx fy.
  destruct (ffield_eq_dec fx fy) as [e | n].
  * assert (ffield_eqn fx fy) by (apply ffield_eqn_eq, e).
    rewrite H ; apply ReflectT; done.
  * assert (~ ffield_eqn fx fy) by (contradict n ; apply ffield_eqn_eq, n).
    apply ReflectF ; assumption.
Qed.*)
Admitted.

HB.instance Definition _ := hasDecEq.Build ffield ffield_eqP.

Lemma fenum_eqP : Equality.axiom fenum_eqn.
Proof.
  (*rewrite /Equality.axiom.
  intros ex ey.
  destruct (fenum_eq_dec ex ey) as [e | n].
  * assert (fenum_eqn ex ey) by (apply fenum_eqn_eq, e).
    rewrite H ; apply ReflectT; done.
  * assert (~ fenum_eqn ex ey) by (contradict n ; apply fenum_eqn_eq, n).
    apply ReflectF ; assumption.
Qed.*)
Admitted.

HB.instance Definition _ := hasDecEq.Build fenum fenum_eqP.

Lemma ftype_eqP : Equality.axiom ftype_eqn.
Proof.
  (*rewrite /Equality.axiom.
  intros x y.
  destruct (ftype_eq_dec x y) as [e | n].
  * assert (x =? y) by (apply ftype_eqn_eq, e).
    rewrite H ; apply ReflectT ; reflexivity.
  * assert (~ (x =? y)) by (contradict n ; apply ftype_eqn_eq, n).
    apply ReflectF ; assumption.
Qed.*)
Admitted.

HB.instance Definition _ := hasDecEq.Build ftype ftype_eqP.

End Ftype.

Section HiFirrtl.

  (****** Syntax ******)

  (****** Expressions ******)

  Variable var : eqType.

  Inductive sign := Unsigned | Signed.

  Inductive hfexpr : Type :=
  | Econst : fgtyp -> bitseq -> hfexpr
  | Ecast : ucast -> hfexpr -> hfexpr
  | Eprim_unop : eunop -> hfexpr -> hfexpr
  | Eprim_binop : ebinop -> hfexpr -> hfexpr -> hfexpr
  | Emux : hfexpr -> hfexpr -> hfexpr -> hfexpr
  | Eref : href -> hfexpr
  (* HiFIRRTL only, enum-related primitives (LowerMatches).
     The variant is identified by NAME (not index), matching CIRCT:
       %0 = firrtl.istag  %x some   : !firrtl.enum<...> -> !firrtl.uint<1>
       %1 = firrtl.subtag %x[some]  : !firrtl.enum<...> -> payload type of 'some' *)
  | Eistag : hfexpr -> var -> hfexpr  (* istag e v: tag of e equals variant v, UInt<1> *)
  | Esubtag : hfexpr -> var -> hfexpr (* subtag e v: view e as the payload of variant v *)
  with href : Type :=
  | Eid : var -> href
  | Esubfield : href -> var -> href (* HiFirrtl *)
  | Esubindex : href -> nat -> href (* HiFirrtl *)
  | Esubaccess : href -> hfexpr -> href (* HiFirrtl *)
  .

  (*Scheme hfstmt_seq_hfstmt_ind := Induction for hfstmt_seq Sort Prop
   with hfstmt_hfstmt_seq_ind := Induction for hfstmt Sort Prop.

  (** equality of hfexpr and href are decidable *)

Lemma hfexpr_eqP : reflect equality hfexpr_eqn
with href_eqP : reflect equality href_eqn.
Proof.
  * clear hfexpr_eqP.
    induction x, y ; simpl ;
          try (apply ReflectF ; discriminate).
    + destruct (t == t0) eqn: Ht ; move /eqP : Ht => Ht ;
            last by (apply ReflectF ; injection ; done).
      rewrite Ht andTb.
      destruct (b == b0) eqn: Hb ; move /eqP : Hb => Hb ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hb.
      apply ReflectT ; reflexivity.
    + destruct (u == u0) eqn: Hu ; move /eqP : Hu => Hu ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hu andTb.
      specialize (IHx y).
      apply reflect_iff in IHx.
      destruct (hfexpr_eqn x y) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      apply ReflectT ; reflexivity.
    + destruct (u == u0) eqn: Hu ; move /eqP : Hu => Hu ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hu andTb.
      specialize (IHx y).
      apply reflect_iff in IHx.
      destruct (hfexpr_eqn x y) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      apply ReflectT ; reflexivity.
    + destruct (b == b0) eqn: Hb ; move /eqP : Hb => Hb ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hb andTb.
      specialize (IHx y).
      apply reflect_iff in IHx.
      destruct (hfexpr_eqn x y) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      andTb.
      specialize (IHf y0).
      apply reflect_iff in IHf.
      destruct (hfexpr_eqn f y0) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHf as [IHf _] ; apply IHf in H0 ; done).
      destruct IHf as [_ IHf] ; rewrite IHf //.
      apply ReflectT ; reflexivity.
    + specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (hfexpr_eqn x y) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx // andTb.
      specialize (IHf y0) ; apply reflect_iff in IHf.
      destruct (hfexpr_eqn f y0) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHf as [IHf _] ; apply IHf in H0 ; done).
      destruct IHf as [_ IHf] ; rewrite IHf // andTb.
      specialize (IHg y1) ; apply reflect_iff in IHg.
      destruct (hfexpr_eqn g y1) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHg as [IHg _] ; apply IHg in H0 ; done).
      destruct IHg as [_ IHg] ; rewrite IHg //.
      apply ReflectT ; reflexivity.
    + specialize (href_eqP h h0) ; apply reflect_iff in href_eqP.
      destruct (href_eqn h h0) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct href_eqP as [href_eqP _] ; apply href_eqP in H0 ; done).
      destruct href_eqP as [_ href_eqP] ; rewrite href_eqP //.
      apply ReflectT ; reflexivity.
    + specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (hfexpr_eqn x y) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx // andTb.
      destruct (s == s0) eqn: Hv ; move /eqP : Hv => Hv ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hv.
      apply ReflectT ; reflexivity.
    + specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (hfexpr_eqn x y) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx // andTb.
      destruct (s == s0) eqn: Hv ; move /eqP : Hv => Hv ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hv.
      apply ReflectT ; reflexivity.
  * clear href_eqP.
    induction x, y ; simpl ;
          try (apply ReflectF ; discriminate).
    + destruct (s == s0) eqn: Hs ; move /eqP : Hs => Hs ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hs.
      apply ReflectT ; reflexivity.
    + specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (href_eqn x y) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      destruct (s == s0) eqn: Hv ; move /eqP : Hv => Hv ;
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
  match x, y with
  | Econst tx bx, Econst ty by_ => (tx == ty) && (bx == by_)
  | Ecast ux ex, Ecast uy ey => (ux == uy) && hfexpr_eqn ex ey
  | Eprim_unop ux ex, Eprim_unop uy ey => (ux == uy) && hfexpr_eqn ex ey
  | Eprim_binop bx ex fx, Eprim_binop by_ ey fy => (bx == by_) && hfexpr_eqn ex ey && hfexpr_eqn fx fy
  | Emux ex fx gx, Emux ey fy gy => hfexpr_eqn ex ey && hfexpr_eqn fx fy && hfexpr_eqn gx gy
  | Eref rx, Eref ry => href_eqn rx ry
  | Eistag ex vx, Eistag ey vy => hfexpr_eqn ex ey && (vx == vy)
  | Esubtag ex vx, Esubtag ey vy => hfexpr_eqn ex ey && (vx == vy)
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
    
  Inductive rst : Type :=
  | NRst : rst
  | Rst : hfexpr (* reset trigger signal *) -> hfexpr (* reset value *) -> rst.

  Record hfreg : Type :=
    mk_freg
      {
        (* rid : var; *)
        type : ftype;
        clock : hfexpr;
        reset : rst
      }.

  Definition inst_ports : Type := seq var.

  (* A single case of a match statement, per spec:

       conditional_match_branch =
           id , [ "(" , id , ")" ] , ":" , newline ,
           [ indent , { statement } , dedent ] ;

     i.e. (variant name, optional binder, branch body).
     - variant name: the id of the enum variant this case handles;
     - binder: `Some v` if the branch is `variant(v)` (payload bound
       to v), `None` if it is a bare `variant:` (no data, or data
       unused);
     - body: the statement sequence of the branch. *)

  Inductive hfstmt : Type :=
  | Sskip
  | Swire : var -> ftype -> hfstmt
  | Sreg : var -> hfreg -> hfstmt
  | Smem : var -> hfmem -> hfstmt
  | Sinst : var -> var -> hfstmt
  | Snode : var -> hfexpr -> hfstmt
  | Sfcnct : href -> hfexpr -> hfstmt
  | Sinvalid : href -> hfstmt
  | Swhen : hfexpr -> hfstmt_seq -> hfstmt_seq -> hfstmt
  (* HiFIRRTL only, FIRRTL >= 4.0 match statement (LowerMatches).

     `Smatch e cases` corresponds to spec:

       conditional_match =
           "match" , expr , ":" , [ info ] , newline ,
           [ indent , { conditional_match_branch } , dedent ] ;

     e is the scrutinee (must be of an enum type); cases is the
     (possibly empty) sequence of branches.  Well-formedness requires
     the case variant names to exhaustively cover, in declaration
     order, all variants of e's enum type; the i-th case handles the
     i-th variant (matching CIRCT's use of fieldIndexAttr(i)). *)
  | Smatch : hfexpr -> seq (var * (option var) * hfstmt_seq) -> hfstmt
  with hfstmt_seq : Type :=
       | Qnil
       | Qcons : hfstmt -> hfstmt_seq -> hfstmt_seq.

   Scheme hfstmt_seq_hfstmt_ind := Induction for hfstmt_seq Sort Prop
   with hfstmt_hfstmt_seq_ind := Induction for hfstmt Sort Prop.
*)
End HiFirrtl.