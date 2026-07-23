
(** * Variables *)

Require Import NArith.
From Coq Require Import OrderedType.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Lib Require Import SsrOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Definition var : Set := N.

Module VarOrder <: SsrOrderWithDefaultSucc.
  Include NOrder.
  Definition succ : t -> t := N.succ.
  Lemma ltn_succ : forall (x : t), ltn x (succ x).
  Proof.
    move=> x. apply/N.ltb_lt. exact: N.lt_succ_diag_r.
  Qed.
  Definition default : t := N0.
End VarOrder.


(** Product of ordered types. *)

Module MakeProdOrderMinimal (O1 O2 : SsrOrder) <: SsrOrderMinimal with Definition t := [eqType of (O1.T * O2.T)].

  Definition t : eqType := [eqType of (O1.T * O2.T)].

  Definition eqn (x y : t) : bool := x == y.

  Definition ltn (x y : t) : bool :=
    O1.ltn (fst x) (fst y) || (fst x == fst y) && O2.ltn (snd x) (snd y).

  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof.
    case: x => x1 x2; case: y => y1 y2; case: z => z1 z2. rewrite /ltn /=.
    case/orP=> [Hxy1 | /andP [Hxy1 Hxy2]]; (case/orP=> [Hyz1 | /andP [Hyz1 Hyz2]]).
    - by rewrite (O1.lt_trans Hxy1 Hyz1).
    - by rewrite -(eqP Hyz1) Hxy1.
    - by rewrite (eqP Hxy1) Hyz1.
    - by rewrite (eqP Hxy1) (eqP Hyz1) eqxx (O2.lt_trans Hxy2 Hyz2) orbT.
  Qed.

  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof.
    case: x => x1 x2; case: y => y1 y2. rewrite /ltn /=.
    case/orP=> [Hxy1 | /andP [Hxy1 Hxy2]].
    - apply/eqP=> H. case: H => H1 H2. apply: (O1.lt_not_eq Hxy1). by apply/eqP.
    - apply/eqP=> H. case: H => H1 H2. apply: (O2.lt_not_eq Hxy2). by apply/eqP.
  Qed.

  Definition compare (x y : t) : Compare ltn eqn x y.
  Proof.
    case: x => x1 x2; case: y => y1 y2. rewrite /ltn /eqn.
    case: (O1.compare x1 y1) => H1.
    - apply: LT => /=. by rewrite H1.
    - case: (O2.compare x2 y2) => H2.
      + apply: LT => /=. by rewrite H1 H2 orbT.
      + apply: EQ => /=. by rewrite (eqP H1) (eqP H2).
      + apply: GT => /=. by rewrite (eqP H1) eqxx H2 orbT.
    - apply: GT => /=. by rewrite H1.
  Defined.

End MakeProdOrderMinimal.

Module MakeProdOrderWithDefaultSucc (O1 O2 : SsrOrderWithDefaultSucc) <: SsrOrderWithDefaultSucc
    with Definition T := [eqType of (O1.T * O2.T)].
  Module M := MakeProdOrderMinimal O1 O2.
  Module P := MakeSsrOrder M.
  Include P.
  Definition default : t := (O1.default, O2.default).
  Definition succ (x : t) : t := (O1.succ (fst x), O2.default).
  Lemma ltn_succ (x : t) : ltn x (succ x).
  Proof.
    case: x => x y. rewrite /ltn /succ /=. rewrite /M.ltn /=.
    by rewrite O1.ltn_succ /=.
  Qed.
End MakeProdOrderWithDefaultSucc.

Module ProdVarOrder := MakeProdOrderWithDefaultSucc VarOrder VarOrder.
