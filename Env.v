From Coq Require Import FMaps (*FunInd FMapAVL OrderedType*).
From mathcomp Require Import all_ssreflect.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(****** Types Environment ******)

(****** Ground Types ******)

From Coq Require Import ZArith.

Inductive fgtyp : Set :=
Fuint : nat -> fgtyp
| Fsint : nat -> fgtyp
| Fuint_implicit : nat (* implicitly inferred width, HiFIRRTL only *) -> fgtyp
| Fsint_implicit : nat (* implicitly inferred width, HiFIRRTL only *) -> fgtyp
| Fclock
| Freset (* HiFIRRTL only *)
| Fasyncreset
(*| Fanalog : nat -> fgtyp*) (* TBD, HiFirrtl *)
.

(* Size of types *)

Definition sizeof_fgtyp (t : fgtyp) : nat :=
match t with
| Fuint w | Fuint_implicit w => w
| Fsint w | Fsint_implicit w => w
(* | Fanalog w => w *)
| _ => 1
end.

(* Equality of types *)

Definition fgtyp_eqn (x y : fgtyp) : bool :=
match x, y with
| Fuint wx, Fuint wy | Fuint_implicit wx, Fuint_implicit wy => wx == wy
| Fsint wx, Fsint wy | Fsint_implicit wx, Fsint_implicit wy => wx == wy
(* | Fanalog wx, Fanalog wy => wx == wy *)
| Fclock, Fclock => true
| Freset, Freset => true
| Fasyncreset, Fasyncreset => true
| _, _ => false
end.

Notation "x =? y" := (fgtyp_eqn x y).

Lemma fgtyp_eqn_refl (x : fgtyp) : x =? x.
Proof.
  destruct x; try (exact: eqxx|| done).
Qed.

Lemma fgtyp_eqP : Equality.axiom fgtyp_eqn.
Proof.
  rewrite /Equality.axiom /fgtyp_eqn.
  intros.
  destruct x, y.
  all : try (apply ReflectF ; discriminate); try (apply ReflectT ; reflexivity).
  destruct n, n0.
  all : try (apply ReflectF ; discriminate); try (apply ReflectT ; reflexivity).
  destruct (n.+1 == n0.+1) eqn: Hnn0.
  apply ReflectT; move /eqP : Hnn0 => Hnn0; rewrite Hnn0; reflexivity.
  apply ReflectF.
  move /eqP : Hnn0 => Hnn0. contradict Hnn0.
  injection Hnn0 ; intro; rewrite H; done.
  
  destruct (n == n0) eqn: Hn1n2.
  apply ReflectT ;
        move /eqP : Hn1n2 => Hn1n2 ; rewrite Hn1n2 ; reflexivity.
  apply ReflectF ;
      move /eqP : Hn1n2 => Hn1n2 ; contradict Hn1n2 ;
      injection Hn1n2 ; intro ; done.
  
  destruct (n == n0) eqn: Hn1n2.
  apply ReflectT ;
        move /eqP : Hn1n2 => Hn1n2 ; rewrite Hn1n2 ; reflexivity.
  apply ReflectF ;
      move /eqP : Hn1n2 => Hn1n2 ; contradict Hn1n2 ;
      injection Hn1n2 ; intro ; done.

  destruct (n == n0) eqn: Hn1n2.
      apply ReflectT ;
            move /eqP : Hn1n2 => Hn1n2 ; rewrite Hn1n2 ; reflexivity.
      apply ReflectF ;
          move /eqP : Hn1n2 => Hn1n2 ; contradict Hn1n2 ;
          injection Hn1n2 ; intro ; done.
Qed.

Lemma fgtyp_eqn_eq (x y : fgtyp) : x =? y <-> x = y.
Proof.
  split; first (destruct x; destruct y; move=> /= H);
    try (discriminate|| rewrite (eqP H); reflexivity).
  - done. - done. - done.
  - move=> ->. exact: fgtyp_eqn_refl.
Qed.

Lemma fgtyp_eq_dec (x y : fgtyp) : {x = y} + {x <> y}.
Proof. decide equality ; apply Nat.eq_dec. Qed.

HB.instance Definition _ := hasDecEq.Build fgtyp fgtyp_eqP.

(* a type for situations where an explicit width is required *)

Definition not_implicit_width (x : fgtyp) : Prop :=
match x with Fuint_implicit _ | Fsint_implicit _ => False
           | _ => True end.

Definition not_implicit (x : fgtyp) : bool :=
match x with Fuint_implicit _ | Fsint_implicit _ => false
           | _ => true end.

Definition fgtyp_explicit : Type :=
(* disallow implicit widths *)
{ x : fgtyp | not_implicit_width x }.

(*Instead of explicit_to_fgtyp you can use proj1_sig.
Definition explicit_to_fgtyp (H: fgtyp_inferred) : fgtyp := let (x, _) := H in x.*)

Definition fgtyp_remove_implicit (gt : fgtyp) : fgtyp := 
match gt with
| Fuint_implicit n => Fuint n 
| Fsint_implicit n => Fsint n 
| _ => gt
end.

Definition fgtyp_add_implicit (gt : fgtyp) : fgtyp := 
match gt with
| Fuint n => Fuint_implicit n 
| Fsint n => Fsint_implicit n 
| _ => gt
end.

(* equality of fgtyp_explicit is decidable *)

Definition fgtyp_explicit_eqn (x y : fgtyp_explicit) : bool :=
match x, y with
exist x' _, exist y' _ => fgtyp_eqn x' y'
end.

Lemma fgtyp_explicit_eqP : Equality.axiom fgtyp_explicit_eqn.
Proof.
rewrite /Equality.axiom /fgtyp_explicit_eqn.
intros.
destruct x, y.
destruct x, x0 ; destruct n, n0 ; simpl fgtyp_eqn ;
 try (apply ReflectF ; discriminate) ;
 try (apply ReflectT ; reflexivity) ;
 destruct (n1 == n2) eqn: Hn1n2.
1, 3: apply ReflectT ;
  move /eqP : Hn1n2 => Hn1n2 ; rewrite Hn1n2 ; reflexivity.
all: apply ReflectF ;
 move /eqP : Hn1n2 => Hn1n2 ; contradict Hn1n2 ;
 injection Hn1n2 ; intro ; done.
Qed.

HB.instance Definition _ := hasDecEq.Build fgtyp_explicit fgtyp_explicit_eqP.

(* 
1. 定义 finType 的 DecidableType Module
2. 定义 map 的 Module
3. 直接 Module.t 就是map的类型
*)
