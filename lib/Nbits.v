From Coq Require Import ZArith Arith List Ascii String Lia.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat ssrfun seq div.

  (* Zero extension and sign extension *)
  Notation copy := nseq.
  Definition b0 : bool := false.
  Definition b1 : bool := true.
  Definition zeros (n : nat) : bitseq := copy n b0.
  Definition zext (n : nat) (bs : bitseq) : bitseq := bs ++ zeros n.
  Definition lastd [A : Type] (d : A) (ls : seq A) :=
    match ls with
    | [::] => d
    | hd::tl => last hd tl
    end.
  Definition belastd [A : Type] (ls : seq A) :=
    match ls with
    | [::] => [::]
    | hd::tl => belast hd tl
    end.
  Definition split_head [A : Type] (d : A) (ls : seq A) : (A * seq A) := (head d ls, behead ls).
  Definition split_last [A : Type] (d : A) (ls : seq A) : (seq A * A) := (belastd ls, lastd d ls).
  Definition splitlsb (bs : bitseq) : (bool * bitseq) := split_head b0 bs.
  Definition splitmsb (bs : bitseq) : (bitseq * bool) := split_last b0 bs.
  Definition droplsb (bs : bitseq) : bitseq := (splitlsb bs).2.
  Definition dropmsb (bs : bitseq) : bitseq := (splitmsb bs).1.
  Definition joinlsb := @cons.
  Definition joinmsb := @rcons.
  Definition lsb (bs : bitseq) : bool := (splitlsb bs).1.
  Definition msb (bs : bitseq) : bool := (splitmsb bs).2.

  Definition sext (n : nat) (bs : bitseq) : bitseq := bs ++ copy n (msb bs).

  Definition to_nat (bs : bitseq) : nat :=
    foldr (fun b res => nat_of_bool b + res.*2) 0 bs.

  Definition bool_adder (c b1 b2 : bool) : bool * bool :=
    match c, b1, b2 with
    | false, false, false => (false, false)
    | true, false, false | false, true, false | false, false, true => (false, true)
    | true, true, false | false, true, true | true, false, true => (true, false)
    | true, true, true => (true, true)
    end.

  Fixpoint full_adder_zip (c : bool) (zip : seq (bool * bool)) : bool * bitseq :=
    match zip with
    | [::] => (c, [::])
    | (hd1, hd2)::tl => let (c, hd) := bool_adder c hd1 hd2 in
                        let (c, tl) := full_adder_zip c tl in
                        (c, hd::tl)
    end.

  Definition full_adder (c : bool) (bs1 bs2 : bitseq) := full_adder_zip c (zip bs1 bs2).

  Definition adcB (c : bool) (bs1 bs2 : bitseq) : bool * bitseq := full_adder c bs1 bs2.

  Definition addB (bs1 bs2 : bitseq) : bitseq := (adcB false bs1 bs2).2.

  Definition carry_addB (bs1 bs2 : bitseq) : bool := (adcB false bs1 bs2).1.

  Definition addB_ovf (bs1 bs2 : bitseq) : bool := carry_addB bs1 bs2.

  Definition invB (bs : bitseq) : bitseq := map (fun b => ~~ b) bs.

  Definition sbbB b (bs1 bs2 : bitseq) : bool * bitseq :=
    let (c, res) := (adcB (~~b) bs1 (invB bs2)) in
    (~~ c, res).

  Fixpoint extzip [S T : Type] (sd : S) (td : T) (ss : seq S) (ts : seq T) : seq (S * T) :=
    match ss, ts with
    | _, [::] => zip ss (nseq (size ss) td)
    | [::], _ => zip (nseq (size ts) sd) ts
    | s::ss, t::ts => (s, t)::(extzip sd td ss ts)
    end.

  Definition extzip0 := extzip b0 b0.

  Fixpoint ltB_lsb_zip (zip : seq (bool * bool)) : bool :=
    match zip with
    | [::] => false
    | (hd1, hd2)::tl => ((unzip1 tl == unzip2 tl) && (~~hd1) && hd2) || ltB_lsb_zip tl
    end.

  (* Test if bs1 < bs2 where LSB is at the head *)
  Definition ltB_lsb (bs1 bs2 : bitseq) : bool := ltB_lsb_zip (extzip0 bs1 bs2).

  (* By default, the ltB operation is ltB_lsb, which makes us easy to prove lemmas.
     To have a better performance, use ltB_rev instead. *)
  Notation ltB := ltB_lsb.

  Definition leB (bs1 bs2 : bitseq) : bool := (bs1 == bs2) || ltB bs1 bs2.

  Definition subB (bs1 bs2 : bitseq) : bitseq := (sbbB false bs1 bs2).2.

  Definition is_zero (bs : bitseq) : bool := all (fun b => b == false) bs.

  Fixpoint from_nat (n : nat) (x : nat) : bitseq :=
    match n with
    | O => [::]
    | S m => joinlsb bool (odd x) (from_nat m x./2)
    end.
