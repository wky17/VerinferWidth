From Coq Require Import OrderedType NArith.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(** Coq OrderedType with Boolean equality. *)

Module Type SsrOrderMinimal.
  Parameter t : eqType.
  Definition eqn : t -> t -> bool := fun x y => x == y.
  Parameter ltn : t -> t -> bool.
  Axiom ltn_trans : forall x y z : t, ltn x y -> ltn y z -> ltn x z.
  Axiom ltn_not_eqn : forall x y : t, ltn x y -> x != y.
  Parameter compare : forall x y : t, Compare ltn eqn x y.
End SsrOrderMinimal.

Module Type SsrOrder <: OrderedType.
  Parameter T : eqType.
  Definition t : Type := T.
  Definition eq : t -> t -> Prop := fun x y => x == y.
  Parameter ltn : t -> t -> bool.
  Definition lt : t -> t -> Prop := fun x y => ltn x y.
  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.

  (* Derived facts *)
  Axiom ltn_trans : forall x y z : t, ltn x y -> ltn y z -> ltn x z.
  Axiom ltn_eqF : forall (x y : t), ltn x y -> (x == y) = false.
  Axiom ltnn : forall (x : t), ltn x x = false.
  Axiom nltn_eqVlt : forall (x y : t), (~~ ltn x y) = ((x == y) || ltn y x).
  Axiom ltn_neqAlt : forall (x y : t), ltn x y = (x != y) && ~~ (ltn y x).
  Axiom neq_ltn : forall (x y : t), (x != y) = (ltn x y) || (ltn y x).
End SsrOrder.


Module MakeSsrOrder (M : SsrOrderMinimal) <: SsrOrder.

  Definition T : eqType := M.t.

  Definition t : Type := T.

  Definition eq : t -> t -> Prop := fun x y => x == y.

  Definition ltn : t -> t -> bool := M.ltn.

  Definition lt : t -> t -> Prop := fun x y => ltn x y.

  Lemma eq_refl (x : t) : eq x x.
  Proof. exact: eqxx. Qed.

  Lemma eq_sym (x y : t) : eq x y -> eq y x.
  Proof. by rewrite /eq eq_sym. Qed.

  Lemma eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof. move=> Hxy Hyz. rewrite (eqP Hxy). exact: Hyz. Qed.

  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z :=
    M.ltn_trans.

  Lemma lt_not_eq (x y : t) : lt x y -> ~ eq x y.
  Proof. move=> Hlt Heq. by move/negP: (M.ltn_not_eqn Hlt). Qed.

  Definition compare : forall x y : t, Compare lt eq x y := M.compare.
  Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    move=> x y.
    case Hxy: (x == y).
    - left; exact: Hxy.
    - right; move=> Heq.
      apply/negPf: Hxy.
      exact: Heq.
  Qed.

  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof. exact: lt_trans. Qed.

  Lemma ltn_eqF (x y : t) : ltn x y -> (x == y) = false.
  Proof. move=> H. apply/negP. exact: lt_not_eq. Qed.

  Lemma ltnn (x : t) : ltn x x = false.
  Proof. case H: (ltn x x) => //=. move: (ltn_eqF H). by rewrite eqxx. Qed.

  Lemma nltn_eqVlt (x y : t) : (~~ ltn x y) = ((x == y) || ltn y x).
  Proof.
    case Heq: (x == y) => /=.
    - by rewrite (eqP Heq) ltnn.
    - case Hlt: (ltn x y) => /=; symmetry.
      + apply/negP => Hyx. move: (ltn_trans Hlt Hyx). by rewrite ltnn.
      + move: Heq Hlt. case: (compare x y); by move=> ->.
  Qed.

  Lemma ltn_neqAlt (x y : t) : ltn x y = (x != y) && ~~ (ltn y x).
  Proof.
    rewrite nltn_eqVlt. case H: ((x != y) && ((y == x) || ltn x y)).
    - move/andP: H=> [H1 H2]. case/orP: H2 => H2.
      + by rewrite (eqP H2) eqxx in H1.
      + assumption.
    - apply/negP=> H2. move/negP: H; apply. rewrite (ltn_eqF H2) H2.
      by rewrite orbT.
  Qed.

  Lemma neq_ltn (x y : t) : (x != y) = (ltn x y) || (ltn y x).
  Proof.
    case: (compare x y) => H.
    - by rewrite (ltn_eqF H) H.
    - by rewrite H (eqP H) !ltnn.
    - by rewrite H eqtype.eq_sym (ltn_eqF H) orbT.
  Qed.

End MakeSsrOrder.


(* OrderedType with a default value and a successor function,
   useful for generating new values *)

Module Type HasSucc (Import T : SsrOrder).
  Parameter succ : t -> t.
End HasSucc.

Module Type HasLtn (Import T : SsrOrder).
  Parameter ltn : t -> t -> bool.
End HasLtn.

Module Type HasLtnSucc (Import T : SsrOrder) (Import L : HasLtn T) (Import S : HasSucc T).
  Parameter ltn_succ : forall (x : t), ltn x (succ x).
End HasLtnSucc.

Module Type HasDefault (Import T : Equalities.Typ).
  Parameter default : t.
End HasDefault.

Module Type SsrOrderWithDefaultSucc <: SsrOrder :=
  SsrOrder <+ HasDefault <+ HasSucc <+ HasLtnSucc.



Section NLemmas.

  Local Open Scope N_scope.

  Lemma N_ltP : forall x y : N, reflect (x < y) (x <? y).
  Proof.
    move=> x y. move: (N.ltb_lt x y) => [H1 H2]. case H: (x <? y).
    - apply: ReflectT. exact: (H1 H).
    - apply: ReflectF. move=> Hlt. move: (H2 Hlt). by rewrite H.
  Qed.

  Lemma N_leP : forall x y : N, reflect (x <= y) (x <=? y).
  Proof.
    move=> x y. move: (N.leb_le x y) => [H1 H2]. case H: (x <=? y).
    - apply: ReflectT. exact: (H1 H).
    - apply: ReflectF. move=> Hlt. move: (H2 Hlt). by rewrite H.
  Qed.

  Lemma NltSn n : n < n + 1.
  Proof. rewrite N.add_1_r. exact: N.lt_succ_diag_r. Qed.

  Lemma NltnSn n : n <? n + 1.
  Proof. apply/N_ltP. exact: NltSn. Qed.

  Lemma Nltnn n : (n <? n) = false.
  Proof. exact: N.ltb_irrefl. Qed.

  Lemma Nltn_eqF n m : (n <? m) -> (n == m) = false.
  Proof. move/N_ltP => H. apply/eqP. exact: N.lt_neq. Qed.

  Lemma Nltn_trans n m p : (m <? n) -> (n <? p) -> (m <? p).
  Proof.
    move=> /N_ltP Hmn /N_ltP Hnp. apply/N_ltP. exact: (N.lt_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma Nleq_trans n m p : (m <=? n) -> (n <=? p) -> (m <=? p).
  Proof.
    move=> /N_leP Hmn /N_leP Hnp. apply/N_leP. exact: (N.le_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma Nleq_ltn_trans n m p : (m <=? n) -> (n <? p) -> (m <? p).
  Proof.
    move=> /N_leP Hmn /N_ltP Hnp. apply/N_ltP. exact: (N.le_lt_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma Nltn_leq_trans n m p : (m <? n) -> (n <=? p) -> (m <? p).
  Proof.
    move=> /N_ltP Hmn /N_leP Hnp. apply/N_ltP. exact: (N.lt_le_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma N_eqn_ltn_gtn_cases m n : (m == n) || (m <? n) || (n <? m).
  Proof.
    move: (N.lt_total m n). case; last case.
    - move/N_ltP => H. rewrite H orbT /=. reflexivity.
    - move/eqP=> H. rewrite H orTb /=. reflexivity.
    - move/N_ltP => H. rewrite H orbT /=. reflexivity.
  Qed.

  Lemma Nltn0Sn n : 0 <? n + 1.
  Proof. apply/N_ltP. apply: N.add_pos_r. done. Qed.

  Lemma NltnW m n : (m <? n) -> (m <=? n).
  Proof. move=> /N_ltP H. apply/N_leP. exact: (N.lt_le_incl _ _ H). Qed.

  Lemma Nltn_ltnF (n m : N) : n <? m -> m <? n = false.
  Proof.
    move=> H1. apply/negP => H2.  move: (Nltn_trans H1 H2). by rewrite Nltnn.
  Qed.

  Lemma Nltn_neqAlt (n m : N) : n <? m = (n != m) && ~~ (m <? n).
  Proof.
    case H: (n == m).
    - rewrite (eqP H) Nltnn. reflexivity.
    - move/negPf/eqP: H => H. move/(N.lt_gt_cases n m): H. case.
      + move/N_ltP=> H. rewrite H. rewrite (Nltn_ltnF H). reflexivity.
      + move/N_ltP=> H; rewrite H. rewrite (Nltn_ltnF H). reflexivity.
  Qed.

  Lemma Nleqnn n : n <=? n.
  Proof. exact: N.leb_refl. Qed.

  Lemma Nleqn0 n : (n <=? 0) = (n == 0).
  Proof.
    move: (N.le_0_r n) => [H1 H2].
    case H: (n == 0); apply/N_leP.
    - exact: (H2 (eqP H)).
    - move=> Hle.
      move: (H1 Hle) => /eqP Heq.
      by rewrite H in Heq.
  Qed.

  Lemma Nleb_add_diag_r x y : x <=? x + y.
  Proof. apply/N_leP. exact: N.le_add_r. Qed.

  Lemma Nltb_add_diag_r x y : 0 <? y -> x <? x + y.
  Proof. move/N_ltP=> H. apply/N_ltP. exact: (N.lt_add_pos_r _ _ H). Qed.

  Lemma Nltb_leb_incl x y : x <? y -> x <=? y.
  Proof. move/N_ltP=> H. apply/N_leP. exact: (N.lt_le_incl _ _ H). Qed.

  Lemma Nsubn0 n : n - 0 = n.
  Proof. exact: (N.sub_0_r n). Qed.

  Lemma Nleq_eqVlt m n : (m <=? n) = (m == n) || (m <? n).
  Proof.
    move: (N.lt_eq_cases m n) => [H1 H2].
    symmetry.
    case H: (m <=? n).
    - apply/orP.
      move/N_leP: H => H.
      case: (H1 H) => {H} H.
      + right; apply/N_ltP; assumption.
      + left; apply/eqP; assumption.
    - apply/negP => /orP Hor.
      move/negP: H; apply; apply/N_leP; apply: H2.
      case: Hor => H.
      + right; apply/eqP; assumption.
      + left; apply/N_ltP; assumption.
  Qed.

  Lemma NltnS n m : (n <? m + 1) = (n <=? m).
  Proof.
    rewrite N.add_1_r.
    move: (N.lt_succ_r n m) => [H1 H2].
    case Hle: (n <=? m).
    - move/N_leP: Hle => Hle.
      apply/N_ltP.
      exact: (H2 Hle).
    - apply/N_ltP => Hlt.
      move/negP: Hle; apply.
      apply/N_leP.
      exact: (H1 Hlt).
  Qed.

  Lemma Nltn_add2r p m n : ((m + p) <? (n + p)) = (m <? n).
  Proof.
    move: (N.add_lt_mono_r m n p) => [H1 H2].
    case Hlt: (m <? n).
    - move/N_ltP: Hlt => Hlt.
      apply/N_ltP.
      exact: (H1 Hlt).
    - apply/negP => /N_ltP H.
      move/negP: Hlt; apply; apply/N_ltP.
      exact: (H2 H).
  Qed.

  Lemma nat_of_bin_pos p :
    nat_of_bin (N.pos p) = nat_of_pos p.
  Proof. reflexivity. Qed.

  Lemma Npos_ge1 p : (1 <= N.pos p)%num.
  Proof. by elim: p. Qed.

End NLemmas.


(** An ordered type for N with a Boolean equality in mathcomp. *)

Module NOrderMinimal <: SsrOrderMinimal.

Local Open Scope N_scope.

Definition t : eqType := [eqType of N].

Definition eqn : t -> t -> bool := fun x y : t => x == y.

Definition ltn : t -> t -> bool := fun x y => N.ltb x y.

Hint Unfold eqn ltn.

Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
Proof.
  move=> /N.ltb_lt Hxy /N.ltb_lt Hyz.
  apply/N.ltb_lt.
  exact: N.lt_trans Hxy Hyz.
Qed.

Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
Proof.
  rewrite /ltn.                     (* 展开 ltn 为 N.ltb *)
  move=> H.                         (* H : (x <? y) = true *)
  apply/negP.                       (* 目标转为 ~ (x == y) *)
  move/eqP => Hxy.                 (* 假设 x == y，由 eqP 得 x = y *)
  have Hlt : x < y by apply/N.ltb_lt.  (* 由 H 推出 x < y *)
  rewrite Hxy in Hlt.               (* 替换 x 为 y，得到 y < y *)
  apply: (N.lt_irrefl y) => //.              (* 与 N.lt_irrefl 矛盾，完成证明 *)
Qed.

Lemma compare (x y : t) : Compare ltn eqn x y.
Proof.
  case H: (N.compare x y).
    - apply: EQ. move: (N.compare_eq_iff x y) => [Hc _].
      apply/eqP. exact: (Hc H).
    - apply: LT. move: (N.compare_lt_iff x y) => [Hc _].
      apply/N_ltP. exact: (Hc H).
    - apply: GT. move: (N.compare_gt_iff x y) => [Hc _].
      apply/N_ltP. exact: (Hc H).
Qed.

Local Close Scope N_scope.

End NOrderMinimal.

Module NOrder <: SsrOrder := MakeSsrOrder NOrderMinimal.
