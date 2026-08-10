From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From firrtl Require Import Env LoFirrtl HiEnv HiFirrtl.
From Lib Require Import Var Nbits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Parameter indeterminate_val : bitseq.
Parameter ebinop_op : ebinop -> fgtyp -> fgtyp -> bitseq -> bitseq -> bitseq.
Parameter eunop_op : eunop -> fgtyp -> bitseq -> bitseq.
Parameter n : nat. 

  (****** Semantics ******)

Inductive hvalue : Type :=
  | Gval : bitseq -> hvalue
  | Aval : array_value -> hvalue
  | Bval : (*forall bu :*) bundle_value (*, not_Bnil bu*) -> hvalue
with array_value : Type :=
  | Anil : array_value
  | Acons : hvalue -> array_value -> array_value
with bundle_value : Type :=
  | Bnil : bundle_value
  | Bflips : var -> fflip -> hvalue -> bundle_value -> bundle_value
(*with not_Bnil (bu : bundle_value) : bool :=
  match bu with
  | Bnil => false
  | _ => true
  end*).

Lemma bitseq_eq_dec : forall (x y : bitseq), {x = y} + {x <> y}.
Proof.
  apply list_eq_dec.
  apply bool_dec.
Qed.

(* general data value equality is decidable *)
Lemma hvalue_eq_dec (x y : hvalue) : {x = y} + {x <> y}
with array_value_eq_dec (x y : array_value) : {x = y} + {x <> y}
with bundle_value_eq_dec (x y : bundle_value) : {x = y} + {x <> y}.
Proof.
  - destruct x, y; try (right; discriminate).
    + destruct (bitseq_eq_dec b b0) as [H|H]; [left; f_equal; exact H | right; injection; auto].
    + destruct (array_value_eq_dec a a0) as [H|H]; [left; f_equal; exact H | right; injection; auto].
    + destruct (bundle_value_eq_dec b b0) as [H|H]; [left; f_equal; exact H | right; injection; auto].
  - destruct x, y; try (right; discriminate); [left; reflexivity |].
    + destruct (hvalue_eq_dec h h0) as [H1|H1];
      [destruct (array_value_eq_dec x y) as [H2|H2]; [left; f_equal; assumption | right; injection; auto] 
      | right; injection; auto].
  - destruct x, y; try (right; discriminate); [left; reflexivity |].
    destruct (N.eq_dec v v0) as [Hv|Hv];
      [destruct (fflip_eq_dec f f0) as [Hf|Hf];
        [destruct (hvalue_eq_dec h h0) as [Hh|Hh];
          [destruct (bundle_value_eq_dec x y) as [Ht|Ht]; 
          [left; do 4 f_equal; assumption | right; injection; auto]
        | right; injection; auto]
      | right; injection; auto]
    | right; injection; auto].
Qed.

(* Boolean equality for general data values *)
Fixpoint hvalue_eqn (x y : hvalue) : bool :=
  match x, y with
  | Gval val1, Gval val2 => val1 == val2
  | Aval val1, Aval val2 => array_value_eqn val1 val2
  | Bval val1, Bval val2 => bundle_value_eqn val1 val2
  | _, _ => false
  end
with array_value_eqn (x y : array_value) : bool :=
  match x, y with
  | Anil, Anil => true
  | Acons val1 tl1, Acons val2 tl2 => (hvalue_eqn val1 val2) && (array_value_eqn tl1 tl2)
  | _, _ => false
  end
with bundle_value_eqn (x y : bundle_value) : bool :=
  match x, y with
  | Bnil, Bnil => true
  | Bflips v1 Nflip val1 ff1, Bflips v2 Nflip val2 ff2 => (v1 == v2) && (hvalue_eqn val1 val2) && (bundle_value_eqn ff1 ff2)
  | Bflips v1 Flipped val1 ff1, Bflips v2 Flipped val2 ff2 => (v1 == v2) && (hvalue_eqn val1 val2) && (bundle_value_eqn ff1 ff2)
  | _, _ => false
  end.

Lemma bits_eqP : forall (x y : bitseq), reflect (x = y) (x == y).
Proof. intros. exact: eqP. Qed.

Lemma N_eqP : forall (x y : N), reflect (x = y) (x == y).
Proof. intros. exact: eqP. Qed.

(* reflection predicate for general data values *)
Lemma hvalue_eqP : forall (x y : hvalue), reflect (x = y) (hvalue_eqn x y)
with array_value_eqP : forall (x y : array_value), reflect (x = y) (array_value_eqn x y)
with bundle_value_eqP : forall (x y : bundle_value), reflect (x = y) (bundle_value_eqn x y).
Proof.
  (* 证明hvalue_eqP *)
  - intros x y.
    destruct x as [n|a|b], y as [m|a'|b']; simpl; try (right; congruence).
    + destruct (bits_eqP n m) as [H|H].
        * left. f_equal; assumption.
        * right; congruence. 
    + destruct (array_value_eqP a a') as [H|H].
        * left; f_equal; assumption.
        * right; congruence.
    + destruct (bundle_value_eqP b b') as [H|H].
        * left; f_equal; assumption.
        * right; congruence.
  
  (* 证明array_value_eqP *)
  - intros x y.
    destruct x as [|h1 t1], y as [|h2 t2]; simpl; try (right; congruence).
    + left; done. 
    + destruct (hvalue_eqP h1 h2) as [H1|H1]; try (right; congruence).
        destruct (array_value_eqP t1 t2) as [H2|H2].
          * left; f_equal; assumption.
          * right; congruence.
  
  (* 证明bundle_value_eqP *)
  - intros x y.
    destruct x as [|v1 flip1 h1 t1], y as [|v2 flip2 h2 t2]; simpl; try (right; congruence).
    left; done. destruct flip1; right; done.
    destruct flip1, flip2; simpl; try (right; congruence).
    + destruct (N_eqP v1 v2) as [Hv|Hv]; try (right; congruence).
      destruct (hvalue_eqP h1 h2) as [Hh|Hh]; try (right; congruence).
      destruct (bundle_value_eqP t1 t2) as [Ht|Ht]; try (right; congruence). 
      left; do 4 f_equal; assumption.
    + destruct (N_eqP v1 v2) as [Hv|Hv]; try (right; congruence).
      destruct (hvalue_eqP h1 h2) as [Hh|Hh]; try (right; congruence).
      destruct (bundle_value_eqP t1 t2) as [Ht|Ht]; try (right; congruence). 
      left; do 4 f_equal; assumption.
Qed.

(*Compute (to_Z [::false;true]).
Compute (to_Zpos [::false;true]).
Compute (to_Z [::true;false]).
Compute (to_Zpos [::true;false]). 后为高位
若使用Z来表示value
| Fsint _ => to_Z c
| Fuint _ => to_Zpos c *)

(* makes val to be of type ft *)
Fixpoint ftext (ft : ftype) (val : hvalue) : option hvalue :=
  match ft, val with
  | Gtyp (Fuint w), Gval c => if (length c > w) then Some (Gval (take w c))
                              else Some (Gval (zext (w - size c) c))
  | Gtyp (Fsint w), Gval c => if (length c > w) then Some (Gval (take w c))
                              else Some (Gval (sext (w - size c) c))
  | Gtyp _, Gval c => if (length c > 1) then Some (Gval (take 1 c))
                              else Some (Gval (zext (1 - size c) c))
  | Atyp atyp n, Aval aval => match atypext atyp aval with
                            | Some aval' => Some (Aval aval')
                            | _ => None
                            end
  | Btyp btyp, Bval bval => match btypext btyp bval with
                            | Some bval' => Some (Bval bval')
                            | _ => None
                            end
  | _, _ => None
  end
with atypext (ft : ftype)(* element type *) (aval : array_value) : option array_value := 
  match aval with
  | Anil => Some Anil
  | Acons val tl => match ftext ft val, atypext ft tl with
                            | Some val', Some tl' => Some (Acons val' tl')
                            | _, _ => None
                            end
  end
with btypext (btyp : ffield) (bval : bundle_value) : option bundle_value :=
  match btyp, bval with
  | Fnil, Bnil => Some Bnil
  | Fflips _ _ ft ff, Bflips v f val tl => match ftext ft val, btypext ff tl with
                | Some val', Some tl' => Some (Bflips v f val' tl')
                | _, _ => None
                end
  | _, _ => None
  end.

Fixpoint ftext0 (ft : ftype) : hvalue :=
  match ft with
  | Gtyp (Fuint w) 
  | Gtyp (Fsint w) => Gval (zeros w)
  | Gtyp _ => Gval [::b0]
  | Atyp atyp n => 
      let fix atypext0 (n : nat) : array_value :=
        match n with
        | 0 => Anil
        | n'.+1 => Acons (ftext0 atyp) (atypext0 n')
        end
      in Aval (atypext0 n)
  | Btyp btyp => 
      let fix btypext0 (btyp : ffield) : bundle_value :=
        match btyp with
        | Fnil => Bnil
        | Fflips v f ft ff => Bflips v f (ftext0 ft) (btypext0 ff)
        end
      in Bval (btypext0 btyp)
  end.

Module Sem_HiF.

(* type of ref expressions *)
Fixpoint type_of_ref (r : HiF.href) (tmap : VM.t (ftype * fcomponent)) : option ftype :=
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
  | Esubaccess r _
  | Esubindex r _ => match type_of_ref r tmap with
              | Some (Atyp ty _) => Some ty
              | _ => None
              end
  end.

(* copied from ModuleGraph *)
Definition fgtyp_mux (x y : fgtyp) : option fgtyp :=
    match x, y with
    | Fuint wx, Fuint wy => Some (Fuint (Nat.max wx wy))
    | Fsint wx, Fsint wy => Some (Fsint (Nat.max wx wy))
    | Fclock, Fclock => Some Fclock
    | Freset, Freset => Some Freset
    | Fasyncreset, Fasyncreset => Some Fasyncreset
    | _, _ => None
    end.

Fixpoint ftype_mux (x y : ftype) : option ftype :=
  match x, y with
  | Gtyp tx, Gtyp ty => match fgtyp_mux tx ty with
                        | Some fgt => Some (Gtyp fgt)
                        | None => None
                        end
  | Atyp tx nx, Atyp ty ny => if (nx == ny)
                              then match ftype_mux tx ty with
                              | Some fat => Some (Atyp fat nx)
                              | None => None
                              end
                              else None
  | Btyp fx, Btyp fy => ffield_mux fx fy
  | _, _ => None
  end
with ffield_mux (f1 f2 : ffield) : option ftype :=
       match f1, f2 with
       | Fnil, Fnil => Some (Btyp Fnil)
       | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2
         => if v1 == v2 then
               match ffield_mux fs1 fs2 with
               | Some (Btyp bf) => match ftype_mux t1 t2 with
                           | Some ft => Some (Btyp (Fflips v1 Nflip ft bf))
                           | _ => None
                           end
               | _ => None
               end
            else None
       | Fflips _ Flipped _ _, Fflips _ Flipped _ _
         => None
       | _, _ => None
       end.

Fixpoint type_of_hfexpr (e : HiF.hfexpr) (tmap: VM.t (ftype * fcomponent)) : option ftype :=
  match e with
  | Econst t bs => Some (Gtyp t)
  | Eref r => Sem_HiF.type_of_ref r tmap 
  | Ecast AsUInt e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp (Fsint w))
                        | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                        | Some (Gtyp Fclock) 
                        | Some (Gtyp Freset)
                        | Some (Gtyp Fasyncreset) => Some (Gtyp (Fuint 1))
                        | _ => None
                        end
  | Ecast AsSInt e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp (Fsint w))
                        | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint w))
                        | Some (Gtyp Fclock) 
                        | Some (Gtyp Freset)
                        | Some (Gtyp Fasyncreset) => Some (Gtyp (Fsint 1))
                        | _ => None
                        end
  | Ecast AsClock e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp _) => Some (Gtyp Fclock)
                        | _ => None
                        end
  | Ecast AsAsync e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp _) => Some (Gtyp Fasyncreset)
                        | _ => None
                        end
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn w n)))
                              | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn w n)))
                              | _ => None
                              end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (w + n)))
                              | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (w + n)))
                              | _ => None
                              end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn (w - n) 1)))
                              | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn (w - n) 0)))
                              | _ => None
                              end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr e1 tmap with
                          | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint w))
                          | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                          | _ => None
                          end
  | Eprim_unop Uneg e1 => match type_of_hfexpr e1 tmap with
                          | Some (Gtyp (Fsint w))
                          | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                          | _ => None
                          end
  | Eprim_unop Unot e1 => match type_of_hfexpr e1 tmap with
                          | Some (Gtyp (Fsint w))
                          | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                          | _ => None
                          end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 tmap with
                                    | Some (Gtyp (Fsint w))
                                    | Some (Gtyp (Fuint w)) =>
                                        if (n2 <= n1) && (n1 < w) then Some (Gtyp (Fuint (n1 - n2 + 1)))
                                                                  else None
                                    | _ => None
                                    end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (Gtyp (Fsint w))
                                | Some (Gtyp (Fuint w)) =>
                                    if n <= w then Some (Gtyp (Fuint n))
                                              else None
                                | _ => None
                                end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (Gtyp (Fsint w))
                                | Some (Gtyp (Fuint w)) =>
                                    if n <= w then Some (Gtyp (Fuint (w - n)))
                                              else None
                                | _ => None
                                end
  | Eprim_unop _ e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp (Fsint _))
                        | Some (Gtyp (Fuint _)) => Some (Gtyp (Fuint 1))
                        | _ => None
                        end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                    | Some (Gtyp (Fsint _)), Some (Gtyp (Fsint _))
                                    | Some (Gtyp (Fuint _)), Some (Gtyp (Fuint _)) => Some (Gtyp (Fuint 1))
                                    | _, _ => None
                                    end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (maxn w1 w2 + 1)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (maxn w1 w2 + 1)))
                              | _, _ => None
                              end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (w1 + w2)))
                              | _, _ => None
                              end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint w1))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (w1 + 1)))
                                | _, _ => None
                                end
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (minn w1 w2)))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (minn w1 w2)))
                                | _, _ => None
                                end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (2 ^ w2 + w1 - 1)))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fsint (2 ^ w2 + w1 - 1)))
                                | _, _ => None
                                end
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint w1))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fsint w1))
                                | _, _ => None
                                end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                              | _, _ => None
                              end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (maxn w1 w2)))
                              | _, _ => None
                              end
  | Emux c e1 e2 => match type_of_hfexpr c tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                    | Some (Gtyp (Fuint _)), Some t1, Some t2 => ftype_mux t1 t2
                    | _, _, _ => None
                    end
  (*| Evalidif _ _ => None*)
  end.

(* value of ref expressions *)
Fixpoint hvalue_of_ref (r : HiF.href) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option hvalue :=
  match r with
  | Eid v => VM.find v s
  | Esubfield r v => match hvalue_of_ref r s tmap with
              | Some (Bval fv) => let fix aux fx := (
                                          match fx with
                                          | Bflips v' f t fxs =>
                                            if (v == v') then Some t
                                            else aux fxs
                                          | Bnil => None
                                          end )
                                  in aux fv
              | _ => None
              end
  | Esubindex r n => match hvalue_of_ref r s tmap with
              | Some (Aval fv) => let fix aux fx m := (
                                          match fx, m with
                                          | Acons t fxs, m'.+1 => aux fxs m'
                                          | Acons t _, 0 => Some t 
                                          | _, _ => None
                                          end )
                                  in aux fv n
              | _ => None
              end
  | Esubaccess r e => match eval_hfexpr e s tmap, hvalue_of_ref r s tmap with 
              | Some (Gval val), Some (Aval fv) => let n := to_nat val in
                                  let fix aux fx m := (
                                          match fx, m with
                                          | Acons t fxs, m'.+1 => aux fxs m'
                                          | Acons t _, 0 => Some t 
                                          | _, _ => None
                                          end )
                                  in aux fv n
              | _, _ => None
              end
  end
(* Expression evaluation, value *)
with eval_hfexpr (exp : HiF.hfexpr) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option hvalue :=
  match exp with
  | Econst t c => match t with
                  | Fuint w1 => if (size c) > w1 then None else Some (Gval (zext (w1 - size c) c))
                  | Fsint w2 => if (size c) > w2 then None else Some (Gval (sext (w2 - size c) c))
                  | _ => None
                  end
  | Eref r => hvalue_of_ref r s tmap
  | Ecast AsUInt e 
  | Ecast AsSInt e => eval_hfexpr e s tmap
  | Ecast AsClock e  
  | Ecast AsAsync e => match eval_hfexpr e s tmap with Some (Gval val) => Some (Gval [::lsb val]) | _ => None end
  | Eprim_binop b e1 e2 =>
      match eval_hfexpr e1 s tmap, eval_hfexpr e2 s tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
      | Some (Gval val1), Some (Gval val2), Some (Gtyp gt1), Some (Gtyp gt2) => 
          let val := ebinop_op b gt1 gt2 val1 val2 in Some (Gval val)
      | _, _, _, _ => None
      end
  | Eprim_unop u e =>
      match eval_hfexpr e s tmap, type_of_hfexpr e tmap with
      | Some (Gval val1), Some (Gtyp gt1) =>
          let val := eunop_op u gt1 val1 in Some (Gval val)
      | _, _ => None
      end
  | Emux c e1 e2 => 
      match eval_hfexpr c s tmap, type_of_hfexpr exp tmap, eval_hfexpr e1 s tmap, eval_hfexpr e2 s tmap with
      | Some (Gval valc), Some ft, Some val1, Some val2 => if ~~ (is_zero valc) then ftext ft val1
                                                                                else ftext ft val2
      | _, _, _, _ => None
      end
  end.

Fixpoint elements_of_ftype ft :=
  match ft with
  | Gtyp t => 1
  | Atyp t n => (elements_of_ftype t) * n + 1
  | Btyp b => elements_of_fields b + 1
  end
with elements_of_fields b :=
       match b with
       | Fnil => 0
       | Fflips v fl t fs => (elements_of_ftype t) + elements_of_fields fs
       end.

(* 内部aggr也有offset的版本 *)
Fixpoint offset_ref (r : HiF.href) (tmap: VM.t (ftype * fcomponent)) (n : nat) : option nat :=
  match r with
  | Eid v => Some n
  | Esubindex v i => match offset_ref v tmap n with
                    | Some os =>  match Sem_HiF.type_of_ref v tmap with
                                | Some (Atyp ty _) => Some (os + i * elements_of_ftype ty + 1)
                                | _ => None
                                end
                    | _ => None
                    end
  | Esubfield v f =>  match offset_ref v tmap n with
                    | Some os => match Sem_HiF.type_of_ref v tmap with
                        | Some (Btyp fs) => let fix aux fx acc :=
                            match fx with
                            | Fflips v' _ ty fxs =>
                                if (v' == f) then Some (acc + 1)
                                else aux fxs (acc + elements_of_ftype ty)
                            | Fnil => None
                            end in aux fs os
                        | _ => None
                        end
                    | None => None
                    end
  | Esubaccess r e => None
  end.

Fixpoint elements_of_hvalue val :=
  match val with
  | Gval _ => 1
  | Aval aval => elements_of_array_value aval + 1
  | Bval bval => elements_of_bundle_value bval + 1
  end
with elements_of_array_value aval :=
  match aval with
  | Anil => 0
  | Acons val tl => elements_of_hvalue val + elements_of_array_value tl
  end
with elements_of_bundle_value bval :=
  match bval with
  | Bnil => 0
  | Bflips _ _ t fs => elements_of_hvalue t + elements_of_bundle_value fs
  end.

(* 通过offset来找到hvalue中对应值 *)
Fixpoint find_hvalue_by_offset (val : hvalue) (offset : nat) : option bitseq :=
  match val, offset with
  | Gval bv, 0 => Some bv
  | Aval aval, os.+1 => find_array_value_by_offset aval os
  | Bval bval, os.+1 => find_bundle_value_by_offset bval os
  | _, _ => None
  end 
with find_array_value_by_offset (aval : array_value) (offset : nat) : option bitseq :=
  match aval with
  | Acons val tl => let element_size := elements_of_hvalue val in if offset >= element_size then
                    find_array_value_by_offset tl (offset - element_size)
                else find_hvalue_by_offset val offset
  | _ => None
  end
with find_bundle_value_by_offset (bval : bundle_value) (offset : nat) : option bitseq := 
  match bval with
  | Bflips _ _ val tl => let element_size := elements_of_hvalue val in if offset >= element_size then
                    find_bundle_value_by_offset tl (offset - element_size)
                else find_hvalue_by_offset val offset
  | _ => None
  end.

(* 通过offset来修改hvalue中的对应值 *)
Fixpoint update_hvalue_by_offset (val : hvalue) (offset : nat) (new_val : hvalue) : option hvalue :=
  match val, offset with
  | _, 0 => Some new_val
  | Gval _, _ => None
  | Aval aval, os.+1 => 
                match update_array_value_by_offset aval os new_val with
                | Some aval' => Some (Aval aval')
                | _ => None
                end
  | Bval bval, os.+1 => 
                match update_bundle_value_by_offset bval os new_val with
                | Some bval' => Some (Bval bval')
                | _ => None
                end
  end 
with update_array_value_by_offset (aval : array_value) (offset : nat) (new_val : hvalue) : option array_value :=
  match aval with
  | Acons val tl => let element_size := elements_of_hvalue val in if offset >= element_size then
                    match update_array_value_by_offset tl (offset - element_size) new_val with
                    | Some tl' => Some (Acons val tl')
                    | _ => None
                    end 
                else match update_hvalue_by_offset val offset new_val with
                    | Some val' => Some (Acons val' tl)
                    | _ => None
                    end
  | _ => None
  end
with update_bundle_value_by_offset (bval : bundle_value) (offset : nat) (new_val : hvalue) : option bundle_value := 
  match bval with
  | Bflips v f val tl => let element_size := elements_of_hvalue val in if offset >= element_size then
                    match update_bundle_value_by_offset tl (offset - element_size) new_val with
                    | Some tl' => Some (Bflips v f val tl')
                    | _ => None
                    end 
                else match update_hvalue_by_offset val offset new_val with
                    | Some val' => Some (Bflips v f val' tl)
                    | _ => None
                    end
  | _ => None
  end.

Fixpoint eval_ref_connection (ft : ftype) (val_l val_r : hvalue) (offset_l offset_r : nat) : option (hvalue * hvalue) :=
  (* bidirectional connect between different components *)
  match ft with
  | Gtyp gt => match find_hvalue_by_offset val_r offset_r with
              | Some bv => match update_hvalue_by_offset val_l offset_l (Gval bv) with
                          | Some val_l' => Some (val_l', val_r)
                          | _ => None
                          end
              | _ => None
              end
  | Atyp atyp n => let element_size := elements_of_ftype atyp in
                   let fix aux m temp_l temp_r os_l os_r := (
                          match m with
                          | m'.+1 => match eval_ref_connection atyp temp_l temp_r os_l os_r with
                                    | Some (temp_l', temp_r') => aux m' temp_l' temp_r' (os_l + element_size) (os_r + element_size)
                                    | _ => None
                                    end
                          | _ => Some (temp_l, temp_r)
                          end) in aux n val_l val_r (offset_l + 1) (offset_r + 1)
  | Btyp ff => eval_bundle_connection ff val_l val_r (offset_l + 1) (offset_r + 1) 
  end
with eval_bundle_connection (ff : ffield) (val_l val_r : hvalue) (offset_l offset_r : nat) : option (hvalue * hvalue) :=
  match ff with
  | Fnil => Some (val_l, val_r)
  | Fflips _ Nflip ft tl => match eval_ref_connection ft val_l val_r offset_l offset_r with
                          | Some (val_l', val_r') => let element_size := elements_of_ftype ft in
                            eval_bundle_connection tl val_l' val_r' (offset_l + element_size) (offset_r + element_size)
                          | _ => None
                          end
  | Fflips _ Flipped ft tl => match eval_ref_connection ft val_r val_l offset_r offset_l with
                          | Some (val_r', val_l') => let element_size := elements_of_ftype ft in
                            eval_bundle_connection tl val_l' val_r' (offset_l + element_size) (offset_r + element_size)
                          | _ => None
                          end
  end.

Fixpoint eval_ref_connection1 (ft : ftype) (val : hvalue) (offset_l offset_r : nat) : option hvalue :=
  (* bidirectional connect between different sub-component inside the same component.
     It is assumed that offset_l indicates the sub-component to be written and offset_r the one to be read,
     even when they are flipped. *)
  match ft with
  | Gtyp gt => match find_hvalue_by_offset val offset_r with
              | Some bv => match update_hvalue_by_offset val offset_l (Gval bv) with
                          | Some val' => Some val'
                          | _ => None
                          end
              | _ => None
              end
  | Atyp atyp n => let element_size := elements_of_ftype atyp in
                   let fix aux m temp os_l os_r := (
                          match m with
                          | m'.+1 => match eval_ref_connection1 atyp temp os_l os_r with
                                    | Some temp' => aux m' temp' (os_l + element_size) (os_r + element_size)
                                    | _ => None
                                    end
                          | _ => Some temp
                          end) in aux n val (offset_l + 1) (offset_r + 1)
  | Btyp ff => eval_bundle_connection1 ff val (offset_l + 1) (offset_r + 1) 
  end
with eval_bundle_connection1 (ff : ffield) (val : hvalue) (offset_l offset_r : nat) : option hvalue :=
  match ff with
  | Fnil => Some val
  | Fflips _ Nflip ft tl => match eval_ref_connection1 ft val offset_l offset_r with
                          | Some val' => let element_size := elements_of_ftype ft in
                            eval_bundle_connection1 tl val' (offset_l + element_size) (offset_r + element_size)
                          | _ => None
                          end
  | Fflips _ Flipped ft tl => match eval_ref_connection1 ft val offset_r offset_l with
                          | Some val' => let element_size := elements_of_ftype ft in
                            eval_bundle_connection1 tl val' (offset_l + element_size) (offset_r + element_size)
                          | _ => None
                          end
  end.

Fixpoint invalidate_ft (ft : ftype) : hvalue :=
  match ft with
  | Gtyp gt => 
      let w := sizeof_fgtyp gt in 
      let w_inde := length indeterminate_val in
      if (w_inde > w) then Gval (take w indeterminate_val)
                  else Gval (zext (w - w_inde) indeterminate_val)
  | Atyp atyp n => 
      let fix invalidate_atyp (n : nat) : array_value :=
        match n with
        | 0 => Anil
        | n'.+1 => Acons (invalidate_ft atyp) (invalidate_atyp n')
        end
      in Aval (invalidate_atyp n)
  | Btyp btyp => 
      let fix invalidate_btyp (btyp : ffield) : bundle_value :=
        match btyp with
        | Fnil => Bnil
        | Fflips v f ft ff => Bflips v f (invalidate_ft ft) (invalidate_btyp ff)
        end
      in Bval (invalidate_btyp btyp)
  end.

Fixpoint eval_hfstmt (st : HiF.hfstmt) (rs ns : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option ((VM.t hvalue) * (VM.t hvalue)) :=
  match st with
  | Snode v e => match eval_hfexpr e s tmap with
                | Some val => Some (rs, VM.add v val ns)
                | _ => None
                end
  | Sfcnct r (Eref ref) => (* 考虑flip和aggr *) 
            match offset_ref r tmap 0, offset_ref ref tmap 0, Sem_HiF.type_of_ref r tmap with
            | Some offset_r, Some offset_ref, Some ft => 
                let base_r := HiF.base_ref r in let base_ref := HiF.base_ref ref in 
                (* 需要单独讨论连接发生在1个aggr内部 *)
                if base_r == base_ref then match VM.find base_r s with
                | Some val_base_r => match eval_ref_connection1 ft val_base_r offset_r offset_ref with
                    | Some val_base_r' => 
                        (* 讨论是否对应reg *)
                        match VM.find base_r tmap with
                        | Some (_, Register) => (* 更新rs *) Some (VM.add base_r val_base_r' rs, ns)
                        | Some _ => (* 更新s *) Some (rs, VM.add base_r val_base_r' ns)
                        | _ => None
                        end
                    | _ => None
                    end
                | _ => None
                end else
                match VM.find base_r s, VM.find base_ref s with
                | Some val_base_r, Some val_base_ref =>
                    match eval_ref_connection ft val_base_r val_base_ref offset_r offset_ref with
                    | Some (val_base_r', val_base_ref') => 
                        (* 分情况讨论r和ref是否对应reg *)
                        match VM.find base_r tmap, VM.find base_ref tmap with
                        | Some (_, Register), Some (_, Register) => (* 均更新rs *) 
                            Some (VM.add base_ref val_base_ref' (VM.add base_r val_base_r' rs), ns)
                        | Some (_, Register), Some _ => (* lhs更新rs, rhs更新s *) 
                            Some (VM.add base_r val_base_r' rs, VM.add base_ref val_base_ref' ns)
                        | Some _, Some (_, Register) => (* lhs更新s, rhs更新rs *) 
                            Some (VM.add base_ref val_base_ref' rs, VM.add base_r val_base_r' ns)
                        | Some _, Some _ => (* 均更新s *) 
                            Some (rs, VM.add base_ref val_base_ref' (VM.add base_r val_base_r' ns))
                        | _,_ => None
                        end
                    | _ => None
                    end
                | _, _ => None
                end
            | _, _, _ => None
            end
  | Sfcnct r e => (* 不考虑flip,考虑aggr,不区分mux和其他expr *)
                  match offset_ref r tmap 0, eval_hfexpr e s tmap with
                  | Some offset, Some new_val => let base_r := HiF.base_ref r in
                      match  VM.find base_r tmap with
                      | Some (ft, Register) => (* 更新rs *) 
                          match VM.find base_r s with
                          | Some val => match update_hvalue_by_offset val offset new_val with
                                      | Some val' => Some (VM.add base_r val' rs, ns)
                                      | _ => None
                                      end
                          | _ => None
                          end
                      | Some (ft, _) => (* 更新s *)
                          match VM.find base_r s with
                          | Some val => match update_hvalue_by_offset val offset new_val with
                                      | Some val' => Some (rs, VM.add base_r val' ns)
                                      | _ => None
                                      end
                          | _ => None
                          end
                      | _ => None
                      end
                  | _, _ => None
                  end 
  | Sinvalid r => (* 不考虑flip,考虑aggr *)
                  match offset_ref r tmap 0, Sem_HiF.type_of_ref r tmap with
                  | Some offset, Some ft => let new_val := invalidate_ft ft in
                      let base_r := HiF.base_ref r in
                      match VM.find base_r tmap with
                      | Some (ft, Register) => (* 更新rs *) 
                          match VM.find base_r s with
                          | Some val => match update_hvalue_by_offset val offset new_val with
                                      | Some val' => Some (VM.add base_r val' rs, ns)
                                      | _ => None
                                      end
                          | _ => None
                          end
                      | Some (ft, _) => (* 更新s *)
                          match VM.find base_r s with
                          | Some val => match update_hvalue_by_offset val offset new_val with
                                      | Some val' => Some (rs, VM.add base_r val' ns)
                                      | _ => None
                                      end
                          | _ => None
                          end
                      | _ => None
                      end
                  | _, _ => None
                  end 
  | Swhen cond ss_true ss_false => match eval_hfexpr cond s tmap with
                  | Some (Gval valc) => if ~~ (is_zero valc) then eval_hfstmts ss_true rs ns s tmap else eval_hfstmts ss_false rs ns s tmap
                  | _ => None
                  end
  | _ => Some (rs,ns)
  end
with eval_hfstmts (sts : HiF.hfstmt_seq) (rs ns : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option ((VM.t hvalue) * (VM.t hvalue)) :=
  match sts with
  | Qnil => Some (rs, ns)
  | Qcons st tl => match eval_hfstmt st rs ns s tmap with
                | Some (rs0, ns0) => eval_hfstmts tl rs0 ns0 s tmap
                | _ => None
                end
  end.

(* functions used to record ftype and component type *)
Fixpoint stmts_tmap (tmap : VM.t (ftype * fcomponent)) (ss : HiF.hfstmt_seq): option (VM.t (ftype * fcomponent)) :=
  match ss with
  | Qnil => Some tmap
  | Qcons s ss' => match stmt_tmap tmap s with
      | Some tmap' => stmts_tmap tmap' ss'
      | None => None
      end
  end
with stmt_tmap (tmap : VM.t (ftype * fcomponent)) (s : HiF.hfstmt) : option (VM.t (ftype * fcomponent)) :=
  match s with
  | Sskip => Some tmap
  | Sfcnct _ _ => Some tmap
  | Sinvalid _ => Some tmap
  | Smem _ _ => Some tmap
  | Sinst _ _ => Some tmap
  | Swire v t => match VM.find v tmap with
      | None => Some (VM.add v (t, Wire) tmap)
      | _ => None
      end
  | Sreg v reg => match VM.find v tmap, type_of_hfexpr (clock reg) tmap with
      | None, Some _ => Some (VM.add v ((type reg), Register) tmap)
      | _, _ => None
      end
  | Snode v expr => match VM.find v tmap, type_of_hfexpr expr tmap with
                  | None, Some ft => Some (VM.add v (ft, Node) tmap)
                  | _, _ => None
                  end
  | Swhen cond ss_true ss_false =>
      match type_of_hfexpr cond tmap, stmts_tmap tmap ss_true with
      | Some (Gtyp _), Some tmap_true => stmts_tmap tmap_true ss_false 
      | _, _ => None
      end
  end.
  
Fixpoint ports_tmap (tmap : VM.t (ftype * fcomponent)) (pp : seq HiF.hfport) : option (VM.t (ftype * fcomponent)) :=
  match pp with
  | [::] => Some tmap
  | Finput v t :: pp' => match VM.find v tmap with
          | Some _ => None
          | None => ports_tmap (VM.add v (t, In_port) tmap) pp'
          end
  | Foutput v t :: pp' => match VM.find v tmap with
          | Some _ => None
          | None => ports_tmap (VM.add v (t, Out_port) tmap) pp'
          end
  end.    

Definition module_tmap (tmap : VM.t (ftype * fcomponent)) (m : HiF.hfmodule) : option (VM.t (ftype * fcomponent)) :=
  match m with
  | FInmod _ ps ss => match ports_tmap tmap ps with
              | Some pmap => stmts_tmap pmap ss
              | None => None
              end
  | _ => None
  end.

Fixpoint modules_tmap (tmap : VM.t (ftype * fcomponent)) (ml : seq HiF.hfmodule) : option (VM.t (ftype * fcomponent)) :=
  match ml with
  | nil => Some tmap
  | hd :: tl => match module_tmap tmap hd with
              | Some tmap' => modules_tmap tmap' tl
              | _ => None
              end
  end.

Definition circuit_tmap (c : HiF.hfcircuit) : option (VM.t (ftype * fcomponent)) :=
  match c with
  | Fcircuit v ml => modules_tmap (VM.empty (ftype * fcomponent)) ml
  end.

Fixpoint init_dclrs (ss : HiF.hfstmt_seq) (valmap : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
  match ss with
  | Qnil => valmap
  | Qcons s ss' => init_dclrs ss' (init_dclr s valmap tmap) tmap
  end
with init_dclr (s : HiF.hfstmt) (valmap : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
  match s with
  | Swire v t => VM.add v (ftext0 t) valmap
  | Snode v e => match eval_hfexpr e valmap tmap with(* e中被用到的变量应该已被赋初值0,则一定有值 *)
                | Some val => VM.add v val valmap
                | _ => valmap
                end
  | Swhen cond ss_true ss_false => init_dclrs ss_false (init_dclrs ss_true valmap tmap) tmap
  | _ => valmap
  end.

(*Fixpoint init_registers (ss : HiF.hfstmt_seq) (valmap rs : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
  match ss with
  | Qnil => rs
  | Qcons s ss' => init_registers ss' valmap (init_register s valmap rs tmap) tmap
  end
with init_register (s : HiF.hfstmt) (valmap rs : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
  match s with
  | Sreg v reg => match reset reg with
      | NRst => rs
      | Rst rst_sig rst_val => (* asyncreset only const reset value *)
          match eval_hfexpr rst_val valmap tmap with 
          | Some val => VM.add v val rs
          | _ => rs
          end
      end
  | Swhen cond ss_true ss_false =>
      match eval_hfexpr cond valmap tmap with
      | Some (Gval valc) => if ~~ (is_zero valc) then init_registers ss_true valmap rs tmap else init_registers ss_false valmap rs tmap
      | _ => rs
      end 
  | _ => rs
  end.*)

Definition update_values (rs : VM.t hvalue) (s : VM.t hvalue) : VM.t hvalue := 
  VM.fold (fun key value temps => VM.add key value temps) rs s.

Fixpoint iterate (n : nat) (func : VM.t hvalue -> VM.t hvalue -> VM.t hvalue -> VM.t (ftype * fcomponent) -> option (VM.t hvalue * VM.t hvalue))
  (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option (VM.t hvalue) :=
  match n with
  | 0 => Some s
  | n'.+1 => match func (VM.empty hvalue) (VM.empty hvalue) s tmap with
            | Some (_, ns) => (* everytime we start with an empty map to record the values to be updated in the next iteration *) 
              let s_upd := update_values ns s in
              if VM.equal (fun val1 val2 => hvalue_eqn val1 val2) s_upd s (* LFP *) then Some s_upd else iterate n' func s_upd tmap
            | _ => None
            end
  end.

Definition compute_Sem (c : HiF.hfcircuit) (inputs : VM.t hvalue) (reg_init : VM.t hvalue) : option (VM.t hvalue * VM.t hvalue) :=
  (* inputs signal and register should update during a rising edge and keep during the iteration *)
  (* compute the value connected to registers according to the stable state, return it as a new reg_init for the next clock cycle *)
  (* the return value is 1) the table state of all components, 2) the to-be-updated values of all registers *)
  match circuit_tmap c, c with
  | Some tmap, Fcircuit _ [::(FInmod _ ps ss)] => 
        let s := update_values reg_init inputs in (* value of inputs and registers should keep during the iteration, wait until the next rising edge comes. *)
        let init_s := init_dclrs ss s tmap in (* only combinational components are initialized *)
        match iterate n (eval_hfstmts ss) init_s tmap with (* only combinational components are iterately computed *)
        | Some s0 => match eval_hfstmts ss (VM.empty hvalue) (VM.empty hvalue) s0 tmap with
            (* compute the registers' new value according to the stable state *)
            | Some (rs, _) => Some (s0, rs) 
            | _ => None
            end
        | _ => None
        end
  | _, _ => None
  end.
  
End Sem_HiF.

Module Sem_HiFP.

Fixpoint type_of_hfexpr (e : HiFP.hfexpr) (tmap: PVM.t (fgtyp * fcomponent)) : option fgtyp :=
  match e with
  | Econst t c => Some t
  | Eref (Eid v) => match PVM.find v tmap with
                    | Some (gt, _) => Some gt
                    | _ => None
                    end
  | Eref _ => None
  | Ecast AsUInt e1 => match type_of_hfexpr e1 tmap with
                        | Some (Fsint w)
                        | Some (Fuint w) => Some (Fuint w)
                        | Some Fclock
                        | Some Freset
                        | Some Fasyncreset => Some (Fuint 1)
                        | _ => None
                        end
  | Ecast AsSInt e1 => match type_of_hfexpr e1 tmap with
                        | Some (Fsint w)
                        | Some (Fuint w) => Some (Fsint w)
                        | Some Fclock
                        | Some Freset
                        | Some Fasyncreset => Some (Fsint 1)
                        | _ => None
                        end
  | Ecast AsClock e1 => match type_of_hfexpr e1 tmap with
                        | Some _ => Some Fclock
                        | _ => None
                        end
  | Ecast AsAsync e1 => match type_of_hfexpr e1 tmap with
                        | Some _ => Some Fasyncreset
                        | _ => None
                        end
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Fsint w) => Some (Fsint (maxn w n))
                              | Some (Fuint w) => Some (Fuint (maxn w n))
                              | _ => None
                              end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Fsint w) => Some (Fsint (w + n))
                              | Some (Fuint w) => Some (Fuint (w + n))
                              | _ => None
                              end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Fsint w) => Some (Fsint (maxn (w - n) 1))
                              | Some (Fuint w) => Some (Fuint (maxn (w - n) 0))
                              | _ => None
                              end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr e1 tmap with
                          | Some (Fsint w) => Some (Fsint w)
                          | Some (Fuint w) => Some (Fsint (w + 1))
                          | _ => None
                          end
  | Eprim_unop Uneg e1 => match type_of_hfexpr e1 tmap with
                          | Some (Fsint w)
                          | Some (Fuint w) => Some (Fsint (w + 1))
                          | _ => None
                          end
  | Eprim_unop Unot e1 => match type_of_hfexpr e1 tmap with
                          | Some (Fsint w)
                          | Some (Fuint w) => Some (Fuint w)
                          | _ => None
                          end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 tmap with
                                    | Some (Fsint w)
                                    | Some (Fuint w) =>
                                        if (n2 <= n1) && (n1 < w) then Some (Fuint (n1 - n2 + 1))
                                                                  else None
                                    | _ => None
                                    end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (Fsint w)
                                | Some (Fuint w) =>
                                    if n <= w then Some (Fuint n)
                                              else None
                                | _ => None
                                end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (Fsint w)
                                | Some (Fuint w) =>
                                    if n <= w then Some (Fuint (w - n))
                                              else None
                                | _ => None
                                end
  | Eprim_unop _ e1 => match type_of_hfexpr e1 tmap with
                        | Some (Fsint _)
                        | Some (Fuint _) => Some (Fuint 1)
                        | _ => None
                        end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                    | Some (Fsint _), Some (Fsint _)
                                    | Some (Fuint _), Some (Fuint _) => Some (Fuint 1)
                                    | _, _ => None
                                    end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Fuint w1), Some (Fuint w2) => Some (Fuint (maxn w1 w2 + 1))
                              | Some (Fsint w1), Some (Fsint w2) => Some (Fsint (maxn w1 w2 + 1))
                              | _, _ => None
                              end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Fuint w1), Some (Fuint w2) => Some (Fuint (w1 + w2))
                              | Some (Fsint w1), Some (Fsint w2) => Some (Fsint (w1 + w2))
                              | _, _ => None
                              end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Fuint w1), Some (Fuint w2) => Some (Fuint w1)
                                | Some (Fsint w1), Some (Fsint w2) => Some (Fsint (w1 + 1))
                                | _, _ => None
                                end
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Fuint w1), Some (Fuint w2) => Some (Fuint (minn w1 w2))
                                | Some (Fsint w1), Some (Fsint w2) => Some (Fsint (minn w1 w2))
                                | _, _ => None
                                end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Fuint w1), Some (Fuint w2) => Some (Fuint (2 ^ w2 + w1 - 1))
                                | Some (Fsint w1), Some (Fuint w2) => Some (Fsint (2 ^ w2 + w1 - 1))
                                | _, _ => None
                                end
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Fuint w1), Some (Fuint w2) => Some (Fuint w1)
                                | Some (Fsint w1), Some (Fuint w2) => Some (Fsint w1)
                                | _, _ => None
                                end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Fuint w1), Some (Fuint w2)
                              | Some (Fsint w1), Some (Fsint w2) => Some (Fuint (w1 + w2))
                              | _, _ => None
                              end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Fuint w1), Some (Fuint w2)
                              | Some (Fsint w1), Some (Fsint w2) => Some (Fuint (maxn w1 w2))
                              | _, _ => None
                              end
  | Emux c e1 e2 => match type_of_hfexpr c tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                    | Some (Fuint _), Some (Fuint w1), Some (Fuint w2) => Some (Fuint (maxn w1 w2))
                    | Some (Fuint _), Some (Fsint w1), Some (Fsint w2) => Some (Fsint (maxn w1 w2))
                    | _, _, _ => None
                    end
  end.

(* Expression evaluation, value *)
Fixpoint eval_hfexpr (exp : HiFP.hfexpr) (s : PVM.t bitseq) (tmap: PVM.t (fgtyp * fcomponent)) : option bitseq :=
  match exp with
  | Econst t c => match t with
                  | Fuint w1 => if (size c) > w1 then None else Some (zext (w1 - size c) c)
                  | Fsint w2 => if (size c) > w2 then None else Some (sext (w2 - size c) c)
                  | _ => None
                  end
  | Eref (Eid v) => PVM.find v s
  | Eref _ => None
  | Ecast AsUInt e 
  | Ecast AsSInt e => eval_hfexpr e s tmap
  | Ecast AsClock e  
  | Ecast AsAsync e => match eval_hfexpr e s tmap with Some val => Some [::lsb val] | _ => None end
  | Eprim_binop b e1 e2 =>
      match eval_hfexpr e1 s tmap, eval_hfexpr e2 s tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
      | Some val1, Some val2, Some gt1, Some gt2 => 
          let val := ebinop_op b gt1 gt2 val1 val2 in Some val
      | _, _, _, _ => None
      end
  | Eprim_unop u e =>
      match eval_hfexpr e s tmap, type_of_hfexpr e tmap with
      | Some val1, Some gt1 =>
          let val := eunop_op u gt1 val1 in Some val
      | _, _ => None
      end
  | Emux c e1 e2 => 
      match eval_hfexpr c s tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap, eval_hfexpr e1 s tmap, eval_hfexpr e2 s tmap with
      | Some valc, Some (Fuint w1), Some (Fuint w2), Some val1, Some val2 => if ~~ (is_zero valc) then Some (zext ((max w1 w2) - w1) val1)
                                                                             else Some (zext ((max w1 w2) - w2) val2)
      | Some valc, Some (Fsint w1), Some (Fsint w2), Some val1, Some val2 => if ~~ (is_zero valc) then Some (sext ((max w1 w2) - w1) val1)
                                                                             else Some (sext ((max w1 w2) - w2) val2)
      | _, _, _, _, _ => None
      end
  end.

Fixpoint eval_hfstmt (st : HiFP.hfstmt) (rs ns : PVM.t bitseq) (s : PVM.t bitseq) (tmap: PVM.t (fgtyp * fcomponent)) : option ((PVM.t bitseq) * (PVM.t bitseq)) :=
  match st with
  | Snode v e => match eval_hfexpr e s tmap with
                | Some val => Some (rs, PVM.add v val ns)
                | _ => None
                end
  | Sreg v _ => match PVM.find v s with
                | Some val => Some (PVM.add v val rs, ns)
                | _ => None
                end
  | Sfcnct (Eid r) e => match PVM.find r tmap, eval_hfexpr e s tmap with
                        | Some (_, Register), Some val => (* 更新rs *) Some (PVM.add r val rs, ns)
                        | Some _, Some val => (* 更新s *) Some (rs, PVM.add r val ns)
                        | _, _ => None
                        end
  | Sinvalid (Eid r) => let w_inde := length indeterminate_val in
                        match PVM.find r tmap with
                        | Some (gt, Register) => (* 更新rs *) 
                            let w := sizeof_fgtyp gt in 
                            if (w_inde > w) then Some (PVM.add r (take w indeterminate_val) rs, ns)
                            else Some (PVM.add r (zext (w - w_inde) indeterminate_val) rs, ns)
                        | Some (gt, _) => 
                            let w := sizeof_fgtyp gt in 
                            if (w_inde > w) then Some (rs, PVM.add r (take w indeterminate_val) ns)
                            else Some (rs, PVM.add r (zext (w - w_inde) indeterminate_val) ns)
                        | _ => None
                        end
  | Swhen cond ss_true ss_false => match eval_hfexpr cond s tmap with
                  | Some valc => if ~~ (is_zero valc) then eval_hfstmts ss_true rs ns s tmap else eval_hfstmts ss_false rs ns s tmap
                  | _ => None
                  end
  | _ => Some (rs,ns)
  end
with eval_hfstmts (sts : HiFP.hfstmt_seq) (rs ns : PVM.t bitseq) (s : PVM.t bitseq) (tmap: PVM.t (fgtyp * fcomponent)) : option ((PVM.t bitseq) * (PVM.t bitseq)) :=
  match sts with
  | Qnil => Some (rs, ns)
  | Qcons st tl => match eval_hfstmt st rs ns s tmap with
                | Some (rs0, ns0) => eval_hfstmts tl rs0 ns0 s tmap
                | _ => None
                end
  end.
  
(* functions used to record ftype and component type *)
Fixpoint stmts_tmap (tmap : PVM.t (fgtyp * fcomponent)) (ss : HiFP.hfstmt_seq): option (PVM.t (fgtyp * fcomponent)) :=
  match ss with
  | Qnil => Some tmap
  | Qcons s ss' => match stmt_tmap tmap s with
      | Some tmap' => stmts_tmap tmap' ss'
      | None => None
      end
  end
with stmt_tmap (tmap : PVM.t (fgtyp * fcomponent)) (s : HiFP.hfstmt) : option (PVM.t (fgtyp * fcomponent)) :=
  match s with
  | Sskip => Some tmap
  | Sfcnct _ _ => Some tmap
  | Sinvalid _ => Some tmap
  | Smem _ _ => Some tmap
  | Sinst _ _ => Some tmap
  | Swire v (Gtyp t) => match PVM.find v tmap with
      | None => Some (PVM.add v (t, Wire) tmap)
      | _ => None
      end
  | Swire v _ => None
  | Sreg v reg => match PVM.find v tmap, type_of_hfexpr (clock reg) tmap, type reg with
      | None, Some _, Gtyp gt => Some (PVM.add v (gt, Register) tmap)
      | _, _, _ => None
      end
  | Snode v expr => match PVM.find v tmap, type_of_hfexpr expr tmap with
                  | None, Some ft => Some (PVM.add v (ft, Node) tmap)
                  | _, _ => None
                  end
  | Swhen _ ss_true ss_false =>
      match stmts_tmap tmap ss_true with
      | Some tmap_true => stmts_tmap tmap_true ss_false 
      | _ => None
      end
  end.

Fixpoint ports_tmap (tmap : PVM.t (fgtyp * fcomponent)) (pp : seq HiFP.hfport) : option (PVM.t (fgtyp * fcomponent)) :=
  match pp with
  | [::] => Some tmap
  | Finput v (Gtyp t) :: pp' => match PVM.find v tmap with
          | Some _ => None
          | None => ports_tmap (PVM.add v (t, In_port) tmap) pp'
          end
  | Foutput v (Gtyp t) :: pp' => match PVM.find v tmap with
          | Some _ => None
          | None => ports_tmap (PVM.add v (t, Out_port) tmap) pp'
          end
  | _ => None
  end.    

Definition module_tmap (tmap : PVM.t (fgtyp * fcomponent)) (m : HiFP.hfmodule) : option (PVM.t (fgtyp * fcomponent)) :=
  match m with
  | FInmod _ ps ss => match ports_tmap tmap ps with
              | Some pmap => stmts_tmap pmap ss
              | None => None
              end
  | _ => None
  end.

Fixpoint modules_tmap (tmap : PVM.t (fgtyp * fcomponent)) (ml : seq HiFP.hfmodule) : option (PVM.t (fgtyp * fcomponent)) :=
  match ml with
  | nil => Some tmap
  | hd :: tl => match module_tmap tmap hd with
              | Some tmap' => modules_tmap tmap' tl
              | _ => None
              end
  end.

Definition circuit_tmap (c : HiFP.hfcircuit) : option (PVM.t (fgtyp * fcomponent)) :=
  match c with
  | Fcircuit v ml => modules_tmap (PVM.empty (fgtyp * fcomponent)) ml
  end.

Fixpoint init_dclrs (ss : HiFP.hfstmt_seq) (valmap : PVM.t bitseq) (tmap: PVM.t (fgtyp * fcomponent)) : option (PVM.t bitseq) := 
  match ss with
  | Qnil => Some valmap
  | Qcons s ss' => match init_dclr s valmap tmap with
                  | Some valmap' => init_dclrs ss' valmap' tmap
                  | _ => None
                  end
  end
with init_dclr (s : HiFP.hfstmt) (valmap : PVM.t bitseq) (tmap: PVM.t (fgtyp * fcomponent)) : option (PVM.t bitseq) := 
  match s with
  | Swire v (Gtyp gt) => let w := sizeof_fgtyp gt in Some (PVM.add v (zeros w) valmap)
  | Swire v _ => None
  | Snode v e => match eval_hfexpr e valmap tmap with(* e中被用到的变量应该已被赋初值0,则一定有值 *)
                | Some val => Some (PVM.add v val valmap)
                | _ => None
                end
  | Swhen cond ss_true ss_false => match init_dclrs ss_true valmap tmap with
                | Some valmap' => init_dclrs ss_false valmap' tmap
                | _ => None
                end
  | _ => Some valmap
  end.

(*Fixpoint init_registers (ss : HiFP.hfstmt_seq) (valmap rs : PVM.t bits) (tmap: PVM.t (fgtyp * fcomponent)) : PVM.t bits := 
  match ss with
  | Qnil => rs
  | Qcons s ss' => init_registers ss' valmap (init_register s valmap rs tmap) tmap
  end
with init_register (s : HiFP.hfstmt) (valmap rs : PVM.t bits) (tmap: PVM.t (fgtyp * fcomponent)) : PVM.t bits := 
  match s with
  | Sreg v reg => match reset reg with
      | NRst => rs
      | Rst rst_sig rst_val => (* 本质这里需要区分同步/异步rst *)
          match eval_hfexpr rst_val valmap tmap with 
          | Some val => PVM.add v val rs
          | _ => rs
          end
      end
  | Swhen cond ss_true ss_false =>
      match eval_hfexpr cond valmap tmap with
      | Some valc => if ~~ (is_zero valc) then init_registers ss_true valmap rs tmap else init_registers ss_false valmap rs tmap
      | _ => rs
      end 
  | _ => rs
  end.*)

Definition update_values (rs s: PVM.t bitseq) : PVM.t bitseq := 
  PVM.fold (fun key value temps => PVM.add key value temps) rs s.

Fixpoint iterate (n : nat) (func : PVM.t bitseq -> PVM.t bitseq -> PVM.t bitseq -> PVM.t (fgtyp * fcomponent) -> option (PVM.t bitseq * PVM.t bitseq))
  (s : PVM.t bitseq) (tmap: PVM.t (fgtyp * fcomponent)) : option (PVM.t bitseq) :=
  match n with
  | 0 => Some s
  | n'.+1 => match func (PVM.empty bitseq) (PVM.empty bitseq) s tmap with
            | Some (_, ns) => (* everytime we start with an empty map to record the values to be updated in the next iteration *) 
              let s_upd := update_values ns s in
              (*if PVM.equal (fun val1 val2 => val1 == val2) s_upd s (* LFP *) then Some s_upd else*) iterate n' func s_upd tmap
            | _ => None
            end
  end.

Definition compute_Sem (c : HiFP.hfcircuit) (inputs reg_init : PVM.t bitseq) : option (PVM.t bitseq * PVM.t bitseq) :=
  match circuit_tmap c, c with
  | Some tmap, Fcircuit _ [::(FInmod _ ps ss)] => 
        let s := update_values reg_init inputs in (* value of inputs and registers should keep during the iteration, wait until the next rising edge comes. *)
        match init_dclrs ss s tmap with (* only combinational components are initialized *)
        | Some init_s => match iterate n (eval_hfstmts ss) init_s tmap with
            (* only combinational components are iterately computed *)
            | Some s0 => match eval_hfstmts ss (PVM.empty bitseq) (PVM.empty bitseq) s0 tmap with
                (* compute the registers' new value according to the stable state *)
                | Some (rs, _) => Some (s0, rs) 
                | _ => None
                end
            | _ => None
            end
        | _ => None
        end
  | _, _ => None
  end.

Definition indeterminate_cst (gt : fgtyp) : HiFP.hfexpr := 
  let w := sizeof_fgtyp gt in 
  let w_inde := length indeterminate_val in
  if (w_inde > w) then HiFP.econst gt (take w indeterminate_val)
                  else HiFP.econst gt (zext (w - w_inde) indeterminate_val).

End Sem_HiFP.

Parameter flat_valmap : (VM.t hvalue) -> (VM.t (ftype * fcomponent)) -> PVM.t bitseq.

Parameter expandConnects : HiF.hfcircuit -> option HiFP.hfcircuit.

Fixpoint expand_inport (v : VarOrder.t) (offset : nat) (flip : bool) (ft : ftype) l : seq (hfport ProdVarOrder.T) :=
  match ft with 
  | Gtyp gt => if flip then cons (HiFP.houtport (v, N.of_nat offset) ft) l 
               else cons (HiFP.hinport (v, N.of_nat offset) ft) l 
  | Atyp atyp n => let fix expand_inport_array (n : nat) (offset' : nat) l' :=
        match n with
        | 0 => l'
        | n'.+1 => expand_inport_array n' (offset' + (size_of_ftype atyp)) (expand_inport v offset' flip atyp l')
        end in expand_inport_array n offset l
  | Btyp btyp => expand_inport_btyp v offset flip btyp l
  end
with expand_inport_btyp (v : VarOrder.t) (offset : nat) (flip : bool) (btyp : ffield) l :=
  match btyp with
  | Fnil => l 
  | Fflips _ Nflip ft ff => expand_inport_btyp v (offset + (size_of_ftype ft)) flip ff (expand_inport v offset flip ft l)
  | Fflips _ Flipped ft ff => expand_inport_btyp v (offset + (size_of_ftype ft)) flip ff (expand_inport v offset (~~ flip) ft l)
  end.

Definition expand_port p l :=
    match p with
    | Finput v t => expand_inport v 0 false t l 
    | Foutput v t => expand_inport v 0 true t l
    end.

Fixpoint expand_ports (ps : seq HiF.hfport) l : seq (hfport ProdVarOrder.T) :=
  match ps with
  | nil => l
  | hd :: tl => expand_ports tl (expand_port hd l)
  end.

Fixpoint expand_wire (v : VarOrder.t) (offset : nat) (ft : ftype) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  match ft with 
  | Gtyp _ => HiFP.qrcons sts (HiFP.swire (v, N.of_nat offset) ft)
  | Atyp atyp n => let fix expand_wire_array (n : nat) (offset' : nat) l' :=
        match n with
        | 0 => l'
        | n'.+1 => expand_wire_array n' (offset' + (size_of_ftype atyp)) (expand_wire v offset' atyp l')
        end in expand_wire_array n offset sts
  | Btyp btyp => expand_wire_btyp v offset btyp sts
  end
with expand_wire_btyp (v : VarOrder.t) (offset : nat) (btyp : ffield) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  match btyp with
  | Fnil => sts
  | Fflips _ _ ft ff => expand_wire_btyp v (offset + (size_of_ftype ft)) ff (expand_wire v offset ft sts)
  end.

Fixpoint offset_of_subfield_b ft fid n : option nat :=
  match ft with
  | Fnil => None
  | Fflips v fl t fs => if fid == v then Some n else offset_of_subfield_b fs fid (n + size_of_ftype t)
  end.

(* offset of subfield/subindex recursive to the base ref *)
Fixpoint offset_ref (r : href VarOrder.T) tmap : option nat :=
  match r with
  | Eid v => Some 0
  | Esubindex v i => match Sem_HiF.type_of_ref v tmap, offset_ref v tmap with
      | Some (Atyp atyp _), Some n => Some (n + i * (size_of_ftype atyp))
      | _,_ => None
      end
  | Esubfield v f => match offset_ref v tmap, Sem_HiF.type_of_ref v tmap with
      | Some n, Some (Btyp ft) => offset_of_subfield_b ft f n
      | _, _ => None
      end
  | Esubaccess v e => None (* not supported yet *)
  end.

Fixpoint base_id (r : href VarOrder.T) : VarOrder.T :=
  match r with
  | Eid v => v 
  | Esubindex v i => base_id v 
  | Esubfield v f => base_id v 
  | Esubaccess v e => base_id v 
  end.

Definition ref2pv (r : href VarOrder.T) (tmap : VM.t (ftype * fcomponent)) : option ProdVarOrder.t :=
  let base_v := base_id r in
  match offset_ref r tmap with
  | Some os => Some (base_v, N.of_nat os)
  | None => None
  end. (* r中包含的第一个ground type的名 *)

Fixpoint expand_ground_expr (e : hfexpr VarOrder.T) (tmap :  VM.t (ftype * fcomponent)) : option (hfexpr ProdVarOrder.T) :=
  match e with
  | Eref ref => match ref2pv ref tmap with
      | Some pv => Some (Eref (Eid pv))
      | _ => None
      end
  | Econst gt bs => Some (Econst _ gt bs)
  | Ecast c e0 => match expand_ground_expr e0 tmap with
      | Some e0' => Some (Ecast c e0')
      | _ => None
      end
  | Eprim_unop op e0 => match expand_ground_expr e0 tmap with
      | Some e0' => Some (Eprim_unop op e0')
      | _ => None
      end
  | Eprim_binop op e0 e1 => match expand_ground_expr e0 tmap, expand_ground_expr e1 tmap with
      | Some e0', Some e1' => Some (Eprim_binop op e0' e1')
      | _,_ => None
      end
  | Emux c e0 e1 => match expand_ground_expr c tmap, expand_ground_expr e0 tmap, expand_ground_expr e1 tmap with
      | Some c', Some e0', Some e1' => Some (Emux c' e0' e1')
      | _, _,_ => None
      end
  end.

Fixpoint expand_reg_nrst (v : VarOrder.t) (offset : nat) (ft : ftype) (clk : hfexpr ProdVarOrder.T) (tmap :  VM.t (ftype * fcomponent)) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match ft with 
  | Gtyp _ => Some (HiFP.qrcons sts (HiFP.sreg (v, N.of_nat offset) (mk_freg ft clk (NRst _))))
  | Atyp atyp n => let fix expand_reg_nrst_array (n : nat) (offset' : nat) l' :=
        match n with
        | 0 => Some l'
        | n'.+1 => match expand_reg_nrst v offset' atyp clk tmap l' with
            | Some sts' => expand_reg_nrst_array n' (offset' + (size_of_ftype atyp)) sts'
            | _ => None
            end
        end in expand_reg_nrst_array n offset sts
  | Btyp btyp => expand_reg_nrst_btyp v offset btyp clk tmap sts
  end
with expand_reg_nrst_btyp (v : VarOrder.t) (offset : nat) (btyp : ffield) clk (tmap :  VM.t (ftype * fcomponent)) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match btyp with
  | Fnil => Some sts
  | Fflips _ _ ft ff => match expand_reg_nrst v offset ft clk tmap sts with
      | Some sts' => expand_reg_nrst_btyp v (offset + (size_of_ftype ft)) ff clk tmap sts'
      | _ => None
      end
  end.

Fixpoint list_ref (n : nat) (pv : ProdVarOrder.t) l : seq ProdVarOrder.t :=
  match n with
  | 0 => l
  | S n' => list_ref n' (fst pv, N.add (snd pv) 1%num) (cons pv l)
  end.

Fixpoint list_emux (c : HiFP.hfexpr) (ze : seq (HiFP.hfexpr * HiFP.hfexpr)) : seq HiFP.hfexpr :=
  match ze with
  | nil => nil
  | (e1, e2) :: zes => cons (HiFP.emux c e1 e2) (list_emux c zes) 
  end.

Fixpoint list_expr (e : HiF.hfexpr) (tmap : VM.t (ftype * fcomponent)) : option (seq HiFP.hfexpr) :=
  match e with
  | Eref ref => match Sem_HiF.type_of_ref ref tmap, ref2pv ref tmap with
      | Some ft, Some pv => Some (map (fun temp_pv => Eref (Eid temp_pv)) (list_ref (size_of_ftype ft) pv nil))
      | _, _ => None
      end
  | Emux c e1 e2 => match expand_ground_expr c tmap, list_expr e1 tmap, list_expr e2 tmap with
      | Some c', Some l1, Some l2 => Some (list_emux c' (zip l1 l2) )
      | _, _, _ => None
      end
  | _ => match expand_ground_expr e tmap with
      | Some e' => Some [::e']
      | _ => None
      end
  end.

Fixpoint list_ftype (ft : ftype) (l : list ftype) : list ftype :=
    match ft with
    | Gtyp t => cons ft l
    | Atyp t n => (flatten (List.repeat (list_ftype t nil) n)) ++ l
    | Btyp b => ftype_list_btyp_all b l
    end
  with ftype_list_btyp_all (b : ffield) (l : list ftype) : list ftype :=
         match b with
         | Fnil => l
         | Fflips v fl t fs => ftype_list_btyp_all fs (list_ftype t l)
         end.

Fixpoint expand_reg_rst (n : nat) (v : VarOrder.t) (clk rst_sig : hfexpr ProdVarOrder.T) (rst_val : seq (hfexpr ProdVarOrder.T)) (ft_l : seq ftype) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match n, rst_val, ft_l with
  | 0, nil, nil => Some sts
  | S n', hd :: tl, ft :: ft_l' => expand_reg_rst n' v clk rst_sig tl ft_l' (HiFP.qcons (HiFP.sreg (v, N.of_nat n') (mk_freg ft clk (Rst rst_sig hd))) sts)
  | _, _, _ => None
  end.

Definition expand_reg (v : VarOrder.t) (r : hfreg VarOrder.T) (tmap : VM.t (ftype * fcomponent)) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match r with
  | mk_freg ft clk NRst => match expand_ground_expr clk tmap with
      | Some clk_p => expand_reg_nrst v 0 ft clk_p tmap sts
      | _ => None
      end
  | mk_freg (Gtyp gt) clk (Rst rst_sig rst_val) => 
      match expand_ground_expr clk tmap, expand_ground_expr rst_sig tmap, expand_ground_expr rst_val tmap with
      | Some clk_p, Some rst_sig_p, Some rst_val_p => Some (HiFP.qrcons sts (HiFP.sreg (v, 0%num) (mk_freg (Gtyp gt) clk_p (Rst rst_sig_p rst_val_p))))
      | _, _, _ => None
      end
  | mk_freg ft clk (Rst rst_sig rst_val) => match expand_ground_expr clk tmap, expand_ground_expr rst_sig tmap, list_expr rst_val tmap with
      | Some clk_p, Some rst_sig_p, Some rst_val_l => expand_reg_rst (size_of_ftype ft) v clk_p rst_sig_p rst_val_l (list_ftype ft nil) sts
      | _, _, _ => None
      end
  end.

Fixpoint expand_invalid (n : nat) (pv : ProdVarOrder.t) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match n with
  | 0 => Some sts
  | S n' => expand_invalid n' (fst pv, N.add (snd pv) 1%num) (HiFP.qrcons sts (HiFP.sinvalid (Eid pv)))
  end.

Fixpoint expand_node (v : VarOrder.t) (offset : nat) (el : seq HiFP.hfexpr) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match el with
  | nil => Some sts
  | hd :: tl => expand_node v (offset + 1) tl (HiFP.qrcons sts (HiFP.snode (v, N.of_nat offset) hd))
  end.

Fixpoint expand_fcnct_nflip (pv : ProdVarOrder.t) (el : seq HiFP.hfexpr) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match el with
  | nil => Some sts
  | hd :: tl => expand_fcnct_nflip (fst pv, N.add (snd pv) 1%num) tl (HiFP.qrcons sts (HiFP.sfcnct (Eid pv) hd))
  end.

Fixpoint expand_fcnct (pv0 pv1 : ProdVarOrder.t) (offset : nat) (flip : bool) (ft : ftype) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match ft with 
  | Gtyp _ => if flip then Some (HiFP.qrcons sts (HiFP.sfcnct (HiFP.eid (fst pv1, (snd pv1) + (N.of_nat offset))%num) 
                  (Eref (HiFP.eid (fst pv0, N.add (snd pv0) (N.of_nat offset))))))
              else Some (HiFP.qrcons sts (HiFP.sfcnct (HiFP.eid (fst pv0, N.add (snd pv0) (N.of_nat offset))) 
                  (Eref (HiFP.eid (fst pv1, N.add (snd pv1) (N.of_nat offset))))))
  | Atyp atyp n => let fix expand_fcnct_array (n : nat) (offset' : nat) l' :=
        match n with
        | 0 => Some l'
        | n'.+1 => match expand_fcnct pv0 pv1 offset' flip atyp l' with
            | Some sts' => expand_fcnct_array n' (offset' + (size_of_ftype atyp)) sts'
            | _ => None
            end
        end in expand_fcnct_array n offset sts
  | Btyp btyp => expand_fcnct_btyp pv0 pv1 offset flip btyp sts
  end
with expand_fcnct_btyp (pv0 pv1 : ProdVarOrder.t) (offset : nat) flip (btyp : ffield) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match btyp with
  | Fnil => Some sts
  | Fflips _ Nflip ft ff => match expand_fcnct pv0 pv1 offset flip ft sts with
      | Some sts' => expand_fcnct_btyp pv0 pv1 (offset + (size_of_ftype ft)) flip ff sts'
      | _ => None
      end
  | Fflips _ Flipped ft ff => match expand_fcnct pv0 pv1 (~~ flip) flip ft sts with
      | Some sts' => expand_fcnct_btyp pv0 pv1 (offset + (size_of_ftype ft)) flip ff sts'
      | _ => None
      end
  end.

Fixpoint expandconnects_stmt (s : HiF.hfstmt) (tmap : VM.t (ftype * fcomponent)) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match s with
  | Sskip 
  | Smem _ _ => Some (HiFP.qrcons sts HiFP.sskip) (* TBD *)
  | Sinst v mv => Some (HiFP.qrcons sts (HiFP.sinst (v, N0) (mv, N0)))
  | Swire v t => Some (expand_wire v 0 t sts)
  | Sreg v r => expand_reg v r tmap sts
  | Sinvalid ref => match Sem_HiF.type_of_ref ref tmap, ref2pv ref tmap with
      | Some ft, Some pv => expand_invalid (size_of_ftype ft) pv sts
      | _, _ => None
      end
  | Snode v e => match list_expr e tmap with
      | Some el => expand_node v 0 (rev el) sts
      | _ => None
      end
  | Sfcnct ref0 (Eref ref1) => match ref2pv ref0 tmap, ref2pv ref1 tmap, Sem_HiF.type_of_ref ref0 tmap with
      | Some pv0, Some pv1, Some ft => expand_fcnct pv0 pv1 0 false ft sts 
      | _, _, _ => None
      end
  | Sfcnct ref e => match ref2pv ref tmap, list_expr e tmap with
      | Some pv, Some el => expand_fcnct_nflip pv (rev el) sts
      | _,_ => None
      end
  | Swhen c ss1 ss2 => match expand_ground_expr c tmap, expandconnects_stmts ss1 tmap HiFP.qnil, expandconnects_stmts ss2 tmap HiFP.qnil with
      | Some c', Some ss1', Some ss2' => Some (HiFP.qrcons sts (Swhen c' ss1' ss2'))
      | _, _, _ => None
      end
  end
with expandconnects_stmts (ss : HiF.hfstmt_seq) (tmap : VM.t (ftype * fcomponent)) (sts : HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
  match ss with
  | Qnil => Some sts
  | Qcons s ss =>
    match expandconnects_stmt s tmap sts with
    | Some sts' => expandconnects_stmts ss tmap sts'
    | None => None
    end
  end.

Definition expandconnects_fmodule (m : HiF.hfmodule) (tmap : VM.t (ftype * fcomponent)) : option HiFP.hfmodule :=
    match m with
    | FInmod v ps ss => let ps' := expand_ports ps nil in
        match expandconnects_stmts ss tmap HiFP.qnil with
        | Some sts => Some (HiFP.hfinmod (v, N0) (rev ps') sts)
        | _ => None
        end
    | m => None
    end.

Definition expandconnects (c : HiF.hfcircuit) : option HiFP.hfcircuit :=
  match c, Sem_HiF.circuit_tmap c with
  | Fcircuit v [:: m], Some tmap => match expandconnects_fmodule m tmap with
    | Some fm => Some (HiFP.fcircuit (v,N0) [:: fm])
    | _ => None
    end
  | _, _ => None
  end.

Section ExpandWhens.

(* a type to indicate connects *)
Inductive def_expr : Type :=
| D_invalidated : fgtyp -> def_expr (* a "is invalid" statement *)
| D_fexpr : HiFP.hfexpr -> def_expr (* connected *)
.

(* equality of def_expr is decidable [because equality of hfexpr is decidable] *)
Lemma def_expr_eq_dec : forall {x y : def_expr}, {x = y} + {x <> y}.
Proof.
  decide equality.
  apply fgtyp_eq_dec.
Admitted.

Definition def_expr_eqn (x y : def_expr) : bool :=
match x, y with
| D_invalidated gt1, D_invalidated gt2 => gt1 == gt2
| D_fexpr expr1, D_fexpr expr2 => expr1 == expr2
| _, _ => false
end.

Lemma def_expr_eqP : Equality.axiom def_expr_eqn.
Proof.
unfold Equality.axiom, def_expr_eqn.
intros ; induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
case Eq: (f == f0).
1-2: move /fgtyp_eqP : Eq => Eq.
apply ReflectT ; replace f0 with f ; reflexivity.
apply ReflectF ; injection ; apply Eq.
case Eq: (h == h0).
all: move /hfexpr_eqP : Eq => Eq.
apply ReflectT ; replace h0 with h ; reflexivity.
apply ReflectF ; injection ; apply Eq.
Qed.

Definition combine_when_connections
    (* a helper function that takes two connection maps, generated
       by the two branches of a when statement, and combines them
       into one connection map containing suitable multiplexers *)
    (cond           : HiFP.hfexpr)    (* condition under which to decide whether to take the value from true_conn_map *)
    (true_conn_map  : PVM.t def_expr) (* connections made before or in the true branch *)
    (false_conn_map : PVM.t def_expr) (* connections made before or in the false branch *)
:   PVM.t def_expr
:=  PVM.map2 (fun true_expr false_expr : option def_expr =>
                      match true_expr, false_expr with
                      | Some (D_fexpr te), Some (D_fexpr fe) =>
                          if te == fe then true_expr
                          else Some (D_fexpr (Emux cond te fe))
                      | None, _ => false_expr 
                      | _, None => true_expr
                      | Some (D_invalidated gt), Some (D_fexpr fe) => 
                          (*if (Sem_HiFP.indeterminate_cst gt) == fe then Some (D_fexpr fe)
                          else*) Some (D_fexpr (Emux cond (Sem_HiFP.indeterminate_cst gt) fe)) 
                      | Some (D_fexpr te), Some (D_invalidated gt) => 
                          (*if te == (Sem_HiFP.indeterminate_cst gt) then Some (D_fexpr te)
                          else*) Some (D_fexpr (Emux cond te (Sem_HiFP.indeterminate_cst gt))) 
                      | Some (D_invalidated gt0), Some (D_invalidated gt1) => 
                          (*if gt0 == gt1 then Some (D_fexpr (Sem_HiFP.indeterminate_cst gt0))
                          else*) Some (D_fexpr (Emux cond (Sem_HiFP.indeterminate_cst gt0) (Sem_HiFP.indeterminate_cst gt1)))
                      end)
             true_conn_map false_conn_map.
(*
Definition combine_when_connections
    (* a helper function that takes two connection maps, generated
       by the two branches of a when statement, and combines them
       into one connection map containing suitable multiplexers *)
    (cond           : HiFP.hfexpr)    (* condition under which to decide whether to take the value from true_conn_map *)
    (true_conn_map  : PVM.t def_expr) (* connections made before or in the true branch *)
    (false_conn_map : PVM.t def_expr) (* connections made before or in the false branch *)
:   PVM.t def_expr
:=  PVM.map2 (fun true_expr false_expr : option def_expr =>
                      match true_expr, false_expr with
                      | Some (D_fexpr te), Some (D_fexpr fe) =>
                          if te == fe then true_expr
                          else Some (D_fexpr (Emux cond te fe))
                      | None, _ => false_expr 
                      | _, None => true_expr
                      | Some (D_invalidated gt), Some (D_fexpr fe) => match gt with
                          | Fuint _ 
                          | Fsint _ => Some (D_fexpr (Emux cond (Sem_HiFP.indeterminate_cst gt) fe)) 
                          | _ => None
                          end
                      | Some (D_fexpr te), Some (D_invalidated gt) => match gt with
                          | Fuint _ 
                          | Fsint _ => Some (D_fexpr (Emux cond te (Sem_HiFP.indeterminate_cst gt))) 
                          | _ => None
                          end
                      | Some (D_invalidated gt0), Some (D_invalidated gt1) => match gt0, gt1 with
                          | Fuint _, Fuint _  
                          | Fuint _, Fsint _  
                          | Fsint _, Fuint _  
                          | Fsint _, Fsint _ => 
                          Some (D_fexpr (Emux cond (Sem_HiFP.indeterminate_cst gt0) (Sem_HiFP.indeterminate_cst gt1)))
                          | _, _ => None
                          end
                      end)
             true_conn_map false_conn_map.
*)
Fixpoint ExpandBranches_funs
(* split a statement sequence (possibly containing when
   statements) into a connection map.  The output does not contain when statements. *)
(ss           : HiFP.hfstmt_seq)   (* sequence of statements being translated *)
(old_conn_map : PVM.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
(tmap : PVM.t (fgtyp * fcomponent))
:   option (PVM.t def_expr)
(* old_conn_map, extended with the connection statements in ss *)
:=  match ss with
| Qnil => Some old_conn_map
| Qcons s ss =>
    match ExpandBranch_fun s old_conn_map tmap with
    | Some temp_conn_map =>
        ExpandBranches_funs ss temp_conn_map tmap
    | None => None
    end
end
with ExpandBranch_fun
(* split a single statement (possibly consisting of a when
   statement) into a connection map.  The output does not contain when statements. *)
(s            : HiFP.hfstmt)       (* a single statement being translated *)
(old_conn_map : PVM.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
(tmap : PVM.t (fgtyp * fcomponent))
:   option (PVM.t def_expr)
(* old_conn_map, extended with the connection statements in s *)
:=  match s with
| Sskip => Some old_conn_map
| Sreg var reg =>
    match type reg with
    | Gtyp gt => Some (PVM.add var (D_fexpr (Eref (Eid var))) old_conn_map)
    | _ => None
    end
| Sfcnct (Eid var) expr => Some (PVM.add var (D_fexpr expr) old_conn_map)
| Sfcnct _ expr => None
| Sinvalid (Eid var) => match PVM.find var tmap with
  | Some (gt, _) => Some (PVM.add var (D_invalidated gt) old_conn_map)
  | _ => None
  end
| Sinvalid _ => None
| Swhen cond ss_true ss_false =>
    match ExpandBranches_funs ss_true old_conn_map tmap with
    | Some true_conn_map =>
        match ExpandBranches_funs ss_false old_conn_map tmap with
        | Some false_conn_map =>
            Some (combine_when_connections cond true_conn_map false_conn_map)
        | _ => None
        end
    | _ => None
    end
| _ => Some old_conn_map (* wire, mem, inst, node *)
end.

Definition convert_to_connect_stmt
    (* convert one entry in a map of connections to a connect statement,
       helper function for PVM.fold *)
    (v : PVM.key) (* key of the connection *)
    (d : def_expr) (* value of the connection *)
    (old_ss : HiFP.hfstmt_seq) (* old sequence of connect statements *)
:   HiFP.hfstmt_seq (* returns old_ss, extended with assigning d to v *)
:=  match d with
    | D_invalidated _ => Qcons (Sinvalid (Eid v)) old_ss
    | D_fexpr e => Qcons (Sfcnct (Eid v) e) old_ss
    end.

Fixpoint component_stmts_of (ss : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
(* extracts from ss the statements that define components *)
match ss with
| Qnil => ss 
| Qcons s ss' => Qcat (component_stmt_of s) (component_stmts_of ss')
end
with component_stmt_of (s : HiFP.hfstmt) : HiFP.hfstmt_seq :=
match s with
| Sskip
| Sfcnct _ _
| Sinvalid _ => Qnil ProdVarOrder.T
| Swire _ _
| Sreg _ _
| Snode _ _
| Smem _ _
| Sinst _ _ => Qcons s (Qnil ProdVarOrder.T)
| Swhen _ ss_true ss_false => Qcat (component_stmts_of ss_true) (component_stmts_of ss_false)
end.

Definition convert_to_connect_stmts
    (* converts a map of connections to connect statements *)
    (conn_map : PVM.t def_expr) (* map that needs to be converted *)
:   HiFP.hfstmt_seq
:=  PVM.fold convert_to_connect_stmt conn_map (Qnil ProdVarOrder.T).

Definition ExpandWhens_fun
    (* Expand When statements in a module *)
    (m : HiFP.hfmodule) (* module that needs to be handled *)
    (tmap : PVM.t (fgtyp * fcomponent))
:   option (HiFP.hfmodule) (* result is either a semantically equivalent module without when statements,
                            or nothing if there was some error *)
:=  match m with
    | FInmod v pp ss =>
        match ExpandBranches_funs ss (PVM.empty def_expr) tmap with
            | Some conn_map =>
                Some (FInmod v pp (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map)))
            | None => None
            end
    | FExmod _ _ _ => None
    end.

Definition expandWhens (c : HiFP.hfcircuit) : option HiFP.hfcircuit :=
  match c, Sem_HiFP.circuit_tmap c with
  | Fcircuit v [:: m], Some tmap => match ExpandWhens_fun m tmap with
    | Some fm => Some (Fcircuit v [:: fm])
    | _ => None
    end
  | _, _ => None
  end.

End ExpandWhens.

Definition is_connection (s : HiFP.hfstmt) := match s with
  | Sinvalid _
  | Sfcnct _ _=> true
  | _ => false
  end.

Definition is_declaration (s : HiFP.hfstmt) := match s with
  | Swire _ _
  | Sreg _ _
  | Snode _ _
  | Smem _ _
  | Sinst _ _ => true
  | _ => false
  end.

Lemma convert_to_connect_stmts_is_connection conn_map : forall s, Qin s (convert_to_connect_stmts conn_map) -> is_connection s.
Proof.
  intro. unfold convert_to_connect_stmts. Search(PVM.fold).
  apply PVM.Lemmas.P.fold_rec ; simpl; intros.
  - done.
  - unfold convert_to_connect_stmt in *.
    destruct e; auto.
    + simpl in H3.
      case /orP : H3 => H3.
      * destruct s; try done.
      * apply H2; done.
    + simpl in H3.
      case /orP : H3 => H3.
      * destruct s; try done.
      * by apply H2.
Qed.

Lemma component_stmts_of_is_declaration ss : forall s, Qin s (component_stmts_of ss) -> is_declaration s
with component_stmt_of_is_declaration ss : forall s, Qin s (component_stmt_of ss) -> is_declaration s.
Proof.
  induction ss as [|s ss IH]. simpl; done.
  simpl; intros. apply Qin_Qcat in H. destruct H. 
  move : H; apply component_stmt_of_is_declaration.
  move : H; apply IH.
  clear component_stmt_of_is_declaration.
  intro. destruct ss as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt; subst ss; simpl; try done; intros.
  1-5 : destruct s; try done. apply Qin_Qcat in H. destruct H. 
  1,2 : move : H; apply component_stmts_of_is_declaration.
Qed.

Lemma stmts_tmap_qcat pmap s1 s2 : match Sem_HiFP.stmts_tmap pmap s1 with
  | Some tmap_true => Sem_HiFP.stmts_tmap tmap_true s2 
  | _ => None
  end = Sem_HiFP.stmts_tmap pmap (Qcat s1 s2).
Proof. 
  move : s1 pmap s2. elim; simpl in *; try done.
  intros hd tl IH pmap s2. destruct (Sem_HiFP.stmt_tmap pmap hd) as [tmap'|]; try done.
Qed.

Lemma stmts_tmap_component_stmts_of_eq ss pmap : Sem_HiFP.stmts_tmap pmap ss = Sem_HiFP.stmts_tmap pmap (component_stmts_of ss)
with stmt_tmap_component_stmts_of_eq s pmap : Sem_HiFP.stmt_tmap pmap s = Sem_HiFP.stmts_tmap pmap (component_stmt_of s).
Proof.
  move : ss pmap; elim. simpl; done.
  intros hd tl IH pmap. simpl. destruct hd as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt; subst hd; simpl in *; try done.
  destruct t; try done; destruct (PVM.find v0 pmap); try done.
  destruct (PVM.find v0 pmap); try done; destruct (Sem_HiFP.type_of_hfexpr (clock r) pmap); try done; destruct r; try done; 
    destruct (HiFirrtl.type {| type := type; clock := clock; reset := reset |}); try done.
  destruct (PVM.find v0 pmap); try done; destruct (Sem_HiFP.type_of_hfexpr e0 pmap); try done.
  rewrite (stmts_tmap_component_stmts_of_eq s1). rewrite -stmts_tmap_qcat. rewrite -stmts_tmap_qcat.
  destruct (Sem_HiFP.stmts_tmap pmap (component_stmts_of s1)) as [tmap_true|]; try done.
  rewrite (stmts_tmap_component_stmts_of_eq s2). destruct (Sem_HiFP.stmts_tmap tmap_true (component_stmts_of s2)) as [tmap_false|]; try done.

  clear stmt_tmap_component_stmts_of_eq. destruct s as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt; subst s; simpl in *; try done.
  (* wire *)
  destruct t as [gt|a b|a b]; try done. destruct (PVM.find v0 pmap); try done.
  (* reg *)
  destruct (PVM.find v0 pmap); try done. destruct (Sem_HiFP.type_of_hfexpr (clock r) pmap); try done. destruct (type r); try done.
  (* node *)
  destruct (PVM.find v0 pmap); destruct (Sem_HiFP.type_of_hfexpr e0 pmap); try done.
  (* when *)
  rewrite stmts_tmap_component_stmts_of_eq. rewrite -stmts_tmap_qcat. destruct (Sem_HiFP.stmts_tmap pmap (component_stmts_of s1)); try done.
Qed.

Lemma stmts_tmap_qcat_convert_to_connect_stmts_eq ss cncts pmap : (forall s, Qin s cncts -> is_connection s) ->
  Sem_HiFP.stmts_tmap pmap (Qcat ss cncts) = Sem_HiFP.stmts_tmap pmap ss.
Proof.
  intro. move : ss pmap. elim. simpl. intro; move : cncts H. elim. simpl; done.
  simpl; intros. assert (is_connection h). apply H0. simpl. specialize (hfstmt_eqn_refl h) as Heq. move/eqP : Heq => Heq. 
    specialize (hfstmt_eqP h h) as Heq'. apply reflect_iff in Heq'. apply Heq' in Heq. rewrite Heq orb_true_l //.
    destruct h; try done. simpl; apply H. intros; apply H0. rewrite H2 orb_true_r //.
    simpl; apply H. intros; apply H0. rewrite H2 orb_true_r //.
  simpl; intros. destruct (Sem_HiFP.stmt_tmap pmap h); try done.
Qed.

Lemma ExpandWhens_fun_tmap_eq m tmap : Sem_HiFP.module_tmap (PVM.empty (fgtyp * fcomponent)) m = Some tmap -> 
  forall fm, ExpandWhens_fun m tmap = Some fm -> Sem_HiFP.module_tmap (PVM.empty (fgtyp * fcomponent)) fm = Some tmap.
Proof.
  intros Htmap fm Hexpand. destruct m as [mv ps ss|]; try discriminate. simpl in *.
  destruct (ExpandBranches_funs ss (PVM.empty def_expr) tmap) as [conn_map|] eqn : Hexpand_branches; try discriminate.
  inversion Hexpand; subst fm; clear Hexpand. simpl.
  destruct (Sem_HiFP.ports_tmap (PVM.empty (fgtyp * fcomponent)) ps) as [pmap|]; try discriminate.
  rewrite stmts_tmap_component_stmts_of_eq in Htmap. rewrite stmts_tmap_qcat_convert_to_connect_stmts_eq //.
  apply convert_to_connect_stmts_is_connection.
Qed.

Lemma init_dclrs_qcat valmap tmap s1 s2 : match Sem_HiFP.init_dclrs s1 valmap tmap with
  | Some valmap' => Sem_HiFP.init_dclrs s2 valmap' tmap 
  | _ => None
  end = Sem_HiFP.init_dclrs (Qcat s1 s2) valmap tmap.
Proof. 
  move : s1 tmap valmap s2. elim; simpl in *; try done.
  intros hd tl IH tmap valmap s2. destruct (Sem_HiFP.init_dclr hd valmap tmap) as [valmap'|]; try done.
Qed.

Lemma init_dclrs_component_stmts_of_eq ss valmap tmap : Sem_HiFP.init_dclrs ss valmap tmap = Sem_HiFP.init_dclrs (component_stmts_of ss) valmap tmap
with init_dclr_component_stmt_of_eq s valmap tmap : Sem_HiFP.init_dclr s valmap tmap = Sem_HiFP.init_dclrs (component_stmt_of s) valmap tmap.
Proof.
  move : ss valmap; elim. simpl; done.
  intros hd tl IH valmap. simpl. rewrite (init_dclr_component_stmt_of_eq hd). rewrite -init_dclrs_qcat.
  destruct (Sem_HiFP.init_dclrs (component_stmt_of hd) valmap tmap); try done.
  
  clear init_dclr_component_stmt_of_eq.
  destruct s as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt; subst s; simpl in *; try done.
  destruct t; try done.
  destruct (Sem_HiFP.eval_hfexpr e0 valmap tmap); try done.
  rewrite (init_dclrs_component_stmts_of_eq s1). rewrite -init_dclrs_qcat. destruct (Sem_HiFP.init_dclrs (component_stmts_of s1) valmap tmap); try done.
Qed.

Lemma init_dclrs_convert_to_connect_stmts_eq ss cncts valmap tmap : (forall s, Qin s cncts -> is_connection s) ->
  Sem_HiFP.init_dclrs (Qcat ss cncts) valmap tmap = Sem_HiFP.init_dclrs ss valmap tmap.
Proof.
  intro. move : ss valmap. elim. simpl. intro; move : cncts H. elim. simpl; done.
  simpl; intros. assert (is_connection h). apply H0. simpl. specialize (hfstmt_eqn_refl h) as Heq. move/eqP : Heq => Heq. 
    specialize (hfstmt_eqP h h) as Heq'. apply reflect_iff in Heq'. apply Heq' in Heq. rewrite Heq orb_true_l //.
    destruct h; try done. simpl; apply H. intros; apply H0. rewrite H2 orb_true_r //.
    simpl; apply H. intros; apply H0. rewrite H2 orb_true_r //.
  simpl; intros. destruct (Sem_HiFP.init_dclr h valmap tmap); try done.
Qed.

Lemma component_stmts_of_init_dclrs_eq ss valmap tmap : 
  forall conn_map, Sem_HiFP.init_dclrs (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map)) valmap tmap = Sem_HiFP.init_dclrs ss valmap tmap.
Proof.
  intros. specialize convert_to_connect_stmts_is_connection as Hcncts. specialize (Hcncts conn_map).
  rewrite init_dclrs_convert_to_connect_stmts_eq; try done. rewrite -init_dclrs_component_stmts_of_eq //.
Qed.

(*Lemma PVM_equal_iff_find_eq (m1 m2 : PVM.t bits) : PVM.equal (fun val1 val2 : bitseq => val1 == val2) m1 m2 <-> (forall v, PVM.find v m1 = PVM.find v m2).
Proof.
Admitted.

Lemma PVM_equal_refl [A : Type] (m : PVM.t A) func: PVM.equal func m m.
Proof.
Admitted.

Lemma PVM_equal_trans (m1 m2 m3: PVM.t bits) func : PVM.equal func m1 m2 -> PVM.equal func m2 m3 -> PVM.equal func m1 m3.
Proof.
Admitted.

Lemma PVM_non_equal_trans (m1 m2 m3: PVM.t bits) func : ~ PVM.equal func m1 m2 -> PVM.equal func m2 m3 -> ~ PVM.equal func m1 m3.
Proof.
Admitted.

Lemma PVM_equal_comm (m1 m2 : PVM.t bits) func : PVM.equal func m1 m2 <-> PVM.equal func m2 m1.
Proof.
Admitted.

Lemma update_values_equal : forall ns1 ns2 s,
  PVM.equal (fun v1 v2 : bitseq => v1 == v2) ns1 ns2 ->
  PVM.equal (fun v1 v2 : bitseq => v1 == v2) (Sem_HiFP.update_values ns1 s) (Sem_HiFP.update_values ns2 s).
Proof.
Admitted.*)
Definition bits : Set := bitseq.

Definition pvm_included (m1 m2 : PVM.t bits) : Prop :=
  forall k v1, 
    PVM.find k m1 = Some v1 -> 
    PVM.find k m2 = Some v1.

Fixpoint Qin_with_cond (s : HiFP.hfstmt) (ss : HiFP.hfstmt_seq) init_s tmap : bool :=
match ss with 
| Qnil => false
| Qcons (Swhen c s1 s2) tl => match Sem_HiFP.eval_hfexpr c init_s tmap with
    | Some valc => if (~~ is_zero valc) then (Qin_with_cond s s1 init_s tmap) || (Qin_with_cond s tl init_s tmap)
                   else (Qin_with_cond s s2 init_s tmap) || (Qin_with_cond s tl init_s tmap)
    | _ => false
    end
| Qcons h tl => (hfstmt_eqn h s) || (Qin_with_cond s tl init_s tmap)
end.

Axiom NoDupA_notin : forall (l1 l2 : list (PVM.key * def_expr)) v e,
  NoDupA (PVM.eq_key (elt:=def_expr)) (l1 ++ (v, e) :: l2) ->
  ~ In v (fst (List.split l1)) /\ ~ In v (fst (List.split l2)).
(* [update_values] is monotone under semantic-map inclusion: included base maps and included update maps yield included updated maps. *)
Axiom included_update_values_included : forall s1 s2 ns1 ns2,
  pvm_included s1 s2 -> pvm_included ns1 ns2 ->
  pvm_included (Sem_HiFP.update_values ns1 s1) (Sem_HiFP.update_values ns2 s2).
(* Dynamic conditional reachability implies syntactic occurrence under a [when]:
   any statement selected by [Qin_with_cond] must also be recorded by the condition-insensitive predicate [Qin_when]. *)
Axiom Qin_with_cond2Qin_when : forall s ss init_s tmap, Qin_with_cond s ss init_s tmap -> Qin_when s ss.
(* A node name already declared in the surrounding sequence cannot be declared again in either branch of the current [when]. *)
Axiom Qin_when_uniqie_False :
  forall (v : ProdVarOrder.T) (e : hfexpr ProdVarOrder.T) (ss : hfstmt_seq ProdVarOrder.T) (e' : hfexpr ProdVarOrder.T)
         (cond : hfexpr ProdVarOrder.T) (ss_true ss_false : hfstmt_seq ProdVarOrder.T),    
  (forall (v' : ProdVarOrder.T) (e' : hfexpr ProdVarOrder.T),
    Qin_when (Snode v' e') (Qremove_when (Snode v e) (Qcons (Swhen cond ss_true ss_false) ss)) ->
    v <> v') ->
  Qin_when (Snode v e) ss ->
  (Qin_when (Snode v e') ss_true \/ Qin_when (Snode v e') ss_false) ->
  False.
(* Any node value produced by statement evaluation has a source declaration *)
Axiom find_node_qin_with_cond : forall mv pp ss tmap, Sem_HiFP.module_tmap (PVM.empty (fgtyp * fcomponent)) (FInmod mv pp ss) = Some tmap ->
  forall v gt, PVM.find v tmap = Some (gt, Node) -> 
  forall init_s rs1 s1 bs, Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs1, s1) ->
  PVM.find v s1 = Some bs ->
  exists e, Qin_with_cond (Snode v e) ss init_s tmap.
(* Any conditionally reachable node declaration present in the declarations. *)
Axiom qin_with_cond_node_qin_cmpnt : forall v e ss init_s tmap,
  Qin_with_cond (Snode v e) ss init_s tmap -> 
  Qin (Snode v e) (component_stmts_of ss).