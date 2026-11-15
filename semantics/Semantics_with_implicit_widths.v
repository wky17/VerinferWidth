(* This file shows a possible development of the semantics.
   It is organized in Sections as follows.

   0. Outside the sections mentioned below, some preliminary definitions
      are given, e.g. a ftype_mux function that is compatible with the
      width and reset inference.
      In a final version these might be moved to a separate file.

   1. Section Kinds_and_Types finds the original types and kinds of all
      components in the modules of the circuit.
      Its result is circuit_tmap_uninferred.
      If the result is <> None, that means that all types are almost
      compatible (the widths may be different, but the types are equal),
      except that abstract Reset signals may be connected to UInt and
      to AsyncReset.

   2. Section InferWidths_and_InferReset infers the widths and the Reset
      type of all components in the modules of the circuit.
      (This is done through calculating a fixed point, in fact the
      smallest fixed point of a monotonous operator.)

      It assumes that circuit_tmap_uninferred <> None.

      Its result is the adapted type-and-kind map circuit_tmap, which
      contains no more unspecified widths or abstract Reset signals.
      If the result is a true fixed point, that means that all types
      are fully compatible.

      The fixed point may take many iterations to compute.  One example
      of a hard circuit is this:

      circuit Top :
          module Top :
              input limit : UInt<128>
              output counter : UInt

              register intern : UInt
              intern <= counter
              counter <= rem(add(intern, UInt(1)), limit)

      Although this circuit has only two connect statements, it takes
      128 iterations to reach the fixed point.  The count-to-infinity
      situation for the register and the counter is broken off by the
      limit.  However, I find it difficult to find a general rule for
      an a-priori maximum number of iterations, or for an acceleration
      of iteration (basically, the acceleration should find that the
      minimum width of the rem() operator should come from limit, not
      from the add() argument).

   3. Section Instances creates a map that defines all instances in
      the circuit.

      It assumes that the top module is present in the circuit, that
      all instance statements refer to existing modules (this would
      also be a consequence ot circuit_tmap_uninferred <> None), and
      that there are no cycles in instance statements.

   4. Section Values defines values and calculates a value for every
      expression, given values for the references.

      There are a number of special values to accommodate for undefined
      expressions: uninitialized registers, not yet determined, or
      left undefined on purpose.

      It works with explicit-width, concrete types only; so it assumes
      that all references and expressions have explicit widths and no
      abstract resets.

   5. Section Single_Cycle_Dynamics creates a function that maps
      (old) register values and external inputs to a value map of all
      components in the instances of the circuit after stabilization.
      (This is again done through calculating a fixed point; however,
      this fixed point is defined because there should be no cyclic
      computations.)

      It assumes that there exists a number iter_count such that after
      iter_count iterations in the previous section, circuit_tmap has
      been calculated properly.

      It also assumes that the top module is present.
*)

From Coq Require Import FunInd FMaps FMapAVL FSets FSetAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph div ssrint ssrfun.
From Lib Require Import SsrOrder Var Nbits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*************************************************************************)
(*************************************************************************)
(***                                                                   ***)
(***                                                                   ***)
(***                           Preliminaries                           ***)
(***                                                                   ***)
(***                                                                   ***)
(*************************************************************************)
(*************************************************************************)

(* Unify the ground types x and y for multiplexers.

   x, y = input ground types

   Result: the smallest ground type that can encompass both x and y without data loss

   The result also takes into account that abstract reset types might be concretized;
   therefore, an abstract reset type should unify with both synchronous and asynchronous
   resets.  This also has implications for a few other cases; overall, the choices
   below ensure that fgtyp_mux is associative and monotonous. *)
Definition fgtyp_mux (x y : fgtyp) : option fgtyp :=
    match x, y with
    | Fuint wx,           Fuint wy           => Some (Fuint          (maxn wx wy))
    | Fuint wx,           Fuint_implicit wy  => Some (Fuint_implicit (maxn wx wy))
    | Fuint wx,           Fuint_implicit_eq1
    | Fuint wx,           Freset             => Some (Fuint_implicit (maxn wx 1 ))
    | Fuint_implicit wx,  Fuint wy
    | Fuint_implicit wx,  Fuint_implicit wy  => Some (Fuint_implicit (maxn wx wy))
    | Fuint_implicit wx,  Fuint_implicit_eq1
    | Fuint_implicit wx,  Freset             => Some (Fuint_implicit (maxn wx 1 ))
    | Fuint_implicit_eq1, Fuint wy
    | Fuint_implicit_eq1, Fuint_implicit wy  => Some (Fuint_implicit (maxn 1  wy))
    | Fuint_implicit_eq1, Fuint_implicit_eq1
    | Fuint_implicit_eq1, Freset             => Some  Fuint_implicit_eq1
    | Fsint wx,           Fsint wy           => Some (Fsint          (maxn wx wy))
    | Fsint wx,           Fsint_implicit wy
    | Fsint_implicit wx,  Fsint wy
    | Fsint_implicit wx,  Fsint_implicit wy  => Some (Fsint_implicit (maxn wx wy))
    | Freset,             Fuint wy
    | Freset,             Fuint_implicit wy  => Some (Fuint_implicit (maxn 1  wy))
    | Freset,             Fuint_implicit_eq1 => Some  Fuint_implicit_eq1
    | Freset,             Fasyncreset
    | Fasyncreset,        Freset             => Some  Fasyncreset
    | _, _ => if x==y then Some x else None
    end.

(* Unify the types x and y for multiplexers.
   This function extends fgtyp_mux to arrays and bundle types.

   x, y = input types

   Result: the smallest type that can encompass both x and y without data loss *)
Fixpoint ftype_mux (passive : bool) (x y : ftype) : option ftype :=
  match x, y with
  | Gtyp tx, Gtyp ty => option_map Gtyp (fgtyp_mux tx ty)
  | Atyp tx nx, Atyp ty ny => if (nx == ny) then option_map (Atyp^~ nx) (ftype_mux passive tx ty)
                                            else None
  | Btyp fx, Btyp fy => option_map Btyp (ffield_mux passive fx fy)
  | _, _ => None
  end
with ffield_mux (passive : bool) (f1 f2 : ffield) : option ffield :=
       match f1, f2 with
       | Fnil, Fnil => Some Fnil
       | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2
         => if v1 == v2 then
               match ftype_mux passive t1 t2, ffield_mux passive fs1 fs2 with
               | Some ft, Some bf => Some (Fflips v1 Nflip ft bf)
               | _, _ => None
               end
            else None
       | Fflips v1 Flipped t1 fs1, Fflips v2 Flipped t2 fs2
         => if ~~passive && (v1 == v2) then
               match ftype_mux passive t1 t2, ffield_mux passive fs1 fs2 with
               | Some ft, Some bf => Some (Fflips v1 Flipped ft bf)
               | _, _ => None
               end
            else None
       | _, _ => None
       end.

Lemma ftype_mux_passive :
    forall (t1 t2 fat : ftype),
        ftype_mux true t1 t2 = Some fat ->
        is_passive t1 && is_passive t2 && is_passive fat && (ftype_mux false t1 t2 == Some fat)
with ffield_mux_passive :
    forall (ff1 ff2 fat : ffield),
        ffield_mux true ff1 ff2 = Some fat ->
        is_passive_fields ff1 && is_passive_fields ff2 && is_passive_fields fat && (ffield_mux false ff1 ff2 == Some fat).
Admitted.

Lemma ftype_mux_idempotent :
    forall (passive : bool) (t : ftype),
        match ftype_mux passive t t with
        | Some t_res => t_res = t
        | None => passive && ~~ is_passive t
        end
with ffield_mux_idempotent :
    forall (passive : bool) (ff : ffield),
        match ffield_mux passive ff ff with
        | Some ff_res => ff_res = ff
        | None => passive && ~~ is_passive_fields ff
        end.
Admitted.

Lemma ftype_mux_commutative :
    forall (passive : bool) (t1 t2 : ftype),
        ftype_mux passive t1 t2 = ftype_mux passive t2 t1
with ffield_mux_commutative :
    forall (passive : bool) (ff1 ff2 : ffield),
        ffield_mux passive ff1 ff2 = ffield_mux passive ff2 ff1.
Admitted.

Lemma ftype_mux_associative :
    forall (passive : bool) (t1 t2 t3 : ftype),
        match ftype_mux passive t1 t2, ftype_mux passive t2 t3 with
        | Some t12, Some t23 => match ftype_mux passive t12 t3, ftype_mux passive t1 t23 with
                                | Some t12_3, Some t1_23 => t12_3 = t1_23
                                | _, _ => ftype_mux passive t1 t3 = None
                                end
        | _, _ => True
        end
with ffield_mux_associative :
    forall (passive : bool) (ff1 ff2 ff3 : ffield),
        match ffield_mux passive ff1 ff2, ffield_mux passive ff2 ff3 with
        | Some ff12, Some ff23 => match ffield_mux passive ff12 ff3, ffield_mux passive ff1 ff23 with
                                  | Some ff12_3, Some ff1_23 => ff12_3 = ff1_23
                                  | _, _ => ffield_mux passive ff1 ff3 = None
                                  end
        | _, _ => True
        end.
Admitted.

(* Module to define the key set of a map. *)
Module VS := FSetAVL.Make(OrderedVarType).

Module VKS.
  Definition key_set {A : Type} (m : VM.t A) : VS.t :=
    List.fold_right (fun p keys => VS.add (fst p) keys)
      (VS.empty) (VM.elements m).
End VKS.

(* sequence order, to create a way to identify all components in instances. *)
(* This module code is copied from Semantics_reorganize.v *)

Module MakeSeqOrderMinimal (O : SsrOrder) <: SsrOrderMinimal with Definition t := [eqType of seq O.T].

  Definition t : eqType := [eqType of seq O.T].

  Definition eqn (x y : t) : bool := x == y.

  (* lexicographic order of sequences, based on the order of the element type *)
  Fixpoint ltn (x y : t) : bool :=
    match x, y with
    | [::], [::] => false
    | [::], _ => true
    | _, [::] => false
    | xh :: xt, yh :: yt => (O.ltn xh yh) || ((xh == yh) && ltn xt yt)
    end.

  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Admitted.

  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Admitted.

  Definition compare (x y : t) : Compare ltn eqn x y.
  Proof.
    revert y ; induction x as [|xh xt] ; intros.
    * destruct y as [|yh yt].
      + apply EQ ; done.
      + apply LT ; done.
    * destruct y as [|yh yt].
      + apply GT ; done.
      + destruct (O.compare xh yh).
        - apply LT ; simpl ; rewrite l orTb //.
        - unfold O.eq in e.
          specialize (IHxt yt) ; destruct IHxt.
          * apply LT ; simpl.
            by rewrite e andTb i orbT //.
          * apply EQ ; unfold eqn in i.
            by rewrite /eqn eqseq_cons e i //.
          * apply GT ; simpl.
            by rewrite eq_sym e andTb i orbT //.
        - apply GT ; simpl ; rewrite l orTb //.
  Defined.

End MakeSeqOrderMinimal.

Module MakeSeqOrder (O : SsrOrder) <: SsrOrder
    with Definition T := [eqType of seq O.T].
  Module M := MakeSeqOrderMinimal O.
  Module P := MakeSsrOrder M.
  Include P.
End MakeSeqOrder.

Module SeqVarOrder := MakeSeqOrder VarOrder.
Module SVM := FMapAVL.Make(SeqVarOrder).

Section Semantics.

(* Sequence of modules in the circuit.

   Note that at this moment we do not yet need to designate the top module,
   as kinds and types are found per module, not per instance.
   Even width inference is independent of instantiations. *)
Variable mml : seq (HiF.hfmodule).

(*************************************************************************)
(*************************************************************************)
(***                                                                   ***)
(***                                                                   ***)
(***        First main section: Kinds_and_Types                        ***)
(***                                                                   ***)
(***        Find the original types and kinds of all components        ***)
(***                                                                   ***)
(***                                                                   ***)
(*************************************************************************)
(*************************************************************************)

Section Kinds_and_Types.

(* find the module with identifier mi

   Result: the module in mml whose identifier is mi;
           None if no such module exists *)
Definition find_module (mi : VarOrder.T) : option HiF.hfmodule :=
    match filter (fun m : HiF.hfmodule => match m with
                                          | FInmod mi' _ _
                                          | FExmod mi' _ _ => mi == mi'
                                          end) mml with
    | [::] => None
    | m :: _ => Some m
    end.

(* bundle type of the ports of a module 

   ppl = list of ports whose type needs to be determined

   Result: bundle type that corresponds to the list of ports;
           this then becomes the type of the (interface of the) module *)
Fixpoint port_type (ppl : seq HiF.hfport) : ffield :=
    match ppl with
    | [::] => Fnil
    | Finput p t :: ppl' => Fflips p Flipped t (port_type ppl')
    | Foutput p t :: ppl' => Fflips p Nflip t (port_type ppl')
    end.

(* type of a module interface

   mi = identifier of the module whose interface type needs to be determined

   Result: type of (the interface of) the module *)
Definition module_type (mi : VarOrder.T) : option ftype :=
    match find_module mi with
    | Some (FInmod _ ppl _) => Some (Btyp (port_type ppl))
    | _ => None
    end.

(* (kind, type) pair of port list.

   ppl = list of ports whose type-and-kind map needs to be found

   Result: a type-and-kind map that maps every port identifier to its type and kind;
           however, if multiple ports have the same identifier, None is returned. *)
Fixpoint ports_tmap (ppl : seq HiF.hfport) : option (VM.t (ftype * fcomponent)) :=
    match ppl with
    | [::] => Some (VM.empty (ftype * fcomponent))
    | Finput  p t :: ppl' => match ports_tmap ppl' with
                             | Some pmap => match VM.find p pmap with
                                            | Some _ => None
                                            | None => Some (VM.add p (t, In_port) pmap)
                                            end
                             | None => None
                             end
    | Foutput p t :: ppl' => match ports_tmap ppl' with
                             | Some pmap => match VM.find p pmap with
                                            | Some _ => None
                                            | None => Some (VM.add p (t, Out_port) pmap)
                                            end
                             | None => None
                             end
    end.

(* Find the type of a reference

   sc = set of identifiers in scope
   tmap = type-and-kind map of all identifiers in the namespace, including those out of scope
   r = reference whose type needs to be found

   Result: type of the reference r;
           None if the reference is undefined or out-of-scope.

   It is not checked whether subindices of arrays are in range,
   nor whether subaccess expressions make sense. *)
Fixpoint type_of_ref (sc : option VS.t) (tmap : VM.t (ftype * fcomponent)) (r : HiF.href) : option ftype :=
    match r with
    | Eid v => match sc with 
               | Some sc' => if VS.mem v sc' then option_map fst (VM.find v tmap)
                                             else None
               | None => option_map fst (VM.find v tmap)
               end
    | Esubfield r v => match type_of_ref sc tmap r with
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
    | Esubindex r _ => match type_of_ref sc tmap r with
                | Some (Atyp ty _) => Some ty
                | _ => None
                end
    end.

(* The function determines the type of an expression,
   based on a function that determines the type of a reference.
   The resulting type has an implicit width if it might be expanded by width inference.

   type_of_ref' = function that determines the type of references (which may appear in e)
   e = expression whose type needs to be found

   Result: type of e, if the type can be found;
           otherwise (if there is a type error or an undefined reference) None *)
Fixpoint type_of_expr' (type_of_ref' : HiF.href -> option ftype) (e : HiF.hfexpr) : option ftype :=
  match e with
  | Econst (Fuint w) bs => if w < size bs then None else Some (Gtyp (Fuint w))
  | Econst (Fsint w) bs => if w < size bs then None else Some (Gtyp (Fsint w))
  | Econst _ bs => None (* constants cannot be of Fclock, Freset, Fasyncreset type *)
  | Eref r => type_of_ref' r
  | Ecast AsUInt e1 => match type_of_expr' type_of_ref' e1 with
                        | Some (Gtyp (Fuint          w))
                        | Some (Gtyp (Fsint          w)) => Some (Gtyp (Fuint          w))
                        | Some (Gtyp (Fuint_implicit w))
                        | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fuint_implicit w))
                          (* Fuint_implicit 0 can be concretized to Fuint_implicit_eq1.
                             Therefore, also Fuint_implicit_eq1 needs to be cast to a
                             type that is compatible.  But then the types Freset and
                             Fasyncreset, which are connected in the (undirected)
                             more_concrete graph, need to be Fuint_implicit. *)
                        | Some (Gtyp Fuint_implicit_eq1)
                        | Some (Gtyp Freset            )
                        | Some (Gtyp Fasyncreset       ) => Some (Gtyp (Fuint_implicit 1))
                        | Some (Gtyp Fclock            ) => Some (Gtyp (Fuint          1))
                        | _ => None
                        end
  | Ecast AsSInt e1 => match type_of_expr' type_of_ref' e1 with
                        | Some (Gtyp (Fuint          w))
                        | Some (Gtyp (Fsint          w)) => Some (Gtyp (Fsint          w))
                        | Some (Gtyp (Fuint_implicit w))
                        | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit w))
                        | Some (Gtyp Fuint_implicit_eq1)
                        | Some (Gtyp Freset            )
                        | Some (Gtyp Fasyncreset       ) => Some (Gtyp (Fsint_implicit 1))
                        | Some (Gtyp Fclock            ) => Some (Gtyp (Fsint          1))
                        | _ => None
                        end
  | Ecast AsClock e1 => match type_of_expr' type_of_ref' e1 with
                        | Some (Gtyp _) => Some (Gtyp Fclock)
                        | _ => None
                        end
  | Ecast AsAsync e1 => match type_of_expr' type_of_ref' e1 with
                        | Some (Gtyp _) => Some (Gtyp Fasyncreset)
                        | _ => None
                        end
  | Eprim_unop (Upad n) e1 => match type_of_expr' type_of_ref' e1 with
                              | Some (Gtyp (Fuint          w)) => Some (Gtyp (Fuint          (maxn w n)))
                              | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit (maxn w n)))
                              | Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit (maxn 1 n)))
                              | Some (Gtyp (Fsint          w)) => Some (Gtyp (Fsint          (maxn w n)))
                              | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (maxn w n)))
                              | _ => None
                              end
  | Eprim_unop (Ushl n) e1 => match type_of_expr' type_of_ref' e1 with
                              | Some (Gtyp (Fuint          w)) => Some (Gtyp (Fuint          (w + n)))
                              | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit (w + n)))
                              | Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit (1 + n)))
                              | Some (Gtyp (Fsint          w)) => Some (Gtyp (Fsint          (w + n)))
                              | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (w + n)))
                              | _ => None
                              end
  | Eprim_unop (Ushr n) e1 => match type_of_expr' type_of_ref' e1 with
                              | Some (Gtyp (Fuint          w)) => Some (Gtyp (Fuint                (w - n)   ))
                              | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit       (w - n)   ))
                              | Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit       (1 - n)   ))
                              | Some (Gtyp (Fsint          w)) => Some (Gtyp (Fsint          (maxn (w - n) 1)))
                              | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (maxn (w - n) 1)))
                              | _ => None
                              end
  | Eprim_unop Ucvt e1 => match type_of_expr' type_of_ref' e1 with
                          | Some (Gtyp (Fuint          w)) => Some (Gtyp (Fsint          (w.+1)))
                          | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fsint_implicit (w.+1)))
                          | Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fsint_implicit (1.+1)))
                          | Some (Gtyp (Fsint          w)) => Some (Gtyp (Fsint           w    ))
                          | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit  w    ))
                          | _ => None
                          end
  | Eprim_unop Uneg e1 => match type_of_expr' type_of_ref' e1 with
                          | Some (Gtyp (Fuint          w))
                          | Some (Gtyp (Fsint          w)) => Some (Gtyp (Fsint          (w.+1)))
                          | Some (Gtyp (Fuint_implicit w))
                          | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (w.+1)))
                          | Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fsint_implicit (1.+1)))
                          | _ => None
                          end
  | Eprim_unop Unot e1 => match type_of_expr' type_of_ref' e1 with
                          | Some (Gtyp (Fuint          w))
                          | Some (Gtyp (Fsint          w)) => Some (Gtyp (Fuint          w))
                          | Some (Gtyp (Fuint_implicit w))
                          | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fuint_implicit w))
                          | Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit 1))
                          | _ => None
                          end
  | Eprim_unop (Uextr hi lo) e1 => match type_of_expr' type_of_ref' e1 with
                                   | Some (Gtyp (Fuint          w))
                                   | Some (Gtyp (Fsint          w)) => if lo <= hi < w then Some (Gtyp (Fuint          (     hi.+1   - lo))) else None
                                   | Some (Gtyp (Fuint_implicit w))
                                   | Some (Gtyp (Fsint_implicit w)) => if lo <= hi     then Some (Gtyp (Fuint_implicit (minn hi.+1 w - lo))) else None
                                   | Some (Gtyp Fuint_implicit_eq1) => if lo <= hi     then Some (Gtyp (Fuint_implicit (minn hi.+1 1 - lo))) else None
                                   | _ => None
                                   end
  | Eprim_unop (Uhead n) e1 => match type_of_expr' type_of_ref' e1 with
                               | Some (Gtyp (Fuint          w))
                               | Some (Gtyp (Fsint          w)) => if n <= w then Some (Gtyp (Fuint                n   )) else None
                               | Some (Gtyp (Fuint_implicit w))
                               | Some (Gtyp (Fsint_implicit w)) =>                Some (Gtyp (Fuint_implicit (minn n w)))
                               | Some (Gtyp Fuint_implicit_eq1) =>                Some (Gtyp (Fuint_implicit (minn n 1)))
                               | _ => None
                               end
  | Eprim_unop (Utail n) e1 => match type_of_expr' type_of_ref' e1 with
                               | Some (Gtyp (Fuint          w))
                               | Some (Gtyp (Fsint          w)) => if n <= w then Some (Gtyp (Fuint          (w - n))) else None
                               | Some (Gtyp (Fsint_implicit w))
                               | Some (Gtyp (Fuint_implicit w)) =>                Some (Gtyp (Fuint_implicit (w - n)))
                               | Some (Gtyp Fuint_implicit_eq1) =>                Some (Gtyp (Fuint_implicit (1 - n)))
                               | _ => None
                               end
  | Eprim_unop _ e1 => match type_of_expr' type_of_ref' e1 with
                       | Some (Gtyp (Fuint          _))
                       | Some (Gtyp (Fuint_implicit _))
                       | Some (Gtyp Fuint_implicit_eq1)
                       | Some (Gtyp (Fsint          _))
                       | Some (Gtyp (Fsint_implicit _)) => Some (Gtyp (Fuint 1))
                       | _ => None
                       end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_expr' type_of_ref' e1, type_of_expr' type_of_ref' e2 with
                                   | Some (Gtyp (Fuint          _)), Some (Gtyp (Fuint          _))
                                   | Some (Gtyp (Fuint          _)), Some (Gtyp (Fuint_implicit _))
                                   | Some (Gtyp (Fuint          _)), Some (Gtyp Fuint_implicit_eq1)
                                   | Some (Gtyp (Fuint_implicit _)), Some (Gtyp (Fuint          _))
                                   | Some (Gtyp (Fuint_implicit _)), Some (Gtyp (Fuint_implicit _))
                                   | Some (Gtyp (Fuint_implicit _)), Some (Gtyp Fuint_implicit_eq1)
                                   | Some (Gtyp Fuint_implicit_eq1), Some (Gtyp (Fuint          _))
                                   | Some (Gtyp Fuint_implicit_eq1), Some (Gtyp (Fuint_implicit _))
                                   | Some (Gtyp Fuint_implicit_eq1), Some (Gtyp Fuint_implicit_eq1)
                                   | Some (Gtyp (Fsint          _)), Some (Gtyp (Fsint          _))
                                   | Some (Gtyp (Fsint          _)), Some (Gtyp (Fsint_implicit _))
                                   | Some (Gtyp (Fsint_implicit _)), Some (Gtyp (Fsint          _))
                                   | Some (Gtyp (Fsint_implicit _)), Some (Gtyp (Fsint_implicit _)) => Some (Gtyp (Fuint 1))
                                   | _, _ => None
                                   end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_expr' type_of_ref' e1, type_of_expr' type_of_ref' e2 with
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint          w2)) => Some (Gtyp (Fuint          (maxn w1 w2).+1))
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint          w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (maxn w1 w2).+1))
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp  Fuint_implicit_eq1)
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp  Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit (maxn w1 1 ).+1))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp (Fuint          w2))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (maxn 1  w2).+1))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp Fuint_implicit_eq1 ) => Some (Gtyp (Fuint_implicit (maxn 1  1 ).+1))
                              | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fsint          w2)) => Some (Gtyp (Fsint          (maxn w1 w2).+1))
                              | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fsint_implicit w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint          w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) => Some (Gtyp (Fsint_implicit (maxn w1 w2).+1))
                              | _, _ => None
                              end
  | Eprim_binop Bmul e1 e2 => match type_of_expr' type_of_ref' e1, type_of_expr' type_of_ref' e2 with
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint          w2)) => Some (Gtyp (Fuint          (w1+w2)))
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint          w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (w1+w2)))
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp  Fuint_implicit_eq1)
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp  Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit (w1+1 )))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp (Fuint          w2))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (1 +w2)))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp Fuint_implicit_eq1 ) => Some (Gtyp (Fuint_implicit (1 +1 )))
                              | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fsint          w2)) => Some (Gtyp (Fsint          (w1+w2)))
                              | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fsint_implicit w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint          w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) => Some (Gtyp (Fsint_implicit (w1+w2)))
                              | _, _ => None
                              end
  | Eprim_binop Bdiv e1 e2  => match type_of_expr' type_of_ref' e1, type_of_expr' type_of_ref' e2 with
                               | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint          _))
                               | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint_implicit _))
                               | Some (Gtyp (Fuint          w1)), Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fuint          w1   ))
                               | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint          _))
                               | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit _))
                               | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit w1   ))
                               | Some (Gtyp  Fuint_implicit_eq1), Some (Gtyp (Fuint          _))
                               | Some (Gtyp  Fuint_implicit_eq1), Some (Gtyp (Fuint_implicit _))
                               | Some (Gtyp  Fuint_implicit_eq1), Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit 1    ))
                               | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fsint          _))
                               | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fsint_implicit _)) => Some (Gtyp (Fsint          w1.+1))
                               | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint          _))
                               | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit _)) => Some (Gtyp (Fsint_implicit w1.+1))
                               | _, _ => None
                               end
  | Eprim_binop Brem e1 e2 => match type_of_expr' type_of_ref' e1, type_of_expr' type_of_ref' e2 with
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint          w2)) => Some (Gtyp (Fuint          (minn w1 w2)))
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint          w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (minn w1 w2)))
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp  Fuint_implicit_eq1)
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp  Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit (minn w1 1 )))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp (Fuint          w2))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (minn 1  w2)))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp Fuint_implicit_eq1 ) => Some (Gtyp (Fuint_implicit (minn 1  1 )))
                              | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fsint          w2)) => Some (Gtyp (Fsint          (minn w1 w2)))
                              | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fsint_implicit w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint          w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) => Some (Gtyp (Fsint_implicit (minn w1 w2)))
                              | _, _ => None
                              end
  | Eprim_binop Bdshl e1 e2 => match type_of_expr' type_of_ref' e1, type_of_expr' type_of_ref' e2 with
                               | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint          w2)) => Some (Gtyp (Fuint          (w1 + 2^w2).-1))
                               | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint_implicit w2))
                               | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint          w2))
                               | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (w1 + 2^w2).-1))
                               | Some (Gtyp (Fuint          w1)), Some (Gtyp  Fuint_implicit_eq1)
                               | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp  Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit (w1 + 2^1 ).-1))
                               | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp (Fuint          w2))
                               | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (1  + 2^w2).-1))
                               | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp Fuint_implicit_eq1 ) => Some (Gtyp (Fuint_implicit (1  + 2^1 ).-1))
                               | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fuint          w2)) => Some (Gtyp (Fsint          (w1 + 2^w2).-1))
                               | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fuint_implicit w2))
                               | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fuint          w2))
                               | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fsint_implicit (w1 + 2^w2).-1))
                               | Some (Gtyp (Fsint          w1)), Some (Gtyp  Fuint_implicit_eq1)
                               | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp  Fuint_implicit_eq1) => Some (Gtyp (Fsint_implicit (w1 + 2^1 ).-1))
                               | _, _ => None
                               end
  | Eprim_binop Bdshr e1 e2 => match type_of_expr' type_of_ref' e1, type_of_expr' type_of_ref' e2 with
                               | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint          _))
                               | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint_implicit _))
                               | Some (Gtyp (Fuint          w1)), Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fuint          w1))
                               | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint          _))
                               | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit _))
                               | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit w1))
                               | Some (Gtyp  Fuint_implicit_eq1), Some (Gtyp (Fuint          _))
                               | Some (Gtyp  Fuint_implicit_eq1), Some (Gtyp (Fuint_implicit _))
                               | Some (Gtyp  Fuint_implicit_eq1), Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit 1 ))
                               | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fuint          _))
                               | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fuint_implicit _))
                               | Some (Gtyp (Fsint          w1)), Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fsint          w1))
                               | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fuint          _))
                               | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fuint_implicit _))
                               | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp Fuint_implicit_eq1) => Some (Gtyp (Fsint_implicit w1))
                               | _, _ => None
                               end
  | Eprim_binop Bcat e1 e2 => match type_of_expr' type_of_ref' e1, type_of_expr' type_of_ref' e2 with
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint          w2))
                              | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fsint          w2)) => Some (Gtyp (Fuint          (w1+w2)))
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint          w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fsint_implicit w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint          w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) => Some (Gtyp (Fuint_implicit (w1+w2)))
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp  Fuint_implicit_eq1)
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp  Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit (w1+1 )))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp (Fuint          w2))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (1 +w2)))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp Fuint_implicit_eq1 ) => Some (Gtyp (Fuint_implicit (1 +1 )))
                              | _, _ => None
                              end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_expr' type_of_ref' e1, type_of_expr' type_of_ref' e2 with
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint          w2))
                              | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fsint          w2)) => Some (Gtyp (Fuint          (maxn w1 w2)))
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint          w2))
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2))
                              | Some (Gtyp (Fsint          w1)), Some (Gtyp (Fsint_implicit w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint          w2))
                              | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) => Some (Gtyp (Fuint_implicit (maxn w1 w2)))
                              | Some (Gtyp (Fuint          w1)), Some (Gtyp  Fuint_implicit_eq1)
                              | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp  Fuint_implicit_eq1) => Some (Gtyp (Fuint_implicit (maxn w1 1 )))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp (Fuint          w2))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (maxn 1  w2)))
                              | Some (Gtyp Fuint_implicit_eq1 ), Some (Gtyp Fuint_implicit_eq1 ) => Some (Gtyp (Fuint_implicit (maxn 1  1 )))
                              | _, _ => None
                              end
  | Emux c e1 e2 => match type_of_expr' type_of_ref' c, type_of_expr' type_of_ref' e1, type_of_expr' type_of_ref' e2 with
                    | Some (Gtyp (Fuint          _)), Some t1, Some t2
                    | Some (Gtyp (Fuint_implicit _)), Some t1, Some t2
                    | Some (Gtyp Fuint_implicit_eq1), Some t1, Some t2 => ftype_mux true t1 t2
                    | _, _, _ => None
                    end
  (*| Evalidif _ _ => None*)
  end.

(* Determines the type of an expression

   sc = scope that determines which references are accessible
   tmap = type-and-kind map of all accessible references (possibly including some that are out of scope)
   e = expression whose type needs to be found

   Result: type of e, if the type can be found;
           otherwise (if there is a type error or an undefined reference) None *)
Definition type_of_expr (sc : option VS.t) (tmap : VM.t (ftype * fcomponent)) (e : HiF.hfexpr) : option ftype :=
    type_of_expr' (type_of_ref sc tmap) e.

(* Determines the type-and-kind map of a statement list

   sc = current scope
   tmap_earlier = type-and-kind map of all references defined earlier (possibly including some that are out of scope)
   ssl = list of statements

   Result: tmap_earlier, extended with the components defined in ssl.
           However, if there is an error (a doubly defined reference,
           an undefined instance or other reference, a type-incorrect
           connect) then the result is None *)
Fixpoint statements_tmap (sc : VS.t) (tmap_earlier : VM.t (ftype * fcomponent)) (ssl : HiF.hfstmt_seq) : option (VS.t * VM.t (ftype * fcomponent)) :=
    match ssl with
    | Qnil => Some (sc, tmap_earlier)
    | Qcons s ssl' => match statement_tmap sc tmap_earlier s with
                      | Some (sc_s, tmap_s) => statements_tmap sc_s tmap_s ssl'
                      | None => None
                      end
    end
with statement_tmap (sc : VS.t) (tmap_earlier : VM.t (ftype * fcomponent)) (s : HiF.hfstmt) : option (VS.t * VM.t (ftype * fcomponent)) :=
    match s with
    | Sskip => Some (sc, tmap_earlier)
    | Swire w t => if ~~VM.find w tmap_earlier then Some (VS.add w sc, VM.add w (t, Wire) tmap_earlier)
                                               else None
    | Sreg r rt => if ~~VM.find r tmap_earlier then Some (VS.add r sc, VM.add r (type rt, Register) tmap_earlier)
                                               else None
    | Sinst i mi => match VM.find i tmap_earlier, module_type mi with
                    | None, Some t => Some (VS.add i sc, VM.add i (t, Instanceof) tmap_earlier)
                    | _, _ => None
                    end
    | Snode n e => match VM.find n tmap_earlier, type_of_expr (Some sc) tmap_earlier e with
                   | None, Some t => Some (VS.add n sc, VM.add n (t, Node) tmap_earlier)
                   | _, _ => None
                   end
    | Sfcnct r e => match type_of_ref (Some sc) tmap_earlier r, type_of_expr (Some sc) tmap_earlier e with
                    | Some tr, Some te => if ftype_mux false tr te then Some (sc, tmap_earlier)
                                                                   else None
                    | _, _ => None
                    end
    | Sinvalid r => if type_of_ref (Some sc) tmap_earlier r then Some (sc, tmap_earlier)
                                                            else None
    | Swhen c ssl_true ssl_false => match type_of_expr (Some sc) tmap_earlier c, statements_tmap sc tmap_earlier ssl_true with
                                    | Some (Gtyp (Fuint _)), Some (_, tmap_true) => match statements_tmap sc tmap_true ssl_false with
                                                                                    | Some (_, tmap_false) => Some (sc, tmap_false)
                                                                                    | None => None
                                                                                    end
                                    | _, _ => None
                                    end
    | _ => None
    end.

(* Determines the type-and-kind map of a list of modules

   mml = sequence of modules whose type-and-kind map needs to be determined
         (the intention is that this is called with the globally defined mml)

   Result: a map of type-and-kind maps;
           for every module, there is a separate type-and-kind map.
           However, if some of the modules contain errors, None is returned. *)
Fixpoint module_tmap (mml : seq HiF.hfmodule) : option (VM.t (VM.t (ftype * fcomponent))) :=
    match mml with
    | [::] => Some (VM.empty (VM.t (ftype * fcomponent)))
    | FInmod mi ppl ssl :: mml' => match ports_tmap ppl with
                                   | Some pk => match statements_tmap (VKS.key_set pk) pk ssl, module_tmap mml' with
                                                | Some sk, Some tmap_earlier => match VM.find mi tmap_earlier with
                                                                                | Some _ => None
                                                                                | None => Some (VM.add mi (snd sk) tmap_earlier)
                                                                                end
                                                | _, _ => None
                                                end
                                   | None => None
                                   end
    | _ => None
    end.

Definition circuit_tmap_uninferred : option (VM.t (VM.t (ftype * fcomponent))) :=
    module_tmap mml.

(* Properties of circuit_tmap_uninferred *)

(* find_module is correct: if it finds a module, it is in mml. *)
Lemma find_module_in : forall (mi : VarOrder.T) (m : HiF.hfmodule),
    find_module mi = Some m -> List.In m mml.
Admitted.


(* If the circuit tmap is constructed, there are no external modules. *)
Lemma no_external_modules :
    circuit_tmap_uninferred <> None ->
    all (fun (m : HiF.hfmodule) => match m with
                                   | FInmod _ _ _ => true
                                   | FExmod _ _ _ => false
                                   end) mml.
Admitted.

(* type_of_ref is not affected by additional defined components *)
Lemma type_of_ref_super_tmap :
    forall (tmap_small tmap_large : VM.t (ftype * fcomponent)),
        (forall i : VM.key, VM.find i tmap_small <> None -> VM.find i tmap_small = VM.find i tmap_large) ->
        forall (sc : VS.t) (r : HiF.href),
            type_of_ref (Some sc) tmap_small r <> None ->
            type_of_ref (Some sc) tmap_small r = type_of_ref (Some sc) tmap_large r.
Admitted.

(* type_of_ref is not affected by extending the scope. *)
Lemma type_of_ref_unscope :
    forall (tmap : VM.t (ftype * fcomponent)) (sc : VS.t) (r : HiF.href),
        type_of_ref (Some sc) tmap r <> None ->
        type_of_ref (Some sc) tmap r = type_of_ref None tmap r.
Admitted.

(* type_of_expr is not affected by additional defined components *)
Lemma type_of_expr_super_tmap :
    forall (tmap_small tmap_large : VM.t (ftype * fcomponent)),
        (forall i : VM.key, VM.find i tmap_small <> None -> VM.find i tmap_small = VM.find i tmap_large) ->
        forall (sc : VS.t) (e : HiF.hfexpr),
            type_of_expr (Some sc) tmap_small e <> None ->
            type_of_expr (Some sc) tmap_small e = type_of_expr (Some sc) tmap_large e.
Admitted.

(* type_of_ref is not affected by extending the scope. *)
Lemma type_of_expr_unscope :
    forall (tmap : VM.t (ftype * fcomponent)) (sc : VS.t) (e : HiF.hfexpr),
        type_of_expr (Some sc) tmap e <> None ->
        type_of_expr (Some sc) tmap e = type_of_expr None tmap e.
Admitted.

(* statements_tmap only extends a type-and-kind map, it never replaces already defined components *)
Lemma statements_tmap_never_replaces :
    forall (ssl : HiF.hfstmt_seq) (sc_old sc_new : VS.t) (tmap_old tmap_new : VM.t (ftype * fcomponent)),
        statements_tmap sc_old tmap_old ssl = Some (sc_new, tmap_new) ->
        (forall i : VarOrder.t, VS.mem i sc_old -> VS.mem i sc_new) /\
        (forall i : VarOrder.t, VM.find i tmap_old <> None -> VM.find i tmap_old = VM.find i tmap_new)
with statement_tmap_never_replaces :
    forall (s : HiF.hfstmt) (sc_old sc_new : VS.t) (tmap_old tmap_new : VM.t (ftype * fcomponent)),
        statement_tmap sc_old tmap_old s = Some (sc_new, tmap_new) ->
        (forall i : VarOrder.t, VS.mem i sc_old -> VS.mem i sc_new) /\
        (forall i : VarOrder.t, VM.find i tmap_old <> None -> VM.find i tmap_old = VM.find i tmap_new).
Admitted.

(* Auxiliary definition for the next lemma:
   true if instance statements refer to modules that actually exist in the circuit *)
Fixpoint hfstmt_inst_in_mml (s : HiF.hfstmt) : bool :=
    match s with
    | Sinst ii mi => if find_module mi is Some _ then true else false
    | Swhen _ ssl_true ssl_false => hfstmt_seq_inst_in_mml ssl_true && hfstmt_seq_inst_in_mml ssl_false
    | _ => true
    end
with hfstmt_seq_inst_in_mml (ssl : HiF.hfstmt_seq) : bool :=
    match ssl with
    | Qnil => true
    | Qcons s ssl' => hfstmt_inst_in_mml s && hfstmt_seq_inst_in_mml ssl'
    end.

(* If statements_tmap is defined, all instance statements refer to existing modules. *)
Lemma statements_tmap_inst_defined :
    forall (ssl : HiF.hfstmt_seq) (sc : VS.t) (tmap_earlier : VM.t (ftype * fcomponent)),
        statements_tmap sc tmap_earlier ssl <> None -> hfstmt_seq_inst_in_mml ssl
with statement_tmap_inst_defined :
    forall (s : HiF.hfstmt) (sc : VS.t) (tmap_earlier : VM.t (ftype * fcomponent)),
        statement_tmap sc tmap_earlier s <> None -> hfstmt_inst_in_mml s.
Admitted.

(* If circuit_tmap_uninferred <> None, then ports_tmap and statements_tmap are defined. *)
Lemma module_statements_tmap :
    circuit_tmap_uninferred <> None ->
        forall (mm : HiF.hfmodule), List.In mm mml ->
                     match mm with
                     | FInmod mi ppl ssl => match ports_tmap ppl with
                                            | Some pk => statements_tmap (VKS.key_set pk) pk ssl <> None
                                            | None => False
                                            end
                     | FExmod _ _ _ => False
                     end.
Admitted.

(* circuit_tmap_uninferred contains information about the modules in mml. *)
Lemma ctu_corresponds_to_mml :
    match circuit_tmap_uninferred with
    | Some ctu => forall mi : VarOrder.T,
                      find_module mi <> None <-> VM.find mi ctu <> None
    | None => True
    end.
Admitted.

(* If circuit_tmap_uninferred is defined, then
   different modules in mml have different module identifiers. *)
Lemma module_identifiers_uniq :
    circuit_tmap_uninferred <> None ->
    uniq (map (fun (mm : HiF.hfmodule) => match mm with
                                          | FInmod mi _ _
                                          | FExmod mi _ _ => mi
                                          end) mml).
Admitted.

(* older, weaker form of the theorem:
    forall (m1 m2 : HiF.hfmodule),
        m1 \in mml -> m2 \in mml -> m1 <> m2 ->
        match m1, m2 with
        | FInmod mi1 _ _, FInmod mi2 _ _ => mi1 <> mi2
        | _, _ => False
        end.
Proof.
unfold circuit_tmap_uninferred, find_module.
induction mml as [|[mi ppl ssl|] mml'] ; try by done.
simpl ; intros.
rewrite in_cons in H0 ; rewrite in_cons in H1.
move /orP : H0 => [/eqP H0|H0] ; move /orP : H1 => [/eqP H1|H1].
* subst m1 m2 ; by contradict H2.
* 1: subst m1 ; rename m2 into m1.
  2: subst m2 ; rename H0 into H1.
  1,2: destruct mm as [mi ppl ssl|mi ppl ssl].
  1-4: destruct (ports_tmap ppl) as [pk|] ; last by contradict H.
  1-4: destruct (statements_tmap (VKS.key_set pk) pk ssl) as [sk|] ; last by contradict H.
  1-4: destruct (module_tmap mml') as [tmap_earlier|] eqn: Htme ; last by contradict H.
  1-4: destruct (VM.find mi tmap_earlier) eqn: Hfind ; first by contradict H.
  1-4: clear -Htme Hfind H1 H2 ; revert tmap_earlier x Htme Hfind H1 H2.
  1-4: induction mml' as [|[mi' ppl' ssl'|mi' ppl' ssl'] mml'] ;
            simpl ; intros ; try done.
  1-4: destruct (ports_tmap ppl') as [pk|] ; last by contradict Htme.
  1-4: destruct (statements_tmap (VKS.key_set pk) pk ssl') as [sk|] ; last by contradict Htme.
  1-4: destruct (module_tmap mml') as [tmap_earlier'|] ; last by contradict Htme.
  1-4: destruct (VM.find mi' tmap_earlier') eqn: Hfind' ; first by contradict Htme.
  1-4: injection Htme ; clear Htme ; intros ; subst tmap_earlier.
  1-4: rewrite in_cons in H1 ; move /orP : H1 => [/eqP H1|H1].
  + 1,3,5,7: subst x mi'.
    1-4: by rewrite VM.Lemmas.find_add_eq // /VM.M.SE.eq in Hfind.
  + 1-4: apply IHmml' with (tmap_earlier := tmap_earlier') ; try done.
    1-4: destruct (mi == mi') eqn: Hmi ; first by rewrite (VM.Lemmas.find_add_eq Hmi) in Hfind.
    1-4: by rewrite (VM.Lemmas.find_add_neq (elimF idP Hmi)) in Hfind.
* apply IHmml' ; try assumption.
  destruct mm as [mi ppl ssl|mi ppl ssl].
  1,2: destruct (ports_tmap ppl) as [pk|] ; last by contradict H.
  1,2: destruct (statements_tmap (VKS.key_set pk) pk ssl) as [sk|] ; last by contradict H.
  1,2: destruct (module_tmap mml') as [tmap_earlier|] ; done.
Qed.
*)

End Kinds_and_Types.

(*************************************************************************)
(*************************************************************************)
(***                                                                   ***)
(***                                                                   ***)
(***     Second main section: InferWidths_and_InferResets              ***)
(***                                                                   ***)
(***     Find the implicit widths and reset types of all components    ***)
(***                                                                   ***)
(***                                                                   ***)
(*************************************************************************)
(*************************************************************************)

Section InferWidths_and_InferResets.

Hypothesis uninferred_circuit_correct : circuit_tmap_uninferred <> None.

(* In a connect statement, the width of the read signal can influence the width of the written signal.
   Additionally, if either has an abstract reset type, it is concretized based on the other one.

   tw = type of the signal that is written
   tr = type of the signal that is read

   Result: a pair of types, suggestions for new (width-extended and concretized) types instead of tw and tr. *)
Definition unify_width_gtyp (tw : fgtyp) (tr : fgtyp) : option (fgtyp * fgtyp) :=
    match tw, tr with
    | Fuint          _,   Fuint          _
    | Fuint          _,   Fuint_implicit _
    | Fuint          _,   Fuint_implicit_eq1 => Some (tw, tr)
    | Fuint          1,   Freset             => Some (tw, Fuint_implicit_eq1) (* according to the spec, the width must be 1 *)
    | Fuint_implicit w,   Fuint          v
    | Fuint_implicit w,   Fuint_implicit v   => Some (Fuint_implicit (maxn w v), tr)
    | Fuint_implicit 0,   Fuint_implicit_eq1
    | Fuint_implicit 0,   Freset
    | Fuint_implicit 1,   Fuint_implicit_eq1
    | Fuint_implicit 1,   Freset             => Some (Fuint_implicit_eq1, Fuint_implicit_eq1)
    | Fuint_implicit_eq1, Fuint          1
    | Fuint_implicit_eq1, Fuint_implicit 0
    | Fuint_implicit_eq1, Fuint_implicit 1   => Some (tw, tr)
    | Fuint_implicit_eq1, Freset             => Some (Fuint_implicit_eq1, Fuint_implicit_eq1)
    | Fsint          _,   Fsint          _
    | Fsint          _,   Fsint_implicit _   => Some (tw, tr)
    | Fsint_implicit w,   Fsint          v
    | Fsint_implicit w,   Fsint_implicit v   => Some (Fsint_implicit (maxn w v), tr)
    | Freset,             Fuint          1
    | Freset,             Fuint_implicit 0
    | Freset,             Fuint_implicit 1
    | Freset,             Fuint_implicit_eq1 => Some (Fuint_implicit_eq1, tr)
    | Freset,             Fasyncreset
    | Fasyncreset,        Freset            => Some (Fasyncreset, Fasyncreset)
    | _, _ => if tw == tr then Some (tw, tr) else None
    end.

(* In a connect statement, the width of the read signal can influence the width of the written signal.
   Additionally, if either has an abstract reset type, it is concretized based on the other one.
   This function applies the principle to the ground-type elements of the current types.

   fl = flip value: if it is Flipped, the role of tw and tr is swapped.
   tw = type of the signal that is written
   tr = type of the signal that is read

   Result: a pair of types, suggestions for new types instead of tw and tr. *)
Fixpoint unify_width (fl : fflip) (tw : ftype) (tr : ftype) : option (ftype * ftype) :=
    match tw, tr, fl with
    | Gtyp gtw, Gtyp gtr, Nflip => match unify_width_gtyp gtw gtr with
                                   | Some (ugtw, ugtr) => Some (Gtyp ugtw, Gtyp ugtr)
                                   | None => None
                                   end
    | Gtyp gtw, Gtyp gtr, Flipped => match unify_width_gtyp gtr gtw with
                                     | Some (ugtr, ugtw) => Some (Gtyp ugtw, Gtyp ugtr)
                                     | None => None
                                     end
    | Atyp tw' nw, Atyp tr' nr, _ => if nw==nr then match unify_width fl tw' tr' with
                                                    | Some (utw', utr') => Some (Atyp utw' nw, Atyp utr' nr)
                                                    | None => None
                                                    end
                                               else None
    | Btyp ffw, Btyp ffr, _ => match unify_width_fields fl ffw ffr with
                               | Some (uffw, uffr) => Some (Btyp uffw, Btyp uffr)
                               | None => None
                               end
    | _, _, _ => None
    end
with unify_width_fields (fl : fflip) (ffw : ffield) (ffr : ffield) : option (ffield * ffield) :=
    match ffw, ffr with
    | Fnil, Fnil => Some (Fnil, Fnil)
    | Fflips vw fw tw ffw', Fflips vr fr tr ffr' => if (vw==vr) && (fw==fr) then match unify_width (if fl==fw then Nflip else Flipped) tw tr, unify_width_fields fl ffw' ffr' with
                                                                                 | Some (utw, utr), Some (uffw', uffr') => Some (Fflips vw fw utw uffw', Fflips vr fr utr uffr')
                                                                                 | _, _ => None
                                                                                 end
                                                                            else None
    | _, _ => None
    end.

(* To allow connect statements to set a *part* of an aggregate component,
   we define functions that do such a replacement.  The problematic part is
   that the recursion of a type definition and the recursion of a reference
   go the other way round, so we cannot just descend into them together.

   I have chosen to handle the situation by functions that return a
   "type with a hole": a function that maps a type to a type, together with
   the original type that was in the hole.  Then, the hole can be replaced
   by the new type. *)

(* Helper function for repl_type_part'.
   It finds a field in a bundle type and constructs the "type with a hole"
   where the hole is at that field.

   v = identifier of field to be found
   ff = bundle type (that should contain v)

   Result: a pair, namely the "type with a hole" constructed from ff, and the original type of v
           However, if v does not exist in bundle type ff, None is returned. *)
Fixpoint repl_ffield_part (v : VarOrder.T) (ff : ffield) : option ((ftype -> ffield) * ftype) :=
    match ff with
    | Fnil => None
    | Fflips v' fl t ff' => if v==v' then Some (fun (t' : ftype) => Fflips v' fl t' ff', t)
                                     else match repl_ffield_part v ff' with
                                          | Some (ffn, old_t) => Some (fun (t' : ftype) => Fflips v' fl t (ffn t'), old_t)
                                          | None => None
                                          end
    end.

(* construct a "type with a hole" for a reference

   r = reference that should get a new type
   old_comp_type = old type of the base reference of r

   Result: a pair, namely a "type with a hole" for the base reference of r where the hole corresponds to r,
           and the original type of r itself
           However, if the type does not fit, None is returned *)
Fixpoint repl_type_part' (r : HiF.href) (old_comp_type : ftype) : option ((ftype -> ftype) * ftype) :=
    match r with
    | Eid _ => Some (fun (t : ftype) => t, old_comp_type)
    | Esubfield r' v => match repl_type_part' r' old_comp_type with
                        | Some (fn, Btyp ff) => match repl_ffield_part v ff with
                                                | Some (ffn, old_t) => Some (fun (t : ftype) => fn (Btyp (ffn t)), old_t)
                                                | None => None
                                                end
                        | _ => None
                        end
    | Esubindex r' _
    | Esubaccess r' _ => match repl_type_part' r' old_comp_type with
                         | Some (fn, Atyp old_t n) => Some (fun (t : ftype) => fn (Atyp t n), old_t)
                         | _ => None
                         end
    end.

(* Replace the type of a reference.

   r = reference that should get a new type
   old_comp_type = original type of the base reference of r
   new_part_type = new type that r should get

   Result: old_comp_type with the part for r replaced by new_part_type.
           However, if the type doesn’t fit r, None is returned. *)
Definition repl_type_part (r : HiF.href) (old_comp_type : ftype) (new_part_type : ftype) : option ftype :=
    match repl_type_part' r old_comp_type with
    | Some (fn, _) => Some (fn new_part_type)
    | None => None
    end.

(* Iterate once through a statement list and update types accordingly

   tmap = type-and-kind map for all components in the current module
   ssl = statement list for the current module

   Result: updated tmap, where connections and register reset values have extended
   widths or concretized resets. Register reset values must have passive types. *)
Fixpoint width_iter (tmap : VM.t (ftype * fcomponent)) (ssl : HiF.hfstmt_seq) : option (VM.t (ftype * fcomponent)) :=
    match ssl with
    | Qnil => Some tmap
    | Qcons s ssl' => match width_iter_one tmap s with
                      | Some tmap_s => width_iter tmap_s ssl'
                      | None => None
                      end
    end
with width_iter_one (tmap : VM.t (ftype * fcomponent)) (st : HiF.hfstmt) : option (VM.t (ftype * fcomponent)) :=
    match st with
    | Sskip
    | Swire _ _
    | Sinst _ _ => Some tmap
    | Sreg r reg =>
        match reset reg with
        | NRst => Some tmap
        | Rst _ reset_value =>
            match VM.find r tmap, type_of_expr None tmap reset_value with
            | Some (reg_type, Register), Some reset_type =>
                if is_passive reg_type && is_passive reset_type then
                  match unify_width Nflip reg_type reset_type with
                  | Some (new_reg_type, _) =>
                      Some (VM.add r (new_reg_type, Register) tmap)
                  | None => None
                  end
                else None
            | _, _ => None
            end
        end
    | Snode n e => match type_of_expr None tmap e with
                   | Some t => Some (VM.add n (t, Node) tmap)
                   | None => None
                   end
    | Sfcnct r (Eref r') => (* bidirectional connect. unify_width suggests a new type for both sides
                               (and takes into account the flipped parts correctly).  We replace the
                               two references one after another because they might have the same base_ref. *)
                            match type_of_ref None tmap r, type_of_ref None tmap r' with
                            | Some tr, Some tr' => match unify_width Nflip tr tr', VM.find (HiF.base_ref r) tmap with
                                                   | Some (ut, ut'), Some (bt, bc) => match repl_type_part r bt ut with
                                                                                      | Some nt => let tmap_r := VM.add (HiF.base_ref r) (nt, bc) tmap
                                                                                                   in match VM.find (HiF.base_ref r') tmap_r with
                                                                                                      | Some (bt', bc') => match repl_type_part r' bt' ut' with
                                                                                                                           | Some nt' => Some (VM.add (HiF.base_ref r') (nt', bc') tmap_r)
                                                                                                                           | None => None
                                                                                                                           end
                                                                                                      | None => None
                                                                                                      end
                                                                                      | None => None
                                                                                      end
                                                   | _, _ => None
                                                   end
                            | _, _ => None
                            end
    | Sfcnct r e => match type_of_ref None tmap r, type_of_expr None tmap e with
                    | Some tr, Some te => match unify_width Nflip tr te, VM.find (HiF.base_ref r) tmap with
                                          | Some (ut, _), Some (bt, bc) => match repl_type_part r bt ut with
                                                                           | Some nt => Some (VM.add (HiF.base_ref r) (nt, bc) tmap)
                                                                           | None => None
                                                                           end
                                          | _, _ => None
                                          end
                    | _, _ => None
                    end
    | Sinvalid r => Some tmap
    | Swhen c ssl_true ssl_false => match width_iter tmap ssl_true with
                                    | Some tmap_true => width_iter tmap_true ssl_false
                                    | None => None
                                    end
    | _ => None (* Smem *)
    end.

Lemma width_iter_one_reg_preserves_other_components
    (tmap updated : VM.t (ftype * fcomponent)) (r x : VarOrder.T)
    (reg : HiF.hfreg) :
    x != r ->
    width_iter_one tmap (Sreg r reg) = Some updated ->
    VM.find x updated = VM.find x tmap.
Proof.
move=> Hneq Hiter.
rewrite /= in Hiter.
destruct (reset reg) as [|trigger value].
- by inversion Hiter.
- destruct (VM.find r tmap) as [[reg_type component]|] eqn:Hreg;
    last discriminate.
  destruct component; try discriminate.
  destruct (type_of_expr None tmap value) as [value_type|]; last discriminate.
  destruct (is_passive reg_type && is_passive value_type); last discriminate.
  destruct (unify_width Nflip reg_type value_type) as [[new_reg new_value]|];
    last discriminate.
  inversion Hiter; subst updated.
  apply VM.Lemmas.find_add_neq.
  by move/negP: Hneq.
Qed.

(* In designs with multiple modules, the type information of instances is stored twice,
   namely once as the interface of the module, and once as the type of the instance.
   Before going through the statements of a module to extend widths (as in width_iter),
   we have to reconcile that information.
   We do it like this: the module interface should contain the authoritative type information.
   Just before calling width_iter, the type information for every instance component
   in the current module is copied from the module interface (using unify_width_down),
   and after width_iter, the updated type information is copied back to the module
   interface (using unify_width_up).

   Note that a module may contain multiple instances of the same type; when unifying up,
   one should also take into account these types. *)

(* calculate the interface type of a module but take the type information from tmap,
   so that concretized types show up in the interface type.

   tmap_mi' = type-and-kind map of the module whose interface type is constructed
   ppl = port list of the module whose interface type is constructed

   Result: the interface type of the module, but types of ports are taken from tmap_mi' *)
Fixpoint port_type_with_widths_from_tmap (tmap_mi' : VM.t (ftype * fcomponent)) (ppl : seq HiF.hfport) : option ffield :=
    match ppl with
    | [::] => Some Fnil
    | Finput p _ :: ppl' => match VM.find p tmap_mi', port_type_with_widths_from_tmap tmap_mi' ppl' with
                            | Some (t, In_port), Some ff => Some (Fflips p Flipped t ff)
                            | _, _ => None
                            end
    | Foutput p _ :: ppl' => match VM.find p tmap_mi', port_type_with_widths_from_tmap tmap_mi' ppl' with
                             | Some (t, Out_port), Some ff => Some (Fflips p Nflip t ff)
                             | _, _ => None
                             end
    end.

(* unify widths down, that is, collect width information from modules that are instantiated in the current module.

   circ_tmap = complete type-and-kind map of all components (this map is only read).
   tmap_mi = type-and-kind map for the current module (this map is being changed) = VM.find mi circ_tmap.
          We provide two separate maps because changing tmap may be less efficient than only changing tmap_mi.
   ssl = list of statements in the current module.

   Result: tmap_mi, with instances adapted to the type information from other modules in circ_tmap *)
Fixpoint unify_width_down (circ_tmap : VM.t (VM.t (ftype * fcomponent))) (tmap_mi : VM.t (ftype * fcomponent)) (ssl : HiF.hfstmt_seq) : option (VM.t (ftype * fcomponent)) :=
    match ssl with
    | Qnil => Some tmap_mi
    | Qcons (Sinst ii mi') ssl' => match find_module mi', VM.find mi' circ_tmap with
                                   | Some (FInmod _ ppl _), Some tmap_mi' => match port_type_with_widths_from_tmap tmap_mi' ppl with
                                                                             | Some t => unify_width_down circ_tmap (VM.add ii (Btyp t, Instanceof) tmap_mi) ssl'
                                                                             | None => None
                                                                             end
                                   | _, _ => None
                                   end
    | Qcons (Swhen _ sst ssf) ssl' => match unify_width_down circ_tmap tmap_mi sst with
                                      | Some tmap_mit => match unify_width_down circ_tmap tmap_mit ssf with
                                                         | Some tmap_mif => unify_width_down circ_tmap tmap_mif ssl'
                                                         | None => None
                                                         end
                                      | None => None
                                      end
    | Qcons _ ssl' => unify_width_down circ_tmap tmap_mi ssl'
    end.

(* update the interface type of a module based on the type of (one of its) instances

   tmap_mi' = type-and-kind map of the (outer) module that needs to be updated
   ff = new type of the module interface

   Result: tmap_mi', where the types of its ports are extended with information in ff.
           (Note that we call ftype_mux with the old and new type information, so that
           multiple instances of the same module are handled correctly.)
           However, if an error occurs (e.g. wrong port type, types cannot be reconciled),
           the result is None. *)
Fixpoint unify_ports_up (tmap_mi' : VM.t (ftype * fcomponent)) (ff : ffield) : option (VM.t (ftype * fcomponent)) :=
    match ff with
    | Fnil => Some tmap_mi'
    | Fflips p Flipped new_t ff' => match VM.find p tmap_mi' with
                                    | Some (old_t, In_port ) => match ftype_mux false old_t new_t with
                                                                | Some uni_t => unify_ports_up (VM.add p (uni_t, In_port ) tmap_mi') ff'
                                                                | None => None
                                                                end
                                    | _ => None
                                    end
    | Fflips p Nflip   new_t ff' => match VM.find p tmap_mi' with
                                    | Some (old_t, Out_port) => match ftype_mux false old_t new_t with
                                                                | Some uni_t => unify_ports_up (VM.add p (uni_t, Out_port) tmap_mi') ff'
                                                                | None => None
                                                                end
                                    | _ => None
                                    end
    end.

(* unify widths up, that is, copy width information from instances in the current module to their definitions.

   circ_tmap = type-and-kind map of all components (this map is being changed).
   tmap_mi = type-and-kind map for the current module (this map is only read) = (VM.find mi circ_tmap).
          We provide two separate maps because calling VM.find mi circ_tmap every time may be less efficient.
   ssl = list of statements in the current module.

   Result: circ_tmap, where the types of all ports of all modules are extended according 
           to instances in tmap_mi. However, if any error occurs, None is returned. *)
Fixpoint unify_width_up (circ_tmap : VM.t (VM.t (ftype * fcomponent))) (tmap_mi : VM.t (ftype * fcomponent)) (ssl : HiF.hfstmt_seq) : option (VM.t (VM.t (ftype * fcomponent))) :=
    match ssl with
    | Qnil => Some circ_tmap
    | Qcons (Sinst ii mi') ssl' => match VM.find mi' circ_tmap, VM.find ii tmap_mi with
                                   | Some tmap_mi', Some (Btyp ff, Instanceof) => match unify_ports_up tmap_mi' ff with
                                                                                  | Some new_tmap_mi' => unify_width_up (VM.add mi' new_tmap_mi' circ_tmap) tmap_mi ssl'
                                                                                  | None => None
                                                                                  end
                                   | _, _ => None
                                   end
    | Qcons (Swhen _ sst ssf) ssl' => match unify_width_up circ_tmap tmap_mi sst with
                                      | Some circ_tmap_true => match unify_width_up circ_tmap_true tmap_mi ssf with
                                                      | Some circ_tmap_false => unify_width_up circ_tmap_false tmap_mi ssl'
                                                      | None => None
                                                      end
                                      | None => None
                                      end
    | Qcons _ ssl' => unify_width_up circ_tmap tmap_mi ssl'
    end.

(* Take one width-and-reset-inference iteration over all modules in a list

   mml = list of modules to be handled
   circ_tmap = type-and-kind map before the iteration

   Result: circ_tmap with updated width and reset types, based on the connection statements in mml. *)
Fixpoint circuit_width_iter' (mml : seq HiF.hfmodule) (circ_tmap : VM.t (VM.t (ftype * fcomponent))) : option (VM.t (VM.t (ftype * fcomponent))) :=
    match mml with
    | [::] => Some circ_tmap
    | FInmod mi _ ssl_i :: mml' => match VM.find mi circ_tmap with
                                   | Some tmap_mi => match unify_width_down circ_tmap tmap_mi ssl_i with
                                                     | Some tmap_mi_down => match width_iter tmap_mi_down ssl_i with
                                                                            | Some tmap_mi_unif => match unify_width_up (VM.add mi tmap_mi_unif circ_tmap) tmap_mi_unif ssl_i with
                                                                                                   | Some tmap_mi_up => circuit_width_iter' mml' tmap_mi_up
                                                                                                   | None => None
                                                                                                   end
                                                                            | None => None
                                                                            end
                                                     | None => None
                                                     end
                                   | _ => None
                                   end
    | _ => None
    end.

(* Take one width-and-reset-inference iteration over the whole circuit

   circ_tmap = type-and-kind map before the iteration

   Result: circ_tmap with updated width and reset types, based on all connection statements in the circuit. *)
Definition circuit_width_iter (circ_tmap : VM.t (VM.t (ftype * fcomponent))) : option (VM.t (VM.t (ftype * fcomponent))) :=
    circuit_width_iter' mml circ_tmap.

(* Take a fixed number of width-and-reset-inference iterations over the whole circuit, for a given type-and-kind map

   n = number of iterations
   circ_tmap = type-and-kind map before the iteration

   Result: circ_tmap with updated width and reset types after n iterations *)
Fixpoint circuit_tmap_iterator (n : nat) (circ_tmap : VM.t (VM.t (ftype * fcomponent))) : option (VM.t (VM.t (ftype * fcomponent))) :=
    match n with
    | 0 => Some circ_tmap
    | n'.+1 => match circuit_width_iter circ_tmap with
               | Some circ_tmap' => circuit_tmap_iterator n' circ_tmap'
               | None => None
               end
    end.

(* Take a fixed number of width-and-reset-inference iterations over the whole circuit

   n = number of iterations

   Result: the circuit’s type-and-kind map with updated width and reset types after n iterations
           (but still with implicit types) *)
Definition circuit_tmap_implicits (n : nat) : option (VM.t (VM.t (ftype * fcomponent))) :=
    match circuit_tmap_uninferred with
    | Some ctu => match circuit_tmap_iterator n ctu with
                  | Some ctu_n => match circuit_width_iter ctu_n with
                                  | Some ctu_nplus1 => if VM.equal (VM.equal pair_eq) ctu_n ctu_nplus1 then Some ctu_n else None
                                  | None => None
                                  end
                  | None => None
                  end
    | None => None
    end.

(* Make all types explicit-width and all resets concrete

   t = type that needs to be concretized

   Result: type t, but all implicit-width elements have been updated to explicit widths.
           Also, still unresolved abstract resets are changed to synchronous resets. *)
Fixpoint make_ftype_explicit (t : ftype) : ftype :=
    match t with
    | Gtyp (Fuint_implicit w) => Gtyp (Fuint w)
    | Gtyp Fuint_implicit_eq1
    | Gtyp Freset             => Gtyp (Fuint 1)
    | Gtyp (Fsint_implicit w) => Gtyp (Fsint w)
    | Gtyp ft => Gtyp ft
    | Atyp t' n => Atyp (make_ftype_explicit t') n
    | Btyp ff => Btyp (make_ffield_explicit ff)
    end
with make_ffield_explicit (ff : ffield) : ffield :=
    match ff with
    | Fnil => Fnil
    | Fflips v f t ff' => Fflips v f (make_ftype_explicit t) (make_ffield_explicit ff')
    end.

(* Calculate the fixed point of width-and-reset inference

   n = number of iterations

   Result: If the fixed point is reached within n iterations, returns the circuit’s
           type-and-kind map with updated width and reset types, all changed to explicit.
           However, if it takes more iterations or another error occurs, None is returned. *)
Definition circuit_tmap (n : nat) : option (VM.t (VM.t (ftype * fcomponent))) :=
    match circuit_tmap_implicits n with
    | Some cti => match circuit_width_iter cti with
                  | Some cti_new => if VM.equal (VM.equal pair_eq) cti cti_new then Some (VM.fold (fun (mi : VarOrder.T) (tmap : VM.t (ftype * fcomponent)) (ct : VM.t (VM.t (ftype * fcomponent))) =>
                                                                                                   VM.add mi (VM.fold (fun (id : VarOrder.T) (ftfc : ftype * fcomponent) (t : VM.t (ftype * fcomponent)) =>
                                                                                                                        VM.add id (let (ty, c) := ftfc in (make_ftype_explicit ty, c)) t)
                                                                                                                       tmap
                                                                                                                       (VM.empty (ftype * fcomponent)))
                                                                                                           ct)
                                                                                                   cti (VM.empty (VM.t (ftype * fcomponent))))
                                                                               else None
                  | None => None
                  end
    | None => None
    end.

(* Tests whether a type has any abstract reset parts

   t = type that is tested

   Result: true iff the type does not contain any abstract Fresets *)
Fixpoint ftype_is_concrete (t : ftype) : bool :=
    match t with
    | Gtyp Freset => false
    | Gtyp _ => true
    | Atyp t _ => ftype_is_concrete t
    | Btyp ff => ffield_is_concrete ff
    end
with ffield_is_concrete (ff : ffield) : bool :=
    match ff with
    | Fnil => true
    | Fflips _ _ t ff => ftype_is_concrete t && ffield_is_concrete ff
    end.

(* Tests whether a type has any implicit-width or abstract reset parts

   t = type that is tested

   Result: true iff the type does not contain any implicit-width parts, nor abstract Fresets *)
Fixpoint ftype_is_explicit_and_concrete (t : ftype) : bool :=
    match t with
    | Gtyp (Fuint_implicit _)
    | Gtyp  Fuint_implicit_eq1
    | Gtyp (Fsint_implicit _)
    | Gtyp Freset             => false
    | Gtyp _                  => true
    | Atyp elt _ => ftype_is_explicit_and_concrete elt
    | Btyp ff => ffield_is_explicit_and_concrete ff
    end
with ffield_is_explicit_and_concrete (ff : ffield) : bool :=
    match ff with
    | Fnil => true
    | Fflips _ _ t ff => ftype_is_explicit_and_concrete t && ffield_is_explicit_and_concrete ff
    end.

(* Properties of definitions in this section *)

(* repl_ffield_part is correct: it creates the "type with a hole" *)
Lemma repl_ffield_part_correct :
    forall (v : VarOrder.T) (ff : ffield),
        match repl_ffield_part v ff with
        | Some (fn, ft) => fn ft = ff /\
                           let fix aux fx := (match fx with
                                              | Fflips v' f t fxs => if (v == v') then Some t else aux fxs
                                              | Fnil => None
                                              end)
                           in aux ff = Some ft
        | None => True
        end.
Admitted.

(* repl_type_part' is correct: it creates the "type with a hole" *)
Lemma repl_type_part'_correct :
    forall (tmap: VM.t (ftype * fcomponent)) (r : HiF.href),
        match VM.find (HiF.base_ref r) tmap with
        | Some (old_comp_type, _) => match repl_type_part' r old_comp_type with
                                     | Some (fn, old_part_type) => fn old_part_type = old_comp_type /\
                                                                   type_of_ref None tmap r = Some old_part_type
                                     | None => True
                                     end
        | None => True
        end.
Admitted.

(* Partial order between types

   t1 = type that should be smaller
   t2 = type that should be larger

   Result: true if really t2 is more concrete than t1 in the sense:
           - either they are both implicit-width types and t2 is wider than (or equally wide as) t1
           - or t1 is an abstract reset type and t2 is a more concrete reset type
           - or t1 is Fuint_implicit with width <= 1 and t2 is Fuint_implicit_eq1
             (because this concretization can also happen)
           and this order is trivially extended to aggregate types *)
Fixpoint more_concrete_type (t1 t2 : ftype) : bool :=
    match t1, t2 with
    | Gtyp (Fuint_implicit w1), Gtyp (Fuint_implicit w2)
    | Gtyp (Fsint_implicit w1), Gtyp (Fsint_implicit w2) => w1 <= w2
    | Gtyp (Fuint_implicit 0 ), Gtyp Fuint_implicit_eq1
    | Gtyp (Fuint_implicit 1 ), Gtyp Fuint_implicit_eq1
    | Gtyp Freset             , Gtyp Fuint_implicit_eq1
    | Gtyp Freset             , Gtyp Fasyncreset        => true
    | Gtyp ft1, Gtyp ft2 => ft1==ft2
    | Atyp t1' n1, Atyp t2' n2 => more_concrete_type t1' t2' && (n1==n2)
    | Btyp ff1, Btyp ff2 => more_concrete_fields ff1 ff2
    | _, _ => false
    end
with more_concrete_fields (ff1 ff2 : ffield) : bool :=
    match ff1, ff2 with
    | Fnil, Fnil => true
    | Fflips v1 f1 t1 ff1', Fflips v2 f2 t2 ff2' => (v1==v2) && (f1==f2) && more_concrete_type t1 t2 && more_concrete_fields ff1' ff2'
    | _, _ => false
    end.

(* It's really a partial order: reflexive, transitive, antisymmetric *)
Lemma more_concrete_type_reflexive :
    forall (t : ftype),
        more_concrete_type t t
with more_concrete_fields_reflexive :
    forall (ff : ffield),
        more_concrete_fields ff ff.
Proof.
* clear more_concrete_type_reflexive.
  induction t as [[| |[|[|]]| | | | |]|elt IHelt n|ff] ; simpl ; try done.
  by rewrite eq_refl andbT.
* clear more_concrete_fields_reflexive.
  induction ff as [|v fl t ff] ; simpl ; try done.
  by rewrite eq_refl eq_refl more_concrete_type_reflexive IHff.
Qed.

Lemma more_concrete_type_transitive :
    forall (t2 t1 t3 : ftype),
        more_concrete_type t1 t2 -> more_concrete_type t2 t3 -> more_concrete_type t1 t3
with more_concrete_fields_transitive :
    forall (ff2 ff1 ff3 : ffield),
        more_concrete_fields ff1 ff2 -> more_concrete_fields ff2 ff3 -> more_concrete_fields ff1 ff3.
Proof.
* clear more_concrete_type_transitive.
  induction t2 as [ft2|elt2 IHelt2 n2|ff2] ;
      destruct t1 as [ft1|elt1 n1|ff1], t3 as [ft3|elt3 n3|ff3] ;
      try done ; simpl ; intros.
  + destruct ft1 as [[|[|w1]]|[|[|w1]]|[|[|w1]]|[|[|w1]]| | | |],
             ft2 as [[|[|w2]]|[|[|w2]]|[|[|w2]]|[|[|w2]]| | | |],
             ft3 as [[|[|w3]]|[|[|w3]]|[|[|w3]]|[|[|w3]]| | | |] ;
          simpl in H, H0 ; simpl ; try done.
    - 1,2: by rewrite (elimT eqP H) H0.
    - 1,2: by apply (leq_trans H H0).
  + 1,2: destruct ft2 as [| |[|[]]| | | | |] ; by contradict H0.
  + move /andP : H => [H /eqP H1] ; move /andP : H0 => [H0 H2].
    rewrite H1 H2 andbT.
    by apply IHelt2 ; assumption.
  + by apply more_concrete_fields_transitive with (ff2 := ff2) ; assumption.
* clear more_concrete_fields_transitive.
  induction ff2 as [|v2 fl2 t2 ff2] ;
      destruct ff1 as [|v1 fl1 t1 ff1], ff3 as [|v3 fl3 t3 ff3] ;
      try done ; simpl.
  move => /andP [/andP [/andP [/eqP H  /eqP H0] H1] H2]
          /andP [/andP [/andP [/eqP H3 /eqP H4] H5] H6].
  subst v2 v3 fl2 fl3.
  by rewrite eq_refl eq_refl (more_concrete_type_transitive t2) // IHff2 //.
Qed.

Lemma more_concrete_type_antisymmetric :
    forall (t1 t2 : ftype),
        more_concrete_type t1 t2 ->
        more_concrete_type t2 t1 ->
        t1 == t2
with more_concrete_fields_antisymmetric :
    forall (ff1 ff2 : ffield),
        more_concrete_fields ff1 ff2 ->
        more_concrete_fields ff2 ff1 ->
        ff1 == ff2.
Proof.
* clear more_concrete_type_antisymmetric.
  induction t1 as [ft1|elt1 IHelt1 n1|ff1] ;
        destruct t2 as [ft2|elt2 n2|ff2] ; simpl ; try done ; intros.
  + destruct ft1 as [[|[|w1]]|[|[|w1]]|[|[|w1]]|[|[|w1]]| | | |],
             ft2 as [[|[|w2]]|[|[|w2]]|[|[|w2]]|[|[|w2]]| | | |] ;
        simpl in H, H0 ; simpl ; try done.
    - 1,2: generalize (eqn_leq w1.+2 w2.+2) ; intro ;
           rewrite H H0 andTb in H1 ;
           rewrite (elimT eqP H1) //.
  + move /andP : H => [H _] ; move /andP : H0 => [H0 /eqP H1] ; subst n2.
    specialize (IHelt1 _ H H0).
    rewrite (elimT eqP IHelt1) //.
  + specialize (more_concrete_fields_antisymmetric _ _ H H0).
    rewrite (elimT eqP more_concrete_fields_antisymmetric) //.
* clear more_concrete_fields_antisymmetric.
  induction ff1 as [|v1 fl1 t1 ff1] ; destruct ff2 as [|v2 fl2 t2 ff2] ;
        simpl ; try done.
  move => /andP [/andP [_ H] H0] /andP [/andP [/andP [/eqP H1 /eqP H2] H3] H4].
  subst v2 fl2.
  specialize (more_concrete_type_antisymmetric _ _ H H3).
  specialize (IHff1 _ H0 H4).
  rewrite (elimT eqP more_concrete_type_antisymmetric) (elimT eqP IHff1) //.
Qed.

(* Now we shall show that the width-and-reset-inference iteration is
   monotonous according to this partial order.  That will allow us to
   guarantee that it finds the least fixed point (if it exists). *)

(* ftype_mux is monotonous *)
Lemma ftype_mux_is_monotonous :
    forall (st1 lt1 st2 lt2 : ftype) (passive : bool),
        more_concrete_type st1 lt1 ->
        more_concrete_type st2 lt2 ->
        match ftype_mux passive st1 st2, ftype_mux passive lt1 lt2 with
        | Some st, Some lt => more_concrete_type st lt
        | None, Some _ => false
        | _, None => true
        end
with ffield_mux_is_monotonous :
    forall (sff1 lff1 sff2 lff2 : ffield) (passive : bool),
        more_concrete_fields sff1 lff1 ->
        more_concrete_fields sff2 lff2 ->
        match ffield_mux passive sff1 sff2, ffield_mux passive lff1 lff2 with
        | Some sff, Some lff => more_concrete_fields sff lff
        | None, Some _ => false
        | _, None => true
        end.
Admitted.

(* unify_width is an increasing function *)
Lemma unify_width_makes_concrete :
    forall (fl : fflip) (tw1 tr1 tw2 tr2 : ftype),
        unify_width fl tw1 tr1 = Some (tw2, tr2) ->
        more_concrete_type tw1 tw2 /\
        more_concrete_type tr1 tr2
with unify_width_makes_concrete_fields:
    forall (fl : fflip) (ffw1 ffr1 ffw2 ffr2 : ffield),
        unify_width_fields fl ffw1 ffr1 = Some (ffw2, ffr2) ->
        more_concrete_fields ffw1 ffw2 /\
        more_concrete_fields ffr1 ffr2.
Admitted.

(* repl_ffield_part is monotonous *)
Lemma repl_ffield_part_more_concrete :
    forall (fld : VarOrder.T) (ffs ffl : ffield) (st lt : ftype),
        more_concrete_fields ffs ffl ->
        more_concrete_type st lt ->
        match repl_ffield_part fld ffs, repl_ffield_part fld ffl with
        | Some (ffns, oldts), Some (ffnl, oldtl) => (ffns oldts == ffs) && (ffnl oldtl == ffl) &&
                                                    more_concrete_type oldts oldtl &&
                                                    more_concrete_fields (ffns st) (ffnl lt)
        | _, _ => true
        end.
Admitted.

(* partial order between type-and-kind maps

   s = type-and-kind map that should be smaller
   l = type-and-kind map that should be larger

   The two type-and-kind maps need to have the same domain,
   and every type in l is more concrete than the corresponding type in s. *)
Lemma vm_equal_find_iff {A : Type} (cmp : A -> A -> bool) (m1 m2 : VM.t A) :
    VM.equal cmp m1 m2 = true <->
    forall k,
      match VM.find k m1, VM.find k m2 with
      | Some x, Some y => cmp x y
      | None, None => true
      | _, _ => false
      end.
Proof.
split.
* intro Heq.
  apply VM.equal_2 in Heq.
  destruct Heq as [Hdomain Hvalues].
  intro k.
  destruct (VM.find k m1) as [x|] eqn:H1,
           (VM.find k m2) as [y|] eqn:H2 ; try done.
  + apply (Hvalues k x y); apply VM.find_2; assumption.
  + exfalso.
    have Hin : VM.In k m1 by exists x; apply VM.find_2.
    apply (proj1 (Hdomain k)) in Hin.
    destruct Hin as [y Hy].
    apply VM.find_1 in Hy.
    by rewrite H2 in Hy.
  + exfalso.
    have Hin : VM.In k m2 by exists y; apply VM.find_2.
    apply (proj2 (Hdomain k)) in Hin.
    destruct Hin as [x Hx].
    apply VM.find_1 in Hx.
    by rewrite H1 in Hx.
* intro Hfind.
  apply VM.equal_1.
  split.
  + intro k; split; intros [x Hx]; apply VM.find_1 in Hx.
    - specialize (Hfind k); rewrite Hx in Hfind.
      destruct (VM.find k m2) as [y|] eqn:Hy; last done.
      exists y; by apply VM.find_2.
    - specialize (Hfind k); rewrite Hx in Hfind.
      destruct (VM.find k m1) as [y|] eqn:Hy; last done.
      exists y; by apply VM.find_2.
  + intros k x y Hx Hy.
    apply VM.find_1 in Hx; apply VM.find_1 in Hy.
    specialize (Hfind k); by rewrite Hx Hy in Hfind.
Qed.

Lemma tmap_equal_find_iff (m1 m2 : VM.t (ftype * fcomponent)) :
    VM.equal pair_eq m1 m2 = true <->
    forall k, VM.find k m1 = VM.find k m2.
Proof.
rewrite vm_equal_find_iff.
split; intros H k; specialize (H k).
* destruct (VM.find k m1) as [[t1 c1]|] eqn:H1,
           (VM.find k m2) as [[t2 c2]|] eqn:H2;
    rewrite H1 H2 in H; try done.
  simpl in H.
  move /andP : H => [/eqP Ht /eqP Hc].
  by subst t2 c2.
* rewrite H.
  destruct (VM.find k m2) as [[t c]|] eqn:H2; rewrite H2; simpl; try done.
  by rewrite !eq_refl.
Qed.

Definition tmap_is_more_concrete (s l : VM.t (ftype * fcomponent)) : Prop :=
    forall (v : VarOrder.T),
        match VM.find v s, VM.find v l with
        | Some (ts, cs), Some (tl, cl) => more_concrete_type ts tl && (cs == cl)
        | None, None => true
        | _, _ => false
        end.

(* It’s really a partial order: reflexive, transitive, and antisymmetric
   (Antisymmetry through content-equality, not structural low-level equality) *)
Lemma tmap_is_more_concrete_reflexive :
    forall tmap : VM.t (ftype * fcomponent),
        tmap_is_more_concrete tmap tmap.
Proof.
unfold tmap_is_more_concrete ; intros.
destruct (VM.find v tmap) as [[t c]|] ; last by done.
rewrite eq_refl andbT.
apply more_concrete_type_reflexive.
Qed.

Lemma tmap_is_more_concrete_transitive :
    forall (tmap2 tmap1 tmap3 : VM.t (ftype * fcomponent)),
        tmap_is_more_concrete tmap1 tmap2 ->
        tmap_is_more_concrete tmap2 tmap3 ->
        tmap_is_more_concrete tmap1 tmap3.
Proof.
unfold tmap_is_more_concrete ; intros.
specialize (H v) ; specialize (H0 v).
destruct (VM.find v tmap1) as [[t1 c1]|].
* destruct (VM.find v tmap2) as [[t2 c2]|] ; last by discriminate H.
  destruct (VM.find v tmap3) as [[t3 c3]|] ; last by discriminate H0.
  move /andP : H => [H /eqP H1] ; move /andP : H0 => [H0 /eqP H2].
  subst c3 c2 ; rewrite eq_refl andbT.
  apply (more_concrete_type_transitive H), H0.
* destruct (VM.find v tmap2) as [[]|] ; first by discriminate H.
  destruct (VM.find v tmap3) as [[]|] ; first by discriminate H0.
  done.
Qed.

Lemma tmap_is_more_concrete_antisymmetric :
    forall (tmap1 tmap2 : VM.t (ftype * fcomponent)),
        tmap_is_more_concrete tmap1 tmap2 ->
        tmap_is_more_concrete tmap2 tmap1 ->
        VM.equal pair_eq tmap1 tmap2.
Proof.
intros.
apply VM.equal_1.
unfold VM.Equivb, VM.Equiv.
split ; intros.
* specialize (H k) ; specialize (H0 k).
  unfold VM.In.
  split ; intro.
  1,2: destruct H1 as [[kt kc] H1].
  1,2: apply VM.find_1 in H1.
  1: rewrite H1 in H ; destruct (VM.find k tmap2) as [[et ec]|] eqn: H2 ; last done.
  2: rewrite H1 in H0 ; destruct (VM.find k tmap1) as [[et ec]|] eqn: H2 ; last done.
  1,2: exists (et, ec).
  1,2: apply VM.find_2, H2.
* destruct e as [et1 ec1] ; destruct e' as [et2 ec2].
  apply VM.find_1 in H1 ; apply VM.find_1 in H2.
  specialize (H k) ; specialize (H0 k).
  rewrite H1 H2 in H ; rewrite H2 H1 in H0.
  unfold Cmp ; simpl.
  move /andP : H => [H H3] ; move /andP : H0 => [H0 _].
  apply (more_concrete_type_antisymmetric H) in H0.
  by rewrite H0 H3.
Qed.

Lemma tmap_equal_iff_more_concrete (m1 m2 : VM.t (ftype * fcomponent)) :
    VM.equal pair_eq m1 m2 = true <->
    tmap_is_more_concrete m1 m2 /\ tmap_is_more_concrete m2 m1.
Proof.
split.
* move /tmap_equal_find_iff => Heq.
  split; intro k; unfold tmap_is_more_concrete in *.
  + rewrite (Heq k).
    destruct (VM.find k m2) as [[t c]|] ; last done.
    by rewrite more_concrete_type_reflexive eq_refl.
  + rewrite -(Heq k).
    destruct (VM.find k m1) as [[t c]|] ; last done.
    by rewrite more_concrete_type_reflexive eq_refl.
* intros [H12 H21].
  by apply tmap_is_more_concrete_antisymmetric.
Qed.

(* type_of_ref is monotonous *)
Lemma type_of_ref_is_monotonous :
    forall (s l : VM.t (ftype * fcomponent)) (sc : option VS.t) (r : HiF.href),
        tmap_is_more_concrete s l ->
        match type_of_ref sc s r, type_of_ref sc l r with
        | Some st, Some lt => more_concrete_type st lt
        | _, _ => true
        end.
Admitted.

(* repl_type_part' is monotonous *)
Lemma repl_type_part'_is_monotonous :
    forall (sbt lbt : ftype),
        more_concrete_type sbt lbt ->
        forall r : HiF.href,
            match repl_type_part' r sbt, repl_type_part' r lbt with
            | Some (fs, ts), Some (fl, tl) => (fs ts == sbt) &&
                                              (fl tl == lbt) &&
                                              more_concrete_type ts tl /\
                                              forall (st lt : ftype),
                                                  more_concrete_type st lt ->
                                                  more_concrete_type (fs st) (fl lt)
            | _, _ => True
            end.
Admitted.

(* repl_type_part is monotonous *)
Lemma repl_type_part_is_monotonous :
    forall (s l : VM.t (ftype * fcomponent)) (r : href VarOrder.T) (st lt : ftype),
        tmap_is_more_concrete s l ->
        more_concrete_type st lt ->
        match VM.find (HiF.base_ref r) s, VM.find (HiF.base_ref r) l with
        | Some (sbt, _), Some (lbt, _) => match repl_type_part r sbt st, repl_type_part r lbt lt with
                                          | Some snt, Some lnt => more_concrete_type snt lnt
                                          | _, _ => true
                                          end
        | _, _ => true
        end.
Admitted.

(* type_of_expr is monotonous *)
Lemma type_of_expr_is_monotonous :
    forall (s l : VM.t (ftype * fcomponent)) (sc : option VS.t) (e : HiF.hfexpr),
        tmap_is_more_concrete s l ->
        match type_of_expr sc s e, type_of_expr sc l e with
        | Some st, Some lt => more_concrete_type st lt
        | _, _ => true
        end.
Admitted.

(* unify_width is also monotonous *)
Lemma unify_width_is_monotonous :
    forall (fl : fflip) (tws trs twl trl : ftype),
        more_concrete_type tws twl ->
        more_concrete_type trs trl ->
        match unify_width fl tws trs, unify_width fl twl trl with
        | Some (ntws, ntrs), Some (ntwl, ntrl) => more_concrete_type ntws ntwl && more_concrete_type ntrs ntrl
        | _, _ => true
        end
with unify_width_fields_is_monotonous :
    forall (fl : fflip) (ffws ffrs ffwl ffrl : ffield),
        more_concrete_fields ffws ffwl ->
        more_concrete_fields ffrs ffrl ->
        match unify_width_fields fl ffws ffrs, unify_width_fields fl ffwl ffrl with
        | Some (nffws, nffrs), Some (nffwl, nffrl) => more_concrete_fields nffws nffwl && more_concrete_fields nffrs nffrl
        | _, _ => true
        end.
Admitted.

(* width_iter is monotonous *)
Lemma width_iter_is_monotonous :
    forall (s l : VM.t (ftype * fcomponent)) (ssl : HiF.hfstmt_seq),
        tmap_is_more_concrete s l ->
        match width_iter s ssl, width_iter l ssl with
        | Some ss, Some ll => tmap_is_more_concrete ss ll
        | _, _ => True
        end
with width_iter_one_is_monotonous :
    forall (s l : VM.t (ftype * fcomponent)) (st : HiF.hfstmt),
        tmap_is_more_concrete s l ->
        match width_iter_one s st, width_iter_one l st with
        | Some ss, Some ll => tmap_is_more_concrete ss ll
        | _, _ => True
        end.
Admitted.

Lemma port_type_with_widths_from_tmap_is_monotonous :
    forall (s_mi' l_mi' : VM.t (ftype * fcomponent)) (ppl : seq HiF.hfport),
        tmap_is_more_concrete s_mi' l_mi' ->
        match port_type_with_widths_from_tmap s_mi' ppl, port_type_with_widths_from_tmap l_mi' ppl with
        | Some ffs, Some ffl => more_concrete_fields ffs ffl
        | _, _ => true
        end.
Admitted.

(* partial order between circuit maps

   ss = type-and-kind map that should be smaller
   ll = type-and-kind map that should be larger

   The two type-and-kind maps need to have the same domain,
   and every type-and-kind map in ll is more concrete than the corresponding type-and-kind map in ss. *)
Definition circuit_tmap_is_more_concrete (ss ll : VM.t (VM.t (ftype * fcomponent))) : Prop :=
    forall (mi : VarOrder.T),
        match VM.find mi ss, VM.find mi ll with
        | Some s_mi, Some l_mi => tmap_is_more_concrete s_mi l_mi
        | None, None => true
        | _, _ => false
        end.

Lemma circuit_tmap_equal_find_iff (ct1 ct2 : VM.t (VM.t (ftype * fcomponent))) :
    VM.equal (VM.equal pair_eq) ct1 ct2 = true <->
    forall mi,
      match VM.find mi ct1, VM.find mi ct2 with
      | Some tm1, Some tm2 => forall v, VM.find v tm1 = VM.find v tm2
      | None, None => True
      | _, _ => False
      end.
Proof.
rewrite vm_equal_find_iff.
split; intros H mi; specialize (H mi).
* destruct (VM.find mi ct1) as [tm1|] eqn:H1,
           (VM.find mi ct2) as [tm2|] eqn:H2;
    rewrite H1 H2 in H; try done.
  by apply tmap_equal_find_iff.
* destruct (VM.find mi ct1) as [tm1|] eqn:H1,
           (VM.find mi ct2) as [tm2|] eqn:H2;
    try rewrite H1 H2 in H; rewrite H1 H2; try done.
  by apply tmap_equal_find_iff.
Qed.

(* It’s really a partial order: reflexive, transitive and antisymmetric *)
Lemma circuit_tmap_is_more_concrete_reflexive :
    forall (ct : VM.t (VM.t (ftype * fcomponent))),
        circuit_tmap_is_more_concrete ct ct.
Proof.
unfold circuit_tmap_is_more_concrete ; intros.
destruct (VM.find mi ct) as [tmap|] ; last done.
by apply tmap_is_more_concrete_reflexive.
Qed.

Lemma circuit_tmap_is_more_concrete_transitive :
    forall (ct2 ct1 ct3 : VM.t (VM.t (ftype * fcomponent))),
        circuit_tmap_is_more_concrete ct1 ct2 ->
        circuit_tmap_is_more_concrete ct2 ct3 ->
        circuit_tmap_is_more_concrete ct1 ct3.
Proof.
intros ; intro mi.
specialize (H mi) ; specialize (H0 mi).
destruct (VM.find mi ct1) as [tmap1|], (VM.find mi ct2) as [tmap2|], (VM.find mi ct3) as [tmap3|] ;
      try done.
by apply (tmap_is_more_concrete_transitive H), H0.
Qed.

Lemma circuit_tmap_is_more_concrete_antisymmetric :
    forall (ct1 ct2 : VM.t (VM.t (ftype * fcomponent))),
        circuit_tmap_is_more_concrete ct1 ct2 ->
        circuit_tmap_is_more_concrete ct2 ct1 ->
        VM.equal (VM.equal pair_eq) ct1 ct2.
Proof.
intros.
apply VM.equal_1.
unfold VM.Equivb, VM.Equiv.
split ; intros.
* specialize (H k) ; specialize (H0 k).
  unfold VM.In.
  split ; intro.
  1,2: destruct H1 as [ktmap H1].
  1,2: apply VM.find_1 in H1.
  1: rewrite H1 in H ; destruct (VM.find k ct2) as [etmap|] eqn: H2 ; last done.
  2: rewrite H1 in H0 ; destruct (VM.find k ct1) as [etmap|] eqn: H2 ; last done.
  1,2: exists etmap.
  1,2: apply VM.find_2, H2.
* apply VM.find_1 in H1, H2.
  specialize (H k) ; specialize (H0 k).
  rewrite H1 H2 in H ; rewrite H2 H1 in H0.
  unfold Cmp ; simpl.
  apply tmap_is_more_concrete_antisymmetric ; by assumption.
Qed.

Lemma circuit_tmap_equal_iff_more_concrete
    (ct1 ct2 : VM.t (VM.t (ftype * fcomponent))) :
    VM.equal (VM.equal pair_eq) ct1 ct2 = true <->
    circuit_tmap_is_more_concrete ct1 ct2 /\
    circuit_tmap_is_more_concrete ct2 ct1.
Proof.
split.
* move /vm_equal_find_iff => Heq.
  split; intro mi; specialize (Heq mi);
    unfold circuit_tmap_is_more_concrete;
    destruct (VM.find mi ct1) as [tm1|] eqn:H1,
             (VM.find mi ct2) as [tm2|] eqn:H2;
    rewrite H1 H2 in Heq; try done.
  + by apply tmap_equal_iff_more_concrete in Heq; destruct Heq.
  + by apply tmap_equal_iff_more_concrete in Heq; destruct Heq.
* intros [H12 H21].
  by apply circuit_tmap_is_more_concrete_antisymmetric.
Qed.

(* unify_width_down is monotonous *)
Lemma unify_width_down_is_monotonous :
    forall (ss ll : VM.t (VM.t (ftype * fcomponent))) (s l : VM.t (ftype * fcomponent)) (ssl : HiF.hfstmt_seq),
        circuit_tmap_is_more_concrete ss ll ->
        tmap_is_more_concrete s l ->
        match unify_width_down ss s ssl, unify_width_down ll l ssl with
        | Some new_s, Some new_l => tmap_is_more_concrete new_s new_l
        | _, _ => True
        end
with unify_width_down_one_is_monotonous :
    forall (ss ll : VM.t (VM.t (ftype * fcomponent))) (s l : VM.t (ftype * fcomponent)) (st : HiF.hfstmt),
        circuit_tmap_is_more_concrete ss ll ->
        tmap_is_more_concrete s l ->
        match unify_width_down ss s (Qcons st (Qnil _)), unify_width_down ll l (Qcons st (Qnil _)) with
        | Some new_s, Some new_l => tmap_is_more_concrete new_s new_l
        | _, _ => True
        end.
Admitted.

(* unify_ports_up is monotonous *)
Lemma unify_ports_up_is_monotonous :
    forall (s l : VM.t (ftype * fcomponent)) (ffs ffl : ffield),
        tmap_is_more_concrete s l ->
        more_concrete_fields ffs ffl ->
        match unify_ports_up s ffs, unify_ports_up l ffl with
        | Some new_s, Some new_l => tmap_is_more_concrete new_s new_l
        | _, None => true
        | _, _ => false
        end.
Admitted.

(* unify_width_up is monotonous *)
Lemma unify_width_up_is_monotonous :
    forall (ss ll : VM.t (VM.t (ftype * fcomponent))) (s l : VM.t (ftype * fcomponent)) (ssl : HiF.hfstmt_seq),
        circuit_tmap_is_more_concrete ss ll ->
        tmap_is_more_concrete s l ->
        match unify_width_up ss s ssl, unify_width_up ll l ssl with
        | Some new_ss, Some new_ll => circuit_tmap_is_more_concrete new_ss new_ll
        | _, _ => True
        end
with unify_width_up_one_is_monotonous :
    forall (ss ll : VM.t (VM.t (ftype * fcomponent))) (s l : VM.t (ftype * fcomponent)) (st : HiF.hfstmt),
        circuit_tmap_is_more_concrete ss ll ->
        tmap_is_more_concrete s l ->
        match unify_width_up ss s (Qcons st (Qnil _)), unify_width_up ll l (Qcons st (Qnil _)) with
        | Some new_ss, Some new_ll => circuit_tmap_is_more_concrete new_ss new_ll
        | _, _ => True
        end.
Admitted.

(* circuit_width_iter, the main iteration operator, is monotonous. *)
Lemma circuit_width_iter_is_monotonous :
    forall (ss ll : VM.t (VM.t (ftype * fcomponent))),
        circuit_tmap_is_more_concrete ss ll ->
        match circuit_width_iter ss, circuit_width_iter ll with
        | Some new_ss, Some new_ll => circuit_tmap_is_more_concrete new_ss new_ll
        | _, _ => True
        end.
Admitted.

(* circuit_tmap_iterator is always smaller than any fixed point,
   or it may be equal to the smallest fixed point. *)
Lemma circuit_tmap_iterator_is_smaller_than_any_fixed_point :
    match circuit_tmap_uninferred with
    | Some ctu => forall (tmap_fix : VM.t (VM.t (ftype * fcomponent))),
                      circuit_tmap_is_more_concrete ctu tmap_fix ->
                      match circuit_width_iter tmap_fix with
                      | Some cwi_tmap_fix => VM.equal (VM.equal pair_eq) cwi_tmap_fix tmap_fix ->
                                             forall n : nat,
                                                 match circuit_tmap_iterator n ctu with
                                                 | Some ctn => circuit_tmap_is_more_concrete ctn tmap_fix
                                                 | None => True
                                                 end
                      | None => True
                      end
    | _ => False
    end.
Admitted.

(* If there exists a fixed point of circuit_width_iter,
   then circuit_tmap_implicits finds the smallest fixed point. *)
Lemma circuit_tmap_is_smaller_than_any_fixed_point :
    match circuit_tmap_uninferred with
    | Some ctu => forall (tmap_fix : VM.t (VM.t (ftype * fcomponent))),
                      circuit_tmap_is_more_concrete ctu tmap_fix ->
                      match circuit_width_iter tmap_fix with
                      | Some cwi_tmap_fix => VM.equal (VM.equal pair_eq) cwi_tmap_fix tmap_fix ->
                                             forall (n : nat),
                                                 match circuit_tmap_implicits n with
                                                 | Some ct => circuit_tmap_is_more_concrete ct tmap_fix
                                                 | None => True
                                                 end
                      | None => True
                      end
    | _ => False
    end.
Admitted.

(* Perhaps also: if circuit_tmap_implicits is not a fixed point,
   then there exists no fixed point (at least none >= circuit_tmap_uninferred). *)

(*
(* make_fype_explicit is idempotent. *)
Lemma make_ftype_explicit_idempotent :
    forall (t : ftype),
        make_ftype_explicit t = make_ftype_explicit (make_ftype_explicit t)
with make_ffield_explicit_idempotent :
    forall (ff : ffield),
        make_ffield_explicit ff = make_ffield_explicit (make_ffield_explicit ff).
Proof.
* clear make_ftype_explicit_idempotent.
  induction t as [[w|w|w|w| | | |]|elt IHelt n|ff] ; simpl ; try done.
  + by rewrite -IHelt.
  + by rewrite -make_ffield_explicit_idempotent.
* clear make_ffield_explicit_idempotent.
  induction ff as [|id fl t ff] ; simpl ; try done.
  by rewrite -make_ftype_explicit_idempotent -IHff.
Qed.
*)

(* If a type is explicit and concrete, then it is concrete. Sounds quite logical, doesn’t it? *)
Lemma ftype_is_explicit_and_concrete_implies_concrete :
    forall (t : ftype),
        ftype_is_explicit_and_concrete t -> ftype_is_concrete t
with ffield_is_explicit_and_concrete_implies_concrete :
    forall (ff : ffield),
        ffield_is_explicit_and_concrete ff -> ffield_is_concrete ff.
Admitted.

(* Making a type explicit-width makes it explicit and concrete. *)
Lemma make_ftype_explicit_is_explicit_and_concrete :
    forall (t : ftype),
        ftype_is_explicit_and_concrete (make_ftype_explicit t)
with make_ffield_explicit_is_explicit_and_concrete :
    forall (ff : ffield),
        ffield_is_explicit_and_concrete (make_ffield_explicit ff).
Admitted.

(* If a type is explicit and concrete, then making it explicit doesn’t change it. *)
Lemma ftype_is_explicit_and_concrete_implies_make_ftype_explicit_id :
    forall (t : ftype),
        ftype_is_explicit_and_concrete t -> t = make_ftype_explicit t
with ffield_is_explicit_and_concrete_implies_make_ffield_explicit_id :
    forall (ff : ffield),
        ffield_is_explicit_and_concrete ff -> ff = make_ffield_explicit ff.
Admitted.

(* ftype_mux preserves whether types are concrete.
   In fact, it suffices that one type is concrete
   (if you know only that the other type is concrete, use ftype_mux_commutative). *)
Lemma ftype_mux_preserves_concrete :
    forall (passive : bool) (t1 t2 : ftype),
        ftype_is_concrete t1 ->
        match ftype_mux passive t1 t2 with
        | Some t12 => ftype_is_concrete t12
        | None => true
        end
with ffield_mux_preserves_concrete :
    forall (passive : bool) (ff1 ff2 : ffield),
        ffield_is_concrete ff1 ->
        match ffield_mux passive ff1 ff2 with
        | Some ff12 => ffield_is_concrete ff12
        | None => true
        end.
Admitted.

(* ftype_mux preserves whether types are explicit and concrete. *)
Lemma ftype_mux_preserves_explicit_and_concrete :
    forall (passive : bool) (t1 t2 : ftype),
        ftype_is_explicit_and_concrete t1 ->
        ftype_is_explicit_and_concrete t2 ->
        match ftype_mux passive t1 t2 with
        | Some t12 => ftype_is_explicit_and_concrete t12
        | None => true
        end
with ffield_mux_preserves_explicit_and_concrete :
    forall (passive : bool) (ff1 ff2 : ffield),
        ffield_is_explicit_and_concrete ff1 ->
        ffield_is_explicit_and_concrete ff2 ->
        match ffield_mux passive ff1 ff2 with
        | Some ff12 => ffield_is_explicit_and_concrete ff12
        | None => true
        end.
Admitted.

(* If types are concrete, then ftype_mux and make_ftype_explicit can be interchanged.
   (Problematic is that ftype_mux _ (Gtyp Freset) (Gtyp Fasyncreset) = Gtyp Fasyncreset,
   but (make_ftype_explicit (Gtyp Freset)) = Gtyp (Fuint 1).  Therefore
   we have to require that both t1 and t2 are concrete.) *)
Lemma ftype_mux_and_make_ftype_explicit:
    forall (passive : bool) (t1 t2 : ftype),
        ftype_is_concrete t1 ->
        ftype_is_concrete t2 ->
        ftype_mux passive (make_ftype_explicit t1) (make_ftype_explicit t2) = option_map make_ftype_explicit (ftype_mux passive t1 t2)
with ffield_mux_and_make_ffield_explicit :
    forall (passive : bool) (ff1 ff2 : ffield),
        ffield_is_concrete ff1 ->
        ffield_is_concrete ff2 ->
        ffield_mux passive (make_ffield_explicit ff1) (make_ffield_explicit ff2) = option_map make_ffield_explicit (ffield_mux passive ff1 ff2).
Admitted.

(* circuit_tmap contains only explicit types *)
Lemma circuit_tmap_is_explicit_and_concrete :
    forall n : nat,
        match circuit_tmap n with
        | Some ct => forall (mi : VarOrder.T),
                         match VM.find mi ct with
                         | Some t => forall (id : VarOrder.T),
                                         match VM.find id t with
                                         | Some (ty, _) => ftype_is_explicit_and_concrete ty
                                         | None => true
                                         end
                         | None => True
                         end
        | None => True
        end.
Admitted.

End InferWidths_and_InferResets.

(*************************************************************************)
(*************************************************************************)
(***                                                                   ***)
(***                                                                   ***)
(***                   Third main section: Instances                   ***)
(***                                                                   ***)
(***                   Find all instances                              ***)
(***                                                                   ***)
(***                                                                   ***)
(*************************************************************************)
(*************************************************************************)

Variable mi_top : VarOrder.T.

Hypothesis top_module_present : find_module mi_top <> None.

(* Because it is difficult to calculate the number of iterations needed
   to find the fixed point resulting from InferWidths and InferResets,
   we just assume that there exists a number: *)

Hypothesis circuit_tmap_correct : exists iter_number : nat, circuit_tmap iter_number <> None.

Section Instances.

(* identifiers for instances *)
(* To identify an instance, we use a sequence of identifiers.
   The empty sequence identifies the top instance,
   and if the instance identified with ``iil'' contains a statement ``inst i of m'',
   then the instance created by such statement is identified by ``i :: iil''.
   (Note that we place the innermost level at the beginning to simplify handling,
   because sequences are constructed this way.) *)

(* practical calculation of inst as a SVM.t,
   and showing that inst normally would be finite
   (as there cannot be cycles in instantiations) *)

(* Add instance information for instance inst and its sub-instances to the instance map.

   n = maximum number of instance levels to descend into
   inst = current instance
   mi = (module identifier) type of the current instance
   inst_map = maps instance identifiers to their types; this map is extended

   Result: inst_map is extended with the information that instance inst has module type mi,
   and its sub-instances are also added up to n levels deep. *)
Fixpoint find_module_instances (n : nat) (inst : SVM.key) (mi : VarOrder.T) (inst_map : SVM.t VarOrder.T) : option (SVM.t VarOrder.T) :=
    let inst_map' := SVM.add inst mi inst_map
    in match find_module mi with
       | Some (FInmod _ _ ssl) => match n with
                                  | 0 => Some inst_map'
                                  | n'.+1 => (fix find_stmts_instances (ssl : HiF.hfstmt_seq) (in_ma : SVM.t VarOrder.T) : option (SVM.t VarOrder.T) :=
                                                   match ssl with
                                                   | Qnil => Some in_ma
                                                   | Qcons s ssl' => match find_stmt_instances s in_ma with
                                                                     | Some in_ma' => find_stmts_instances ssl' in_ma'
                                                                     | None => None
                                                                     end
                                                   end
                                              with find_stmt_instances (s : HiF.hfstmt) (in_ma : SVM.t VarOrder.T) : option (SVM.t VarOrder.T) :=
                                                   match s with
                                                   | Sinst i m' => find_module_instances n' (i :: inst) m' in_ma
                                                   | Swhen _ ssl_true ssl_false => match find_stmts_instances ssl_true in_ma with
                                                                                   | Some in_ma_true => find_stmts_instances ssl_false in_ma_true
                                                                                   | None => None
                                                                                   end
                                                   | _ => Some in_ma
                                                   end
                                              for find_stmts_instances) ssl inst_map'
                                 end
       | _ => None
       end.

(* Find all instances of the circuit.
   The result is a map with domain all instances, and for every instance its module is indicated. *)
Definition find_circuit_instances : option (SVM.t VarOrder.T) :=
    find_module_instances (size mml) [::] mi_top (SVM.empty VarOrder.T).

(* Properties of find_circuit_instances *)

Lemma find_module_instances_not_none :
    forall (n : nat) (inst : SVM.key) (mi : VarOrder.T) (inst_map : SVM.t VarOrder.T),
        find_module mi <> None ->
        find_module_instances n inst mi inst_map <> None.
Admitted.

Lemma find_circuit_instances_not_none :
    find_circuit_instances <> None.
Admitted.

(* Auxiliary definition: the instance map maps elements to proper module types

   inst_map = instance map whose elements are being checked

   Result: True iff inst_map maps elements to modules that are in mml *)
Definition inst_map_has_module_types (inst_map : SVM.t VarOrder.T) : Prop :=
    forall (iil : SVM.key),
        match SVM.find iil inst_map with
        | Some mi => find_module mi <> None
        | None => True
        end.

(* find_module_instances creates a legal instance map *)
Lemma find_module_instances_finds_modules :
    forall (n : nat) (inst : SVM.key) (mi : VarOrder.T) (inst_map : SVM.t VarOrder.T),
        inst_map_has_module_types inst_map ->
        match find_module_instances n inst mi inst_map with
        | Some new_inst_map => inst_map_has_module_types new_inst_map
        | None => True
        end.
Admitted.

(* find_circuit_instances creates a legal instance map *)
Lemma find_circuit_instances_finds_modules :
    match find_circuit_instances with
    | Some fci => inst_map_has_module_types fci
    | None => True
    end.
Admitted.

(* inst does not allow cycles *)
(* This should probably be defined as:
   in the domain of find_circuit_instances, there is no sequence
   that models onto a repeated module. *)

Fixpoint module_path (fci : SVM.t VarOrder.T) (iil : seq VarOrder.T) : option (seq VarOrder.T) :=
    match SVM.find iil fci with
    | Some mi => option_map (cons mi) (match iil with
                                       | [::] => Some [::]
                                       | ii :: iil' => module_path fci iil'
                                       end)
    | None => None
    end.

Hypothesis inst_modules_acyclic :
    match find_circuit_instances with
    | Some fci => forall iil : seq VarOrder.T,
                      match module_path fci iil with
                      | Some mil => uniq mil
                      | None => true
                      end
    | None => True
    end.

Lemma find_circuit_instances_is_fixed_point :
    match find_circuit_instances with
    | Some fci => match find_module_instances (size mml).+1 [::] mi_top (SVM.empty VarOrder.T) with
                  | Some fci' => SVM.equal N.eqb fci fci'
                  | None => false
                  end
    | None => true
    end.
Admitted.

(*
Fixpoint module_identifiers' (mml' : seq HiF.hfmodule) : seq VarOrder.T :=
    match mml' with
    | [::] => [::]
    | FInmod mi _ _ :: mml''
    | FExmod mi _ _ :: mml'' => mi :: module_identifiers' mml''
    end.

Definition module_identifiers : seq VarOrder.T := module_identifiers' mml.

Lemma inst_bounded :
    forall (ii : seq VarOrder.T) (mi : VarOrder.T) (im : inst ii mi),
        size ii < size mml.
Proof.
intros.
assert (size (module_path im) == size ii + 1).
      induction im ; simpl.
      * by rewrite add0n.
      * by rewrite addn1 eqSS -addn1 IHim.
assert ({subset module_path im <= module_identifiers}).
      clear H.
      unfold sub_mem.
      induction im ; simpl.
      * generalize (Top_module_present) ; unfold find_module ; simpl ; intro.
        intros.
        rewrite mem_seq1 in H0 ; move /eqP : H0 => Ho ; subst x.
        unfold module_identifiers.
        induction mml ; simpl ; simpl in H.
        + by contradict H.
        + destruct a as [mi ppl ssl|mi ppl ssl].
          1,2: rewrite (in_cons (T := VarOrder.T)).
          1,2: destruct (mi_top == mi) eqn: Hmitop ; first by rewrite orTb.
          1,2: rewrite orFb.
          1,2: by apply IHl, H.
      * intros.
        rewrite in_cons in H.
        destruct (x == mi_inner) eqn: Hxmii ; last by rewrite orFb in H ; apply IHim, H.
        move /eqP : Hxmii => Hxmii ; subst x.
        unfold contains_instance in i.
        destruct (find_module mi_outer) as [[_ _ ssl|]|] ; try done.
Check (in_cons (T := VarOrder.T)).

; first by rewrite orTb.

generalize (inst_modules_acyclic im) ; intro.
(* Every suffix of ii corresponds to a module, different suffixes must correspond to different modules. *)

*)

End Instances.

(*************************************************************************)
(*************************************************************************)
(***                                                                   ***)
(***                                                                   ***)
(***              Fourth main section: Values                          ***)
(***                                                                   ***)
(***              Calculate the value of every expression              ***)
(***                                                                   ***)
(***                                                                   ***)
(*************************************************************************)
(*************************************************************************)

Section Values.

Inductive hvalue : Type :=
  | Gval : fgtyp -> bitseq -> hvalue
  | Aval : ftype (* element type *) -> array_value -> hvalue
  | Bval : bundle_value -> hvalue
  | Undefinedonpurpose : ftype -> hvalue (* the value has been declared undefined by an "is invalid" statement. *)
  | Needtobedefined : ftype -> hvalue (* the value needs to be defined. If this remains at the end of the iteration, the programmer forgot a connect or invalidate statement *)
  | Uninitialized : ftype -> hvalue (* the register has not yet been initialized. If it is read, it reads the same as "Needtobedefined". *)
with array_value : Type :=
  | Anil : array_value
  | Acons : hvalue -> array_value -> array_value
with bundle_value : Type :=
  | Bnil : bundle_value
  | Bflips : var -> fflip -> hvalue -> bundle_value -> bundle_value.

(* general data value equality is decidable *)
Lemma hvalue_eq_dec (x y : hvalue) : {x = y} + {x <> y}
with array_value_eq_dec (x y : array_value) : {x = y} + {x <> y}
with bundle_value_eq_dec (x y : bundle_value) : {x = y} + {x <> y}.
Admitted.

(* Boolean equality for general data values *)
Fixpoint hvalue_eqn (x y : hvalue) : bool :=
  match x, y with
  | Gval ft1 val1, Gval ft2 val2 => (ft1 == ft2) && (val1 == val2)
  | Aval elt1 val1, Aval elt2 val2 => (elt1==elt2) && array_value_eqn val1 val2
  | Bval val1, Bval val2 => bundle_value_eqn val1 val2
  | Needtobedefined t1, Needtobedefined t2
  | Undefinedonpurpose t1, Undefinedonpurpose t2
  | Uninitialized t1, Uninitialized t2 => t1 == t2
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

(*
Lemma bits_eqP : forall (x y : bits), reflect (x = y) (x == y).
Proof. intros. exact: eqP. Qed.

Lemma N_eqP : forall (x y : N), reflect (x = y) (x == y).
Proof. intros. exact: eqP. Qed.
*)

(* reflection predicate for general data values *)
Lemma hvalue_eqP : forall (x y : hvalue), reflect (x = y) (hvalue_eqn x y)
with array_value_eqP : forall (x y : array_value), reflect (x = y) (array_value_eqn x y)
with bundle_value_eqP : forall (x y : bundle_value), reflect (x = y) (bundle_value_eqn x y).
Admitted.

(* eqType for hvalue *)
Definition hvalue_eqMixin := Equality.Mixin hvalue_eqP.
Canonical hvalue_eqType := Equality.Pack (Equality.Class hvalue_eqMixin).
Definition array_value_eqMixin := Equality.Mixin array_value_eqP.
Canonical array_value_eqType := Equality.Pack (Equality.Class array_value_eqMixin).
Definition bundle_value_eqMixin := Equality.Mixin bundle_value_eqP.
Canonical bundle_value_eqType := Equality.Pack (Equality.Class bundle_value_eqMixin).

Fixpoint array_value_size (av : array_value) : nat :=
    match av with
    | Anil => 0
    | Acons _ av' => (array_value_size av').+1
    end.

Fixpoint type_of_val (v : hvalue) : ftype :=
    match v with
    | Gval ft _ => Gtyp ft
    | Aval elt av => Atyp elt (array_value_size av)
    | Bval bv => Btyp (type_of_bundle_val bv)
    | Undefinedonpurpose t
    | Needtobedefined    t
    | Uninitialized      t => t
    end
with type_of_bundle_val (bv : bundle_value) : ffield :=
    match bv with
    | Bnil => Fnil
    | Bflips id fl v bv' => Fflips id fl (type_of_val v) (type_of_bundle_val bv')
    end.

(* Find the type of a reference, based on the values stored in sem_old.
   The logic is exactly the same as in type_of_ref. *)
Fixpoint eval_type_of_ref (r : HiF.href) (sem_old : VM.t hvalue) : option ftype :=
    match r with
    | Eid v => option_map type_of_val (VM.find v sem_old)
    | Esubfield r' v => match eval_type_of_ref r' sem_old with
                        | Some (Btyp fs) => let fix aux fx := (match fx with
                                                               | Fflips v' f t fxs => if (v == v') then Some t
                                                                                                   else aux fxs
                                                               | Fnil => None
                                                               end)
                                            in aux fs
                        | _ => None
                        end
    | Esubaccess r' _
    | Esubindex r' _ => match eval_type_of_ref r' sem_old with
                        | Some (Atyp ty _) => Some ty
                        | _ => None
                        end
    end.

(* Find the type of expression exp, where reference types are found based on the values in sem_old.
   The logic is exactly the same as in type_of_expr.
   However, we have to apply make_ftype_explicit because Ecast AsUInt casts Fasyncreset values
   to type Fuint_implicit 1 (which is required to make the width-and-reset inference work nicely). *)
Definition eval_type_of_expr (exp : HiF.hfexpr) (sem_old : VM.t hvalue) : option ftype :=
    option_map make_ftype_explicit (type_of_expr' (fun (r : HiF.href) => eval_type_of_ref r sem_old) exp).

(* The function converts values that are not bundle values but have a bundle type to ``Bval ...'' values. *)

Fixpoint create_undef_bundle_value (undef : ftype -> hvalue) (ff : ffield) : bundle_value :=
    match ff with
    | Fnil => Bnil
    | Fflips v fl t ff' => Bflips v fl (undef t) (create_undef_bundle_value undef ff')
    end.

Fixpoint create_undef_array_value (undef : ftype -> hvalue) (elt : ftype) (n : nat) : array_value :=
    match n with
    | 0 => Anil
    | n'.+1 => Acons (undef elt) (create_undef_array_value undef elt n')
    end.

Definition convert_to_bundle_value (hv : hvalue) : option bundle_value :=
    match hv with
    | Bval bv => Some bv
    | Undefinedonpurpose (Btyp ff) => Some (create_undef_bundle_value Undefinedonpurpose ff)
    | Needtobedefined    (Btyp ff) => Some (create_undef_bundle_value Needtobedefined    ff)
    | Uninitialized      (Btyp ff) => Some (create_undef_bundle_value Uninitialized      ff)
    | _ => None
    end.

(* The function returns a pair consisting of the element type and an array value *)
Definition convert_to_array_value (hv : hvalue) : option (ftype * array_value) :=
    match hv with
    | Aval elt av => Some (elt, av)
    | Undefinedonpurpose (Atyp elt n) => Some (elt, create_undef_array_value Undefinedonpurpose elt n)
    | Needtobedefined    (Atyp elt n) => Some (elt, create_undef_array_value Needtobedefined    elt n)
    | Uninitialized      (Atyp elt n) => Some (elt, create_undef_array_value Uninitialized      elt n)
    | _ => None
    end.

Definition zext_to (n : nat) (bs : bitseq) : bitseq :=
    zext (n - size bs) bs.

Definition sext_to (n : nat) (bs : bitseq) : bitseq :=
    sext (n - size bs) bs.

Definition to_N (bs : bitseq) : N :=
    foldr (fun b res => N.add (N.of_nat (if b then 1 else 0)) (N.mul res (N.of_nat 2))) N0 bs.

Fixpoint from_N (n : nat) (x : N) : bitseq :=
    match n with
    | 0 => [::]
    | n'.+1 => N.odd x :: from_N n' (N.div x 2)
    end.

Definition to_Zpos (bs : bitseq) : Z :=
    foldr (fun b res => Z.add (Z.of_nat (if b then 1 else 0)) (Z.mul res (Z.of_nat 2))) Z0 bs.

Definition to_Zneg (bs : bitseq) : Z :=
    foldr (fun b res => Z.add (Z.of_nat (if b then 0 else 1)) (Z.mul res (Z.of_nat 2))) Z0 bs.

Definition to_Z (bs : bitseq) : Z :=
    match splitmsb bs with
    | (low, false) => to_Zpos low
    | (low, true) => Z.opp (Z.succ (to_Zneg low))
    end.

Fixpoint from_Zpos (n : nat) (x : Z) : bitseq :=
    match n with
    | 0 => [::]
    | n'.+1 => Z.odd x :: from_Zpos n' (Z.div2 x)
    end.

Fixpoint from_Zneg (n : nat) (x : Z) : bitseq :=
    match n with
    | 0 => [::]
    | n'.+1 => Z.even x :: from_Zneg n' (Z.div2 x)
    end.

Definition from_Z (n : nat) (x : Z) : bitseq :=
    match x with
    | Zpos _ => from_Zpos n x
    | Zneg _ => from_Zneg n (Z.pred (Z.opp x))
    | Z0 => zeros n
    end.

Definition andB (bs1 bs2 : bitseq) : bitseq :=
    map (fun p => p.1 && p.2) (extzip0 bs1 bs2).

Definition orB (bs1 bs2 : bitseq) : bitseq :=
    map (fun p => p.1 || p.2) (extzip0 bs1 bs2).

Definition xorB (bs1 bs2 : bitseq) : bitseq :=
    map (fun p => xorb p.1 p.2) (extzip0 bs1 bs2).

Fixpoint succB (bs : bitseq) : bitseq :=
    match bs with
    | [::] => [::]
    | b :: tl => if b then false :: succB tl else true :: tl
    end.

Definition negB (bs : bitseq) : bitseq := succB (invB bs).

(* evaluate binary operators *)
Definition eval_binop (op : ebinop) (val1 val2 : hvalue) : option hvalue :=
    match val1 with
    | Gval (Fuint          w1) val1 => match val2 with
                                       | Gval                     (Fuint          w2) val2 => match op with
                                                                                              | Badd  => Some (Gval (Fuint          (maxn w1 w2).+1) (from_N (maxn w1 w2).+1 (to_N val1  +  to_N val2)))
                                                                                              | Bsub  => Some (Gval (Fuint          (maxn w1 w2).+1) (from_Z (maxn w1 w2).+1 (to_Z val1  -  to_Z val2)))
                                                                                              | Bmul  => Some (Gval (Fuint          (w1 + w2)      ) (from_N (w1 + w2)       (to_N val1  *  to_N val2)))
                                                                                              | Bdiv  => Some (Gval (Fuint          w1             ) (from_N w1              (to_N val1  /  to_N val2)))
                                                                                              | Brem  => Some (Gval (Fuint          (minn w1 w2)   ) (from_N (minn w1 w2)    (to_N val1 mod to_N val2)))
                                                                                              | Bdshl => Some (Gval (Fuint          (w1 + 2^w2).-1 ) (zext_to (w1+2^w2).-1 ((zeros (to_nat val2)) ++ val1)))
                                                                                              | Bdshr => Some (Gval (Fuint          w1             ) (zext_to w1 (drop (to_nat val2) val1)))
                                                                                              | Band  => Some (Gval (Fuint          (maxn w1 w2)   ) (andB val1 val2))
                                                                                              | Bor   => Some (Gval (Fuint          (maxn w1 w2)   ) (orB  val1 val2))
                                                                                              | Bxor  => Some (Gval (Fuint          (maxn w1 w2)   ) (xorB val1 val2))
                                                                                              | Bcat  => Some (Gval (Fuint          (w1 + w2)      ) (val2 ++ val1))
                                                                                              | Bcomp Blt  => Some (Gval (Fuint 1) [:: to_N val1 <  to_N val2])
                                                                                              | Bcomp Bleq => Some (Gval (Fuint 1) [:: to_N val1 <= to_N val2])
                                                                                              | Bcomp Bgt  => Some (Gval (Fuint 1) [:: to_N val1 >  to_N val2])
                                                                                              | Bcomp Bgeq => Some (Gval (Fuint 1) [:: to_N val1 >= to_N val2])
                                                                                              | Bcomp Beq  => Some (Gval (Fuint 1) [:: to_N val1 == to_N val2])
                                                                                              | Bcomp Bneq => Some (Gval (Fuint 1) [:: to_N val1 != to_N val2])
                                                                                              end
                                       | Undefinedonpurpose (Gtyp (Fuint          w2)) => match op with
                                                                                          | Badd
                                                                                          | Bsub  => Some (Undefinedonpurpose (Gtyp (Fuint          (maxn w1 w2).+1)))
                                                                                          | Bmul
                                                                                          | Bcat  => Some (Undefinedonpurpose (Gtyp (Fuint          (w1 + w2)      )))
                                                                                          | Bdiv
                                                                                          | Bdshr => Some (Undefinedonpurpose (Gtyp (Fuint           w1            )))
                                                                                          | Brem  => Some (Undefinedonpurpose (Gtyp (Fuint          (minn w1 w2)   )))
                                                                                          | Bdshl => Some (Undefinedonpurpose (Gtyp (Fuint          (w1 + 2^w2).-1 )))
                                                                                          | Band
                                                                                          | Bor
                                                                                          | Bxor  => Some (Undefinedonpurpose (Gtyp (Fuint          (maxn w1 w2)   )))
                                                                                          | Bcomp _ => Some (Undefinedonpurpose (Gtyp (Fuint 1)))
                                                                                          end
                                       | Needtobedefined    (Gtyp (Fuint          w2))
                                       | Uninitialized      (Gtyp (Fuint          w2)) => match op with
                                                                                          | Badd
                                                                                          | Bsub  => Some (Needtobedefined    (Gtyp (Fuint          (maxn w1 w2).+1)))
                                                                                          | Bmul
                                                                                          | Bcat  => Some (Needtobedefined    (Gtyp (Fuint          (w1 + w2)      )))
                                                                                          | Bdiv
                                                                                          | Bdshr => Some (Needtobedefined    (Gtyp (Fuint           w1            )))
                                                                                          | Brem  => Some (Needtobedefined    (Gtyp (Fuint          (minn w1 w2)   )))
                                                                                          | Bdshl => Some (Needtobedefined    (Gtyp (Fuint          (w1 + 2^w2).-1 )))
                                                                                          | Band
                                                                                          | Bor
                                                                                          | Bxor  => Some (Needtobedefined    (Gtyp (Fuint          (maxn w1 w2)   )))
                                                                                          | Bcomp _ => Some (Needtobedefined    (Gtyp (Fuint 1)))
                                                                                          end
                                       | _ => None
                                       end
    | Gval (Fsint          w1) val1 => match val2 with
                                       | Gval                     (Fuint          w2) val2 => match op with
                                                                                              | Bdshl => Some (Gval (Fsint          (w1 + 2^w2).-1 ) (sext_to (w1+2^w2).-1 ((zeros (to_nat val2)) ++ val1)))
                                                                                              | Bdshr => Some (Gval (Fsint          w1             ) (sext_to w1 (drop (minn (to_nat val2) (w1-1)) val1)))
                                                                                              | _ => None
                                                                                              end
                                       | Gval                     (Fsint          w2) val2 => match op with
                                                                                              | Badd  => Some (Gval (Fsint          (maxn w1 w2).+1) (from_Z (maxn w1 w2).+1 (to_Z val1  +  to_Z val2)))
                                                                                              | Bsub  => Some (Gval (Fsint          (maxn w1 w2).+1) (from_Z (maxn w1 w2).+1 (to_Z val1  -  to_Z val2)))
                                                                                              | Bmul  => Some (Gval (Fsint          (w1 + w2)      ) (from_Z (w1 + w2)       (to_Z val1  *  to_Z val2)))
                                                                                              | Bdiv  => Some (Gval (Fsint          w1.+1          ) (from_Z w1.+1           (to_Z val1  /  to_Z val2)))
                                                                                              | Brem  => Some (Gval (Fsint          (minn w1 w2)   ) (from_Z (minn w1 w2)    (to_Z val1 mod to_Z val2)))
                                                                                              | Band  => Some (Gval (Fuint          (maxn w1 w2)   ) (andB val1 val2))
                                                                                              | Bor   => Some (Gval (Fuint          (maxn w1 w2)   ) (orB  val1 val2))
                                                                                              | Bxor  => Some (Gval (Fuint          (maxn w1 w2)   ) (xorB val1 val2))
                                                                                              | Bcat  => Some (Gval (Fuint          (w1 + w2)      ) (val2 ++ val1))
                                                                                              | Bcomp Blt  => Some (Gval (Fuint 1) [:: Z.ltb (to_Z val1) (to_Z val2)])
                                                                                              | Bcomp Bleq => Some (Gval (Fuint 1) [:: Z.leb (to_Z val1) (to_Z val2)])
                                                                                              | Bcomp Bgt  => Some (Gval (Fuint 1) [:: Z.gtb (to_Z val1) (to_Z val2)])
                                                                                              | Bcomp Bgeq => Some (Gval (Fuint 1) [:: Z.geb (to_Z val1) (to_Z val2)])
                                                                                              | Bcomp Beq  => Some (Gval (Fuint 1) [:: Z.eqb (to_Z val1) (to_Z val2)])
                                                                                              | Bcomp Bneq => Some (Gval (Fuint 1) [:: ~~ Z.eqb (to_Z val1) (to_Z val2)])
                                                                                              | _ => None
                                                                                              end
                                       | Undefinedonpurpose (Gtyp (Fuint          w2)) => match op with
                                                                                          | Bdshl => Some (Undefinedonpurpose (Gtyp (Fsint          (w1 + 2^w2).-1 )))
                                                                                          | Bdshr => Some (Undefinedonpurpose (Gtyp (Fsint          w1             )))
                                                                                          | _ => None
                                                                                          end
                                       | Undefinedonpurpose (Gtyp (Fsint          w2)) => match op with
                                                                                          | Badd
                                                                                          | Bsub  => Some (Undefinedonpurpose (Gtyp (Fsint          (maxn w1 w2).+1)))
                                                                                          | Bmul  => Some (Undefinedonpurpose (Gtyp (Fsint          (w1 + w2)      )))
                                                                                          | Bdiv  => Some (Undefinedonpurpose (Gtyp (Fsint          w1.+1          )))
                                                                                          | Brem  => Some (Undefinedonpurpose (Gtyp (Fsint          (minn w1 w2)   )))
                                                                                          | Band
                                                                                          | Bor
                                                                                          | Bxor  => Some (Undefinedonpurpose (Gtyp (Fuint          (maxn w1 w2)   )))
                                                                                          | Bcat  => Some (Undefinedonpurpose (Gtyp (Fuint          (w1 + w2)      )))
                                                                                          | Bcomp _  => Some (Undefinedonpurpose (Gtyp (Fuint 1)))
                                                                                          | _ => None
                                                                                          end
                                       | Needtobedefined    (Gtyp (Fuint          w2))
                                       | Uninitialized      (Gtyp (Fuint          w2)) => match op with
                                                                                          | Bdshl => Some (Needtobedefined    (Gtyp (Fsint          (w1 + 2^w2).-1 )))
                                                                                          | Bdshr => Some (Needtobedefined    (Gtyp (Fsint          w1             )))
                                                                                          | _ => None
                                                                                          end
                                       | Needtobedefined    (Gtyp (Fsint          w2))
                                       | Uninitialized      (Gtyp (Fsint          w2)) => match op with
                                                                                          | Badd
                                                                                          | Bsub  => Some (Needtobedefined    (Gtyp (Fsint          (maxn w1 w2).+1)))
                                                                                          | Bmul  => Some (Needtobedefined    (Gtyp (Fsint          (w1 + w2)      )))
                                                                                          | Bdiv  => Some (Needtobedefined    (Gtyp (Fsint          w1.+1          )))
                                                                                          | Brem  => Some (Needtobedefined    (Gtyp (Fsint          (minn w1 w2)   )))
                                                                                          | Band
                                                                                          | Bor
                                                                                          | Bxor  => Some (Needtobedefined    (Gtyp (Fuint          (maxn w1 w2)   )))
                                                                                          | Bcat  => Some (Needtobedefined    (Gtyp (Fuint          (w1 + w2)      )))
                                                                                          | Bcomp _  => Some (Needtobedefined    (Gtyp (Fuint 1)))
                                                                                          | _ => None
                                                                                          end
                                       | _ => None
                                       end
    | Undefinedonpurpose (Gtyp (Fuint          w1)) => match val2 with
                                                       | Gval                     (Fuint          w2) _
                                                       | Undefinedonpurpose (Gtyp (Fuint          w2)) => match op with
                                                                                                          | Badd
                                                                                                          | Bsub  => Some (Undefinedonpurpose (Gtyp (Fuint          (maxn w1 w2).+1)))
                                                                                                          | Bmul
                                                                                                          | Bcat  => Some (Undefinedonpurpose (Gtyp (Fuint          (w1 + w2)      )))
                                                                                                          | Bdiv
                                                                                                          | Bdshr => Some (Undefinedonpurpose (Gtyp (Fuint          w1             )))
                                                                                                          | Brem  => Some (Undefinedonpurpose (Gtyp (Fuint          (minn w1 w2)   )))
                                                                                                          | Bdshl => Some (Undefinedonpurpose (Gtyp (Fuint          (w1 + 2^w2).-1 )))
                                                                                                          | Band
                                                                                                          | Bor
                                                                                                          | Bxor  => Some (Undefinedonpurpose (Gtyp (Fuint          (maxn w1 w2)   )))
                                                                                                          | Bcomp _ => Some (Undefinedonpurpose (Gtyp (Fuint 1)))
                                                                                                          end
                                                       | Needtobedefined    (Gtyp (Fuint          w2))
                                                       | Uninitialized      (Gtyp (Fuint          w2)) => match op with
                                                                                                          | Badd
                                                                                                          | Bsub  => Some (Needtobedefined    (Gtyp (Fuint          (maxn w1 w2).+1)))
                                                                                                          | Bmul
                                                                                                          | Bcat  => Some (Needtobedefined    (Gtyp (Fuint          (w1 + w2)      )))
                                                                                                          | Bdiv
                                                                                                          | Bdshr => Some (Needtobedefined    (Gtyp (Fuint          w1             )))
                                                                                                          | Brem  => Some (Needtobedefined    (Gtyp (Fuint          (minn w1 w2)   )))
                                                                                                          | Bdshl => Some (Needtobedefined    (Gtyp (Fuint          (w1 + 2^w2).-1 )))
                                                                                                          | Band
                                                                                                          | Bor
                                                                                                          | Bxor  => Some (Needtobedefined    (Gtyp (Fuint          (maxn w1 w2)   )))
                                                                                                          | Bcomp _ => Some (Needtobedefined    (Gtyp (Fuint 1)))
                                                                                                          end
                                                       | _ => None
                                                       end
    | Undefinedonpurpose (Gtyp (Fsint          w1)) => match val2 with
                                                       | Gval                     (Fuint          w2) _
                                                       | Undefinedonpurpose (Gtyp (Fuint          w2)) => match op with
                                                                                                          | Bdshl => Some (Undefinedonpurpose (Gtyp (Fsint          (w1 + 2^w2).-1 )))
                                                                                                          | Bdshr => Some (Undefinedonpurpose (Gtyp (Fsint          w1             )))
                                                                                                          | _ => None
                                                                                                          end
                                                       | Gval                     (Fsint          w2) _
                                                       | Undefinedonpurpose (Gtyp (Fsint          w2)) => match op with
                                                                                                          | Badd
                                                                                                          | Bsub  => Some (Undefinedonpurpose (Gtyp (Fsint          (maxn w1 w2).+1)))
                                                                                                          | Bmul  => Some (Undefinedonpurpose (Gtyp (Fsint          (w1 + w2)      )))
                                                                                                          | Bdiv  => Some (Undefinedonpurpose (Gtyp (Fsint          w1.+1          )))
                                                                                                          | Brem  => Some (Undefinedonpurpose (Gtyp (Fsint          (minn w1 w2)   )))
                                                                                                          | Band
                                                                                                          | Bor
                                                                                                          | Bxor  => Some (Undefinedonpurpose (Gtyp (Fuint          (maxn w1 w2)   )))
                                                                                                          | Bcat  => Some (Undefinedonpurpose (Gtyp (Fuint          (w1 + w2)      )))
                                                                                                          | Bcomp _ => Some (Undefinedonpurpose (Gtyp (Fuint 1)))
                                                                                                          | _ => None
                                                                                                          end
                                                       | Needtobedefined    (Gtyp (Fuint          w2))
                                                       | Uninitialized      (Gtyp (Fuint          w2)) => match op with
                                                                                                          | Bdshl => Some (Needtobedefined    (Gtyp (Fsint          (w1 + 2^w2).-1 )))
                                                                                                          | Bdshr => Some (Needtobedefined    (Gtyp (Fsint          w1             )))
                                                                                                          | _ => None
                                                                                                          end
                                                       | Needtobedefined    (Gtyp (Fsint          w2))
                                                       | Uninitialized      (Gtyp (Fsint          w2)) => match op with
                                                                                                          | Badd
                                                                                                          | Bsub  => Some (Needtobedefined    (Gtyp (Fsint          (maxn w1 w2).+1)))
                                                                                                          | Bmul  => Some (Needtobedefined    (Gtyp (Fsint          (w1 + w2)      )))
                                                                                                          | Bdiv  => Some (Needtobedefined    (Gtyp (Fsint          w1.+1          )))
                                                                                                          | Brem  => Some (Needtobedefined    (Gtyp (Fsint          (minn w1 w2)   )))
                                                                                                          | Band
                                                                                                          | Bor
                                                                                                          | Bxor  => Some (Needtobedefined    (Gtyp (Fuint          (maxn w1 w2)   )))
                                                                                                          | Bcat  => Some (Needtobedefined    (Gtyp (Fuint          (w1 + w2)      )))
                                                                                                          | Bcomp _  => Some (Needtobedefined    (Gtyp (Fuint 1)))
                                                                                                          | _ => None
                                                                                                          end
                                                       | _ => None
                                                       end
    | Needtobedefined (Gtyp (Fuint          w1))
    | Uninitialized   (Gtyp (Fuint          w1)) => match val2 with
                                                       | Gval                     (Fuint          w2) _
                                                       | Undefinedonpurpose (Gtyp (Fuint          w2))
                                                       | Needtobedefined    (Gtyp (Fuint          w2))
                                                       | Uninitialized      (Gtyp (Fuint          w2)) => match op with
                                                                                                          | Badd
                                                                                                          | Bsub  => Some (Needtobedefined    (Gtyp (Fuint          (maxn w1 w2).+1)))
                                                                                                          | Bmul
                                                                                                          | Bcat  => Some (Needtobedefined    (Gtyp (Fuint          (w1 + w2)      )))
                                                                                                          | Bdiv
                                                                                                          | Bdshr => Some (Needtobedefined    (Gtyp (Fuint          w1             )))
                                                                                                          | Brem  => Some (Needtobedefined    (Gtyp (Fuint          (minn w1 w2)   )))
                                                                                                          | Bdshl => Some (Needtobedefined    (Gtyp (Fuint          (w1 + 2^w2).-1 )))
                                                                                                          | Band
                                                                                                          | Bor
                                                                                                          | Bxor  => Some (Needtobedefined    (Gtyp (Fuint          (maxn w1 w2)   )))
                                                                                                          | Bcomp _ => Some (Needtobedefined    (Gtyp (Fuint 1)))
                                                                                                          end
                                                       | _ => None
                                                       end
    | Needtobedefined (Gtyp (Fsint          w1))
    | Uninitialized   (Gtyp (Fsint          w1)) => match val2 with
                                                       | Gval                     (Fuint          w2) _
                                                       | Undefinedonpurpose (Gtyp (Fuint          w2))
                                                       | Needtobedefined    (Gtyp (Fuint          w2))
                                                       | Uninitialized      (Gtyp (Fuint          w2)) => match op with
                                                                                                          | Bdshl => Some (Needtobedefined    (Gtyp (Fsint          (w1 + 2^w2).-1 )))
                                                                                                          | Bdshr => Some (Needtobedefined    (Gtyp (Fsint          w1             )))
                                                                                                          | _ => None
                                                                                                          end
                                                       | Gval                     (Fsint          w2) _
                                                       | Undefinedonpurpose (Gtyp (Fsint          w2))
                                                       | Needtobedefined    (Gtyp (Fsint          w2))
                                                       | Uninitialized      (Gtyp (Fsint          w2)) => match op with
                                                                                                          | Badd
                                                                                                          | Bsub  => Some (Needtobedefined    (Gtyp (Fsint          (maxn w1 w2).+1)))
                                                                                                          | Bmul  => Some (Needtobedefined    (Gtyp (Fsint          (w1 + w2)      )))
                                                                                                          | Bdiv  => Some (Needtobedefined    (Gtyp (Fsint          w1.+1          )))
                                                                                                          | Brem  => Some (Needtobedefined    (Gtyp (Fsint          (minn w1 w2)   )))
                                                                                                          | Band
                                                                                                          | Bor
                                                                                                          | Bxor  => Some (Needtobedefined    (Gtyp (Fuint          (maxn w1 w2)   )))
                                                                                                          | Bcat  => Some (Needtobedefined    (Gtyp (Fuint          (w1 + w2)      )))
                                                                                                          | Bcomp _  => Some (Needtobedefined    (Gtyp (Fuint 1)))
                                                                                                          | _ => None
                                                                                                          end
                                                       | _ => None
                                                       end
    | _ => None
    end.

Definition eval_unop (op : eunop) (e1 : hvalue) : option hvalue :=
    match op, e1 with
    | Upad n, Gval (Fuint          w) val1 => Some (Gval (Fuint          (maxn w n)) (zext_to n val1))
    | Upad n, Gval (Fsint          w) val1 => Some (Gval (Fsint          (maxn w n)) (sext_to n val1))
    | Upad n, Undefinedonpurpose (Gtyp (Fuint          w)) => Some (Undefinedonpurpose (Gtyp (Fuint          (maxn w n))))
    | Upad n, Undefinedonpurpose (Gtyp (Fsint          w)) => Some (Undefinedonpurpose (Gtyp (Fsint          (maxn w n))))
    | Upad n, Needtobedefined    (Gtyp (Fuint          w))
    | Upad n, Uninitialized      (Gtyp (Fuint          w)) => Some (Needtobedefined    (Gtyp (Fuint          (maxn w n))))
    | Upad n, Needtobedefined    (Gtyp (Fsint          w))
    | Upad n, Uninitialized      (Gtyp (Fsint          w)) => Some (Needtobedefined    (Gtyp (Fsint          (maxn w n))))

    | Ushl n, Gval (Fuint          w) val1 => Some (Gval (Fuint          (w+n)) (cat (zeros n) val1))
    | Ushl n, Gval (Fsint          w) val1 => Some (Gval (Fsint          (w+n)) (cat (zeros n) val1))
    | Ushl n, Undefinedonpurpose (Gtyp (Fuint          w)) => Some (Undefinedonpurpose (Gtyp (Fuint          (w+n))))
    | Ushl n, Undefinedonpurpose (Gtyp (Fsint          w)) => Some (Undefinedonpurpose (Gtyp (Fsint          (w+n))))
    | Ushl n, Needtobedefined    (Gtyp (Fuint          w))
    | Ushl n, Uninitialized      (Gtyp (Fuint          w)) => Some (Needtobedefined    (Gtyp (Fuint          (w+n))))
    | Ushl n, Needtobedefined    (Gtyp (Fsint          w))
    | Ushl n, Uninitialized      (Gtyp (Fsint          w)) => Some (Needtobedefined    (Gtyp (Fsint          (w+n))))

    | Ushr n, Gval (Fuint          w) val1 => Some (Gval (Fuint                (w-n)   ) (drop n              val1))
    | Ushr n, Gval (Fsint          0) _    => Some (Gval (Fsint          (maxn (0-n) 1)) [:: b0])
    | Ushr n, Gval (Fsint          w) val1 => Some (Gval (Fsint          (maxn (w-n) 1)) (drop (minn n (w-1)) val1))
    | Ushr n, Undefinedonpurpose (Gtyp (Fuint          w)) => Some (Undefinedonpurpose (Gtyp (Fuint                (w-n)   )))
    | Ushr n, Undefinedonpurpose (Gtyp (Fsint          w)) => Some (Undefinedonpurpose (Gtyp (Fsint          (maxn (w-n) 1))))
    | Ushr n, Needtobedefined    (Gtyp (Fuint          w))
    | Ushr n, Uninitialized      (Gtyp (Fuint          w)) => Some (Needtobedefined (Gtyp (Fuint                (w-n)   )))
    | Ushr n, Needtobedefined    (Gtyp (Fsint          w))
    | Ushr n, Uninitialized      (Gtyp (Fsint          w)) => Some (Needtobedefined (Gtyp (Fsint          (maxn (w-n) 1))))

    | Ucvt, Gval (Fuint          w) val1 => Some (Gval (Fsint          w.+1) (zext 1 val1))
    | Ucvt, Gval (Fsint          w) val1 => Some (Gval (Fsint          w) val1)
    | Ucvt, Undefinedonpurpose (Gtyp (Fuint          w)) => Some (Undefinedonpurpose (Gtyp (Fsint          w.+1)))
    | Ucvt, Undefinedonpurpose (Gtyp (Fsint          w)) => Some (Undefinedonpurpose (Gtyp (Fsint          w)))
    | Ucvt, Needtobedefined    (Gtyp (Fuint          w))
    | Ucvt, Uninitialized      (Gtyp (Fuint          w)) => Some (Needtobedefined    (Gtyp (Fsint          w.+1)))
    | Ucvt, Needtobedefined    (Gtyp (Fsint          w))
    | Ucvt, Uninitialized      (Gtyp (Fsint          w)) => Some (Needtobedefined    (Gtyp (Fsint          w)))

    | Uneg, Gval (Fuint          w) val1 => Some (Gval (Fsint          w.+1) (negB (zext 1 val1)))
    | Uneg, Gval (Fsint          w) val1 => Some (Gval (Fsint          w.+1) (negB (sext 1 val1)))
    | Uneg, Undefinedonpurpose (Gtyp (Fuint          w))
    | Uneg, Undefinedonpurpose (Gtyp (Fsint          w)) => Some (Undefinedonpurpose (Gtyp (Fsint          w.+1)))
    | Uneg, Needtobedefined    (Gtyp (Fuint          w))
    | Uneg, Uninitialized      (Gtyp (Fuint          w))
    | Uneg, Needtobedefined    (Gtyp (Fsint          w))
    | Uneg, Uninitialized      (Gtyp (Fsint          w)) => Some (Needtobedefined (Gtyp (Fsint          w.+1)))

    | Unot, Gval (Fuint          w) val1
    | Unot, Gval (Fsint          w) val1 => Some (Gval (Fuint          w) (invB val1))
    | Unot, Undefinedonpurpose (Gtyp (Fuint          w))
    | Unot, Undefinedonpurpose (Gtyp (Fsint          w)) => Some (Undefinedonpurpose (Gtyp (Fuint          w)))
    | Unot, Needtobedefined    (Gtyp (Fuint          w))
    | Unot, Uninitialized      (Gtyp (Fuint          w))
    | Unot, Needtobedefined    (Gtyp (Fsint          w))
    | Unot, Uninitialized      (Gtyp (Fsint          w)) => Some (Needtobedefined    (Gtyp (Fuint          w)))

    | Uandr, Gval (Fuint          _) val1
    | Uandr, Gval (Fsint          _) val1 => Some (Gval (Fuint 1) [::foldr andb b1 val1])
    | Uandr, Undefinedonpurpose (Gtyp (Fuint          _))
    | Uandr, Undefinedonpurpose (Gtyp (Fsint          _)) => Some (Undefinedonpurpose (Gtyp (Fuint 1)))
    | Uandr, Needtobedefined    (Gtyp (Fuint          _))
    | Uandr, Needtobedefined    (Gtyp (Fsint          _))
    | Uandr, Uninitialized      (Gtyp (Fuint          _))
    | Uandr, Uninitialized      (Gtyp (Fsint          _)) => Some (Needtobedefined    (Gtyp (Fuint 1)))

    | Uorr, Gval (Fuint          _) val1
    | Uorr, Gval (Fsint          _) val1 => Some (Gval (Fuint 1) [::foldr orb b0 val1])
    | Uorr, Undefinedonpurpose (Gtyp (Fuint          _))
    | Uorr, Undefinedonpurpose (Gtyp (Fsint          _)) => Some (Undefinedonpurpose (Gtyp (Fuint 1)))
    | Uorr, Needtobedefined    (Gtyp (Fuint          _))
    | Uorr, Needtobedefined    (Gtyp (Fsint          _))
    | Uorr, Uninitialized      (Gtyp (Fuint          _))
    | Uorr, Uninitialized      (Gtyp (Fsint          _)) => Some (Needtobedefined    (Gtyp (Fuint 1)))

    | Uxorr, Gval (Fuint          _) val1
    | Uxorr, Gval (Fsint          _) val1 => Some (Gval (Fuint 1) [::foldr xorb b0 val1])
    | Uxorr, Undefinedonpurpose (Gtyp (Fuint          _))
    | Uxorr, Undefinedonpurpose (Gtyp (Fsint          _)) => Some (Undefinedonpurpose (Gtyp (Fuint 1)))
    | Uxorr, Needtobedefined    (Gtyp (Fuint          _))
    | Uxorr, Needtobedefined    (Gtyp (Fsint          _))
    | Uxorr, Uninitialized      (Gtyp (Fuint          _))
    | Uxorr, Uninitialized      (Gtyp (Fsint          _)) => Some (Needtobedefined    (Gtyp (Fuint 1)))

    | Uextr hi lo, Gval (Fuint          w) val1
    | Uextr hi lo, Gval (Fsint          w) val1 => if lo <= hi < w then Some (Gval (Fuint          (     hi.+1  -lo)) (drop lo (take hi.+1 val1))) else None
    | Uextr hi lo, Undefinedonpurpose (Gtyp (Fuint          w))
    | Uextr hi lo, Undefinedonpurpose (Gtyp (Fsint          w)) => if lo <= hi < w then Some (Undefinedonpurpose (Gtyp (Fuint          (     hi.+1  -lo)))) else None
    | Uextr hi lo, Needtobedefined    (Gtyp (Fuint          w))
    | Uextr hi lo, Needtobedefined    (Gtyp (Fsint          w))
    | Uextr hi lo, Uninitialized      (Gtyp (Fuint          w))
    | Uextr hi lo, Uninitialized      (Gtyp (Fsint          w)) => if lo <= hi < w then Some (Needtobedefined    (Gtyp (Fuint          (     hi.+1  -lo)))) else None

    | Uhead n, Gval (Fuint          w) val1
    | Uhead n, Gval (Fsint          w) val1 => if n <= w then Some (Gval (Fuint                n   ) (drop (w-n) val1)) else None
    | Uhead n, Undefinedonpurpose (Gtyp (Fuint          w))
    | Uhead n, Undefinedonpurpose (Gtyp (Fsint          w)) => if n <= w then Some (Undefinedonpurpose (Gtyp (Fuint                n   ))) else None
    | Uhead n, Needtobedefined    (Gtyp (Fuint          w))
    | Uhead n, Needtobedefined    (Gtyp (Fsint          w))
    | Uhead n, Uninitialized      (Gtyp (Fuint          w))
    | Uhead n, Uninitialized      (Gtyp (Fsint          w)) => if n <= w then Some (Needtobedefined    (Gtyp (Fuint                n   ))) else None

    | Utail n, Gval (Fuint          w) val1
    | Utail n, Gval (Fsint          w) val1 => if n <= w then Some (Gval (Fuint          (w-n)) (take (w-n) val1)) else None
    | Utail n, Undefinedonpurpose (Gtyp (Fuint          w))
    | Utail n, Undefinedonpurpose (Gtyp (Fsint          w)) => if n <= w then Some (Undefinedonpurpose (Gtyp (Fuint          (w-n)))) else None
    | Utail n, Needtobedefined    (Gtyp (Fuint          w))
    | Utail n, Needtobedefined    (Gtyp (Fsint          w))
    | Utail n, Uninitialized      (Gtyp (Fuint          w))
    | Utail n, Uninitialized      (Gtyp (Fsint          w)) => if n <= w then Some (Needtobedefined    (Gtyp (Fuint          (w-n)))) else None

    | _, _ => None
    end.

(* Adapts the widths in val to be exactly those of val_for_type.
   Is used to adapt the type for connect statements in case the value read
   does not have exactly the same type as the value written.
   A variant can also be used for operator Emux. *)
Fixpoint adapt_hvalue_as_type (val : hvalue) (t : ftype) : option hvalue :=
    match val, t with
    | Gval (Fuint w)   c, Gtyp (Fuint w') => Some (Gval (Fuint w') (zext_to w' (take w' c)))
    | Gval (Fsint w)   c, Gtyp (Fsint w') => Some (Gval (Fsint w') (sext_to w' (take w' c)))
    | Gval Fasyncreset c, Gtyp Fasyncreset
    | Gval Fclock      c, Gtyp Fclock      => Some val
    | Aval elt aval, (Atyp elt' n) => option_map (Aval elt') (adapt_array_value_as_type aval elt' n)
    | Bval bval, (Btyp ff) => option_map Bval (adapt_bundle_value_as_type bval ff)
    | Undefinedonpurpose t, t' => if ftype_mux false t t' then Some (Undefinedonpurpose t') else None
    | Needtobedefined    t, t' => if ftype_mux false t t' then Some (Needtobedefined    t') else None
    | Uninitialized      t, t' => if ftype_mux false t t' then Some (Uninitialized      t') else None
    | _, _ => None
    end
with adapt_array_value_as_type (av : array_value) (elt : ftype) (n : nat) : option array_value :=
    match av, n with
    | Anil, 0 => Some Anil
    | Acons v av', n'.+1 => match adapt_hvalue_as_type v elt, adapt_array_value_as_type av' elt n' with
                            | Some v_res, Some av_res => Some (Acons v_res av_res)
                            | _, _ => None
                            end
    | _, _ => None
    end
with adapt_bundle_value_as_type (bv : bundle_value) (ff : ffield) : option bundle_value :=
    match bv, ff with
    | Bnil, Fnil => Some Bnil
    | Bflips id fl v bv', Fflips id_for_type fl_for_type t ff' =>
            if (id==id_for_type) && (fl==fl_for_type) then match adapt_hvalue_as_type v t, adapt_bundle_value_as_type bv' ff' with
                                                           | Some v_res, Some bv_res => Some (Bflips id_for_type fl_for_type v_res bv_res)
                                                           | _, _ => None
                                                           end
                                                      else None
    | _, _ => None
    end.

(* Extends the widths in val to be at least those of val_for_type.
   Is used for operator Emux, so it should follow the logic of ftype_mux. *)
Definition extend_hvalue_as_type (val : hvalue) (t : ftype) : option hvalue :=
    match ftype_mux true (type_of_val val) t with
    | Some t' => adapt_hvalue_as_type val t'
    | None => None
    end.

Definition extend_bundle_value_as_type (bv : bundle_value) (ff : ffield) : option bundle_value :=
    match ffield_mux true (type_of_bundle_val bv) ff with
    | Some ff' => adapt_bundle_value_as_type bv ff'
    | None => None
    end.

(* value of ref expressions.
   We need both sem_old and sem_new:
   sem_old is used to read Esubaccess indices, sem_new is used to read the actual value *)
Fixpoint eval_href (r : HiF.href) (sem_old sem_new: VM.t hvalue) : option hvalue :=
  match r with
  | Eid v => VM.find v sem_new
  | Esubfield r' v => match eval_href r' sem_old sem_new with
                      | Some bv => match convert_to_bundle_value bv with
                                   | Some fv => (fix aux fx := match fx with
                                                               | Bflips v' f t fxs => if (v == v') then Some t else aux fxs
                                                               | Bnil => None
                                                               end) fv
                                   | _ => None
                                   end
                      | _ => None
                      end
  | Esubindex r' n => match eval_href r' sem_old sem_new with
                      | Some av => match convert_to_array_value av with
                                   | Some (_, fv) => (fix aux fx m := match fx, m with
                                                                      | Acons t fxs, m'.+1 => aux fxs m'
                                                                      | Acons t _, 0 => Some t 
                                                                      | _, _ => None
                                                                      end) fv n
                                   | _ => None
                                   end
                      | _ => None
                      end
  | Esubaccess r' e => match eval_hfexpr e sem_old sem_old with
                       | Some (Gval (Fuint _) val) => match eval_href r' sem_old sem_new with
                                                      | Some av => match convert_to_array_value av with 
                                                                   | Some (_, fv) => (fix aux fx m := match fx, m with
                                                                                                      | Acons t fxs, m'.+1 => aux fxs m'
                                                                                                      | Acons t _, 0 => Some t 
                                                                                                      | _, _ => None
                                                                                                      end) fv (to_nat val)
                                                                   | None => None
                                                                   end
                                                      | None => None
                                                      end
                       | Some (Needtobedefined (Gtyp (Fuint _)))
                       | Some (Uninitialized (Gtyp (Fuint _))) => match eval_type_of_ref r' sem_new with
                                                                  | Some (Atyp elt _) => Some (Needtobedefined elt)
                                                                  | _ => None
                                                                  end
                       | Some (Undefinedonpurpose (Gtyp (Fuint _))) => match eval_type_of_ref r' sem_new with
                                                                       | Some (Atyp elt _) => Some (Undefinedonpurpose elt)
                                                                       | _ => None
                                                                       end
                       | _ => None
                       end
  end
(* Expression evaluation, value *)
with eval_hfexpr (exp : HiF.hfexpr) (sem_old sem_new : VM.t hvalue) : option hvalue :=
  match exp with
  | Econst t c => match t with
                  | Fuint w1 => if (size c) > w1 then None else Some (Gval (Fuint w1) (zext_to w1 c))
                  | Fsint w2 => if (size c) > w2 then None else Some (Gval (Fsint w2) (sext_to w2 c))
                  | _ => None
                  end
  | Eref r => eval_href r sem_old sem_new
  | Ecast AsUInt e => match eval_hfexpr e sem_old sem_new with
                      | Some (Gval (Fuint          w) val)
                      | Some (Gval (Fsint          w) val) => Some (Gval (Fuint w) val)
                      | Some (Gval _                  val) => Some (Gval (Fuint 1) val)
                      | Some (Undefinedonpurpose (Gtyp (Fuint          w)))
                      | Some (Undefinedonpurpose (Gtyp (Fsint          w))) => Some (Undefinedonpurpose (Gtyp (Fuint          w)))
                      | Some (Undefinedonpurpose (Gtyp _                 )) => Some (Undefinedonpurpose (Gtyp (Fuint          1)))
                      | Some (Needtobedefined    (Gtyp (Fuint          w)))
                      | Some (Needtobedefined    (Gtyp (Fsint          w)))
                      | Some (Uninitialized      (Gtyp (Fuint          w)))
                      | Some (Uninitialized      (Gtyp (Fsint          w))) => Some (Needtobedefined    (Gtyp (Fuint          w)))
                      | Some (Needtobedefined    (Gtyp _                 ))
                      | Some (Uninitialized      (Gtyp _                 )) => Some (Needtobedefined    (Gtyp (Fuint          1)))
                      | _ => None
                      end
  | Ecast AsSInt e => match eval_hfexpr e sem_old sem_new with 
                      | Some (Gval (Fuint          w) val)
                      | Some (Gval (Fsint          w) val) => Some (Gval (Fsint w) val)
                      | Some (Gval _                  val) => Some (Gval (Fsint          1) val)
                      | Some (Undefinedonpurpose (Gtyp (Fuint          w)))
                      | Some (Undefinedonpurpose (Gtyp (Fsint          w))) => Some (Undefinedonpurpose (Gtyp (Fsint          w)))
                      | Some (Undefinedonpurpose (Gtyp _                 )) => Some (Undefinedonpurpose (Gtyp (Fsint          1)))
                      | Some (Needtobedefined    (Gtyp (Fuint          w)))
                      | Some (Needtobedefined    (Gtyp (Fsint          w)))
                      | Some (Uninitialized      (Gtyp (Fuint          w)))
                      | Some (Uninitialized      (Gtyp (Fsint          w))) => Some (Needtobedefined    (Gtyp (Fsint          w)))
                      | Some (Needtobedefined    (Gtyp _                 ))
                      | Some (Uninitialized      (Gtyp _                 )) => Some (Needtobedefined    (Gtyp (Fsint          1)))
                      | _ => None
                      end
  | Ecast AsClock e => match eval_hfexpr e sem_old sem_new with 
                       | Some (Gval _ val) => Some (Gval Fclock [::lsb val])
                       | Some (Undefinedonpurpose (Gtyp _)) => Some (Undefinedonpurpose (Gtyp Fclock))
                       | Some (Needtobedefined    (Gtyp _))
                       | Some (Uninitialized      (Gtyp _)) => Some (Needtobedefined    (Gtyp Fclock))
                       | _ => None
                       end
  | Ecast AsAsync e => match eval_hfexpr e sem_old sem_new with
                       | Some (Gval _ val) => Some (Gval Fasyncreset [::lsb val])
                       | Some (Undefinedonpurpose (Gtyp _)) => Some (Undefinedonpurpose (Gtyp Fasyncreset))
                       | Some (Needtobedefined    (Gtyp _))
                       | Some (Uninitialized      (Gtyp _)) => Some (Needtobedefined    (Gtyp Fasyncreset))
                       | _ => None
                       end
(*| Ecast AsReset e => match eval_hfexpr e sem_old with Some (Gval (Fuint 1) val) => Some (Gval Freset [::lsb val]) | _ => None end *)
  | Eprim_binop op e1 e2 => match eval_hfexpr e1 sem_old sem_new, eval_hfexpr e2 sem_old sem_new with
                            | Some val1, Some val2 => eval_binop op val1 val2
                            | _, _ => None
                            end
  | Eprim_unop op e1 => match eval_hfexpr e1 sem_old sem_new with
                        | Some val => eval_unop op val
                        | None => None
                        end
  | Emux c e1 e2 => match eval_hfexpr c sem_old sem_new with
                    | Some (Gval (Fuint _) valc) => if is_zero valc then match eval_hfexpr e2 sem_old sem_new, eval_type_of_expr e1 sem_new with
                                                                         | Some val2, Some ty1 => extend_hvalue_as_type val2 ty1
                                                                         | _, _ => None
                                                                         end
                                                                    else match eval_hfexpr e1 sem_old sem_new, eval_type_of_expr e2 sem_new with
                                                                         | Some val1, Some ty2 => extend_hvalue_as_type val1 ty2
                                                                         | _, _ => None
                                                                         end
                    | Some (Undefinedonpurpose (Gtyp (Fuint _))) => match eval_type_of_expr e1 sem_new, eval_type_of_expr e2 sem_new with (* need to find result type *)
                                                                    | Some ft1, Some ft2 => option_map Undefinedonpurpose (ftype_mux true ft1 ft2)
                                                                    | _, _ => None
                                                                    end
                    | Some (Needtobedefined    (Gtyp (Fuint _)))
                    | Some (Uninitialized      (Gtyp (Fuint _))) => match eval_type_of_expr e1 sem_new, eval_type_of_expr e2 sem_new with (* need to find result type *)
                                                                    | Some ft1, Some ft2 => option_map Needtobedefined    (ftype_mux true ft1 ft2)
                                                                    | _, _ => None
                                                                    end
                    | _ => None
                    end
  end.

(* Properties of values *)

(* check the type correctness of a value.
   In particular, check whether bit strings have the correct length and
   whether array elements conform to the stated element type.
   Also disallows any implicit-width type. *)
Fixpoint hvalue_is_type_correct (val : hvalue) (t : ftype) : bool :=
    match val, t with
    | Gval (Fuint          w') bs, Gtyp (Fuint          w)
    | Gval (Fsint          w') bs, Gtyp (Fsint          w) => (size bs==w') && (w'==w)
    | Gval Fasyncreset bs, Gtyp Fasyncreset
    | Gval Fclock      bs, Gtyp Fclock      => size bs==1
    | Aval elt' aval, Atyp elt n => (elt'==elt) && array_value_is_type_correct aval elt n
    | Bval bval, Btyp ff => bundle_value_is_type_correct bval ff
    | Undefinedonpurpose t', t
    | Needtobedefined    t', t
    | Uninitialized      t', t => ftype_is_explicit_and_concrete t' && (t'==t)
    | _, _ => false
    end
with array_value_is_type_correct (aval : array_value) (elt : ftype) (n : nat) : bool :=
    match aval, n with
    | Anil, 0 => ftype_is_explicit_and_concrete elt
    | Acons val aval', n'.+1 => hvalue_is_type_correct val elt && array_value_is_type_correct aval' elt n'
    | _, _ => false
    end
with bundle_value_is_type_correct (bval : bundle_value) (ff : ffield) : bool :=
    match bval, ff with
    | Bnil, Fnil => true
    | Bflips v' f' val bval', Fflips v f t ff' => (v'==v) && (f'==f) && hvalue_is_type_correct val t && bundle_value_is_type_correct bval' ff'
    | _, _ => false
    end.

(* hvalue_is_type_correct requires explicit and concrete types *)
Lemma hvalue_is_type_correct_is_explicit :
    forall (val : hvalue) (t : ftype),
        hvalue_is_type_correct val t -> ftype_is_explicit_and_concrete t
with array_value_is_type_correct_is_explicit :
    forall (aval : array_value) (elt : ftype) (n : nat),
        array_value_is_type_correct aval elt n -> ftype_is_explicit_and_concrete elt
with bundle_value_is_type_correct_is_explicit :
    forall (bval : bundle_value) (ff : ffield),
        bundle_value_is_type_correct bval ff -> ffield_is_explicit_and_concrete ff.
Admitted.

(* If a value is type correct, then type_of_val finds the correct type. *)
Lemma type_of_array_val_correct :
    forall (av : array_value) (elt : ftype) (n : nat),
        array_value_is_type_correct av elt n -> type_of_val (Aval elt av)==Atyp elt n.
Admitted.

Lemma type_of_val_correct :
    forall (v : hvalue) (t : ftype),
        hvalue_is_type_correct v t -> type_of_val v==t
with type_of_bundle_val_correct :
    forall (bv : bundle_value) (ff : ffield),
        bundle_value_is_type_correct bv ff -> type_of_bundle_val bv==ff.
Admitted.

(* adapt_hvalue_as corrects the type of the value *)
Lemma adapt_hvalue_as_type_correct :
    forall (val : hvalue) (t1 t2 : ftype),
        hvalue_is_type_correct val t1 ->
        ftype_is_explicit_and_concrete t2 ->
        match adapt_hvalue_as_type val t2 with
        | Some val' => hvalue_is_type_correct val' t2
        | None => ~~ftype_mux false t1 t2
        end
with adapt_array_value_as_type_correct :
    forall (av : array_value) (elt1 elt2 : ftype) (n1 n2 : nat),
        array_value_is_type_correct av elt1 n1 ->
        ftype_is_explicit_and_concrete elt2 ->
        match adapt_array_value_as_type av elt2 n2 with
        | Some av' => array_value_is_type_correct av' elt2 n2
        | None => (~~ftype_mux false elt1 elt2) || (n1 != n2)
        end
with adapt_bundle_value_as_type_correct :
    forall (bv : bundle_value) (ff1 ff2 : ffield),
        bundle_value_is_type_correct bv ff1 ->
        ffield_is_explicit_and_concrete ff2 ->
        match adapt_bundle_value_as_type bv ff2 with
        | Some bv' => bundle_value_is_type_correct bv' ff2
        | None => ~~ffield_mux false ff1 ff2
        end.
Admitted.

(* extend_hvalue_as_type produces results of the same type as ftype_mux, as long as the types involved are concrete *)
Lemma extend_hvalue_as_type_and_ftype_mux :
    forall (val : hvalue) (t1 t2 : ftype),
        hvalue_is_type_correct val t1 ->
        ftype_is_explicit_and_concrete t1 ->
        ftype_is_explicit_and_concrete t2 ->
        match extend_hvalue_as_type val t2, ftype_mux true t1 t2 with
        | Some extval, Some extt => hvalue_is_type_correct extval extt
        | None, None => true
        | _, _ => false
        end.
Admitted.

(*
Lemma extend_bundle_value_as_type_and_ffield_mux :
    forall (bv : bundle_value) (ff1 ff2 : ffield),
        bundle_value_is_type_correct bv ff1 ->
        ffield_is_explicit_and_concrete ff1 ->
        ffield_is_explicit_and_concrete ff2 ->
        match extend_bundle_value_as_type bv ff2, ffield_mux true ff1 ff2 with
        | Some extbv, Some extff => bundle_value_is_type_correct extbv extff
        | None, None => true
        | _, _ => false
        end.
Proof.
unfold extend_bundle_value_as_type.
intros.
rewrite (elimT eqP (type_of_bundle_val_correct H)).
generalize (ffield_mux_associative false ff1 ff1 ff2) ; intro.
generalize (ffield_mux_idempotent false ff1) ; intro.
destruct (ffield_mux false ff1 ff1) as [ff1'|] ;
          first (subst ff1') ;
          last done.
generalize (ffield_mux_preserves_explicit_and_concrete true H0 H1) ; intro.
generalize (@ffield_mux_passive ff1 ff2) ; intro.
destruct (ffield_mux true ff1 ff2) as [ff12|] ; last done ; simpl.
specialize (H4 _ Logic.eq_refl).
rewrite (elimT eqP (proj2 (elimT andP H4))) in H2.
apply (adapt_bundle_value_as_type_correct H) in H3.
destruct (adapt_bundle_value_as_type bv ff12) as [evtbv|] ; first done.
destruct (ffield_mux false ff1 ff12) ; done.
Qed.
*)

Lemma eval_href_type_correct :
    forall sem_old sem_new : VM.t hvalue,
        ((* all elements of sem_new are type-correct *)
         forall (id : VarOrder.T),
            match VM.find id sem_new with
            | Some val => hvalue_is_type_correct val (type_of_val val) (* for array values this is not a trivial condition *)
            | None => true
            end) ->
        forall r : HiF.href,
            match eval_href r sem_old sem_new, eval_type_of_ref r sem_new with
            | Some val, Some tor => hvalue_is_type_correct val tor
            | Some _, None => false
            | None, Some tor => ftype_is_explicit_and_concrete tor (* should allow for out-of-bound array indices *)
            | None, _ => true
            end
with eval_hfexpr_type_correct :
    forall sem_old sem_new : VM.t hvalue,
        ((* all elements of sem_new are type-correct *)
         forall (id : VarOrder.T),
            match VM.find id sem_new with
            | Some val => hvalue_is_type_correct val (type_of_val val) (* for array values this is not a trivial condition *)
            | None => true
            end) ->
        forall e : HiF.hfexpr,
            match eval_hfexpr e sem_old sem_new, eval_type_of_expr e sem_new with
            | Some val, Some toe => hvalue_is_type_correct val toe
            | Some _, None => false
            | None, Some toe => ftype_is_explicit_and_concrete toe (* should allow for out-of-bound array indices *)
            | None, _ => true
            end.
Admitted.

Lemma most_expressions_are_Gtyp :
    forall (e : HiF.hfexpr) (sem : VM.t hvalue),
        match e, eval_type_of_expr e sem with
        | Emux _ _ _, _
        | Eref _, _
        | _, None
        | _, Some (Gtyp _) => True
        | _, _ => False
        end.
Admitted.

Lemma create_undef_bundle_value_is_type_correct :
    forall (undef : ftype -> hvalue) (ff : ffield),
        (forall t : ftype,
            ftype_is_explicit_and_concrete t ->
            hvalue_is_type_correct (undef t) t) ->
        ffield_is_explicit_and_concrete ff ->
        bundle_value_is_type_correct (create_undef_bundle_value undef ff) ff.
Admitted.

Lemma create_undef_array_value_is_type_correct :
    forall (undef : ftype -> hvalue) (elt : ftype) (n : nat),
        (forall t : ftype,
            ftype_is_explicit_and_concrete t ->
            hvalue_is_type_correct (undef t) t) ->
        ftype_is_explicit_and_concrete elt ->
        array_value_is_type_correct (create_undef_array_value undef elt n) elt n.
Admitted.

End Values.

(*************************************************************************)
(*************************************************************************)
(***                                                                   ***)
(***                                                                   ***)
(***           Fifth main section: Single_Cycle_Dynamics               ***)
(***                                                                   ***)
(***           Calculate the combinational part of a circuit           ***)
(***                                                                   ***)
(***                                                                   ***)
(*************************************************************************)
(*************************************************************************)

Section Single_Cycle_Dynamics.

(* We first need a function to replace a part of a reference with a new value,
   to execute a connect statement.

   However, the recursion of references href and the recursion of storage
   in array_value/bundle_value works the other way round, so it is difficult
   to just create a recursive function that accesses it.

   For example, if r has type "Atyp (Btyp (Fflips si Nflip (Fsint 2) (Fflips ui Nflip (Fuint 1) Fnil))) 3" and value
   "Aval (Acons (Bval (Bflips si Nflip (Gval (Fsint 2) [:: true , false]) (Bflips ui Nflip (Gval (Fuint 1) [:: true ]) Bnil)))
         (Acons (Bval (Bflips si Nflip (Gval (Fsint 2) [:: false, true ]) (Bflips ui Nflip (Gval (Fuint 1) [:: true ]) Bnil)))
         (Acons (Bval (Bflips si Nflip (Gval (Fsint 2) [:: true , true ]) (Bflips ui Nflip (Gval (Fuint 1) [:: false]) Bnil)))
          Anil)))", then elements of r are accessed with expression
   "Esubfield (Esubindex (Eid r) 2) fld".

   We do this: the function repl_val_part' that replaces a part of a reference
   takes as one of its parameter a function that inserts a new value for the
   reference into the old value.  This function is extended by recursing down
   until it gets a function that replaces (HiF.base_ref r).

   So, one could call the function repl_val_part' with parameters:
   reference = "Esubfield (Esubindex (Eid r) 2) si",
   function : (old value of "Esubfield (Esubindex (Eid r) 2) si") -> (new value of "Esubfield (Esubindex (Eid r) 2) si") -> (combined value of "Esubfield (Esubindex (Eid r) 2) si")
   new value for "Esubfield (Esubindex (Eid r) 2) si"
          This calls repl_val_part' recursively with
          reference = "Esubindex (Eid r) 2".
          function : (old value of "Esubindex (Eid r) 2") -> (new value of "Esubfield (Esubindex (Eid r) 2) si") -> (combined value of "Esubindex (Eid r) 2")
          new value for "Esubfield (Esubindex (Eid r) 2) si"
                This calls repl_val_part' recursively with
                reference = "Eid r".
                function : (old value of "Eid r") -> (new value of "Esubfield (Esubindex (Eid r) 2) si") -> (combined value of "Eid r")
                new value for "Esubfield (Esubindex (Eid r) 2) si"

                It returns the function, applied to the current value of "Eid r"
                                                and the new value for "Esubfield (Esubindex (Eid r) 2) si".
                That is, the combined value that "Eid r" should get.

   An additional advantage of this recursion is that also Esubaccess references
   with undefined index can be handled.  This kind of reference should replace
   every element in the array with the corresponding undefined value.  For
   example:
   reference = "Esubfield (Esubaccess (Eid r) (Undefinedonpurpose (Fuint 5)))"
   function : (old value of "Esubfield (Esubaccess (Eid r) (Undefinedonpurpose (Fuint 5))) ui") -> (new value of "Esubfield (Esubaccess (Eid r) (Undefinedonpurpose (Fuint 5))) ui") -> (combined value of "Esubfield (Esubaccess (Eid r) (Undefinedonpurpose (Fuint 5))) ui")
   new value for "Esubfield (Esubaccess (Eid r) (Undefinedonpurpose (Fuint 5))) ui"
          This calls repl_val_part' recursively with
          reference = "Esubaccess (Eid r) (Undefinedonpurpose (Fuint 5))".
          function : (old value of "Esubaccess (Eid r) (Undefinedonpurpose (Fuint 5))") -> (new value of "Esubfield (Esubaccess (Eid r) (Undefinedonpurpose (Fuint 5))) ui") -> (combined value of "Esubaccess (Eid r) (Undefinedonpurpose (Fuint 5))")
          new value for "Esubfield (Esubaccess (Eid r) (Undefinedonpurpose (Fuint 5))) ui"
                This calls repl_val_part' recursively with
                reference = "Eid r".
                function : (old value of "Eid r") -> (new value of "Esubfield (Esubaccess (Eid r) (Undefinedonpurpose (Fuint 5))) ui") -> (combined value of "Eid r")
                    * This function, however, replaces every "Esubfield (Esubindex (Eid r) ...) ui"
                      with the new value, by calling the previous function multiple times.
                new value for "Esubfield (Esubaccess (Eid r) (Undefinedonpurpose (Fuint 5))) ui"
                    * The new value is changed to "Undefinedonpurpose (Fuint 1)"

                It returns the function, applied to the current value of "Eid r"
                                                and "Undefinedonpurpose (Fuint 1)".
                That is, the combined value that "Eid r" should get.
 *)

(* takes the "most undefined" value of two values.
   It is assumed that they have the same type, and at least one of them is undefined. *)
Definition undef_max (undef1 undef2 : hvalue) : hvalue :=
    match undef1 with
    | Undefinedonpurpose _ => match undef2 with
                              | Needtobedefined _
                              | Uninitialized   _ => undef2
                              | _ => undef1
                              end
    | Needtobedefined    _ => match undef2 with
                              | Uninitialized   _ => undef2
                              | _ => undef1
                              end
    | Uninitialized      _ => undef1
    | _ => undef2
    end.

(* Replace the current value of reference r with a new value,
   and return the combined value that (HiF.base_ref r) should become.

   r = reference that needs to be replaced
   fn = function that takes the old value for r and the new_val parameter
                      and returns the combined value that r should become
   old_base_val = old value for (HiF.base_ref r)
   new_val = new value for the part of r that needs to be replaced
   sem_old = semantics, used to read Esubaccess indices

   Result: a suggestion for a new value of (HiF.base_ref r). *)
Fixpoint repl_val_part (r : HiF.href) (fn : hvalue -> hvalue -> option hvalue) (old_base_val new_val : hvalue) (sem_old : VM.t hvalue) : option hvalue :=
    match r with
    | Eid id => fn old_base_val new_val
    | Esubfield r' id => repl_val_part r' (fun (old_val new_val : hvalue) => match convert_to_bundle_value old_val with
                                                                             | Some old_bval => option_map Bval ((fix repl_bundle_value_part (bv : bundle_value) :=
                                                                                                                      match bv with
                                                                                                                      | Bnil => None
                                                                                                                      | Bflips id' fl vv bv' => if id==id' then option_map ((Bflips id' fl)^~ bv') (fn vv new_val)
                                                                                                                                                           else option_map ( Bflips id' fl vv) (repl_bundle_value_part bv')
                                                                                                                      end) old_bval)
                                                                             | None => None
                                                                             end) old_base_val new_val sem_old
    | Esubindex r' i => repl_val_part r' (fun (old_val new_val : hvalue) => match convert_to_array_value old_val with
                                                                            | Some (elt, old_aval) => option_map (Aval elt) ((fix repl_array_value_part (av : array_value) (i : nat) :=
                                                                                                                                  match av, i with
                                                                                                                                  | Anil, _ => None
                                                                                                                                  | Acons el av', 0 => option_map (Acons^~ av') (fn el new_val)
                                                                                                                                  | Acons el av', i'.+1 => option_map (Acons el) (repl_array_value_part av' i')
                                                                                                                                  end) old_aval i)
                                                                             | _ => None
                                                                             end) old_base_val new_val sem_old
    | Esubaccess r' e => match eval_hfexpr e sem_old sem_old with
                         | Some (Gval (Fuint _) bs) => (* same as for Esubindex *)
                                                       repl_val_part r' (fun (old_val new_val : hvalue) => match convert_to_array_value old_val with
                                                                                                           | Some (elt, old_aval) => option_map (Aval elt) ((fix repl_array_value_part (av : array_value) (i : nat) :=
                                                                                                                                                                 match av, i with
                                                                                                                                                                 | Anil, _ => None (* perhaps this should be changed: instead the function might return a Needtobedefined value for the whole array *)
                                                                                                                                                                 | Acons el av', 0 => option_map (Acons^~ av') (fn el new_val)
                                                                                                                                                                 | Acons el av', i'.+1 => option_map (Acons el) (repl_array_value_part av' i')
                                                                                                                                                                 end) old_aval (to_nat bs))
                                                                                                            | _ => None
                                                                                                            end) old_base_val new_val sem_old
                         | Some (Undefinedonpurpose (Gtyp (Fuint _))) => (* new function: replaces every subexpression *)
                                                       repl_val_part r' (fun (old_val new_val : hvalue) => match convert_to_array_value old_val with
                                                                                                           | Some (elt, old_aval) => option_map (Aval elt) ((fix repl_array_value_part (av : array_value) :=
                                                                                                                                                                 match av with
                                                                                                                                                                 | Anil => Some Anil
                                                                                                                                                                 | Acons el av' => match fn el new_val, repl_array_value_part av' with
                                                                                                                                                                                   | Some el_new, Some av'_new => Some (Acons el_new av'_new)
                                                                                                                                                                                   | _, _ => None
                                                                                                                                                                                   end
                                                                                                                                                                 end) old_aval)
                                                                                                            | _ => None
                                                                                                            end) old_base_val (undef_max (Undefinedonpurpose (type_of_val new_val)) new_val) sem_old
                         | Some (Needtobedefined (Gtyp (Fuint _))) => (* new function: replaces every subexpression *)
                                                       repl_val_part r' (fun (old_val new_val : hvalue) => match convert_to_array_value old_val with
                                                                                                           | Some (elt, old_aval) => option_map (Aval elt) ((fix repl_array_value_part (av : array_value) :=
                                                                                                                                                                 match av with
                                                                                                                                                                 | Anil => Some Anil
                                                                                                                                                                 | Acons el av' => match fn el new_val, repl_array_value_part av' with
                                                                                                                                                                                   | Some el_new, Some av'_new => Some (Acons el_new av'_new)
                                                                                                                                                                                   | _, _ => None
                                                                                                                                                                                   end
                                                                                                                                                                 end) old_aval)
                                                                                                            | _ => None
                                                                                                            end) old_base_val (undef_max (Needtobedefined (type_of_val new_val)) new_val) sem_old
                         | Some (Uninitialized (Gtyp (Fuint _))) => (* new function: replaces every subexpression *)
                                                       repl_val_part r' (fun (old_val new_val : hvalue) => match convert_to_array_value old_val with
                                                                                                           | Some (elt, old_aval) => option_map (Aval elt) ((fix repl_array_value_part (av : array_value) :=
                                                                                                                                                                 match av with
                                                                                                                                                                 | Anil => Some Anil
                                                                                                                                                                 | Acons el av' => match fn el new_val, repl_array_value_part av' with
                                                                                                                                                                                   | Some el_new, Some av'_new => Some (Acons el_new av'_new)
                                                                                                                                                                                   | _, _ => None
                                                                                                                                                                                   end
                                                                                                                                                                 end) old_aval)
                                                                                                            | _ => None
                                                                                                            end) old_base_val (undef_max (Uninitialized (type_of_val new_val)) new_val) sem_old
                         | _ => None
                         end
    end.

(* Flips the orientation ori if fl = Flipped.

   fl = fflip that indicates whether the orientation should be flipped.
   ori = orientatioon (can be Duplex, Source, or Sink)

   Returns: the flipped orientation if fl = Flipped; otherwise, just ori. *)
Definition flip_orient_if (fl : fflip) (ori : forient) : option forient :=
    match fl, ori with
    | Nflip, _
    | Flipped, Duplex => Some ori
    | Flipped, Source => Some Sink
    | Flipped, Sink => Some Source
    | Flipped, _ => None
    end.

(* calculates the flow orientation and the type of r

   r = reference whose orientation and type is needed
   tmap = type-and-kind map of the circuit

   Returns: a pair consisting of the orientation of r and its type;
            however, if r is undefined, None is returned. *)
Fixpoint orient_of_ref (r : HiF.href) (tmap : VM.t (ftype * fcomponent)) : option (forient * ftype) :=
    match r with
    | Eid v => match VM.find v tmap with
               | Some (t, c) => Some (orient_of_comp c, t)
               | None => None
               end
    | Esubfield r' v => match orient_of_ref r' tmap with
                        | Some (ori, Btyp ff) => let fix orient_of_field (ff0 : ffield) : option (forient * ftype) :=
                                                         match ff0 with
                                                         | Fnil => None
                                                         | Fflips v' fl t ff0' => if v!=v' then orient_of_field ff0'
                                                                                           else match flip_orient_if fl ori with
                                                                                                | Some ori => Some (ori, t)
                                                                                                | None => None
                                                                                                end
                                                         end
                                                 in orient_of_field ff
                        | _ => None
                        end
    | Esubindex r' _
    | Esubaccess r' _ => match orient_of_ref r' tmap with
                         | Some (ori, Atyp t _) => Some (ori, t)
                         | _ => None
                         end
    end.

(* Checks whether v is passive

   v = value that is checked

   Returns: true if v does not contain any flipped fields *)
Fixpoint is_passive_value (v : hvalue) : bool :=
    match v with
    | Gval _ _ => true
    | Aval elt _ => is_passive elt
    | Bval bv => is_passive_bundle_value bv
    | Undefinedonpurpose t
    | Needtobedefined    t
    | Uninitialized      t => is_passive t
    end
with is_passive_bundle_value (bv : bundle_value) : bool :=
    match bv with
    | Bnil => true
    | Bflips _ Nflip v bv' => is_passive_value v && is_passive_bundle_value bv'
    | Bflips _ Flipped _ _ => false
    end.

(* combines two (different) undefined values to a value of type t

   ori = orientation of the values (either Source or Sink):
         the flipped parts of a Source are replaced; the unflipped parts of a Sink are replaced.
   t = desired type of the result
   writeable_undef = value (e.g. Undefinedonpurpose) that the writeable parts of t should get
   unchanged_undef = value (e.g. Uninitialized) that the unchanged parts of t should get

   Returns: a combination of writeable_undef and unchanged_undef having type t *)
Fixpoint combine_writeable_undef (ori : forient) (t : ftype) (writeable_undeftype unchanged_undeftype : ftype -> hvalue) : option hvalue :=
    match t with
    | Gtyp ft => match ori with
                 | Source => Some (unchanged_undeftype t)
                 | Sink
                 | Duplex => Some (writeable_undeftype t)
                 | _ => None
                 end
    | Atyp elt n => match combine_writeable_undef ori elt writeable_undeftype unchanged_undeftype with
                    | Some el => Some (Aval elt ((fix combine_writeable_undef_array (n : nat) : array_value :=
                                                  match n with
                                                  | 0 => Anil
                                                  | n'.+1 => Acons el (combine_writeable_undef_array n')
                                                  end) n))
                    | None => None
                    end
    | Btyp ff => option_map Bval (combine_writeable_undef_ffield ori ff writeable_undeftype unchanged_undeftype)
    end
with combine_writeable_undef_ffield (ori : forient) (ff : ffield) (writeable_undeftype unchanged_undeftype : ftype -> hvalue) : option bundle_value :=
    match ff with
    | Fnil => Some Bnil
    | Fflips id fl t ff' => match (if is_passive t then match flip_orient_if fl ori with
                                                        | Some Source => Some (unchanged_undeftype t)
                                                        | Some Sink
                                                        | Some Duplex => Some (writeable_undeftype t)
                                                        | _ => None
                                                        end
                                                   else match flip_orient_if fl ori with
                                                        | Some ori_t => combine_writeable_undef ori_t t writeable_undeftype unchanged_undeftype
                                                        | None => None
                                                        end),
                                  combine_writeable_undef_ffield ori ff' writeable_undeftype unchanged_undeftype with
                            | Some v, Some bv => Some (Bflips id fl v bv)
                            | _, _ => None
                            end
    end.

(* replaces the writeable parts of old_val by the corresponding undefined value (Undefinedonpurpose, Needtobedefined or Uninitialized).
   replace_array_writeable_undef and replace_bundle_writeable_undef are inefficient
   if they are called directly on passive values.

   undeftype = type of the undefined value (Undefinedonpurpose, Needtobedefined or Uninitialized)
   ori = orientation of the values (either Source or Sink):
         the flipped parts of a Source are replaced; the unflipped parts of a Sink are replaced.
   old_val = old value (for all parts; needs to be preserved for the non-writeable parts)

   Result: mix between old_val and undeftype: the writeable parts are undefined,
   the other parts equal to old_val *)
Fixpoint replace_writeable_undef (undeftype : ftype -> hvalue) (ori : forient) (old_val : hvalue) : option hvalue :=
    if is_passive_value old_val then match ori with
                                     | Source => Some old_val
                                     | Sink
                                     | Duplex => Some (undeftype (type_of_val old_val))
                                     | _ => None
                                     end
                                else match old_val with
                                     | Gval _ _ => None (* cannot happen, as Gval is passive *)
                                     | Aval elt old_aval => option_map (Aval elt) (replace_array_writeable_undef undeftype ori old_aval)
                                     | Bval old_bval => option_map Bval (replace_bundle_writeable_undef undeftype ori old_bval)
                                     | Undefinedonpurpose t => if old_val==undeftype t then Some old_val else combine_writeable_undef ori t undeftype Undefinedonpurpose
                                     | Needtobedefined    t => if old_val==undeftype t then Some old_val else combine_writeable_undef ori t undeftype Needtobedefined
                                     | Uninitialized      t => if old_val==undeftype t then Some old_val else combine_writeable_undef ori t undeftype Uninitialized
                                     end
with replace_array_writeable_undef (undeftype : ftype -> hvalue) (ori : forient) (old_aval : array_value) : option array_value :=
    match old_aval with
    | Anil => Some Anil
    | Acons v av' => match replace_writeable_undef undeftype ori v, replace_array_writeable_undef undeftype ori av' with
                     | Some new_v, Some new_av => Some (Acons new_v new_av)
                     | _, _ => None
                     end
    end
with replace_bundle_writeable_undef (undeftype : ftype -> hvalue) (ori : forient) (old_bval : bundle_value) : option bundle_value :=
    match old_bval with
    | Bnil => Some Bnil
    | Bflips id fl v bv' => match (match flip_orient_if fl ori with
                                   | Some ori_t => replace_writeable_undef undeftype ori_t v
                                   | None => None
                                   end),
                                  replace_bundle_writeable_undef undeftype ori bv' with
                            | Some new_v, Some new_bv => Some (Bflips id fl new_v new_bv)
                            | _, _ => None
                            end
    end.

(* replaces the writeable parts of old_val by the corresponding parts of new_val.
   The types and widths of the old and new values should be exactly the same.
   replace_array_writeable and replace_bundle_writeable should only be called
   for non-passive values to ensure efficiency.

   ori = orientation of the values (Source, Sink, or Duplex):
         the flipped parts of a Source are replaced; the unflipped parts of a Sink are replaced.
         All parts of a Duplex are replaced.
   old_val = old value (for all parts; needs to be preserved for the non-writeable parts)
   new_val = new value (may include dummy values for parts that are not writeable)

   Result: mix between old_val and new_val: the writeable parts are equal
   to new_val, the other parts equal to old_val *)
Fixpoint replace_writeable (ori : forient) (old_val new_val : hvalue) : option hvalue :=
    if is_passive_value new_val then match ori with
                                     | Source => Some old_val
                                     | Sink
                                     | Duplex => Some new_val
                                     | _ => None
                                     end
                                else match new_val with
                                     | Gval _ _ => None (* cannot happen, as Gval is passive *)
                                     | Aval elt new_aval => match convert_to_array_value old_val with
                                                            | Some (_, old_aval) => option_map (Aval elt) (replace_array_writeable ori old_aval new_aval)
                                                            | None => None
                                                            end
                                     | Bval new_bval => match convert_to_bundle_value old_val with
                                                        | Some old_bval => option_map Bval (replace_bundle_writeable ori old_bval new_bval)
                                                        | None => None
                                                        end
                                     | Undefinedonpurpose _ => replace_writeable_undef Undefinedonpurpose ori old_val
                                     | Needtobedefined    _ => replace_writeable_undef Needtobedefined    ori old_val
                                     | Uninitialized      _ => replace_writeable_undef Uninitialized      ori old_val
                                     end
with replace_array_writeable (ori : forient) (old_av new_av : array_value) : option array_value :=
    match new_av, old_av with
    | Anil, Anil => Some Anil
    | Acons nv nav', Acons ov oav' => match replace_writeable ori ov nv, replace_array_writeable ori oav' nav' with
                                      | Some v, Some av' => Some (Acons v av')
                                      | _, _ => None
                                      end
    | _, _ => None
    end
with replace_bundle_writeable (ori : forient) (old_bv new_bv : bundle_value) : option bundle_value :=
    match new_bv, old_bv with
    | Bnil, Bnil => Some Bnil
    | Bflips nv nfl nhv nbv, Bflips ov ofl ohv obv => if (ov!=nv) || (ofl!=nfl) then None
                                                                                else match (match flip_orient_if ofl ori with
                                                                                            | Some ori_hv => replace_writeable ori_hv ohv nhv
                                                                                            | None => None
                                                                                            end),
                                                                                           replace_bundle_writeable ori obv nbv with
                                                                                     | Some hv, Some bv => Some (Bflips ov ofl hv bv)
                                                                                     | _, _ => None
                                                                                     end
    | _, _ => None
    end.

(* Unidirectional connect statements replace r with expression e, which is not a reference.
   e must be passive; therefore, we can simplify the replacement a little bit.

   r = reference on the left side of the Sfcnct statement; it is being changed. Must be passive.
   e = expression on the right side of the Sfcnct statement; this is the new value being assigned. Must be passive.
   sem_old = values of all components in the instance before the iteration
             (from this semantics, the values are read in connect statements)
   sem_new = new values of all components in the instance

   Result: sem_new, updated with the connection, i.e. the value of reference r is now e *)
Definition unidirectional_connect (r : HiF.href) (e : HiF.hfexpr) (sem_old sem_new : VM.t hvalue) : option (VM.t hvalue) :=
    match VM.find (HiF.base_ref r) sem_new, eval_type_of_ref r sem_new, eval_hfexpr e sem_old sem_old with
    | Some old_base_val, Some tor, Some new_val => match adapt_hvalue_as_type new_val tor with
                                                   | Some new_val => option_map ((VM.add (HiF.base_ref r))^~ sem_new) (repl_val_part r (fun (_ new_val : hvalue) => Some new_val) old_base_val new_val sem_old)
                                                   | None => None
                                                   end
    | _, _, _ => None
    end.

(* Bidirectional connect. The unflipped parts of r1 are replaced with the corresponding parts of r2;
   the flipped parts of r2 are replaced with the corresponding parts of r1.
   We have to be careful if r1 and/or r2 are Duplex; even then only one part is replaced.
   Also, it might be that r1 and r2 are different parts of the same (aggregate) variable;
   therefore, we do the replacements one after another.

   r1 = reference on the left side of the Sfcnct statement; its unflipped parts are changed.
   r2 = reference on the right side of the Sfcnct statement; its flipped parts are changed.
   tmap = type/kind map of the corresponding module (used to determine flow orientation)
   sem_old = values of all components in the instance before the iteration
             (from this semantics, the values are read in connect statements)
   sem_new = new values of all components in the instance
             (this semantics is updated and returned)

   Result: sem_new, updated with the connection, i.e. the value of the writeable parts of reference r1 is now the old value of r2,
           and the value of the writeable parts of reference r2 is now the old value of r1. *)
Definition bidirectional_connect (r1 r2 : HiF.href) (sem_old sem_new : VM.t hvalue) : option (VM.t hvalue) :=
    match (match VM.find (HiF.base_ref r1) sem_new, eval_type_of_ref r1 sem_new, eval_href r2 sem_old sem_old with
           | Some old_base_val1, Some tor1, Some new_val1 => match adapt_hvalue_as_type new_val1 tor1 with
                                                             | Some new_val1 => option_map ((VM.add (HiF.base_ref r1))^~ sem_new) (repl_val_part r1 (replace_writeable Sink) old_base_val1 new_val1 sem_old)
                                                             | None => None
                                                             end
           | _, _, _ => None
           end) with
    | Some sem_1 => match VM.find (HiF.base_ref r2) sem_1, eval_type_of_ref r2 sem_1, eval_href r1 sem_old sem_old with
                    | Some old_base_val2, Some tor2, Some new_val2 => match adapt_hvalue_as_type new_val2 tor2 with
                                                                      | Some new_val2 => option_map ((VM.add (HiF.base_ref r2))^~ sem_1) (repl_val_part r2 (replace_writeable Source) old_base_val2 new_val2 sem_old)
                                                                      | None => None
                                                                      end
                    | _, _, _ => None
                    end
    | None => None
    end.

(* Sets r to an undefined value (basically a simplified version of the connect functions above)

   r = reference to be changed (may be passive or not)
   undeftype = sort of undefined value (Undefinedonpurpose or Needtobedefined)
   sem_old = values of all components in the instance before the iteration
             (used to calculate subaccess indices)
   sem_new = new values of all components in the instance, calculated from earlier statements

   Result: sem_new, updated as required: the value of the writeable parts of r is now undeftype *)
Definition undef_ref (r : HiF.href) (undeftype : ftype -> hvalue) (sem_old sem_new : VM.t hvalue) : option (VM.t hvalue) :=
    match VM.find (HiF.base_ref r) sem_new, eval_type_of_ref r sem_new with
    | Some old_base_val, Some tor => option_map ((VM.add (HiF.base_ref r))^~ sem_new) (repl_val_part r (replace_writeable Sink) old_base_val (undeftype tor) sem_old)
    | _, _ => None
    end.

(* Sets everything that is touched by a command in ssl to Needtobedefined.
   (This is done if a Swhen condition is Needtobedefined or Uninitialized.)
   sem_old = values of all components in the instance before the iteration
             (used to calculate subaccess indices)
   set_regs = true iff register values should also be stored
              (this should only be true in the very last iteration)
   undeftype = sort of undefined value (Undefinedonpurpose or Needtobedefined)
   sem_new = new values of all components in the instance, calculated from earlier statements
             (this semantics is updated and returned)
   ssl = remaining statements in the module

   Result: sem_new, updated as required: the value of everything touched by statements in ssl is now Needtobedefined *)
Fixpoint make_undefined (sem_old : VM.t hvalue) (set_regs : bool) (undeftype : ftype -> hvalue) (sem_new : VM.t hvalue) (ssl : HiF.hfstmt_seq) : option (VM.t hvalue) :=
    match ssl with
    | Qnil => Some sem_new
    | Qcons Sskip ssl'
    | Qcons (Sinst _ _) ssl' => make_undefined sem_old set_regs undeftype sem_new ssl'
    | Qcons (Swire w t) ssl' => make_undefined sem_old set_regs undeftype (VM.add w (undeftype t) sem_new) ssl'
    | Qcons (Sreg r rt) ssl' => make_undefined sem_old set_regs undeftype (VM.add r (undeftype (type rt)) sem_new) ssl'
    | Qcons (Snode n e) ssl' => match eval_type_of_expr e sem_old with
                                | Some t => make_undefined sem_old set_regs undeftype (VM.add n (undeftype t) sem_new) ssl'
                                | None => None
                                end
    | Qcons (Sfcnct r (Eref r')) ssl' => (* bidirectional connect *)
                                         match undef_ref r undeftype sem_old sem_new with
                                         | Some sem_r => match undef_ref r' undeftype sem_old sem_r with
                                                         | Some sem_r' => make_undefined sem_old set_regs undeftype sem_r' ssl'
                                                         | None => None
                                                         end
                                         | None => None
                                         end
    | Qcons (Sfcnct r _) ssl'    (* unidirectional connect *)
    | Qcons (Sinvalid r) ssl' => match undef_ref r undeftype sem_old sem_new with
                                 | Some sem_r => make_undefined sem_old set_regs undeftype sem_r ssl'
                                 | None => None
                                 end
    | Qcons (Swhen _ ssl_true ssl_false) ssl' => match make_undefined sem_old set_regs undeftype sem_new ssl_true with
                                                 | Some sem_true => match make_undefined sem_old set_regs undeftype sem_true ssl_false with
                                                                    | Some sem_false => make_undefined sem_old set_regs undeftype sem_false ssl'
                                                                    | None => None
                                                                    end
                                                 | None => None
                                                 end
    | _ => None
    end.

(* Run one iteration of calculating the stabilized value of all components in one instance
   (the instance is given implicitly, based on its statement sequence).

   sem_old = values of all components in the instance before the iteration
             (from this semantics, the values are read in connect statements)
   set_regs = true iff register values should also be stored
              (this should only be true in the very last iteration)
   sem_new = new values of all components in the instance, calculated from earlier statements
             (this semantics is updated and returned)
   ssl = remaining statements in the module.

   Result: sem_new, updated with the effects of ssl

   We distinguish sem_old and sem_new to ensure the last connect semantics holds:
   sem_old would contain the last connect value from the previous iteration,
   while sem_new may contain a value that is going to be overwritten again. *)
Fixpoint value_iter (sem_old : VM.t hvalue) (set_regs : bool) (sem_new : VM.t hvalue) (ssl : HiF.hfstmt_seq) : option (VM.t hvalue) :=
    match ssl with
    | Qnil => Some sem_new
    | Qcons Sskip ssl'
    | Qcons (Sinst _ _) ssl' => value_iter sem_old set_regs sem_new ssl'
    | Qcons (Swire w t) ssl' => value_iter sem_old set_regs (VM.add w (Needtobedefined t) sem_new) ssl'
    | Qcons (Sreg r rt) ssl' => match VM.find r sem_old with
                                | Some old_r => value_iter sem_old set_regs (VM.add r old_r sem_new) ssl'
                                | None => None
                                end
    | Qcons (Snode n e) ssl' => match eval_hfexpr e sem_old sem_old with
                                | Some hval => value_iter sem_old set_regs (VM.add n hval sem_new) ssl'
                                | None => None
                                end
    | Qcons (Sfcnct r (Eref r')) ssl' => (* bidirectional connect *)
                                         match bidirectional_connect r r' sem_old sem_new with
                                         | Some sem_cnct => value_iter sem_old set_regs sem_cnct ssl'
                                         | None => None
                                         end
    | Qcons (Sfcnct r e) ssl' => (* unidirectional connect; must be passive *) 
                                 match unidirectional_connect r e sem_old sem_new with
                                 | Some sem_cnct => value_iter sem_old set_regs sem_cnct ssl'
                                 | None => None
                                 end
    | Qcons (Sinvalid r) ssl' => match undef_ref r Undefinedonpurpose sem_old sem_new with
                                 | Some sem_inv => value_iter sem_old set_regs sem_inv ssl'
                                 | None => None
                                 end
    | Qcons (Swhen c ssl_true ssl_false) ssl' => match eval_hfexpr c sem_old sem_old with
                                                 | Some (Gval (Fuint _) valc) => if is_zero valc then match value_iter sem_old set_regs sem_new ssl_false with
                                                                                                      | Some sem_false => value_iter sem_old set_regs sem_false ssl'
                                                                                                      | None => None
                                                                                                      end
                                                                                                 else match value_iter sem_old set_regs sem_new ssl_true with
                                                                                                      | Some sem_true => value_iter sem_old set_regs sem_true ssl'
                                                                                                      | None => None
                                                                                                      end
                                                 | Some (Undefinedonpurpose (Gtyp (Fuint _))) => match make_undefined sem_old set_regs Undefinedonpurpose sem_new ssl_true with
                                                                                                 | Some sem_true => match make_undefined sem_old set_regs Undefinedonpurpose sem_true ssl_false with
                                                                                                                    | Some sem_false => value_iter sem_old set_regs sem_false ssl'
                                                                                                                    | None => None
                                                                                                                    end
                                                                                                 | None => None
                                                                                                 end
                                                 | Some (Needtobedefined    (Gtyp (Fuint _)))
                                                 | Some (Uninitialized      (Gtyp (Fuint _))) => match make_undefined sem_old set_regs Needtobedefined sem_new ssl_true with
                                                                                                 | Some sem_true => match make_undefined sem_old set_regs Needtobedefined sem_true ssl_false with
                                                                                                                    | Some sem_false => value_iter sem_old set_regs sem_false ssl'
                                                                                                                    | None => None
                                                                                                                    end
                                                                                                 | None => None
                                                                                                 end
                                                 | _ => None
                                                 end
    | _ => None
    end.

(* Run one iteration of calculating the stabilized value of all components in the circuit.
   circuit_sem_old = values of all componentns in the circuit before the iteration
   set_regs = true iff register values should also be stored
              (this should only be true in the very last iteration)

   Result: circuit_sem_old, updated with the effects of all statements (in particular connect statements) in all modules. *)
Definition circuit_value_iter (circuit_sem_old : SVM.t (VM.t hvalue)) (set_regs : bool) : option (SVM.t (VM.t hvalue)) :=
    match find_circuit_instances with
    | Some fci => SVM.fold (fun (ii : SVM.key) (mi : VarOrder.T) (circuit_sem_new_or_none : option (SVM.t (VM.t hvalue))) =>
                            match circuit_sem_new_or_none with
                            | Some circuit_sem_new => match SVM.find ii circuit_sem_old, SVM.find ii circuit_sem_new, find_module mi with
                                                      | Some sem_old, Some sem_new, Some (FInmod _ _ ssl) => match value_iter sem_old set_regs sem_new ssl with
                                                                                                                        | Some sem_res => Some (SVM.add ii sem_res circuit_sem_new)
                                                                                                                        | None => None
                                                                                                                        end
                                                      | _, _, _ => None
                                                      end
                            | None => None
                            end) fci (Some circuit_sem_old)
    | None => None
    end.

(* Now repeat circuit_value_iter until a fixed point is reached.
   Probably we can use a similar iterator construction as earlier,
   but we need to calculate the counter differently,
   because now array elements are counted separately. *)

(* Iterate the calculation of the stabilized value of all components in the circuit
   (assuming that there are no combinatorial cycles).
   circuit_tmap = type/kind map of all modules in the circuit (used mainly to determine flow orientation in connect statements)
   n = number of iterations to take
   circuit_sem = values of all components in the circuit before the iteration *)
Fixpoint circuit_value_iterator (iter_number : nat) (circuit_sem : SVM.t (VM.t hvalue)) : option (SVM.t (VM.t hvalue)) :=
    match iter_number with
    | 0 => Some circuit_sem
    | iter_number'.+1 => match circuit_value_iter circuit_sem false with
                         | Some circuit_sem' => circuit_value_iterator iter_number' circuit_sem'
                         | None => None
                         end
    end.

(* counts the number of iterations that is needed at most, based on the the connect statements in ssl *)
Fixpoint max_iter_count (connect_count : ftype -> nat) (tmap_mi : VM.t (ftype * fcomponent)) (ssl : HiF.hfstmt_seq) : option nat :=
    match ssl with
    | Qnil => Some 0
    | Qcons s ssl' => match max_iter_count_stmt' connect_count tmap_mi s, max_iter_count connect_count tmap_mi ssl' with
                      | Some count_s, Some count_ssl' => Some (count_s + count_ssl')
                      | _, _ => None
                      end
    end
with max_iter_count_stmt' (connect_count : ftype -> nat) (tmap_mi : VM.t (ftype * fcomponent)) (s : HiF.hfstmt) : option nat :=
    match s with
    | Sfcnct r e => option_map connect_count (type_of_ref None tmap_mi r)
    | Swhen _ ssl_true ssl_false => match max_iter_count connect_count tmap_mi ssl_true, max_iter_count connect_count tmap_mi ssl_false with
                                    | Some count_true, Some count_false => Some (count_true + count_false)
                                    | _, _ => None
                                    end
    | _ => Some 0
    end.

Fixpoint module_iter_count (mml : seq HiF.hfmodule) (connect_count : ftype -> nat) (tmap : VM.t (VM.t (ftype * fcomponent))) : option nat :=
    match mml with
    | [::] => Some 0
    | FInmod mi _ ssl :: mml' => match VM.find mi tmap with
                                 | Some tmap_mi => match max_iter_count connect_count tmap_mi ssl, module_iter_count mml' connect_count tmap with
                                                   | Some n, Some n' => Some (n + n')
                                                   | _, _ => None
                                                   end
                                 | None => None
                                 end
    | _ => None
    end.

(* maximum number of iterations needed to find the fixed point of width inference.
   tmap is not changed; it is used to find the type of references. *)
Definition circuit_iter_count (connect_count : ftype -> nat) : option nat :=
    match circuit_tmap_uninferred with
    | Some ctu => module_iter_count mml connect_count ctu
    | None => None
    end.

(* count the number of ground type components in type t.
   This function is used to determine the number of iterations needed at most
   for the value iteration. Therefore it needs to count every array element separately. *)
Fixpoint Gtyp_connect_count (t : ftype) : nat :=
    match t with
    | Gtyp _ => 1
    | Atyp t' n => Gtyp_connect_count t' * n
    | Btyp ff => Gtyp_connect_count_ffield ff
    end
with Gtyp_connect_count_ffield (ff : ffield) : nat :=
    match ff with
    | Fnil => 0
    | Fflips _ _ t ff' => Gtyp_connect_count t + Gtyp_connect_count_ffield ff'
    end.

(* Calculate initial values for all ports in one module at the beginning of a cycle.
   This function sets most values to "Needtobedefined".
   ppl = list of ports of the module *)
Fixpoint ports_initial_map (ppl : seq HiF.hfport) : VM.t hvalue :=
    match ppl with
    | [::] => VM.empty hvalue
    | Finput id t :: ppl'
    | Foutput id t :: ppl' => VM.add id (Needtobedefined t) (ports_initial_map ppl')
    end.

(* Calculate initial values for all components in one module at the beginning of a cycle.
   This function sets most values to "Needtobedefined", except registers and external inputs.
   ssl = statements list of the module
   previous_cycle_register_map = (the relevant part of the) result of the previous cycle, used to initialize register values
                    (If None is given, the registers are set to "Uninitialized"; this is meant for the first cycle.)
   partial_map = partial value map of the module *)
Fixpoint statements_initial_map (ssl : HiF.hfstmt_seq) (previous_cycle_register_map : option (VM.t hvalue)) (partial_map : VM.t hvalue) : option (VM.t hvalue) :=
    match ssl with
    | Qnil => Some partial_map
    | Qcons s ssl' => match statement_initial_map s previous_cycle_register_map partial_map with
                      | Some partial_map' => statements_initial_map ssl' previous_cycle_register_map partial_map'
                      | None => None
                      end
    end
with statement_initial_map (s : HiF.hfstmt) (previous_cycle_register_map : option (VM.t hvalue)) (partial_map : VM.t hvalue) : option (VM.t hvalue) :=
    match s with
    | Sskip => Some partial_map
    | Swire v t => Some (VM.add v (Needtobedefined t) partial_map)
    | Sreg v rt => match previous_cycle_register_map with
                   | None => Some (VM.add v (Uninitialized (type rt)) partial_map)
                   | Some pcrm => match VM.find v pcrm with
                                  | Some val => Some (VM.add v val partial_map)
                                  | None => None
                                  end
                   end
    | Sinst ii mi => match module_type mi with
                     | Some t => Some (VM.add ii (Needtobedefined t) partial_map)
                     | None => None
                     end
    | Snode v e => match eval_type_of_expr e partial_map with
                   | Some t => Some (VM.add v (Needtobedefined t) partial_map)
                   | None => None
                   end
    | Sfcnct _ _
    | Sinvalid _ => Some partial_map
    | Swhen _ sst ssf => match statements_initial_map sst previous_cycle_register_map partial_map with
                         | Some partial_map_true => statements_initial_map ssf previous_cycle_register_map partial_map_true
                         | None => None
                         end
    | _ => None (* Smem *)
    end.

(* Calculate initial values for all components in one module at the beginning of a cycle.
   This function sets most values to "Needtobedefined", except registers and external inputs.
   ii = instance identifier
   mi = module identifier (module type) of this instance
   previous_cycle_register_map = result of the previous cycle, used to initialize register values
                    (If None is given, the registers are set to "Uninitialized"; this is meant for the first cycle.)
   partial_map = partial value map of the circuit; the values for instance ii are updated in this map *)
Definition module_initial_map (ii : seq VarOrder.T) (mi : VarOrder.T) (previous_cycle_register_map : option (SVM.t (VM.t hvalue))) (partial_map : SVM.t (VM.t hvalue)) : option (SVM.t (VM.t hvalue)) :=
    match find_module mi, previous_cycle_register_map with
    | Some (FInmod _ ppl ssl), Some circ_pcrm => match SVM.find ii circ_pcrm with
                                                 | Some pcrm => match statements_initial_map ssl (Some pcrm) (ports_initial_map ppl) with
                                                                | Some imm => Some (SVM.add ii imm partial_map)
                                                                | None => None
                                                                end
                                                 | None => None
                                                 end
    | Some (FInmod _ ppl ssl), None => match statements_initial_map ssl None (ports_initial_map ppl) with
                                       | Some imm => Some (SVM.add ii imm partial_map)
                                       | None => None
                                       end
    | _, _ => None
    end.

(* Update top_map, which is assumed to be the value map of the top module,
   with input port values taken from external_inputs.
   top_map = initial value for the components in the top module at the beginning of a cycle
   external_inputs = value map of the top module, from which values of external inputs are copied
   ppl = list of ports of the top module. This determines which values are copied from external_inputs to top_map. *)
Fixpoint update_external_ports (top_map : VM.t hvalue) (external_inputs : VM.t hvalue) (ppl : seq HiF.hfport) : option (VM.t hvalue) :=
    match ppl with
    | [::] => Some top_map
    | Finput id t :: ppl'  => if is_passive t then match VM.find id external_inputs with
                                                   | Some new_val => update_external_ports (VM.add id new_val top_map) external_inputs ppl'
                                                   | None => None
                                                   end
                                              else match VM.find id top_map, VM.find id external_inputs with
                                                   | Some old_val, Some new_val => match replace_writeable Sink old_val new_val with
                                                                                   | Some combined_val => update_external_ports (VM.add id combined_val top_map) external_inputs ppl'
                                                                                   | None => None
                                                                                   end
                                                   | _, _ => None
                                                   end
    | Foutput id t :: ppl' => if is_passive t then update_external_ports top_map external_inputs ppl'
                                              else match VM.find id top_map, VM.find id external_inputs with
                                                   | Some old_val, Some new_val => match replace_writeable Source old_val new_val with
                                                                                   | Some combined_val => update_external_ports (VM.add id combined_val top_map) external_inputs ppl'
                                                                                   | None => None
                                                                                   end
                                                   | _, _ => None
                                                   end
    end.

(* Calculate initial values for all components in the circuit at the beginning of a cycle.
   This function sets most values to "Needtobedefined", except registers and external inputs.
   previous_cycle_register_map = result of the previous cycle, used to initialize register values
                    (If None is given, the registers are set to "Uninitialized"; this is meant for the first cycle.)
   external_inputs = value map of the top module, used to initialize external inputs of the whole circuit *)
Definition circuit_initial_map (previous_cycle_register_map : option (SVM.t (VM.t hvalue))) (external_inputs : VM.t hvalue) : option (SVM.t (VM.t hvalue)) :=
    match find_circuit_instances with
    | Some fci => match SVM.fold (fun (ii : seq VarOrder.T) (mi : VarOrder.T) (partial_map : option (SVM.t (VM.t hvalue))) 
                                      => match partial_map with
                                         | Some pm => module_initial_map ii mi previous_cycle_register_map pm
                                         | None => None
                                         end) fci (Some (SVM.empty (VM.t hvalue))) with
                  | Some cim => match find_module mi_top, SVM.find [::] cim with
                                | Some (FInmod _ ppl _), Some top_map => match update_external_ports top_map external_inputs ppl with
                                                                         | Some new_top_map => Some (SVM.add [::] new_top_map cim)
                                                                         | None => None
                                                                         end
                                | _, _ => None
                                end
                  | None => None
                  end
    | None => None
    end.

(* Iteratively calculate the stabilized value of all components in the circuit
   (assuming that there are no combinatorial cycles).
   previous_cycle_register_map = result of the previous cycle, used to initialize register values
                    (If None is given, the registers are set to "Uninitialized"; this is meant for the first cycle.)
   external_inputs = value map of the top module, used to initialize external inputs of the whole circuit *)
Definition circuit_value (previous_cycle_register_map : option (SVM.t (VM.t (hvalue)))) (external_inputs : VM.t hvalue) : option (SVM.t (VM.t hvalue)) :=
    match circuit_initial_map previous_cycle_register_map external_inputs, circuit_iter_count Gtyp_connect_count with
    | Some circuit_sem_basic, Some n => match circuit_value_iterator n circuit_sem_basic with
                                        | Some circuit_sem => circuit_value_iter circuit_sem true (* one additional iteration to set registers to their new values *)
                                        | None => None
                                        end
    | _, _ => None
    end.

(* Properties of circuit_value *)

Fixpoint ftype_is_empty (t : ftype) : bool :=
    match t with
    | Gtyp _ => false
    | Atyp _ 0 => true
    | Atyp elt _ => ftype_is_empty elt
    | Btyp ff => ffield_is_empty ff
    end
with ffield_is_empty (ff : ffield) : bool :=
    match ff with
    | Fnil => true
    | Fflips _ _ t ff => ftype_is_empty t && ffield_is_empty ff
    end.

Fixpoint hvalue_is_undef_or_empty (undeftype : ftype -> hvalue) (v : hvalue) (t : ftype) : bool :=
    match v with
    | Aval eltv av => match t with
                      | Atyp eltt n => (eltv==eltt) && array_value_is_undef_or_empty undeftype av eltt n
                      | _ => false
                      end
    | Bval bv => match t with
                 | Btyp ff => bundle_value_is_undef_or_empty undeftype bv ff
                 | _ => false
                 end
    | Undefinedonpurpose tv
    | Needtobedefined    tv
    | Uninitialized      tv => if ftype_is_empty tv then tv==t else v==undeftype t
    | _ => false
    end
with array_value_is_undef_or_empty (undeftype : ftype -> hvalue) (av : array_value) (elt : ftype) (n : nat) : bool :=
    match av, n with
    | Anil, 0 => true
    | Acons el av, n.+1 => hvalue_is_undef_or_empty undeftype el elt && array_value_is_undef_or_empty undeftype av elt n
    | _, _ => false
    end
with bundle_value_is_undef_or_empty (undeftype : ftype -> hvalue) (bv : bundle_value) (ff : ffield) : bool :=
    match bv, ff with
    | Bnil, Fnil => true
    | Bflips idv flv vv bv, Fflips idt flt ty ff => (idv==idt) && (flv==flt) && hvalue_is_undef_or_empty undeftype vv ty && bundle_value_is_undef_or_empty undeftype bv ff
    | _, _ => false
    end.

(* Not sure if this lemma is helpful; we do not have hvalue_is_type_correct
   in the assumptions below.
Lemma ftype_is_empty_implies_hvalue_is_undef_or_empty :
    forall (elt : ftype) (undeftype : ftype -> hvalue) (val : hvalue),
        ftype_is_empty elt -> 
        hvalue_is_type_correct val elt ->
        hvalue_is_undef_or_empty undeftype val elt
with ftype_is_empty_implies_array_value_is_undef_or_empty :
    forall (elt : ftype) (n : nat) (undeftype : ftype -> hvalue) (av : array_value),
        ftype_is_empty elt || (n == 0) ->
        array_value_is_type_correct av elt n ->
        array_value_is_undef_or_empty undeftype av elt n
with ffield_is_empty_implies_bundle_value_is_undef_or_empty :
    forall (ff : ffield) (undeftype : ftype -> hvalue) (bv : bundle_value),
        ffield_is_empty ff ->
        bundle_value_is_type_correct bv ff ->
        bundle_value_is_undef_or_empty undeftype bv ff.
Proof.
* clear ftype_is_empty_implies_hvalue_is_undef_or_empty.
  intros elt undeftype val ; revert elt undeftype.
  induction val as [ft|av|bv|ut|ut|ut] ; simpl ; try done ; intros.
*)

(* If a value is undef, it can only be one kind of undef (unless it's empty) *)
Lemma hvalue_is_undef_or_empty_unique :
    forall (undeftype1 undeftype2 : ftype -> hvalue),
        (undeftype1 = Undefinedonpurpose \/ undeftype1 = Needtobedefined \/ undeftype1 = Uninitialized) ->
        (undeftype2 = Undefinedonpurpose \/ undeftype2 = Needtobedefined \/ undeftype2 = Uninitialized) ->
        forall (v : hvalue) (t1 t2 : ftype),
            hvalue_is_undef_or_empty undeftype1 v t1 ->
            (hvalue_is_undef_or_empty undeftype2 v t2 <-> t1==t2 /\ (ftype_is_empty t1 \/ forall t : ftype, undeftype1 t==undeftype2 t))
with array_value_is_undef_or_empty_unique :
    forall (undeftype1 undeftype2 : ftype -> hvalue),
        (undeftype1 = Undefinedonpurpose \/ undeftype1 = Needtobedefined \/ undeftype1 = Uninitialized) ->
        (undeftype2 = Undefinedonpurpose \/ undeftype2 = Needtobedefined \/ undeftype2 = Uninitialized) ->
        forall (av : array_value) (elt1 elt2 : ftype) (n1 n2 : nat),
            array_value_is_undef_or_empty undeftype1 av elt1 n1 ->
            (array_value_is_undef_or_empty undeftype2 av elt2 n2 <-> ((elt1==elt2) || (n1==0)) && (n1==n2) /\ (ftype_is_empty elt1 || (n1==0) \/ forall t : ftype, undeftype1 t==undeftype2 t))
with bundle_value_is_undef_or_empty_unique :
    forall (undeftype1 undeftype2 : ftype -> hvalue),
        (undeftype1 = Undefinedonpurpose \/ undeftype1 = Needtobedefined \/ undeftype1 = Uninitialized) ->
        (undeftype2 = Undefinedonpurpose \/ undeftype2 = Needtobedefined \/ undeftype2 = Uninitialized) ->
        forall (bv : bundle_value) (ff1 ff2 : ffield),
            bundle_value_is_undef_or_empty undeftype1 bv ff1 ->
            (bundle_value_is_undef_or_empty undeftype2 bv ff2 <-> ff1==ff2 /\ (ffield_is_empty ff1 \/ forall t : ftype, undeftype1 t==undeftype2 t)).
Admitted.

(* Equality up to unfolding of undefined values using create_undef ... *)
Fixpoint unfold_undef_hvalue_eq (v1 v2 : hvalue) : bool :=
    match v1 with
  (*|Gval _ _ => v1==v2 *)
    | Aval elt1 av1 => match v2 with
                       | Aval elt2 av2 => (elt1==elt2) && unfold_undef_array_value_eq av1 av2
                       | Undefinedonpurpose (Atyp elt2 n2) => (elt1==elt2) && array_value_is_undef_or_empty Undefinedonpurpose av1 elt2 n2
                       | Needtobedefined    (Atyp elt2 n2) => (elt1==elt2) && array_value_is_undef_or_empty Needtobedefined    av1 elt2 n2
                       | Uninitialized      (Atyp elt2 n2) => (elt1==elt2) && array_value_is_undef_or_empty Uninitialized      av1 elt2 n2
                       | _ => false
                       end
    | Bval bv1 => match v2 with
                  | Bval bv2 => unfold_undef_bundle_value_eq bv1 bv2
                  | Undefinedonpurpose (Btyp ff2) => bundle_value_is_undef_or_empty Undefinedonpurpose bv1 ff2
                  | Needtobedefined    (Btyp ff2) => bundle_value_is_undef_or_empty Needtobedefined    bv1 ff2
                  | Uninitialized      (Btyp ff2) => bundle_value_is_undef_or_empty Uninitialized      bv1 ff2
                  | _ => false
                  end
    | Undefinedonpurpose t1 => hvalue_is_undef_or_empty Undefinedonpurpose v2 t1
    | Needtobedefined    t1 => hvalue_is_undef_or_empty Needtobedefined    v2 t1
    | Uninitialized      t1 => hvalue_is_undef_or_empty Uninitialized      v2 t1
    | _ => v1==v2
    end
with unfold_undef_array_value_eq (av1 av2 : array_value) : bool :=
    match av1, av2 with
    | Anil, Anil => true
    | Acons el1 av1, Acons el2 av2 => unfold_undef_hvalue_eq el1 el2 && unfold_undef_array_value_eq av1 av2
    | _, _ => false
    end
with unfold_undef_bundle_value_eq (bv1 bv2 : bundle_value) : bool :=
    match bv1, bv2 with
    | Bnil, Bnil => true
    | Bflips id1 fl1 vv1 bv1, Bflips id2 fl2 vv2 bv2 => (id1==id2) && (fl1==fl2) && unfold_undef_hvalue_eq vv1 vv2 && unfold_undef_bundle_value_eq bv1 bv2
    | _, _ => false
    end.

(* unfold_undef_hvalue_eq is truly an equivalence relation: it is reflexive, symmetric, and transitive *)
Lemma unfold_undef_hvalue_eq_reflexive :
    forall (v : hvalue), unfold_undef_hvalue_eq v v
with unfold_undef_array_value_eq_reflexive :
    forall (av : array_value), unfold_undef_array_value_eq av av
with unfold_undef_bundle_value_eq_reflexive :
    forall (bv : bundle_value), unfold_undef_bundle_value_eq bv bv.
Admitted.

Lemma unfold_undef_hvalue_eq_symmetric :
    forall (v1 v2 : hvalue), unfold_undef_hvalue_eq v1 v2 -> unfold_undef_hvalue_eq v2 v1
with unfold_undef_array_value_eq_symmetric :
    forall (av1 av2 : array_value), unfold_undef_array_value_eq av1 av2 -> unfold_undef_array_value_eq av2 av1
with unfold_undef_bundle_value_eq_symmetric :
    forall (bv1 bv2 : bundle_value), unfold_undef_bundle_value_eq bv1 bv2 -> unfold_undef_bundle_value_eq bv2 bv1.
Admitted.

(* helper lemma for transitivity *)
Lemma unfold_undef_hvalue_and_hvalue_is_undef_or_empty :
    forall undeftype : ftype -> hvalue,
        (undeftype = Undefinedonpurpose \/ undeftype = Needtobedefined \/ undeftype = Uninitialized) ->
        forall (v1 v2 : hvalue) (t : ftype),
            unfold_undef_hvalue_eq v1 v2 -> hvalue_is_undef_or_empty undeftype v1 t -> hvalue_is_undef_or_empty undeftype v2 t
with unfold_undef_array_value_and_array_value_is_undef_or_empty :
    forall undeftype : ftype -> hvalue,
        (undeftype = Undefinedonpurpose \/ undeftype = Needtobedefined \/ undeftype = Uninitialized) ->
        forall (av1 av2 : array_value) (elt : ftype) (n : nat),
          unfold_undef_array_value_eq av1 av2 -> array_value_is_undef_or_empty undeftype av1 elt n -> array_value_is_undef_or_empty undeftype av2 elt n
with unfold_undef_bundle_value_and_bundle_value_is_undef_or_empty :
    forall undeftype : ftype -> hvalue,
        (undeftype = Undefinedonpurpose \/ undeftype = Needtobedefined \/ undeftype = Uninitialized) ->
        forall (bv1 bv2 : bundle_value) (ff : ffield),
            unfold_undef_bundle_value_eq bv1 bv2 -> bundle_value_is_undef_or_empty undeftype bv1 ff -> bundle_value_is_undef_or_empty undeftype bv2 ff.
Admitted.

(* helper lemma for transitivity: if two values have the same type, then they are the equivalent. *)
Lemma hvalue_is_undef_or_empty_unique_val :
    forall (undeftype : ftype -> hvalue),
        (undeftype = Undefinedonpurpose \/ undeftype = Needtobedefined \/ undeftype = Uninitialized) ->
            forall (v1 v2: hvalue) (t : ftype),
                hvalue_is_undef_or_empty undeftype v1 t ->
                hvalue_is_undef_or_empty undeftype v2 t ->
                unfold_undef_hvalue_eq v1 v2
with array_value_is_undef_or_empty_unique_val :
    forall (undeftype : ftype -> hvalue),
        (undeftype = Undefinedonpurpose \/ undeftype = Needtobedefined \/ undeftype = Uninitialized) ->
            forall (av1 av2: array_value) (elt : ftype) (n : nat),
                array_value_is_undef_or_empty undeftype av1 elt n ->
                array_value_is_undef_or_empty undeftype av2 elt n ->
                unfold_undef_array_value_eq av1 av2
with bundle_value_is_undef_or_empty_unique_val :
    forall (undeftype : ftype -> hvalue),
        (undeftype = Undefinedonpurpose \/ undeftype = Needtobedefined \/ undeftype = Uninitialized) ->
            forall (bv1 bv2: bundle_value) (ff : ffield),
                bundle_value_is_undef_or_empty undeftype bv1 ff ->
                bundle_value_is_undef_or_empty undeftype bv2 ff ->
                unfold_undef_bundle_value_eq bv1 bv2.
Admitted.

(*
Transitivity only holds for non-empty values;
in particular, if one of the three values is empty, it may not hold.
(Or should we just equate all empty values? -- that might be better)
*)

Lemma unfold_undef_hvalue_eq_transitive :
    forall (v2 v1 v3 : hvalue), unfold_undef_hvalue_eq v1 v2 -> unfold_undef_hvalue_eq v2 v3 -> unfold_undef_hvalue_eq v1 v3
with unfold_undef_array_value_eq_transitive :
    forall (av2 av1 av3 : array_value), unfold_undef_array_value_eq av1 av2 -> unfold_undef_array_value_eq av2 av3 -> unfold_undef_array_value_eq av1 av3
with unfold_undef_bundle_value_eq_transitive :
    forall (bv2 bv1 bv3 : bundle_value), unfold_undef_bundle_value_eq bv1 bv2 -> unfold_undef_bundle_value_eq bv2 bv3 -> unfold_undef_bundle_value_eq bv1 bv3.
Admitted.

(*Lemma unfold_undef_hvalue_eq_implies_hvalue_is_undef_or_empty :
    forall (undeftype : ftype -> hvalue),
        undeftype = Undefinedonpurpose \/ undeftype = Needtobedefined \/ undeftype = Uninitialized ->
        forall (t : ftype) (v : hvalue),
            unfold_undef_hvalue_eq (undeftype t) v ->
            hvalue_is_undef_or_empty undeftype v t
with unfold_undef_bundle_value_eq_implies_bundle_value_is_undef_or_empty:
    forall (undeftype : ftype -> hvalue),
        undeftype = Undefinedonpurpose \/ undeftype = Needtobedefined \/ undeftype = Uninitialized ->
        forall (ff : ffield) (bv : bundle_value),
            unfold_undef_hvalue_eq (undeftype (Btyp ff)) (Bval bv) ->
            bundle_value_is_undef_or_empty undeftype bv ff.
Proof.
* clear unfold_undef_hvalue_eq_implies_hvalue_is_undef_or_empty.
  intros undeftype H.
  destruct H as [H|[H|H]] ; subst undeftype.
  1-3: simpl.
  1-3: induction t as [ft|elt n|ff] ; try done.
destruct v as [fv|av|bv|[ftv|eltv nv|ffv]|[ftv|eltv nv|ffv]|[ftv|eltv nv|ffv]] ; simpl ; try done.
  + destruct H as [H|[H|H]] ; subst undeftype ; done.
destruct ft, fv ; simpl ; try done.
  destruct v as [

 (Undefinedonpurpose tv)
       fn_vv_onv
______________________________________(1/8)
hvalue_is_undef_or_empty Undefinedonpurpose fn_vv_onv tv &&
bundle_value_is_undef_or_empty Undefinedonpurpose
  (create_undef_bundle_value Undefinedonpurpose ff) ff*)


Lemma undef_type_correct :
    forall (undeftype : ftype -> hvalue),
        undeftype = Undefinedonpurpose \/ undeftype = Needtobedefined \/ undeftype = Uninitialized ->
        forall t : ftype,
            ftype_is_explicit_and_concrete t ->
            hvalue_is_type_correct (undeftype t) t.
Admitted.

Fixpoint has_undefined_subaccess (r : HiF.href) (sem_old : VM.t hvalue) : bool :=
    match r with
    | Eid _ => false
    | Esubfield r' _
    | Esubindex r' _ => has_undefined_subaccess r' sem_old
    | Esubaccess r' e => match eval_hfexpr e sem_old sem_old with
                         | Some (Undefinedonpurpose _)
                         | Some (Needtobedefined    _)
                         | Some (Uninitialized      _) => true
                         | _ => has_undefined_subaccess r' sem_old
                         end
    end.

Lemma repl_val_part_correct :
    forall (r : HiF.href) (fn : hvalue -> hvalue -> option hvalue) (new_val : hvalue) (sem_old sem_new : VM.t hvalue),
        ((* all elements of sem_new are type-correct *)
         forall (id : VarOrder.T),
            match VM.find id sem_new with
            | Some val => hvalue_is_type_correct val (type_of_val val) (* for array values this is not a trivial condition *)
            | None => true
            end) ->
        match VM.find (HiF.base_ref r) sem_new, eval_href r sem_old sem_new with
        | Some base_val, Some old_r_val =>
                forall (old_new_val : hvalue), (* = the old value that was in the part of r that should become new_val *)
                    (forall (ov nv : hvalue),
                        hvalue_is_type_correct ov (type_of_val old_r_val) ->
                        hvalue_is_type_correct nv (type_of_val new_val) ->
                            match fn ov nv with
                            | Some fn_ov_nv => hvalue_is_type_correct fn_ov_nv (type_of_val old_r_val)
                            | None => false
                            end) ->
                    match fn old_r_val old_new_val with
                    | Some fn_old_r_val_old_new_val => unfold_undef_hvalue_eq old_r_val fn_old_r_val_old_new_val
                    | None => false
                    end ->
                    hvalue_is_type_correct base_val (type_of_val base_val) ->
                    hvalue_is_type_correct new_val (type_of_val new_val) ->
                    (* sem_old does not need to satisfy additional conditions??? -> *)
                    hvalue_is_type_correct old_new_val (type_of_val new_val) ->
                    ~~has_undefined_subaccess r sem_old ->
                        match repl_val_part r fn base_val new_val sem_old with
                        | Some new_base_val => hvalue_is_type_correct new_base_val (type_of_val base_val)
                        | None => false (* actually: r contains some specific errors *)
                        end &&
                        match repl_val_part r fn base_val old_new_val sem_old with
                        | Some old_new_base_val => unfold_undef_hvalue_eq base_val old_new_base_val
                        | None => false
                        end
      (*| None, Some _ => False*)
        | _, _ => True
        end.
Admitted.

Lemma max_iter_count_not_none :
    forall (connect_count : ftype -> nat) (tmap_super : VM.t (ftype * fcomponent)) (ssl : HiF.hfstmt_seq) (sc_old : VS.t) (tmap_old : VM.t (ftype * fcomponent)) (sc_new : VS.t) (tmap_new : VM.t (ftype * fcomponent)),
        statements_tmap sc_old tmap_old ssl = Some (sc_new, tmap_new) ->
        (forall k : VM.key, VM.find k tmap_new <> None -> VM.find k tmap_new = VM.find k tmap_super) ->
        max_iter_count connect_count tmap_super ssl <> None
with max_iter_count_stmt'_not_none :
    forall (connect_count : ftype -> nat) (tmap_super : VM.t (ftype * fcomponent)) (s : HiF.hfstmt) (sc_old : VS.t) (tmap_old : VM.t (ftype * fcomponent)) (sc_new : VS.t) (tmap_new : VM.t (ftype * fcomponent)),
        statement_tmap sc_old tmap_old s = Some (sc_new, tmap_new) ->
        (forall k : VM.key, VM.find k tmap_new <> None -> VM.find k tmap_new = VM.find k tmap_super) ->
        max_iter_count_stmt' connect_count tmap_super s <> None.
Admitted.

Lemma circuit_iter_count_not_none :
    forall (connect_count : ftype -> nat), circuit_iter_count connect_count <> None.
Admitted.

(* Perhaps a lemma that says:
   if statements_tmap ... ssl <> None
   and previous_cycle_register_map contains all registers,
   then statements_initial_map ssl ... <> None. *)

End Single_Cycle_Dynamics.

End Semantics.
