From Coq Require Import NArith ZArith.
From mathcomp Require Import all_ssreflect.
From mathcomp.tarjan Require Import kosaraju.
From Lib Require Import Var.
From firrtl Require Import Env HiEnv HiFirrtl
  Env_with_implicit_widths HiEnv_with_implicit_widths.
From Solver Require Import constraints extract_cs extract_cswithmin graph inferWidths.
From Semantics Require Import Width_solution_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive scalar_type_relation : HiEnv.ftype -> HiEnv_with_implicit_widths.ftype -> Prop :=
| related_uint_implicit sw mw :
    scalar_type_relation (HiEnv.Gtyp (Env.Fuint_implicit sw))
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit mw))
| related_sint_implicit sw mw :
    scalar_type_relation (HiEnv.Gtyp (Env.Fsint_implicit sw))
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit mw))
| related_uint_explicit w :
    scalar_type_relation (HiEnv.Gtyp (Env.Fuint w))
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint w))
| related_sint_explicit w :
    scalar_type_relation (HiEnv.Gtyp (Env.Fsint w))
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint w))
| related_clock :
    scalar_type_relation (HiEnv.Gtyp Env.Fclock)
      (HiEnv_with_implicit_widths.Gtyp Env_with_implicit_widths.Fclock).

Definition scalar_maps_related (solver_map : solver_type_map) (sem_map : sem_component_map) : Prop :=
  forall id,
    match SolverSyntax.VM.find id solver_map, SemSyntax.VM.find id sem_map with
    | Some (st, _), Some (mt, _) => scalar_type_relation st mt
    | None, None => True
    | _, _ => False
    end.

Lemma translated_scalar_types_related t :
  scalar_type_relation (solver_type t) (sem_type t).
Proof. by case: t; constructor. Qed.

Lemma scalar_maps_related_empty :
  scalar_maps_related (SolverSyntax.VM.empty _) (SemSyntax.VM.empty _).
Proof.
  move=> id. rewrite SolverSyntax.VM.Lemmas.F.empty_o SemSyntax.VM.Lemmas.F.empty_o.
  exact I.
Qed.

Lemma scalar_maps_related_add solver_map sem_map id st mt orient kind :
  scalar_maps_related solver_map sem_map ->
  scalar_type_relation st mt ->
  scalar_maps_related (SolverSyntax.VM.add id (st, orient) solver_map)
    (SemSyntax.VM.add id (mt, kind) sem_map).
Proof.
  move=> Hmaps Htypes x.
  case Hx: (x == id).
  - rewrite (SolverSyntax.VM.Lemmas.find_add_eq Hx)
      (SemSyntax.VM.Lemmas.find_add_eq Hx).
    exact Htypes.
  - have Hneq : ~ (x == id) by move/negP: Hx.
    rewrite (SolverSyntax.VM.Lemmas.find_add_neq Hneq)
      (SemSyntax.VM.Lemmas.find_add_neq Hneq).
    exact (Hmaps x).
Qed.

Lemma scalar_maps_related_lookup solver_map sem_map id st orient :
  scalar_maps_related solver_map sem_map ->
  SolverSyntax.VM.find id solver_map = Some (st, orient) ->
  exists mt kind, SemSyntax.VM.find id sem_map = Some (mt, kind) /\
    scalar_type_relation st mt.
Proof.
  move=> Hmaps Hfind.
  move: (Hmaps id); rewrite Hfind.
  case Hsem: (SemSyntax.VM.find id sem_map) => [[mt kind]|] //= Hrel.
  by exists mt, kind.
Qed.

Lemma scalar_maps_related_is_scalar solver_map sem_map :
  scalar_maps_related solver_map sem_map ->
  forall id ty orient,
    SolverSyntax.VM.find id solver_map = Some (ty, orient) ->
    exists gt, ty = HiEnv.Gtyp gt.
Proof.
  move=> Hmaps id ty orient Hfind.
  have [mt [kind [_ Hty]]] := scalar_maps_related_lookup Hmaps Hfind.
  by case: Hty => [sw mw|sw mw|w|w|]; eexists.
Qed.

Lemma original_implicit_has_solver_position initial module_id sem_map solver_map id :
  SemSyntax.VM.find module_id initial = Some sem_map ->
  scalar_maps_related solver_map sem_map ->
  original_implicit initial module_id id ->
  exists gt orient,
    SolverSyntax.VM.find id solver_map = Some (HiEnv.Gtyp gt, orient) /\
    (exists w, gt = Env.Fuint_implicit w \/ gt = Env.Fsint_implicit w).
Proof.
  move=> Hmodule Hmaps.
  rewrite /original_implicit Hmodule.
  case Hsem: (SemSyntax.VM.find id sem_map) => [[ty kind]|] //.
  case: ty Hsem => [gt|elt n|fields] Hsem //.
  case: gt Hsem => [w|w|w|w| | | |] Hsem //= _.
  - move: (Hmaps id); rewrite Hsem.
    case Hsolver: (SolverSyntax.VM.find id solver_map) => [[st orient]|] //= Hrel.
    inversion Hrel; subst.
    exists (Env.Fuint_implicit sw), orient.
    by split; first reflexivity; exists sw; left.
  - move: (Hmaps id); rewrite Hsem.
    case Hsolver: (SolverSyntax.VM.find id solver_map) => [[st orient]|] //= Hrel.
    inversion Hrel; subst.
    exists (Env.Fsint_implicit sw), orient.
    by split; first reflexivity; exists sw; right.
Qed.

Lemma statement_tmaps_preserve_relation modules scope solver_map sem_map
    s solver_next sem_next scope_next :
  scalar_maps_related solver_map sem_map ->
  SolverSyntax.stmt_tmap' solver_map (solver_stmt s) = Some solver_next ->
  Semantics.statement_tmap modules scope sem_map (sem_stmt s) =
    Some (scope_next, sem_next) ->
  scalar_maps_related solver_next sem_next.
Proof.
  move=> Hmaps Hsolver Hsem.
  case: s Hsolver Hsem => [|id ty|id ty clock rst|id value] /=.
  - move=> H1 H2. by inversion H1; inversion H2; subst.
  - case: (SolverSyntax.VM.find id solver_map) => [[st orient]|] //=.
    case: (SemSyntax.VM.find id sem_map) => [[mt kind]|] //=.
    move=> H1 H2. inversion H1; inversion H2; subst.
    exact: scalar_maps_related_add Hmaps (translated_scalar_types_related ty).
  - case: (SolverSyntax.VM.find id solver_map) => [[st orient]|] //=.
    case: (SolverSyntax.VM.find clock solver_map) => [[ct orient]|] //=.
    case: (SemSyntax.VM.find id sem_map) => [[mt kind]|] //=.
    move=> H1 H2. inversion H1; inversion H2; subst.
    exact: scalar_maps_related_add Hmaps (translated_scalar_types_related ty).
  - move=> [<-].
    case: (Semantics.VS.mem id scope) => //=.
    case: (SemSyntax.VM.find id sem_map) => [[tr kind]|] //=.
    case: (Semantics.type_of_expr (Some scope) sem_map (sem_expr value)) => [te|] //=.
    case: (Semantics.ftype_mux false tr te) => [t|] //=.
    move=> H. by inversion H; subst.
Qed.

Lemma statements_tmaps_preserve_relation modules ss scope solver_map sem_map
    solver_final sem_final scope_final :
  scalar_maps_related solver_map sem_map ->
  SolverSyntax.stmts_tmap' solver_map (solver_stmts ss) = Some solver_final ->
  Semantics.statements_tmap modules scope sem_map (sem_stmts ss) =
    Some (scope_final, sem_final) ->
  scalar_maps_related solver_final sem_final.
Proof.
  move: scope solver_map sem_map.
  elim: ss => [|s ss IH] scope solver_map sem_map Hmaps /=.
  - move=> H1 H2. by inversion H1; inversion H2; subst.
  - case Hsolver: (SolverSyntax.stmt_tmap' solver_map (solver_stmt s))
      => [solver_next|] //=.
    case Hsem: (Semantics.statement_tmap modules scope sem_map (sem_stmt s))
      => [[scope_next sem_next]|] //=.
    move=> Hsolver_final Hsem_final.
    apply: (IH scope_next solver_next sem_next _ Hsolver_final Hsem_final).
    exact: (statement_tmaps_preserve_relation Hmaps Hsolver Hsem).
Qed.

Lemma solver_ports_preserve_existing ports initial final id binding :
  SolverSyntax.ports_tmap' initial (map solver_port ports) = Some final ->
  SolverSyntax.VM.find id initial = Some binding ->
  SolverSyntax.VM.find id final = Some binding.
Proof.
  move: initial.
  elim: ports => [|p ports IH] initial /=.
  - by move=> [<-].
  - case: p => [v ty|v ty|v] /=;
      case Hfind: (SolverSyntax.VM.find v initial) => [[t o]|] //=;
      move=> Hfinal Hinitial;
      apply: (IH _ Hfinal);
      case Hsame: (id == v).
    all: try (move/eqP: Hsame => Hsame; subst id; by rewrite Hfind in Hinitial).
    all: have Hneq : ~ (id == v) by move/negP: Hsame.
    all: by rewrite (SolverSyntax.VM.Lemmas.find_add_neq Hneq).
Qed.

Definition common_port_id (p : common_port) : var :=
  match p with CInput id _ | COutput id _ | CClock id => id end.

Definition solver_port_binding (p : common_port) : HiEnv.ftype * SolverSyntax.forient :=
  match p with
  | CInput _ ty => (solver_type ty, SolverSyntax.Source)
  | COutput _ ty => (solver_type ty, SolverSyntax.Duplex)
  | CClock _ => (HiEnv.Gtyp Env.Fclock, SolverSyntax.Source)
  end.

Definition sem_port_binding (p : common_port)
    : HiEnv_with_implicit_widths.ftype * HiEnv_with_implicit_widths.fcomponent :=
  match p with
  | CInput _ ty => (sem_type ty, HiEnv_with_implicit_widths.In_port)
  | COutput _ ty => (sem_type ty, HiEnv_with_implicit_widths.Out_port)
  | CClock _ => (HiEnv_with_implicit_widths.Gtyp Env_with_implicit_widths.Fclock,
                  HiEnv_with_implicit_widths.In_port)
  end.

Lemma common_port_binding_related p :
  scalar_type_relation (solver_port_binding p).1 (sem_port_binding p).1.
Proof. by case: p => [id ty|id ty|id] /=; [apply: translated_scalar_types_related | apply: translated_scalar_types_related | constructor]. Qed.

Lemma solver_ports_find_member ports initial final p :
  SolverSyntax.ports_tmap' initial (map solver_port ports) = Some final ->
  List.In p ports ->
  SolverSyntax.VM.find (common_port_id p) final = Some (solver_port_binding p).
Proof.
  move: initial.
  elim: ports => [|q ports IH] initial //=.
  case: q => [id ty|id ty|id] /=;
    case Hfind: (SolverSyntax.VM.find id initial) => [[t o]|] //=;
    move=> Hfinal [Hp|Hp].
  all: try (subst p; apply: (solver_ports_preserve_existing Hfinal);
            by rewrite SolverSyntax.VM.Lemmas.find_add_eq // eqxx).
  all: exact: (IH _ Hfinal Hp).
Qed.

Lemma sem_ports_find_member ports final p :
  Semantics.ports_tmap (map sem_port ports) = Some final ->
  List.In p ports ->
  SemSyntax.VM.find (common_port_id p) final = Some (sem_port_binding p).
Proof.
  elim: ports final => [|q ports IH] final //=.
  case: q => [id ty|id ty|id] /=;
    case Htail: (Semantics.ports_tmap (map sem_port ports)) => [tail|] //=;
    case Hfind: (SemSyntax.VM.find id tail) => [[t k]|] //=;
    move=> Hfinal [Hp|Hp].
  all: try (subst p; inversion Hfinal; subst final;
            by rewrite SemSyntax.VM.Lemmas.find_add_eq // eqxx).
  all: have Hmember := IH tail Htail Hp.
  all: have Hneq : ~ (common_port_id p == id).
  all: try (move/eqP=> Heq; rewrite Heq Hfind in Hmember; discriminate).
  all: inversion Hfinal; subst final;
    by rewrite (SemSyntax.VM.Lemmas.find_add_neq Hneq).
Qed.

Lemma solver_ports_find_outside ports initial final id :
  SolverSyntax.ports_tmap' initial (map solver_port ports) = Some final ->
  (forall p, List.In p ports -> common_port_id p <> id) ->
  SolverSyntax.VM.find id final = SolverSyntax.VM.find id initial.
Proof.
  move: initial.
  elim: ports => [|p ports IH] initial /=.
  - by move=> [<-] _.
  - case: p => [v ty|v ty|v] /=;
    case Hfind: (SolverSyntax.VM.find v initial) => [[t o]|] //=;
    move=> Hfinal Houtside.
    all: have Hrest : forall p, List.In p ports -> common_port_id p <> id
      by move=> p Hp; apply: Houtside; right.
    all: rewrite (IH _ Hfinal Hrest).
    all: have Hneq : ~ (id == v).
    all: try (move/eqP=> Heq; apply: (Houtside _ (or_introl erefl)); by symmetry).
    all: by rewrite (SolverSyntax.VM.Lemmas.find_add_neq Hneq).
Qed.

Lemma sem_ports_find_outside ports final id :
  Semantics.ports_tmap (map sem_port ports) = Some final ->
  (forall p, List.In p ports -> common_port_id p <> id) ->
  SemSyntax.VM.find id final = None.
Proof.
  elim: ports final => [|p ports IH] final /=.
  - move=> [<-] _. by rewrite SemSyntax.VM.Lemmas.F.empty_o.
  - case: p => [v ty|v ty|v] /=;
      case Htail: (Semantics.ports_tmap (map sem_port ports)) => [tail|] //=;
      case Hfind: (SemSyntax.VM.find v tail) => [[t k]|] //=;
      move=> Hfinal Houtside; inversion Hfinal; subst final.
    all: have Hneq : ~ (id == v).
    all: try (move/eqP=> Heq; apply: (Houtside _ (or_introl erefl)); by symmetry).
    all: rewrite (SemSyntax.VM.Lemmas.find_add_neq Hneq).
    all: apply: (IH tail Htail); by move=> p Hp; apply: Houtside; right.
Qed.

Lemma ports_tmaps_related ports solver_map sem_map :
  SolverSyntax.ports_tmap' (SolverSyntax.VM.empty _) (map solver_port ports) =
    Some solver_map ->
  Semantics.ports_tmap (map sem_port ports) = Some sem_map ->
  scalar_maps_related solver_map sem_map.
Proof.
  move=> Hsolver Hsem id.
  destruct (List.in_dec N.eq_dec id (map common_port_id ports)) as [Hin|Hnotin].
  -
    apply List.in_map_iff in Hin.
    destruct Hin as [p [Hpid Hps]].
    have Hs := solver_ports_find_member Hsolver Hps.
    have Hm := sem_ports_find_member Hsem Hps.
    rewrite Hpid in Hs Hm.
    rewrite Hs Hm.
    have Hrel := common_port_binding_related p.
    case: (solver_port_binding p) Hrel => [st orient].
    by case: (sem_port_binding p) => [mt kind].
  - have Houtside : forall p, List.In p ports -> common_port_id p <> id.
    { move=> p Hp Heq.
      apply: Hnotin. apply List.in_map_iff. by exists p. }
    rewrite (solver_ports_find_outside Hsolver Houtside)
      (sem_ports_find_outside Hsem Houtside)
      SolverSyntax.VM.Lemmas.F.empty_o.
    exact I.
Qed.

Theorem initial_circuit_tmaps_related m circuit_name solver_map initial :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  exists sem_map,
    SemSyntax.VM.find (common_module_name m) initial = Some sem_map /\
    scalar_maps_related solver_map sem_map.
Proof.
  rewrite /SolverSyntax.circuit_tmap /solver_circuit /SolverSyntax.modules_tmap
    /SolverSyntax.module_tmap /solver_module /=.
  case Hports: (SolverSyntax.ports_tmap' _ (map solver_port (common_ports m)))
    => [solver_ports|] //=.
  case Hstmts: (SolverSyntax.stmts_tmap' solver_ports (solver_stmts (common_stmts m)))
    => [solver_final|] //=.
  move=> Hsolver; inversion Hsolver; subst solver_final.
  rewrite /Semantics.circuit_tmap_uninferred /sem_circuit /sem_module /=.
  case Hsemports: (Semantics.ports_tmap (map sem_port (common_ports m)))
    => [sem_ports|] //=.
  case Hsemstmts: (Semantics.statements_tmap (sem_circuit m)
      (Semantics.VKS.key_set sem_ports) sem_ports (sem_stmts (common_stmts m)))
    => [[scope_final sem_final]|] //=.
  move=> Hinitial; inversion Hinitial; subst initial.
  exists sem_final; split.
  - by rewrite SemSyntax.VM.Lemmas.find_add_eq // eqxx.
  - apply: (statements_tmaps_preserve_relation _ Hstmts Hsemstmts).
    exact: (ports_tmaps_related Hports Hsemports).
Qed.

Lemma successful_semantic_result_is_fixed m n result :
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  exists next,
    Semantics.circuit_width_iter (sem_circuit m) result = Some next /\
    forall module_id,
      match SemSyntax.VM.find module_id result, SemSyntax.VM.find module_id next with
      | Some before, Some after => forall id,
          SemSyntax.VM.find id before = SemSyntax.VM.find id after
      | None, None => True
      | _, _ => False
      end.
Proof.
  rewrite /Semantics.circuit_tmap_implicits.
  case: (Semantics.circuit_tmap_uninferred (sem_circuit m)) => [initial|] //=.
  case: (Semantics.circuit_tmap_iterator (sem_circuit m) n initial) => [iterated|] //=.
  case Hnext: (Semantics.circuit_width_iter (sem_circuit m) iterated) => [next|] //=.
  case Heq: (SemSyntax.VM.equal (SemSyntax.VM.equal pair_eq)
      iterated next) => //=.
  move=> Hresult; inversion Hresult; subst iterated.
  exists next; split; first exact Hnext.
  exact: (proj1 (Semantics.circuit_tmap_equal_find_iff result next) Heq).
Qed.

Definition common_rhs (tmap : solver_type_map) (e : common_expr)
    : option regular_rhs :=
  match e with
  | CRef id =>
      match SolverSyntax.VM.find id tmap with
      | Some (HiEnv.Gtyp (Env.Fuint_implicit _), _)
      | Some (HiEnv.Gtyp (Env.Fsint_implicit _), _) =>
          Some (make_rhs [:: (1, (id, N0))] [::] 0%Z)
      | Some (HiEnv.Gtyp gt, _) =>
          Some (make_rhs [::] [::] (Z.of_nat (Env.sizeof_fgtyp gt)))
      | _ => None
      end
  | CUInt w _ | CSInt w _ => Some (make_rhs [::] [::] (Z.of_nat w))
  end.

Lemma extract_common_expr tmap e :
  extract_constraint_expr (solver_expr e) tmap =
  option_map (fun rhs => ([:: Expr rhs], [::])) (common_rhs tmap e).
Proof.
  case: e => [id|w bits|w bits] //=.
  rewrite /HiFirrtl.type_of_ref /HiFirrtl.ref2pv /=.
  case: (SolverSyntax.VM.find id tmap) => [[ty orient]|] //=.
  by case: ty => [gt|elt n|fields] //=; case: gt.
Qed.

Definition sem_numeric_width (ty : HiEnv_with_implicit_widths.ftype) : option nat :=
  match ty with
  | HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint w)
  | HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint w)
  | HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit w)
  | HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit w) => Some w
  | _ => None
  end.

Definition valuation_matches_sem_map (value : Valuation) (sem_map : sem_component_map) : Prop :=
  forall id ty kind w,
    SemSyntax.VM.find id sem_map = Some (ty, kind) ->
    (ty = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit w) \/
     ty = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit w)) ->
    solver_width value id = Some w.

Lemma common_rhs_matches_sem_expr solver_map sem_map value e ty width :
  scalar_maps_related solver_map sem_map ->
  valuation_matches_sem_map value sem_map ->
  Semantics.type_of_expr None sem_map (sem_expr e) = Some ty ->
  sem_numeric_width ty = Some width ->
  exists rhs, common_rhs solver_map e = Some rhs /\
    min_rhs_value value (Expr rhs) = Some (Z.of_nat width).
Proof.
  move=> Hmaps Hvalue.
  case: e => [id|w bits|w bits] /=.
  - rewrite /Semantics.type_of_expr /=.
    case Hsem: (SemSyntax.VM.find id sem_map) => [[mt kind]|] //=.
    move=> [<-] Hwidth.
    move: (Hmaps id); rewrite Hsem.
    case Hsolver: (SolverSyntax.VM.find id solver_map) => [[st orient]|] //= Hrel.
    inversion Hrel; subst; simpl in Hwidth; try discriminate;
      inversion Hwidth; subst width.
    + have Hfind := Hvalue id _ _ _ Hsem (or_introl erefl).
      exists (make_rhs [:: (1, (id, N0))] [::] 0%Z).
      split; first by rewrite /common_rhs ?Hsolver.
      rewrite /solver_width in Hfind.
      by rewrite /min_rhs_value /make_rhs /= /terms_value /= Hfind /= Z.add_0_r mul1n.
    + have Hfind := Hvalue id _ _ _ Hsem (or_intror erefl).
      exists (make_rhs [:: (1, (id, N0))] [::] 0%Z).
      split; first by rewrite /common_rhs ?Hsolver.
      rewrite /solver_width in Hfind.
      by rewrite /min_rhs_value /make_rhs /= /terms_value /= Hfind /= Z.add_0_r mul1n.
    + exists (make_rhs [::] [::] (Z.of_nat w)).
      by rewrite /common_rhs ?Hsolver /= /min_rhs_value /terms_value /power_value /= Z.add_0_r.
    + exists (make_rhs [::] [::] (Z.of_nat w)).
      by rewrite /common_rhs ?Hsolver /= /min_rhs_value /terms_value /power_value /= Z.add_0_r.
  - rewrite /Semantics.type_of_expr /=.
    case: (w < size bits) => //= Hty Hwidth.
    inversion Hty; subst ty. simpl in Hwidth. inversion Hwidth; subst width.
    exists (make_rhs [::] [::] (Z.of_nat w)).
    by rewrite /common_rhs /min_rhs_value /terms_value /power_value /= Z.add_0_r.
  - rewrite /Semantics.type_of_expr /=.
    case: (w < size bits) => //= Hty Hwidth.
    inversion Hty; subst ty. simpl in Hwidth. inversion Hwidth; subst width.
    exists (make_rhs [::] [::] (Z.of_nat w)).
    by rewrite /common_rhs /min_rhs_value /terms_value /power_value /= Z.add_0_r.
Qed.

Definition common_constraint (id : var) (rhs : regular_rhs) : Constraint1 :=
  {| lhs_var1 := (id, N0);
     rhs_const1 := regular_const rhs;
     rhs_terms1 := regular_terms rhs;
     rhs_power := regular_power rhs |}.

Lemma common_constraint_rhs_value value id rhs :
  rhs_value1 value (common_constraint id rhs) = min_rhs_value value (Expr rhs).
Proof.
  rewrite /rhs_value1 /common_constraint /=.
  by case: (terms_value value (regular_terms rhs) (Some (regular_const rhs)));
     case: (power_value value (regular_power rhs)).
Qed.

Lemma common_constraint_satisfaction value id rhs :
  satisfies_constraint1 value (common_constraint id rhs) =
    match solver_width value id, min_rhs_value value (Expr rhs) with
    | Some lhs, Some value_rhs => Z.leb value_rhs (Z.of_nat lhs)
    | _, _ => false
    end.
Proof. by rewrite /satisfies_constraint1 common_constraint_rhs_value. Qed.

Lemma common_constraint_matches_sem_width solver_map sem_map value e ty width id lhs :
  scalar_maps_related solver_map sem_map ->
  valuation_matches_sem_map value sem_map ->
  Semantics.type_of_expr None sem_map (sem_expr e) = Some ty ->
  sem_numeric_width ty = Some width ->
  solver_width value id = Some lhs ->
  exists rhs, common_rhs solver_map e = Some rhs /\
    (satisfies_constraint1 value (common_constraint id rhs) = true <->
     (width <= lhs)%coq_nat).
Proof.
  move=> Hmaps Hvalue Htype Hwidth Hlhs.
  have [rhs [Hrhs Heval]] :=
    common_rhs_matches_sem_expr Hmaps Hvalue Htype Hwidth.
  exists rhs; split; first exact Hrhs.
  rewrite common_constraint_satisfaction Hlhs Heval.
  by rewrite Z.leb_le Nat2Z.inj_le.
Qed.

Lemma common_constraint_matches_sem_components solver_map sem_map value e ty width
    id dest kind lhs rhs :
  scalar_maps_related solver_map sem_map ->
  valuation_matches_sem_map value sem_map ->
  SemSyntax.VM.find id sem_map = Some (dest, kind) ->
  (dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit lhs) \/
   dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit lhs)) ->
  Semantics.type_of_expr None sem_map (sem_expr e) = Some ty ->
  sem_numeric_width ty = Some width ->
  common_rhs solver_map e = Some rhs ->
  (satisfies_constraint1 value (common_constraint id rhs) = true <->
   (width <= lhs)%coq_nat).
Proof.
  move=> Hmaps Hvalue Hdest Himplicit Hexpr Hwidth Hrhs.
  have Hlhs := Hvalue id dest kind lhs Hdest Himplicit.
  have [rhs' [Hrhs' Hbound]] :=
    common_constraint_matches_sem_width Hmaps Hvalue Hexpr Hwidth Hlhs.
  rewrite Hrhs in Hrhs'. inversion Hrhs'; subst rhs'. exact Hbound.
Qed.

Definition semantic_operands (sem_map : sem_component_map) (id : var)
    (e : common_expr) : Prop :=
  exists dest kind lhs ty width,
    SemSyntax.VM.find id sem_map = Some (dest, kind) /\
    (dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit lhs) \/
     dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit lhs)) /\
    Semantics.type_of_expr None sem_map (sem_expr e) = Some ty /\
    sem_numeric_width ty = Some width.

Definition semantic_width_bound (sem_map : sem_component_map) (id : var)
    (e : common_expr) : Prop :=
  exists dest kind lhs ty width,
    SemSyntax.VM.find id sem_map = Some (dest, kind) /\
    (dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit lhs) \/
     dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit lhs)) /\
    Semantics.type_of_expr None sem_map (sem_expr e) = Some ty /\
    sem_numeric_width ty = Some width /\
    (width <= lhs)%coq_nat.

Lemma common_constraint_semantic_bound solver_map sem_map value id e rhs :
  scalar_maps_related solver_map sem_map ->
  valuation_matches_sem_map value sem_map ->
  semantic_operands sem_map id e ->
  common_rhs solver_map e = Some rhs ->
  (satisfies_constraint1 value (common_constraint id rhs) = true <->
   semantic_width_bound sem_map id e).
Proof.
  move=> Hmaps Hvalue [dest [kind [lhs [ty [width [Hdest [Himplicit [Hexpr Hwidth]]]]]]]] Hrhs.
  have Hiff := common_constraint_matches_sem_components Hmaps Hvalue Hdest
    Himplicit Hexpr Hwidth Hrhs.
  rewrite Hiff.
  split.
  - move=> Hle. exists dest, kind, lhs, ty, width. by repeat split.
  - move=> [dest' [kind' [lhs' [ty' [width'
      [Hdest' [Himplicit' [Hexpr' [Hwidth' Hle]]]]]]]]].
    rewrite Hdest in Hdest'. inversion Hdest'; subst dest' kind'.
    rewrite Hexpr in Hexpr'. inversion Hexpr'; subst ty'.
    rewrite Hwidth in Hwidth'. inversion Hwidth'; subst width'.
    destruct Himplicit as [Himplicit|Himplicit];
      destruct Himplicit' as [Himplicit'|Himplicit'];
      rewrite Himplicit in Himplicit'; inversion Himplicit'; subst lhs'; exact Hle.
Qed.

Definition add_common_constraint (id : var) (rhs : regular_rhs)
    (cmap : SolverSyntax.PVM.t (list Constraint1)) :=
  let pv := (id, N0) in
  let prior := match SolverSyntax.PVM.find pv cmap with
               | Some cs => cs
               | None => [::]
               end in
  SolverSyntax.PVM.add pv (common_constraint id rhs :: prior) cmap.

Definition constraint_map_satisfied (value : Valuation)
    (cmap : SolverSyntax.PVM.t (list Constraint1)) : Prop :=
  forall pv cs c, SolverSyntax.PVM.find pv cmap = Some cs ->
    List.In c cs -> satisfies_constraint1 value c = true.

Lemma flattened_constraint_member (entries : list (SolverSyntax.ProdVar.t * list Constraint1))
    (c : Constraint1) :
  List.In c (List.concat (snd (List.split entries))) <->
  exists pv cs, List.In (pv, cs) entries /\ List.In c cs.
Proof.
  elim: entries => [|[pv cs] entries IH] /=.
  - split; first by case. by move=> [x [ys [[] _]]].
  - case Hsplit: (List.split entries) => [keys lists] /=.
    rewrite List.in_app_iff.
    have Htail : List.In c (List.concat lists) <->
        exists x ys, List.In (x, ys) entries /\ List.In c ys.
    { by rewrite Hsplit in IH. }
    rewrite Htail.
    split.
    + move=> [Hc|[x [ys [Hin Hc]]]].
      * exists pv, cs; split; first by left.
        exact Hc.
      * exists x, ys; split; first by right.
        exact Hc.
    + move=> [x [ys [[Heq|Hin] Hc]]].
      * inversion Heq; subst. by left.
      * right. exists x, ys. by split.
Qed.

Lemma constraint_map_satisfied_flattened value cmap :
  constraint_map_satisfied value cmap <->
  List.forallb (satisfies_constraint1 value)
    (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true.
Proof.
  rewrite /constraint_map_satisfied.
  split.
  - move=> H; apply List.forallb_forall => c.
    move/flattened_constraint_member => [pv [cs [Hin Hc]]].
    apply: (H pv cs c _ Hc).
    by apply find_in_elements.
  - move/List.forallb_forall=> H pv cs c Hfind Hc.
    apply: H.
    apply/flattened_constraint_member.
    exists pv, cs; split; last exact Hc.
    by apply find_in_elements.
Qed.

Lemma add_common_constraint_satisfied value cmap id rhs :
  constraint_map_satisfied value (add_common_constraint id rhs cmap) <->
  satisfies_constraint1 value (common_constraint id rhs) = true /\
  constraint_map_satisfied value cmap.
Proof.
  rewrite /constraint_map_satisfied /add_common_constraint.
  set pv := (id, N0).
  case Hprior: (SolverSyntax.PVM.find pv cmap) => [prior|].
  - split.
    + move=> H; split.
      * apply: (H pv (common_constraint id rhs :: prior)).
        -- by rewrite SolverSyntax.PVM.Lemmas.F.add_eq_o.
        -- by left.
      * move=> x cs c Hfind Hin.
        case Hx: (x == pv).
        -- move/eqP: Hx => Hx; subst x. rewrite Hprior in Hfind.
           inversion Hfind; subst cs.
           apply: (H pv (common_constraint id rhs :: prior)).
           ++ by rewrite SolverSyntax.PVM.Lemmas.F.add_eq_o.
           ++ by right.
        -- apply: (H x cs c _ Hin).
           rewrite SolverSyntax.PVM.Lemmas.F.add_neq_o.
           ++ exact Hfind.
           ++ move=> Heq. apply eq_from_prodvar_eq in Heq.
              subst x. by rewrite eqxx in Hx.
    + move=> [Hhead Htail] x cs c Hfind Hin.
      case Hx: (x == pv).
      * move/eqP: Hx => Hx; subst x.
        rewrite SolverSyntax.PVM.Lemmas.F.add_eq_o in Hfind; last by split; rewrite eqxx.
        inversion Hfind; subst cs.
        case: Hin => [<-|Hin]; first exact Hhead.
        exact: (Htail pv prior c Hprior Hin).
      * rewrite SolverSyntax.PVM.Lemmas.F.add_neq_o in Hfind.
        -- exact: (Htail x cs c Hfind Hin).
        -- move=> Heq. apply eq_from_prodvar_eq in Heq.
           subst x. by rewrite eqxx in Hx.
  - split.
    + move=> H; split.
      * apply: (H pv [:: common_constraint id rhs]).
        -- by rewrite SolverSyntax.PVM.Lemmas.F.add_eq_o.
        -- by left.
      * move=> x cs c Hfind Hin.
        case Hx: (x == pv).
        -- move/eqP: Hx => Hx; subst x. by rewrite Hprior in Hfind.
        -- apply: (H x cs c _ Hin).
           rewrite SolverSyntax.PVM.Lemmas.F.add_neq_o.
           ++ exact Hfind.
           ++ move=> Heq. apply eq_from_prodvar_eq in Heq.
              subst x. by rewrite eqxx in Hx.
    + move=> [Hhead Htail] x cs c Hfind Hin.
      case Hx: (x == pv).
      * move/eqP: Hx => Hx; subst x.
        rewrite SolverSyntax.PVM.Lemmas.F.add_eq_o in Hfind; last by split; rewrite eqxx.
        inversion Hfind; subst cs.
        by case: Hin => [<-|[]].
      * rewrite SolverSyntax.PVM.Lemmas.F.add_neq_o in Hfind.
        -- exact: (Htail x cs c Hfind Hin).
        -- move=> Heq. apply eq_from_prodvar_eq in Heq.
           subst x. by rewrite eqxx in Hx.
Qed.

Lemma extract_common_connect_implicit tmap cmap extra mins id value gt orient rhs :
  (gt = Env.Fuint_implicit 0 \/ gt = Env.Fsint_implicit 0) ->
  SolverSyntax.VM.find id tmap = Some (HiEnv.Gtyp gt, orient) ->
  common_rhs tmap value = Some rhs ->
  extract_constraint (solver_stmt (CConnect id value)) tmap cmap extra mins =
    Some (add_common_constraint id rhs cmap, extra, mins).
Proof.
  move=> [->|->] Hfind Hrhs;
    rewrite /solver_stmt /extract_constraint /= /HiFirrtl.ref2pv /= Hfind
      (extract_common_expr _ value) Hrhs /= /add_common_constraint /common_constraint /=;
    by case: (SolverSyntax.PVM.find (id, N0) cmap).
Qed.

Lemma extract_common_reg_implicit tmap cmap extra mins id ty clock trigger value rhs :
  (ty = UIntImplicit \/ ty = SIntImplicit) ->
  common_rhs tmap value = Some rhs ->
  extract_constraint (solver_stmt (CReg id ty clock (CReset trigger value)))
    tmap cmap extra mins =
    Some (add_common_constraint id rhs cmap, extra, mins).
Proof.
  move=> [->|->] Hrhs;
    rewrite /solver_stmt /extract_constraint /solver_type /solver_reset /=
      (extract_common_expr _ value) Hrhs /= /add_common_constraint /common_constraint /=;
    by case: (SolverSyntax.PVM.find (id, N0) cmap).
Qed.

Lemma extract_common_reg_no_reset tmap cmap extra mins id ty clock :
  extract_constraint (solver_stmt (CReg id ty clock CNoReset))
    tmap cmap extra mins = Some (cmap, extra, mins).
Proof. by case: ty. Qed.

Lemma extract_common_connect_explicit tmap cmap extra mins id value gt orient :
  (exists w, gt = Env.Fuint w \/ gt = Env.Fsint w) ->
  SolverSyntax.VM.find id tmap = Some (HiEnv.Gtyp gt, orient) ->
  extract_constraint (solver_stmt (CConnect id value)) tmap cmap extra mins =
    Some (cmap, extra, mins).
Proof.
  move=> [w [->|->]] Hfind;
    by rewrite /solver_stmt /extract_constraint /= Hfind.
Qed.

Definition solver_map_is_scalar (tmap : solver_type_map) : Prop :=
  forall id ty orient,
    SolverSyntax.VM.find id tmap = Some (ty, orient) ->
    exists gt, ty = HiEnv.Gtyp gt.

Definition common_extract_step (tmap : solver_type_map)
    (cmap : SolverSyntax.PVM.t (list Constraint1)) (s : common_stmt)
    : option (SolverSyntax.PVM.t (list Constraint1)) :=
  match s with
  | CSkip | CWire _ _ => Some cmap
  | CReg id ty _ rst =>
      match ty, rst with
      | UIntImplicit, CReset _ value
      | SIntImplicit, CReset _ value =>
          option_map (fun rhs => add_common_constraint id rhs cmap) (common_rhs tmap value)
      | _, _ => Some cmap
      end
  | CConnect id value =>
      match SolverSyntax.VM.find id tmap with
      | Some (HiEnv.Gtyp (Env.Fuint_implicit _), _)
      | Some (HiEnv.Gtyp (Env.Fsint_implicit _), _) =>
          option_map (fun rhs => add_common_constraint id rhs cmap) (common_rhs tmap value)
      | Some (HiEnv.Gtyp _, _) => Some cmap
      | _ => None
      end
  end.

Definition common_step_satisfied (value : Valuation) (tmap : solver_type_map)
    (s : common_stmt) : Prop :=
  match s with
  | CSkip | CWire _ _ => True
  | CReg id ty _ rst =>
      match ty, rst with
      | UIntImplicit, CReset _ e
      | SIntImplicit, CReset _ e =>
          match common_rhs tmap e with
          | Some rhs => satisfies_constraint1 value (common_constraint id rhs) = true
          | None => False
          end
      | _, _ => True
      end
  | CConnect id e =>
      match SolverSyntax.VM.find id tmap with
      | Some (HiEnv.Gtyp (Env.Fuint_implicit _), _)
      | Some (HiEnv.Gtyp (Env.Fsint_implicit _), _) =>
          match common_rhs tmap e with
          | Some rhs => satisfies_constraint1 value (common_constraint id rhs) = true
          | None => False
          end
      | Some (HiEnv.Gtyp _, _) => True
      | _ => False
      end
  end.

Definition common_step_operand (tmap : solver_type_map) (s : common_stmt)
    : option (var * common_expr) :=
  match s with
  | CReg id ty _ (CReset _ e) =>
      match ty with
      | UIntImplicit | SIntImplicit => Some (id, e)
      | _ => None
      end
  | CConnect id e =>
      match SolverSyntax.VM.find id tmap with
      | Some (HiEnv.Gtyp (Env.Fuint_implicit _), _)
      | Some (HiEnv.Gtyp (Env.Fsint_implicit _), _) => Some (id, e)
      | _ => None
      end
  | _ => None
  end.

Definition common_step_semantic_ready sem_map tmap s : Prop :=
  match common_step_operand tmap s with
  | Some (id, e) => semantic_operands sem_map id e
  | None => True
  end.

Definition common_step_semantic_bound sem_map tmap s : Prop :=
  match common_step_operand tmap s with
  | Some (id, e) => semantic_width_bound sem_map id e
  | None => True
  end.

Lemma common_step_satisfied_semantic_bound solver_map sem_map value s cmap next :
  scalar_maps_related solver_map sem_map ->
  valuation_matches_sem_map value sem_map ->
  common_step_semantic_ready sem_map solver_map s ->
  common_extract_step solver_map cmap s = Some next ->
  (common_step_satisfied value solver_map s <->
   common_step_semantic_bound sem_map solver_map s).
Proof.
  move=> Hmaps Hvalue.
  rewrite /common_step_semantic_ready /common_step_semantic_bound
    /common_step_operand /common_step_satisfied /common_extract_step.
  case: s => [|id ty|id ty clock rst|id e] /=.
  - by move=> _ _.
  - by move=> _ _.
  - case: ty rst => [| |w|w] [|trigger e] //=;
      try (by move=> _ _).
    + case Hrhs: (common_rhs solver_map e) => [rhs|] //=.
      move=> Hready _. exact: (common_constraint_semantic_bound Hmaps Hvalue Hready Hrhs).
    + case Hrhs: (common_rhs solver_map e) => [rhs|] //=.
      move=> Hready _. exact: (common_constraint_semantic_bound Hmaps Hvalue Hready Hrhs).
  - case: (SolverSyntax.VM.find id solver_map) => [[ty orient]|] //=.
    case: ty => [gt|elt n|fields] //=.
    case: gt => [w|w|w|w| | |] //=;
      try (by move=> _ _).
    + case Hrhs: (common_rhs solver_map e) => [rhs|] //=.
      move=> Hready _. exact: (common_constraint_semantic_bound Hmaps Hvalue Hready Hrhs).
    + case Hrhs: (common_rhs solver_map e) => [rhs|] //=.
      move=> Hready _. exact: (common_constraint_semantic_bound Hmaps Hvalue Hready Hrhs).
Qed.

Lemma common_extract_step_satisfied value tmap cmap s next :
  common_extract_step tmap cmap s = Some next ->
  (constraint_map_satisfied value next <->
   common_step_satisfied value tmap s /\ constraint_map_satisfied value cmap).
Proof.
  case: s => [|id ty|id ty clock rst|id e] /=.
  - by move=> [<-]; split; [move=> H; split|case]; auto.
  - by move=> [<-]; split; [move=> H; split|case]; auto.
  - case: ty rst => [| |w|w] [|trigger e] //=;
      try (move=> H; inversion H; subst; tauto);
      case: (common_rhs tmap e) => [rhs|] //=;
      by move=> [<-]; rewrite add_common_constraint_satisfied.
  - case: (SolverSyntax.VM.find id tmap) => [[ty orient]|] //=.
    case: ty => [gt|elt n|fields] //=.
    case: gt => [w|w|w|w| | |] //=;
      try (move=> H; inversion H; subst; tauto);
      case: (common_rhs tmap e) => [rhs|] //=;
      by move=> [<-]; rewrite add_common_constraint_satisfied.
Qed.

Lemma extract_common_step tmap cmap extra mins s :
  solver_map_is_scalar tmap ->
  extract_constraint (solver_stmt s) tmap cmap extra mins =
    option_map (fun next => (next, extra, mins)) (common_extract_step tmap cmap s).
Proof.
  move=> Hscalar.
  case: s => [|id ty|id ty clock rst|id value] //=.
  - case: ty rst => [| |w|w] [|trigger value] //=;
      rewrite (extract_common_expr _ value);
      case: (common_rhs tmap value) => [rhs|] //=;
      rewrite /add_common_constraint /common_constraint /=;
      by case: (SolverSyntax.PVM.find (id, N0) cmap).
  - case Hfind: (SolverSyntax.VM.find id tmap) => [[ty orient]|] //=.
    have [gt ->] := Hscalar _ _ _ Hfind.
    case: gt Hfind => [w|w|w|w| | |] Hfind //=;
      rewrite (extract_common_expr _ value);
      case: (common_rhs tmap value) => [rhs|] //=;
      rewrite /add_common_constraint /common_constraint /=;
      by case: (SolverSyntax.PVM.find (id, N0) cmap).
Qed.

Fixpoint common_extract_steps (tmap : solver_type_map)
    (cmap : SolverSyntax.PVM.t (list Constraint1)) (ss : seq common_stmt)
    : option (SolverSyntax.PVM.t (list Constraint1)) :=
  match ss with
  | [::] => Some cmap
  | s :: rest =>
      match common_extract_step tmap cmap s with
      | Some next => common_extract_steps tmap next rest
      | None => None
      end
  end.

Lemma common_extract_steps_satisfied value tmap ss cmap result :
  common_extract_steps tmap cmap ss = Some result ->
  (constraint_map_satisfied value result <->
   List.Forall (common_step_satisfied value tmap) ss /\
   constraint_map_satisfied value cmap).
Proof.
  move: cmap; elim: ss => [|s ss IH] cmap /=.
  - move=> [<-]. split.
    + by move=> H; split; [constructor|].
    + by case.
  - case Hstep: (common_extract_step tmap cmap s) => [next|] //=.
    move=> Hsteps.
    rewrite (IH next Hsteps) (common_extract_step_satisfied value Hstep).
    split.
    + move=> [Hrest [Hfirst Hcmap]].
      split; last exact Hcmap. by constructor.
    + move=> [Hall Hcmap].
      inversion Hall; subst. by split; first assumption; split.
Qed.

Lemma common_extract_steps_semantic_bounds solver_map sem_map value ss cmap result :
  scalar_maps_related solver_map sem_map ->
  valuation_matches_sem_map value sem_map ->
  List.Forall (common_step_semantic_ready sem_map solver_map) ss ->
  common_extract_steps solver_map cmap ss = Some result ->
  (List.Forall (common_step_satisfied value solver_map) ss <->
   List.Forall (common_step_semantic_bound sem_map solver_map) ss).
Proof.
  move=> Hmaps Hvalue.
  move: cmap; elim: ss => [|s ss IH] cmap /= Hready.
  - by split; constructor.
  - inversion Hready as [|? ? Hfirst Hrest]; subst.
    case Hstep: (common_extract_step solver_map cmap s) => [next|] //=.
    move=> Hsteps.
    have Hiff := common_step_satisfied_semantic_bound Hmaps Hvalue Hfirst Hstep.
    have Htail := IH next Hrest Hsteps.
    split.
    + move=> H; inversion H; subst. constructor.
      * by apply Hiff.
      * by apply Htail.
    + move=> H; inversion H; subst. constructor.
      * by apply Hiff.
      * by apply Htail.
Qed.

Lemma extract_common_steps tmap ss cmap extra mins :
  solver_map_is_scalar tmap ->
  extract_constraints (solver_stmts ss) tmap cmap extra mins =
    option_map (fun next => (next, extra, mins))
      (common_extract_steps tmap cmap ss).
Proof.
  move=> Hscalar.
  move: cmap; elim: ss => [|s rest IH] cmap //=.
  rewrite (extract_common_step cmap extra mins s Hscalar).
  case: (common_extract_step tmap cmap s) => [next|] //=.
Qed.

Fixpoint solver_append (ss tail : SolverSyntax.HiF.hfstmt_seq)
    : SolverSyntax.HiF.hfstmt_seq :=
  match ss with
  | HiFirrtl.Qnil => tail
  | HiFirrtl.Qcons s rest => HiFirrtl.Qcons s (solver_append rest tail)
  end.

Lemma solver_stmts_cat a b :
  solver_stmts (a ++ b) = solver_append (solver_stmts a) (solver_stmts b).
Proof. by elim: a => [|s a IH] //=; rewrite IH. Qed.

Lemma solver_append_assoc a b c :
  solver_append (solver_append a b) c = solver_append a (solver_append b c).
Proof. by elim: a => [|s a IH] //=; rewrite IH. Qed.

Lemma solver_append_nil a :
  solver_append a (HiFirrtl.Qnil VarOrder.T) = a.
Proof. by elim: a => [|s a IH] //=; rewrite IH. Qed.

Lemma expand_common_stmts ss tail conditions :
  expandwhens (solver_stmts ss) (tail, conditions) =
    (solver_append (solver_stmts (rev ss)) tail, conditions).
Proof.
  move: tail; elim: ss => [|s ss IH] tail //=.
  case: s => [|id ty|id ty clock rst|id value] /=;
    by rewrite IH rev_cons -cats1 solver_stmts_cat /= solver_append_assoc /=.
Qed.

Lemma extract_common_module tmap m :
  solver_map_is_scalar tmap ->
  extract_constraint_m (solver_module m) tmap =
    option_map (fun next => (next, [::], [::]))
      (common_extract_steps tmap (SolverSyntax.PVM.empty _) (rev (common_stmts m))).
Proof.
  move=> Hscalar.
  rewrite /extract_constraint_m /solver_module (expand_common_stmts _ _ _)
    solver_append_nil /=.
  by rewrite (extract_common_steps _ _ _ _ Hscalar); case: (common_extract_steps _ _ _).
Qed.

Lemma extract_common_circuit tmap m circuit_name :
  solver_map_is_scalar tmap ->
  extract_constraints_c (solver_circuit circuit_name m) tmap =
    option_map (fun next => ([:: next], [::]))
      (common_extract_steps tmap (SolverSyntax.PVM.empty _) (rev (common_stmts m))).
Proof.
  move=> Hscalar.
  rewrite /extract_constraints_c /solver_circuit
    (extract_common_module m Hscalar).
  by case: (common_extract_steps _ _ _) => [result|].
Qed.

Lemma extract_common_circuit_satisfied value tmap m circuit_name cmap :
  solver_map_is_scalar tmap ->
  extract_constraints_c (solver_circuit circuit_name m) tmap =
    Some ([:: cmap], [::]) ->
  (constraint_map_satisfied value cmap <->
   List.Forall (common_step_satisfied value tmap) (rev (common_stmts m))).
Proof.
  move=> Hscalar Hextract.
  rewrite (extract_common_circuit m circuit_name Hscalar) in Hextract.
  case Hsteps: (common_extract_steps tmap (SolverSyntax.PVM.empty _)
                  (rev (common_stmts m))) => [result|] //= in Hextract.
  inversion Hextract; subst result.
  rewrite (common_extract_steps_satisfied value Hsteps).
  have Hempty : constraint_map_satisfied value (SolverSyntax.PVM.empty _) .
  { move=> pv cs c Hfind; by rewrite SolverSyntax.PVM.Lemmas.F.empty_o in Hfind. }
  by split; [case|move=> H; split].
Qed.

Theorem extracted_constraints_match_semantic_bounds
    value solver_map sem_map m circuit_name cmap :
  scalar_maps_related solver_map sem_map ->
  valuation_matches_sem_map value sem_map ->
  List.Forall (common_step_semantic_ready sem_map solver_map)
    (rev (common_stmts m)) ->
  extract_constraints_c (solver_circuit circuit_name m) solver_map =
    Some ([:: cmap], [::]) ->
  (List.forallb (satisfies_constraint1 value)
     (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true <->
   List.Forall (common_step_semantic_bound sem_map solver_map)
     (rev (common_stmts m))).
Proof.
  move=> Hmaps Hvalue Hready Hextract.
  have Hscalar := scalar_maps_related_is_scalar Hmaps.
  have Hsat := extract_common_circuit_satisfied value Hscalar Hextract.
  have Hsteps : common_extract_steps solver_map (SolverSyntax.PVM.empty _)
      (rev (common_stmts m)) = Some cmap.
  { rewrite (extract_common_circuit m circuit_name Hscalar) in Hextract.
    case Hresult: (common_extract_steps _ _ _) => [result|] //= in Hextract.
    by inversion Hextract; subst. }
  rewrite -constraint_map_satisfied_flattened Hsat.
  exact: (common_extract_steps_semantic_bounds Hmaps Hvalue Hready Hsteps).
Qed.

Corollary fixed_point_constraints_match_semantic_bounds
    value solver_map result sem_map m circuit_name cmap n :
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  SemSyntax.VM.find (common_module_name m) result = Some sem_map ->
  scalar_maps_related solver_map sem_map ->
  valuation_matches_sem_map value sem_map ->
  List.Forall (common_step_semantic_ready sem_map solver_map)
    (rev (common_stmts m)) ->
  extract_constraints_c (solver_circuit circuit_name m) solver_map =
    Some ([:: cmap], [::]) ->
  (List.forallb (satisfies_constraint1 value)
     (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true <->
   List.Forall (common_step_semantic_bound sem_map solver_map)
     (rev (common_stmts m))).
Proof.
  move=> _ _ Hmaps Hvalue Hready Hextract.
  exact: (extracted_constraints_match_semantic_bounds Hmaps Hvalue Hready Hextract).
Qed.

Inductive scalar_width_growth :
    HiEnv_with_implicit_widths.ftype -> HiEnv_with_implicit_widths.ftype -> Prop :=
| grows_uint_implicit a b :
    (a <= b)%coq_nat ->
    scalar_width_growth
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit a))
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit b))
| grows_sint_implicit a b :
    (a <= b)%coq_nat ->
    scalar_width_growth
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit a))
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit b))
| grows_uint_explicit w :
    scalar_width_growth
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint w))
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint w))
| grows_sint_explicit w :
    scalar_width_growth
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint w))
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint w))
| grows_clock :
    scalar_width_growth
      (HiEnv_with_implicit_widths.Gtyp Env_with_implicit_widths.Fclock)
      (HiEnv_with_implicit_widths.Gtyp Env_with_implicit_widths.Fclock).

Definition semantic_map_growth (before after : sem_component_map) : Prop :=
  forall id,
    match SemSyntax.VM.find id before, SemSyntax.VM.find id after with
    | Some (old, kind), Some (new, kind') =>
        kind = kind' /\ scalar_width_growth old new
    | None, None => True
    | _, _ => False
    end.

Lemma scalar_growth_refl st mt :
  scalar_type_relation st mt -> scalar_width_growth mt mt.
Proof.
  case=> [sw mw|sw mw|w|w|]; constructor; auto.
Qed.

Lemma scalar_growth_related st mt mt' :
  scalar_type_relation st mt -> scalar_width_growth mt mt' ->
  scalar_type_relation st mt'.
Proof. move=> Hrel Hgrow; inversion Hrel; subst; inversion Hgrow; subst; constructor. Qed.

Lemma scalar_growth_trans t1 t2 t3 :
  scalar_width_growth t1 t2 -> scalar_width_growth t2 t3 ->
  scalar_width_growth t1 t3.
Proof.
  move=> H1 H2; inversion H1; subst; inversion H2; subst; constructor;
    eauto using Nat.le_trans.
Qed.

Lemma scalar_growth_more_concrete old new :
  scalar_width_growth old new -> Semantics.more_concrete_type old new.
Proof.
  move=> H; inversion H; subst; simpl; try by rewrite eqxx.
  all: try by apply/leP.
  all: destruct a; simpl; try by apply/leP.
  all: destruct a; simpl; by apply/leP.
Qed.

Lemma semantic_growth_more_concrete before after :
  semantic_map_growth before after ->
  Semantics.tmap_is_more_concrete before after.
Proof.
  move=> H id; move: (H id).
  rewrite /Semantics.tmap_is_more_concrete.
  case: (SemSyntax.VM.find id before) => [[old kind]|];
    case: (SemSyntax.VM.find id after) => [[new kind']|] //=.
  move=> [-> Hgrowth].
  by rewrite eqxx andbT; exact: scalar_growth_more_concrete Hgrowth.
Qed.

Lemma semantic_map_growth_refl solver_map sem_map :
  scalar_maps_related solver_map sem_map -> semantic_map_growth sem_map sem_map.
Proof.
  move=> Hmaps id; move: (Hmaps id).
  case: (SolverSyntax.VM.find id solver_map) => [[st orient]|];
    case: (SemSyntax.VM.find id sem_map) => [[mt kind]|] //=.
  by move=> Hty; split; first reflexivity; exact: scalar_growth_refl Hty.
Qed.

Lemma semantic_map_growth_trans a b c :
  semantic_map_growth a b -> semantic_map_growth b c -> semantic_map_growth a c.
Proof.
  move=> Hab Hbc id; move: (Hab id) (Hbc id).
  case: (SemSyntax.VM.find id a) => [[ta ka]|];
    case: (SemSyntax.VM.find id b) => [[tb kb]|];
    case: (SemSyntax.VM.find id c) => [[tc kc]|] //=.
  move=> [-> H1] [-> H2]; split; first reflexivity.
  exact: (scalar_growth_trans H1 H2).
Qed.

Lemma semantic_growth_preserves_related solver_map before after :
  scalar_maps_related solver_map before -> semantic_map_growth before after ->
  scalar_maps_related solver_map after.
Proof.
  move=> Hmaps Hgrowth id; move: (Hmaps id) (Hgrowth id).
  case: (SolverSyntax.VM.find id solver_map) => [[st orient]|];
    case: (SemSyntax.VM.find id before) => [[old kind]|];
    case: (SemSyntax.VM.find id after) => [[new kind']|] //=.
  move=> Hty [_ Hgrow]. exact: (scalar_growth_related Hty Hgrow).
Qed.

Lemma semantic_map_growth_add solver_map sem_map id old new kind :
  scalar_maps_related solver_map sem_map ->
  SemSyntax.VM.find id sem_map = Some (old, kind) ->
  scalar_width_growth old new ->
  semantic_map_growth sem_map (SemSyntax.VM.add id (new, kind) sem_map).
Proof.
  move=> Hmaps Hfind Hgrow x.
  case Hx: (x == id).
  - move/eqP: Hx => ->.
    by rewrite Hfind SemSyntax.VM.Lemmas.find_add_eq // eqxx.
  - have Hneq : ~ (x == id) by move/negP: Hx.
    rewrite (SemSyntax.VM.Lemmas.find_add_neq Hneq).
    exact: (semantic_map_growth_refl Hmaps x).
Qed.

Lemma common_expr_is_semantic_scalar solver_map sem_map e ty :
  scalar_maps_related solver_map sem_map ->
  Semantics.type_of_expr None sem_map (sem_expr e) = Some ty ->
  exists st, scalar_type_relation st ty.
Proof.
  move=> Hmaps.
  case: e => [id|w bits|w bits] /=.
  - rewrite /Semantics.type_of_expr /=.
    case Hsem: (SemSyntax.VM.find id sem_map) => [[mt kind]|] //=.
    move=> [<-]. move: (Hmaps id); rewrite Hsem.
    case: (SolverSyntax.VM.find id solver_map) => [[st orient]|] //= Hrel.
    by exists st.
  - rewrite /Semantics.type_of_expr /=.
    case: (w < size bits) => //= H; inversion H; subst ty.
    by exists (HiEnv.Gtyp (Env.Fuint w)); constructor.
  - rewrite /Semantics.type_of_expr /=.
    case: (w < size bits) => //= H; inversion H; subst ty.
    by exists (HiEnv.Gtyp (Env.Fsint w)); constructor.
Qed.

Lemma scalar_unify_growth st sr tw tr neww newr :
  scalar_type_relation st tw ->
  scalar_type_relation sr tr ->
  Semantics.unify_width HiEnv_with_implicit_widths.Nflip tw tr = Some (neww, newr) ->
  scalar_width_growth tw neww /\ scalar_width_growth tr newr.
Proof.
  move=> Htw Htr.
  inversion Htw; subst; inversion Htr; subst; simpl.
  all: repeat match goal with
       | |- context [match ?n with 0 => _ | S _ => _ end] => destruct n
       end.
  all: simpl; try (move=> H; discriminate).
  all: move=> H; inversion H; subst; split; constructor; auto.
  all: apply/leP; exact: leq_maxl.
Qed.

Lemma related_semantic_lookup solver_map sem_map id ty kind :
  scalar_maps_related solver_map sem_map ->
  SemSyntax.VM.find id sem_map = Some (ty, kind) ->
  exists st, scalar_type_relation st ty.
Proof.
  move=> Hmaps Hfind.
  move: (Hmaps id); rewrite Hfind.
  case: (SolverSyntax.VM.find id solver_map) => [[st orient]|] //= Hty.
  by exists st.
Qed.

Lemma common_reg_width_growth solver_map sem_map result id ty clock rst :
  scalar_maps_related solver_map sem_map ->
  Semantics.width_iter_one sem_map (sem_stmt (CReg id ty clock rst)) = Some result ->
  semantic_map_growth sem_map result.
Proof.
  move=> Hmaps.
  case: rst => [|trigger e] /=.
  - move=> [<-]. exact: semantic_map_growth_refl Hmaps.
  - case Hreg: (SemSyntax.VM.find id sem_map) => [[reg kind]|] //=.
    case: kind Hreg => //= Hreg.
    case Hexpr: (Semantics.type_of_expr None sem_map (sem_expr e)) => [value|] //=.
    case: (HiEnv_with_implicit_widths.is_passive reg &&
           HiEnv_with_implicit_widths.is_passive value) => //=.
    case Hunify: (Semantics.unify_width HiEnv_with_implicit_widths.Nflip reg value)
      => [[newreg newvalue]|] //=.
    move=> Hresult; inversion Hresult; subst result.
    have [st Hst] := related_semantic_lookup Hmaps Hreg.
    have [sr Hsr] := common_expr_is_semantic_scalar Hmaps Hexpr.
    have [Hgrow _] := scalar_unify_growth Hst Hsr Hunify.
    exact: (semantic_map_growth_add Hmaps Hreg Hgrow).
Qed.

Lemma semantic_map_growth_add_two solver_map sem_map id src old new oldsrc newsrc kind ksrc :
  scalar_maps_related solver_map sem_map ->
  SemSyntax.VM.find id sem_map = Some (old, kind) ->
  SemSyntax.VM.find src sem_map = Some (oldsrc, ksrc) ->
  scalar_width_growth old new ->
  scalar_width_growth oldsrc newsrc ->
  semantic_map_growth sem_map
    (SemSyntax.VM.add src (newsrc, ksrc)
      (SemSyntax.VM.add id (new, kind) sem_map)).
Proof.
  move=> Hmaps Hdst Hsrc Hnew Hnewsrc x.
  case Hxs: (x == src).
  - move/eqP: Hxs => ->.
    by rewrite Hsrc SemSyntax.VM.Lemmas.find_add_eq // eqxx.
  - have Hneq : ~ (x == src) by move/negP: Hxs.
    rewrite (SemSyntax.VM.Lemmas.find_add_neq Hneq).
    exact: (semantic_map_growth_add Hmaps Hdst Hnew x).
Qed.

Lemma common_ref_connect_width_growth solver_map sem_map result id src :
  scalar_maps_related solver_map sem_map ->
  Semantics.width_iter_one sem_map (sem_stmt (CConnect id (CRef src))) = Some result ->
  semantic_map_growth sem_map result.
Proof.
  move=> Hmaps.
  rewrite /=.
  case Hdst: (SemSyntax.VM.find id sem_map) => [[dst kd]|] //=.
  case Hsrc: (SemSyntax.VM.find src sem_map) => [[source ks]|] //=.
  case Hunify: (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dst source)
    => [[newdst newsrc]|] //=.
  have [st Hst] := related_semantic_lookup Hmaps Hdst.
  have [sr Hsr] := related_semantic_lookup Hmaps Hsrc.
  have [Hgrow Hgrow_src] := scalar_unify_growth Hst Hsr Hunify.
  case Hsame: (src == id).
  - move/eqP: Hsame => Heq; subst src.
    rewrite Hdst in Hsrc. inversion Hsrc; subst source ks.
    rewrite SemSyntax.VM.Lemmas.find_add_eq //=.
    move=> Hresult; inversion Hresult; subst result.
    exact: (semantic_map_growth_add_two Hmaps Hdst Hdst Hgrow Hgrow_src).
  - have Hneq : ~ (src == id) by move/negP: Hsame.
    rewrite (SemSyntax.VM.Lemmas.find_add_neq Hneq) Hsrc /=.
    move=> Hresult; inversion Hresult; subst result.
    exact: (semantic_map_growth_add_two Hmaps Hdst Hsrc Hgrow Hgrow_src).
Qed.

Lemma common_const_connect_width_growth solver_map sem_map result id e :
  scalar_maps_related solver_map sem_map ->
  (match e with CRef _ => False | _ => True end) ->
  Semantics.width_iter_one sem_map (sem_stmt (CConnect id e)) = Some result ->
  semantic_map_growth sem_map result.
Proof.
  move=> Hmaps Hconst.
  case: e Hconst => [src|w bits|w bits] //= _;
    rewrite /=;
    case Hdst: (SemSyntax.VM.find id sem_map) => [[dst kd]|] //=;
    rewrite /Semantics.type_of_expr /=;
    case Hvalid: (w < size bits) => //=.
  - case Hunify: (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dst
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint w)))
      => [[newdst newval]|] //=.
    move=> Hresult.
    inversion Hresult; subst result.
    have [st Hst] := related_semantic_lookup Hmaps Hdst.
    have Hsr : scalar_type_relation (HiEnv.Gtyp (Env.Fuint w))
        (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint w))
      by constructor.
    have [Hgrow _] := scalar_unify_growth Hst Hsr Hunify.
    exact: (semantic_map_growth_add Hmaps Hdst Hgrow).
  - case Hunify: (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dst
      (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint w)))
      => [[newdst newval]|] //=.
    move=> Hresult; inversion Hresult; subst result.
    have [st Hst] := related_semantic_lookup Hmaps Hdst.
    have Hsr : scalar_type_relation (HiEnv.Gtyp (Env.Fsint w))
        (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint w))
      by constructor.
    have [Hgrow _] := scalar_unify_growth Hst Hsr Hunify.
    exact: (semantic_map_growth_add Hmaps Hdst Hgrow).
Qed.

Lemma common_width_iter_one_growth solver_map sem_map result s :
  scalar_maps_related solver_map sem_map ->
  Semantics.width_iter_one sem_map (sem_stmt s) = Some result ->
  semantic_map_growth sem_map result.
Proof.
  move=> Hmaps.
  case: s => [|id ty|id ty clock rst|id e].
  - rewrite /=. move=> [<-]. exact: semantic_map_growth_refl Hmaps.
  - rewrite /=. move=> [<-]. exact: semantic_map_growth_refl Hmaps.
  - exact: common_reg_width_growth Hmaps.
  - case: e => [src|w bits|w bits].
    + exact: common_ref_connect_width_growth Hmaps.
    + move=> Hiter.
      apply: (@common_const_connect_width_growth solver_map sem_map result id (CUInt w bits)).
      * exact Hmaps.
      * exact I.
      * exact Hiter.
    + move=> Hiter.
      apply: (@common_const_connect_width_growth solver_map sem_map result id (CSInt w bits)).
      * exact Hmaps.
      * exact I.
      * exact Hiter.
Qed.

Lemma common_width_iter_growth solver_map sem_map result ss :
  scalar_maps_related solver_map sem_map ->
  Semantics.width_iter sem_map (sem_stmts ss) = Some result ->
  semantic_map_growth sem_map result.
Proof.
  move: sem_map.
  elim: ss => [|s ss IH] sem_map Hmaps /=.
  - move=> [<-]. exact: semantic_map_growth_refl Hmaps.
  - case Hstep: (Semantics.width_iter_one sem_map (sem_stmt s)) => [next|] //=.
    move=> Hrest.
    have Hgrowth := common_width_iter_one_growth Hmaps Hstep.
    have Hrelated := semantic_growth_preserves_related Hmaps Hgrowth.
    exact: (semantic_map_growth_trans Hgrowth (IH next Hrelated Hrest)).
Qed.

Lemma semantic_growth_sandwich before middle after :
  semantic_map_growth before middle ->
  semantic_map_growth middle after ->
  (forall id, SemSyntax.VM.find id before = SemSyntax.VM.find id after) ->
  forall id, SemSyntax.VM.find id before = SemSyntax.VM.find id middle.
Proof.
  move=> Hfirst Hlast Hequal.
  apply (proj1 (Semantics.tmap_equal_find_iff before middle)).
  apply (proj2 (Semantics.tmap_equal_iff_more_concrete before middle)).
  split; first exact: semantic_growth_more_concrete Hfirst.
  have Hconcrete := semantic_growth_more_concrete Hlast.
  move=> id.
  move: (Hconcrete id).
  rewrite /Semantics.tmap_is_more_concrete -(Hequal id).
  by [].
Qed.

Inductive common_stable_width_trace (anchor : sem_component_map) :
    sem_component_map -> seq common_stmt -> sem_component_map -> Prop :=
| stable_width_trace_nil current :
    (forall id, SemSyntax.VM.find id anchor = SemSyntax.VM.find id current) ->
    common_stable_width_trace anchor current [::] current
| stable_width_trace_cons current next final s ss :
    (forall id, SemSyntax.VM.find id anchor = SemSyntax.VM.find id current) ->
    Semantics.width_iter_one current (sem_stmt s) = Some next ->
    (forall id, SemSyntax.VM.find id current = SemSyntax.VM.find id next) ->
    common_stable_width_trace anchor next ss final ->
    common_stable_width_trace anchor current (s :: ss) final.

Theorem common_fixed_width_iter_stable_trace solver_map anchor current final ss :
  scalar_maps_related solver_map current ->
  (forall id, SemSyntax.VM.find id anchor = SemSyntax.VM.find id current) ->
  Semantics.width_iter current (sem_stmts ss) = Some final ->
  (forall id, SemSyntax.VM.find id current = SemSyntax.VM.find id final) ->
  common_stable_width_trace anchor current ss final.
Proof.
  move: current.
  elim: ss => [|s ss IH] current Hmaps Hanchor /=.
  - move=> [<-] _. exact: stable_width_trace_nil Hanchor.
  - case Hstep: (Semantics.width_iter_one current (sem_stmt s)) => [next|] //=.
    move=> Hrest Hfixed.
    have Hfirst := common_width_iter_one_growth Hmaps Hstep.
    have Hnextmaps := semantic_growth_preserves_related Hmaps Hfirst.
    have Hlast := common_width_iter_growth Hnextmaps Hrest.
    have Hstable := semantic_growth_sandwich Hfirst Hlast Hfixed.
    have Hanchornext : forall id,
        SemSyntax.VM.find id anchor = SemSyntax.VM.find id next.
    { move=> id. by rewrite Hanchor Hstable. }
    have Hnextfinal : forall id,
        SemSyntax.VM.find id next = SemSyntax.VM.find id final.
    { move=> id. by rewrite -(Hstable id) Hfixed. }
    apply: (stable_width_trace_cons Hanchor Hstep Hstable).
    exact: (IH next Hnextmaps Hanchornext Hrest Hnextfinal).
Qed.

Lemma common_stable_width_trace_execution anchor current ss final :
  common_stable_width_trace anchor current ss final ->
  Semantics.width_iter current (sem_stmts ss) = Some final.
Proof.
  move=> Htrace; induction Htrace.
  - by [].
  - by simpl; rewrite H0.
Qed.

Lemma common_stable_width_trace_split anchor current prefix s suffix final :
  common_stable_width_trace anchor current (prefix ++ s :: suffix) final ->
  exists before after,
    Semantics.width_iter current (sem_stmts prefix) = Some before /\
    Semantics.width_iter_one before (sem_stmt s) = Some after /\
    (forall id, SemSyntax.VM.find id anchor = SemSyntax.VM.find id before) /\
    (forall id, SemSyntax.VM.find id before = SemSyntax.VM.find id after) /\
    Semantics.width_iter after (sem_stmts suffix) = Some final.
Proof.
  move: current.
  elim: prefix => [|first prefix IH] current /= Htrace.
  - inversion Htrace as [|cur next fin stmt rest Hanch Hstep Hsame Htail]; subst.
    exists current, next.
    repeat split; try assumption.
    exact: common_stable_width_trace_execution Htail.
  - inversion Htrace as [|cur next fin stmt rest Hanch Hfirst Hsame Htail]; subst.
    have [before [after [Hprefix [Hstep [Hbefore [Hafter Hsuffix]]]]]] :=
      IH next Htail.
    exists before, after.
    repeat split; try assumption.
    by simpl; rewrite Hfirst Hprefix.
Qed.

Lemma common_unify_width_down modules circ sem_map ss :
  Semantics.unify_width_down modules circ sem_map (sem_stmts ss) = Some sem_map.
Proof.
  elim: ss => [|s ss IH] //=.
  by case: s => [|id ty|id ty clock rst|id e] /=.
Qed.

Lemma common_unify_width_up circ sem_map ss :
  Semantics.unify_width_up circ sem_map (sem_stmts ss) = Some circ.
Proof.
  elim: ss => [|s ss IH] //=.
  by case: s => [|id ty|id ty clock rst|id e] /=.
Qed.

Lemma common_circuit_width_iter solver_map m circ sem_map result :
  scalar_maps_related solver_map sem_map ->
  SemSyntax.VM.find (common_module_name m) circ = Some sem_map ->
  Semantics.circuit_width_iter (sem_circuit m) circ = Some result ->
  exists next,
    Semantics.width_iter sem_map (sem_stmts (common_stmts m)) = Some next /\
    semantic_map_growth sem_map next /\
    result = SemSyntax.VM.add (common_module_name m) next circ.
Proof.
  move=> Hmaps Hfind.
  rewrite /Semantics.circuit_width_iter /sem_circuit /sem_module /= Hfind.
  rewrite common_unify_width_down.
  case Hiter: (Semantics.width_iter sem_map (sem_stmts (common_stmts m)))
    => [next|] //=.
  rewrite common_unify_width_up /=.
  move=> Hresult; inversion Hresult; subst result.
  exists next; split; first reflexivity.
  split; last reflexivity.
  exact: (common_width_iter_growth Hmaps Hiter).
Qed.

Theorem common_circuit_iterator_growth solver_map m n circ sem_map result :
  scalar_maps_related solver_map sem_map ->
  SemSyntax.VM.find (common_module_name m) circ = Some sem_map ->
  Semantics.circuit_tmap_iterator (sem_circuit m) n circ = Some result ->
  exists sem_result,
    SemSyntax.VM.find (common_module_name m) result = Some sem_result /\
    semantic_map_growth sem_map sem_result /\
    scalar_maps_related solver_map sem_result.
Proof.
  move: circ sem_map.
  elim: n => [|n IH] circ sem_map Hmaps Hfind /=.
  - move=> Hresult; inversion Hresult; subst result.
    exists sem_map; split; first exact Hfind.
    split; first exact: semantic_map_growth_refl Hmaps.
    exact Hmaps.
  - case Hiter: (Semantics.circuit_width_iter (sem_circuit m) circ) => [nextcirc|] //=.
    move=> Hrest.
    have [next [Hwidth [Hgrowth Hnext]]] :=
      common_circuit_width_iter Hmaps Hfind Hiter.
    subst nextcirc.
    have Hnextfind :
        SemSyntax.VM.find (common_module_name m)
          (SemSyntax.VM.add (common_module_name m) next circ) = Some next
      by rewrite SemSyntax.VM.Lemmas.find_add_eq // eqxx.
    have Hnextmaps := semantic_growth_preserves_related Hmaps Hgrowth.
    have [sem_result [Hresult [Hgrowth' Hfinalmaps]]] :=
      IH _ next Hnextmaps Hnextfind Hrest.
    exists sem_result; split; first exact Hresult.
    split; last exact Hfinalmaps.
    exact: (semantic_map_growth_trans Hgrowth Hgrowth').
Qed.

Theorem common_successful_result_growth solver_map m circuit_name n initial result :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  exists before after,
    SemSyntax.VM.find (common_module_name m) initial = Some before /\
    SemSyntax.VM.find (common_module_name m) result = Some after /\
    semantic_map_growth before after /\
    scalar_maps_related solver_map after.
Proof.
  move=> Hsolver Hinitial Hresult.
  have [before [Hfind Hmaps]] := initial_circuit_tmaps_related Hsolver Hinitial.
  rewrite /Semantics.circuit_tmap_implicits Hinitial in Hresult.
  case Hiter: (Semantics.circuit_tmap_iterator (sem_circuit m) n initial)
    => [iterated|] //= in Hresult.
  case: (Semantics.circuit_width_iter (sem_circuit m) iterated) => [next|] //= in Hresult.
  case: (SemSyntax.VM.equal (SemSyntax.VM.equal pair_eq) iterated next) => //= in Hresult.
  inversion Hresult; subst iterated.
  have [after [Hafter [Hgrowth Hrelated]]] :=
    common_circuit_iterator_growth Hmaps Hfind Hiter.
  by exists before, after.
Qed.

Lemma common_expr_growth before after e old :
  semantic_map_growth before after ->
  Semantics.type_of_expr None before (sem_expr e) = Some old ->
  exists new,
    Semantics.type_of_expr None after (sem_expr e) = Some new /\
    scalar_width_growth old new.
Proof.
  move=> Hmaps.
  case: e => [id|w bits|w bits] /=.
  - rewrite /Semantics.type_of_expr /=.
    case Hfind: (SemSyntax.VM.find id before) => [[ty kind]|] //=.
    move=> [<-].
    move: (Hmaps id); rewrite Hfind.
    case Hafter: (SemSyntax.VM.find id after) => [[new kind']|] //=.
    move=> [_ Hgrow]. by exists new.
  - rewrite /Semantics.type_of_expr /=.
    case: (w < size bits) => //= H; inversion H; subst old.
    by exists (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint w));
      split; first reflexivity; constructor.
  - rewrite /Semantics.type_of_expr /=.
    case: (w < size bits) => //= H; inversion H; subst old.
    by exists (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint w));
      split; first reflexivity; constructor.
Qed.

Lemma scalar_growth_numeric old new width :
  scalar_width_growth old new ->
  sem_numeric_width old = Some width ->
  exists width', sem_numeric_width new = Some width' /\ (width <= width')%coq_nat.
Proof.
  move=> Hgrow Hwidth; inversion Hgrow; subst; simpl in Hwidth;
    try discriminate; inversion Hwidth; subst;
    eexists; split; try reflexivity; auto.
Qed.

Lemma semantic_operands_preserved before after id e :
  semantic_map_growth before after ->
  semantic_operands before id e ->
  semantic_operands after id e.
Proof.
  move=> Hmaps [dest [kind [lhs [ty [width [Hdest [Himplicit [Hexpr Hwidth]]]]]]]].
  have [newty [Hexpr' Htygrowth]] := common_expr_growth Hmaps Hexpr.
  have [width' [Hwidth' _]] := scalar_growth_numeric Htygrowth Hwidth.
  move: (Hmaps id); rewrite Hdest.
  case Hafter: (SemSyntax.VM.find id after) => [[newdest newkind]|] //=.
  move=> [Hkind Hgrowth]; subst newkind.
  destruct Himplicit as [Himplicit|Himplicit]; subst dest;
    inversion Hgrowth; subst.
  - exists (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit b)),
      kind, b, newty, width'.
    by repeat split; try assumption; left.
  - exists (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit b)),
      kind, b, newty, width'.
    by repeat split; try assumption; right.
Qed.

Lemma common_step_ready_preserved solver_map before after s :
  semantic_map_growth before after ->
  common_step_semantic_ready before solver_map s ->
  common_step_semantic_ready after solver_map s.
Proof.
  rewrite /common_step_semantic_ready.
  case: (common_step_operand solver_map s) => [[id e]|] //=.
  exact: semantic_operands_preserved.
Qed.

Lemma common_steps_ready_preserved solver_map before after ss :
  semantic_map_growth before after ->
  List.Forall (common_step_semantic_ready before solver_map) ss ->
  List.Forall (common_step_semantic_ready after solver_map) ss.
Proof.
  move=> Hgrow Hready.
  induction Hready.
  - constructor.
  - constructor; last exact IHHready.
    exact: (common_step_ready_preserved Hgrow H).
Qed.

Lemma semantic_growth_uint_lookup before after id kind width :
  semantic_map_growth before after ->
  SemSyntax.VM.find id before =
    Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit width), kind) ->
  exists width',
    SemSyntax.VM.find id after =
      Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit width'), kind) /\
    (width <= width')%coq_nat.
Proof.
  move=> Hmaps Hfind; move: (Hmaps id); rewrite Hfind.
  case Hafter: (SemSyntax.VM.find id after) => [[ty kind']|] //=.
  move=> [Hkind Hgrowth]; subst kind'.
  inversion Hgrowth; subst. by exists b.
Qed.

Lemma semantic_growth_sint_lookup before after id kind width :
  semantic_map_growth before after ->
  SemSyntax.VM.find id before =
    Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit width), kind) ->
  exists width',
    SemSyntax.VM.find id after =
      Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit width'), kind) /\
    (width <= width')%coq_nat.
Proof.
  move=> Hmaps Hfind; move: (Hmaps id); rewrite Hfind.
  case Hafter: (SemSyntax.VM.find id after) => [[ty kind']|] //=.
  move=> [Hkind Hgrowth]; subst kind'.
  inversion Hgrowth; subst. by exists b.
Qed.

Corollary successful_result_preserves_step_readiness solver_map m circuit_name n initial result before after :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  SemSyntax.VM.find (common_module_name m) initial = Some before ->
  SemSyntax.VM.find (common_module_name m) result = Some after ->
  List.Forall (common_step_semantic_ready before solver_map) (rev (common_stmts m)) ->
  List.Forall (common_step_semantic_ready after solver_map) (rev (common_stmts m)).
Proof.
  move=> Hsolver Hinitial Hresult Hbefore Hafter Hready.
  have [before' [after' [Hbefore' [Hafter' [Hgrowth _]]]]] :=
    common_successful_result_growth Hsolver Hinitial Hresult.
  rewrite Hbefore in Hbefore'. inversion Hbefore'; subst before'.
  rewrite Hafter in Hafter'. inversion Hafter'; subst after'.
  exact: (common_steps_ready_preserved Hgrowth Hready).
Qed.

Lemma solver_statement_preserves_lookup solver_map next s id binding :
  SolverSyntax.stmt_tmap' solver_map (solver_stmt s) = Some next ->
  SolverSyntax.VM.find id solver_map = Some binding ->
  SolverSyntax.VM.find id next = Some binding.
Proof.
  case: s => [|v ty|v ty clock rst|v e] /=.
  - by move=> [<-].
  - case Hv: (SolverSyntax.VM.find v solver_map) => [[t o]|] //=.
    move=> [<-] Hfind.
    case Heq: (id == v).
    + move/eqP: Heq => Heq; subst id. by rewrite Hv in Hfind.
    + have Hneq : ~ (id == v) by move/negP: Heq.
      by rewrite (SolverSyntax.VM.Lemmas.find_add_neq Hneq).
  - case Hv: (SolverSyntax.VM.find v solver_map) => [[t o]|] //=.
    case: (SolverSyntax.VM.find clock solver_map) => [[ct co]|] //=.
    move=> [<-] Hfind.
    case Heq: (id == v).
    + move/eqP: Heq => Heq; subst id. by rewrite Hv in Hfind.
    + have Hneq : ~ (id == v) by move/negP: Heq.
      by rewrite (SolverSyntax.VM.Lemmas.find_add_neq Hneq).
  - by move=> [<-].
Qed.

Lemma solver_statements_preserve_lookup solver_map next ss id binding :
  SolverSyntax.stmts_tmap' solver_map (solver_stmts ss) = Some next ->
  SolverSyntax.VM.find id solver_map = Some binding ->
  SolverSyntax.VM.find id next = Some binding.
Proof.
  move: solver_map; elim: ss => [|s ss IH] solver_map /=.
  - by move=> [<-].
  - case Hstep: (SolverSyntax.stmt_tmap' solver_map (solver_stmt s)) => [mid|] //=.
    move=> Hrest Hfind.
    apply: (IH mid Hrest).
    exact: (solver_statement_preserves_lookup Hstep Hfind).
Qed.

Lemma solver_statements_register_lookup solver_map final ss id ty clock rst :
  SolverSyntax.stmts_tmap' solver_map (solver_stmts ss) = Some final ->
  List.In (CReg id ty clock rst) ss ->
  SolverSyntax.VM.find id final = Some (solver_type ty, SolverSyntax.Duplex).
Proof.
  move: solver_map; elim: ss => [|s ss IH] solver_map /=.
  - by move=> _ [].
  - case Hstep: (SolverSyntax.stmt_tmap' solver_map (solver_stmt s)) => [mid|] //=.
    move=> Hrest [Heq|Hin].
    + subst s.
      simpl in Hstep.
      case Hfind: (SolverSyntax.VM.find id solver_map) => [[t o]|] //= in Hstep.
      case Hclock: (SolverSyntax.VM.find clock solver_map) => [[ct co]|] //= in Hstep.
      inversion Hstep; subst mid.
      apply: (solver_statements_preserve_lookup Hrest).
      by rewrite SolverSyntax.VM.Lemmas.find_add_eq // eqxx.
    + exact: (IH mid Hrest Hin).
Qed.

Lemma solver_circuit_register_lookup m circuit_name solver_map id ty clock rst :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  List.In (CReg id ty clock rst) (common_stmts m) ->
  SolverSyntax.VM.find id solver_map = Some (solver_type ty, SolverSyntax.Duplex).
Proof.
  rewrite /SolverSyntax.circuit_tmap /solver_circuit /SolverSyntax.modules_tmap
    /SolverSyntax.module_tmap /solver_module /=.
  case Hports: (SolverSyntax.ports_tmap' _ (map solver_port (common_ports m)))
    => [ports|] //=.
  case Hstmts: (SolverSyntax.stmts_tmap' ports (solver_stmts (common_stmts m)))
    => [final|] //=.
  move=> Hfinal Hin. inversion Hfinal; subst final.
  exact: (solver_statements_register_lookup Hstmts Hin).
Qed.

Lemma common_expr_growth_reflect before after e new :
  semantic_map_growth before after ->
  Semantics.type_of_expr None after (sem_expr e) = Some new ->
  exists old,
    Semantics.type_of_expr None before (sem_expr e) = Some old /\
    scalar_width_growth old new.
Proof.
  move=> Hmaps.
  case: e => [id|w bits|w bits] /=.
  - rewrite /Semantics.type_of_expr /=.
    case Hfind: (SemSyntax.VM.find id after) => [[ty kind]|] //=.
    move=> [<-].
    move: (Hmaps id); rewrite Hfind.
    case Hbefore: (SemSyntax.VM.find id before) => [[old kind']|] //=.
    move=> [_ Hgrow]. by exists old.
  - rewrite /Semantics.type_of_expr /=.
    case: (w < size bits) => //= H; inversion H; subst new.
    by exists (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint w));
      split; first reflexivity; constructor.
  - rewrite /Semantics.type_of_expr /=.
    case: (w < size bits) => //= H; inversion H; subst new.
    by exists (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint w));
      split; first reflexivity; constructor.
Qed.

Lemma scalar_growth_numeric_reflect old new width :
  scalar_width_growth old new ->
  sem_numeric_width new = Some width ->
  exists width', sem_numeric_width old = Some width'.
Proof.
  move=> Hgrow Hwidth; inversion Hgrow; subst; simpl in Hwidth;
    try discriminate; by eexists.
Qed.

Lemma semantic_operands_reflected before after id e :
  semantic_map_growth before after ->
  semantic_operands after id e ->
  semantic_operands before id e.
Proof.
  move=> Hmaps [dest [kind [lhs [ty [width [Hdest [Himplicit [Hexpr Hwidth]]]]]]]].
  have [oldty [Hexpr' Htygrowth]] := common_expr_growth_reflect Hmaps Hexpr.
  have [width' Hwidth'] := scalar_growth_numeric_reflect Htygrowth Hwidth.
  move: (Hmaps id); rewrite Hdest.
  case Hbefore: (SemSyntax.VM.find id before) => [[olddest oldkind]|] //=.
  move=> [Hkind Hgrowth]; subst oldkind.
  destruct Himplicit as [Himplicit|Himplicit]; subst dest;
    inversion Hgrowth; subst.
  - exists (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit a)),
      kind, a, oldty, width'.
    by repeat split; try assumption; left.
  - exists (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit a)),
      kind, a, oldty, width'.
    by repeat split; try assumption; right.
Qed.

Lemma common_step_ready_reflected solver_map before after s :
  semantic_map_growth before after ->
  common_step_semantic_ready after solver_map s ->
  common_step_semantic_ready before solver_map s.
Proof.
  rewrite /common_step_semantic_ready.
  case: (common_step_operand solver_map s) => [[id e]|] //=.
  exact: semantic_operands_reflected.
Qed.

Lemma common_steps_ready_reflected solver_map before after ss :
  semantic_map_growth before after ->
  List.Forall (common_step_semantic_ready after solver_map) ss ->
  List.Forall (common_step_semantic_ready before solver_map) ss.
Proof.
  move=> Hgrowth Hready.
  induction Hready.
  - constructor.
  - constructor; last exact IHHready.
    exact: (common_step_ready_reflected Hgrowth H).
Qed.

Lemma implicit_target_unify_source_numeric st sr target source newtarget newsource lhs :
  scalar_type_relation st target ->
  scalar_type_relation sr source ->
  (target = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit lhs) \/
   target = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit lhs)) ->
  Semantics.unify_width HiEnv_with_implicit_widths.Nflip target source =
    Some (newtarget, newsource) ->
  exists width, sem_numeric_width source = Some width.
Proof.
  move=> Htarget Hsource [Huint|Hsint]; subst target;
    inversion Hsource; subst; simpl;
    try (move=> _; by eexists);
    repeat match goal with
      | |- context [match ?n with 0 => _ | S _ => _ end] => destruct n
    end;
    simpl; by move=> H; discriminate.
Qed.

Lemma implicit_solver_lookup_sem solver_map sem_map id st orient :
  scalar_maps_related solver_map sem_map ->
  SolverSyntax.VM.find id solver_map = Some (st, orient) ->
  (exists w, st = HiEnv.Gtyp (Env.Fuint_implicit w) \/
             st = HiEnv.Gtyp (Env.Fsint_implicit w)) ->
  exists dest kind lhs,
    SemSyntax.VM.find id sem_map = Some (dest, kind) /\
    (dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit lhs) \/
     dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit lhs)).
Proof.
  move=> Hmaps Hfind [w [Heq|Heq]]; subst st;
    have [dest [kind [Hsem Hrel]]] := scalar_maps_related_lookup Hmaps Hfind;
    inversion Hrel; subst.
  - exists (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit mw)), kind, mw.
    by split; first exact Hsem; left.
  - exists (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit mw)), kind, mw.
    by split; first exact Hsem; right.
Qed.

Lemma implicit_unify_operands solver_map sem_map id e dest kind lhs ty newdst newty :
  scalar_maps_related solver_map sem_map ->
  SemSyntax.VM.find id sem_map = Some (dest, kind) ->
  (dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit lhs) \/
   dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit lhs)) ->
  Semantics.type_of_expr None sem_map (sem_expr e) = Some ty ->
  Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest ty = Some (newdst, newty) ->
  semantic_operands sem_map id e.
Proof.
  move=> Hmaps Hfind Himplicit Hexpr Hunify.
  have [st Hst] := related_semantic_lookup Hmaps Hfind.
  have [sr Hsr] := common_expr_is_semantic_scalar Hmaps Hexpr.
  have [width Hwidth] := implicit_target_unify_source_numeric Hst Hsr Himplicit Hunify.
  by exists dest, kind, lhs, ty, width.
Qed.

Lemma implicit_reg_step_operands solver_map sem_map result id ty clock trigger e :
  scalar_maps_related solver_map sem_map ->
  (exists orient w,
     SolverSyntax.VM.find id solver_map =
       Some (HiEnv.Gtyp (Env.Fuint_implicit w), orient) \/
     SolverSyntax.VM.find id solver_map =
       Some (HiEnv.Gtyp (Env.Fsint_implicit w), orient)) ->
  Semantics.width_iter_one sem_map (sem_stmt (CReg id ty clock (CReset trigger e))) =
    Some result ->
  semantic_operands sem_map id e.
Proof.
  move=> Hmaps [orient [w [Hfind|Hfind]]] Hiter.
  all: have Htarget : exists dest kind lhs,
      SemSyntax.VM.find id sem_map = Some (dest, kind) /\
      (dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit lhs) \/
       dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit lhs)).
  all: try solve [exact: (implicit_solver_lookup_sem Hmaps Hfind (ex_intro _ w (or_introl erefl)))].
  all: try solve [exact: (implicit_solver_lookup_sem Hmaps Hfind (ex_intro _ w (or_intror erefl)))].
  all: destruct Htarget as [dest [kind [lhs [Hdest Himplicit]]]].
  all: rewrite /= Hdest in Hiter.
  all: destruct kind; try discriminate.
  all: destruct (Semantics.type_of_expr None sem_map (sem_expr e)) as [value|] eqn:Hexpr;
    try discriminate.
  all: destruct (HiEnv_with_implicit_widths.is_passive dest &&
             HiEnv_with_implicit_widths.is_passive value); try discriminate.
  all: destruct (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest value)
    as [[newdst newvalue]|] eqn:Hunify; try discriminate.
  all: exact: (implicit_unify_operands Hmaps Hdest Himplicit Hexpr Hunify).
Qed.

Lemma implicit_connect_step_operands solver_map sem_map result id e :
  scalar_maps_related solver_map sem_map ->
  (exists orient w,
     SolverSyntax.VM.find id solver_map =
       Some (HiEnv.Gtyp (Env.Fuint_implicit w), orient) \/
     SolverSyntax.VM.find id solver_map =
       Some (HiEnv.Gtyp (Env.Fsint_implicit w), orient)) ->
  Semantics.width_iter_one sem_map (sem_stmt (CConnect id e)) = Some result ->
  semantic_operands sem_map id e.
Proof.
  move=> Hmaps [orient [w Hfind]] Hiter.
  have Htarget : exists dest kind lhs,
      SemSyntax.VM.find id sem_map = Some (dest, kind) /\
      (dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit lhs) \/
       dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit lhs)).
  { case: Hfind => Hfind.
    - exact: (implicit_solver_lookup_sem Hmaps Hfind (ex_intro _ w (or_introl erefl))).
    - exact: (implicit_solver_lookup_sem Hmaps Hfind (ex_intro _ w (or_intror erefl))). }
  destruct Htarget as [dest [kind [lhs [Hdest Himplicit]]]].
  case: e Hiter => [src|width bits|width bits] Hiter.
  - rewrite /= Hdest in Hiter.
    case Hsrc: (SemSyntax.VM.find src sem_map) => [[source skind]|] //= in Hiter.
    case Hunify: (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest source)
      => [[newdst newsource]|] //= in Hiter.
    have Hexpr : Semantics.type_of_expr None sem_map (sem_expr (CRef src)) = Some source
      by rewrite /Semantics.type_of_expr /= Hsrc.
    exact: (implicit_unify_operands Hmaps Hdest Himplicit Hexpr Hunify).
  - rewrite /= Hdest /Semantics.type_of_expr /= in Hiter.
    case Hvalid: (width < size bits) => //= in Hiter.
    case Hunify: (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest
        (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint width)))
      => [[newdst newsource]|] //= in Hiter.
    have Hexpr : Semantics.type_of_expr None sem_map (sem_expr (CUInt width bits)) =
        Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint width))
      by rewrite /Semantics.type_of_expr /= Hvalid.
    exact: (implicit_unify_operands Hmaps Hdest Himplicit Hexpr Hunify).
  - rewrite /= Hdest /Semantics.type_of_expr /= in Hiter.
    case Hvalid: (width < size bits) => //= in Hiter.
    case Hunify: (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest
        (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint width)))
      => [[newdst newsource]|] //= in Hiter.
    have Hexpr : Semantics.type_of_expr None sem_map (sem_expr (CSInt width bits)) =
        Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint width))
      by rewrite /Semantics.type_of_expr /= Hvalid.
    exact: (implicit_unify_operands Hmaps Hdest Himplicit Hexpr Hunify).
Qed.

Definition registers_match_solver_map solver_map ss : Prop :=
  forall id ty clock rst,
    List.In (CReg id ty clock rst) ss ->
    SolverSyntax.VM.find id solver_map = Some (solver_type ty, SolverSyntax.Duplex).

Lemma common_width_step_ready solver_map sem_map result s :
  scalar_maps_related solver_map sem_map ->
  registers_match_solver_map solver_map [:: s] ->
  Semantics.width_iter_one sem_map (sem_stmt s) = Some result ->
  common_step_semantic_ready sem_map solver_map s.
Proof.
  move=> Hmaps Hregs Hiter.
  case: s Hregs Hiter => [|id ty|id ty clock rst|id e] Hregs Hiter //=.
  - have Hfind := Hregs id ty clock rst (or_introl erefl).
    clear Hregs.
    case: ty Hfind Hiter => [| |w|w] Hfind Hiter;
      case: rst Hfind Hiter => [|trigger value] Hfind Hiter //=.
    + apply: (implicit_reg_step_operands Hmaps _ Hiter).
      exists SolverSyntax.Duplex, 0. by left.
    + apply: (implicit_reg_step_operands Hmaps _ Hiter).
      exists SolverSyntax.Duplex, 0. by right.
  - rewrite /common_step_semantic_ready /common_step_operand.
    case Hfind: (SolverSyntax.VM.find id solver_map) => [[ty orient]|] //=.
    case: ty Hfind => [gt|elt n|fields] Hfind //=.
    case: gt Hfind => [w|w|w|w| | |] Hfind //=.
    + apply: (implicit_connect_step_operands Hmaps _ Hiter).
      exists orient, w. by left.
    + apply: (implicit_connect_step_operands Hmaps _ Hiter).
      exists orient, w. by right.
Qed.

Lemma common_width_iter_initial_ready solver_map sem_map result ss :
  scalar_maps_related solver_map sem_map ->
  registers_match_solver_map solver_map ss ->
  Semantics.width_iter sem_map (sem_stmts ss) = Some result ->
  List.Forall (common_step_semantic_ready sem_map solver_map) ss.
Proof.
  move: sem_map; elim: ss => [|s ss IH] sem_map Hmaps Hregs /=.
  - by move=> _; constructor.
  - case Hstep: (Semantics.width_iter_one sem_map (sem_stmt s)) => [mid|] //=.
    move=> Hrest.
    have Hregfirst : registers_match_solver_map solver_map [:: s].
    { move=> id ty clock rst [Heq|[]].
      apply: Hregs. left. exact Heq. }
    have Hregtail : registers_match_solver_map solver_map ss.
    { move=> id ty clock rst Hin. apply: Hregs. right. exact Hin. }
    have Hgrowth := common_width_iter_one_growth Hmaps Hstep.
    have Hmapsmid := semantic_growth_preserves_related Hmaps Hgrowth.
    have Htail := IH mid Hmapsmid Hregtail Hrest.
    constructor.
    + exact: (common_width_step_ready Hmaps Hregfirst Hstep).
    + exact: (common_steps_ready_reflected Hgrowth Htail).
Qed.

Lemma forall_mathcomp_rev (A : Type) (P : A -> Prop) (xs : seq A) :
  List.Forall P xs -> List.Forall P (rev xs).
Proof.
  move=> H; induction H.
  - constructor.
  - rewrite rev_cons -cats1.
    apply List.Forall_app. split; first exact IHForall.
    by constructor; first exact H; constructor.
Qed.

Theorem successful_circuit_initial_operands_ready solver_map m circuit_name n initial result :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  exists before after,
    SemSyntax.VM.find (common_module_name m) initial = Some before /\
    SemSyntax.VM.find (common_module_name m) result = Some after /\
    semantic_map_growth before after /\
    scalar_maps_related solver_map after /\
    List.Forall (common_step_semantic_ready before solver_map) (rev (common_stmts m)) /\
    List.Forall (common_step_semantic_ready after solver_map) (rev (common_stmts m)).
Proof.
  move=> Hsolver Hinitial Hresult.
  have [before [after [Hbefore [Hafter [Hgrowth Hmaps]]]]] :=
    common_successful_result_growth Hsolver Hinitial Hresult.
  have [nextcirc [Hiter _]] := successful_semantic_result_is_fixed Hresult.
  have [next [Hwidth [_ _]]] := common_circuit_width_iter Hmaps Hafter Hiter.
  have Hregs : registers_match_solver_map solver_map (common_stmts m).
  { move=> id ty clock rst Hin.
    exact: (solver_circuit_register_lookup Hsolver Hin). }
  have Hready := common_width_iter_initial_ready Hmaps Hregs Hwidth.
  have Hready_rev : List.Forall (common_step_semantic_ready after solver_map)
      (rev (common_stmts m)).
  { exact: (forall_mathcomp_rev Hready). }
  exists before, after.
  repeat split; try assumption.
  exact: (common_steps_ready_reflected Hgrowth Hready_rev).
Qed.

Corollary successful_result_extracted_constraints_match_bounds
    value solver_map m circuit_name n initial result cmap :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  extract_constraints_c (solver_circuit circuit_name m) solver_map =
    Some ([:: cmap], [::]) ->
  exists sem_map,
    SemSyntax.VM.find (common_module_name m) result = Some sem_map /\
    (valuation_matches_sem_map value sem_map ->
      (List.forallb (satisfies_constraint1 value)
         (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true <->
       List.Forall (common_step_semantic_bound sem_map solver_map)
         (rev (common_stmts m)))).
Proof.
  move=> Hsolver Hinitial Hresult Hextract.
  have [before [after [_ [Hafter [_ [Hmaps [_ Hready]]]]]]] :=
    successful_circuit_initial_operands_ready Hsolver Hinitial Hresult.
  exists after; split; first exact Hafter.
  move=> Hvalue.
  exact: (extracted_constraints_match_semantic_bounds Hmaps Hvalue Hready Hextract).
Qed.

Theorem successful_circuit_result_stable_width_trace
    solver_map m circuit_name n initial result :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  exists sem_map next,
    SemSyntax.VM.find (common_module_name m) result = Some sem_map /\
    scalar_maps_related solver_map sem_map /\
    Semantics.width_iter sem_map (sem_stmts (common_stmts m)) = Some next /\
    (forall id, SemSyntax.VM.find id sem_map = SemSyntax.VM.find id next) /\
    common_stable_width_trace sem_map sem_map (common_stmts m) next.
Proof.
  move=> Hsolver Hinitial Hresult.
  have [before [sem_map [_ [Hfind [_ Hmaps]]]]] :=
    common_successful_result_growth Hsolver Hinitial Hresult.
  have [nextcirc [Hiter Hfixed]] := successful_semantic_result_is_fixed Hresult.
  have [next [Hwidth [_ Hnextcirc]]] := common_circuit_width_iter Hmaps Hfind Hiter.
  have Hnextfind : SemSyntax.VM.find (common_module_name m) nextcirc = Some next.
  { rewrite Hnextcirc SemSyntax.VM.Lemmas.find_add_eq // eqxx. }
  have Hequal : forall id, SemSyntax.VM.find id sem_map = SemSyntax.VM.find id next.
  { move: (Hfixed (common_module_name m)). by rewrite Hfind Hnextfind. }
  exists sem_map, next.
  repeat split; try assumption.
  apply: (common_fixed_width_iter_stable_trace Hmaps _ Hwidth Hequal).
  by [].
Qed.

Lemma implicit_unify_unchanged_bound st sr dest source newsource lhs width :
  scalar_type_relation st dest ->
  scalar_type_relation sr source ->
  (dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit lhs) \/
   dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit lhs)) ->
  sem_numeric_width source = Some width ->
  Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest source =
    Some (dest, newsource) ->
  (width <= lhs)%coq_nat.
Proof.
  move=> Hdest Hsource [Huint|Hsint] Hwidth Hunify; subst dest;
    inversion Hsource; subst; simpl in Hwidth, Hunify;
    try discriminate;
    repeat match goal with
      | H : context [match ?n with 0 => _ | S _ => _ end] |- _ => destruct n
    end;
    simpl in Hwidth, Hunify; try discriminate;
    inversion Hwidth; subst width; inversion Hunify; subst;
    apply/leP; try by rewrite -H0; exact: leq_maxr.
Qed.

Lemma stable_reg_reset_semantic_bound solver_map sem_map result id ty clock trigger e :
  scalar_maps_related solver_map sem_map ->
  semantic_operands sem_map id e ->
  Semantics.width_iter_one sem_map (sem_stmt (CReg id ty clock (CReset trigger e))) =
    Some result ->
  (forall key, SemSyntax.VM.find key sem_map = SemSyntax.VM.find key result) ->
  semantic_width_bound sem_map id e.
Proof.
  move=> Hmaps Hready Hiter Hstable.
  destruct Hready as [dest [kind [lhs [source [width
    [Hdest [Himplicit [Hexpr Hwidth]]]]]]]].
  rewrite /= Hdest Hexpr in Hiter.
  destruct kind; try discriminate.
  destruct (HiEnv_with_implicit_widths.is_passive dest &&
    HiEnv_with_implicit_widths.is_passive source); try discriminate.
  destruct (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest source)
    as [[newdest newsource]|] eqn:Hunify; try discriminate.
  inversion Hiter; subst result.
  have Hsame := Hstable id.
  rewrite Hdest SemSyntax.VM.Lemmas.find_add_eq //= in Hsame.
  inversion Hsame; subst newdest.
  have [st Hst] := related_semantic_lookup Hmaps Hdest.
  have [sr Hsr] := common_expr_is_semantic_scalar Hmaps Hexpr.
  have Hle := implicit_unify_unchanged_bound Hst Hsr Himplicit Hwidth Hunify.
  by exists dest, HiEnv_with_implicit_widths.Register, lhs, source, width.
Qed.

Lemma stable_connect_semantic_bound solver_map sem_map result id e :
  scalar_maps_related solver_map sem_map ->
  semantic_operands sem_map id e ->
  Semantics.width_iter_one sem_map (sem_stmt (CConnect id e)) = Some result ->
  (forall key, SemSyntax.VM.find key sem_map = SemSyntax.VM.find key result) ->
  semantic_width_bound sem_map id e.
Proof.
  move=> Hmaps Hready Hiter Hstable.
  destruct Hready as [dest [kind [lhs [source [width
    [Hdest [Himplicit [Hexpr Hwidth]]]]]]]].
  have [st Hst] := related_semantic_lookup Hmaps Hdest.
  have [sr Hsr] := common_expr_is_semantic_scalar Hmaps Hexpr.
  have Hle : (width <= lhs)%coq_nat.
  { case: e Hexpr Hiter => [src|w bits|w bits] Hexpr Hiter.
    - rewrite /Semantics.type_of_expr /= in Hexpr.
      case Hsrc: (SemSyntax.VM.find src sem_map) => [[sty skind]|] //= in Hexpr.
      inversion Hexpr; subst sty.
      case Hsame: (src == id).
      + move/eqP: Hsame => Hsame; subst src.
        rewrite Hdest in Hsrc. inversion Hsrc; subst source skind.
        destruct Himplicit as [Himplicit|Himplicit]; subst dest;
          simpl in Hwidth; inversion Hwidth; subst width; auto.
      + have Hneq : ~ (src == id) by move/negP: Hsame.
        rewrite /= Hdest Hsrc in Hiter.
        destruct (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest source)
          as [[newdest newsource]|] eqn:Hunify.
        2: { simpl in Hiter. by rewrite Hunify in Hiter. }
        cbn [option_map fst] in Hiter. rewrite Hunify /= in Hiter.
        rewrite (SemSyntax.VM.Lemmas.find_add_neq Hneq) Hsrc /= in Hiter.
        inversion Hiter; subst result.
        have Heq := Hstable id.
        have Hneq' : ~ (id == src) by rewrite eq_sym; exact Hneq.
        rewrite Hdest (SemSyntax.VM.Lemmas.find_add_neq Hneq')
          SemSyntax.VM.Lemmas.find_add_eq //= in Heq.
        inversion Heq; subst newdest.
        exact: (implicit_unify_unchanged_bound Hst Hsr Himplicit Hwidth Hunify).
    - rewrite /Semantics.type_of_expr /= in Hexpr.
      case Hvalid: (w < size bits) => //= in Hexpr.
      inversion Hexpr; subst source.
      rewrite /= Hdest /Semantics.type_of_expr /= Hvalid in Hiter.
      destruct (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest
          (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint w)))
        as [[newdest newsource]|] eqn:Hunify.
      2: discriminate.
      inversion Hiter; subst result.
      have Heq := Hstable id.
      rewrite Hdest SemSyntax.VM.Lemmas.find_add_eq //= in Heq.
      inversion Heq; subst newdest.
      exact: (implicit_unify_unchanged_bound Hst Hsr Himplicit Hwidth Hunify).
    - rewrite /Semantics.type_of_expr /= in Hexpr.
      case Hvalid: (w < size bits) => //= in Hexpr.
      inversion Hexpr; subst source.
      rewrite /= Hdest /Semantics.type_of_expr /= Hvalid in Hiter.
      destruct (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest
          (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint w)))
        as [[newdest newsource]|] eqn:Hunify.
      2: discriminate.
      inversion Hiter; subst result.
      have Heq := Hstable id.
      rewrite Hdest SemSyntax.VM.Lemmas.find_add_eq //= in Heq.
      inversion Heq; subst newdest.
      exact: (implicit_unify_unchanged_bound Hst Hsr Himplicit Hwidth Hunify). }
  by exists dest, kind, lhs, source, width.
Qed.

Lemma common_expr_equal_maps before after e :
  (forall id, SemSyntax.VM.find id before = SemSyntax.VM.find id after) ->
  Semantics.type_of_expr None before (sem_expr e) =
    Semantics.type_of_expr None after (sem_expr e).
Proof.
  move=> Heq; case: e => [id|w bits|w bits] //=.
  by rewrite /Semantics.type_of_expr /= Heq.
Qed.

Lemma semantic_operands_equal_maps before after id e :
  (forall key, SemSyntax.VM.find key before = SemSyntax.VM.find key after) ->
  semantic_operands before id e -> semantic_operands after id e.
Proof.
  move=> Heq [dest [kind [lhs [ty [width [Hfind [Himplicit [Hexpr Hwidth]]]]]]]].
  exists dest, kind, lhs, ty, width.
  repeat split; try assumption.
  - by rewrite -Heq.
  - by rewrite -(common_expr_equal_maps e Heq).
Qed.

Lemma semantic_bound_equal_maps before after id e :
  (forall key, SemSyntax.VM.find key before = SemSyntax.VM.find key after) ->
  semantic_width_bound before id e -> semantic_width_bound after id e.
Proof.
  move=> Heq [dest [kind [lhs [ty [width
    [Hfind [Himplicit [Hexpr [Hwidth Hle]]]]]]]]].
  exists dest, kind, lhs, ty, width.
  repeat split; try assumption.
  - by rewrite -Heq.
  - by rewrite -(common_expr_equal_maps e Heq).
Qed.

Lemma stable_common_step_semantic_bound solver_map sem_map result s :
  scalar_maps_related solver_map sem_map ->
  common_step_semantic_ready sem_map solver_map s ->
  Semantics.width_iter_one sem_map (sem_stmt s) = Some result ->
  (forall id, SemSyntax.VM.find id sem_map = SemSyntax.VM.find id result) ->
  common_step_semantic_bound sem_map solver_map s.
Proof.
  move=> Hmaps Hready Hstep Hstable.
  rewrite /common_step_semantic_ready /common_step_semantic_bound
    /common_step_operand in Hready *.
  case: s Hready Hstep => [|id ty|id ty clock rst|id e] Hready Hstep //=.
  - case: ty rst Hready Hstep => [| |w|w] [|trigger e] Hready Hstep //=.
    + exact: (stable_reg_reset_semantic_bound Hmaps Hready Hstep Hstable).
    + exact: (stable_reg_reset_semantic_bound Hmaps Hready Hstep Hstable).
  - case: (SolverSyntax.VM.find id solver_map) Hready => [[ty orient]|] //= Hready.
    case: ty Hready => [gt|elt n|fields] //= Hready.
    case: gt Hready => [w|w|w|w| | |] //= Hready;
      exact: (stable_connect_semantic_bound Hmaps Hready Hstep Hstable).
Qed.

Lemma stable_trace_semantic_bounds solver_map anchor current ss final :
  scalar_maps_related solver_map anchor ->
  List.Forall (common_step_semantic_ready anchor solver_map) ss ->
  common_stable_width_trace anchor current ss final ->
  List.Forall (common_step_semantic_bound anchor solver_map) ss.
Proof.
  move=> Hmaps Hready Htrace.
  induction Htrace as [current Heq|current next final s ss Heq Hstep Hstable Htail IH].
  - constructor.
  - inversion Hready as [|s' ss' Hfirst Hrest]; subst.
    have Hcurrentmaps : scalar_maps_related solver_map current.
    { move=> id. move: (Hmaps id). by rewrite Heq. }
    have Hcurrentready : common_step_semantic_ready current solver_map s.
    { rewrite /common_step_semantic_ready in Hfirst *.
      case: (common_step_operand solver_map s) Hfirst => [[id e]|] //=.
      exact: semantic_operands_equal_maps Heq. }
    have Hbound := stable_common_step_semantic_bound Hcurrentmaps Hcurrentready Hstep Hstable.
    constructor.
    + rewrite /common_step_semantic_bound in Hbound *.
      case: (common_step_operand solver_map s) Hbound => [[id e]|] //=.
      apply: semantic_bound_equal_maps.
      * move=> id'. by rewrite Heq.
    + exact: (IH Hrest).
Qed.

Theorem successful_result_semantic_bounds solver_map m circuit_name n initial result :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  exists sem_map,
    SemSyntax.VM.find (common_module_name m) result = Some sem_map /\
    scalar_maps_related solver_map sem_map /\
    List.Forall (common_step_semantic_bound sem_map solver_map) (common_stmts m) /\
    List.Forall (common_step_semantic_bound sem_map solver_map) (rev (common_stmts m)).
Proof.
  move=> Hsolver Hinitial Hresult.
  have [sem_map [next [Hfind [Hmaps [_ [_ Htrace]]]]]] :=
    successful_circuit_result_stable_width_trace Hsolver Hinitial Hresult.
  have [before [after [_ [Hafter [_ [_ [_ Hready]]]]]]] :=
    successful_circuit_initial_operands_ready Hsolver Hinitial Hresult.
  rewrite Hfind in Hafter. inversion Hafter; subst after.
  have Hready' : List.Forall (common_step_semantic_ready sem_map solver_map)
      (common_stmts m).
  { have Hrev := forall_mathcomp_rev Hready.
    by rewrite revK in Hrev. }
  have Hbounds := stable_trace_semantic_bounds Hmaps Hready' Htrace.
  exists sem_map; repeat split; try assumption.
  exact: forall_mathcomp_rev Hbounds.
Qed.

Corollary successful_result_matching_valuation_satisfies_constraints
    value solver_map m circuit_name n initial result cmap :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  extract_constraints_c (solver_circuit circuit_name m) solver_map =
    Some ([:: cmap], [::]) ->
  exists sem_map,
    SemSyntax.VM.find (common_module_name m) result = Some sem_map /\
    (valuation_matches_sem_map value sem_map ->
      List.forallb (satisfies_constraint1 value)
        (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true).
Proof.
  move=> Hsolver Hinitial Hresult Hextract.
  have [sem_map [Hfind [_ [_ Hbounds]]]] :=
    successful_result_semantic_bounds Hsolver Hinitial Hresult.
  have [matched [Hmatched Hiff]] :=
    successful_result_extracted_constraints_match_bounds
      value Hsolver Hinitial Hresult Hextract.
  rewrite Hfind in Hmatched. inversion Hmatched; subst matched.
  exists sem_map; split; first exact Hfind.
  move=> Hvalue.
  exact: (proj2 (Hiff Hvalue) Hbounds).
Qed.

Definition semantic_implicit_width (sem_map : sem_component_map) (id : var) : option nat :=
  match SemSyntax.VM.find id sem_map with
  | Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit w), _)
  | Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit w), _) =>
      Some w
  | _ => None
  end.

Fixpoint semantic_valuation_of_ids (sem_map : sem_component_map) (ids : seq var) : Valuation :=
  match ids with
  | [::] => SolverSyntax.PVM.empty _
  | id :: rest =>
      match semantic_implicit_width sem_map id with
      | Some w => SolverSyntax.PVM.add (id, N0) w (semantic_valuation_of_ids sem_map rest)
      | None => semantic_valuation_of_ids sem_map rest
      end
  end.

Definition semantic_valuation (sem_map : sem_component_map) : Valuation :=
  semantic_valuation_of_ids sem_map (map fst (SemSyntax.VM.elements sem_map)).

Lemma semantic_valuation_ids_find sem_map ids id :
  solver_width (semantic_valuation_of_ids sem_map ids) id =
    if id \in ids then semantic_implicit_width sem_map id else None.
Proof.
  elim: ids => [|first rest IH] /=.
  - by rewrite /solver_width SolverSyntax.PVM.Lemmas.F.empty_o.
  - case Hfirst: (semantic_implicit_width sem_map first) => [w|].
    + rewrite /solver_width /=.
      case Hsame: (id == first).
      * move/eqP: Hsame => ->.
        by rewrite SolverSyntax.PVM.Lemmas.F.add_eq_o //= Hfirst in_cons eqxx.
      * have Hneq : ~ SolverSyntax.ProdVar.eq (first, N0) (id, N0).
        { move=> Heq. apply eq_from_prodvar_eq in Heq.
          inversion Heq; subst. by rewrite eqxx in Hsame. }
        rewrite SolverSyntax.PVM.Lemmas.F.add_neq_o //.
        change (solver_width (semantic_valuation_of_ids sem_map rest) id =
          if id \in first :: rest then semantic_implicit_width sem_map id else None).
        by rewrite IH in_cons Hsame /=.
    + change (solver_width (semantic_valuation_of_ids sem_map rest) id =
          if id \in first :: rest then semantic_implicit_width sem_map id else None).
      rewrite IH in_cons.
      case Hsame: (id == first) => //=.
      move/eqP: Hsame => ->. by rewrite Hfirst; case: (first \in rest).
Qed.

Lemma semantic_find_in_element_ids (sem_map : sem_component_map) id binding :
  SemSyntax.VM.find id sem_map = Some binding ->
  id \in map fst (SemSyntax.VM.elements sem_map).
Proof.
  move=> Hfind.
  have Hin := SemSyntax.VM.elements_1 (SemSyntax.VM.find_2 Hfind).
  apply SetoidList.InA_alt in Hin.
  destruct Hin as [[key value] [Heq Hin]].
  move: Heq => [Hkey Hvalue].
  simpl in Hkey.
  move/eqP: Hkey => Hkey; subst key.
  have Hmember : List.In id (map fst (SemSyntax.VM.elements sem_map)).
  { have H := List.in_map fst (SemSyntax.VM.elements sem_map) (id, value) Hin.
    exact H. }
  elim: (map fst (SemSyntax.VM.elements sem_map)) Hmember => [|first rest IH] //=.
  move=> [->|Htail].
  - by rewrite in_cons eqxx.
  - rewrite in_cons. by apply/orP; right; apply: IH Htail.
Qed.

Theorem semantic_valuation_find sem_map id :
  solver_width (semantic_valuation sem_map) id = semantic_implicit_width sem_map id.
Proof.
  rewrite /semantic_valuation semantic_valuation_ids_find.
  case Hwidth: (semantic_implicit_width sem_map id) => [w|].
  - rewrite /semantic_implicit_width in Hwidth.
    case Hfind: (SemSyntax.VM.find id sem_map) => [[ty kind]|] // in Hwidth.
    by rewrite (semantic_find_in_element_ids Hfind).
  - by case: (id \in map fst (SemSyntax.VM.elements sem_map)).
Qed.

Corollary semantic_valuation_matches sem_map :
  valuation_matches_sem_map (semantic_valuation sem_map) sem_map.
Proof.
  move=> id ty kind w Hfind [Hty|Hty]; subst ty;
    by rewrite semantic_valuation_find /semantic_implicit_width Hfind.
Qed.

Lemma semantic_valuation_ids_nonzero sem_map ids id offset :
  offset <> N0 ->
  SolverSyntax.PVM.find (id, offset) (semantic_valuation_of_ids sem_map ids) = None.
Proof.
  move=> Hnonzero; elim: ids => [|first rest IH] /=.
  - exact: SolverSyntax.PVM.Lemmas.F.empty_o.
  - case: (semantic_implicit_width sem_map first) => [w|]; last exact IH.
    rewrite SolverSyntax.PVM.Lemmas.F.add_neq_o; first exact IH.
    move=> Heq. apply eq_from_prodvar_eq in Heq.
    inversion Heq; subst offset. exact: Hnonzero erefl.
Qed.

Corollary semantic_valuation_nonzero sem_map id offset :
  offset <> N0 -> SolverSyntax.PVM.find (id, offset) (semantic_valuation sem_map) = None.
Proof. exact: semantic_valuation_ids_nonzero. Qed.

Lemma semantic_growth_implicit_width before after id w :
  semantic_map_growth before after ->
  semantic_implicit_width before id = Some w ->
  exists w', semantic_implicit_width after id = Some w' /\ (w <= w')%coq_nat.
Proof.
  move=> Hgrowth Hwidth.
  rewrite /semantic_implicit_width in Hwidth *.
  case Hbefore: (SemSyntax.VM.find id before) => [[ty kind]|] // in Hwidth.
  case Hafter: (SemSyntax.VM.find id after) => [[ty' kind']|].
  - have Htype := Hgrowth id.
    rewrite Hbefore Hafter in Htype.
    destruct Htype as [_ Htype].
    inversion Htype; subst; simpl; try discriminate;
      simpl in Hwidth; try discriminate; inversion Hwidth; subst w; eauto.
  - move: (Hgrowth id); by rewrite Hbefore Hafter.
Qed.

Theorem semantic_result_valuation_covers_original
    solver_map m circuit_name n initial result :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  exists sem_map,
    SemSyntax.VM.find (common_module_name m) result = Some sem_map /\
    valuation_matches_sem_map (semantic_valuation sem_map) sem_map /\
    covered (semantic_valuation sem_map) initial (common_module_name m).
Proof.
  move=> Hsolver Hinitial Hresult.
  have [before [after [Hbefore [Hafter [Hgrowth Hmaps]]]]] :=
    common_successful_result_growth Hsolver Hinitial Hresult.
  exists after; split; first exact Hafter.
  split; first exact: semantic_valuation_matches.
  move=> id Horiginal.
  rewrite /original_implicit Hbefore in Horiginal.
  have [w Hwidth] : exists w, semantic_implicit_width before id = Some w.
  { rewrite /semantic_implicit_width.
    case: (SemSyntax.VM.find id before) Horiginal => [[ty kind]|] //.
    case: ty => [gt|elt len|fields] //.
    by case: gt => [w|w|w|w| | | |] //= _; exists w. }
  have [w' [Hafterwidth _]] := semantic_growth_implicit_width Hgrowth Hwidth.
  exists w'. by rewrite semantic_valuation_find Hafterwidth.
Qed.

Corollary semantic_result_valuation_satisfies_constraints
    solver_map m circuit_name n initial result cmap :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  extract_constraints_c (solver_circuit circuit_name m) solver_map =
    Some ([:: cmap], [::]) ->
  exists sem_map,
    SemSyntax.VM.find (common_module_name m) result = Some sem_map /\
    covered (semantic_valuation sem_map) initial (common_module_name m) /\
    List.forallb (satisfies_constraint1 (semantic_valuation sem_map))
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true.
Proof.
  move=> Hsolver Hinitial Hresult Hextract.
  have [sem_map [Hfind [_ Hcovered]]] :=
    semantic_result_valuation_covers_original Hsolver Hinitial Hresult.
  have [matched [Hmatched Hsat]] :=
    successful_result_matching_valuation_satisfies_constraints
      (semantic_valuation sem_map) Hsolver Hinitial Hresult Hextract.
  rewrite Hfind in Hmatched. inversion Hmatched; subst matched.
  exists sem_map; split; first exact Hfind.
  split; first exact Hcovered.
  apply: Hsat. exact: semantic_valuation_matches.
Qed.

Definition semantic_implicit_initial_zero (sem_map : sem_component_map) : Prop :=
  forall id w, semantic_implicit_width sem_map id = Some w -> w = 0.

Lemma semantic_initial_zero_add sem_map id ty kind :
  semantic_implicit_initial_zero sem_map ->
  semantic_implicit_initial_zero (SemSyntax.VM.add id (sem_type ty, kind) sem_map).
Proof.
  move=> Hzero key w.
  rewrite /semantic_implicit_width.
  case Hsame: (key == id).
  - rewrite (SemSyntax.VM.Lemmas.find_add_eq Hsame).
    by case: ty => [| |n|n] //=; move=> [<-].
  - have Hneq : ~ (key == id) by move/negP: Hsame.
    rewrite (SemSyntax.VM.Lemmas.find_add_neq Hneq).
    exact: Hzero.
Qed.

Lemma semantic_initial_zero_add_clock sem_map id kind :
  semantic_implicit_initial_zero sem_map ->
  semantic_implicit_initial_zero
    (SemSyntax.VM.add id
      (HiEnv_with_implicit_widths.Gtyp Env_with_implicit_widths.Fclock, kind) sem_map).
Proof.
  move=> Hzero key w.
  rewrite /semantic_implicit_width.
  case Hsame: (key == id).
  - by rewrite (SemSyntax.VM.Lemmas.find_add_eq Hsame).
  - have Hneq : ~ (key == id) by move/negP: Hsame.
    rewrite (SemSyntax.VM.Lemmas.find_add_neq Hneq).
    exact: Hzero.
Qed.

Lemma semantic_ports_initial_zero ports sem_map :
  Semantics.ports_tmap (map sem_port ports) = Some sem_map ->
  semantic_implicit_initial_zero sem_map.
Proof.
  elim: ports sem_map => [|p ports IH] sem_map /=.
  - move=> [<-] id w. by rewrite /semantic_implicit_width SemSyntax.VM.Lemmas.F.empty_o.
  - case: p => [id ty|id ty|id] /=;
      case Hports: (Semantics.ports_tmap (map sem_port ports)) => [tail|] //=;
      case: (SemSyntax.VM.find id tail) => [[t k]|] //=;
      move=> Hfinal; inversion Hfinal; subst sem_map.
    + exact: semantic_initial_zero_add (IH tail Hports).
    + exact: semantic_initial_zero_add (IH tail Hports).
    + exact: semantic_initial_zero_add_clock (IH tail Hports).
Qed.

Lemma semantic_statements_initial_zero modules ss scope sem_map final_scope final :
  semantic_implicit_initial_zero sem_map ->
  Semantics.statements_tmap modules scope sem_map (sem_stmts ss) =
    Some (final_scope, final) ->
  semantic_implicit_initial_zero final.
Proof.
  move: scope sem_map; elim: ss => [|s ss IH] scope sem_map Hzero /=.
  - by move=> H; inversion H; subst.
  - case Hstep: (Semantics.statement_tmap modules scope sem_map (sem_stmt s))
      => [[next_scope next]|] //=.
    move=> Hrest.
    apply: (IH next_scope next _ Hrest).
    case: s Hstep => [|id ty|id ty clock rst|id e] /= Hstep.
    + by inversion Hstep; subst.
    + case: (SemSyntax.VM.find id sem_map) Hstep => [[t k]|] //= Hstep.
      inversion Hstep; subst. exact: semantic_initial_zero_add Hzero.
    + case: (SemSyntax.VM.find id sem_map) Hstep => [[t k]|] //= Hstep.
      inversion Hstep; subst. exact: semantic_initial_zero_add Hzero.
    + case: (Semantics.VS.mem id scope) Hstep => //= Hstep.
      case: (SemSyntax.VM.find id sem_map) Hstep => [[t k]|] //= Hstep.
      case: (Semantics.type_of_expr (Some scope) sem_map (sem_expr e)) Hstep => [et|] //= Hstep.
      case: (Semantics.ftype_mux false t et) Hstep => [mt|] //= Hstep.
      by inversion Hstep; subst.
Qed.

Theorem semantic_initial_map_zero m initial sem_map :
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  SemSyntax.VM.find (common_module_name m) initial = Some sem_map ->
  semantic_implicit_initial_zero sem_map.
Proof.
  rewrite /Semantics.circuit_tmap_uninferred /sem_circuit /sem_module /=.
  case Hports: (Semantics.ports_tmap (map sem_port (common_ports m))) => [ports|] //=.
  case Hstmts: (Semantics.statements_tmap (sem_circuit m)
      (Semantics.VKS.key_set ports) ports (sem_stmts (common_stmts m)))
    => [[scope final]|] //=.
  move=> Hinitial; inversion Hinitial; subst initial.
  rewrite SemSyntax.VM.Lemmas.find_add_eq //= => Hfind.
  inversion Hfind; subst sem_map.
  exact: (semantic_statements_initial_zero (semantic_ports_initial_zero Hports) Hstmts).
Qed.

Definition semantic_map_bounded (value : Valuation) (sem_map : sem_component_map) : Prop :=
  forall id width, semantic_implicit_width sem_map id = Some width ->
    exists bound, solver_width value id = Some bound /\ (width <= bound)%coq_nat.

Lemma semantic_initial_zero_bounded value sem_map :
  semantic_implicit_initial_zero sem_map ->
  (forall id w, semantic_implicit_width sem_map id = Some w ->
    exists bound, solver_width value id = Some bound) ->
  semantic_map_bounded value sem_map.
Proof.
  move=> Hzero Hcover id w Hwidth.
  have [bound Hfind] := Hcover id w Hwidth.
  exists bound; split; first exact Hfind.
  by rewrite (Hzero id w Hwidth); apply Nat.le_0_l.
Qed.

Lemma bounded_common_rhs solver_map sem_map value e ty width :
  scalar_maps_related solver_map sem_map ->
  semantic_map_bounded value sem_map ->
  Semantics.type_of_expr None sem_map (sem_expr e) = Some ty ->
  sem_numeric_width ty = Some width ->
  exists rhs bound,
    common_rhs solver_map e = Some rhs /\
    min_rhs_value value (Expr rhs) = Some (Z.of_nat bound) /\
    (width <= bound)%coq_nat.
Proof.
  move=> Hmaps Hbounded.
  case: e => [id|w bits|w bits] /=.
  - rewrite /Semantics.type_of_expr /=.
    case Hsem: (SemSyntax.VM.find id sem_map) => [[mt kind]|] //=.
    move=> [<-] Hwidth.
    move: (Hmaps id); rewrite Hsem.
    case Hsolver: (SolverSyntax.VM.find id solver_map) => [[st orient]|] //= Hrel.
    inversion Hrel; subst; simpl in Hwidth; try discriminate;
      inversion Hwidth; subst width.
    + have Hwidth' : semantic_implicit_width sem_map id = Some mw
        by rewrite /semantic_implicit_width Hsem.
      have [bound [Hfind Hle]] := Hbounded id mw Hwidth'.
      exists (make_rhs [:: (1, (id, N0))] [::] 0%Z), bound.
      split; first by rewrite /common_rhs ?Hsolver.
      split; last exact Hle.
      rewrite /solver_width in Hfind.
      by rewrite /min_rhs_value /make_rhs /= /terms_value /= Hfind /= Z.add_0_r mul1n.
    + have Hwidth' : semantic_implicit_width sem_map id = Some mw
        by rewrite /semantic_implicit_width Hsem.
      have [bound [Hfind Hle]] := Hbounded id mw Hwidth'.
      exists (make_rhs [:: (1, (id, N0))] [::] 0%Z), bound.
      split; first by rewrite /common_rhs ?Hsolver.
      split; last exact Hle.
      rewrite /solver_width in Hfind.
      by rewrite /min_rhs_value /make_rhs /= /terms_value /= Hfind /= Z.add_0_r mul1n.
    + exists (make_rhs [::] [::] (Z.of_nat w)), w.
      by rewrite /common_rhs ?Hsolver /= /min_rhs_value /terms_value /power_value /=
        Z.add_0_r; repeat split.
    + exists (make_rhs [::] [::] (Z.of_nat w)), w.
      by rewrite /common_rhs ?Hsolver /= /min_rhs_value /terms_value /power_value /=
        Z.add_0_r; repeat split.
  - rewrite /Semantics.type_of_expr /=.
    case: (w < size bits) => //= Hty Hwidth.
    inversion Hty; subst ty. simpl in Hwidth. inversion Hwidth; subst width.
    exists (make_rhs [::] [::] (Z.of_nat w)), w.
    by rewrite /common_rhs /min_rhs_value /terms_value /power_value /= Z.add_0_r; repeat split.
  - rewrite /Semantics.type_of_expr /=.
    case: (w < size bits) => //= Hty Hwidth.
    inversion Hty; subst ty. simpl in Hwidth. inversion Hwidth; subst width.
    exists (make_rhs [::] [::] (Z.of_nat w)), w.
    by rewrite /common_rhs /min_rhs_value /terms_value /power_value /= Z.add_0_r; repeat split.
Qed.

Lemma bounded_satisfied_source solver_map sem_map value id e :
  scalar_maps_related solver_map sem_map ->
  semantic_map_bounded value sem_map ->
  semantic_operands sem_map id e ->
  common_step_satisfied value solver_map (CConnect id e) ->
  exists bound source width,
    solver_width value id = Some bound /\
    Semantics.type_of_expr None sem_map (sem_expr e) = Some source /\
    sem_numeric_width source = Some width /\
    (width <= bound)%coq_nat.
Proof.
  move=> Hmaps Hbounded [dest [kind [lhs [source [width
    [Hdest [Himplicit [Hexpr Hwidth]]]]]]]] Hsat.
  have [rhs [rhsbound [Hrhs [Heval Hle]]]] :=
    bounded_common_rhs Hmaps Hbounded Hexpr Hwidth.
  have Hdestwidth : semantic_implicit_width sem_map id = Some lhs.
  { rewrite /semantic_implicit_width Hdest.
    by case: Himplicit => ->. }
  have [bound [Hfind _]] := Hbounded id lhs Hdestwidth.
  have Hsolver : exists st orient,
      SolverSyntax.VM.find id solver_map = Some (st, orient) /\
      (exists w, st = HiEnv.Gtyp (Env.Fuint_implicit w) \/
                 st = HiEnv.Gtyp (Env.Fsint_implicit w)).
  { move: (Hmaps id); rewrite Hdest.
    case Hlookup: (SolverSyntax.VM.find id solver_map) => [[st orient]|] //= Hrel.
    destruct Himplicit as [Himplicit|Himplicit]; subst dest;
      inversion Hrel; subst.
    - exists (HiEnv.Gtyp (Env.Fuint_implicit sw)), orient.
      split; first reflexivity. by exists sw; left.
    - exists (HiEnv.Gtyp (Env.Fsint_implicit sw)), orient.
      split; first reflexivity. by exists sw; right. }
  destruct Hsolver as [st [orient [Hsolver [sw [Huint|Hsint]]]]];
    subst st;
    rewrite /common_step_satisfied Hsolver Hrhs in Hsat;
    rewrite common_constraint_satisfaction Hfind Heval in Hsat;
    apply Z.leb_le in Hsat; apply Nat2Z.inj_le in Hsat;
    exists bound, source, width; repeat split; try assumption.
  all: eapply Nat.le_trans; eassumption.
Qed.

Lemma covered_initial_semantic_map value initial module_id before :
  SemSyntax.VM.find module_id initial = Some before ->
  covered value initial module_id ->
  forall id w, semantic_implicit_width before id = Some w ->
    exists bound, solver_width value id = Some bound.
Proof.
  move=> Hfind Hcovered id w Hwidth.
  apply: Hcovered.
  rewrite /original_implicit Hfind.
  rewrite /semantic_implicit_width in Hwidth.
  case Hlookup: (SemSyntax.VM.find id before) => [[ty kind]|] // in Hwidth *.
  clear Hlookup.
  case: ty Hwidth => [gt|elt n|fields] //.
  by case: gt => [n|n|n|n| | | |] //=.
Qed.

Theorem covered_initial_valuation_bounds m initial before value :
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  SemSyntax.VM.find (common_module_name m) initial = Some before ->
  covered value initial (common_module_name m) ->
  semantic_map_bounded value before.
Proof.
  move=> Hinitial Hbefore Hcovered.
  apply: semantic_initial_zero_bounded.
  - exact: (semantic_initial_map_zero Hinitial Hbefore).
  - exact: (covered_initial_semantic_map Hbefore Hcovered).
Qed.

Lemma scalar_unify_source_unchanged st sr dest source newdest newsource :
  scalar_type_relation st dest ->
  scalar_type_relation sr source ->
  Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest source =
    Some (newdest, newsource) ->
  newsource = source.
Proof.
  move=> Hdest Hsource Hunify.
  inversion Hdest; subst; inversion Hsource; subst; simpl in Hunify;
    repeat match goal with
      | H : context [match ?n with 0 => _ | S _ => _ end] |- _ => destruct n
    end;
    simpl in Hunify; try discriminate; by inversion Hunify.
Qed.

Lemma implicit_unify_target_shape sr dest source newdest newsource lhs :
  scalar_type_relation sr source ->
  (dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit lhs) \/
   dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit lhs)) ->
  Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest source =
    Some (newdest, newsource) ->
  exists width, sem_numeric_width source = Some width /\
    (newdest = HiEnv_with_implicit_widths.Gtyp
       (Env_with_implicit_widths.Fuint_implicit (maxn lhs width)) \/
     newdest = HiEnv_with_implicit_widths.Gtyp
       (Env_with_implicit_widths.Fsint_implicit (maxn lhs width))).
Proof.
  move=> Hsource [Huint|Hsint] Hunify; subst dest;
    inversion Hsource; subst; simpl in Hunify;
    repeat match goal with
      | H : context [match ?n with 0 => _ | S _ => _ end] |- _ => destruct n
    end;
    simpl in Hunify; try discriminate; inversion Hunify; subst;
    try (eexists; split; first reflexivity; first [left; reflexivity | right; reflexivity]).
Qed.

Lemma semantic_map_bounded_add value sem_map id ty kind :
  semantic_map_bounded value sem_map ->
  (forall w,
    (ty = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit w) \/
     ty = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit w)) ->
    exists bound, solver_width value id = Some bound /\ (w <= bound)%coq_nat) ->
  semantic_map_bounded value (SemSyntax.VM.add id (ty, kind) sem_map).
Proof.
  move=> Hbounded Hnew key w.
  rewrite /semantic_implicit_width.
  case Hsame: (key == id).
  - move/eqP: Hsame => ->.
    rewrite SemSyntax.VM.Lemmas.find_add_eq //=.
    case: ty Hnew => [gt|elt n|fields] Hnew //.
    case: gt Hnew => [n|n|n|n| | | |] Hnew //= H; inversion H; subst w.
    + exact: Hnew _ (or_introl erefl).
    + exact: Hnew _ (or_intror erefl).
  - have Hneq : ~ (key == id) by move/negP: Hsame.
    rewrite (SemSyntax.VM.Lemmas.find_add_neq Hneq).
    exact: Hbounded.
Qed.

Lemma semantic_bounded_add_existing value sem_map id ty kind :
  semantic_map_bounded value sem_map ->
  SemSyntax.VM.find id sem_map = Some (ty, kind) ->
  semantic_map_bounded value (SemSyntax.VM.add id (ty, kind) sem_map).
Proof.
  move=> Hbounded Hfind.
  apply: (semantic_map_bounded_add (id := id) (ty := ty) (kind := kind) Hbounded).
  move=> w [Hty|Hty]; subst ty; apply: Hbounded;
    by rewrite /semantic_implicit_width Hfind.
Qed.

Lemma bounded_unify_target_update solver_map sem_map value id e dest kind source newdest newsource :
  scalar_maps_related solver_map sem_map ->
  semantic_map_bounded value sem_map ->
  SemSyntax.VM.find id sem_map = Some (dest, kind) ->
  Semantics.type_of_expr None sem_map (sem_expr e) = Some source ->
  Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest source =
    Some (newdest, newsource) ->
  (forall lhs,
    (dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit lhs) \/
     dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit lhs)) ->
    common_step_satisfied value solver_map (CConnect id e)) ->
  semantic_map_bounded value (SemSyntax.VM.add id (newdest, kind) sem_map).
Proof.
  move=> Hmaps Hbounded Hdest Hexpr Hunify Hsat.
  have [st Hst] := related_semantic_lookup Hmaps Hdest.
  have [sr Hsr] := common_expr_is_semantic_scalar Hmaps Hexpr.
  have [Hgrow _] := scalar_unify_growth Hst Hsr Hunify.
  apply: (semantic_map_bounded_add (id := id) (ty := newdest) (kind := kind) Hbounded).
  move=> w Hnew.
  inversion Hgrow; subst;
    try (destruct Hnew as [Hbad|Hbad]; discriminate).
  all: match type of Hdest with
    | _ = Some (?target, _) =>
        assert (Himplicit : target =
          HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit a) \/
          target = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit a))
          by first [left; reflexivity | right; reflexivity]
    end.
  all: have [width [Hwidth Hshape]] :=
      implicit_unify_target_shape Hsr Himplicit Hunify.
  all: have Hready : semantic_operands sem_map id e.
  all: try solve [do 5 eexists; repeat split; eauto].
  all: have [bound [source' [width' [Hfind [Hexpr' [Hwidth' Hle]]]]]] :=
      bounded_satisfied_source Hmaps Hbounded Hready (Hsat a Himplicit).
  all: rewrite Hexpr in Hexpr'; inversion Hexpr'; subst source'.
  all: rewrite Hwidth in Hwidth'; inversion Hwidth'; subst width'.
  all: have Hbefore : semantic_implicit_width sem_map id = Some a
    by rewrite /semantic_implicit_width Hdest.
  all: have [oldbound [Hold Hbound]] := Hbounded id a Hbefore.
  all: rewrite Hfind in Hold; inversion Hold; subst oldbound.
  all: destruct Hshape as [Hshape|Hshape]; destruct Hnew as [Hnew|Hnew];
    rewrite Hshape in Hnew; try discriminate;
    inversion Hnew; subst w.
  all: exists bound; split; first exact Hfind.
  all: apply/leP; rewrite geq_max; apply/andP; split; apply/leP; assumption.
Qed.

Lemma common_reg_satisfied_connect solver_map sem_map value id ty clock trigger e dest kind lhs :
  scalar_maps_related solver_map sem_map ->
  SolverSyntax.VM.find id solver_map = Some (solver_type ty, SolverSyntax.Duplex) ->
  SemSyntax.VM.find id sem_map = Some (dest, kind) ->
  (dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint_implicit lhs) \/
   dest = HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint_implicit lhs)) ->
  common_step_satisfied value solver_map (CReg id ty clock (CReset trigger e)) ->
  common_step_satisfied value solver_map (CConnect id e).
Proof.
  move=> Hmaps Hsolver Hdest Himplicit Hsat.
  have Hrelation := Hmaps id.
  rewrite Hsolver Hdest in Hrelation.
  case: ty Hsolver Hrelation Hsat => [| |w|w] Hsolver Hrelation Hsat /=.
  - by rewrite /common_step_satisfied Hsolver.
  - by rewrite /common_step_satisfied Hsolver.
  - destruct Himplicit as [Himplicit|Himplicit]; subst dest; inversion Hrelation.
  - destruct Himplicit as [Himplicit|Himplicit]; subst dest; inversion Hrelation.
Qed.

Lemma common_width_step_preserves_bound solver_map sem_map result value s :
  scalar_maps_related solver_map sem_map ->
  semantic_map_bounded value sem_map ->
  registers_match_solver_map solver_map [:: s] ->
  common_step_satisfied value solver_map s ->
  Semantics.width_iter_one sem_map (sem_stmt s) = Some result ->
  semantic_map_bounded value result.
Proof.
  move=> Hmaps Hbounded Hregs Hsat.
  case: s Hregs Hsat => [|id ty|id ty clock rst|id e] Hregs Hsat /=.
  - by move=> [<-].
  - by move=> [<-].
  - case: rst Hregs Hsat => [|trigger e] Hregs Hsat /=.
    + by move=> [<-].
    + case Hdest: (SemSyntax.VM.find id sem_map) => [[dest kind]|] //=.
      case: kind Hdest => //= Hdest.
      case Hexpr: (Semantics.type_of_expr None sem_map (sem_expr e)) => [source|] //=.
      case: (HiEnv_with_implicit_widths.is_passive dest &&
             HiEnv_with_implicit_widths.is_passive source) => //=.
      case Hunify: (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest source)
        => [[newdest newsource]|] //=.
      move=> Hresult; inversion Hresult; subst result.
      apply: (bounded_unify_target_update Hmaps Hbounded Hdest Hexpr Hunify).
      move=> lhs Himplicit.
      apply: (common_reg_satisfied_connect Hmaps _ Hdest Himplicit Hsat).
      exact: (Hregs id ty clock (CReset trigger e) (or_introl erefl)).
  - clear Hregs.
    case: e Hsat => [src|w bits|w bits] Hsat /=.
    + case Hdest: (SemSyntax.VM.find id sem_map) => [[dest kind]|] //=.
      case Hsrc: (SemSyntax.VM.find src sem_map) => [[source skind]|] //=.
      case Hunify: (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest source)
        => [[newdest newsource]|] //=.
      have [st Hst] := related_semantic_lookup Hmaps Hdest.
      have [sr Hsr] := related_semantic_lookup Hmaps Hsrc.
      have Hsourceeq := scalar_unify_source_unchanged Hst Hsr Hunify.
      subst newsource.
      have Hexpr : Semantics.type_of_expr None sem_map (sem_expr (CRef src)) = Some source
        by rewrite /Semantics.type_of_expr /= Hsrc.
      case Hsame: (src == id).
      * move/eqP: Hsame => Hsame; subst src.
        rewrite Hdest in Hsrc. inversion Hsrc; subst source skind.
        rewrite SemSyntax.VM.Lemmas.find_add_eq //=.
        move=> Hresult; inversion Hresult; subst result.
        apply: (semantic_map_bounded_add (id := id) (ty := dest) (kind := kind)).
        -- apply: (bounded_unify_target_update Hmaps Hbounded Hdest Hexpr Hunify).
           by move=> lhs _.
        --
        move=> lhs Himplicit.
        apply: Hbounded.
        rewrite /semantic_implicit_width Hdest.
        by case: Himplicit => ->.
      * have Hneq : ~ (src == id) by move/negP: Hsame.
        rewrite (SemSyntax.VM.Lemmas.find_add_neq Hneq) Hsrc /=.
        move=> Hresult; inversion Hresult; subst result.
        apply: semantic_bounded_add_existing.
        -- apply: (bounded_unify_target_update Hmaps Hbounded Hdest Hexpr Hunify).
           by move=> lhs _.
        -- by rewrite (SemSyntax.VM.Lemmas.find_add_neq Hneq).
    + case Hdest: (SemSyntax.VM.find id sem_map) => [[dest kind]|] //=.
      rewrite /Semantics.type_of_expr /=.
      case Hvalid: (w < size bits) => //=.
      case Hunify: (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest
          (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint w)))
        => [[newdest newsource]|] //=.
      move=> Hresult; inversion Hresult; subst result.
      have Hexpr : Semantics.type_of_expr None sem_map (sem_expr (CUInt w bits)) =
          Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fuint w))
        by rewrite /Semantics.type_of_expr /= Hvalid.
      apply: (bounded_unify_target_update Hmaps Hbounded Hdest Hexpr Hunify).
      by move=> lhs _.
    + case Hdest: (SemSyntax.VM.find id sem_map) => [[dest kind]|] //=.
      rewrite /Semantics.type_of_expr /=.
      case Hvalid: (w < size bits) => //=.
      case Hunify: (Semantics.unify_width HiEnv_with_implicit_widths.Nflip dest
          (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint w)))
        => [[newdest newsource]|] //=.
      move=> Hresult; inversion Hresult; subst result.
      have Hexpr : Semantics.type_of_expr None sem_map (sem_expr (CSInt w bits)) =
          Some (HiEnv_with_implicit_widths.Gtyp (Env_with_implicit_widths.Fsint w))
        by rewrite /Semantics.type_of_expr /= Hvalid.
      apply: (bounded_unify_target_update Hmaps Hbounded Hdest Hexpr Hunify).
      by move=> lhs _.
Qed.

Lemma common_width_iter_preserves_bound solver_map sem_map result value ss :
  scalar_maps_related solver_map sem_map ->
  semantic_map_bounded value sem_map ->
  registers_match_solver_map solver_map ss ->
  List.Forall (common_step_satisfied value solver_map) ss ->
  Semantics.width_iter sem_map (sem_stmts ss) = Some result ->
  semantic_map_bounded value result.
Proof.
  move: sem_map; elim: ss => [|s ss IH] sem_map Hmaps Hbounded Hregs Hsat /=.
  - by move=> [<-].
  - inversion Hsat as [|s' ss' Hfirst Htail]; subst.
    case Hstep: (Semantics.width_iter_one sem_map (sem_stmt s)) => [next|] //=.
    move=> Hrest.
    have Hregfirst : registers_match_solver_map solver_map [:: s].
    { move=> id ty clock rst [Heq|[]]. apply: Hregs. left. exact Heq. }
    have Hregtail : registers_match_solver_map solver_map ss.
    { move=> id ty clock rst Hin. apply: Hregs. right. exact Hin. }
    have Hnextbounded := common_width_step_preserves_bound Hmaps Hbounded Hregfirst Hfirst Hstep.
    have Hgrowth := common_width_iter_one_growth Hmaps Hstep.
    have Hnextmaps := semantic_growth_preserves_related Hmaps Hgrowth.
    exact: (IH next Hnextmaps Hnextbounded Hregtail Htail Hrest).
Qed.

Theorem common_circuit_iterator_preserves_bound solver_map m n circ sem_map result value :
  scalar_maps_related solver_map sem_map ->
  semantic_map_bounded value sem_map ->
  registers_match_solver_map solver_map (common_stmts m) ->
  List.Forall (common_step_satisfied value solver_map) (common_stmts m) ->
  SemSyntax.VM.find (common_module_name m) circ = Some sem_map ->
  Semantics.circuit_tmap_iterator (sem_circuit m) n circ = Some result ->
  exists sem_result,
    SemSyntax.VM.find (common_module_name m) result = Some sem_result /\
    semantic_map_bounded value sem_result.
Proof.
  move: circ sem_map.
  elim: n => [|n IH] circ sem_map Hmaps Hbounded Hregs Hsat Hfind /=.
  - move=> Hresult; inversion Hresult; subst result.
    by exists sem_map.
  - case Hiter: (Semantics.circuit_width_iter (sem_circuit m) circ) => [nextcirc|] //=.
    move=> Hrest.
    have [next [Hwidth [Hgrowth Hnext]]] :=
      common_circuit_width_iter Hmaps Hfind Hiter.
    subst nextcirc.
    have Hnextbounded := common_width_iter_preserves_bound Hmaps Hbounded Hregs Hsat Hwidth.
    have Hnextmaps := semantic_growth_preserves_related Hmaps Hgrowth.
    apply: (IH _ next Hnextmaps Hnextbounded Hregs Hsat _ Hrest).
    by rewrite SemSyntax.VM.Lemmas.find_add_eq // eqxx.
Qed.

Theorem satisfying_valuation_bounds_successful_semantic_result
    solver_map m circuit_name n initial result cmap value :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  extract_constraints_c (solver_circuit circuit_name m) solver_map =
    Some ([:: cmap], [::]) ->
  covered value initial (common_module_name m) ->
  List.forallb (satisfies_constraint1 value)
    (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true ->
  exists sem_map,
    SemSyntax.VM.find (common_module_name m) result = Some sem_map /\
    semantic_map_bounded value sem_map /\
    forall id, original_implicit initial (common_module_name m) id ->
      exists width bound,
        semantic_width result (common_module_name m) id = Some width /\
        solver_width value id = Some bound /\
        (width <= bound)%coq_nat.
Proof.
  move=> Hsolver Hinitial Hresult Hextract Hcover Hsat.
  have [before [Hbefore Hmaps]] := initial_circuit_tmaps_related Hsolver Hinitial.
  have Hbounded := covered_initial_valuation_bounds Hinitial Hbefore Hcover.
  have Hscalar := scalar_maps_related_is_scalar Hmaps.
  have Hmap_sat : constraint_map_satisfied value cmap.
  { apply (proj2 (constraint_map_satisfied_flattened value cmap)). exact Hsat. }
  have Hsat_rev := (proj1 (extract_common_circuit_satisfied value Hscalar Hextract)) Hmap_sat.
  have Hsat_forward : List.Forall (common_step_satisfied value solver_map) (common_stmts m).
  { have Hrev := forall_mathcomp_rev Hsat_rev. by rewrite revK in Hrev. }
  have Hregs : registers_match_solver_map solver_map (common_stmts m).
  { move=> id ty clock rst Hin. exact: (solver_circuit_register_lookup Hsolver Hin). }
  have [initial_before [after [Hinitial_before [Hafter [Hgrowth _]]]]] :=
    common_successful_result_growth Hsolver Hinitial Hresult.
  rewrite Hbefore in Hinitial_before. inversion Hinitial_before; subst initial_before.
  have Hactual := Hresult.
  rewrite /Semantics.circuit_tmap_implicits Hinitial in Hactual.
  case Hiter: (Semantics.circuit_tmap_iterator (sem_circuit m) n initial)
    => [iterated|] //= in Hactual.
  case: (Semantics.circuit_width_iter (sem_circuit m) iterated) => [next|] //= in Hactual.
  case: (SemSyntax.VM.equal (SemSyntax.VM.equal pair_eq) iterated next) => //= in Hactual.
  inversion Hactual; subst iterated.
  have [bounded_map [Hbounded_find Hbounded_final]] :=
    common_circuit_iterator_preserves_bound Hmaps Hbounded Hregs Hsat_forward Hbefore Hiter.
  rewrite Hafter in Hbounded_find. inversion Hbounded_find; subst bounded_map.
  exists after; repeat split; try assumption.
  move=> id Horiginal.
  rewrite /original_implicit Hbefore in Horiginal.
  have [w Hwidth] : exists w, semantic_implicit_width before id = Some w.
  { rewrite /semantic_implicit_width.
    case: (SemSyntax.VM.find id before) Horiginal => [[ty kind]|] //.
    case: ty => [gt|elt len|fields] //.
    by case: gt => [w|w|w|w| | | |] //= _; exists w. }
  have [width [Hfinalwidth _]] := semantic_growth_implicit_width Hgrowth Hwidth.
  have [bound [Hvalue Hle]] := Hbounded_final id width Hfinalwidth.
  exists width, bound; repeat split; try assumption.
  rewrite /semantic_width Hafter.
  exact Hfinalwidth.
Qed.

Lemma semantic_map_bounded_valuation_le value sem_map :
  semantic_map_bounded value sem_map ->
  constraints.le (semantic_valuation sem_map) value.
Proof.
  move=> Hbounded [id offset] width Hfind.
  destruct (N.eq_dec offset N0) as [Heq|Hneq].
  - subst offset.
    have Hwidth : semantic_implicit_width sem_map id = Some width.
    { rewrite -semantic_valuation_find. exact Hfind. }
    have [bound [Hvalue Hle]] := Hbounded id width Hwidth.
    exists bound; split; first exact Hvalue.
    exact/leP.
  - rewrite (semantic_valuation_nonzero sem_map id Hneq) in Hfind.
    discriminate.
Qed.

Corollary semantic_result_valuation_le_satisfying_valuation
    solver_map m circuit_name n initial result cmap value :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  extract_constraints_c (solver_circuit circuit_name m) solver_map =
    Some ([:: cmap], [::]) ->
  covered value initial (common_module_name m) ->
  List.forallb (satisfies_constraint1 value)
    (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true ->
  exists sem_map,
    SemSyntax.VM.find (common_module_name m) result = Some sem_map /\
    constraints.le (semantic_valuation sem_map) value.
Proof.
  move=> Hsolver Hinitial Hresult Hextract Hcover Hsat.
  have [sem_map [Hfind [Hbounded _]]] :=
    satisfying_valuation_bounds_successful_semantic_result
      Hsolver Hinitial Hresult Hextract Hcover Hsat.
  exists sem_map; split; first exact Hfind.
  exact: semantic_map_bounded_valuation_le Hbounded.
Qed.

Fixpoint overlay_semantic_ids (sem_map : sem_component_map) (ids : seq var)
    (base : Valuation) : Valuation :=
  match ids with
  | [::] => base
  | id :: rest =>
      match semantic_implicit_width sem_map id with
      | Some w => SolverSyntax.PVM.add (id, N0) w (overlay_semantic_ids sem_map rest base)
      | None => overlay_semantic_ids sem_map rest base
      end
  end.

Definition extended_semantic_valuation (sem_map : sem_component_map) (base : Valuation)
    : Valuation :=
  overlay_semantic_ids sem_map (map fst (SemSyntax.VM.elements sem_map)) base.

Lemma overlay_semantic_ids_find sem_map ids base id :
  solver_width (overlay_semantic_ids sem_map ids base) id =
    if id \in ids then
      match semantic_implicit_width sem_map id with
      | Some w => Some w
      | None => solver_width base id
      end
    else solver_width base id.
Proof.
  elim: ids => [|first rest IH] /=.
  - reflexivity.
  - case Hfirst: (semantic_implicit_width sem_map first) => [w|].
    + rewrite /solver_width /=.
      case Hsame: (id == first).
      * move/eqP: Hsame => ->.
        by rewrite SolverSyntax.PVM.Lemmas.F.add_eq_o //= Hfirst in_cons eqxx.
      * have Hneq : ~ SolverSyntax.ProdVar.eq (first, N0) (id, N0).
        { move=> Heq. apply eq_from_prodvar_eq in Heq.
          inversion Heq; subst. by rewrite eqxx in Hsame. }
        rewrite SolverSyntax.PVM.Lemmas.F.add_neq_o //.
        change (solver_width (overlay_semantic_ids sem_map rest base) id =
          if id \in first :: rest then
            match semantic_implicit_width sem_map id with
            | Some w => Some w | None => solver_width base id end
          else solver_width base id).
        by rewrite IH in_cons Hsame /=.
    + change (solver_width (overlay_semantic_ids sem_map rest base) id =
        if id \in first :: rest then
          match semantic_implicit_width sem_map id with
          | Some w => Some w | None => solver_width base id end
        else solver_width base id).
      rewrite IH in_cons.
      case Hsame: (id == first) => //=.
      move/eqP: Hsame => ->. by rewrite Hfirst; case: (first \in rest).
Qed.

Theorem extended_semantic_valuation_find sem_map base id :
  solver_width (extended_semantic_valuation sem_map base) id =
    match semantic_implicit_width sem_map id with
    | Some w => Some w
    | None => solver_width base id
    end.
Proof.
  rewrite /extended_semantic_valuation overlay_semantic_ids_find.
  case Hwidth: (semantic_implicit_width sem_map id) => [w|].
  - rewrite /semantic_implicit_width in Hwidth.
    case Hfind: (SemSyntax.VM.find id sem_map) => [[ty kind]|] // in Hwidth.
    by rewrite (semantic_find_in_element_ids Hfind).
  - by case: (id \in map fst (SemSyntax.VM.elements sem_map)).
Qed.

Lemma overlay_semantic_ids_nonzero sem_map ids base id offset :
  offset <> N0 ->
  SolverSyntax.PVM.find (id, offset) (overlay_semantic_ids sem_map ids base) =
    SolverSyntax.PVM.find (id, offset) base.
Proof.
  move=> Hnonzero; elim: ids => [|first rest IH] /=.
  - reflexivity.
  - case: (semantic_implicit_width sem_map first) => [w|]; last exact IH.
    rewrite SolverSyntax.PVM.Lemmas.F.add_neq_o; first exact IH.
    move=> Heq. apply eq_from_prodvar_eq in Heq.
    inversion Heq; subst offset. exact: Hnonzero erefl.
Qed.

Corollary extended_semantic_valuation_nonzero sem_map base id offset :
  offset <> N0 ->
  SolverSyntax.PVM.find (id, offset) (extended_semantic_valuation sem_map base) =
    SolverSyntax.PVM.find (id, offset) base.
Proof. exact: overlay_semantic_ids_nonzero. Qed.

Lemma extended_semantic_valuation_matches sem_map base :
  valuation_matches_sem_map (extended_semantic_valuation sem_map base) sem_map.
Proof.
  move=> id ty kind w Hfind [Hty|Hty]; subst ty;
    by rewrite extended_semantic_valuation_find /semantic_implicit_width Hfind.
Qed.

Lemma extended_semantic_valuation_domain sem_map base key w :
  SolverSyntax.PVM.find key base = Some w ->
  exists w', SolverSyntax.PVM.find key (extended_semantic_valuation sem_map base) = Some w'.
Proof.
  move=> Hfind.
  destruct key as [id offset].
  destruct (N.eq_dec offset N0) as [->|Hneq].
  - change (solver_width base id = Some w) in Hfind.
    change (exists w', solver_width (extended_semantic_valuation sem_map base) id = Some w').
    rewrite extended_semantic_valuation_find.
    by case: (semantic_implicit_width sem_map id) => [w'|]; eauto.
  - exists w.
    by rewrite extended_semantic_valuation_nonzero.
Qed.

Lemma extended_semantic_valuation_covered sem_map base initial module_id :
  covered (semantic_valuation sem_map) initial module_id ->
  covered (extended_semantic_valuation sem_map base) initial module_id.
Proof.
  move=> Hcovered id Horiginal.
  have [w Hfind] := Hcovered id Horiginal.
  rewrite semantic_valuation_find in Hfind.
  exists w. by rewrite extended_semantic_valuation_find Hfind.
Qed.

Theorem extended_result_valuation_satisfies_constraints
    solver_map m circuit_name n initial result cmap base :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  extract_constraints_c (solver_circuit circuit_name m) solver_map =
    Some ([:: cmap], [::]) ->
  exists sem_map,
    SemSyntax.VM.find (common_module_name m) result = Some sem_map /\
    valuation_matches_sem_map (extended_semantic_valuation sem_map base) sem_map /\
    covered (extended_semantic_valuation sem_map base) initial (common_module_name m) /\
    List.forallb (satisfies_constraint1 (extended_semantic_valuation sem_map base))
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true /\
    (forall key w, SolverSyntax.PVM.find key base = Some w ->
      exists w', SolverSyntax.PVM.find key (extended_semantic_valuation sem_map base) =
        Some w').
Proof.
  move=> Hsolver Hinitial Hresult Hextract.
  have [sem_map [Hfind [_ Hcovered]]] :=
    semantic_result_valuation_covers_original Hsolver Hinitial Hresult.
  have Hmatches : valuation_matches_sem_map (extended_semantic_valuation sem_map base) sem_map
    by apply: extended_semantic_valuation_matches.
  have [other [Hother Hsat]] :=
    successful_result_matching_valuation_satisfies_constraints
      (extended_semantic_valuation sem_map base) Hsolver Hinitial Hresult Hextract.
  rewrite Hfind in Hother. inversion Hother; subst other.
  exists sem_map; split; first exact Hfind.
  split; first exact Hmatches.
  split; first exact: extended_semantic_valuation_covered Hcovered.
  split; first exact: Hsat Hmatches.
  exact: extended_semantic_valuation_domain.
Qed.

Definition valuation_domain_covers (candidate required : Valuation) : Prop :=
  forall key w, SolverSyntax.PVM.find key required = Some w ->
    exists w', SolverSyntax.PVM.find key candidate = Some w'.

Definition solver_solution_contract initial module_id cmap solution : Prop :=
  List.forallb (satisfies_constraint1 solution)
    (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true /\
  forall candidate,
    covered candidate initial module_id ->
    valuation_domain_covers candidate solution ->
    List.forallb (satisfies_constraint1 candidate)
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true ->
    constraints.le solution candidate.

Theorem conditional_single_module_min_solution_matches_fixed_point
    solver_map m circuit_name n initial result cmap solution :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  extract_constraints_c (solver_circuit circuit_name m) solver_map =
    Some ([:: cmap], [::]) ->
  covered solution initial (common_module_name m) ->
  solver_solution_contract initial (common_module_name m) cmap solution ->
  forall id, original_implicit initial (common_module_name m) id ->
    exists w,
      solver_width solution id = Some w /\
      semantic_width result (common_module_name m) id = Some w.
Proof.
  move=> Hsolver Hinitial Hresult Hextract Hcover [Hsat Hminimal] id Horiginal.
  have [sem_map [Hfind [_ [Hextendedcover [Hextendedsat Hextendeddomain]]]]] :=
    extended_result_valuation_satisfies_constraints solution
      Hsolver Hinitial Hresult Hextract.
  have Hle := Hminimal (extended_semantic_valuation sem_map solution)
    Hextendedcover Hextendeddomain Hextendedsat.
  have [other [Hother [_ Hupper]]] :=
    satisfying_valuation_bounds_successful_semantic_result
      Hsolver Hinitial Hresult Hextract Hcover Hsat.
  rewrite Hfind in Hother. inversion Hother; subst other.
  have [width [bound [Hsemantic [Hvalue Hwidthle]]]] := Hupper id Horiginal.
  have [upper [Hextended Hboundle]] :=
    Hle (id, N0) bound Hvalue.
  have Hwidth : semantic_implicit_width sem_map id = Some width.
  { rewrite /semantic_width Hfind in Hsemantic. exact Hsemantic. }
  change (solver_width (extended_semantic_valuation sem_map solution) id = Some upper) in Hextended.
  rewrite extended_semantic_valuation_find Hwidth in Hextended.
  inversion Hextended; subst upper.
  have Heq : bound = width by apply Nat.le_antisymm; [exact/leP | exact Hwidthle].
  subst bound. by exists width.
Qed.

Lemma successful_single_module_solver_extracts
    solver_map m circuit_name solution sem_map :
  scalar_maps_related solver_map sem_map ->
  inferWidths.solve_fun (solver_circuit circuit_name m) solver_map = Some solution ->
  exists cmap,
    extract_constraints_c (solver_circuit circuit_name m) solver_map =
      Some ([:: cmap], [::]).
Proof.
  move=> Hmaps Hsolve.
  have Hscalar := scalar_maps_related_is_scalar Hmaps.
  rewrite /inferWidths.solve_fun (extract_common_circuit m circuit_name Hscalar) in Hsolve.
  case Hextract: (common_extract_steps solver_map (SolverSyntax.PVM.empty _)
      (rev (common_stmts m))) => [cmap|] //= in Hsolve.
  exists cmap. by rewrite (extract_common_circuit m circuit_name Hscalar) Hextract.
Qed.

Corollary conditional_solve_fun_matches_fixed_point
    solver_map m circuit_name n initial result solution :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  inferWidths.solve_fun (solver_circuit circuit_name m) solver_map = Some solution ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  covered solution initial (common_module_name m) ->
  (forall cmap,
    extract_constraints_c (solver_circuit circuit_name m) solver_map =
      Some ([:: cmap], [::]) ->
    solver_solution_contract initial (common_module_name m) cmap solution) ->
  forall id, original_implicit initial (common_module_name m) id ->
    exists w,
      solver_width solution id = Some w /\
      semantic_width result (common_module_name m) id = Some w.
Proof.
  move=> Hsolver Hsolve Hinitial Hresult Hcover Hcontract.
  have [sem_map [_ Hmaps]] := initial_circuit_tmaps_related Hsolver Hinitial.
  have [cmap Hextract] := successful_single_module_solver_extracts Hmaps Hsolve.
  exact: (conditional_single_module_min_solution_matches_fixed_point
    Hsolver Hinitial Hresult Hextract Hcover (Hcontract cmap Hextract)).
Qed.

Definition solver_sccs (c : SolverSyntax.HiF.hfcircuit) (g : graph.Graph c) :=
  map (map (@SolverSyntax.finProdVar2ProdVar c))
    (rev (map rev (kosaraju g))).

Lemma sequence_membership_in (T : eqType) (x : T) (xs : seq T) :
  x \in xs -> List.In x xs.
Proof.
  elim: xs => [|y ys IH] //=.
  rewrite in_cons. move/orP => [/eqP ->|H]; first by left.
  right. exact: IH.
Qed.

Lemma sequence_in_membership (T : eqType) (x : T) (xs : seq T) :
  List.In x xs -> x \in xs.
Proof.
  elim: xs => [|y ys IH] //= [Heq|Hin].
  - subst y. by rewrite in_cons eqxx.
  - by rewrite in_cons (IH Hin) orbT.
Qed.

Lemma solver_sccs_complete c (g : graph.Graph c) (v : SolverSyntax.finProdVar c) :
  List.In (SolverSyntax.finProdVar2ProdVar v) (List.concat (solver_sccs g)).
Proof.
  have [_ Hall _] := kosaraju_correct g.
  have Hin := sequence_membership_in (Hall v).
  change (List.In v (List.concat (kosaraju g))) in Hin.
  apply List.in_concat in Hin.
  destruct Hin as [component [Hcomponent Hv]].
  rewrite /solver_sccs.
  apply List.in_concat.
  exists (map (@SolverSyntax.finProdVar2ProdVar c) (rev component)).
  split.
  - apply List.in_map.
    apply (@sequence_membership_in (Equality.clone (seq (SolverSyntax.finProdVar c)) _)).
    rewrite mem_rev.
    apply sequence_in_membership. by apply List.in_map.
  - apply List.in_map.
    apply sequence_membership_in.
    rewrite mem_rev. exact: sequence_in_membership Hv.
Qed.

Lemma sequence_uniq_nodup (T : eqType) (xs : seq T) :
  uniq xs -> List.NoDup xs.
Proof.
  elim: xs => [|x xs IH] /=; first by constructor.
  move/andP => [Hnotin Huniq]. constructor; last exact: IH.
  move=> Hin. have Hmem := sequence_in_membership Hin.
  by rewrite Hmem in Hnotin.
Qed.

Lemma solver_sccs_nodup c (g : graph.Graph c) :
  List.NoDup (List.concat (solver_sccs g)).
Proof.
  apply sequence_uniq_nodup.
  change (uniq (flatten (solver_sccs g))).
  rewrite /solver_sccs -map_flatten -rev_flatten.
  have Hinj : injective (@SolverSyntax.finProdVar2ProdVar c).
  { move=> x y Hxy. exact: val_inj Hxy. }
  rewrite (map_inj_uniq Hinj) rev_uniq.
  have [Huniq _ _] := kosaraju_correct g.
  exact Huniq.
Qed.

Lemma solver_sccs_nonempty c (g : graph.Graph c) component :
  List.In component (solver_sccs g) -> component <> [::].
Proof.
  rewrite /solver_sccs.
  move/List.in_map_iff => [inner [<- Hin]].
  have Hin' := @sequence_in_membership (Equality.clone (seq (SolverSyntax.finProdVar c)) _)
    inner _ Hin.
  rewrite mem_rev in Hin'.
  have Hin'' := @sequence_membership_in (Equality.clone (seq (SolverSyntax.finProdVar c)) _)
    inner _ Hin'.
  apply List.in_map_iff in Hin''.
  destruct Hin'' as [original [<- Horiginal]].
  have [_ _ Hcomponents] := kosaraju_correct g.
  have [x Hx] := Hcomponents original
    (@sequence_in_membership (Equality.clone (seq (SolverSyntax.finProdVar c)) _) _ _ Horiginal).
  have Hmember := Hx x.
  rewrite /extra.symconnect !connect0 in Hmember.
  move=> Hnil.
  have : List.In (SolverSyntax.finProdVar2ProdVar x)
      (map (@SolverSyntax.finProdVar2ProdVar c) (rev original)).
  { apply List.in_map. apply sequence_membership_in.
    by rewrite mem_rev Hmember. }
  by rewrite Hnil.
Qed.

Lemma solver_sccs_component_characterization c (g : graph.Graph c) component :
  List.In component (solver_sccs g) ->
  exists representative : SolverSyntax.finProdVar c,
    forall v : SolverSyntax.finProdVar c,
      (SolverSyntax.finProdVar2ProdVar v \in component) =
        extra.symconnect g representative v.
Proof.
  rewrite /solver_sccs.
  move/List.in_map_iff => [inner [<- Hin]].
  have Hin' := @sequence_in_membership (Equality.clone (seq (SolverSyntax.finProdVar c)) _)
    inner _ Hin.
  rewrite mem_rev in Hin'.
  have Hin'' := @sequence_membership_in (Equality.clone (seq (SolverSyntax.finProdVar c)) _)
    inner _ Hin'.
  apply List.in_map_iff in Hin''.
  destruct Hin'' as [original [<- Horiginal]].
  have [_ _ Hcomponents] := kosaraju_correct g.
  have [x Hx] := Hcomponents original
    (@sequence_in_membership (Equality.clone (seq (SolverSyntax.finProdVar c)) _) _ _ Horiginal).
  exists x => v.
  have Hinj : injective (@SolverSyntax.finProdVar2ProdVar c).
  { move=> a b Hab. exact: val_inj Hab. }
  by rewrite (mem_map Hinj) mem_rev Hx.
Qed.

Lemma dependency_fold_preserves c (g : graph.Graph c) (terms : list term)
    (from to : SolverSyntax.finProdVar c) (target : SolverSyntax.ProdVar.t) :
  g from to ->
  List.fold_left
    (fun current '(_, source) => graph.add_dependency current source target)
    terms g from to.
Proof.
  move: g; elim: terms => [|[coeff source] rest IH] g /= H.
  - exact H.
  - apply: IH. by rewrite /graph.add_dependency H.
Qed.

Lemma dependency_fold_contains c (g : graph.Graph c) (terms : list term)
    (from to : SolverSyntax.finProdVar c) coeff :
  List.In (coeff, SolverSyntax.finProdVar2ProdVar from) terms ->
  List.fold_left
    (fun current '(_, source) => graph.add_dependency current source
      (SolverSyntax.finProdVar2ProdVar to)) terms g from to.
Proof.
  move: g; elim: terms => [|[coeff' source] rest IH] g //= [Heq|Hin].
  - inversion Heq; subst.
    apply dependency_fold_preserves.
    by rewrite /graph.add_dependency !eqxx orbT.
  - exact: IH Hin.
Qed.

Lemma dependency_fold_origin c (g : graph.Graph c) (terms : list term)
    (from to : SolverSyntax.finProdVar c) target :
  List.fold_left
    (fun current '(_, source) => graph.add_dependency current source target)
    terms g from to ->
  g from to \/
    exists coeff, List.In (coeff, SolverSyntax.finProdVar2ProdVar from) terms /\
      target = SolverSyntax.finProdVar2ProdVar to.
Proof.
  move: g; elim: terms => [|[coeff source] rest IH] g /= H.
  - by left.
  - have [Hprevious|[n [Hin Htarget]]] := IH _ H.
    + rewrite /graph.add_dependency in Hprevious.
      move/orP: Hprevious => [Hg|/andP [/eqP Hsource /eqP Htarget]].
      * by left.
      * right. exists coeff; split; last by symmetry.
        left. by rewrite Hsource.
    + right. exists n; split; last exact Htarget. by right.
Qed.

Lemma dependency_graph_contains_edge c constraints g constraint
    (from to : SolverSyntax.finProdVar c) coeff :
  graph.build_dependency_graph c constraints = Some g ->
  List.In constraint constraints ->
  lhs_var1 constraint = SolverSyntax.finProdVar2ProdVar to ->
  List.In (coeff, SolverSyntax.finProdVar2ProdVar from)
    (rhs_terms1 constraint ++ rhs_power constraint) ->
  g from to.
Proof.
  move=> Hgraph Hin Hlhs Hterm.
  rewrite /graph.build_dependency_graph in Hgraph.
  case: (all (constraint_vars_in_graph c) constraints) Hgraph => //= Hgraph.
  inversion Hgraph; subst g.
  clear Hgraph.
  move: constraints Hin.
  elim=> [|head rest IH] //= [Heq|Hin].
  - subst head. rewrite Hlhs.
    exact: dependency_fold_contains Hterm.
  - apply dependency_fold_preserves.
    exact: IH Hin.
Qed.

Lemma dependency_graph_edge_origin c constraints g
    (from to : SolverSyntax.finProdVar c) :
  graph.build_dependency_graph c constraints = Some g ->
  g from to ->
  exists constraint coeff,
    List.In constraint constraints /\
    lhs_var1 constraint = SolverSyntax.finProdVar2ProdVar to /\
    List.In (coeff, SolverSyntax.finProdVar2ProdVar from)
      (rhs_terms1 constraint ++ rhs_power constraint).
Proof.
  move=> Hgraph Hedge.
  rewrite /graph.build_dependency_graph in Hgraph.
  case: (all (constraint_vars_in_graph c) constraints) Hgraph => //= Hgraph.
  inversion Hgraph; subst g. clear Hgraph.
  move: constraints Hedge.
  elim=> [|head rest IH] //= Hedge.
  have [Hrest|[coeff [Hterm Htarget]]] := dependency_fold_origin Hedge.
  - have [constraint [n [Hin [Hlhs Hterm]]]] := IH Hrest.
    exists constraint, n; split; first by right.
    by split.
  - exists head, coeff; split; first by left.
    by split.
Qed.

Lemma solve_alg_domain scclist initial cmap solution :
  inferWidths.solve_alg scclist initial cmap = Some solution ->
  forall key, SolverSyntax.PVM.mem key solution <->
    List.In key (List.concat scclist) \/ SolverSyntax.PVM.mem key initial.
Proof.
  move: initial solution.
  elim: scclist => [|scc rest IH] initial solution /=.
  - move=> [<-] key. by split; [right|case].
  - case Hscc: (inferWidths.solve_scc scc
      (List.map (remove_solved_c initial) (extract_cs scc cmap))) => [local|] //.
    case Hmerge: (merge_solution scc initial local) => [next|] //.
    move=> Hsolve key.
    rewrite (IH next solution Hsolve key) (merge_solution_mem_or local scc initial next Hmerge key).
    rewrite List.in_app_iff. tauto.
Qed.

Lemma solver_scalar_position_in_finite_set c tmap id gt orient :
  SolverSyntax.circuit_tmap c = Some tmap ->
  SolverSyntax.VM.find id tmap = Some (HiEnv.Gtyp gt, orient) ->
  (id, N0) \in SolverSyntax.finProdVar_list c.
Proof.
  move=> Hmap Hfind.
  rewrite /SolverSyntax.finProdVar_list Hmap.
  have Hin : List.In (id, (HiEnv.Gtyp gt, orient)) (SolverSyntax.VM.elements tmap).
  { have Hin := SolverSyntax.VM.elements_1 (SolverSyntax.VM.find_2 Hfind).
    apply SetoidList.InA_alt in Hin.
    destruct Hin as [[key value] [[Hkey Hvalue] Hin]].
    simpl in Hkey, Hvalue.
    move/eqP: Hkey => Hkey; subst key.
    subst value. exact Hin. }
  have Hflat : List.In (id, N0)
      (List.flat_map (fun '(key, (ft, _)) =>
        SolverSyntax.all_vars_of_ftype key 0 ft) (SolverSyntax.VM.elements tmap)).
  { apply List.in_flat_map.
    exists (id, (HiEnv.Gtyp gt, orient)); split; first exact Hin.
    by left. }
  exact: sequence_in_membership Hflat.
Qed.

Lemma extract_cs_member_iff keys cmap c :
  List.In c (extract_cs keys cmap) <->
  exists key cs, List.In key keys /\
    SolverSyntax.PVM.find key cmap = Some cs /\ List.In c cs.
Proof.
  split.
  - move=> Hin.
    have [key [Hkey [cs [Hfind Hc]]]] := extract_cs_exist_c c cmap keys Hin.
    by exists key, cs.
  move=> [key [cs [Hin [Hfind Hc]]]].
  elim: keys Hin => [|head rest IH] //= [Heq|Hin].
  - subst head. by rewrite Hfind; apply List.in_or_app; left.
  - case: (SolverSyntax.PVM.find head cmap) => [other|].
    + apply List.in_or_app; right. exact: IH.
    + exact: IH.
Qed.

Theorem extract_cs_flattened_satisfaction keys cmap value :
  (forall key cs, SolverSyntax.PVM.find key cmap = Some cs -> List.In key keys) ->
  List.forallb (satisfies_constraint1 value) (extract_cs keys cmap) =
  List.forallb (satisfies_constraint1 value)
    (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))).
Proof.
  move=> Hkeys.
  apply Bool.eq_true_iff_eq.
  rewrite !List.forallb_forall.
  split => H c Hin.
  - apply H. apply/extract_cs_member_iff.
    apply flattened_constraint_member in Hin.
    destruct Hin as [key [cs [Hentry Hc]]].
    have Hfind : SolverSyntax.PVM.find key cmap = Some cs by apply find_in_elements.
    exists key, cs. by repeat split; [apply: Hkeys Hfind | exact Hfind | exact Hc].
  - apply H. apply/flattened_constraint_member.
    apply extract_cs_member_iff in Hin.
    destruct Hin as [key [cs [_ [Hfind Hc]]]].
    exists key, cs; split; last exact Hc.
    by apply find_in_elements.
Qed.

Lemma successful_single_module_solver_helper c tmap cmap solution :
  extract_constraints_c c tmap = Some ([:: cmap], [::]) ->
  inferWidths.solve_fun c tmap = Some solution ->
  exists g,
    graph.build_dependency_graph c
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = Some g /\
    inferWidths.solve_alg (solver_sccs g) initial_valuation cmap = Some solution.
Proof.
  move=> Hextract Hsolve.
  rewrite /inferWidths.solve_fun Hextract /= in Hsolve.
  case Hvalid: (all (constraint_vars_in_graph c)
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap))))) => //= in Hsolve.
  rewrite /inferWidths.solve_helper in Hsolve.
  case Hgraph: (build_dependency_graph c
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap))))) => [g|] //= in Hsolve.
  rewrite /inferWidths.solve_alg_check in Hsolve.
  case Halg: (inferWidths.solve_alg (solver_sccs g) initial_valuation cmap)
    => [value|] //= in Hsolve.
  inversion Hsolve; subst value.
  by exists g.
Qed.

Theorem successful_single_module_solver_domain c tmap cmap solution :
  extract_constraints_c c tmap = Some ([:: cmap], [::]) ->
  inferWidths.solve_fun c tmap = Some solution ->
  forall key, SolverSyntax.PVM.mem key solution <-> key \in SolverSyntax.finProdVar_list c.
Proof.
  move=> Hextract Hsolve key.
  have [g [_ Halg]] := successful_single_module_solver_helper Hextract Hsolve.
  rewrite (solve_alg_domain Halg key) /initial_valuation.
  have Hempty : ~ SolverSyntax.PVM.mem key (SolverSyntax.PVM.empty nat).
  { move=> Hmem. apply find_mem in Hmem.
    destruct Hmem as [w Hfind]. by rewrite SolverSyntax.PVM.Lemmas.F.empty_o in Hfind. }
  split.
  - move=> [Hin|Hmem]; last contradiction.
    apply List.in_concat in Hin.
    destruct Hin as [scc [Hscc Hkey]].
    rewrite /solver_sccs in Hscc.
    apply List.in_map_iff in Hscc.
    destruct Hscc as [component [<- _]].
    apply List.in_map_iff in Hkey.
    destruct Hkey as [v [<- _]].
    exact: (valP v).
  - move=> Hkey. left.
    pose v : SolverSyntax.finProdVar c :=
      @Sub _ (fun x => x \in SolverSyntax.finProdVar_list c)
        (seq_sub (SolverSyntax.finProdVar_list c)) key Hkey.
    have Hin := solver_sccs_complete g v.
    exact Hin.
Qed.

Theorem successful_solve_fun_covers_initial solver_map m circuit_name initial solution :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  inferWidths.solve_fun (solver_circuit circuit_name m) solver_map = Some solution ->
  covered solution initial (common_module_name m).
Proof.
  move=> Hsolver Hinitial Hsolve id Horiginal.
  have [sem_map [Hsem Hmaps]] := initial_circuit_tmaps_related Hsolver Hinitial.
  have [gt [orient [Hfind _]]] :=
    original_implicit_has_solver_position Hsem Hmaps Horiginal.
  have Hfinite := solver_scalar_position_in_finite_set Hsolver Hfind.
  have [cmap Hextract] := successful_single_module_solver_extracts Hmaps Hsolve.
  have Hmem := (proj2 (successful_single_module_solver_domain Hextract Hsolve (id, N0))) Hfinite.
  apply find_mem in Hmem.
  exact Hmem.
Qed.

Definition common_constraint_map_keys (cmap : SolverSyntax.PVM.t (list Constraint1)) : Prop :=
  forall key cs, SolverSyntax.PVM.find key cmap = Some cs ->
    exists c, List.In c cs /\ lhs_var1 c = key.

Lemma add_common_constraint_map_keys cmap id rhs :
  common_constraint_map_keys cmap ->
  common_constraint_map_keys (add_common_constraint id rhs cmap).
Proof.
  move=> Hkeys key cs.
  rewrite /add_common_constraint.
  case Hsame: (key == (id, N0)).
  - move/eqP: Hsame => ->.
    rewrite SolverSyntax.PVM.Lemmas.F.add_eq_o; last by split; rewrite eqxx.
    case: (SolverSyntax.PVM.find (id, N0) cmap) => [prior|] [<-];
      exists (common_constraint id rhs); by split; [left|].
  - rewrite SolverSyntax.PVM.Lemmas.F.add_neq_o.
    + exact: Hkeys.
    + move=> Heq. apply eq_from_prodvar_eq in Heq.
      subst key. by rewrite eqxx in Hsame.
Qed.

Lemma common_extract_step_map_keys tmap cmap s next :
  common_constraint_map_keys cmap ->
  common_extract_step tmap cmap s = Some next ->
  common_constraint_map_keys next.
Proof.
  move=> Hkeys.
  case: s => [|id ty|id ty clock rst|id e] /=.
  - by move=> [<-].
  - by move=> [<-].
  - case: ty rst => [| |w|w] [|trigger e] //=;
      try (case: (common_rhs tmap e) => [rhs|] //=;
        move=> [<-]; exact: add_common_constraint_map_keys Hkeys);
      by move=> [<-].
  - case: (SolverSyntax.VM.find id tmap) => [[ty orient]|] //=.
    case: ty => [gt|elt n|fields] //=.
    case: gt => [w|w|w|w| | |] //=;
      try (case: (common_rhs tmap e) => [rhs|] //=;
        move=> [<-]; exact: add_common_constraint_map_keys Hkeys);
      by move=> [<-].
Qed.

Lemma common_extract_steps_map_keys tmap ss cmap result :
  common_constraint_map_keys cmap ->
  common_extract_steps tmap cmap ss = Some result ->
  common_constraint_map_keys result.
Proof.
  move: cmap; elim: ss => [|s ss IH] cmap Hkeys /=.
  - by move=> [<-].
  - case Hstep: (common_extract_step tmap cmap s) => [next|] //=.
    move=> Hresult. apply: (IH next _ Hresult).
    exact: common_extract_step_map_keys Hkeys Hstep.
Qed.

Theorem extracted_common_map_keys tmap m circuit_name cmap :
  solver_map_is_scalar tmap ->
  extract_constraints_c (solver_circuit circuit_name m) tmap = Some ([:: cmap], [::]) ->
  common_constraint_map_keys cmap.
Proof.
  move=> Hscalar Hextract.
  rewrite (extract_common_circuit m circuit_name Hscalar) in Hextract.
  case Hsteps: (common_extract_steps tmap (SolverSyntax.PVM.empty _)
    (rev (common_stmts m))) => [result|] //= in Hextract.
  inversion Hextract; subst result.
  apply: (common_extract_steps_map_keys _ Hsteps).
  move=> key cs Hfind. by rewrite SolverSyntax.PVM.Lemmas.F.empty_o in Hfind.
Qed.

Theorem successful_common_solver_extraction_bridge
    solver_map m circuit_name initial cmap solution :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  extract_constraints_c (solver_circuit circuit_name m) solver_map =
    Some ([:: cmap], [::]) ->
  inferWidths.solve_fun (solver_circuit circuit_name m) solver_map = Some solution ->
  exists g,
    graph.build_dependency_graph (solver_circuit circuit_name m)
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = Some g /\
    inferWidths.solve_alg (solver_sccs g) initial_valuation cmap = Some solution /\
    (forall value,
      List.forallb (satisfies_constraint1 value)
        (extract_cs (List.concat (solver_sccs g)) cmap) =
      List.forallb (satisfies_constraint1 value)
        (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap))))).
Proof.
  move=> Hsolver Hinitial Hextract Hsolve.
  have [sem_map [_ Hmaps]] := initial_circuit_tmaps_related Hsolver Hinitial.
  have Hkeys := extracted_common_map_keys (scalar_maps_related_is_scalar Hmaps) Hextract.
  have [g [Hgraph Halg]] := successful_single_module_solver_helper Hextract Hsolve.
  exists g; split; first exact Hgraph.
  split; first exact Halg.
  move=> value. apply extract_cs_flattened_satisfaction.
  move=> key cs Hfind.
  have [constraint [Hconstraint Hlhs]] := Hkeys key cs Hfind.
  have Hflat : List.In constraint
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))).
  { apply flattened_constraint_member.
    exists key, cs; split; last exact Hconstraint.
    by apply find_in_elements. }
  rewrite /build_dependency_graph in Hgraph.
  case Hvalid: (all (constraint_vars_in_graph (solver_circuit circuit_name m))
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap))))) => // in Hgraph.
  have Hforall : List.forallb
      (constraint_vars_in_graph (solver_circuit circuit_name m))
      (List.concat (snd (List.split (SolverSyntax.PVM.elements cmap)))) = true.
  { exact Hvalid. }
  apply List.forallb_forall with (x := constraint) in Hforall; last exact Hflat.
  move/andP: Hforall => [Hfinite _].
  rewrite Hlhs in Hfinite.
  pose v : SolverSyntax.finProdVar (solver_circuit circuit_name m) :=
    @Sub _ (fun x => x \in SolverSyntax.finProdVar_list (solver_circuit circuit_name m))
      (seq_sub (SolverSyntax.finProdVar_list (solver_circuit circuit_name m))) key Hfinite.
  exact: (solver_sccs_complete g v).
Qed.

Corollary conditional_solve_fun_matches_fixed_point_without_coverage
    solver_map m circuit_name n initial result solution :
  SolverSyntax.circuit_tmap (solver_circuit circuit_name m) = Some solver_map ->
  inferWidths.solve_fun (solver_circuit circuit_name m) solver_map = Some solution ->
  Semantics.circuit_tmap_uninferred (sem_circuit m) = Some initial ->
  Semantics.circuit_tmap_implicits (sem_circuit m) n = Some result ->
  (forall cmap,
    extract_constraints_c (solver_circuit circuit_name m) solver_map =
      Some ([:: cmap], [::]) ->
    solver_solution_contract initial (common_module_name m) cmap solution) ->
  forall id, original_implicit initial (common_module_name m) id ->
    exists w,
      solver_width solution id = Some w /\
      semantic_width result (common_module_name m) id = Some w.
Proof.
  move=> Hsolver Hsolve Hinitial Hresult Hcontract.
  have Hcover := successful_solve_fun_covers_initial Hsolver Hinitial Hsolve.
  exact: (conditional_solve_fun_matches_fixed_point
    Hsolver Hsolve Hinitial Hresult Hcover Hcontract).
Qed.
