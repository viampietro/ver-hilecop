(** * Simulation environment for the H-VHDL semantics. *)

(** Module defining the components of the simulation environment.  *)

Require Import Setoid.
Require Import common.Coqlib.
Require Import common.CoqTactics.
Require Import common.ListPlus.
Require Import common.GlobalTypes.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.HVhdlTypes.

Open Scope natset_scope.

(** ** Miscellaneous Environment Definitions *)

(** *** Equal Domains *)

(** Defines the design environment describing H-VHDL design instances
    in the semantical world. The design environment maps identifiers
    of a certain category of constructs (e.g, constant identifiers) to
    their declaration information (e.g, type and value for
    constants). *)

(** Definition of the [dom] function that yields a list of identifiers
    corresponding to the definition domain of an IdMap. *)

Definition EqualDom {A} (m m' : NatMap.t A) : Prop := forall (k : nat), NatMap.In k m <-> NatMap.In k m'.
Definition dom {A : Type} (f : IdMap A) : list ident := fs (NatMap.elements f).

Definition EqualDom_refl : forall {A} (m : IdMap A), EqualDom m m. firstorder. Defined.
Definition EqualDom_trans : forall {A} (m m' m'' : IdMap A), EqualDom m m' -> EqualDom m' m'' -> EqualDom m m''.
  unfold EqualDom; intros; transitivity (NatMap.In k m'); auto.
Defined.
Definition EqualDom_sym : forall {A} (m m' : IdMap A), EqualDom m m' -> EqualDom m' m.
  unfold EqualDom; symmetry; auto.
Defined.

Add Parametric Relation {A : Type} : (IdMap A) (EqualDom)
    reflexivity proved by EqualDom_refl
    symmetry proved by EqualDom_sym
    transitivity proved by EqualDom_trans
      as EqualDom_rel.           

Hint Resolve EqualDom_refl : hvhdl.
Hint Resolve EqualDom_trans : hvhdl.
Hint Resolve EqualDom_sym : hvhdl.

(** Defines the relation stating that a set [idset] is the
    differentiated intersection of two maps [m] and [m'] mapping
    identifier to value.
    
    The differentiated intersection of two maps [m] and [m'] is the
    set { x ∈ dom(m) ∩ dom(m') | m(x) ≠ m'(x) }. 
 *)

Definition IsDiffInter (m m' : IdMap value) (idset : IdSet) :=
  (forall id v v', NatSet.In id idset -> MapsTo id v m -> MapsTo id v' m' -> ~VEq v v') /\
  (forall id v v', MapsTo id v m -> MapsTo id v' m' -> ~VEq v v' -> NatSet.In id idset).

(** Defines the relation stating that a map [ovunion] results of the
    overriding union of two maps [ovridden] and [ovriding].

    A map [m''] results of the overriding union of maps [m] and [m']
    if m'' = λx. m'(x) if x ∈ dom(m') ∧ m(x) otherwise.

    We add in the relation definition that the overridden map
    [ovridden] and the resulting map [ovunion] must have the same
    definition domains.  *)

Definition IsOverrUnion (ovridden ovriding ovunion : IdMap value) :=
  EqualDom ovridden ovunion /\
  (forall id v, MapsTo id v ovriding -> MapsTo id v ovunion) /\
  (forall id v, ~NatMap.In id ovriding -> MapsTo id v ovridden -> MapsTo id v ovunion).

(** ** Local Environment *)

(** Defines a local environment of a process
    as a map from id to couples (type * value).
 *)

Definition LEnv := IdMap (type * value).

(** Defines an empty local environment. *)

Definition EmptyLEnv := NatMap.empty (type * value).

(* Needed because [SemanticalObject] as a recurvise definition that
   does not respect the strict positivity requirement.
   
   However, I am almost sure that it is not dangerous to do so. *)

Local Unset Positivity Checking.

(** ** Elaborated Design *)

(** Type of semantical objects that populate the design
    environment. *)

Inductive SemanticalObject : Type :=
| Generic (t : type) (v : value)
| Input (t : type)
| Output (t : type)
| Declared (t : type)
| Process (lenv : LEnv)
| Component (Δ__c : IdMap SemanticalObject).

(** Macro definition for the design environment type. 
    Mapping from identifiers to [SemanticalObject]. *)

Definition ElDesign := IdMap SemanticalObject.

(** Defines an empty design environment. *)

Definition EmptyElDesign := NatMap.empty SemanticalObject.

(** *** Identifiers Qualification *)

Definition GenericOf (Δ : ElDesign) id :=
  exists t v, MapsTo id (Generic t v) Δ.

Definition InputOf (Δ : ElDesign) id :=
  exists t, MapsTo id (Input t) Δ.

Definition OutputOf (Δ : ElDesign) id :=
  exists t, MapsTo id (Output t) Δ.

Definition DeclaredOf (Δ : ElDesign) id :=
  exists t, MapsTo id (Declared t) Δ.

Definition ProcessOf (Δ : ElDesign) id :=
  exists Λ, MapsTo id (Process Λ) Δ.

Definition CompOf (Δ : ElDesign) id :=
  exists Δ__c, MapsTo id (Component Δ__c) Δ.

(** ** Design State *)

(** Defines the structure of design state. *)

Inductive DState : Type :=
  MkDState {
      sigstore  : IdMap value;
      compstore : IdMap DState;
      events    : IdSet;
    }.

(** Defines an empty design state. *)

Definition EmptyDState := MkDState (NatMap.empty value)
                                   (NatMap.empty DState)
                                   (NatSet.empty).

(** Returns a DState with an empty event set, i.e, a record
    <S,C,∅>. *)

Definition NoEvDState (σ : DState) :=
  MkDState (sigstore σ)
           (compstore σ)
           (NatSet.empty).

(** Macro to add a new mapping id ⇒ value in the [sigstore] of the
    design state [σ].  *)

Definition sstore_add (id : ident) (v : value) (σ : DState) : DState :=
  MkDState (NatMap.add id v (sigstore σ)) (compstore σ) (events σ).

(** Macro to add a new mapping [id__c ⇒ σ__c] in the [compstore] of the
    design state [σ].  *)

Definition cstore_add (id__c : ident) (σ__c : DState) (σ : DState) : DState :=
  MkDState (sigstore σ) (NatMap.add id__c σ__c (compstore σ)) (events σ).

(** Returns a new DState where identifier [id] has been added to
    the [events] field.
 *)

Definition events_add (id : ident) (σ : DState) :=
  MkDState (sigstore σ) (compstore σ) (NatSet.add id (events σ)).

(** Defines the [InSStore] predicate that states that
    [id] is mapped in the [sigstore] of design state [σ].

    Wrapper around the [In] predicate.
 *)

Definition InSStore (id : ident) (σ : DState) :=
  NatMap.In id (sigstore σ).

(** Useful function to create a merged [DState] *)

Definition merge_natmap {A : Type} (s : NatSet.t) (m1 m2 : NatMap.t A) : NatMap.t A :=
  let f := fun k m =>
             match find k m1 with
             | Some a => NatMap.add k a m
             | _ => m
             end
  in NatSet.fold f s m2.

Definition merge_sstore (σ__o σ σ' : DState) : IdMap value :=
  merge_natmap (events σ) (sigstore σ) (merge_natmap (events σ') (sigstore σ') (sigstore σ__o)).

Definition merge_cstore (σ__o σ σ' : DState) : IdMap DState :=
  merge_natmap (events σ) (compstore σ) (merge_natmap (events σ') (compstore σ') (compstore σ__o)).

(** Predicate stating that a DState [σ__m] results from the
    interleaving of an origin DState [σ__o], and two DState
    [σ'] and [σ''].

    To understand the predicate, one can consider that the states
    [σ'] and [σ''] result from the interpretation of two
    different concurrent statements in the context of [σ__o].  *)

Definition IsMergedDState (σ__o σ' σ'' σ__m : DState) : Prop :=

  (* The definition domains of [sigstore] and [compstore] must be
     the same between the original state and the other states. *)
  
  EqualDom (sigstore σ__o) (sigstore σ__m) /\
  EqualDom (compstore σ__o) (compstore σ__m) /\
  EqualDom (sigstore σ__o) (sigstore σ') /\
  EqualDom (compstore σ__o) (compstore σ') /\
  EqualDom (sigstore σ__o) (sigstore σ'') /\
  EqualDom (compstore σ__o) (compstore σ'') /\
  
  (* Describes the content of [(sigstore σ__m)] *)

  (forall id v, NatSet.In id (events σ') ->
                NatMap.MapsTo id v (sigstore σ') <->
                NatMap.MapsTo id v (sigstore σ__m)) /\
  (forall id v, NatSet.In id (events σ'') ->
                NatMap.MapsTo id v (sigstore σ'') <->
                NatMap.MapsTo id v (sigstore σ__m)) /\
  (forall id v,
      ~NatSet.In id ((events σ') U (events σ'')) ->
      NatMap.MapsTo id v (sigstore σ__o) <->
      NatMap.MapsTo id v (sigstore σ__m)) /\

  (* Describes the content of [(compstore σ__m)] *)

  (forall id σ__c, NatSet.In id (events σ') ->
                 NatMap.MapsTo id σ__c (compstore σ') <->
                 NatMap.MapsTo id σ__c (compstore σ__m)) /\
  (forall id σ__c, NatSet.In id (events σ'') ->
                 NatMap.MapsTo id σ__c (compstore σ'') <->
                 NatMap.MapsTo id σ__c (compstore σ__m)) /\
  (forall id σ__c,
      ~NatSet.In id ((events σ') U (events σ'')) ->
      NatMap.MapsTo id σ__c (compstore σ__o) <->
      NatMap.MapsTo id σ__c (compstore σ__m)) /\

  (* Describes the content of [(events σ__m)] *)
  
  NatSet.Equal (events σ__m) ((events σ') U (events σ'')).

(** Defines the relation stating that a design state [σ__inj] is the
    result of the "injection" of the values of map [m] in the
    [sigstore] and the [events] fields of design state [σ__o]. *)

Definition IsInjectedDState (σ__o : DState) (m : IdMap value) (σ__inj : DState) : Prop :=
  IsOverrUnion (sigstore σ__o) m (sigstore σ__inj) /\
  forall idset, IsDiffInter (sigstore σ__o) m idset ->
                NatSet.Equal (events σ__inj) ((events σ__o) U idset).

(** ** Equivalence Relations between Elaborated Designs *)

(** *** Generic Constant Set Equivalence *)

Definition EqGens (Δ Δ' : ElDesign) :=
  forall id t v,
    MapsTo id (Generic t v) Δ <-> MapsTo id (Generic t v) Δ'.

Definition EqGens_refl : forall (Δ : ElDesign), EqGens Δ Δ. firstorder. Defined.
Definition EqGens_trans : forall (Δ Δ' Δ'' : ElDesign), EqGens Δ Δ' -> EqGens Δ' Δ'' -> EqGens Δ Δ''.
  unfold EqGens; intros; transitivity (MapsTo id (Generic t0 v) Δ'); auto.
Defined.
Definition EqGens_sym : forall (Δ Δ' : ElDesign), EqGens Δ Δ' -> EqGens Δ' Δ.
  unfold EqGens; symmetry; auto.
Defined.

Add Parametric Relation : (ElDesign) (EqGens)
    reflexivity proved by EqGens_refl
    symmetry proved by EqGens_sym
    transitivity proved by EqGens_trans
      as EqGens_rel.           

(** Enable rewriting [MapsTo id (Generic t v) Δ1] into  
    [MapsTo id (Generic t) Δ2] if [EqGens Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) (v : value) : (MapsTo id (Generic t v)) 
    with signature (@EqGens ==> impl) as eqgens_mapsto_mor.
Proof. intros x y H; rewrite (H id t); unfold impl; auto. Qed.

Hint Resolve EqGens_refl : hvhdl.
Hint Resolve EqGens_trans : hvhdl.
Hint Resolve EqGens_sym : hvhdl.

(** *** Input Port Set Equivalence *)

Definition EqIns (Δ Δ' : ElDesign) :=
  forall id t,
    MapsTo id (Input t) Δ <-> MapsTo id (Input t) Δ'.

Definition EqIns_refl : forall (Δ : ElDesign), EqIns Δ Δ. firstorder. Defined.
Definition EqIns_trans : forall (Δ Δ' Δ'' : ElDesign), EqIns Δ Δ' -> EqIns Δ' Δ'' -> EqIns Δ Δ''.
  unfold EqIns; intros; transitivity (MapsTo id (Input t0) Δ'); auto.
Defined.
Definition EqIns_sym : forall (Δ Δ' : ElDesign), EqIns Δ Δ' -> EqIns Δ' Δ.
  unfold EqIns; symmetry; auto.
Defined.

Add Parametric Relation : (ElDesign) (EqIns)
    reflexivity proved by EqIns_refl
    symmetry proved by EqIns_sym
    transitivity proved by EqIns_trans
      as EqIns_rel.

(** Rewrite [MapsTo id (Input t) Δ1] into  
    [MapsTo id (Input t) Δ2] if [EqIns Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) : (MapsTo id (Input t)) 
    with signature (@EqIns ==> impl) as eqins_mapsto_in_mor.
Proof. intros x y H; rewrite (H id t); unfold impl; auto. Qed.

(** *** Output Port Set Equivalence *)

Definition EqOuts (Δ Δ' : ElDesign) :=
  forall id t,
    MapsTo id (Output t) Δ <-> MapsTo id (Output t) Δ'.

Definition EqOuts_refl : forall (Δ : ElDesign), EqOuts Δ Δ. firstorder. Defined.
Definition EqOuts_trans : forall (Δ Δ' Δ'' : ElDesign), EqOuts Δ Δ' -> EqOuts Δ' Δ'' -> EqOuts Δ Δ''.
  unfold EqOuts; intros; transitivity (MapsTo id (Output t0) Δ'); auto.
Defined.
Definition EqOuts_sym : forall (Δ Δ' : ElDesign), EqOuts Δ Δ' -> EqOuts Δ' Δ.
  unfold EqOuts; symmetry; auto.
Defined.

Add Parametric Relation : (ElDesign) (EqOuts)
    reflexivity proved by EqOuts_refl
    symmetry proved by EqOuts_sym
    transitivity proved by EqOuts_trans
      as EqOuts_rel.

(** Rewrite [MapsTo id (Output t) Δ1] into  
    [MapsTo id (Output t) Δ2] if [EqOuts Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) : (MapsTo id (Output t)) 
    with signature (@EqOuts ==> impl) as eqouts_mapsto_out_mor.
Proof. intros x y H; rewrite (H id t); unfold impl; auto. Qed.

(** *** Declared Signal Set Equivalence *)

Definition EqDecls (Δ Δ' : ElDesign) :=
  forall id t,
    MapsTo id (Declared t) Δ <-> MapsTo id (Declared t) Δ'.

Definition EqDecls_refl : forall (Δ : ElDesign), EqDecls Δ Δ. firstorder. Defined.
Definition EqDecls_trans : forall (Δ Δ' Δ'' : ElDesign), EqDecls Δ Δ' -> EqDecls Δ' Δ'' -> EqDecls Δ Δ''.
  unfold EqDecls; intros; transitivity (MapsTo id (Declared t0) Δ'); auto.
Defined.
Definition EqDecls_sym : forall (Δ Δ' : ElDesign), EqDecls Δ Δ' -> EqDecls Δ' Δ.
  unfold EqDecls; symmetry; auto.
Defined.

Add Parametric Relation : (ElDesign) (EqDecls)
    reflexivity proved by EqDecls_refl
    symmetry proved by EqDecls_sym
    transitivity proved by EqDecls_trans
      as EqDecls_rel.

(** Enable rewriting [MapsTo id (Declared t) Δ1] into  
    [MapsTo id (Declared t) Δ2] if [EqDecls Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) : (MapsTo id (Declared t)) 
    with signature (@EqDecls ==> impl) as eqdecls_mapsto_decl_mor.
Proof. intros x y H; rewrite (H id t); unfold impl; auto. Qed.

(** *** Signal (Input, Output and Declared) Set Equivalence *)

Definition EqSigs (Δ Δ' : ElDesign) :=
  EqIns Δ Δ' /\ EqOuts Δ Δ' /\ EqDecls Δ Δ'.

Definition EqSigs_refl : forall (Δ : ElDesign), EqSigs Δ Δ. firstorder. Defined.
Definition EqSigs_trans : forall (Δ Δ' Δ'' : ElDesign), EqSigs Δ Δ' -> EqSigs Δ' Δ'' -> EqSigs Δ Δ''.
  unfold EqSigs; intros; decompose [and] H; decompose [and] H0.
  split_and; transitivity Δ'; auto.
Defined.
Definition EqSigs_sym : forall (Δ Δ' : ElDesign), EqSigs Δ Δ' -> EqSigs Δ' Δ.
  unfold EqSigs; intros; decompose [and] H.
  split_and; symmetry; auto.
Defined.

Add Parametric Relation : (ElDesign) (EqSigs)
    reflexivity proved by EqSigs_refl
    symmetry proved by EqSigs_sym
    transitivity proved by EqSigs_trans
      as EqSigs_rel.

(** Enable rewriting [MapsTo id (Declared t) Δ1] into  
    [MapsTo id (Declared t) Δ2] if [EqSigs Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) : (MapsTo id (Declared t)) 
    with signature (@EqSigs ==> impl) as eqsigs_mapsto_decl_mor.
Proof. intros x y H; do 2 (apply proj2 in H); rewrite H; unfold impl; auto. Qed.

(** Enable rewriting [MapsTo id (Output t) Δ1] into  
    [MapsTo id (Output t) Δ2] if [EqSigs Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) : (MapsTo id (Output t)) 
    with signature (@EqSigs ==> impl) as eqsigs_mapsto_out_mor.
Proof. intros x y H; apply proj2, proj1 in H. rewrite H; unfold impl; auto. Qed.

(** Enable rewriting [MapsTo id (Input t) Δ1] into  
    [MapsTo id (Input t) Δ2] if [EqSigs Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) : (MapsTo id (Input t)) 
    with signature (@EqSigs ==> impl) as eqsigs_mapsto_in_mor.
Proof. intros x y H; apply proj1 in H; rewrite H; unfold impl; auto. Qed.

(** *** Process and Component Instance Set Equivalence *)

Definition EqPs (Δ Δ' : ElDesign) :=
  forall id Λ,
    MapsTo id (Process Λ) Δ <-> MapsTo id (Process Λ) Δ'.

Definition EqComps (Δ Δ' : ElDesign) :=
  forall id Δ__c,
    MapsTo id (Component Δ__c) Δ <-> MapsTo id (Component Δ__c) Δ'.

(** ** Equivalence Relations between Design States *)

(** *** Signal Store Equivalence *)

Definition EqSStore (σ σ' : DState) :=
  forall id v,
    MapsTo id v (sigstore σ) <-> MapsTo id v (sigstore σ').

Definition EqSStore_refl : forall (σ : DState), EqSStore σ σ. firstorder. Defined.
Definition EqSStore_trans : forall (σ σ' σ'' : DState), EqSStore σ σ' -> EqSStore σ' σ'' -> EqSStore σ σ''.
  unfold EqSStore; intros; transitivity (MapsTo id v (sigstore σ')); auto.
Defined.
Definition EqSStore_sym : forall (σ σ' : DState), EqSStore σ σ' -> EqSStore σ' σ.
  unfold EqSStore; symmetry; auto.
Defined.

Add Parametric Relation : (DState) (EqSStore)
    reflexivity proved by EqSStore_refl
    symmetry proved by EqSStore_sym
    transitivity proved by EqSStore_trans
      as EqSStore_rel.

(** Enable rewriting [MapsTo id v (sigstore σ1)] into  
    [MapsTo id v (sigstore σ2)] if [EqSStore σ1 σ2]. *)

Add Parametric Morphism (id : ident) (v : value) : (fun σ => MapsTo id v (sigstore σ)) 
    with signature (@EqSStore ==> impl) as eqsstore_mapsto_mor.
Proof. intros x y H; unfold EqSStore in H; erewrite H; unfold impl; eauto. Qed.

(** *** Component Store Equivalence *)

Definition EqCStore (σ σ' : DState) :=
  forall id σ__c,
    MapsTo id σ__c (compstore σ) <-> MapsTo id σ__c (compstore σ').

Definition EqCStore_refl : forall (σ : DState), EqCStore σ σ. firstorder. Defined.
Definition EqCStore_trans : forall (σ σ' σ'' : DState), EqCStore σ σ' -> EqCStore σ' σ'' -> EqCStore σ σ''.
  unfold EqCStore; intros; transitivity (MapsTo id σ__c (compstore σ')); auto.
Defined.
Definition EqCStore_sym : forall (σ σ' : DState), EqCStore σ σ' -> EqCStore σ' σ.
  unfold EqCStore; symmetry; auto.
Defined.

Add Parametric Relation : (DState) (EqCStore)
    reflexivity proved by EqCStore_refl
    symmetry proved by EqCStore_sym
    transitivity proved by EqCStore_trans
      as EqCStore_rel.

(** *** Events Set Equivalence *)

Definition EqEvs (σ σ' : DState) :=
  NatSet.Equal (events σ) (events σ').

Definition EqEvs_refl : forall (σ : DState), EqEvs σ σ. firstorder. Defined.
Definition EqEvs_trans : forall (σ σ' σ'' : DState), EqEvs σ σ' -> EqEvs σ' σ'' -> EqEvs σ σ''.
  unfold EqEvs; intros; transitivity (events σ'); auto.
Defined.
Definition EqEvs_sym : forall (σ σ' : DState), EqEvs σ σ' -> EqEvs σ' σ.
  unfold EqEvs; symmetry; auto.
Defined.

Add Parametric Relation : (DState) (EqEvs)
    reflexivity proved by EqEvs_refl
    symmetry proved by EqEvs_sym
    transitivity proved by EqEvs_trans
      as EqEvs_rel.

(** *** Design State Equivalence *)

Definition EqDState (σ σ' : DState) :=
  EqSStore σ σ' /\ EqCStore σ σ' /\ EqEvs σ σ'.

Definition EqDState_refl : forall (σ : DState), EqDState σ σ. firstorder. Defined.
Definition EqDState_trans : forall (σ σ' σ'' : DState), EqDState σ σ' -> EqDState σ' σ'' -> EqDState σ σ''.
  unfold EqDState; intros; decompose [and] H; decompose [and] H0.
  split_and; transitivity σ'; auto.
Defined.
Definition EqDState_sym : forall (σ σ' : DState), EqDState σ σ' -> EqDState σ' σ.
  unfold EqDState; intros; decompose [and] H.
  split_and; symmetry; auto.
Defined.

Add Parametric Relation : (DState) (EqDState)
    reflexivity proved by EqDState_refl
    symmetry proved by EqDState_sym
    transitivity proved by EqDState_trans
      as EqDState_rel.

