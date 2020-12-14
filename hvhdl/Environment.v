(** * Simulation environment for the H-VHDL semantics. *)

(** Module defining the components of the simulation environment.  *)

Require Import Coqlib.
Require Import ListsPlus.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.HVhdlTypes.

Open Scope natset_scope.

(** Defines the design environment describing H-VHDL design instances
    in the semantical world. The design environment maps identifiers
    of a certain category of constructs (e.g, constant identifiers) to
    their declaration information (e.g, type and value for
    constants). *)

(** Definition of the [dom] function that yields a list of identifiers
    corresponding to the definition domain of an IdMap. *)

Definition EqualDom {A} (m m' : t A) : Prop := forall (k : nat), NatMap.In k m <-> NatMap.In k m'.
Definition dom {A : Type} (f : IdMap A) : list ident := fs (elements f).

(** Defines the relation stating that a set [idset] is the
    differentiated intersection of two maps [m] and [m'] mapping
    identifier to value.
    
    The differentiated intersection of two maps [m] and [m'] is the
    set { x ∈ dom(m) ∩ dom(m') | m(x) ≠ m'(x) }. 
 *)

Definition IsDiffInter (m m' : IdMap value) (idset : IdSet) :=
  (forall id, NatSet.In id idset -> forall v v', MapsTo id v m -> MapsTo id v' m' -> ~VEq v v') /\
  (forall id v v', (MapsTo id v m /\ MapsTo id v' m' /\ ~VEq v v') -> NatSet.In id idset).

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

(** Type of semantical objects that populate the design
    environment. *)
                                                     
Inductive SemanticalObject : Type :=
| Generic (t : type) (v : value)
| Input (t : type)
| Output (t : type)
| Declared (t : type)
| Process (lenv : LEnv)
| Component (ecomp : IdMap SemanticalObject) (behavior : cs).

(** Macro definition for the design environment type. 
    Mapping from identifiers to [SemanticalObject]. *)

Definition ElDesign := IdMap SemanticalObject.

(* genids : list ident; *)
(*   G := { id | In id genids} *)
(*   Gens : G -> type * value        *)

(** Defines an empty design environment. *)

Definition EmptyElDesign := NatMap.empty SemanticalObject.

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

(** Macro to add a new mapping id ⇒ DState in the [compstore] of the
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

(** Predicate stating that a DState [σ__m] results from the
    interleaving of an origin DState [σ__o], and two DState
    [σ'] and [σ''].

    To understand the predicate, one can consider that the states
    [σ'] and [σ''] result from the interpretation of two
    different concurrent statements in the context of [σ__o].  *)

Definition IsMergedDState (σ__o σ' σ'' σ__m : DState) : Prop :=

  (* The definition domains of [sigstore] and [compstore] must be
     the same for [σ__o] and [σ__m]. *)
  
  EqualDom (sigstore σ__o) (sigstore σ__m) /\
  EqualDom (compstore σ__o) (compstore σ__m) /\
  
  (* Describes the content of (sigstore σ__m) *)

  (forall id v, NatSet.In id (events σ') ->
                NatMap.MapsTo id v (sigstore σ') ->
                NatMap.MapsTo id v (sigstore σ__m)) /\
  (forall id v, NatSet.In id (events σ'') ->
                NatMap.MapsTo id v (sigstore σ'') ->
                NatMap.MapsTo id v (sigstore σ__m)) /\
  (forall id v,
      ~NatSet.In id ((events σ') U (events σ'')) ->
      NatMap.MapsTo id v (sigstore σ__o) ->
      NatMap.MapsTo id v (sigstore σ__m)) /\

  (* Describes the content of (compstore σ__m) *)

  (forall id σ__c, NatSet.In id (events σ') ->
                 NatMap.MapsTo id σ__c (compstore σ') ->
                 NatMap.MapsTo id σ__c (compstore σ__m)) /\
  (forall id σ__c, NatSet.In id (events σ'') ->
                 NatMap.MapsTo id σ__c (compstore σ'') ->
                 NatMap.MapsTo id σ__c (compstore σ__m)) /\
  (forall id σ__c,
      ~NatSet.In id ((events σ') U (events σ'')) ->
      NatMap.MapsTo id σ__c (compstore σ__o) ->
      NatMap.MapsTo id σ__c (compstore σ__m)) /\

  (* Describes the content of (events σ__m) *)
  
  NatSet.Equal (events σ__m) ((events σ') U (events σ'')).

(** Defines the relation stating that a design state [σ__inj] is the
    result of the "injection" of the values of map [m] in the
    [sigstore] and the [events] fields of design state [σ__o]. *)

Definition IsInjectedDState (σ__o : DState) (m : IdMap value) (σ__inj : DState) : Prop :=
  IsOverrUnion (sigstore σ__o) m (sigstore σ__inj) /\
  forall idset, IsDiffInter (sigstore σ__o) m idset ->
                NatSet.Equal (events σ__inj) ((events σ__o) U idset).


