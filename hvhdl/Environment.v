(** * Simulation environment for the H-VHDL semantics. *)

(** Module defining the components of the simulation environment.  *)

Require Import Coqlib.
Require Import ListsPlus.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.
Require Import HVhdlTypes.

Open Scope natset_scope.

(** Defines the design environment describing H-VHDL design instances
    in the semantical world. The design environment maps identifiers
    of a certain category of constructs (e.g, constant identifiers) to
    their declaration information (e.g, type and value for
    constants). *)

(** Definition of the [dom] function that yields a list of identifiers
    corresponding to the definition domain of an IdMap. *)

Definition dom {A : Type} (f : IdMap A) : list ident := fs (NatMap.elements f).

(** Defines the relation stating that a set [idset] is the
    differentiated intersection of two maps [m] and [m'] mapping
    identifier to value.
    
    The differentiated intersection of two maps [m] and [m'] is the
    set { x ∈ dom(m) ∩ dom(m') | m(x) ≠ m'(x) }. 
 *)

Definition IsDiffInter (m m' : IdMap value) (idset : IdSet) :=
  (forall {id}, NatSet.In id idset -> forall {v v'}, MapsTo id v m -> MapsTo id v' m' -> VEq v v' (Some false)) /\
  (forall {id v v'}, (MapsTo id v m /\ MapsTo id v' m' /\ VEq v v' (Some false)) -> NatSet.In id idset).

(** Defines the relation stating that a map [ovunion] results of the
    overriding union of two maps [ovridden] and [ovriding].

    A map [m''] results of the overriding union of maps [m] and [m']
    if m'' = λx. m'(x) if x ∈ dom(m') ∧ m(x) otherwise.

    We add in the relation definition that the overridden map
    [ovridden] and the resulting map [ovunion] must have the same
    definition domains.  *)

Definition IsOverrUnion (ovridden ovriding ovunion : IdMap value) :=
  EqualDom ovridden ovunion /\
  (forall {id v}, MapsTo id v ovriding -> MapsTo id v ovunion) /\
  (forall {id v}, ~NatMap.In id ovriding -> MapsTo id v ovridden -> MapsTo id v ovunion).

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
| Constant (t : type) (v : value)
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

Definition NoEvDState (dstate : DState) :=
  MkDState (sigstore dstate)
           (compstore dstate)
           (NatSet.empty).

(** Macro to add a new mapping id ⇒ value in the [sigstore] of the
    design state [dstate].  *)

Definition sstore_add (id : ident) (v : value) (dstate : DState) : DState :=
  MkDState (NatMap.add id v (sigstore dstate)) (compstore dstate) (events dstate).

(** Returns a new DState where identifier [id] has been added to
    the [events] field.
 *)

Definition events_add (id : ident) (dstate : DState) :=
  MkDState (sigstore dstate) (compstore dstate) (NatSet.add id (events dstate)).

(** Defines the [InSStore] predicate that states that
    [id] is mapped in the [sigstore] of design state [dstate].

    Wrapper around the [In] predicate.
 *)

Definition InSStore (id : ident) (dstate : DState) :=
  NatMap.In id (sigstore dstate).

(** Predicate stating that a DState [merged] results from the
    interleaving of an origin DState [origin], and two DState
    [dstate'] and [dstate''].

    To understand the predicate, one can consider that the states
    [dstate'] and [dstate''] result from the interpretation of two
    different concurrent statements in the context of [origin].  *)

Definition IsMergedDState (origin dstate' dstate'' merged : DState) : Prop :=

  (* The definition domains of [sigstore] and [compstore] must be
     the same for [origin] and [merged]. *)
  
  EqualDom (sigstore origin) (sigstore merged) ->
  EqualDom (compstore origin) (compstore merged) ->
  
  (* Describes the content of (sigstore merged) *)

  (forall {id v}, NatSet.In id (events dstate') ->
                  NatMap.MapsTo id v (sigstore dstate') ->
                  NatMap.MapsTo id v (sigstore merged)) /\
  (forall {id v}, NatSet.In id (events dstate'') ->
                  NatMap.MapsTo id v (sigstore dstate'') ->
                  NatMap.MapsTo id v (sigstore merged)) /\
  (forall {id v},
      ~NatSet.In id ((events dstate') U (events dstate'')) ->
      NatMap.MapsTo id v (sigstore origin) ->
      NatMap.MapsTo id v (sigstore merged)) /\

  (* Describes the content of (compstore merged) *)

  (forall {id cstate}, NatSet.In id (events dstate') ->
                       NatMap.MapsTo id cstate (compstore dstate') ->
                       NatMap.MapsTo id cstate (compstore merged)) /\
  (forall {id cstate}, NatSet.In id (events dstate'') ->
                       NatMap.MapsTo id cstate (compstore dstate'') ->
                       NatMap.MapsTo id cstate (compstore merged)) /\
  (forall {id cstate},
      ~NatSet.In id ((events dstate') U (events dstate'')) ->
      NatMap.MapsTo id cstate (compstore origin) ->
      NatMap.MapsTo id cstate (compstore merged)) /\

  (* Describes the content of (events merged) *)
  
  NatSet.Equal (events merged) ((events dstate') U (events dstate'')).

(** Defines the relation stating that a design state [injected] is the
    result of the "injection" of the values of map [m] in the
    [sigstore] and the [events] fields of design state [origin]. *)

Definition IsInjectedDState (origin : DState) (m : IdMap value) (injected : DState) : Prop :=
  IsOverrUnion (sigstore origin) m (sigstore injected) /\
  forall {idset}, IsDiffInter (sigstore origin) m idset ->
                  NatSet.Equal (events injected) ((events origin) U idset).


