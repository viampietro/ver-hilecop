(** * Simulation environment for the H-VHDL semantics. *)

(** Module defining the components of the simulation environment.  *)

Require Import Setoid.
Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.NatSet.
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

#[export] Hint Resolve EqualDom_refl : hvhdl.
#[export] Hint Resolve EqualDom_trans : hvhdl.
#[export] Hint Resolve EqualDom_sym : hvhdl.

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

(** Defines a process local variable environment as a map from local
    variable identifiers to couples (type * value).  *)

Definition LEnv := IdMap (type * value).

(** Defines an empty process local variable environment. *)

Definition EmptyLEnv := NatMap.empty (type * value).


(** ** Elaborated Design *)

(** Elaborated design attributes *)

(* Needed because the inductive definition of the [DesignAttribute]
   type does not respect the strict positivity requirement.
   
   However, I am almost sure that it is not dangerous to do so. *)

Local Unset Positivity Checking.

(** Defines an elaborated design as a mapping from identifiers to
    [DesignAttribute]. *)

Inductive ElDesign : Type :=
| MkElDesign : NatMap.t DesignAttribute -> ElDesign
with DesignAttribute  :=
| Generic (t : type) (v : value)
| Input (t : type)
| Output (t : type)
| Declared (t : type)
| Process (lenv : LEnv)
| Component (Δ__c : ElDesign).

Coercion ElDesign_to_IdMap (Δ : ElDesign) :=
  match Δ with MkElDesign m => m end.

(** Defines a bare elaborated design. *)

Definition EmptyElDesign := MkElDesign (NatMap.empty DesignAttribute).

(** *** Identifiers qualification *)

Definition GenericOf (Δ : ElDesign) id :=
  exists t v, MapsTo id (Generic t v) Δ.

Definition InputOf (Δ : ElDesign) id :=
  exists t, MapsTo id (Input t) Δ.

Definition OutputOf (Δ : ElDesign) id :=
  exists t, MapsTo id (Output t) Δ.

Definition InternalOf (Δ : ElDesign) id :=
  exists t, MapsTo id (Declared t) Δ.

Definition ProcessOf (Δ : ElDesign) id :=
  exists Λ, MapsTo id (Process Λ) Δ.

Definition CompOf (Δ : ElDesign) id :=
  exists Δ__c, MapsTo id (Component Δ__c) Δ.

(** ** Design State *)

(** Defines the structure of design state composed of a signal store
    [sstore], and a design instance store [cstore]. *)

Inductive DState : Type :=
  MkDState {
      sstore  : IdMap value;
      cstore : IdMap DState;
    }.

(** Defines an empty design state. *)

Definition EmptyDState := MkDState (NatMap.empty value)
                                   (NatMap.empty DState).

(** Macro to add, or to override, a mapping [id ⇒ value] in the
    [sstore] of the design state [σ].  *)

Definition sstore_add (id : ident) (v : value) (σ : DState) : DState :=
  MkDState (NatMap.add id v (sstore σ)) (cstore σ).

(** Macro to add, or to override, a mapping [id__c ⇒ σ__c] in the [cstore]
    of the design state [σ].  *)

Definition cstore_add (id__c : ident) (σ__c : DState) (σ : DState) : DState :=
  MkDState (sstore σ) (NatMap.add id__c σ__c (cstore σ)).

(** Defines the [InSStore] predicate that states that [id] is mapped
    to a value in the [sstore] of design state [σ].

    Wrapper around the [In] predicate.  *)

Definition InSStore (id : ident) (σ : DState) :=
  NatMap.In id (sstore σ).

(** Useful function to create a merged [DState] *)

Definition merge_natmap {A : Type}
           (Aeq : A -> A -> Prop)
           (Aeq_dec : forall x y, {Aeq x y} + {~Aeq x y})
           (m0 m1 m2 : NatMap.t A) : NatMap.t A := m0.

(** Design state equality relation *)

Inductive DStateEq (σ1 σ2 : DState) : Prop :=
  DSEq {
      sstore_eq :
      forall id v1 v2,
        NatMap.MapsTo id v1 (sstore σ1) ->
        NatMap.MapsTo id v2 (sstore σ2) ->
        VEq v1 v2;

      cstore_eq :
      forall id σ__c1 σ__c2,
        NatMap.MapsTo id σ__c1 (cstore σ1) ->
        NatMap.MapsTo id σ__c2 (cstore σ2) ->
        DStateEq σ__c1 σ__c2
    }.

(** Predicate stating that a DState [σ__m] results from the
    interleaving of an origin DState [σ__o], and two DState
    [σ'] and [σ''].

    To understand the predicate, one can consider that the states
    [σ'] and [σ''] result from the parallel execution of two
    concurrent statements in the context of [σ__o].  

*)

Record IsMergedDState (σ__o σ' σ'' σ__m : DState) : Prop :=
  IMDS {

      (* Describes the content of [(sstore σ__m)] *)
      sstore1 :
      forall id v1 v2,
        NatMap.MapsTo id v1 (sstore σ') ->
        NatMap.MapsTo id v2 (sstore σ__o) ->
        VNEq v1 v2 ->
        NatMap.MapsTo id v1 (sstore σ__m);

      sstore2 :
      forall id v1 v2,
        NatMap.MapsTo id v1 (sstore σ'') ->
        NatMap.MapsTo id v2 (sstore σ__o) ->
        VNEq v1 v2 ->
        NatMap.MapsTo id v1 (sstore σ__m);

      sstore__o :
      forall id v__o v1 v2,
        NatMap.MapsTo id v__o (sstore σ__o) ->
        NatMap.MapsTo id v1 (sstore σ') ->
        NatMap.MapsTo id v2 (sstore σ'') ->
        VEq v__o v1 ->
        VEq v__o v2 ->
        NatMap.MapsTo id v__o (sstore σ__m);

      (* Describes the content of [(cstore σ__m)] *)
      cstore1 :
      forall id σ__c1 σ__c2,
        NatMap.MapsTo id σ__c1 (cstore σ') ->
        NatMap.MapsTo id σ__c2 (cstore σ__o) ->
        ~DStateEq σ__c1 σ__c2 ->
        NatMap.MapsTo id σ__c1 (cstore σ__m);

      cstore2 :
      forall id σ__c1 σ__c2,
        NatMap.MapsTo id σ__c1 (cstore σ'') ->
        NatMap.MapsTo id σ__c2 (cstore σ__o) ->
        ~DStateEq σ__c1 σ__c2 ->
        NatMap.MapsTo id σ__c1 (cstore σ__m);

      cstore__o :
      forall id σ__co σ__c1 σ__c2,
        NatMap.MapsTo id σ__co (cstore σ__o) ->
        NatMap.MapsTo id σ__c1 (cstore σ') ->
        NatMap.MapsTo id σ__c2 (cstore σ'') ->
        DStateEq σ__co σ__c1 ->
        DStateEq σ__co σ__c2 ->
        NatMap.MapsTo id σ__co (cstore σ__m)
                      
    }.

(** Defines the relation stating that a design state [σ__i] is the
    result of the "injection" of the values of map [m] in the
    [sstore] of design state [σ__o]. *)

Definition IsInjectedDState (σ__o : DState) (m : IdMap value) (σ__i : DState) : Prop :=
  IsOverrUnion (sstore σ__o) m (sstore σ__i).

