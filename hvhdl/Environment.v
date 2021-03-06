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
    set { x ??? dom(m) ??? dom(m') | m(x) ??? m'(x) }. 
 *)

Definition IsDiffInter (m m' : IdMap value) (idset : IdSet) :=
  (forall id v v', NatSet.In id idset -> MapsTo id v m -> MapsTo id v' m' -> ~VEq v v') /\
  (forall id v v', MapsTo id v m -> MapsTo id v' m' -> ~VEq v v' -> NatSet.In id idset).

(** Defines the relation stating that a map [ovunion] results of the
    overriding union of two maps [ovridden] and [ovriding].

    A map [m''] results of the overriding union of maps [m] and [m']
    if m'' = ??x. m'(x) if x ??? dom(m') ??? m(x) otherwise.

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
| MkElDesign :> NatMap.t DesignAttribute -> ElDesign
with DesignAttribute  :=
| Generic (t : type) (v : value)
| Input (t : type)
| Output (t : type)
| Internal (t : type)
| Process (lenv : LEnv)
| Component (??__c : ElDesign).

Coercion ElDesign_to_IdMap (?? : ElDesign) : NatMap.t DesignAttribute :=
  match ?? with MkElDesign m => m end.

(** Defines a bare elaborated design. *)

Definition EmptyElDesign := MkElDesign (NatMap.empty DesignAttribute).

(** *** Identifiers qualification *)

Definition GenericOf (?? : ElDesign) id :=
  exists t v, MapsTo id (Generic t v) ??.

Definition InputOf (?? : ElDesign) id :=
  exists t, MapsTo id (Input t) ??.

Definition OutputOf (?? : ElDesign) id :=
  exists t, MapsTo id (Output t) ??.

Definition InternalOf (?? : ElDesign) id :=
  exists t, MapsTo id (Internal t) ??.

Definition ProcessOf (?? : ElDesign) id :=
  exists ??, MapsTo id (Process ??) ??.

Definition CompOf (?? : ElDesign) id :=
  exists ??__c, MapsTo id (Component ??__c) ??.

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

Definition EmptySStore := (NatMap.empty value).

(** Macro to add, or to override, a mapping [id ??? value] in the
    [sstore] of the design state [??].  *)

Definition sstore_add (id : ident) (v : value) (?? : DState) : DState :=
  MkDState (NatMap.add id v (sstore ??)) (cstore ??).

(** Macro to add, or to override, a mapping [id__c ??? ??__c] in the [cstore]
    of the design state [??].  *)

Definition cstore_add (id__c : ident) (??__c : DState) (?? : DState) : DState :=
  MkDState (sstore ??) (NatMap.add id__c ??__c (cstore ??)).

(** Defines the [InSStore] predicate that states that [id] is mapped
    to a value in the [sstore] of design state [??].

    Wrapper around the [In] predicate.  *)

Definition InSStore (id : ident) (?? : DState) :=
  NatMap.In id (sstore ??).


(** Design state equality relation *)

Inductive DStateEq (??1 ??2 : DState) : Prop :=
  DSEq {
      sstore_eq :
      forall id v1 v2,
        NatMap.MapsTo id v1 (sstore ??1) ->
        NatMap.MapsTo id v2 (sstore ??2) ->
        VEq v1 v2;

      cstore_eq :
      forall id ??__c1 ??__c2,
        NatMap.MapsTo id ??__c1 (cstore ??1) ->
        NatMap.MapsTo id ??__c2 (cstore ??2) ->
        DStateEq ??__c1 ??__c2
    }.

(** DStateEq is decidable *)

Lemma DStateEq_dec : forall x y, {DStateEq x y} + {~DStateEq x y}. Admitted.

(** Predicate stating that a DState [??__m] results from the
    interleaving of an origin DState [??__o], and two DState
    [??'] and [??''].

    To understand the predicate, one can consider that the states
    [??'] and [??''] result from the parallel execution of two
    concurrent statements in the context of [??__o].  

*)

Record IsMergedDState (??__o ??' ??'' ??__m : DState) : Prop :=
  IMDS {

      (* Describes the content of [(sstore ??__m)] *)
      sstore1 :
      forall id v1 v2,
        NatMap.MapsTo id v1 (sstore ??') ->
        NatMap.MapsTo id v2 (sstore ??__o) ->
        VNEq v1 v2 ->
        NatMap.MapsTo id v1 (sstore ??__m);

      sstore2 :
      forall id v1 v2,
        NatMap.MapsTo id v1 (sstore ??'') ->
        NatMap.MapsTo id v2 (sstore ??__o) ->
        VNEq v1 v2 ->
        NatMap.MapsTo id v1 (sstore ??__m);

      sstore__o :
      forall id v__o v1 v2,
        NatMap.MapsTo id v__o (sstore ??__o) ->
        NatMap.MapsTo id v1 (sstore ??') ->
        NatMap.MapsTo id v2 (sstore ??'') ->
        VEq v__o v1 ->
        VEq v__o v2 ->
        NatMap.MapsTo id v__o (sstore ??__m);

      (* Describes the content of [(cstore ??__m)] *)
      cstore1 :
      forall id ??__c1 ??__c2,
        NatMap.MapsTo id ??__c1 (cstore ??') ->
        NatMap.MapsTo id ??__c2 (cstore ??__o) ->
        ~DStateEq ??__c1 ??__c2 ->
        NatMap.MapsTo id ??__c1 (cstore ??__m);

      cstore2 :
      forall id ??__c1 ??__c2,
        NatMap.MapsTo id ??__c1 (cstore ??'') ->
        NatMap.MapsTo id ??__c2 (cstore ??__o) ->
        ~DStateEq ??__c1 ??__c2 ->
        NatMap.MapsTo id ??__c1 (cstore ??__m);

      cstore__o :
      forall id ??__co ??__c1 ??__c2,
        NatMap.MapsTo id ??__co (cstore ??__o) ->
        NatMap.MapsTo id ??__c1 (cstore ??') ->
        NatMap.MapsTo id ??__c2 (cstore ??'') ->
        DStateEq ??__co ??__c1 ->
        DStateEq ??__co ??__c2 ->
        NatMap.MapsTo id ??__co (cstore ??__m)
                      
    }.

(** Looks up the value associated to [id] in map [m1] and [m2] and
    compares it to [v0]. If values are equal then the [v0] is
    returned, otherwise the looked-up value is returned.

    Note that if [id] is not bound in [m1] or [m2], [v0] is
    returned instead of raising an error, in order to have a total
    function.  *)

Definition get_freshest_value {A : Type}
  {Aeq : A -> A -> Prop}
  (Aeq_dec : forall x y, {Aeq x y} + {~Aeq x y})
  (m1 m2 : IdMap A) (id : ident) (v0 : A) : A :=
  match find id m1 with
  | Some v1 =>
      if Aeq_dec v0 v1 then
        match find id m2 with
        | Some v2 => if Aeq_dec v0 v2 then v0 else v2
        (* Case [id] is not bound in [m1] *)
        | None => v0
        end
      else v1
  (* Case [id] is not bound in [m1] *)
  | None => v0
  end.

(** Returns a new identifier map where the identifiers bound in [m0]
    are associated with the freshest value either coming from [m1] or
    [m2], or from [m0] if an identifier is associated with the same
    value in the three maps. *)

Definition merge_idmap {A : Type}
           {Aeq : A -> A -> Prop}
           (Aeq_dec : forall x y, {Aeq x y} + {~Aeq x y})
           (m0 m1 m2 : IdMap A) : IdMap A :=
  NatMap.mapi (get_freshest_value Aeq_dec m1 m2) m0.

(** Returns a new design state resulting from the merging of the
    origin state [??0] with the two states [??1] and [??2]. *)

Definition merge (??0 ??1 ??2 : DState) : DState :=
  MkDState
    (merge_idmap value_eq_dec (sstore ??0) (sstore ??1) (sstore ??2))
    (merge_idmap DStateEq_dec (cstore ??0) (cstore ??1) (cstore ??2)).

(** Defines the relation stating that a design state [??__i] is the
    result of the "injection" of the values of map [m] in the
    [sstore] of design state [??__o]. *)

Definition IsInjectedDState (??__o : DState) (m : IdMap value) (??__i : DState) : Prop :=
  IsOverrUnion (sstore ??__o) m (sstore ??__i).

(** Overrides map [m0] with the values defined in map [m1] for all
    identifiers mapped in [m0] and [m1]. *)

Definition inj_in_map {A : Type} (m0 m1 : IdMap A) :=
  let overr_value id v := match find id m1 with
                          | Some v1 => v1
                          | None => v
                          end in
  NatMap.mapi overr_value m0.

(** Overrides the signal store of state [??] with the values of map
    [m]. *)

Definition inj (?? : DState) (m : IdMap value) : DState :=
  MkDState (inj_in_map (sstore ??) m) (cstore ??).
