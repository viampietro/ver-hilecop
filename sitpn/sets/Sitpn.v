(** * Sitpn and Sitpn state definitions. *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import NatSet.
Require Import SitpnTypes.
Require Import Datatypes.

Import ListNotations.

Set Implicit Arguments.

(** ** Sitpn structure definition. *)

(** Defines the Sitpn structure as a record. *)

Record Sitpn  :=
  BuildSitpn {
      
      (* A PlaceSet object representing the finite set of places. *)
      places : NatSet.t;

      (* A TransitionSet object representing the finite set of transitions. *)
      transitions : NatSet.t;
      
      (* Alias for the set of elements that belong to the finite set [places]. *)
      P := { p | In p (NatSet.this places) };
      
      (* Alias for the set of elements that belong to the finite set [transitions]. *)
      T := { t | In t (NatSet.this transitions) };

      (* 
         Given a place p ∈ P and t ∈ T:

         Yields a couple (a, n) where a is the type of the input arc
         between the place and transition in parameter, and n is the
         weight of the arc (therefore, strictly more than zero).  
         
         Yields None if there is no arc between p and t.
         
       *)
      pre : P -> T -> option (ArcT * natstar);
      
      (* The function associating a weight to transition-place edges. *)
      post : T -> P -> option natstar;

      (* The initial marking of the SITPN. *)
      M0 : P -> nat;

      (* Associates a static time interval to certain transitions 
       * of the SITPN.
       *
       * For a given sitpn : Sitpn, and a transition t : Trans, 
       * Is sitpn t = None if no time interval
       * is associated with t in sitpn. *)
      Is : T -> option StaticTimeInterval;

      (* Finite sets of conditions, actions and functions. *)
      conditions : NatSet.t;
      actions : NatSet.t;
      functions : NatSet.t;

      (* Aliases for the set of elements that belong to the finite set
         [conditions] (resp. [actions] and [functions]). *)
      C := { c | NatSet.In c conditions };
      A := { a | NatSet.In a actions };
      F := { f | NatSet.In f functions };
      
      (* The function associating conditions to transitions. *)
      has_C : T -> C -> MOneZeroOne; 

      (* The function associating actions to places. *)
      has_A : P -> A -> bool;

      (* The function associating interpretation functions to
         transitions. *)
      has_F : T -> F -> bool;

      (* Priority relation between transitions. *)

      pr : T -> T -> bool;

      (* The priority relation is a strict order over set T. *)
      pr_is_strict_order : IsStrictOrderBRel pr;
    }.

Notation "a '>~' b" := (pr _ a b) (at level 0).

Definition Psubset sitpn Q := { p : P sitpn | Q p }.
Definition Psubset_in_P sitpn (Q : P sitpn -> Prop) (p : Psubset Q) := proj1_sig p.
Definition P_in_nat sitpn (p : P sitpn) : nat := proj1_sig p.

Definition Tsubset sitpn Q := { t : T sitpn | Q t }.
Definition Tsubset_in_T sitpn (Q : T sitpn -> Prop) (t : Tsubset Q) := proj1_sig t.
Definition T_in_nat sitpn (t : T sitpn) : nat := proj1_sig t.

Definition Ti (sitpn : Sitpn) := Tsubset (fun t : T sitpn => (Is t) <> None).
Definition Ti_in_T (sitpn : Sitpn) (t : Ti sitpn) := proj1_sig t.

(* Shortcut to express elements of subset of P and T as elements of P
   and T. *)

Coercion P_in_nat : P >-> nat.
Coercion Psubset_in_P : Psubset >-> P.
Coercion Tsubset_in_T : Tsubset >-> T.
Coercion Ti_in_T : Ti >-> T. 
Coercion T_in_nat : T >-> nat.

(** ** Sitpn state definition. *)

(** Defines the Sitpn state structure as a record. *)

Record SitpnState (sitpn : Sitpn) :=
  BuildSitpnState {

      (* Fired set: transitions to be fired on falling edge, 
         and transitions that have been fired on rising edge.
       *)
      
      Fired : (T sitpn) -> Prop;
      
      (* Current marking of the Sitpn. *)
      
      M : (P sitpn) -> nat;

      (* Current state of time intervals. *)
      
      I : (Ti sitpn) -> DynamicTimeInterval;

      (* - On falling edge: orders to reset time counters at this
           cycle.  
         - On rising edge: orders to reset time counters at the
           next cycle. *)
      
      reset : (Ti sitpn) -> bool;

      (* Current condition (boolean) values. *)
      
      cond : (C sitpn) -> bool;

      (* Current activation state for continuous actions. *)
      
      exa : (A sitpn) -> bool;

      (* Current activation state for interpretation functions. *)
      
      exf : (F sitpn) -> bool;
    }.

(** ** Well-definition predicate for an Sitpn. *)


(** States that a given place [p] of [sitpn] is isolated.  *)

Definition PlaceIsIsolated (sitpn : Sitpn) (p : P sitpn) : Prop :=
  forall t, pre p t = None /\ post t p = None.

(** States that [sitpn] has no isolated place. *)

Definition HasNoIsolatedPlace (sitpn : Sitpn) : Prop :=
  forall (p : P sitpn), ~PlaceIsIsolated p.

(** States that a given transition [t] of [sitpn] is isolated.  *)

Definition TransitionIsIsolated (sitpn : Sitpn) (t : T sitpn) : Prop :=
  forall p, pre p t = None /\ post t p = None.

(** States that [sitpn] has no isolated transition. *)

Definition HasNoIsolatedTransition (sitpn : Sitpn) : Prop :=
  forall (t : T sitpn), ~TransitionIsIsolated t.

(** ** Priority relation as a strict total order for conflict groups. *)

(** States that two transition are in conflict through a group of
    places. *)

Inductive AreInConflictThroughPlaces sitpn (t t' : T sitpn) : list (P sitpn) -> Prop :=
| AreInCTPCommonPlace :
    forall p,
      pre p t <> None ->
      pre p t' <> None ->
      AreInConflictThroughPlaces t t' [p]
| AreInCTPTrans :
    forall Pc Pc' t'',
      AreInConflictThroughPlaces t t'' Pc ->
      AreInConflictThroughPlaces t'' t' Pc' ->
      AreInConflictThroughPlaces t t' (Pc ++ Pc').

(** For a given [sitpn], defines the equivalence relation [eq_trans]
    between two transitions as the equality between the first element
    of the [sig] type [T sitpn].  *)

Definition eq_trans sitpn (t t' : T sitpn) : Prop := proj1_sig t = proj1_sig t'.

(** Equivalence relation between two transitions that are elements of
    a subset of T. *)

Definition eq_trans' sitpn (Q : T sitpn -> Prop) (t t' : Tsubset Q) : Prop :=
  eq_trans (proj1_sig t) (proj1_sig t').

(** The equivalence relation [eq_trans] is decidable. *)

Definition eq_trans_dec sitpn : forall x y : T sitpn, {eq_trans x y} + {~eq_trans x y}.
  unfold eq_trans. decide equality.
Defined.

(** The equivalence relation [eq_trans'] is also decidable. *)

Definition eq_trans'_dec sitpn (Q : T sitpn -> Prop) :
  forall x y : Tsubset Q, {eq_trans' x y} + {~eq_trans' x y}.
  unfold eq_trans'. intros. 
  exact (eq_trans_dec (proj1_sig x) (proj1_sig y)).
Defined.

(** Priority relation between two transitions that are elements
    of a subset of T.
 *)

Definition pr' sitpn (Q : T sitpn -> Prop) (t t' : Tsubset Q) : bool :=
  pr (proj1_sig t) (proj1_sig t').

(** States that a group of transitions is a conflict group. *)

Definition IsConflictGroup sitpn (Tc : list (T sitpn)) : Prop :=
  exists Pc : list (P sitpn),
    let InPc := (fun pc => List.In pc Pc) in
    let InTc := (fun tc => List.In tc Tc) in
    (forall p : Psubset InPc, forall t, pre p t <> None -> List.In t Tc)
    /\ (forall t : Tsubset InTc, forall p, pre p t <> None -> List.In p Pc)
    /\ (forall t t' : Tsubset InTc, ~eq_trans t t' -> AreInConflictThroughPlaces t t' Pc).

(** States that the priority relation of a given [sitpn] is
    well-defined, that is, the priority relation is a strict total
    order over the elements of each conflict group of transitions. *)

Definition PriorityRelIsWellDefined (sitpn : Sitpn) : Prop :=
  forall Tc : list (T sitpn),
    IsConflictGroup Tc ->
    let InTc := (fun tc => List.In tc Tc) in
    @IsStrictTotalOrderBRel (Tsubset InTc) (@eq_trans' sitpn InTc) (@eq_trans'_dec sitpn InTc) (@pr' sitpn InTc).

(** Defines a predicate stating that an Sitpn is well-defined, that is: 

    - The set of places and transitions of the Sitpn must not be empty.
    - The priority relation is a strict _total_ order over the group
      of transitions in structural conflict.
    - There are no isolated (unconnected) place or transition.
 *)

Definition IsWellDefined (sitpn : Sitpn) :=
  ~NatSet.Empty (places sitpn)
  /\ ~NatSet.Empty (transitions sitpn)
  /\ HasNoIsolatedPlace sitpn
  /\ HasNoIsolatedTransition sitpn
  /\ PriorityRelIsWellDefined sitpn.
