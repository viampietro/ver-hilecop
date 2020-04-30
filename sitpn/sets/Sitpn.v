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
      InP := (fun p => In p (NatSet.this places));
      P := { p | InP p };
      
      (* Alias for the set of elements that belong to the finite set [transitions]. *)
      InT := (fun t => In t (NatSet.this transitions));
      T := { t | InT t };

      (* Given a place p ∈ P and t ∈ T:

         Yields a couple (a, n) where a is the type of the input arc
         between p and t, and n is the weight of the arc (therefore,
         strictly more than zero).
         
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
      InC := (fun c => In c (NatSet.this conditions));
      C := { c | InC c };
      
      InA := (fun a => In a (NatSet.this actions));
      A := { a | InA a };

      InF := (fun f => In f (NatSet.this functions));
      F := { f | InF f };
      
      (* The function associating conditions to transitions. *)
      has_C : T -> C -> MOneZeroOne; 

      (* The function associating actions to places. *)
      has_A : P -> A -> bool;

      (* The function associating interpretation functions to
         transitions. *)
      has_F : T -> F -> bool;

      (* Priority relation between transitions. *)

      pr : T -> T -> bool;
      
    }.

(** Notations for Sitpn. *)

Notation "a '>~' b" := (pr a b) (at level 0).

(** Subsets of P and T, and misc. casting functions. *)

Definition Psubset sitpn Q := { p : P sitpn | Q p }.
Definition Psubset_in_P sitpn (Q : P sitpn -> Prop) (p : Psubset Q) := proj1_sig p.
Definition P_in_nat sitpn (p : P sitpn) : nat := proj1_sig p.
Definition nat_to_P {sitpn} p := (fun (pf : InP sitpn p) => exist _ p pf).

Definition Tsubset sitpn Q := { t : T sitpn | Q t }.
Definition Tsubset_in_T sitpn (Q : T sitpn -> Prop) (t : Tsubset Q) := proj1_sig t.
Definition T_in_nat sitpn (t : T sitpn) : nat := proj1_sig t.
Definition nat_to_T {sitpn} t := (fun (pf : InT sitpn t) => exist _ t pf).

Definition Ti (sitpn : Sitpn) := Tsubset (fun t : T sitpn => (Is t) <> None).
Definition Ti_in_T (sitpn : Sitpn) (t : Ti sitpn) := proj1_sig t.

Definition nat_to_C {sitpn} c := (fun (pf : InC sitpn c) => exist _ c pf).
Definition nat_to_A {sitpn} a := (fun (pf : InA sitpn a) => exist _ a pf).
Definition nat_to_F {sitpn} f := (fun (pf : InF sitpn f) => exist _ f pf).


(** Coercions for Sitpn. *)

Coercion P_in_nat : P >-> nat.
Coercion Psubset_in_P : Psubset >-> P.
Coercion Tsubset_in_T : Tsubset >-> T.
Coercion Ti_in_T : Ti >-> T. 
Coercion T_in_nat : T >-> nat.

(** Macro functions for Sitpn. *)

Definition P2List (sitpn : Sitpn) : list nat := NatSet.this (places sitpn).
Definition T2List (sitpn : Sitpn) : list nat := NatSet.this (transitions sitpn).
Definition C2List (sitpn : Sitpn) : list nat := NatSet.this (conditions sitpn).
Definition A2List (sitpn : Sitpn) : list nat := NatSet.this (actions sitpn).
Definition F2List (sitpn : Sitpn) : list nat := NatSet.this (functions sitpn).

(** ** Sitpn state definition. *)

(** Defines the Sitpn state structure as a record. *)

Record SitpnState (sitpn : Sitpn) :=
  BuildSitpnState {

      (* Fired set: transitions to be fired on falling edge, 
         and transitions that have been fired on rising edge.
       *)
      
      Fired : T sitpn -> Prop;
      
      (* Current marking of the Sitpn. *)
      
      M : P sitpn -> nat;

      (* Current state of time intervals. *)
      
      I : Ti sitpn -> DynamicTimeInterval;

      (* - On falling edge: orders to reset time counters at this
           cycle.  
         - On rising edge: orders to reset time counters at the
           next cycle. *)
      
      reset : Ti sitpn -> bool;

      (* Current condition (boolean) values. *)
      
      cond : C sitpn -> bool;

      (* Current activation state for continuous actions. *)
      
      exa : A sitpn -> bool;

      (* Current activation state for interpretation functions. *)
      
      exf : F sitpn -> bool;
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
    - There are no isolated (unconnected) place or transition.
    - The priority relation is a strict _total_ order over the group
      of transitions in structural conflict.
 *)

Definition IsWellDefined (sitpn : Sitpn) :=
  ~NatSet.Empty (places sitpn)
  /\ ~NatSet.Empty (transitions sitpn)
  /\ HasNoIsolatedPlace sitpn
  /\ HasNoIsolatedTransition sitpn
  /\ PriorityRelIsWellDefined sitpn.
