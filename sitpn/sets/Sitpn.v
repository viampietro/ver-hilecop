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
      post : P -> T -> option natstar;

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
      pr_is_strict_order : StrictOrderB pr;
    }.

Notation "a '>~' b" := (pr _ a b) (at level 0).

Definition Ti (sitpn : Sitpn) : Type := { t : T sitpn | (Is t) <> None }. 
Definition Ti_in_T (sitpn : Sitpn) (t : Ti sitpn) := proj1_sig t.

(* Shortcut to express a Ti as a T using Ti_in_T as an implicit
   casting function. *)
Coercion Ti_in_T : Ti >-> T. 

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



(** Defines a predicate stating that an Sitpn is well-defined, that is: 

    - The set of places and transitions of the Sitpn must not be empty.
    - The net is a connected graph.
    - The priority relation is a strict _total_ order over the group
      of transitions in structural conflict.

 *)

Definition IsWellDefined (sitpn : Sitpn) :=
  ~NatSet.Empty (places sitpn)
  /\ ~NatSet.Empty (transitions sitpn).
