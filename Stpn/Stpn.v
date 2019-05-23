(* Import standard library modules. *)

Require Import Omega.

(* Import Spn module. *)

Require Import Hilecop.Spn.Spn.

(*! ============================================== !*)
(*! TYPES FOR SYNCHRONOUSLY EXECUTED, GENERALIZED, !*)
(*! EXTENDED, TIME PETRI NETS.                     !*)
(*! ============================================== !*)

(** * Types for Synchronously executed, generalized, extended, Time Petri Nets *)

(** Defines the inductive type to express positive or (positively)
    infinite values.  Useful to type the upper bound of the time
    interval in [TimeInterval]. *)

Inductive PositiveIntervalBound : Set :=
| pos_inf : PositiveIntervalBound
| pos_val : nat -> PositiveIntervalBound.

(** Defines the time interval structure associated with transitions. *)

Structure TimeInterval : Set :=
  mk_TimeItval {
      min_t : nat;
      max_t : PositiveIntervalBound;
    }.

(** ** Properties on [TimeInterval] *)

(** Predicate telling if a given [itval] is well-formed according to
    Hilecop standard.
    
    A itval is well-formed if its lower bound is greater than 0 and
    less than or equal to its upper bound. 

    This predicate doesn't stand for DynamicTimeInterval,
    as in dynamic time intervals, bounds can take zero as value.
 *)

Definition IsWellFormedTimeInterval (itval : TimeInterval) : Prop :=
  match itval with
  | mk_TimeItval min_t max_t =>
    (* Checks min_t and max_t structure. *)
    match min_t, max_t with
    (* If min_t equals O then itval is ill-formed. *)
    | O, _ => False
    (* If max_t is infinite then itval is well-formed. *)
    | _, pos_inf => True
    (* Else if max_t has a finite positive value, then 
     * checks that it is greater than or equal to min_t. *)
    | _, pos_val max_val => min_t <= max_val
    end
  end.

(** Defines the dynamic time interval type. 
    
    Differentiate the behavior of static and dynamic time
    intervals as in the STPN semantics.

    A dynamic time interval is either active or blocked. *)

Inductive DynamicTimeInterval : Set :=
| active : TimeInterval -> DynamicTimeInterval
| blocked : DynamicTimeInterval.

(** Defines the Stpn structure.
 
    Basically, same structure as an [Spn] with time intervals
    associated to transitions.  (At most one interval by transition,
    or None)
 
    Note that [static_intervals] associates static time interval
    (denoted by the TimeInterval type) to transitions.

    [Stpn] is declared as a coercion of [Spn]. *)

Structure Stpn : Set :=
  mk_Stpn {
      static_intervals : list (Trans * option TimeInterval);
      spn :> Spn
    }.

(** ** Properties on [Stpn] *)

(** *** Properties on [Stpn.(static_intervals)] *)

(** All intervals in [Stpn.(static_intervals)] are well-formed. *)

Definition AreWellFormedTimeIntervals (stpn : Stpn) :=
  forall (chrono : TimeInterval),
    In (Some chrono) (snd (split stpn.(static_intervals))) -> IsWellFormedTimeInterval chrono.

(** All transitions in [Stpn.(static_intervals)] are in the list of
    transitions [Stpn.(transs)]. *)

Definition NoUnknownTransInTimeIntervals (stpn : Stpn) :=
  stpn.(transs) = fst (split stpn.(static_intervals)).

(** *** Properties on the whole [Stpn]. *)

Definition IsWellDefinedStpn (stpn : Stpn) :=
  AreWellFormedTimeIntervals stpn /\
  NoUnknownTransInTimeIntervals stpn /\
  IsWellDefinedSpn stpn.

(** ** Stpn state. *)

(** Defines the state of an Stpn.

    - fired, marking: same as SpnState.
      
    - intervals: contains the time interval values at the current state.
                 Implement the I function, associating dynamic time
                 interval to transitions in the STPN semantics.

    - reset: list of transitions having their intervals reset at this
             clock cycle or the next (depending on how the current
             Stpn state is reached).

             Even transitions with no intervals are referenced in the
             reset list, and possibly receive a reset order.  *)

Structure StpnState := mk_StpnState {
                           intervals  : list (Trans * option DynamicTimeInterval);
                           reset    : list (Trans * bool);
                           spnstate :> SpnState;
                         }.

(** Checks that state s is well-defined compared to stpn's structure.
    
    State s is well-defined compared to stpn if:

    - All transitions referenced in [s.(reset)] are referenced in
      [stpn.(transs)], and inversely.

    - All transitions referenced in
      [s.(intervals)] are referenced in [stpn.(static_intervals)], and
      inversely.

    - ∀ t ∈ T, (Is(t) = ∅ ∧ I(t) = ∅) ∨ (Is(t) ≠ ∅ ∧ I(t) ≠ ∅) *)

Definition IsWellDefinedStpnState (stpn : Stpn) (s : StpnState) :=
  IsWellDefinedSpnState stpn s /\
  fst (split stpn.(static_intervals)) = fst (split s.(intervals)) /\
  fst (split stpn.(static_intervals)) = fst (split s.(reset)) /\
  (forall (t : Trans),
      (In (t, None) stpn.(static_intervals) /\ In (t, None) s.(intervals)) \/
      (~In (t, None) stpn.(static_intervals) /\ ~In (t, None) s.(intervals))).

