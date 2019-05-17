(* Import standard library modules. *)

Require Import Omega.

(* Import Spn module. *)

Require Import Hilecop.Spn.Spn.

(*! ============================================== !*)
(*! TYPES FOR SYNCHRONOUSLY EXECUTED, GENERALIZED, !*)
(*! EXTENDED, TIME PETRI NETS.                     !*)
(*! ============================================== !*)

(** * Types for Synchronous executed, generalized, extended, Time Petri Nets *)

(** Defines the inductive type to express positive or (positively)
    infinite values.  Useful to type the upper bound of the time
    interval in [Chrono]. *)

Inductive PositiveIntervalBound : Set :=
| pos_inf : PositiveIntervalBound
| pos_val : nat -> PositiveIntervalBound.

(** Defines the time interval structure associated with transitions.
    Transitions are firable when min_t <= cnt <= max_t. 

    The [blocked] field is true when cnt > max_t, meaning
    that the time counter passed the time interval. *)

Structure Chrono : Set :=
  mk_chrono {
      cnt : nat;  
      min_t : nat;
      max_t : PositiveIntervalBound;
    }.

(** ** Properties on [Chrono] *)

(** Predicate telling if a given [chrono] is well-formed according to
    Hilecop standard.
    
    A chrono is well-formed if its lower bound is greater than 0 and
    less than or equal to its upper bound. *)

Definition IsWellFormedChrono (chrono : Chrono) : Prop :=
  match chrono with
  | mk_chrono cnt min_t max_t =>
    (* Checks min_t and max_t structure. *)
    match min_t, max_t with
    (* If min_t equals O then time interval is ill-formed. *)
    | O, _ => False
    (* If max_t is infinite then chrono is well-formed. *)
    | _, pos_inf => True
    (* Else if max_t has a finite positive value, then 
     * checks that it is greater than or equal to min_t. *)
    | _, pos_val max_val => min_t <= max_val
    end
  end.

(** Defines the dynamic chrono (time interval) type. 
    
    Differentiate the behavior of static and dynamic time
    intervals as in the STPN semantics.

    A dynamic chrono is either active or blocked. *)

Inductive DynamicChrono : Set :=
| active : Chrono -> DynamicChrono
| blocked : DynamicChrono.

(** Defines the Stpn structure.
 
    Basically, same structure as an [Spn] with chronos associated to
    transitions.  (At most one chrono by transition, or None)
 
    Note that [static_chronos] associates static chrono (denoted by
    the Chrono type) to transitions.

    [Stpn] is declared as a coercion of [Spn]. *)

Structure Stpn : Set :=
  mk_Stpn {
      static_chronos : list (Trans * option Chrono);
      spn :> Spn
    }.

(** ** Properties on [Stpn] *)

(** *** Properties on [Stpn.(chronos)] *)

(** All chronos in [Stpn.(chronos)] are well-formed. *)

Definition AreWellFormedChronos (stpn : Stpn) :=
  forall (chrono : Chrono),
    In (Some chrono) (snd (split stpn.(static_chronos))) -> IsWellFormedChrono chrono.

(** All transitions in [Stpn.(chronos)] are in the list of transitions [Stpn.(transs)]. *)

Definition NoUnknownTransInChronos (stpn : Stpn) :=
  stpn.(transs) = fst (split stpn.(static_chronos)).

(** *** Properties on the whole [Stpn]. *)

Definition IsWellDefinedStpn (stpn : Stpn) :=
  AreWellFormedChronos stpn /\ NoUnknownTransInChronos stpn /\ IsWellDefinedSpn stpn.(spn).

(** ** Stpn state. *)

(** Defines the state of an Stpn.

    - fired, marking: same as SpnState.
      
    - chronos: contains the chronos value at the current state.
               Implement the I function, associating dynamic time
               interval to transitions in the STPN semantics.

    - reset: list of transitions having their chronos reset at this
             clock cycle or the next (depending on how the current
             Stpn state is reached).

 *)

Structure StpnState := mk_StpnState {
                           chronos  : list (Trans * option DynamicChrono);
                           reset    : list (Trans * option bool);
                           spnstate :> SpnState;
                         }.

(** Checks that state s is well-defined compared to stpn's structure.
    
    State s is well-defined compared to stpn if:

    - All transitions referenced in [s.(reset)] are referenced in
      [stpn.(transs)], and inversely.

    - All transitions referenced in
      [s.(chronos)] are referenced in [stpn.(static_chronos)], and
      inversely.

    - ∄ t ∈ T, Is(t) ≠ ∅ ∧ (I(t) = ∅ ∨ reset(t) = ∅)
    - ∄ t ∈ T, Is(t) = ∅ ∧ (I(t) ≠ ∅ ∨ reset(t) ≠ ∅)

 *)

Definition IsWellDefinedStpnState (stpn : Stpn) (s : StpnState) :=
  IsWellDefinedSpnState stpn s /\
  fst (split stpn.(static_chronos)) = fst (split s.(chronos)) /\
  fst (split stpn.(static_chronos)) = fst (split s.(reset)) /\
  (forall (t : Trans) (chrono : Chrono),
      In (t, Some chrono) stpn.(static_chronos) ->
      ~In (t, None) s.(chronos) /\ ~In (t, None) s.(reset)) /\
  (forall (t : Trans),
      In (t, None) stpn.(static_chronos) ->
      In (t, None) s.(chronos) /\ In (t, None) s.(reset)).

