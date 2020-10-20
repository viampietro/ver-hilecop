(** * Well-definition predicate for the Sitpn Structure. *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import dp.Sitpn.
Require Import dp.SitpnFacts.
Require Import dp.SitpnTypes.

Set Implicit Arguments.

(** ** Well-definition of the transition and place sets *)

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

(** ** Well-definition of the priority relation *)

Definition PriorityRelIsWellDefined (sitpn : Sitpn) :=
  IsStrictOrderBRel (@pr sitpn).

(** ** Definitions about transitions in conflict *)

(* Two different transitions are in structural confict if there exists
   a common input place connecting them by mean of a basic arc.  *)

Definition InStructConflict {sitpn} (t t' : T sitpn) :=
  ~Teq t t' /\ exists p ω ω', pre p t = Some (basic, ω) /\ pre p t' = Some (basic, ω').

(* Cases of mutual exclusion between two transitions *)

Definition MutualExclByInhib {sitpn} (t t' : T sitpn) :=
  exists p ω ω', pre p t = Some (basic, ω) /\ pre p t' = Some (inhibitor, ω')
                 \/ pre p t = Some (inhibitor, ω) /\ pre p t' = Some (basic, ω').

Definition MutualExclByConds {sitpn} (t t' : T sitpn) :=
  exists c, has_C t c = one /\ has_C t' c = mone
            \/ has_C t c = mone /\ has_C t' c = one.

Definition MutualExclByTimeItvals {sitpn} (t t' : T sitpn) :=
  exists i i', Is t = Some i /\ Is t' = Some i' /\ NoOverlap i i'.

Definition MutualExcl {sitpn} (t t' : T sitpn) :=
  MutualExclByInhib t t' \/ MutualExclByConds t t' \/ MutualExclByTimeItvals t t'.

(* States that the conflict between two transitions is solved either
   thanks to the priority relation, or by other means of mutual
   execlusion. *)

Definition ConflictSolved {sitpn} (t t' : T sitpn) (conflict : InStructConflict t t') :=
  IsStrictOrderBRel (@pr sitpn) /\
  (AreComparableWithBRel t t' (@pr sitpn) \/ ~AreComparableWithBRel t t' (@pr sitpn) /\ MutualExcl t t').

(* [True] if transitions [t] and [t'] are not in structural conflict
   or if the conflict is solved.  *)

Definition NoConflictOrConflictSolved {sitpn} (t t' : T sitpn) :=
  ~InStructConflict t t'
  \/ forall (conflict : InStructConflict t t'), ConflictSolved conflict.

(* For all couple of transitions of [sitpn], either the couple is not
   in conflict or the conflict is solved *)

Definition AllConflictsSolved (sitpn : Sitpn) :=
  forall t t' : T sitpn, NoConflictOrConflictSolved t t'.

(** Defines a predicate stating that the list of nat used in an
    [Sitpn] structure to implement finite sets respect the [Nodup]
    constraint. 

    We define this property in a separate predicate because it is
    an implementation-dependent property.
 *)

Definition AreWellImplementedFiniteSets (sitpn : Sitpn) : Prop :=
  NoDup (places sitpn)
  /\ NoDup (transitions sitpn)
  /\ NoDup (conditions sitpn)
  /\ NoDup (actions sitpn)
  /\ NoDup (functions sitpn).

(** Defines a predicate stating that an Sitpn is well-defined, that is: 

    - The set of places and transitions of the Sitpn must not be empty.
    - There are no isolated (unconnected) place or transition.
    - The priority relation is a strict _total_ order over the group
      of transitions in structural conflict.
 *)

Definition IsWellDefined (sitpn : Sitpn) :=
  places sitpn <> nil
  /\ transitions sitpn <> nil
  /\ HasNoIsolatedPlace sitpn
  /\ HasNoIsolatedTransition sitpn
  /\ PriorityRelIsWellDefined sitpn
  /\ AllConflictsSolved sitpn
                              
  (* Implementation-dependent property. *)
  /\ AreWellImplementedFiniteSets sitpn.

