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
  IsStrictOrder (T sitpn) (@pr sitpn).

(** ** Definitions about transitions in conflict *)

(** Conflict group: a maximal subset of transitions that a linked to a
    common input place by a basic arc. *)

Definition IsConflictGroupOfP sitpn (p : P sitpn) (cg : list (T sitpn)) : Prop :=
  NoDup cg /\ (forall t, List.In t cg <-> exists ω, pre p t = Some (basic, ω)).

Definition IsConflictGroup sitpn (cg : list (T sitpn)) : Prop :=
  exists p, IsConflictGroupOfP p cg.

(* States that [{a, b}] is a pair in list [l] *)

Definition IsAPair {A : Type} (a b : A) (l : list A) :=
  List.In a l /\ List.In b l /\ a <> b.

Definition ForallPair {A : Type} (P : A -> A -> Prop) (l : list A) : Prop:=
  forall a b, IsAPair a b l -> P a b.

(* Cases of mutual exclusion between two transitions 

   TO DO: 
   - Add mutual exclusion by mean of an "anneau memoire" 

 *)

(* Two transitions are in mutual exclusion by mean of an inhibitor arc
   if there exists a common input place connecting [t] by a basic arc
   and [t'] by an inhibitor arc, or the other way around.

   Note that the two connecting arcs must have the same weight to be
   mutually exclusive.

 *)

Definition MutualExclByInhib {sitpn} (t t' : T sitpn) :=
  exists p ω, (pre p t = Some (basic, ω) \/ pre p t = Some (test, ω)) /\ pre p t' = Some (inhibitor, ω)
              \/
              pre p t = Some (inhibitor, ω) /\ (pre p t' = Some (basic, ω) \/ pre p t' = Some (test, ω)).

(* Two transitions are in mutual exclusion by mean of inverse
   conditions if there exists a condition [c] associated to [t], and
   the inverse of condition [c] associated to [t']. *)

Definition MutualExclByConds {sitpn} (t t' : T sitpn) :=
  exists c, has_C t c = one /\ has_C t' c = mone
            \/ has_C t c = mone /\ has_C t' c = one.

(* Two transitions are in mutual exclusion thanks to time intervals if
   the two transitions are associated to time intervals that are not
   overlapping; i.e, [a,b] and [c,d] are not overlapping if b < c or 
   d < a (and the two intervals must be well-formed).
 *)

Definition MutualExclByTimeItvals {sitpn} (t t' : T sitpn) :=
  exists i i', Is t = Some i /\ Is t' = Some i' /\ NoOverlap i i'.

Definition MutualExcl {sitpn} (t t' : T sitpn) :=
  MutualExclByInhib t t' \/ MutualExclByConds t t' \/ MutualExclByTimeItvals t t'.

(* States that in a given conflict group, conflicts are solved by
   mutual exclusion for all pair of transitions. *)

Definition AllConflictsSolvedByMutualExcl sitpn (cg : list (T sitpn)) (pf : IsConflictGroup cg) :=
  ForallPair MutualExcl cg.

(* States that for a given [sitpn], and for a given conflict group
   [cg], the priority relation is a strict total order of the elements
   of [cg]. *)

Definition PrIsTotalOverConflictGroup sitpn (cg : list (T sitpn)) (pf : IsConflictGroup cg) : Prop.
  refine (IsStrictTotalOrderOverList (T sitpn) (@Teq sitpn) (@pr sitpn) cg _);
    unfold IsConflictGroup in pf;
    inversion pf as (p, pf'); unfold IsConflictGroupOfP in pf'; apply (proj1 pf').
Defined.

(* For all couple of transitions (in the set of transitions of
   [sitpn]), either the couple is not in conflict or the conflict is
   solved *)

Definition AllConflictsSolved (sitpn : Sitpn) :=
  forall (cg : list (T sitpn)) (pf : IsConflictGroup cg),
    AllConflictsSolvedByMutualExcl pf \/ PrIsTotalOverConflictGroup pf.

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

(** Defines a predicate stating that an [Sitpn] is well-defined, that is: 

    - The set of places and transitions of the [Sitpn] must not be empty.
    - There are no isolated (unconnected) place or transition.
    - The priority relation is a strict order over the set
      of transitions.
    - All conflicts are solved thanks to the priority relation
      or another mean of mutual exclusion.
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

