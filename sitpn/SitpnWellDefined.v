(** * Well-definition predicate for the Sitpn Structure. *)

Require Import CoqLib.
Require Import GlobalTypes.
Require Import sitpn.Sitpn.
Require Import sitpn.SitpnFacts.
Require Import sitpn.SitpnTypes.
Require Import sitpn.SitpnSemanticsDefs.
Require Import sitpn.SitpnUtils.

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

(* States that [{a, b}] is a pair in list [l] *)

Definition IsAPair {A : Type} (eqA : A -> A -> Prop) (a b : A) (l : list A) :=
  InA eqA a l /\ InA eqA b l /\ ~eqA a b.

Definition ForallPair {A : Type} (eqA : A -> A -> Prop) (P : A -> A -> Prop) (l : list A) : Prop:=
  forall a b, IsAPair eqA a b l -> P a b.

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

Definition MutualExcl {sitpn} (t t' : T sitpn) :=
  MutualExclByInhib t t' \/ MutualExclByConds t t'.

(* States that in a given conflict group, conflicts are solved by
   mutual exclusion for all pair of transitions. *)

Definition AllConflictsSolvedByMutualExcl sitpn (cg : list (T sitpn)) :=
  ForallPair (@Teq sitpn) MutualExcl cg.

(* States that for a given [sitpn], and for a given conflict group
   [cg], the priority relation is a strict total order of the elements
   of [cg]. *)

Definition PrIsTotalOverConflictGroup sitpn (cg : list (T sitpn)) : Prop :=
  IsStrictTotalOrder
    { t | InA (@Teq sitpn) t cg }
    (fun t t' => (@Teq sitpn (proj1_sig t) (proj1_sig t')))
    (fun t t' => @pr sitpn (proj1_sig t) (proj1_sig t')).

(* For all place [p], and conflicting output transitions of [p], all
   pairs of conflict are either solved by mutual exclusion or the
   priority relation is a strict total order over the set of
   conflicting output transitions of [p]. *)

Definition AllConflictsSolved (sitpn : Sitpn) :=
  forall (p : P sitpn),
    AllConflictsSolvedByMutualExcl (coutputs_of_p p)
    \/ PrIsTotalOverConflictGroup (coutputs_of_p p).

(** Defines a predicate stating that an [Sitpn] is well-defined, that is: 

    - The set of places and transitions of the [Sitpn] must not be empty.
    - There are no isolated (unconnected) place or transition.
    - The priority relation is a strict order over the set
      of transitions.
    - All conflicts are solved thanks to the priority relation
      or another mean of mutual exclusion.
 *)

Record IsWellDefined (sitpn : Sitpn) :=
  {
    pls_not_empty : places sitpn <> nil;
    trs_not_empty : transitions sitpn <> nil;
    no_iso_pl : HasNoIsolatedPlace sitpn;
    no_iso_tr : HasNoIsolatedTransition sitpn;
    all_confl_solved : AllConflictsSolved sitpn;
  }.

