(** * Well-definition predicate for the Sitpn Structure. *)

Require Import CoqLib.
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

Record AreWellImplementedFiniteSets (sitpn : Sitpn) : Prop :=
  {
  nodup_pls : NoDup (places sitpn);
  nodup_trs : NoDup (transitions sitpn);
  nodup_conds : NoDup (conditions sitpn);
  nodup_actions : NoDup (actions sitpn);
  nodup_funs : NoDup (functions sitpn);
  }.

(* Defines a predicate stating that the functions [pre, post, M0, I__s,
   has_C, has_A, has_F] and also the [pr] relation of a given [sitpn],
   yield the same value for inputs that verify the [P1SigEq] relation.
   
 *)

Record AreWellImplementedFunsAndRel (sitpn : Sitpn) := {
  wi_pre : forall p1 p2 t1 t2, Peq p1 p2 -> Teq t1 t2 -> @pre sitpn p1 t1 = @pre sitpn p2 t2;
  wi_post : forall p1 p2 t1 t2, Peq p1 p2 -> Teq t1 t2 -> @post sitpn t1 p1 = @post sitpn t2 p2;
  wi_M0 : forall p1 p2, Peq p1 p2 -> @M0 sitpn p1 = @M0 sitpn p2;
  wi_Is : forall t1 t2, Teq t1 t2 -> @Is sitpn t1 = @Is sitpn t2;
  wi_has_C : forall t1 t2 c1 c2, Teq t1 t2 -> Ceq c1 c2 -> @has_C sitpn t1 c1 = @has_C sitpn t2 c2;
  wi_has_A : forall p1 p2 a1 a2, Peq p1 p2 -> Aeq a1 a2 -> @has_A sitpn p1 a1 = @has_A sitpn p2 a2;
  wi_has_F : forall t1 t2 f1 f2, Teq t1 t2 -> Feq f1 f2 -> @has_F sitpn t1 f1 = @has_F sitpn t2 f2;
  wi_pr : forall t1 t2 t3 t4, Teq t1 t2 -> Teq t3 t4 -> @pr sitpn t1 t3 <-> @pr sitpn t2 t4;
  }.

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
  pr_wd : PriorityRelIsWellDefined sitpn;
  all_confl_solved : AllConflictsSolved sitpn;
                              
  (* Implementation-dependent property. *)
  wi_fsets : AreWellImplementedFiniteSets sitpn;
  wi_funs : AreWellImplementedFunsAndRel sitpn;
  }.

