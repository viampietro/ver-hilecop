(** * The initialization relation. *)

(** Defines the relation that performs the initialization phase, as
    defined in the simulation loop of H-VHDL, on the behavioral part
    of a design (i.e, a concurrent statement).

    The [init] relation, defined in this file, is the sequential
    composition of the [runinit] and the [stabilize] relations.

    The [runinit] relation, also defined in this file, runs exactly
    once all concurrent statements composing the behavior of the
    simulated design.
    
 *)

Require Import Environment.
Require Import AbstractSyntax.
Require Import SSEvaluation.
Require Import PortMapEvaluation.
Require Import Stabilize.
Require Import SemanticalDomains.
Require Import GlobalTypes.
Require Import Petri.

(** Defines the [runinit] relation that computes all concurrent
    statements once, regardless of sensitivity lists or events on
    signals and component instances.  *)

Inductive vruninit (denv : DEnv) (dstate : DState) : cs -> DState -> Prop :=

(** Evaluates a process statement exactly once, regardless of its
    sensitivity list. *)

| VRunInitPs :
    forall {pid sl vars stmt lenv dstate' lenv'},

      (* * Premises * *)
      vseq denv dstate lenv stmt dstate' lenv' ->
      
      (* * Side conditions * *)
      NatMap.MapsTo pid (Process lenv) denv ->
      
      (* * Conclusion * *)
      vruninit denv dstate (cs_ps pid sl vars stmt) dstate'

(** Evaluates a component instance; the new state of the component
    instance, resulting of the interpretation of its behavior,
    registered some events. Therefore, we need to add the component
    identifier to the events field in the state of the
    embedding design. *)

| VRunInitCompEvents :
    forall {compid entid gmap ipmap opmap cstmt
                   cenv cstate cstate' cstate'' dstate'},
      
      (* * Premises * *)
      mapip denv cenv dstate cstate ipmap cstate' ->
      vruninit cenv cstate' cstmt cstate'' ->
      mapop denv cenv dstate cstate'' opmap dstate' ->
      
      (* * Side conditions * *)

      (* compid ∈ Comps(Δ) and Δ(compid) = (cenv, cstmt) *)
      NatMap.MapsTo compid (Component cenv cstmt) denv ->
      
      (* compid ∈ σ and σ(compid) = cstate *)
      NatMap.MapsTo compid cstate (compstore dstate) ->

      (* Events registered in cstate''. *)
      events cstate'' <> NatSet.empty ->
      
      (* * Conclusion * *)
      (* Add compid to the events field of dstate' because compid
         registered some events in its internal state. *)
      vruninit denv dstate (cs_comp compid entid gmap ipmap opmap) (events_add compid dstate')

(** Evaluates a component instance; the new state of the component
    instance, resulting of the interpretation of its behavior,
    registered no events. *)

| VRunInitCompNoEvent :
    forall {compid entid gmap ipmap opmap cstmt
                   cenv cstate cstate' cstate'' dstate'},
      
      (* * Premises * *)
      mapip denv cenv dstate cstate ipmap cstate' ->
      vruninit cenv cstate' cstmt cstate'' ->
      mapop denv cenv dstate cstate'' opmap dstate' ->
      
      (* * Side conditions * *)

      (* compid ∈ Comps(Δ) and Δ(compid) = (cenv, cstmt) *)
      NatMap.MapsTo compid (Component cenv cstmt) denv ->
      
      (* compid ∈ σ and σ(compid) = cstate *)
      NatMap.MapsTo compid cstate (compstore dstate) ->

      (* No event registered in cstate''. *)
      events cstate'' = NatSet.empty ->
      
      (* * Conclusion * *)
      vruninit denv dstate (cs_comp compid entid gmap ipmap opmap) dstate'

(** Evaluates the parallel execution of two concurrent
    statements computed with the [runinit] relation.  *)
               
| VRunInitPar :
    forall {cstmt cstmt' dstate' dstate'' merged},

      (* * Premises * *)
      vruninit denv dstate cstmt dstate' ->
      vruninit denv dstate cstmt' dstate'' ->

      (* * Side conditions * *)
      
      (* E ∩ E' = ∅ ⇒ enforces the "no multiply-driven signals" condition. *)
      NatSet.inter (events dstate') (events dstate'') = NatSet.empty ->

      (* States that merged is the result of the merging 
         of states dstate, dstate' and dstate''. *)
      IsMergedDState dstate dstate' dstate'' merged ->
      
      (* * Conclusion * *)
      vruninit denv dstate (cstmt // cstmt') merged.

(** Defines the [init] relation, sequential composition of the
    [vruninit] and the [stabilize] relation. *)

Inductive init (denv : DEnv) : DState -> cs -> DState -> Prop :=

| Init :
    forall {dstate behavior dstate' dstate''},

      (* * Premises * *)

      (* Sets the rst (i.e, reset) signal to ⊥ to trigger the
         evaluation of code related to "factory reset".  *)
      vruninit denv (sstore_add rst (Vbool false) dstate) behavior dstate' ->

      (* Sets the rst signal to ⊤, and no longer will it gain the
         value ⊥ during the whole simulation loop.  *)
      stabilize denv (sstore_add rst (Vbool true) dstate') behavior dstate'' ->
      
      (* * Conclusion * *)
      init denv dstate behavior dstate''.

