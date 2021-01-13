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

Require Import common.GlobalTypes.
Require Import common.NatSet.

Require Import hvhdl.Environment.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SSEvaluation.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.Stabilize.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Petri.
Require Import hvhdl.HVhdlTypes.

Include HVhdlCsNotations.

(** Defines the [runinit] relation that computes all concurrent
    statements once, regardless of sensitivity lists or events on
    signals and component instances.  *)

Inductive vruninit (D__s : IdMap design) (Δ : ElDesign) (σ : DState) : cs -> DState -> Prop :=

(** Evaluates a process statement exactly once, regardless of its
    sensitivity list. *)

| VRunInitPs :
    forall pid sl vars stmt Λ σ' Λ',

      (* * Premises * *)
      vseq Δ σ Λ stab stmt σ' Λ' ->
      
      (* * Side conditions * *)
      
      (* Process id maps to the local environment Λ in elaborated design Δ *)
      NatMap.MapsTo pid (Process Λ) Δ ->
      
      (* * Conclusion * *)
      vruninit D__s Δ σ (cs_ps pid sl vars stmt) σ'

(** Evaluates a component instance; the new state of the component
    instance, resulting of the interpretation of its behavior,
    registered some events. Therefore, we need to add the component
    identifier to the events field in the state of the
    embedding design. *)

| VRunInitCompEvents :
    forall {compid entid gmap ipmap opmap d
                   Δ__c σ__c σ__c' σ__c'' σ'},
      
      (* * Premises * *)

      (* Injects input port values into component state *)
      mapip Δ Δ__c σ σ__c ipmap σ__c' ->

      (* Executes component behavior *)
      vruninit D__s Δ__c σ__c' (behavior d) σ__c'' ->

      (* Propagates output port values to embedded design *)
      mapop Δ Δ__c σ σ__c'' opmap σ' ->
      
      (* * Side conditions * *)

      (* Identifier [entid] is associated to design [d] in design store [D__s] *)
      NatMap.MapsTo entid d D__s ->
      
      (* [compid ∈ Comps(Δ) and Δ(compid) = Δ__c] *)
      NatMap.MapsTo compid (Component Δ__c) Δ ->
      
      (* [compid ∈ σ and σ(compid) = σ__c] *)
      NatMap.MapsTo compid σ__c (compstore σ) ->

      (* Events registered in σc''. *)
      events σ__c'' <> NatSet.empty ->
      
      (* * Conclusion * *)
      
      (* Add compid to the events field of σ' because compid
         registered some events in its internal state. *)
      
      vruninit D__s Δ σ (cs_comp compid entid gmap ipmap opmap) (events_add compid σ')

(** Evaluates a component instance; the new state of the component
    instance, resulting of the interpretation of its behavior,
    registered no events. *)

| VRunInitCompNoEvent :
    forall {compid entid gmap ipmap opmap d
                   Δ__c σ__c σ__c' σ__c'' σ'},
      
      (* * Premises * *)
      mapip Δ Δ__c σ σ__c ipmap σ__c' ->
      vruninit D__s Δ__c σ__c' (behavior d) σ__c'' ->
      mapop Δ Δ__c σ σ__c'' opmap σ' ->
      
      (* * Side conditions * *)

      (* Identifier [entid] is associated to design [d] in design store [D__s] *)
      NatMap.MapsTo entid d D__s ->

      (* compid ∈ Comps(Δ) and Δ(compid) = (Δ__c, cstmt) *)
      NatMap.MapsTo compid (Component Δ__c) Δ ->
      
      (* compid ∈ σ and σ(compid) = \sigma__c *)
      NatMap.MapsTo compid σ__c (compstore σ) ->

      (* No event registered in \sigma__c''. *)
      events σ__c'' = NatSet.empty ->
      
      (* * Conclusion * *)
      vruninit D__s Δ σ (cs_comp compid entid gmap ipmap opmap) σ'

(** Evaluates the null concurrent statement.  *)

| VRunInitNull : vruninit D__s Δ σ cs_null σ
                          
(** Evaluates the parallel execution of two concurrent
    statements computed with the [runinit] relation.  *)
               
| VRunInitPar :
    forall {cstmt cstmt' σ' σ'' merged},

      (* * Premises * *)
      vruninit D__s Δ σ cstmt σ' ->
      vruninit D__s Δ σ cstmt' σ'' ->

      (* * Side conditions * *)
      
      (* E ∩ E' = ∅ ⇒ enforces the "no multiply-driven signals" condition. *)
      NatSet.inter (events σ') (events σ'') = NatSet.empty ->

      (* States that merged is the result of the merging 
         of states \sigma, \sigma' and \sigma''. *)
      IsMergedDState σ σ' σ'' merged ->
      
      (* * Conclusion * *)
      vruninit D__s Δ σ (cstmt // cstmt') merged.

(** Defines the [init] relation, sequential composition of the
    [vruninit] and the [stabilize] relation. *)

Inductive init (D__s : IdMap design) (Δ : ElDesign) : DState -> cs -> DState -> Prop :=

| Init :
    forall σ behavior σ' σ'' θ,

      (* * Premises * *)

      (* Sets the rst (i.e, reset) signal to ⊥ to trigger the
         evaluation of code related to "factory reset".  *)
      vruninit D__s Δ (sstore_add rst (Vbool false) σ) behavior σ' ->

      (* Sets the rst signal to ⊤, and no longer will it gain the
         value ⊥ during the whole simulation loop.  *)
      stabilize D__s Δ (sstore_add rst (Vbool true) σ') behavior θ σ'' ->
      
      (* * Conclusion * *)
      init D__s Δ σ behavior σ''.

