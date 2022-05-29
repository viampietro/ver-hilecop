(** * Evaluation of combinational concurrent statements. *)

(** Defines the relation that evaluates combinational concurrent
    statements; used in the stabilization phases. *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.NatSet.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.SSEvaluation.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.HVhdlTypes.

(** Defines the relation that evaluates combinational
    concurrent statements. *)

Inductive vcomb (D__s : IdMap design) (Δ : ElDesign) (σ : DState) : cs -> DState -> Prop :=

(** Evaluates a process. *)

| VCombPs :
    forall id__p sl vars stmt Λ σ' Λ',

      (* * Premises * *)
      vseq Δ σ (NoEvDState σ) Λ stab stmt σ' Λ' ->
      
      (* * Side conditions * *)
      NatMap.MapsTo id__p (Process Λ) Δ -> (* [id__p ∈ Δ and Δ(id__p) = Λ] *)
      
      (* * Conclusion * *)
      vcomb D__s Δ σ (cs_ps id__p sl vars stmt) σ'

(** Evaluates a component instance. The new state of the component
    instance, resulting of the interpretation of its behavior,
    registered some events. *)

| VCombCompEvents :
    forall id__c id__e g i o d Δ__c σ__c σ__c' σ__c'' σ',
      
      (* * Premises * *)
      mapip Δ Δ__c σ σ__c i σ__c' ->
      vcomb D__s Δ__c σ__c' (behavior d) σ__c'' ->
      mapop Δ Δ__c (NoEvDState σ) σ__c'' o σ' ->
      
      (* * Side conditions * *)

      (* [id__e] is associated to design [d] in design store [D__s] *)
      NatMap.MapsTo id__e d D__s ->
      
      (* [id__c ∈ Comps(Δ) and Δ(id__c) = Δ__c] *)
      NatMap.MapsTo id__c (Component Δ__c) Δ ->
      
      (* [id__c ∈ σ and σ(id__c) = σ__c] *)
      NatMap.MapsTo id__c σ__c (cstore σ) ->

      (* [Events registered in σ__c''.] *)
      (events σ__c'') <> NatSet.empty ->
      
      (* * Conclusion * *)
      
      (* Add [id__c] to the events set of [σ'] because id__c
         registered some events in its internal state.
         
         Associates [id__c] to its new state [σ__c''] in the component
         store of σ'. *)
      vcomb D__s Δ σ (cs_comp id__c id__e g i o) (cstore_add id__c σ__c'' (events_add id__c σ'))

(** Evaluates a component instance. The new state of the component
    instance, resulting of the interpretation of its behavior,
    registered no events. *)

| VCombCompNoEvent :
    forall id__c id__e g i o d Δ__c σ__c σ__c' σ__c'' σ',
      
      (* * Premises * *)
      mapip Δ Δ__c σ σ__c i σ__c' ->
      vcomb D__s Δ__c σ__c' (behavior d) σ__c'' ->
      mapop Δ Δ__c (NoEvDState σ) σ__c'' o σ' ->
      
      (* * Side conditions * *)
      
      (* [id__e] is associated to design [d] in design store [D__s] *)
      NatMap.MapsTo id__e d D__s ->
      
      (* [id__c ∈ Comps(Δ)] and [Δ(id__c) = Δ__c] *)
      NatMap.MapsTo id__c (Component Δ__c) Δ ->
      
      (* [id__c ∈ σ] and [σ(id__c) = σ__c] *)
      NatMap.MapsTo id__c σ__c (cstore σ) ->

      (* No event registered in [σ__c'']. *)
      (events σ__c'') = NatSet.empty ->
      
      (* * Conclusion * *)
      vcomb D__s Δ σ (cs_comp id__c id__e g i o) σ'

(** Evaluates the null concurrent statement. *)

| VCombNull : vcomb D__s Δ σ cs_null (NoEvDState σ) 
            
(** Evaluates the parallel execution of two combinational concurrent
    statements.  *)
            
| VCombPar :
    forall {cstmt cstmt' σ' σ'' merged},

      (* * Premises * *)
      vcomb D__s Δ σ cstmt σ' ->
      vcomb D__s Δ σ cstmt' σ'' ->

      (* * Side conditions * *)
      
      (* E ∩ E' = ∅ ⇒ enforces the "no multiply-driven signals" condition. *)
      NatSet.Equal (NatSet.inter (events σ') (events σ'')) NatSet.empty ->

      (* States that merged is the result of the merging 
         of states σ, σ' and σ''. *)
      IsMergedDState σ σ' σ'' merged ->
      
      (* * Conclusion * *)
      vcomb D__s Δ σ (cs_par cstmt cstmt') merged.

#[export] Hint Constructors vcomb : hvhdl.
