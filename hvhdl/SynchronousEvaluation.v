(** * Evaluation of synchronous concurrent statements. *)

(** Defines two relations that evaluate synchronous concurrent
    statements: the evaluation relation on the falling edge event of
    the clock signal, and the evaluation relation on the rising edge
    of the clock signal. *)

Require Import common.GlobalTypes.
Require Import common.NatSet.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.SSEvaluation.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.SSEvaluation.
Require Import hvhdl.Petri.
Require Import hvhdl.HVhdlTypes.

Include HVhdlCsNotations.

(** Defines the relation that evaluates concurrent statement in
    reaction to the rising edge event of the clock signal. *)

Inductive vrising (D__s : IdMap design) (Δ : ElDesign) (σ : DState) : cs -> DState -> Prop :=

(** Evaluates a process statement that does not hold the reserved
    identifier [clk] (referring to the clock signal identifier) in its
    sensitivity list.  *)
  
| VRisingPsNoClk :
    forall id__p sl vars stmt,
      
      (* * Side conditions * *)
      ~NatSet.In clk sl ->
      
      (* * Conclusion * *)
      vrising D__s Δ σ (cs_ps id__p sl vars stmt) σ

(** Evaluates a process statement that is sensitive to the clock
    signal.
    
    Then, the process body is evaluated leveraging the [vseq] relation
    with the [re] flag.  *)
  
| VRisingPsClk :
    forall id__p sl vars stmt Λ σ' Λ',

      (* * Premises * *)
      vseq Δ σ σ Λ re stmt σ' Λ' ->
      
      (* * Side conditions * *)
      NatSet.In clk sl ->
      NatMap.MapsTo id__p (Process Λ) Δ ->
      
      (* * Conclusion * *)
      vrising D__s Δ σ (cs_ps id__p sl vars stmt) σ'

(** Evaluates a component instance; the new state of the component
    instance, resulting of the interpretation of its behavior,
    registered some events. Therefore, we need to add the component
    identifier to the events field in the state of the
    embedding design. *)

| VRisingCompEvents :
    forall id__c id__e g i o d Δ__c σ__c σ__c' σ__c'' σ',
      
      (* * Premises * *)
      mapip Δ Δ__c σ σ__c i σ__c' ->
      vrising D__s Δ__c σ__c' (behavior d) σ__c'' ->
      mapop Δ Δ__c σ σ__c'' o σ' ->
      
      (* * Side conditions * *)

      (* [id__e] is associated to design [d] in design store [D__s] *)
      NatMap.MapsTo id__e d D__s ->
      
      (* [id__c ∈ Comps(Δ)] and [Δ(id__c) = Δ__c] *)
      NatMap.MapsTo id__c (Component Δ__c) Δ ->
      
      (* [id__c ∈ σ] and [σ(id__c) = σ__c] *)
      NatMap.MapsTo id__c σ__c (compstore σ) ->

      (* Events registered in [σ__c'']. *)
      events σ__c'' <> NatSet.empty ->
      
      (* * Conclusion * *)
      
      (* Add [id__c] to the events field of [σ'] because [id__c]
         registered some events in its internal state.

         Associates [id__c] to its new state [σ__c''] in the component
         store of [σ'].  *)
      vrising D__s Δ σ (cs_comp id__c id__e g i o) (cstore_add id__c σ__c'' (events_add id__c σ'))

(** Evaluates a component instance; the new state of the component
    instance, resulting of the interpretation of its behavior,
    registered no events. *)

| VRisingCompNoEvent :
    forall id__c id__e g i o d Δ__c σ__c σ__c' σ__c'' σ',
      
      (* * Premises * *)
      mapip Δ Δ__c σ σ__c i σ__c' ->
      vrising D__s Δ__c σ__c' (behavior d) σ__c'' ->
      mapop Δ Δ__c σ σ__c'' o σ' ->
      
      (* * Side conditions * *)

      (* [id__e] is associated to design [d] in design store [D__s] *)
      NatMap.MapsTo id__e d D__s ->
      
      (* [id__c ∈ Comps(Δ)] and [Δ(id__c) = Δ__c] *)
      NatMap.MapsTo id__c (Component Δ__c) Δ ->
      
      (* [id__c ∈ σ] and [σ(id__c) = σ__c] *)
      NatMap.MapsTo id__c σ__c (compstore σ) ->

      (* No event registered in [σ__c'']. *)
      events σ__c'' = NatSet.empty ->
      
      (* * Conclusion * *)
      vrising D__s Δ σ (cs_comp id__c id__e g i o) σ'

(** Evaluates the null statement. *)

| VRisingNull : vrising D__s Δ σ cs_null σ
              
(** Evaluates the parallel execution of two synchronous concurrent
    statements.  *)
            
| VRisingPar :
    forall cstmt cstmt' σ' σ'' merged,

      (* * Premises * *)
      vrising D__s Δ σ cstmt σ' ->
      vrising D__s Δ σ cstmt' σ'' ->

      (* * Side conditions * *)
      
      (* E ∩ E' = ∅ ⇒ enforces the "no multiply-driven signals" condition. *)
      NatSet.inter (events σ') (events σ'') = NatSet.empty ->

      (* States that merged is the result of the merging 
         of states σ, σ' and σ''. *)
      IsMergedDState σ σ' σ'' merged ->
      
      (* * Conclusion * *)
      vrising D__s Δ σ (cstmt // cstmt') merged.

(** Defines the relation that evaluates concurrent statement in
    reaction to the falling edge event of the clock signal. *)

Inductive vfalling (D__s : IdMap design) (Δ : ElDesign) (σ : DState) : cs -> DState -> Prop :=

(** Evaluates a process statement that does not hold the reserved
    identifier [clk] (referring to the clock signal identifier) in its
    sensitivity list.  *)
  
| VFallingPsNoClk :
    forall id__p sl vars stmt,
      
      (* * Side conditions * *)
      ~NatSet.In clk sl ->
      
      (* * Conclusion * *)
      vfalling D__s Δ σ (cs_ps id__p sl vars stmt) σ

(** Evaluates a process statement that is sensitive to the clock
    signal.
    
    Then, the process body is evaluated leveraging the [vseqre]
    relation.
 *)
  
| VFallingPsClk :
    forall id__p sl vars stmt Λ σ' Λ',

      (* * Premises * *)
      vseq Δ σ σ Λ fe stmt σ' Λ' ->
      
      (* * Side conditions * *)
      NatSet.In clk sl ->
      NatMap.MapsTo id__p (Process Λ) Δ ->
      
      (* * Conclusion * *)
      vfalling D__s Δ σ (cs_ps id__p sl vars stmt) σ'

(** Evaluates a component instance; the new state of the component
    instance, resulting of the interpretation of its behavior,
    registered some events. *)

| VFallingCompEvents :
    forall id__c id__e g i o d Δ__c σ__c σ__c' σ__c'' σ',
      
      (* * Premises * *)
      mapip Δ Δ__c σ σ__c i σ__c' ->
      vfalling D__s Δ__c σ__c' (behavior d) σ__c'' ->
      mapop Δ Δ__c σ σ__c'' o σ' ->
      
      (* * Side conditions * *)
      
      (* [id__e] is associated to design [d] in design store [D__s] *)
      NatMap.MapsTo id__e d D__s ->
      
      (* [id__c ∈ Comps(Δ) and Δ(id__c) = Δ__c] *)
      NatMap.MapsTo id__c (Component Δ__c) Δ ->
      
      (* [id__c ∈ σ and σ(id__c) = σ__c] *)
      NatMap.MapsTo id__c σ__c (compstore σ) ->

      (* Events registered in [σ__c'']. *)
      events σ__c'' <> NatSet.empty ->
      
      (* * Conclusion * *)
      (* Add id__c to the events field of σ' because id__c
         registered some events in its internal state.

         Associates [id__c] to its new state [σ__c''] in the component
         store of [σ'].  *)
      
      vfalling D__s Δ σ (cs_comp id__c id__e g i o) (cstore_add id__c σ__c'' (events_add id__c σ'))

(** Evaluates a component instance; the new state of the component
    instance, resulting of the interpretation of its behavior,
    registered no events. *)

| VFallingCompNoEvent :
    forall id__c id__e g i o d Δ__c σ__c σ__c' σ__c'' σ',
      
      (* * Premises * *)
      mapip Δ Δ__c σ σ__c i σ__c' ->
      vfalling D__s Δ__c σ__c' (behavior d) σ__c'' ->
      mapop Δ Δ__c σ σ__c'' o σ' ->
      
      (* * Side conditions * *)
      
      (* [id__e] is associated to design [d] in design store [D__s] *)
      NatMap.MapsTo id__e d D__s ->
      
      (* [id__c ∈ Comps(Δ)] and [Δ(id__c) = Δ__c] *)
      NatMap.MapsTo id__c (Component Δ__c) Δ ->
      
      (* [id__c ∈ σ] and [σ(id__c) = σ__c] *)
      NatMap.MapsTo id__c σ__c (compstore σ) ->

      (* No event registered in [σ__c'']. *)
      events σ__c'' = NatSet.empty ->
      
      (* * Conclusion * *)
      vfalling D__s Δ σ (cs_comp id__c id__e g i o) σ'

(** Evaluates the null statement. *)

| VFallingNull : vfalling D__s Δ σ cs_null σ
               
(** Evaluates the parallel execution of two synchronous concurrent
    statements.  *)
            
| VFallingPar :
    forall {cstmt cstmt' σ' σ'' merged},

      (* * Premises * *)
      vfalling D__s Δ σ cstmt σ' ->
      vfalling D__s Δ σ cstmt' σ'' ->

      (* * Side conditions * *)
      
      (* E ∩ E' = ∅ ⇒ enforces the "no multiply-driven signals" condition. *)
      NatSet.inter (events σ') (events σ'') = NatSet.empty ->

      (* States that merged is the result of the merging 
         of states σ, σ' and σ''. *)
      IsMergedDState σ σ' σ'' merged ->
      
      (* * Conclusion * *)
      vfalling D__s Δ σ (cstmt // cstmt') merged.
