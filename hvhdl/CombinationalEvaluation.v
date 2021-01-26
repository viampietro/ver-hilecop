(** * Evaluation of combinational concurrent statements. *)

(** Defines the relation that evaluates combinational concurrent
    statements; used in the stabilization phases. *)

Require Import common.Coqlib.
Require Import common.NatMap.
Require Import common.NatSet.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.SSEvaluation.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.HVhdlTypes.

(** Defines the relation that evaluates combinational
    concurrent statements.
 *)

Inductive vcomb (D__s : IdMap design) (Δ : ElDesign) (σ : DState) : cs -> DState -> Prop :=

(** Evaluates a stable process (no event are related to signals of the
    process sensitivity list). *)

| VCombStablePs :
    forall pid sl vars stmt,
      
      (* * Side conditions * *)
      NatSet.Equal (NatSet.inter sl (events σ)) NatSet.empty -> (* sl ∩ E = ∅ *)
      
      (* * Conclusion * *)
      vcomb D__s Δ σ (cs_ps pid sl vars stmt) (NoEvDState σ)
            
(** Evaluates an unstable process (signals of the process sensitivity
    list generated events). Then, the process body is evaluated. *)

| VCombUnstablePs :
    forall pid sl vars stmt Λ σ' Λ',

      (* * Premises * *)
      vseq Δ (NoEvDState σ) Λ stab stmt σ' Λ' ->
      
      (* * Side conditions * *)
      NatSet.Equal (NatSet.inter sl (events σ)) NatSet.empty -> (* sl ∩ E ≠ ∅ *)
      NatMap.MapsTo pid (Process Λ) Δ ->         (* pid ∈ Δ and Δ(pid) = Λ *)
      
      (* * Conclusion * *)
      vcomb D__s Δ σ (cs_ps pid sl vars stmt) σ'

(** Evaluates a component instance. The new state of the component
    instance, resulting of the interpretation of its behavior,
    registered some events. *)

| VCombCompEvents :
    forall {compid entid gmap ipmap opmap d
                   Δ__c σ__c σ__c' σ__c'' σ'},
      
      (* * Premises * *)
      mapip Δ Δ__c σ σ__c ipmap σ__c' ->
      vcomb D__s Δ__c σ__c' (behavior d) σ__c'' ->
      mapop Δ Δ__c σ σ__c'' opmap σ' ->
      
      (* * Side conditions * *)

      (* [entid] is associated to design [d] in design store [D__s] *)
      NatMap.MapsTo entid d D__s ->
      
      (* [compid ∈ Comps(Δ) and Δ(compid) = Δ__c] *)
      NatMap.MapsTo compid (Component Δ__c) Δ ->
      
      (* [compid ∈ σ and σ(compid) = σ__c] *)
      NatMap.MapsTo compid σ__c (compstore σ) ->

      (* [Events registered in σ__c''.] *)
      (events σ__c'') <> NatSet.empty ->
      
      (* * Conclusion * *)
      
      (* Add [compid] to the events set of [σ'] because compid
         registered some events in its internal state.
         
         Associates [compid] to its new state [σ__c''] in the component
         store of σ'. *)
      vcomb D__s Δ σ (cs_comp compid entid gmap ipmap opmap) (cstore_add compid σ__c'' (events_add compid σ'))

(** Evaluates a component instance. The new state of the component
    instance, resulting of the interpretation of its behavior,
    registered no events. *)

| VCombCompNoEvent :
    forall {compid entid gmap ipmap opmap d
                   Δ__c σ__c σ__c' σ__c'' σ'},
      
      (* * Premises * *)
      mapip Δ Δ__c σ σ__c ipmap σ__c' ->
      vcomb D__s Δ__c σ__c' (behavior d) σ__c'' ->
      mapop Δ Δ__c σ σ__c'' opmap σ' ->
      
      (* * Side conditions * *)
      
      (* [entid] is associated to design [d] in design store [D__s] *)
      NatMap.MapsTo entid d D__s ->
      
      (* [compid ∈ Comps(Δ)] and [Δ(compid) = Δ__c] *)
      NatMap.MapsTo compid (Component Δ__c) Δ ->
      
      (* [compid ∈ σ] and [σ(compid) = σ__c] *)
      NatMap.MapsTo compid σ__c (compstore σ) ->

      (* No event registered in [σ__c'']. *)
      (events σ__c'') = NatSet.empty ->
      
      (* * Conclusion * *)
      vcomb D__s Δ σ (cs_comp compid entid gmap ipmap opmap) σ'

(** Evaluates the null concurrent statement. *)

| VCombNull : vcomb D__s Δ σ cs_null σ 
            
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

