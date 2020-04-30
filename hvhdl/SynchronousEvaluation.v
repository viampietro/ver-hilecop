(** * Evaluation of synchronous concurrent statements. *)

(** Defines two relations that evaluate synchronous concurrent
    statements: the evaluation relation on the falling edge event of
    the clock signal, and the evaluation relation on the rising edge
    of the clock signal.

 *)

Require Import AbstractSyntax.
Require Import Environment.
Require Import SSEvaluation.
Require Import PortMapEvaluation.
Require Import GlobalTypes.
Require Import SSEvaluation.
Require Import Petri.
Require Import NatSet.

(** Defines the relation that evaluates concurrent statement in
    reaction to the rising edge event of the clock signal. *)

Inductive vrising (denv : DEnv) (dstate : DState) : cs -> DState -> Prop :=

(** Evaluates a process statement that does not hold the reserved
    identifier [clk] (referring to the clock signal identifier) in its
    sensitivity list.  *)
  
| VRisingPsNoClk :
    forall {pid sl vars stmt},
      
      (* * Side conditions * *)
      ~NatSet.In clk sl ->
      
      (* * Conclusion * *)
      vrising denv dstate (cs_ps pid sl vars stmt) dstate

(** Evaluates a process statement that is sensitive to the clock
    signal.
    
    Then, the process body is evaluated leveraging the [vseqre]
    relation.
 *)
  
| VRisingPsClk :
    forall {pid sl vars stmt lenv dstate' lenv'},

      (* * Premises * *)
      vseqre denv dstate lenv stmt dstate' lenv' ->
      
      (* * Side conditions * *)
      NatSet.In clk sl ->
      NatMap.MapsTo pid (Process lenv) denv ->
      
      (* * Conclusion * *)
      vrising denv dstate (cs_ps pid sl vars stmt) dstate'

(** Evaluates a component instance; the new state of the component
    instance, resulting of the interpretation of its behavior,
    registered some events. Therefore, we need to add the component
    identifier to the events field in the state of the
    embedding design. *)

| VRisingCompEvents :
    forall {compid entid gmap ipmap opmap cstmt
                   cenv cstate cstate' cstate'' dstate'},
      
      (* * Premises * *)
      mapip denv cenv dstate cstate ipmap cstate' ->
      vrising cenv cstate' cstmt cstate'' ->
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
      vrising denv dstate (cs_comp compid entid gmap ipmap opmap) (events_add compid dstate')

(** Evaluates a component instance; the new state of the component
    instance, resulting of the interpretation of its behavior,
    registered no events. *)

| VRisingCompNoEvent :
    forall {compid entid gmap ipmap opmap cstmt
                   cenv cstate cstate' cstate'' dstate'},
      
      (* * Premises * *)
      mapip denv cenv dstate cstate ipmap cstate' ->
      vrising cenv cstate' cstmt cstate'' ->
      mapop denv cenv dstate cstate'' opmap dstate' ->
      
      (* * Side conditions * *)

      (* compid ∈ Comps(Δ) and Δ(compid) = (cenv, cstmt) *)
      NatMap.MapsTo compid (Component cenv cstmt) denv ->
      
      (* compid ∈ σ and σ(compid) = cstate *)
      NatMap.MapsTo compid cstate (compstore dstate) ->

      (* No event registered in cstate''. *)
      events cstate'' = NatSet.empty ->
      
      (* * Conclusion * *)
      vrising denv dstate (cs_comp compid entid gmap ipmap opmap) dstate'

(** Evaluates the parallel execution of two synchronous concurrent
    statements.  *)
            
| VRisingPar :
    forall {cstmt cstmt' dstate' dstate'' merged},

      (* * Premises * *)
      vrising denv dstate cstmt dstate' ->
      vrising denv dstate cstmt' dstate'' ->

      (* * Side conditions * *)
      
      (* E ∩ E' = ∅ ⇒ enforces the "no multiply-driven signals" condition. *)
      NatSet.inter (events dstate') (events dstate'') = NatSet.empty ->

      (* States that merged is the result of the merging 
         of states dstate, dstate' and dstate''. *)
      IsMergedDState dstate dstate' dstate'' merged ->
      
      (* * Conclusion * *)
      vrising denv dstate (cstmt // cstmt') merged.

(** Defines the relation that evaluates concurrent statement in
    reaction to the falling edge event of the clock signal. *)

Inductive vfalling (denv : DEnv) (dstate : DState) : cs -> DState -> Prop :=

(** Evaluates a process statement that does not hold the reserved
    identifier [clk] (referring to the clock signal identifier) in its
    sensitivity list.  *)
  
| VFallingPsNoClk :
    forall {pid sl vars stmt},
      
      (* * Side conditions * *)
      ~NatSet.In clk sl ->
      
      (* * Conclusion * *)
      vfalling denv dstate (cs_ps pid sl vars stmt) dstate

(** Evaluates a process statement that is sensitive to the clock
    signal.
    
    Then, the process body is evaluated leveraging the [vseqre]
    relation.
 *)
  
| VFallingPsClk :
    forall {pid sl vars stmt lenv dstate' lenv'},

      (* * Premises * *)
      vseqre denv dstate lenv stmt dstate' lenv' ->
      
      (* * Side conditions * *)
      NatSet.In clk sl ->
      NatMap.MapsTo pid (Process lenv) denv ->
      
      (* * Conclusion * *)
      vfalling denv dstate (cs_ps pid sl vars stmt) dstate'

(** Evaluates a component instance; the new state of the component
    instance, resulting of the interpretation of its behavior,
    registered some events. Therefore, we need to add the component
    identifier to the events field in the state of the
    embedding design. *)

| VFallingCompEvents :
    forall {compid entid gmap ipmap opmap cstmt
                   cenv cstate cstate' cstate'' dstate'},
      
      (* * Premises * *)
      mapip denv cenv dstate cstate ipmap cstate' ->
      vfalling cenv cstate' cstmt cstate'' ->
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
      vfalling denv dstate (cs_comp compid entid gmap ipmap opmap) (events_add compid dstate')

(** Evaluates a component instance; the new state of the component
    instance, resulting of the interpretation of its behavior,
    registered no events. *)

| VFallingCompNoEvent :
    forall {compid entid gmap ipmap opmap cstmt
                   cenv cstate cstate' cstate'' dstate'},
      
      (* * Premises * *)
      mapip denv cenv dstate cstate ipmap cstate' ->
      vfalling cenv cstate' cstmt cstate'' ->
      mapop denv cenv dstate cstate'' opmap dstate' ->
      
      (* * Side conditions * *)

      (* compid ∈ Comps(Δ) and Δ(compid) = (cenv, cstmt) *)
      NatMap.MapsTo compid (Component cenv cstmt) denv ->
      
      (* compid ∈ σ and σ(compid) = cstate *)
      NatMap.MapsTo compid cstate (compstore dstate) ->

      (* No event registered in cstate''. *)
      events cstate'' = NatSet.empty ->
      
      (* * Conclusion * *)
      vfalling denv dstate (cs_comp compid entid gmap ipmap opmap) dstate'

(** Evaluates the parallel execution of two synchronous concurrent
    statements.  *)
            
| VFallingPar :
    forall {cstmt cstmt' dstate' dstate'' merged},

      (* * Premises * *)
      vfalling denv dstate cstmt dstate' ->
      vfalling denv dstate cstmt' dstate'' ->

      (* * Side conditions * *)
      
      (* E ∩ E' = ∅ ⇒ enforces the "no multiply-driven signals" condition. *)
      NatSet.inter (events dstate') (events dstate'') = NatSet.empty ->

      (* States that merged is the result of the merging 
         of states dstate, dstate' and dstate''. *)
      IsMergedDState dstate dstate' dstate'' merged ->
      
      (* * Conclusion * *)
      vfalling denv dstate (cstmt // cstmt') merged.
