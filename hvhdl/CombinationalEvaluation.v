(** * Evaluation of combinational concurrent statements. *)

(** Defines the relation that evaluates combinational concurrent
    statements; used in the stabilization phases. *)

Require Import AbstractSyntax.
Require Import Environment.
Require Import SSEvaluation.
Require Import PortMapEvaluation.

(** Defines the relation that evaluates combinational
    concurrent statements.
 *)

Inductive vcomb (denv : DEnv) (dstate : DState) : cs -> DState -> Prop :=

(** Evaluates a stable process (no event are related to signals of the
    process sensitivity list). *)

| VCombStablePs :
    forall {pid sl vars stmt},
      
      (* * Side conditions * *)
      Equal (inter sl (events dstate)) NatSet.empty -> (* sl ∩ E = ∅ *)
      
      (* * Conclusion * *)
      vcomb denv dstate (cs_ps pid sl vars stmt) (NoEvDState dstate)
            
(** Evaluates an unstable process (signals of the process sensitivity
    list generated events). Then, the process body is evaluated. *)

| VCombUnstablePs :
    forall {pid sl vars stmt lenv dstate' lenv'},

      (* * Premises * *)
      vseq denv (NoEvDState dstate) lenv stmt dstate' lenv' ->
      
      (* * Side conditions * *)
      Equal (inter sl (events dstate)) NatSet.empty -> (* sl ∩ E ≠ ∅ *)
      NatMap.MapsTo pid (Process lenv) denv ->         (* pid ∈ Δ and Δ(pid) = Λ *)
      
      (* * Conclusion * *)
      vcomb denv dstate (cs_ps pid sl vars stmt) dstate'

(** Evaluates a component instance. The new state of the component
    instance, resulting of the interpretation of its behavior,
    registered some events. Therefore, we need to add the component
    identifier to the events field in the state of the
    embedding design. *)

| VCombCompEvents :
    forall {compid entid gmap ipmap opmap cstmt
                   cenv cstate cstate' cstate'' dstate'},
      
      (* * Premises * *)
      mapip denv cenv dstate cstate ipmap cstate' ->
      vcomb cenv cstate' cstmt cstate'' ->
      mapop denv cenv dstate cstate'' opmap dstate' ->
      
      (* * Side conditions * *)

      (* compid ∈ Comps(Δ) and Δ(compid) = (cenv, cstmt) *)
      NatMap.MapsTo compid (Component cenv cstmt) denv ->
      
      (* compid ∈ σ and σ(compid) = cstate *)
      NatMap.MapsTo compid cstate (compstore dstate) ->

      (* Events registered in cstate''. *)
      Equal (events cstate'') NatSet.empty ->
      
      (* * Conclusion * *)
      (* Add compid to the events field of dstate' because compid
         registered some events in its internal state. *)
      vcomb denv dstate (cs_comp compid entid gmap ipmap opmap) (events_add compid dstate')

(** Evaluates a component instance. The new state of the component
    instance, resulting of the interpretation of its behavior,
    registered no events. *)

| VCombCompNoEvent :
    forall {compid entid gmap ipmap opmap cstmt
                   cenv cstate cstate' cstate'' dstate'},
      
      (* * Premises * *)
      mapip denv cenv dstate cstate ipmap cstate' ->
      vcomb cenv cstate' cstmt cstate'' ->
      mapop denv cenv dstate cstate'' opmap dstate' ->
      
      (* * Side conditions * *)

      (* compid ∈ Comps(Δ) and Δ(compid) = (cenv, cstmt) *)
      NatMap.MapsTo compid (Component cenv cstmt) denv ->
      
      (* compid ∈ σ and σ(compid) = cstate *)
      NatMap.MapsTo compid cstate (compstore dstate) ->

      (* No event registered in cstate''. *)
      Equal (events cstate'') NatSet.empty ->
      
      (* * Conclusion * *)
      vcomb denv dstate (cs_comp compid entid gmap ipmap opmap) dstate'

(** Evaluates the parallel execution of two combinational concurrent
    statements.  *)
            
| VCombPar :
    forall {cstmt cstmt' dstate' dstate'' merged},

      (* * Premises * *)
      vcomb denv dstate cstmt dstate' ->
      vcomb denv dstate cstmt' dstate'' ->

      (* * Side conditions * *)
      
      (* E ∩ E' = ∅ ⇒ enforces the "no multiply-driven signals" condition. *)
      Equal (inter (events dstate') (events dstate'')) NatSet.empty ->

      (* States that merged is the result of the merging 
         of states dstate, dstate' and dstate''. *)
      IsMergedDState dstate dstate' dstate'' merged ->
      
      (* * Conclusion * *)
      vcomb denv dstate (cs_par cstmt cstmt') merged.
