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
      NatSet.inter sl (events dstate) = NatSet.empty -> (* sl ∩ E = ∅ *)
      
      (* * Conclusion * *)
      vcomb denv dstate (cs_ps pid sl vars stmt) (NoEvDState dstate)
            
(** Evaluates an unstable process (signals of the process sensitivity
    list generated events). Then, the process body is evaluated. *)

| VCombUnstablePs :
    forall {pid sl vars stmt lenv dstate' lenv'},

      (* * Premises * *)
      vseq denv (NoEvDState dstate) lenv stmt dstate' lenv' ->
      
      (* * Side conditions * *)
      NatSet.inter sl (events dstate) <> NatSet.empty -> (* sl ∩ E ≠ ∅ *)
      NatMap.MapsTo pid (Process lenv) denv ->                  (* pid ∈ Δ and Δ(pid) = Λ *)
      
      (* * Conclusion * *)
      vcomb denv dstate (cs_ps pid sl vars stmt) dstate'

(** Evaluates a stable component instance (no events and still no
    events after in port map evaluation). *)

| VCombStableComp :
    forall {compid entid gmap ipmap opmap cstmt cenv cstate cstate'},
      
      (* * Premises * *)
      mapip denv cenv dstate cstate ipmap cstate' ->

      (* * Side conditions * *)

      (* compid ∈ Comps(Δ) and Δ(compid) = (cenv, cstmt) *)
      NatMap.MapsTo compid (Component cenv cstmt) denv ->
      
      (* compid ∈ σ and σ(compid) = cstate *)
      NatMap.MapsTo compid cstate (compstore dstate) ->

      (* No events after evaluation of ipmap. *)
      events cstate' = NatSet.empty ->
      
      (* * Conclusion * *)
      vcomb denv dstate (cs_comp compid entid gmap ipmap opmap) (NoEvDState dstate)

(** Evaluates an unstable component instance, i.e there are some
    events in the component instance state. Then, the internal
    behavior of the component instance is evaluated. *)

| VCombUnstableComp :
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

      (* No events after evaluation of ipmap. *)
      events cstate' <> NatSet.empty ->
      
      (* * Conclusion * *)
      vcomb denv dstate (cs_comp compid entid gmap ipmap opmap) dstate'

(** Evaluates the parallel execution of two combinational concurrent
    statements.  *)
            
| VCombPar :
    forall {cstmt cstmt'},

(* * Conclusion * *)
      vcomb denv dstate (cstmt // cstmt') 
.
