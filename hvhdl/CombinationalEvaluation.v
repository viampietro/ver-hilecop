(** * Evaluation of combinational concurrent statements. *)

(** Defines the relation that evaluates combinational concurrent
    statements; used in the stabilization phases. *)

Require Import Coqlib.
Require Import NatMap.
Require Import NatSet.
Require Import AbstractSyntax.
Require Import Environment.
Require Import SSEvaluation.
Require Import PortMapEvaluation.

(** Defines the relation that evaluates combinational
    concurrent statements.
 *)

Inductive vcomb (ed : ElDesign) (dstate : DState) : cs -> DState -> Prop :=

(** Evaluates a stable process (no event are related to signals of the
    process sensitivity list). *)

| VCombStablePs :
    forall {pid sl vars stmt},
      
      (* * Side conditions * *)
      NatSet.Equal (NatSet.inter sl (events dstate)) NatSet.empty -> (* sl ∩ E = ∅ *)
      
      (* * Conclusion * *)
      vcomb ed dstate (cs_ps pid sl vars stmt) (NoEvDState dstate)
            
(** Evaluates an unstable process (signals of the process sensitivity
    list generated events). Then, the process body is evaluated. *)

| VCombUnstablePs :
    forall {pid sl vars stmt lenv dstate' lenv'},

      (* * Premises * *)
      vseq ed (NoEvDState dstate) lenv stmt dstate' lenv' ->
      
      (* * Side conditions * *)
      NatSet.Equal (NatSet.inter sl (events dstate)) NatSet.empty -> (* sl ∩ E ≠ ∅ *)
      NatMap.MapsTo pid (Process lenv) ed ->         (* pid ∈ Δ and Δ(pid) = Λ *)
      
      (* * Conclusion * *)
      vcomb ed dstate (cs_ps pid sl vars stmt) dstate'

(** Evaluates a component instance. The new state of the component
    instance, resulting of the interpretation of its behavior,
    registered some events. Therefore, we need to add the component
    identifier to the events field in the state of the
    embedding design. *)

| VCombCompEvents :
    forall {compid entid gmap ipmap opmap cstmt
                   cenv cstate cstate' cstate'' dstate'},
      
      (* * Premises * *)
      mapip ed cenv dstate cstate ipmap cstate' ->
      vcomb cenv cstate' cstmt cstate'' ->
      mapop ed cenv dstate cstate'' opmap dstate' ->
      
      (* * Side conditions * *)

      (* compid ∈ Comps(Δ) and Δ(compid) = (cenv, cstmt) *)
      NatMap.MapsTo compid (Component cenv cstmt) ed ->
      
      (* compid ∈ σ and σ(compid) = cstate *)
      NatMap.MapsTo compid cstate (compstore dstate) ->

      (* Events registered in cstate''. *)
      NatSet.Equal (events cstate'') NatSet.empty ->
      
      (* * Conclusion * *)
      (* Add compid to the events field of dstate' because compid
         registered some events in its internal state. *)
      vcomb ed dstate (cs_comp compid entid gmap ipmap opmap) (events_add compid dstate')

(** Evaluates a component instance. The new state of the component
    instance, resulting of the interpretation of its behavior,
    registered no events. *)

| VCombCompNoEvent :
    forall {compid entid gmap ipmap opmap cstmt
                   cenv cstate cstate' cstate'' dstate'},
      
      (* * Premises * *)
      mapip ed cenv dstate cstate ipmap cstate' ->
      vcomb cenv cstate' cstmt cstate'' ->
      mapop ed cenv dstate cstate'' opmap dstate' ->
      
      (* * Side conditions * *)

      (* compid ∈ Comps(Δ) and Δ(compid) = (cenv, cstmt) *)
      NatMap.MapsTo compid (Component cenv cstmt) ed ->
      
      (* compid ∈ σ and σ(compid) = cstate *)
      NatMap.MapsTo compid cstate (compstore dstate) ->

      (* No event registered in cstate''. *)
      NatSet.Equal (events cstate'') NatSet.empty ->
      
      (* * Conclusion * *)
      vcomb ed dstate (cs_comp compid entid gmap ipmap opmap) dstate'

(** Evaluates the parallel execution of two combinational concurrent
    statements.  *)
            
| VCombPar :
    forall {cstmt cstmt' dstate' dstate'' merged},

      (* * Premises * *)
      vcomb ed dstate cstmt dstate' ->
      vcomb ed dstate cstmt' dstate'' ->

      (* * Side conditions * *)
      
      (* E ∩ E' = ∅ ⇒ enforces the "no multiply-driven signals" condition. *)
      NatSet.Equal (NatSet.inter (events dstate') (events dstate'')) NatSet.empty ->

      (* States that merged is the result of the merging 
         of states dstate, dstate' and dstate''. *)
      IsMergedDState dstate dstate' dstate'' merged ->
      
      (* * Conclusion * *)
      vcomb ed dstate (cs_par cstmt cstmt') merged.

(** ** Facts about [vcomb] *)

Lemma comb_maps_id :
  forall Δ σ behavior σ' id σ__id,
    vcomb Δ σ behavior σ' ->
    MapsTo id σ__id (compstore σ) ->
    exists σ'__id, MapsTo id σ'__id (compstore σ').
Proof.
  induction 1; intros Hmaps.

  (* CASE behavior is a quiescent process  *)
  - simpl; exists σ__id; assumption.

  (* CASE behavior is an eventful process, needs ind. on vseq. *)
  - admit.

  (* CASE behavior is an eventful component *)
  - admit.

  (* CASE behavior is a quiescent component *)
  - admit.

  (* CASE behavior is a sequence of concurrent statements. *)
    
  - unfold IsMergedDState in H2.
    apply proj2, proj1 in H2.
    unfold MapsTo.
    unfold EqualDom in H2.
    unfold common.NatMap.In, common.NatMap.Raw.PX.In in H2.
    rewrite <- (H2 id).
    exists σ__id. assumption.
    
Admitted.

(*  *)

Lemma comb_maps_id_rev :
  forall Δ σ behavior σ' id σ'__id,
    vcomb Δ σ behavior σ' ->
    MapsTo id σ'__id (compstore σ') ->
    exists σ__id, MapsTo id σ__id (compstore σ).
Proof.
Admitted.
