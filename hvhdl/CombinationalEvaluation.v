(** * Evaluation of combinational concurrent statements. *)

(** Defines the relation that evaluates combinational concurrent
    statements; used in the stabilization phases. *)

Require Import Coqlib.
Require Import NMap.
Require Import NSet.
Require Import AbstractSyntax.
Require Import Environment.
Require Import SSEvaluation.
Require Import PortMapEvaluation.

(** Defines the relation that evaluates combinational
    concurrent statements.
 *)

Inductive vcomb (Δ : ElDesign) (σ : DState) : cs -> DState -> Prop :=

(** Evaluates a stable process (no event are related to signals of the
    process sensitivity list). *)

| VCombStablePs :
    forall pid sl vars stmt,
      
      (* * Side conditions * *)
      NSet.Equal (NSet.inter sl (events σ)) NSet.empty -> (* sl ∩ E = ∅ *)
      
      (* * Conclusion * *)
      vcomb Δ σ (cs_ps pid sl vars stmt) (NoEvDState σ)
            
(** Evaluates an unstable process (signals of the process sensitivity
    list generated events). Then, the process body is evaluated. *)

| VCombUnstablePs :
    forall pid sl vars stmt Λ σ' Λ',

      (* * Premises * *)
      vseq Δ (NoEvDState σ) Λ stab stmt σ' Λ' ->
      
      (* * Side conditions * *)
      NSet.Equal (NSet.inter sl (events σ)) NSet.empty -> (* sl ∩ E ≠ ∅ *)
      NMap.MapsTo pid (Process Λ) Δ ->         (* pid ∈ Δ and Δ(pid) = Λ *)
      
      (* * Conclusion * *)
      vcomb Δ σ (cs_ps pid sl vars stmt) σ'

(** Evaluates a component instance. The new state of the component
    instance, resulting of the interpretation of its behavior,
    registered some events. Therefore, we need to add the component
    identifier to the events field in the state of the
    embedding design. *)

| VCombCompEvents :
    forall {compid entid gmap ipmap opmap cstmt
                   cenv cstate cstate' cstate'' σ'},
      
      (* * Premises * *)
      mapip Δ cenv σ cstate ipmap cstate' ->
      vcomb cenv cstate' cstmt cstate'' ->
      mapop Δ cenv σ cstate'' opmap σ' ->
      
      (* * Side conditions * *)

      (* compid ∈ Comps(Δ) and Δ(compid) = (cenv, cstmt) *)
      NMap.MapsTo compid (Component cenv cstmt) Δ ->
      
      (* compid ∈ σ and σ(compid) = cstate *)
      NMap.MapsTo compid cstate (compstore σ) ->

      (* Events registered in cstate''. *)
      NSet.Equal (events cstate'') NSet.empty ->
      
      (* * Conclusion * *)
      (* Add compid to the events field of σ' because compid
         registered some events in its internal state. *)
      vcomb Δ σ (cs_comp compid entid gmap ipmap opmap) (events_add compid σ')

(** Evaluates a component instance. The new state of the component
    instance, resulting of the interpretation of its behavior,
    registered no events. *)

| VCombCompNoEvent :
    forall {compid entid gmap ipmap opmap cstmt
                   cenv cstate cstate' cstate'' σ'},
      
      (* * Premises * *)
      mapip Δ cenv σ cstate ipmap cstate' ->
      vcomb cenv cstate' cstmt cstate'' ->
      mapop Δ cenv σ cstate'' opmap σ' ->
      
      (* * Side conditions * *)

      (* compid ∈ Comps(Δ) and Δ(compid) = (cenv, cstmt) *)
      NMap.MapsTo compid (Component cenv cstmt) Δ ->
      
      (* compid ∈ σ and σ(compid) = cstate *)
      NMap.MapsTo compid cstate (compstore σ) ->

      (* No event registered in cstate''. *)
      NSet.Equal (events cstate'') NSet.empty ->
      
      (* * Conclusion * *)
      vcomb Δ σ (cs_comp compid entid gmap ipmap opmap) σ'

(** Evaluates the null concurrent statement. *)

| VCombNull : vcomb Δ σ cs_null σ 
            
(** Evaluates the parallel execution of two combinational concurrent
    statements.  *)
            
| VCombPar :
    forall {cstmt cstmt' σ' σ'' merged},

      (* * Premises * *)
      vcomb Δ σ cstmt σ' ->
      vcomb Δ σ cstmt' σ'' ->

      (* * Side conditions * *)
      
      (* E ∩ E' = ∅ ⇒ enforces the "no multiply-driven signals" condition. *)
      NSet.Equal (NSet.inter (events σ') (events σ'')) NSet.empty ->

      (* States that merged is the result of the merging 
         of states σ, σ' and σ''. *)
      IsMergedDState σ σ' σ'' merged ->
      
      (* * Conclusion * *)
      vcomb Δ σ (cs_par cstmt cstmt') merged.

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

  (* CASE null statement. *)
  - exists σ__id; assumption.
    
  (* CASE behavior is a sequence of concurrent statements. *)
    
  - unfold IsMergedDState in H2.
    apply proj2, proj1 in H2.
    unfold MapsTo.
    unfold EqualDom in H2.
    unfold common.NMap.In, common.NMap.Raw.PX.In in H2.
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

(*  *)

Lemma comb_maps_sigid :
  forall Δ σ behavior σ' s v,
    vcomb Δ σ behavior σ' ->
    MapsTo s v (sigstore σ) ->
    exists v', MapsTo s v' (sigstore σ').
Proof.
Admitted.
