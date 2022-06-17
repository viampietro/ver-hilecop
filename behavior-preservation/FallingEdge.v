(** * Falling edge lemma *)

Require Import common.NatMap.

Require Import sitpn.SitpnTypes.
Require Import sitpn.SitpnSemantics.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Stabilization.
Require Import hvhdl.Environment.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.CSEvaluation.
Require Import hvhdl.HVhdlTypes.

Require Import transformation.GenerateHVhdl.

Require Import soundness.SemanticPreservationDefs.

(** ** Falling edge lemmas *)

Lemma falling_edge_full :
  forall sitpn b d γ E__c E__p Δ σ__e s σ τ s' σ__f σ',

    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post rising edge). *)
    @FullSimStateAfterRE sitpn γ E__c τ s σ ->

    (* From s to s' after ↓. *)
    SitpnStateTransition E__c τ s s' fe ->

    (* From σ to σ' after ↓. *)
    VConc hdstore Δ σ falling (beh d) σ__f ->
    Stabilize hdstore Δ σ__f (beh d) σ' ->

    (* States s' and σ' are similar (post falling edge). *)
    FullSimStateAfterFE sitpn γ s' σ'.
Admitted.

#[export] Hint Resolve falling_edge_full : hilecop.

Lemma falling_edge :
  forall sitpn b d γ E__c E__p Δ σ__e s σ τ s' σ__f σ',

    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post rising edge). *)
    @FullSimStateAfterRE sitpn γ E__c τ s σ ->

    (* From s to s' after ↓. *)
    SitpnStateTransition E__c τ s s' fe ->

    (* From σ to σ' after ↓. *)
    VConc hdstore Δ σ falling (beh d) σ__f ->
    Stabilize hdstore Δ σ__f (beh d) σ' ->

    (* States s' and σ' are similar (post falling edge). *)
    SimStateAfterFE sitpn γ s' σ'.
Proof. intros; eapply falling_edge_full; eauto with hilecop. Qed.

#[export] Hint Resolve falling_edge : hilecop.

Lemma falling_edge_lock_step_full :
  forall sitpn b d γ E__c E__p Δ σ__e s σ τ s',

    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are fully similar (post rising edge). *)
    @FullSimStateAfterRE sitpn γ E__c τ s σ ->

    (* From s to s' after ↓. *)
    SitpnStateTransition E__c τ s s' fe ->

    exists σ__f σ',
      (* From σ to σ' after ↓. *)
      VConc hdstore Δ σ falling (beh d) σ__f 
      /\ Stabilize hdstore Δ σ__f (beh d) σ' 

      (* States s' and σ' are fully similar (post falling edge). *)
      /\ FullSimStateAfterFE sitpn γ s' σ'.
Admitted.

#[export] Hint Resolve falling_edge_lock_step_full : hilecop.

Lemma falling_edge_lock_step :
  forall sitpn b d γ E__c E__p Δ σ__e s σ τ s',

    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are fully similar (post rising edge). *)
    @FullSimStateAfterRE sitpn γ E__c τ s σ ->

    (* From s to s' after ↓. *)
    SitpnStateTransition E__c τ s s' fe ->

    exists σ__f σ',
      (* From σ to σ' after ↓. *)
      VConc hdstore Δ σ falling (beh d) σ__f 
      /\ Stabilize hdstore Δ σ__f (beh d) σ' 

      (* States s' and σ' are similar (post falling edge). *)
      /\ SimStateAfterFE sitpn γ s' σ'.
Proof.
  intros. 
  edestruct falling_edge_lock_step_full as (σ__f, (σ', (HVConc, (Hstab, Hfsim)))); eauto.
  exists σ__f, σ'; eauto with hilecop.
Qed.
  
#[export] Hint Resolve falling_edge_lock_step : hilecop.
