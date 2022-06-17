(** * Rising Edge Lemma *)

Require Import common.NatMap.

Require Import sitpn.SitpnTypes.
Require Import sitpn.SitpnSemantics.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Stabilization.
Require Import hvhdl.CSEvaluation.
Require Import hvhdl.Environment.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.HVhdlTypes.

Require Import transformation.GenerateHVhdl.

Require Import soundness.SemanticPreservationDefs.

(** ** Rising edge lemmas *)

Lemma rising_edge_full :
  forall sitpn b d γ E__c E__p Δ σ__e s σ τ s' σ__r σ',

    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post falling edge). *)
    FullSimStateAfterFE sitpn γ s σ ->

    (* From s to s' after ↑. *)
    SitpnStateTransition E__c τ s s' re ->

    (* From σ to σ' after ↑. *)
    VConc hdstore Δ (inj σ (E__p τ)) rising (beh d) σ__r ->
    Stabilize hdstore Δ σ__r (beh d) σ' ->

    (* States s' and σ' are similar (full post rising edge similarity). *)
    FullSimStateAfterRE sitpn γ E__c τ s' σ'.
Admitted.

#[export] Hint Resolve rising_edge_full : hilecop.

Lemma rising_edge :
  forall sitpn b d γ E__c E__p Δ σ__e s σ τ s' σ__r σ',

    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post falling edge). *)
    FullSimStateAfterFE sitpn γ s σ ->

    (* From s to s' after ↑. *)
    SitpnStateTransition E__c τ s s' re ->

    (* From σ to σ' after ↑. *)
    VConc hdstore Δ (inj σ (E__p τ)) rising (beh d) σ__r ->
    Stabilize hdstore Δ σ__r (beh d) σ' ->

    (* States s' and σ' are similar (post rising edge similarity). *)
    SimStateAfterRE sitpn γ s' σ'.
Proof. intros; eapply rising_edge_full; eauto with hilecop. Qed.

#[export] Hint Resolve rising_edge : hilecop.

Lemma rising_edge_lock_step_full :
  forall sitpn b d γ E__c E__p Δ σ__e s σ τ s',

    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post falling edge). *)
    FullSimStateAfterFE sitpn γ s σ ->

    (* From s to s' after ↑. *)
    SitpnStateTransition E__c τ s s' re ->

    exists  σ__r σ',
      (* From σ to σ' after ↑. *)
      VConc hdstore Δ (inj σ (E__p τ)) rising (beh d) σ__r 
      /\ Stabilize hdstore Δ σ__r (beh d) σ' 

      (* States s' and σ' are similar (full post rising edge similarity). *)
      /\ FullSimStateAfterRE sitpn γ E__c τ s' σ'.
Admitted.

#[export] Hint Resolve rising_edge_lock_step_full : hilecop.

Lemma rising_edge_lock_step :
  forall sitpn b d γ E__c E__p Δ σ__e s σ τ s',

    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post falling edge). *)
    FullSimStateAfterFE sitpn γ s σ ->

    (* From s to s' after ↑. *)
    SitpnStateTransition E__c τ s s' re ->

    exists  σ__r σ',
      (* From σ to σ' after ↑. *)
      VConc hdstore Δ (inj σ (E__p τ)) rising (beh d) σ__r 
      /\ Stabilize hdstore Δ σ__r (beh d) σ' 

      (* States s' and σ' are similar (full post rising edge similarity). *)
      /\ SimStateAfterRE sitpn γ s' σ'.
Proof.
  intros;
    edestruct rising_edge_lock_step_full as (σ__r, (σ', (HVconc, (Hstab, Hsim)))); eauto.
  do 2 eexists; eauto with hilecop.
Qed.

#[export] Hint Resolve rising_edge_lock_step : hilecop.

