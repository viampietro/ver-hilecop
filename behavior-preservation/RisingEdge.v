(** * Rising Edge Lemma *)

Require Import common.NatMap.

Require Import sitpn.SitpnTypes.
Require Import sitpn.SitpnSemantics.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Stabilize.
Require Import hvhdl.SynchronousEvaluation.
Require Import hvhdl.Environment.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.HilecopDesignStore.

Require Import transformation.GenerateHVhdl.

Require Import soundness.SemanticPreservationDefs.

(** ** Rising edge lemmas *)

Lemma rising_edge_full :
  forall sitpn id__ent id__arch mm d γ E__c E__p Δ σ__e s σ τ s' σ__i σ__r σ',

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post falling edge). *)
    FullSimStateAfterFE sitpn γ s σ ->

    (* From s to s' after ↑. *)
    SitpnStateTransition E__c τ s s' re ->

    (* From σ to σ' after ↑. *)
    IsInjectedDState σ (E__p τ) σ__i ->
    vrising hdstore Δ σ__i (behavior d) σ__r ->
    stabilize hdstore Δ σ__r (behavior d) σ' ->

    (* States s' and σ' are similar (full post rising edge similarity). *)
    FullSimStateAfterRE sitpn γ E__c τ s' σ'.
Admitted.

#[export] Hint Resolve rising_edge_full : hilecop.

Lemma rising_edge :
  forall sitpn id__ent id__arch mm d γ E__c E__p Δ σ__e s σ τ s' σ__i σ__r σ',

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post falling edge). *)
    FullSimStateAfterFE sitpn γ s σ ->

    (* From s to s' after ↑. *)
    SitpnStateTransition E__c τ s s' re ->

    (* From σ to σ' after ↑. *)
    IsInjectedDState σ (E__p τ) σ__i ->
    vrising hdstore Δ σ__i (behavior d) σ__r ->
    stabilize hdstore Δ σ__r (behavior d) σ' ->

    (* States s' and σ' are similar (post rising edge similarity). *)
    SimStateAfterRE sitpn γ s' σ'.
Admitted.

#[export] Hint Resolve rising_edge : hilecop.
