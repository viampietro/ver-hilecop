(** * Falling Edge Lemma *)

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

(** ** Falling Edge Lemma *)

Lemma falling_edge_full :
  forall sitpn decpr id__ent id__arch mm d γ E__c E__p Δ σ__e s σ τ s' σ__f σ',

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post rising edge). *)
    @FullSimStateAfterRE sitpn γ E__c τ s σ ->

    (* From s to s' after ↓. *)
    SitpnStateTransition E__c τ s s' fe ->

    (* From σ to σ' after ↓. *)
    vfalling hdstore Δ σ (behavior d) σ__f ->
    stabilize hdstore Δ σ__f (behavior d) σ' ->

    (* States s' and σ' are similar (post falling edge). *)
    FullSimStateAfterFE sitpn γ s' σ'.
Admitted.

#[export] Hint Resolve falling_edge_full : hilecop.

Lemma falling_edge :
  forall sitpn decpr id__ent id__arch mm d γ E__c E__p Δ σ__e s σ τ s' σ__f σ',

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post rising edge). *)
    @FullSimStateAfterRE sitpn γ E__c τ s σ ->

    (* From s to s' after ↓. *)
    SitpnStateTransition E__c τ s s' fe ->

    (* From σ to σ' after ↓. *)
    vfalling hdstore Δ σ (behavior d) σ__f ->
    stabilize hdstore Δ σ__f (behavior d) σ' ->

    (* States s' and σ' are similar (post falling edge). *)
    SimStateAfterFE sitpn γ s' σ'.
Admitted.

#[export] Hint Resolve falling_edge : hilecop.
