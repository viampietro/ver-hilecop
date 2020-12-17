(** * Falling Edge Lemma *)

Require Import common.NatMap.

Require Import sitpn.dp.SitpnTypes.
Require Import sitpn.dp.SitpnSemantics.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Stabilize.
Require Import hvhdl.SynchronousEvaluation.
Require Import hvhdl.Environment.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.HilecopDesignStore.

Require Import sitpn2hvhdl.GenerateHVhdl.

Require Import soundness.SoundnessDefs.

(** ** Falling Edge Lemma *)

Lemma falling_edge :
  forall sitpn decpr id__ent id__arch mm d γ E__c E__p Δ σ__e s σ τ s' σ__injf σ__f σ' θ,

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post rising edge). *)
    SimStateAfterRE sitpn γ s σ ->

    (* From s to s' after ↓. *)
    SitpnStateTransition E__c τ s s' fe ->

    (* From σ to σ' after ↓. *)
    IsInjectedDState σ (E__p τ fe) σ__injf ->
    vfalling Δ σ__injf (behavior d) σ__f ->
    stabilize Δ σ__f (behavior d) θ σ' ->

    (* States s' and σ' are similar (post falling edge). *)
    SimStateAfterFE sitpn γ s' σ'.
Admitted.

Hint Resolve falling_edge : core.
