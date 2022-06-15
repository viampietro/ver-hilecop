(** * Similar states after first rising edge  *)

Require Import sitpn.SitpnLib.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.HVhdlHilecopLib.

Require Import transformation.Sitpn2HVhdl.

Require Import soundness.SemanticPreservationDefs.

Lemma first_rising_edge_full :
  forall sitpn b d γ E__c E__p Δ σ__e σ0 τ σ__r σ,

    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* [σ0] is the initial state of [d]. *)
    Init hdstore Δ σ__e (AbstractSyntax.beh d) σ0 ->

    (* From [σ0] to [σ] after [↑]. *)
    VConc hdstore Δ (inj σ0 (E__p τ)) rising (AbstractSyntax.beh d) σ__r ->
    Stabilize hdstore Δ σ__r (AbstractSyntax.beh d) σ ->
    
    (* States [s] and [σ] are similar. *)
    FullSimStateAfterRE sitpn γ E__c τ (s0 sitpn) σ.
Admitted.

(* Tries to apply the [first_rising_edge] lemma when the goal is of the form
   [SimStateAfterFE _ _ _ _] or [_ ⊢ _ ∼ _]. *)
#[export] Hint Resolve first_rising_edge_full : hilecop.
#[export] Hint Extern 1 ( _ ⊢ _ ∼ _ ) => eapply first_rising_edge_full; eauto : hilecop.

Lemma first_rising_edge :
  forall sitpn b d γ E__c E__p Δ σ__e σ0 τ σ__r σ,

    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* [σ0] is the initial state of [d]. *)
    Init hdstore Δ σ__e (AbstractSyntax.beh d) σ0 ->

    (* From [σ0] to [σ] after [↑]. *)
    VConc hdstore Δ (inj σ0 (E__p τ)) rising (AbstractSyntax.beh d) σ__r ->
    Stabilize hdstore Δ σ__r (AbstractSyntax.beh d) σ ->
    Stabilize hdstore Δ σ__r (AbstractSyntax.beh d) σ ->
    
    (* States [s] and [σ] are similar. *)
    SimStateAfterRE sitpn γ (s0 sitpn) σ.
Admitted.

(* Tries to apply the [first_rising_edge] lemma when the goal is of the form
   [SimStateAfterFE _ _ _ _] or [_ ⊢ _ ∼ _]. *)
#[export] Hint Resolve first_rising_edge : hilecop.
#[export] Hint Extern 1 ( _ ⊢ _ ∼ _ ) => eapply first_rising_edge; eauto : hilecop.
