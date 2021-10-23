(** * Similar states after first rising edge  *)

Require Import sitpn.dp.SitpnLib.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.HVhdlHilecopLib.

Require Import sitpn2hvhdl.Sitpn2HVhdl.

Require Import soundness.SemanticPreservationDefs.

Lemma first_rising_edge_full :
  forall sitpn decpr id__ent id__arch b d γ E__c E__p Δ σ__e σ0 τ σ__i σ__r σ,

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* [σ0] is the initial state of [d]. *)
    init hdstore Δ σ__e (behavior d) σ0 ->

    (* From [σ0] to [σ] after [↑]. *)
    IsInjectedDState σ0 (E__p τ) σ__i ->
    vrising hdstore Δ σ__i (behavior d) σ__r ->
    stabilize hdstore Δ σ__r (behavior d) σ ->
    
    (* States [s] and [σ] are similar. *)
    FullSimStateAfterRE sitpn γ E__c τ (s0 sitpn) σ.
Admitted.

(* Tries to apply the [first_rising_edge] lemma when the goal is of the form
   [SimStateAfterFE _ _ _ _] or [_ ⊢ _ ∼ _]. *)
Hint Resolve first_rising_edge_full : hilecop.
Hint Extern 1 ( _ ⊢ _ ∼ _ ) => eapply first_rising_edge_full; eauto : hilecop.

Lemma first_rising_edge :
  forall sitpn decpr id__ent id__arch b d γ E__c E__p Δ σ__e σ0 τ σ__i σ__r σ,

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* [σ0] is the initial state of [d]. *)
    init hdstore Δ σ__e (behavior d) σ0 ->

    (* From [σ0] to [σ] after [↑]. *)
    IsInjectedDState σ0 (E__p τ) σ__i ->
    vrising hdstore Δ σ__i (behavior d) σ__r ->
    stabilize hdstore Δ σ__r (behavior d) σ ->
    
    (* States [s] and [σ] are similar. *)
    SimStateAfterRE sitpn γ (s0 sitpn) σ.
Admitted.

(* Tries to apply the [first_rising_edge] lemma when the goal is of the form
   [SimStateAfterFE _ _ _ _] or [_ ⊢ _ ∼ _]. *)
Hint Resolve first_rising_edge : hilecop.
Hint Extern 1 ( _ ⊢ _ ∼ _ ) => eapply first_rising_edge; eauto : hilecop.
