(** * Facts about Rising Edge and the Soundness Proof *)

Require Import common.NatMap.
Require Import common.GlobalTypes.

Require Import dp.Sitpn.
Require Import dp.SitpnSemantics.
Require Import dp.SitpnTypes.

Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Stabilize.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SynchronousEvaluation.
Require Import hvhdl.HVhdlTypes.

Require Import sitpn2hvhdl.GenerateHVhdl.

Require Import SoundnessDefs.

(** ** Rising edge marking equal lemma

    States that starting from similar state, markings are equal
    after the rising edge of the clock signal.  *)

Lemma rising_edge_marking_equal :
  forall Δ σ__r d θ σ' σ sitpn decpr Ec τ s s' mm γ,

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn decpr mm = Success d ->

    (* Similar starting states *)
    γ ⊢ s ∼ σ ->
    
    (* Rising edge from s to s', s ⇝↑ s' *)
    SitpnStateTransition Ec τ s s' rising_edge -> 

    (* Rising edge from σ to σr *)
    vrising Δ σ (get_behavior d) σ__r -> 

    (* Stabilize from σr to σ' *)
    stabilize Δ σ__r (get_behavior d) θ σ' ->
    
    (* Conclusion *)
    forall p id__p σ'__p,
      (* [idp] is the identifier of the place component associated with
       place [p] by the [γ] binder. *)
      γ (inl p) = id__p ->

      (* [σp] is the current state of component [idp] is the global design
       state [σ]. *)
      MapsTo id__p σ'__p (compstore σ') ->

      (* Marking of place [p] at state [s] equals value of signal
         [s_marking] at state [σp]. *)
      MapsTo Place.s_marking (Vnat (@M sitpn s' p)) (sigstore σ'__p).
Proof.
Admitted.

(** ** Rising edge states equal.
 
    Utopic lemma; not sure it is provable. *)

Lemma rising_edge_states_equal :
  forall Δ σ__r d θ σ' σ sitpn decpr E__c τ s s' mm (γ : P sitpn + T sitpn -> ident),

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn decpr mm = Success d ->

    (* Similar starting states *)
    γ ⊢ s ∼ σ ->
    
    (* Rising edge from s to s', s ⇝↑ s' *)
    SitpnStateTransition E__c τ s s' rising_edge -> 

    (* Rising edge from σ to σr *)
    vrising Δ σ (get_behavior d) σ__r -> 

    (* Stabilize from σr to σ' *)
    stabilize Δ σ__r (get_behavior d) θ σ' ->
    
    (* Conclusion *)
    γ ⊢ s' ∼ σ'.
Proof.
Admitted.
