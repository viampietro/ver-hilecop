(** * Similar Initial States *)

Require Import common.NatMap.

Require Import sitpn.dp.SitpnSemantics.

Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.Initialization.

Require Import sitpn2hvhdl.GenerateHVhdl.

Require Import soundness.SoundnessDefs.

(** ** Similar Initial States Lemma *)

Lemma sim_init_states :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ__e σ0,
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (empty value) d Δ σ__e ->

    (* initialization d's state. *)
    init Δ σ__e (behavior d) σ0 ->

    (* init states are similar *)
    γ ⊢ (s0 sitpn) ∼ σ0.
Proof.
  
Admitted.

Hint Resolve sim_init_states : core.
