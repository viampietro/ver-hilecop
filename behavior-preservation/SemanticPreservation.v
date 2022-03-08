(** * Semantic Preservation Theorem *)

Require Import NatMap.

Require Import common.CoqLib.
Require Import common.InAndNoDup.
Require Import common.GlobalTypes.
Require Import common.ListPlus.

(* SITPN Libraries *)

Require Import sitpn.SitpnSemanticsDefs.
Require Import sitpn.SitpnTypes.
Require Import sitpn.Sitpn.
Require Import sitpn.SitpnSemantics.
Require Import sitpn.Fired.
Require Import sitpn.SitpnWellDefined.

(* H-VHDL Libraries *)

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Simulation.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.SynchronousEvaluation.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.Initialization.
Require Import hvhdl.Stabilize.
Require Import hvhdl.PortMapEvaluation.

(* SITPN to H-VHDL Libraries *)

Require Import transformation.GenerateHVhdl.

(* Soundness definitions and lemmas *)

Require Import soundness.SemanticPreservationDefs.
Require Import soundness.TraceSimilarity.
(* Require Import soundness.InitialStates. *)
(* Require Import soundness.RisingEdge. *)
(* Require Import soundness.FallingEdge. *)

Local Unset Implicit Arguments.

(** ** Elaboration theorem *)

(** There exist an elaborated design [Δ], a default state [σ__e] that
    verify the elaboration relation for a design [d], where [d] is the
    result of the HILECOP transformation performed on a well-defined
    SITPN model [sitpn]. *)

Axiom sitpn2hvhdl_elab_ex :
  forall sitpn id__ent id__arch mm d γ,

    (* The SITPN model [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn id__ent id__arch mm = (inl (d, γ)) ->

    (* there exists an elaborated version [Δ] of [d], with a default state [σ__e] *)
    exists Δ σ__e, edesign hdstore (NatMap.empty value) d Δ σ__e.

(** ** Initialization theorem *)

(** There exist an initial state [σ0] that verify the initialization
    relation for a design [d] result of the HILECOP transformation of
    a well-defined SITPN model [sitpn], an elaborated design [Δ] and a
    default design state [σ__e].  *)

Axiom sitpn2vhdl_init_state_ex :
  forall sitpn id__ent id__arch mm d γ Δ σ__e,

    (* The SITPN model [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn id__ent id__arch mm = (inl (d, γ)) ->

    (* An elaborated version [Δ] of [d], with a default state [σ__e] *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* There exists an initial state [σ0] of [d]. *)
    exists σ0, init hdstore Δ σ__e (behavior d) σ0. 

(** ** Simulation trace theorem *)

(** The simulation environment [E__p] is well-defined, i.e, it
    associates a value of the right type to all the input ports of
    [Δ]. *)

Definition IsWellDefinedSimEnv (Δ : ElDesign) (E__p : nat -> IdMap value) : Prop :=
  forall τ,
    (forall id v, MapsTo id v (E__p τ) -> exists t, MapsTo id (Input t) Δ /\ is_of_type v t)
    /\ (forall id t, MapsTo id (Input t) Δ -> exists v, MapsTo id v (E__p τ) /\ is_of_type v t).

Axiom IsWellDefinedSimEnv_ex :
  forall Δ, exists E__p, IsWellDefinedSimEnv Δ E__p.

Axiom SimEnv_ex : forall sitpn γ E__c, exists E__p, SimEnv sitpn γ E__c E__p.

(** There exist a simulation trace [θ__σ] that verify the [simloop] for
    all design [d] result of the transformation of a well-defined and
    bounded SITPN model [sitpn]. *)

Axiom sitpn2vhdl_sim_ex :
  forall sitpn id__ent id__arch mm d γ Δ σ__e σ0 τ E__p b,

    (* The SITPN model [sitpn] is well-defined. *)
    IsWellDefined sitpn ->

    (* The SITPN model [sitpn] is bounded through [b]. *)
    @BoundedSitpn sitpn b ->
    
    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn id__ent id__arch mm = (inl (d, γ)) ->

    (* An elaborated version [Δ] of [d], with a default state [σ__e] *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* An initial state [σ0] of [d]. *)
    init hdstore Δ σ__e (behavior d) σ0 ->

    (* The simulation env [E__p] is well-defined. *)
    IsWellDefinedSimEnv Δ E__p ->
    
    exists θ__σ, simloop hdstore E__p Δ σ0 (behavior d) τ θ__σ.

(** ** Semantic preservation theorem  *)

Theorem sitpn2vhdl_semantic_preservation :
  forall sitpn id__ent id__arch b d γ E__c τ θ__s,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] is bounded through [b]. *)
    @BoundedSitpn sitpn b ->
    
    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn id__ent id__arch b = (inl (d, γ)) ->
    
    (* SITPN [sitpn] yields execution trace [θ__s] after [τ] execution cycles. *)
    
    @SitpnFullExec sitpn E__c τ θ__s ->    

    exists Δ,
    forall E__p,
      (* Simulation environment [E__p] is well-defined. *)
      IsWellDefinedSimEnv Δ E__p ->

      (* Environments are similar. *)
      SimEnv sitpn γ E__c E__p ->
      
      exists θ__σ,
        
        (* Design [d] yields simulation trace [θ__σ] after [τ] simulation cycles. *)
        hfullsim E__p τ Δ d θ__σ /\
        
        (* Traces are fully similar. *)
        FullSimTrace γ θ__s θ__σ.
Proof.
  (* intros. *)
  (* edestruct sitpn2hvhdl_elab_ex as (Δ, (σ__e, Helab)); eauto. *)
  (* edestruct sitpn2vhdl_init_state_ex as (σ0, Hinit); eauto. *)
  (* exists Δ; intros. *)
  (* edestruct @sitpn2vhdl_sim_ex with (τ := τ) as (θ__σ, Hsim); eauto.   *)
  (* exists (σ0 :: θ__σ). split. *)

  (* Existence of an elaborated design [Δ], a default state [σ__e], an
     initial state [σ0], and a simulation trace [θ__σ]. *)
  (* unfold hfullsim; eapply FullSim; eauto. *)

  (* Similar traces. *)
  (* eapply trace_sim; eauto. *)
  (* unfold hfullsim; eapply FullSim; eauto.   *)
Admitted.




