(** * Semantic preservation theorem *)

(** This module gathers all theorems stating the correctness of the
    HILECOP model-to-text transformation (HM2T). The HM2T is
    implemented by the sitpn2hvhdl function. *)

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
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.Initialization.
Require Import hvhdl.Stabilization.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.TypeElaboration.
Require Import hvhdl.CSEvaluation.

(* SITPN to H-VHDL Libraries *)

Require Import transformation.GenerateHVhdl.

(* Soundness definitions and lemmas *)

Require Import soundness.SemanticPreservationDefs.
Require Import soundness.TraceSimilarity.

Require Import soundness.InitialStates.
Require Import soundness.FirstRisingEdge.
Require Import soundness.RisingEdge.
Require Import soundness.FallingEdge.

Local Unset Implicit Arguments.

(** ** Elaboration theorem *)

(** There exist an elaborated design [Δ], a default state [σ__e] that
    verify the elaboration relation for a design [d], where [d] is the
    result of the HM2T performed on a well-defined SITPN model
    [sitpn]. *)

Axiom elab_ex :
  forall sitpn b d γ,

    (* The SITPN model [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* there exists an elaborated version [Δ] of [d], with a default state [σ__e] *)
    exists Δ σ__e, EDesign hdstore (NatMap.empty value) d Δ σ__e.

(** ** Correctness of the HM2T *)

(** The simulation environment [E__p] is well-defined, i.e. at each time
    count, it associates a value of the right type to all the
    identifiers declared as input ports of the design [d].  *)

Definition IsWDSimEnvForDesign (d : design) (E__p : nat -> IdMap value) : Prop :=
  forall tc,
    (forall id v,
        MapsTo id v (E__p tc) ->
        exists τ, In (pdecl_in id τ) (ports d)
                  /\ forall Δ t, EType Δ τ t -> IsOfType v t).

(** The simulation environment [E__p] is well-defined, i.e. it
    associates a value of the right type to all the input ports
    declared in the elaborated design [Δ]. Injectivity of the map
    yielded by the [E__p] function at a given time count [τ] regarding
    the set of input port identifiers declared in [Δ]. *)

Definition IsWDSimEnvForElDesign (Δ : ElDesign) (E__p : nat -> IdMap value) : Prop :=
  forall tc,
    (forall id v, MapsTo id v (E__p tc) -> exists t, MapsTo id (Input t) Δ /\ IsOfType v t).

(** States that if an simulation environment [E__p] is well-defined for
    a design [d], then it is well-defined for the elaborated version
    of the design [Δ]. *)

Lemma IsWDSimEnv_trans :
  forall D__s M__g d Δ σ__e,
    EDesign D__s M__g d Δ σ__e ->
    forall E__p,
      IsWDSimEnvForDesign d E__p -> IsWDSimEnvForElDesign Δ E__p.
Admitted.

(** There exist a simulation trace [θ__σ] that verify the [SimLoop] for
    all design [d] result of the transformation of a well-defined and
    bounded SITPN model [sitpn]. *)

Axiom sitpn2vhdl_sim_ex :
  forall sitpn (b : P sitpn -> nat) d γ Δ σ__e σ0 τ E__p b,

    (* The SITPN model [sitpn] is well-defined. *)
    IsWellDefined sitpn ->

    (* The SITPN model [sitpn] is bounded through [b]. *)
    BoundedSitpn b ->
    
    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* An elaborated version [Δ] of [d], with a default state [σ__e] *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* An initial state [σ0] of [d]. *)
    Init hdstore Δ σ__e (beh d) σ0 ->

    (* The simulation env [E__p] is well-defined. *)
    IsWDSimEnvForElDesign Δ E__p ->
    
    exists θ__σ, SimLoop hdstore E__p Δ σ0 (beh d) τ θ__σ.

(** ** Semantic preservation (correctness) theorem  *)

(** Declares the correctness theorem for the HM2T. This version of the
    proof uses the "Full trace similarity" lemma (defined in
    TraceSimilarity.v). *)

Theorem sitpn2vhdl_correct_with_trace_sim :
  forall sitpn b d γ E__c E__p τ θ__s,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] is bounded through [b]. *)
    BoundedSitpn b ->
    
    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* [E__p] is a well-defined simulation environment for design [d]. *)
    IsWDSimEnvForDesign d E__p ->
    
    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* SITPN [sitpn] yields execution trace [θ__s] after [τ] execution cycles. *)
    @SitpnFullExec sitpn E__c τ θ__s ->    
      
    exists θ__σ,
      
      (* Design [d] yields simulation trace [θ__σ] after [τ] simulation cycles. *)
      HFullSim E__p τ d θ__σ
        
      (* Traces are fully similar. *)
      /\ FullSimTrace γ θ__s θ__σ.
Proof.
  intros.
  edestruct elab_ex as (Δ, (σ__e, Helab)); eauto.
  edestruct init_state_ex as (σ0, Hinit); eauto.
  edestruct @sitpn2vhdl_sim_ex with (τ := τ) as (θ__σ, Hsim); eauto.
  eapply IsWDSimEnv_trans; eauto.
  exists (σ0 :: θ__σ). split.

  (* Existence of an elaborated design [Δ], a default state [σ__e], an *)
  (*    initial state [σ0], and a simulation trace [θ__σ]. *)
  unfold HFullSim; eapply FullSim_; eauto.

  (* Similar traces. *)
  eapply full_trace_sim; eauto.
  unfold HFullSim; eapply FullSim_; eauto.  
Qed.

(** Declares the forward simulation theorem for the HM2T. *)

Theorem sitpn2vhdl_fwd_sim :
  forall sitpn b d γ E__c E__p s τ θ__s Δ σ__e,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] is bounded through [b]. *)
    BoundedSitpn b ->
    
    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->
    
    (* [E__p] is a well-defined simulation environment for design [d]. *)
    IsWDSimEnvForDesign d E__p ->

    (* An elaborated version [Δ] of [d], with a default state [σ__e] *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    
    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* SITPN [sitpn] yields execution trace [θ__s] after [τ] execution
       cycles, starting from state [s]. *)
    @SitpnExecute sitpn E__c s τ θ__s ->
    
    forall σ,

      (* States [s] and [σ] are similar as intended after a whole
         clock cycle. *)
      FullSimStateAfterFE sitpn γ s σ ->
      
    exists θ__σ,
      
      (* Design [d] yields simulation trace [θ__σ] after [τ] simulation
         cycles starting from state [σ]. *)
      SimLoop hdstore E__p Δ σ (beh d) τ θ__σ

      (* Traces are fully similar. *)
      /\ SimTrace γ θ__s θ__σ re.
Proof.
  intros *; do 6 intro.

  (* Induction over the SITPN execution relation. *)
  induction 1.

  (* CASE [θ__s = []] and [τ = 0]. *)
  - intros; exists []; split; econstructor.

  (* CASE τ > 0 and [θ__s = s' :: s'' :: θ__s] *)
  - intros.
    edestruct rising_edge_lock_step_full as (σ__r, (σ', (HVConc_r, (HStab_r, Hsim_r))));
      eauto.
    edestruct falling_edge_lock_step_full as (σ__f, (σ'', (HVConc_f, (HStab_f, Hsim_f))));
      eauto.
    edestruct IHSitpnExecute as (θ__σ, (Htrace, Hsim_traces)); eauto.
    exists (σ' :: σ'' :: θ__σ); split.
    constructor; eauto with hilecop hvhdl.
    econstructor; eauto with hilecop hvhdl.
    constructor; eauto with hilecop.
Qed.

(** Declares the correctness theorem for the HM2T. This version of the
   proof is performed by induction on the SITPN execution relation and
   uses the different lock-step lemmas. *)

Theorem sitpn2vhdl_correct_with_lock_step :
  forall sitpn b d γ E__c E__p τ θ__s,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] is bounded through [b]. *)
    BoundedSitpn b ->
    
    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* [E__p] is a well-defined simulation environment for design [d]. *)
    IsWDSimEnvForDesign d E__p ->
    
    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* SITPN [sitpn] yields execution trace [θ__s] after [τ] execution cycles. *)
    @SitpnFullExec sitpn E__c τ θ__s ->    
    
    exists θ__σ,
      
      (* Design [d] yields simulation trace [θ__σ] after [τ] simulation cycles. *)
      HFullSim E__p τ d θ__σ

      (* Traces are fully similar. *)
      /\ FullSimTrace γ θ__s θ__σ.

Proof.
  intros *; do 5 intro.

  edestruct elab_ex as (Δ, (σ__e, Helab)); eauto.
  edestruct sim_init_state_ex as (σ0, (Hinit, Hsim_ini_state)); eauto.

  induction 1.

  (* CASE τ = 0 *)
  - exists [σ0].
    split;
      [ unfold HFullSim; eapply FullSim_; eauto with hilecop hvhdl
      | eauto with hilecop ].

  (* CASE τ > 0, then at least one cycle is performed. *)
  - (* States are similar after first rising edge. *)
    edestruct first_rising_edge_lock_step_full with (τ := S τ)
      as (σ__r, (σ'0, (HVConc0, (Hstab0, Hfsim0))));
      eauto.

    (* States are similar at the end of the first clock cycle
       (i.e. after the first falling edge). *)
    edestruct falling_edge_lock_step_full as (σ__f, (σ', (HVConc1, (Hstab1, Hfsim1)))); eauto.

    (* Trailing traces are similar *)
    edestruct @sitpn2vhdl_fwd_sim with (τ := τ) as (θ__σ, (Hloop, Hsim)); eauto.

    (* Exhibits the similar simulation trace. *)
    exists (σ0 :: σ'0 :: σ' :: θ__σ).
    split.
    unfold HFullSim; eapply FullSim_; eauto with hilecop hvhdl.
    constructor; eauto with hilecop hvhdl.
    econstructor; eauto with hvhdl.
    eauto with hilecop.
    econstructor; eauto.
    econstructor; eauto with hilecop.
Qed.


