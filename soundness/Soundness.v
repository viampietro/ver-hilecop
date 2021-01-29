(** * Semantic Preservation Theorem *)

Require Import NatMap.

Require Import common.Coqlib.
Require Import common.InAndNoDup.
Require Import common.GlobalTypes.
Require Import common.ListPlus.

(* SITPN Libraries *)

Require Import dp.SitpnSemanticsDefs.
Require Import dp.SitpnTypes.
Require Import dp.Sitpn.
Require Import dp.SitpnSemantics.
Require Import dp.Fired.
Require Import dp.SitpnWellDefined.

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

Require Import sitpn2hvhdl.GenerateHVhdl.

(* Soundness definitions and lemmas *)

Require Import soundness.SoundnessDefs.
Require Import soundness.InitialStates.
Require Import soundness.RisingEdge.
Require Import soundness.FallingEdge.

Local Unset Implicit Arguments.

(** ** Similar States after First Cycle  *)

Lemma first_cycle :
  forall sitpn decpr id__ent id__arch mm d γ E__c E__p Δ σ__e σ0 τ σ s,

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* [σ0] is the initial state of [d]. *)
    init hdstore Δ σ__e (behavior d) σ0 ->

    (* From [σ0] to [σ] in one simulation cycle. *)
    simcycle hdstore E__p Δ τ σ0 (behavior d) σ ->

    (* From [s0] to [s] in one execution cycle, with an idle rising
       edge (where [Fired(s0) = ∅]). *)
    SitpnStateTransition E__c τ (s0 sitpn) s fe ->

    (* States [s] and [σ] are similar. *)
    SimStateAfterFE sitpn γ s σ.
Admitted.

(* Tries to apply the [first_cycle] lemma when the goal is of the form
   [SimStateAfterFE _ _ _ _] or [_ ⊢ _ ∼ _]. *)
Hint Resolve first_cycle : hilecop.
Hint Extern 1 ( _ ⊢ _ ∼ _ ) => eapply first_cycle; eauto : hilecop.

(** ** Step lemma
    
    States that starting from similar state, state are similar after
    one execution cycle. *)

Lemma step :
  forall sitpn decpr id__ent id__arch mm d γ E__c E__p Δ σ__e τ s s'' σ σ'',
    
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->

    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    
    (* Starting states are similar (post fe similarity). *)
    SimStateAfterFE sitpn γ s σ ->
    
    (* One execution cycle for [sitpn]. *)    
    @SitpnCycle sitpn E__c τ s s'' ->

    (* One execution cycle for [d] *)
    simcycle hdstore E__p Δ τ σ (behavior d) σ'' ->
     
    (* Final states are similar *)
    SimStateAfterFE sitpn γ s'' σ''.
Proof.
  intros *; intros Htransl Hsenv Helab Hsimstate Hsitpncyc Hhcyc.
  
  inversion_clear Hsitpncyc as (s' & (Hrising, Hfalling)).
  inversion_clear Hhcyc as
      (σ__injr, σ__r, σ', σ__injf, σ__f, θ, θ',
       Hh_rising, Hstab_rising, Hh_falling, Hstab_falling, Hinj_rising, Hinj_falling).
  (* Applies [rising_edge], then [falling_edge] lemmas. *)
  eauto.
Qed.

(* Tries to apply the [step] lemma when the goal is of the form
   [SimStateAfterFE _ _ _ _] or [_ ⊢ _ ∼ _]. *)

Hint Resolve step : hilecop.
Hint Extern 1 ( _ ⊢ _ ∼ _ ) => eapply step; eauto : hilecop.

(** ** Simulation Lemma *)

Lemma simulation :
  forall sitpn decpr id__ent id__arch mm d γ E__c E__p Δ σ__e τ s σ θ__s θ__σ, 

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of d. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* States s and σ are similar (after a fe). *)
    SimStateAfterFE sitpn γ s σ ->

    (* From state s, produces trace [θ__s] after τ execution cycles. *)
    SitpnExecute E__c s τ θ__s ->
    
    (* From [σ], produces trace [θ__σ] after τ execution cycles. *)
    simloop hdstore E__p Δ σ (behavior d) τ θ__σ ->

    (* Conclusion *)
    SimTrace γ θ__s θ__σ.
Proof.
  (* Induction on τ *)
  induction τ;
    intros *;
    intros Htransl Hsenv Helab Hsimstate Hsitpnexec Hhsim.
  
  (* CASE τ = 0, trivial. *)
  - inversion_clear Hsitpnexec; inversion_clear Hhsim; auto.

  (* CASE τ > 0 *)
  - inversion_clear Hsitpnexec; inversion_clear Hhsim; constructor.

    (* GOAL [γ ⊢ s' ∼ σ']. Solved with [step] lemma. *)
    + eauto with hilecop.

    (* Apply induction hypothesis. *)
    + eapply IHτ with (s := s') (σ := σ'); eauto with hilecop.
      
Qed.

Hint Resolve simulation : hilecop.

(** ** Behavior Preservation Theorem *)

(** ** Version 1 *)

(** Assuming the existence of an elaborated design [Δ], a default
    state [σ__e], an initial state [σ0], and a simulation trace [θ__σ] for
    a given H-VHDL design [d]. *)

Theorem sitpn2vhdl_sound1 :
  forall sitpn decpr id__ent id__arch E__c τ θ__s d E__p mm θ__σ γ Δ,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* SITPN [sitpn] yields execution trace [θ__s] after [τ] execution cycles. *)
    
    @SitpnFullExec sitpn E__c τ θ__s ->    
    
    (* Design [d] yields simulation trace [θ__σ] after [τ] simulation cycles. *)
    hfullsim E__p τ Δ d θ__σ ->
    
    (* ** Conclusion: traces are positionally similar. ** *)
    SimTrace γ θ__s θ__σ.
Proof.
  (* Case analysis on τ *)
  destruct τ;
    intros *;
    inversion_clear 4;
    inversion_clear 1;

  (* - CASE τ = 0, GOAL [γ ⊢ s0 ∼ σ0]. Solved with [sim_init_states] lemma. 
     - CASE τ > 0, GOAL [γ ⊢ (s0 :: s :: θ__s) ∼ (σ0 :: σ :: θ0)].  
     Solved with [first_cycle] and [simulation] lemmas. *)
    lazymatch goal with
    | [ Hsimloop: simloop _ _ _ _ _ _ _ |- _ ] =>
      inversion_clear Hsimloop; constructor; eauto with hilecop
    end.
Qed.

(** ** Version 2  *)

(** Proving the existence of an elaborated design [Δ], a default state
    [σ__e], an initial state [σ0], and a simulation trace [θ__σ] for a
    given H-VHDL design [d].

    Right now the existence theorems are declared as axioms.  *)

Axiom sitpn2hvhdl_elab_ex :
  forall sitpn decpr id__ent id__arch mm d γ,
    
    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* there exists an elaborated version [Δ] of [d], with a default state [σ__e] *)
    exists Δ σ__e, edesign hdstore (NatMap.empty value) d Δ σ__e.

Axiom sitpn2vhdl_init_state_ex :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ__e,
    
    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* An elaborated version [Δ] of [d], with a default state [σ__e] *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* There exists an initial state [σ0] of [d]. *)
    exists σ0, init hdstore Δ σ__e (behavior d) σ0. 

(** The simulation environment [E__p] is well-defined, i.e, it
    associates a value of the right type to all the input ports of
    [Δ]. *)

Definition IsWellDefinedSimEnv (Δ : ElDesign) (E__p : nat -> Clk -> IdMap value) : Prop :=
  forall τ clk,
    (forall id v, MapsTo id v (E__p τ clk) -> exists t, MapsTo id (Input t) Δ /\ is_of_type v t)
    /\ (forall id t, MapsTo id (Input t) Δ -> exists v, MapsTo id v (E__p τ clk) /\ is_of_type v t).

Axiom IsWellDefinedSimEnv_ex :
  forall Δ, exists E__p, IsWellDefinedSimEnv Δ E__p.

Axiom SimEnv_ex : forall sitpn γ E__c, exists E__p, SimEnv sitpn γ E__c E__p.

Axiom sitpn2vhdl_sim_ex :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ__e σ0 τ E__p,

    
    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* An elaborated version [Δ] of [d], with a default state [σ__e] *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* An initial state [σ0] of [d]. *)
    init hdstore Δ σ__e (behavior d) σ0 ->

    (* The simulation env [E__p] is well-defined. *)
    IsWellDefinedSimEnv Δ E__p ->
    
    exists θ__σ, simloop hdstore E__p Δ σ0 (behavior d) τ θ__σ.

Theorem sitpn2vhdl_sound2 :
  forall sitpn decpr id__ent id__arch mm d γ E__c τ θ__s,
      
    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
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
        
        (* Traces are positionally similar. *)
        SimTrace γ θ__s θ__σ.
Proof.
  intros.
  edestruct sitpn2hvhdl_elab_ex as (Δ, (σ__e, Helab)); eauto.
  edestruct sitpn2vhdl_init_state_ex as (σ0, Hinit); eauto.
  exists Δ; intros.
  edestruct @sitpn2vhdl_sim_ex with (τ := τ) as (θ__σ, Hsim); eauto.  
  exists (σ0 :: θ__σ). split.

  (* Existence of an elaborated design [Δ], a default state [σ__e], an
     initial state [σ0], and a simulation trace [θ__σ]. *)
  unfold hfullsim; eapply FullSim; eauto.

  (* Similar traces. *)
  eapply sitpn2vhdl_sound1; eauto.
  unfold hfullsim; eapply FullSim; eauto.  
Qed.
