(** * Semantic Preservation Theorem *)

Require Import NatMap.

Require Import common.Coqlib.
Require Import common.InAndNoDup.
Require Import common.GlobalTypes.
Require Import common.ListsPlus.


(* SITPN Libraries *)

Require Import dp.SitpnSemanticsDefs.
Require Import dp.SitpnTypes.
Require Import dp.Sitpn.
Require Import dp.SitpnSemantics.
Require Import dp.Fired.

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

Local Unset Implicit Arguments.

(* ** Equal Initial States *)

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

(** ** Step lemma
    
    States that starting from similar state, state are similar after
    one execution cycle.

 *)

Lemma step :
  forall sitpn decpr id__ent id__arch mm d γ E__c E__p Δ σ__e τ s s'' σ σ'',
    
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->

    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (empty value) d Δ σ__e ->
    
    (* Starting states are similar (post fe similarity). *)
    SimStateAfterFE sitpn γ s σ ->
    
    (* One execution cycle for [sitpn]. *)    
    @SitpnCycle sitpn E__c τ s s'' ->

    (* One execution cycle for [d] *)
    simcycle E__p Δ τ σ (behavior d) σ'' ->
     
    (* Final states are similar *)
    SimStateAfterFE sitpn γ s'' σ''.
Proof.
  intros *; intros Htransl Hsenv Helab Hsimstate Hsitpncyc Hhcyc.
  
  inversion_clear Hsitpncyc as (s' & (Hrising, Hfalling)).
  inversion_clear Hhcyc as
      (σ__injr, σ__r, σ', σ__injf, σ__f, θ, θ',
       Hh_rising, Hstab_rising, Hh_falling, Hstab_falling, Hinj_rising, Hinj_falling).
Admitted.

(* Tries to apply the [step] lemma when the goal is of the form
   [SimStateAfterFE _ _ _ _] or [_ ⊢ _ ∼ _]. *)

Hint Resolve step : core.
Hint Extern 1 ( _ ⊢ _ ∼ _ ) => eapply step; eauto : core.

(** ** Similar States after First Cycle  *)

Lemma first_cycle :
  forall sitpn decpr id__ent id__arch mm d γ E__c E__p Δ σ__e σ0 τ σ s,

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (empty value) d Δ σ__e ->

    (* [σ0] is the initial state of [d]. *)
    init Δ σ__e (behavior d) σ0 ->

    (* From [σ0] to [σ] in one simulation cycle. *)
    simcycle E__p Δ τ σ0 (behavior d) σ ->

    (* From [s0] to [s] in one execution cycle, where [Fired(s0) = ∅]. *)
    SitpnStateTransition E__c τ (s0 sitpn) s falling_edge ->

    (* States [s] and [σ] are similar. *)
    SimStateAfterFE sitpn γ s σ.
Admitted.

(* Tries to apply the [first_cycle] lemma when the goal is of the form
   [SimStateAfterFE _ _ _ _] or [_ ⊢ _ ∼ _]. *)
Hint Resolve first_cycle : core.
Hint Extern 1 ( _ ⊢ _ ∼ _ ) => eapply first_cycle; eauto : core.

(** ** Simulation Lemma *)

Lemma simulation :
  forall sitpn decpr id__ent id__arch mm d γ E__c E__p Δ σ__e τ s σ θ__s θ__σ, 

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of d. *)
    edesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (after a fe). *)
    SimStateAfterFE sitpn γ s σ ->

    (* From state s, produces trace [θ__s] after τ execution cycles. *)
    SitpnExecute E__c s τ θ__s ->
    
    (* From [σ], produces trace [θ__σ] after τ execution cycles. *)
    simloop E__p Δ σ (behavior d) τ θ__σ ->

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
    + eauto.

    (* Apply induction hypothesis. *)
    + eapply IHτ with (s := s') (σ := σ'); eauto.
      
Qed.

Hint Resolve simulation : core.

(** ** Behavior Preservation Theorem *)

Theorem sitpn2vhdl_sound :
  forall sitpn decpr id__ent id__arch E__c τ θ__s d E__p mm θ__σ γ Δ,
      
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
    intros *; intros Htransl Hsenv Hsitpnfexec Hhfsim;
    inversion_clear Hsitpnfexec;
    inversion_clear Hhfsim;

    (* - CASE τ = 0, GOAL [γ ⊢ s0 ∼ σ0]. Solved with [sim_init_states] lemma. 
       - CASE τ > 0, GOAL [γ ⊢ (s0 :: s :: θ__s) ∼ (σ0 :: σ :: θ0)].  
         Solved with [first_cycle] and [simulation] lemmas. *)
    lazymatch goal with
    | [ Hsimloop: simloop _ _ _ _ _ _ |- _ ] =>
      inversion_clear Hsimloop; constructor; eauto
    end.
Qed.
    
