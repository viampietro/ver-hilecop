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

(** ** Step lemma
    
    States that starting from similar state, state are similar after
    one execution cycle.

 *)

(* Lemma step_lemma : *)
(*   forall sitpn decpr id__ent id__arch mm d s s' E__c σ σ' Δ Mg σ__e P__i τ γ, *)
    
(*     (* sitpn translates into d. *) *)
(*     sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) -> *)

(*     (* Starting states are similar *) *)
(*     γ ⊢ s ∼ σ -> *)

(*     (* [Δ, σ__e] are the results of the elaboration of [d]. *) *)
(*     edesign hdstore Mg d Δ σ__e -> *)
    
(*     (* One execution cycle for SITPN *) *)
    
(*     @SitpnCycle sitpn E__c τ s s' -> *)

(*     (* One execution cycle for VHDL *) *)
(*     simcycle P__i Δ τ σ (behavior d) σ' -> *)
     
(*     (* Final states are similar *) *)
(*     γ ⊢ s' ∼ σ'. *)
(* Proof. *)
(*   intros *; intros Htransl Hsim Helab Hsitpn_cyc Hhdl_cyc. *)
(*   unfold SitpnCycle in Hsitpn_cyc. *)
(*   inversion_clear Hsitpn_cyc as (s__i & (Hrising, Hfalling)). *)
(*   inversion_clear Hhdl_cyc as *)
(*       (σ__injr, σ__r, σ__i, σ__injf, σ__f, σ'', θ, θ', *)
(*        Hhdl_rising, Hstab_rising, Hhdl_falling, Hstab_falling, Hinj_rising, Hinj_falling). *)

(*   (* Must prove s similar to σ after capture of input values on rising edge.  *)
(*      Necessary premise to apply [rising_edge_states_equal].       *)
(*    *) *)
(*   cut (γ ⊢ s ∼ σ__injr); intros Hsim_injr. *)
(*   specialize (rising_edge_states_equal *)
(*            Δ σ__r d θ σ__i σ__injr sitpn decpr E__c τ s s__i mm γ *)
(*            Htransl Hsim_injr Hrising Hhdl_rising Hstab_rising); intros Heq_int_states. *)

(*   (* Must prove s similar to σ after capture of input values on falling edge.  *)
(*      Necessary premise to apply [falling_edge_states_equal]. *)
(*    *) *)
(*   cut (γ ⊢ s__i ∼ σ__injf); intros Hsim_injf. *)
(*   apply (falling_edge_states_equal Δ σ__f d θ' σ' σ__injf sitpn decpr E__c τ s__i s' mm γ *)
(*                                    Htransl Hsim_injf Hfalling Hhdl_falling Hstab_falling). *)
  
(*   - admit. *)
(*   - admit. *)
(* Admitted. *)

(** ** Equal Initial States  *)

(* Lemma init_states_sim : *)
(*   forall sitpn decpr mm d Δ σ__e σ0 γ, *)
    
(*     (* sitpn translates into d. *) *)
(*     sitpn_to_hvhdl sitpn decpr mm = Success d -> *)

(*     (* ed, dstate are the results of the elaboration of d. *) *)
(*     edesign hdstore (empty value) d Δ σ__e -> *)

(*     (* initialization d's state. *) *)
(*     init Δ σ__e (get_behavior d) σ0 -> *)

(*     (* init states are similar *) *)
(*     γ ⊢ (s0 sitpn) ∼ σ0. *)
(* Proof. *)
(*   intros *; intros Htransl Helab Hinit. *)
(*   inversion_clear Hinit as (σ, beh, σ', σ'', θ, Hruninit, Hstab). *)

(* Admitted. *)

(** ** Similar States after First Cycle  *)

(* Lemma sim_after_first_cycle : *)
(*   forall sitpn decpr mm d E__c E__p Δ σ__e σ0 τ σ s γ, *)
(*     (* [sitpn] translates into [d]. *) *)
(*     sitpn_to_hvhdl sitpn decpr mm = Success d -> *)

(*     (* Environments are similar. *) *)
(*     EnvEq sitpn E__c E__p -> *)

(*     (* [Δ, σ__e] are the results of the elaboration of [d]. *) *)
(*     edesign hdstore (empty value) d Δ σ__e -> *)

(*     (* [σ0] is the initial state of [d]. *) *)
(*     init Δ σ__e (get_behavior d) σ0 -> *)

(*     (* From [σ0] to [σ] in one simulation cycle. *) *)
(*     simcycle E__p Δ (S τ) σ0 (get_behavior d) σ -> *)

(*     (* From [s0] to [s] in one execution cycle, where [Fired(s0) = ∅]. *) *)
(*     SitpnStateTransition E__c (S τ) (s0 sitpn) s falling_edge -> *)

(*     (* States [s] and [σ] are similar. *) *)
(*     γ ⊢ s ∼ σ. *)
(* Admitted. *)

(** ** Simulation Lemma *)

(* Lemma simulation_lemma : *)
  
(*   forall sitpn Ec τ s θ__s s', *)

(*     (* From state s to state s' after τ execution cycles, and *)
(*        producing trace θs. *) *)
(*     SitpnExecute Ec s τ θ__s s' -> *)

(*     forall decpr d mm Ep Δ σ__e θ__σ σ σ' γ, *)
      
(*     (* sitpn translates into d. *) *)
(*     sitpn_to_hvhdl sitpn decpr mm = Success d -> *)

(*     (* Environments are similar. *) *)
(*     EnvEq sitpn Ec Ep -> *)

(*     (* Δ, σe are the results of the elaboration of d. *) *)
(*     edesign hdstore (empty value) d Δ σ__e -> *)

(*     (* States s and σ are similar; *) *)
(*     γ ⊢ s ∼ σ -> *)
    
(*     (* From [σ] to [σ'] after τ execution cycles, producing trace [θ__σ]. *) *)
(*     simloop Ep Δ σ (get_behavior d) τ θ__σ σ' -> *)

(*     (* Conclusion *) *)
(*     SimTrace γ θ__s θ__σ. *)
(* Proof. *)
(*   intros *; intros Hexec; dependent induction Hexec; *)
(*   intros *; intros Htransl Henveq Helab Hsimstate Hsim. *)
  
(*   (* CASE tau = 0, trivial. *) *)
(*   - inversion Hsim; apply SimTraceInit. *)

(*   (* CASE tau > 0 *) *)
(*   - inversion_clear Hsim as [ τ0 σ0 σ'0 θ0 Hcyc Hsiml |  ]. *)
    
(*     (* Specializes the induction hypothesis, then apply the step lemma. *) *)
    
(*     specialize (IHHexec decpr d mm Ep Δ σ__e θ0 σ0 σ'). *)
(*     specialize (IHHexec γ Htransl Henveq Helab). *)

(*     (* Then, we need a lemma stating that s' ∼ σ0. That is, state are *)
(*        similar after one execution cycle. *) *)

(*     specialize (step_lemma sitpn decpr mm d s s' Ec σ σ0 Δ (empty value) σ__e Ep (S τ) γ *)
(*                            Htransl Hsimstate Helab H Hcyc) *)
(*       as Heq_state_cyc. *)

(*     (* Solve the induction case. *) *)
(*     apply (@SimTraceCons sitpn γ s' σ0 θ θ0); *)
(*       [ assumption | apply (IHHexec Heq_state_cyc Hsiml)]. *)
(* Qed. *)

(** ** Semantic Preservation Theorem *)

Theorem sitpn2vhdl_sound :
  forall sitpn decpr id__ent id__arch E__c τ θ__s d E__p mm θ__σ γ Δ,
      
    (* sitpn translates into d. *)
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
  intros.
  
  lazymatch goal with
  | [
    Htransl: sitpn_to_hvhdl _ _ _ _ _ = _,
    Hsenv: @SimEnv _ _ _ _,
    Hsitpnfexec: @SitpnFullExec _ _ _ _,
    Hhfsim: hfullsim _ _ _ _ _
    |- _ ] =>
    
    (* CASE τ = 0, traces are empty. Trivial. *)
    destruct τ; inversion_clear Hsitpnfexec; inversion_clear Hhfsim; [
      eauto |
      eauto
    ]
  end.

  (* CASE τ > 0. *)
  
  (* Asserts s0 ∼ σ0 *)
  lazymatch goal with
  | [ Htransl: sitpn_to_hvhdl _ _ _ = _, Helab: edesign _ _ _ _ _, Hinit: init _ _ _ _ |- _ ] =>
    specialize (init_states_sim sitpn decpr mm d Δ σ__e σ0 γ Htransl Helab Hinit) as Hinit_eq
  end.

  (* Asserts that [s0 ⇝↓ s] and [σ0 ⇝↑,↓ σ] then 
     [s ∼ σ].
     
     Here, [s0 ⇝↓ s ≡ s0 ⇝↑,↓ s] where [Fired(s0)] is
     forced to the empty set.
   *)
  lazymatch goal with
  | [ Htransl: sitpn_to_hvhdl _ _ _ = _,
      Henveq: EnvEq _ _ _,
      Helab: edesign _ _ _ _ _,
      Hinit: init _ _ _ _,
      Hsimcycle: simcycle _ _ _ _ _ _,
      Hexecfe: SitpnStateTransition _ _ _ _ _
      |-
      _
    ] =>
    specialize (sim_after_first_cycle
                  sitpn decpr mm d E__c E__p Δ σ__e σ0 τ σ s γ
                  Htransl Henveq Helab Hinit Hsimcycle Hexecfe)
      as Hfirst_sim
  end.

  (* Apply [simulation_lemma] to complete the proof *)
  
  lazymatch goal with
  | [ Htransl: sitpn_to_hvhdl _ _ _ = _,
      Henveq: EnvEq _ _ _,
      Helab: edesign _ _ _ _ _,
      Hinit: init _ _ _ _,
      Hsimcycle: simcycle _ _ _ _ _ _,
      Hexecfe: SitpnStateTransition _ _ _ _ _,
      Hsimloop: simloop _ _ _ _ _ _ _,
      Hsitpnexec: SitpnExecute _ _ _ _ _
      |-
      _
    ] =>
    apply (simulation_lemma
             sitpn E__c τ s θ__s s' Hsitpnexec decpr d mm E__p Δ σ__e θ__σ σ σ' γ
             Htransl Henveq Helab Hfirst_sim Hsimloop)
    end.
Qed.
    
