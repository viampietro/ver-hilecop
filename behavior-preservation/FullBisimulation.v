(** * Full bisimulation theorem *)

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
Require Import soundness.InitialStates.
Require Import soundness.FirstRisingEdge.
Require Import soundness.FallingEdge.
Require Import soundness.RisingEdge.

(** ** Bisimulation lemma *)

Lemma bisimulation :
  forall sitpn decpr id__ent id__arch b d γ E__c E__p Δ σ__e τ s σ θ__s θ__σ, 

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of d. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* States s and σ are similar (after a fe). *)
    FullSimStateAfterFE sitpn γ s σ ->

    (* From state s, produces trace [θ__s] after τ execution cycles. *)
    SitpnExecute E__c s τ θ__s ->
    
    (* From [σ], produces trace [θ__σ] after τ execution cycles. *)
    simloop hdstore E__p Δ σ (behavior d) τ θ__σ ->

    (* Conclusion *)
    SimTrace γ θ__s θ__σ re.
Proof.
  (* Induction on τ *)
  induction τ;
    intros *;
    intros Htransl Hsenv Helab Hsimstate Hsitpnexec Hhsim.
  
  (* CASE τ = 0, trivial. *)
  - inversion_clear Hsitpnexec; inversion_clear Hhsim; auto.

  (* CASE τ > 0 *)
  - inversion_clear Hsitpnexec; inversion_clear Hhsim;
    match goal with
    | [ H: simcycle _ _ _ _ _ _ _ _ |- _ ] =>
        inversion_clear H; constructor; [
          eauto with hilecop
        | constructor; eauto with hilecop ]
    end.      
Qed.

Hint Resolve bisimulation : hilecop.

(** Assuming the existence of an elaborated design [Δ], a default
    state [σ__e], an initial state [σ0], and a simulation trace [θ__σ] for
    a given H-VHDL design [d]. *)

Theorem full_bisimulation :
  forall sitpn decpr id__ent id__arch E__c τ θ__s d E__p b θ__σ γ Δ,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* SITPN [sitpn] yields execution trace [θ__s] after [τ] execution cycles. *)
    
    @SitpnFullExec sitpn E__c τ θ__s ->    
    
    (* Design [d] yields simulation trace [θ__σ] after [τ] simulation cycles. *)
    hfullsim E__p τ Δ d θ__σ ->
    
    (* ** Conclusion: traces are positionally similar. ** *)
    FullSimTrace γ θ__s θ__σ.
Proof.  
  (* Case analysis on τ *)
  destruct τ;
    intros *;
    inversion_clear 4;
    inversion_clear 1.

  (* CASE τ = 0, GOAL [γ ⊢ s0 ∼ σ0]. Solved with [sim_init_states] lemma. *)
  - lazymatch goal with
    | [ Hsimloop: simloop _ _ _ _ _ _ _ |- _ ] =>
        inversion_clear Hsimloop;
        constructor; eauto with hilecop
    end.

  (* CASE τ > 0, GOAL [γ ⊢ (s0 :: s :: θ__s) ∼ (σ0 :: σ :: θ0)].   
     Solved with [first_rising_edge], [falling_edge] and [bisimulation] lemmas. *)
    
  - lazymatch goal with
    | [ Hsimloop: simloop _ _ _ _ _ _ _ |- _ ] =>
        inversion_clear Hsimloop
    end.
    match goal with
    | [ H: simcycle _ _ _ _ _ _ _ _ |- _ ] =>
        inversion_clear H; constructor; eauto with hilecop
    end.
    constructor; eauto with hilecop.
    constructor; eauto with hilecop.
Qed.
