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

(** ** Trace similarity lemma *)

Lemma trace_sim :
  forall sitpn id__ent id__arch b d γ E__c E__p Δ σ__e τ s σ θ__s θ__σ, 

    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn id__ent id__arch b = (inl (d, γ)) ->

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

#[export] Hint Resolve trace_sim : hilecop.

(** Assuming the existence of an elaborated design [Δ], a default
    state [σ__e], an initial state [σ0], and a simulation trace [θ__σ] for
    a given H-VHDL design [d]. *)

Theorem full_trace_sim :
  forall sitpn id__ent id__arch E__c τ θ__s d E__p b θ__σ γ,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn id__ent id__arch b = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* SITPN [sitpn] yields execution trace [θ__s] after [τ] execution cycles. *)
    
    @SitpnFullExec sitpn E__c τ θ__s ->    
    
    (* Design [d] yields simulation trace [θ__σ] after [τ] simulation cycles. *)
    hfullsim E__p τ d θ__σ ->
    
    (* ** Conclusion: traces are positionally similar. ** *)
    FullSimTrace γ θ__s θ__σ.
Proof.  
  (* Case analysis on τ *)
  destruct τ; intros;
  match goal with
  | [ Hsitpn: SitpnFullExec _ _ _, Hd: hfullsim _ _ _ _
      |- _ ] =>
    inversion_clear Hsitpn; inversion_clear Hd
  end;
    lazymatch goal with
    | [ Hsimloop: simloop _ _ _ _ _ _ _ |- _ ] =>
        inversion_clear Hsimloop
    end.
  (* CASE τ = 0, GOAL [γ ⊢ s0 ∼ σ0]. Solved with [sim_init_states] lemma. *)
  - constructor; eauto with hilecop.

  (* CASE τ > 0, GOAL [γ ⊢ (s0 :: s :: θ__s) ∼ (σ0 :: σ :: θ0)].   
     Solved with [first_rising_edge], [falling_edge] and [trace_sim] lemmas. *)
    
  - match goal with
    | [ H: simcycle _ _ _ _ _ _ _ _ |- _ ] =>
        inversion_clear H; repeat (constructor; eauto with hilecop)
    end.

Restart.

  (* Version of the proof closer to the paper proof.

     Induction on τ on the second part (no more appealing to lemma
     [trace_sim]), and trying not to use the hilecop hint database. *)
  destruct τ; intros;
  match goal with
  | [ Hsitpn: SitpnFullExec _ _ _, Hd: hfullsim _ _ _ _
      |- _ ] =>
    inversion_clear Hsitpn; inversion_clear Hd
  end;
    lazymatch goal with
    | [ Hsimloop: simloop _ _ _ _ _ _ _ |- _ ] =>
        inversion_clear Hsimloop
    end.

  (* CASE τ = 0, GOAL [ γ ⊢ [s0] ∼ [σ0] ] ⇒ [γ ⊢ s0 ≈ σ0]. 
     Solved with [sim_init_states] lemma. *)
  - eapply FullSimTraceCons; eauto.
    eapply sim_init_states; eauto.

  (* CASE τ > 0, GOAL [γ ⊢ (s0 :: s :: θ__s) ∼ (σ0 :: σ :: θ0)].   
     Solved with [first_rising_edge], [falling_edge] and [trace_sim] lemmas. *)
  - match goal with
    | [ H: simcycle _ _ _ _ _ _ _ _ |- _ ] =>
        inversion_clear H
    end.
    (* SUBGOAL [γ ⊢ s0 ≈ σ0], solved with [sim_init_states]. *)
    constructor. eapply sim_init_states; eauto.
    (* SUBGOAL [γ ⊢ s0 ≈ σ'], solved with [first_rising_edge]. *)
    constructor. eapply first_rising_edge; eauto.
    (* SUBGOAL [γ ⊢ s ≈ σ''], solved with [falling_edge]. *)
    constructor. eapply falling_edge; eauto with hilecop.
    (* SUBGOAL [γ ⊢ θ ∼ θ1], induction on τ *)

    (* Prepares the context and the goal to obtain the wanted
       induction hypothesis. *)
    assert (Hsimfe : FullSimStateAfterFE sitpn γ s σ'') by
      (eauto with hilecop).

    match goal with
    | [
        H0: SitpnStateTransition _ (S τ) _ _ _,
          H1: IsInjectedDState _ (_ (S τ)) _,
            H2: SitpnExecute _ ?s τ ?θ__s,
              H3: simloop _ _ _ ?σ _ τ ?θ__σ,
        H4: FullSimStateAfterFE _ _ ?s ?σ |- _
      ] =>
        clear H0 H1;
        generalize H2 H3 H4; clear H2 H3 H4;
        generalize s θ__s σ θ__σ
    end. 
    (*  *)
    induction τ.
    + (* CASE τ = 0 *)
      intros;
      lazymatch goal with
      | [ Hexec: SitpnExecute _ _ _ _, Hsim: simloop _ _ _ _ _ _ _ |- _ ] =>
        inversion_clear Hexec; inversion_clear Hsim; eauto
      end.
    + (* CASE τ > 0 *)
      intros;
      lazymatch goal with
      | [ Hexec: SitpnExecute _ _ _ _, Hsim: simloop _ _ _ _ _ _ _ |- _ ] =>
        inversion_clear Hexec; inversion_clear Hsim
      end.
      match goal with
      | [ H1: simcycle _ _ _ _ _ _ _ _ |- _ ] =>
        inversion_clear H1
      end.
      constructor. eapply rising_edge; eauto with hilecop.
      constructor. eapply falling_edge; eauto with hilecop.
      (* Apply the induction hypothesis. *)
      eapply IHτ; eauto.
      eapply falling_edge_full; eauto.
      eapply rising_edge_full; eauto.
Qed.
