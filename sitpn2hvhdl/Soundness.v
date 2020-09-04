(** * Semantic Preservation Theorem *)

Require Import GlobalTypes.

(* SITPN Libraries *)

Require Import dp.SitpnTypes.
Require Import dp.Sitpn.
Require Import dp.SitpnSemantics.
Require Import dp.Fired.

(* H-VHDL Libraries *)

Require Import HVhdlTypes.
Require Import Environment.
Require Import SemanticalDomains.
Require Import Simulation.
Require Import CombinationalEvaluation.
Require Import SynchronousEvaluation.
Require Import DesignElaboration.
Require Import AbstractSyntax.
Require Import HilecopDesignStore.
Require Import Initialization.
Require Import Stabilize.

(* SITPN to H-VHDL Libraries *)

Require Import GenerateHVhdl.

(* Specific Tactics. *)

Require Import Coq.Program.Equality.

(** Defines the relation stating that an SITPN execution environment
    and a H-VHDL design execution environment described the same
    behavior.

    - The environment [Ec] provides boolean values to the conditions
    of [sitpn] depending on the cycle count [tau] 
    
    - The environment [Ep] provides values (must be boolean) to the input
    ports of design [d] that implements the conditions of [sitpn].
*)

Definition EnvEq sitpn (Ec : nat -> C sitpn -> bool) (Ep : nat -> Clk -> IdMap value) : Prop := False.

(** Defines the state similarity relation between an SITPN state and
    a H-VHDL design state.
 *)

Definition SimState {sitpn} (s : SitpnState sitpn) (σ : DState) : Prop := False.
Local Notation "s '∼' σ" := (SimState s σ) (at level 50).

(** States that two execution trace are similar. The first list
    argument is the execution trace of an SITPN and the second list
    argument is the execution trace of a VHDL design.
    
    By construction, and in order to be similar, the two traces must
    have the same length, and must have pair-wise similar states. *)

Inductive SimTrace {sitpn} : list (SitpnState sitpn) -> list DState -> Prop :=
| SimTraceInit: SimTrace nil nil
| SimTraceCons: forall s σ θ__s θ__σ,
    s ∼ σ ->
    SimTrace θ__s θ__σ ->
    SimTrace (s :: θ__s) (σ :: θ__σ).

(** ** Step lemma
    
    States that starting from similar state, state are similar after
    one execution cycle.

 *)

Lemma step_lemma :
  forall sitpn mm d s s' E__c σ σ' Δ Mg σ__e P__i τ,
    
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Starting states are similar *)
    s ∼ σ ->

    (* Δ, σ are the results of the elaboration of d. *)
    edesign hdstore Mg d Δ σ__e ->
    
    (* One execution cycle for SITPN *)
    
    @SitpnCycle sitpn E__c τ s s' ->

    (* One execution cycle for VHDL *)
    simcycle P__i Δ τ σ (get_behavior d) σ' ->
     
    (* Final states are similar *)
    s' ∼ σ'.
Proof.
  
Admitted.

(** ** Equal Initial States  *)

Lemma init_states_sim :
  forall sitpn mm d Mg Δ σ__e σ0,
    
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* ed, dstate are the results of the elaboration of d. *)
    edesign hdstore Mg d Δ σ__e ->

    (* initialization d's state. *)
    init Δ σ__e (get_behavior d) σ0 ->

    (* init states are similar *)
    (s0 sitpn) ∼ σ0.
Proof.
Admitted.

(** ** Simulation Lemma *)

Lemma simulation_lemma :
  
  forall sitpn Ec τ s θ__s s',

    (* From state s to state s' after τ execution cycles, and
       producing trace θs. *)
    SitpnExecute Ec s τ θ__s s' ->

    forall d mm Ep Mg Δ σ__e θ__σ σ σ',
      
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Environments are similar. *)
    EnvEq sitpn Ec Ep ->

    (* Δ, σe are the results of the elaboration of d. *)
    edesign hdstore Mg d Δ σ__e ->

    (* States s and σ are similar; *)
    s ∼ σ ->
    
    (* From σ to σ' after τ execution cycles, producing trace θσ. *)
    simloop Ep Δ σ (get_behavior d) τ θ__σ σ' ->

    (* Conclusion *)
    SimTrace θ__s θ__σ.
Proof.
  intros *; intros Hexec; dependent induction Hexec;
  intros *; intros Htransl Henveq Helab Hsimstate Hsim.
  
  (* CASE tau = 0, trivial. *)
  - inversion Hsim; apply SimTraceInit.

  (* CASE tau > 0 *)
  - inversion_clear Hsim as [ τ0 σ0 σ'0 θ0 Hcyc Hsiml |  ].
    
    (* Specializes the induction hypothesis, then apply the step lemma. *)
    
    specialize (IHHexec d mm Ep Mg Δ σ__e θ0 σ0 σ').
    specialize (IHHexec Htransl Henveq Helab).

    (* Then, we need a lemma stating that s' ∼ σ0. That is, state are
       similar after one execution cycle. *)

    specialize (step_lemma sitpn mm d s s' Ec σ σ0 Δ Mg σ__e Ep (S tau)
                           Htransl Hsimstate Helab H Hcyc)
      as Heq_state_cyc.

    (* Solve the induction case. *)
    apply SimTraceCons; [ assumption | apply (IHHexec Heq_state_cyc Hsiml)].
Qed.

(** ** Semantic Preservation Theorem *)

Theorem sitpn2vhdl_sound :
  forall sitpn E__c τ θ__s s' d Mg E__p σ' mm Δ σ__e σ0 θ__σ,
      
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* (* Environments are similar. *) *)
    EnvEq sitpn E__c E__p ->

    (* sitpn is in state s' after τ execution cycles and yields
       exec. trace θs. *)
    
    SitpnExecute E__c (s0 sitpn) τ θ__s s' ->    
    
    (* Design elaboration *)
    edesign hdstore Mg d Δ σ__e ->
    
    (* Initialization of design state *)
    init Δ σ__e (get_behavior d) σ0 ->

    (* Simulation of design *)
    simloop E__p Δ σ0 (get_behavior d) τ θ__σ σ' ->
    
    (* ** Conclusion: exec. traces are equal. ** *)
    SimTrace θ__s θ__σ.
Proof.
  intros.

  lazymatch goal with
  | [
    Htransl: sitpn_to_hvhdl _ _ = Success _,
    Henveq: EnvEq _ _ _,
    Hsitpnexec: SitpnExecute _ _ _ _ _,
    Helab: edesign _ _ _ _ _,
    Hinit: init _ _ _ _,
    Hsimloop: simloop _ _ _ _ _ _ _
    |- _ ] =>
    specialize (init_states_sim sitpn mm d Mg Δ σ__e σ0 Htransl Helab Hinit) as Hinit_eq;
      apply (simulation_lemma sitpn E__c τ (s0 sitpn) θ__s s' Hsitpnexec
                              d mm E__p Mg Δ σ__e θ__σ σ0 σ'
                              Htransl Henveq Helab Hinit_eq Hsimloop)
  end.

Qed.
    
Lemma falling_edge_compute_fired :
  forall Δ σ__f d θ σ' σ sitpn Ec τ s s' mm γ id__t σ'__t,

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Similar starting states *)
    s ∼ σ ->

    (* Falling edge from s to s' *)
    SitpnStateTransition Ec τ s s' falling_edge ->

    (* Falling edge from σ to σf *)
    vfalling Δ σ (get_behavior d) σ__f ->

    (* Stabilize from σf to σ' *)
    stabilize Δ σ__f (get_behavior d) θ σ' ->
    
    (* Conclusion *)
    forall flist t,
      (** Component idt implements transition t *)
      γ t = id__t ->

      (* σ't is the state of component idt at design's state σ'. *)
      MapsTo id__t σ'__t (compstore σ') ->

      (* Conclusion *)
      @Fired sitpn s' flist t ->
      MapsTo Transition.fired (Vbool true) (sigstore σ'__t).
Proof.
  intros.
  unfold Fired in H6.
  inversion H6.
  inversion H7.
  inversion H10.
  - admit.
  -

Admitted.  
