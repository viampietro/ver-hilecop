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

(** ** Simulation Lemma *)

Lemma simulation_lemma :
  forall sitpn Ec s1 s2 tau,

    (* From state s1 to state s2 after tau execution cycles. *)
    SitpnExecute Ec s1 tau s2 ->

    forall  Mg d Ep dstate1 dstate2 ed dstatee mm,
      
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Environments are similar. *)
    EnvEq sitpn Ec Ep ->

    (* ed, dstate are the results of the elaboration of d. *)
    edesign hdstore Mg d ed dstatee ->

    (* States s1 and dstate1 are similar; *)
    SimState s1 dstate1 ->
    
    (* From dstate1 to dstate2 after tau execution cycles. *)
    simloop Ep ed dstate1 (get_behavior d) tau dstate2 ->

    (* Conclusion *)
    SimState s2 dstate2.
Proof.
  intros *; intros Hexec; dependent induction Hexec;
    intros *; intros Htransl Henveq Helab Hsimstate Hsim.
  
  (* CASE tau = 0, trivial. *)
  - inversion Hsim. rewrite <- H0; assumption.

  (* CASE tau > 0 *)
  - inversion_clear Hsim as [ tau0 dstate' dstate'' Hcyc Hsiml Heqtau Heqdstate |  ].
    (* Specializes the induction hypothesis, then apply the step lemma. *)
    specialize (IHHexec Mg d Ep dstate' dstate2 ed dstatee mm Htransl Henveq Helab).
    
Admitted.

(** ** Equal Initial States  *)

Lemma init_states_sim :
  forall sitpn mm d Mg ed dstatee dstate0,
    
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* ed, dstate are the results of the elaboration of d. *)
    edesign hdstore Mg d ed dstatee ->

    (* initialization d's state. *)
    init ed dstatee (get_behavior d) dstate0 ->

    (* init states are similar *)
    SimState (s0 sitpn) dstate0.
Proof.
Admitted.
  
(** ** Semantic Preservation Theorem *)

Theorem sitpn2vhdl_sound :
  forall sitpn Ec τ s' d Mg Ep σ' mm,

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Environments are similar. *)
    EnvEq sitpn Ec Ep ->      

    (* sitpn is in state s after \tau execution cycles. *)
    SitpnExecute Ec (s0 sitpn) τ s' ->
    
    (* d is in state dstate after \tau execution cycles. *)
    simwf hdstore Mg Ep τ d σ' ->

    (* ** Conclusion: final states are equal. ** *)
    SimState s' σ'.
Proof.
  inversion_clear 4.

  lazymatch goal with
  | [
    Htransl: sitpn_to_hvhdl _ _ = _,
    Henveq: EnvEq _ _ _,
    Hsitpnexec: SitpnExecute _ _ _ _,
    Helab: edesign _ _ _ _ _,
    Hinit: init _ _ _ _,
    Hsimloop: simloop _ _ _ _ _ _
    |- _ ] =>
    specialize (init_states_sim sitpn mm d Mg ed dstatee dstate0 Htransl Helab Hinit) as Hinit_eq; 
      apply (simulation_lemma sitpn Ec (s0 sitpn) s' τ Hsitpnexec 
                              Mg d Ep dstate0 σ' ed dstatee mm
                              Htransl Henveq Helab Hinit_eq Hsimloop)
  end.

Qed.

Lemma falling_edge_compute_fired :
  forall Δ σ__f d σ' σ sitpn Ec τ s s' mm γ id__t σ'__t,

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Similar starting states *)
    s ∼ σ ->

    (* Falling edge from s to s' *)
    SitpnStateTransition Ec τ s s' falling_edge ->

    (* Falling edge from σ to σf *)
    vfalling Δ σ (get_behavior d) σ__f ->

    (* Stabilize from σf to σ' *)
    stabilize Δ σ__f (get_behavior d) σ' ->
    
    (* Conclusion *)
    forall t,
      (** Component idt implements transition t *)
      γ t = id__t ->

      (* σ't is the state of component idt at design's state σ'. *)
      MapsTo id__t σ'__t (compstore σ') ->

      (* Conclusion *)
      @Fired sitpn s' t ->
      MapsTo Transition.fired (Vbool true) (sigstore σ'__t).
Proof.
  inversion 5.
  - admit.
  -
Admitted.  
