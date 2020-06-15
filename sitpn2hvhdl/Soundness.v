(** * Semantic Preservation Theorem *)

Require Import GlobalTypes.

(* SITPN Libraries *)

Require Import SitpnTypes.
Require Import Sitpn.
Require Import dp.SitpnSemantics.

(* H-VHDL Libraries *)

Require Import HVhdlTypes.
Require Import Environment.
Require Import SemanticalDomains.
Require Import Simulation.
Require Import SimulationFacts.
Require Import DesignElaboration.
Require Import AbstractSyntax.
Require Import HilecopDesignStore.
Require Import Initialization.

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

Definition EnvEq sitpn (Ec : nat -> C sitpn -> bool) (Ep : nat -> Clk -> IdMap value) : Prop := True.

(** Defines the state similarity relation between an SITPN state and
    a H-VHDL design state.
 *)

Definition SimState {sitpn} (s : SitpnState sitpn) (dstate : DState) : Prop := False.

(** ** Simulation Lemma *)

Lemma simulation_lemma :
  forall sitpn Ec s1 s2 tau,

    (* From state s1 to state s2 after tau execution cycles. *)
    SitpnExecute Ec s1 tau s2 ->

    forall  Mg d Ep dstate1 dstate2 ed dstate mm,
      
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Environments are similar. *)
    EnvEq sitpn Ec Ep ->

    (* ed, dstate are the results of the elaboration of d. *)
    edesign hdstore Mg d ed dstate ->

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
  - apply simloop_eqstate_at_0 in Hsim; rewrite <- Hsim; assumption.

  (* CASE tau > 0 *)
  -
    (* Adds premises of simloop relation in the context (using a lemma
       instead of inversion). *)
    match goal with
    | [ H: tau > 0 |- _ ] => 
      specialize (simloop_tau_gt0 Ep ed dstate1 (get_behavior d) dstate2 tau H Hsim) as Hex;
        inversion_clear Hex as (dstate' & Hcyc & Hsim')
    end.

    (* Specializes the induction hypothesis, then apply the step lemma. *)
    specialize (IHHexec Mg d Ep dstate' dstate2 ed dstate mm Htransl Henveq Helab).
    
Admitted.

(** ** Equal Initial States  *)

Lemma init_states_sim :
  forall sitpn mm d Mg ed dstate dstate0,
    
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* ed, dstate are the results of the elaboration of d. *)
    edesign hdstore Mg d ed dstate ->

    (* initialization d's state. *)
    init ed dstate (get_behavior d) dstate0 ->

    (* init states are similar *)
    SimState (s0 sitpn) dstate0.
Proof.
Admitted.
  
(** ** Semantic Preservation Theorem *)

Theorem sitpn2vhdl_sound :
  forall sitpn Ec tau s d Mg Ep dstate mm,

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Environments are similar. *)
    EnvEq sitpn Ec Ep ->      

    (* sitpn is in state s after tau execution cycles. *)
    SitpnExecute Ec (s0 sitpn) tau s ->
    
    (* d is in state dstate after tau execution cycles. *)
    simwf hdstore Mg Ep tau d dstate ->

    (* ** Conclusion: final states are equal. ** *)
    SimState s dstate.
Proof.
  inversion_clear 4.
  specialize (init_states_sim sitpn mm d Mg ed dstate0 dstate1 H H3 H4) as Hinit_eq.
  apply (simulation_lemma sitpn d Ep Ec Mg (s0 sitpn) s dstate1 dstate ed dstate0 tau mm H H0 H3 Hinit_eq H1 H5).
Qed.
