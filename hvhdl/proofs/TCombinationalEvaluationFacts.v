(** * Facts about Combinational Evaluation of the Transition Design Behavior *)

Require Import common.CoqLib.
Require Import common.ListLib.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.
Require Import common.NatSet.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.proofs.HVhdlCoreFactsLib.
Require Import hvhdl.proofs.HVhdlCoreTacticsLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.proofs.HVhdlSimulationFactsLib.
Require Import hvhdl.proofs.CombinationalEvaluationTactics.

Lemma vcomb_tc_ps_inv_sstore :
  forall {D__s Δ σ σ' id v},
    vcomb D__s Δ σ time_counter_ps σ' ->
    MapsTo id v (sstore σ) ->
    MapsTo id v (sstore σ').
Proof.
  unfold time_counter_ps.
  inversion 1; auto.
  do 2 (match goal with
        | [ H: VSeq _ _ _ _ _ _ _ _ |- _ ] =>
          inversion H
        end); simpl; auto.
Qed.

Lemma vcomb_tc_ps_no_events :
  forall {D__s Δ σ σ'},
    vcomb D__s Δ σ time_counter_ps σ' ->
    Equal (events σ') {[]}.
Proof.
  unfold time_counter_ps.
  inversion 1; auto; simpl; try reflexivity.
  do 2 (match goal with
        | [ H: VSeq _ _ _ _ _ _ _ _ |- _ ] =>
          inversion H
        end); simpl; auto; try reflexivity.
Qed.

Lemma vcomb_transition_inv_s_tc :
  forall {Δ σ σ' v},
    vcomb hdstore Δ σ transition_behavior σ' ->
    InternalOf Δ s_time_counter ->
    MapsTo s_time_counter v (sstore σ) ->
    MapsTo s_time_counter v (sstore σ').
Proof.
  intros *; unfold transition_behavior.

  (* Put the [time_counter] in head position. *)
  rewrite vcomb_par_comm, <- vcomb_par_assoc.
  do 2 (rewrite vcomb_par_comm, <- vcomb_par_assoc, <- vcomb_par_assoc).
  
  inversion_clear 1; intros DeclOf_.

  (* Use merge state definition *)
  rename H3 into IMDS; erw_IMDS_sstore_m <- IMDS; eauto.
  apply nIn_nIn_Union.

  (* CASE [id ∉ (events σ'0)] *)
  - erewrite vcomb_tc_ps_no_events; eauto with set.

  (* CASE [id ∉ (events σ'')] *)
  - eapply vcomb_not_in_events_if_not_assigned; eauto.
    destruct 1; destruct DeclOf_; mapsto_discriminate.
    simpl; cbv; lia.
Qed.

Lemma vcomb_inv_s_tc :
  forall Δ σ behavior σ',
    vcomb hdstore Δ σ behavior σ' ->
    forall id__t gm ipm opm Δ__t σ__t σ__t' v compids,
      InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
      CsHasUniqueCompIds behavior compids -> 
      MapsTo id__t (Component Δ__t) Δ ->
      InternalOf Δ__t s_time_counter ->
      MapsTo id__t σ__t (cstore σ) ->
      MapsTo s_time_counter v (sstore σ__t) ->
      MapsTo id__t σ__t' (cstore σ') ->
      MapsTo s_time_counter v (sstore σ__t').
Proof.
  induction 1; try (solve [inversion 1]).

  (* CASE component with events. *)
  - inversion 1.
    cbn; subst; subst_transition_design.
    erewrite @MapsTo_add_eqv with (e' := σ__c'') (e := σ__t'); eauto.
    erewrite @MapsTo_fun with (x := id__c) (e := σ__t) (e' := σ__c) in *; eauto.
    assert (e : Component Δ__t = Component Δ__c) by (eapply MapsTo_fun; eauto).
    inject_left e; eauto.
    eapply vcomb_transition_inv_s_tc; eauto.
    eapply MIP_inv_sstore; eauto.
    unfold InputOf; destruct 1; unfold InternalOf in *.
    mapsto_discriminate.
    
  (* CASE component with no events. *)
  - inversion 1.
    intros; erewrite @MapsTo_fun with (e := σ__t') (e' := σ__t); eauto.
    eapply MOP_inv_cstore; eauto.

  (* CASE || *)
  - inversion_clear 1;
      destruct 1 as (ACCI, NoDup_);
      destruct (AreCsCompIds_ex cstmt) as (compids1, ACCI1);
      destruct (AreCsCompIds_ex cstmt') as (compids2, ACCI2);
      intros.
    eapply IHvcomb1; eauto; [ split; eauto; solve_nodup_compids_l | solve_vcomb_par_l ].
    eapply IHvcomb2; eauto; [ split; eauto; solve_nodup_compids_r | solve_vcomb_par_r ].
Qed.
