(** * Facts about Initialization and Transition Design *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.NatMapTactics.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.HVhdlSimulationFactsLib.
Require Import hvhdl.PInitializationFacts.
Require Import hvhdl.TStabilizeFacts.
Require Import hvhdl.InitializationTactics.
Require Import hvhdl.SSEvaluationTactics.
Require Import hvhdl.ExpressionEvaluationTactics.

(** ** Facts about [vruninit] and Place Design *)

Section TVRunInit.

  Lemma vruninit_tc_ps_assign_s_tc :
    forall {Δ σ σ'},
      vruninit hdstore Δ σ time_counter_ps σ' ->
      MapsTo s_time_counter (Vnat 0) (sigstore σ').
  Proof.
    inversion_clear 1; intros.
    vseqinv_cl; [contradiction | ].
    vseqinv_cl; subst; cbn.
    vexprinv_cl; eauto with mapsto.
    inversion H0 in H5.
    erewrite <- OVEq_eq_1 with (val2 := currv) in H4; eauto.
  Qed.

  Lemma vruninit_tc_ps_no_events_s_tc :
    forall {Δ σ σ'},
      vruninit hdstore Δ σ time_counter_ps σ' ->
      ~NatSet.In s_time_counter (events σ') ->
      MapsTo s_time_counter (Vnat 0) (sigstore σ).
  Proof.
    inversion_clear 1; intros.
    vseqinv_cl; [contradiction | ].
    vseqinv_cl; subst; cbn.
    cbn in H; contrad_not_in_add.
    inversion H0 in H6.
    erewrite <- OVEq_eq_1 with (val2 := currv) in H5; eauto.
  Qed.
  
  Lemma vruninit_transition_s_tc_eq_O :    
    forall Δ σ σ',
      vruninit hdstore Δ σ transition_behavior σ' ->
      ~NatSet.In s_time_counter (events σ) ->
      DeclaredOf Δ s_time_counter ->
      MapsTo s_time_counter (Vnat 0) (sigstore σ').
  Proof.
    intros *; unfold transition_behavior.
    rewrite vruninit_par_comm, <- vruninit_par_assoc.
    do 2 (rewrite vruninit_par_comm,
          <- vruninit_par_assoc,
          <- vruninit_par_assoc).
    inversion_clear 1; intros; rename H3 into IMDS.

    (* 2 CASES: [s_tc ∈ events σ'0] or [s_tc ∉ events σ'0] *)
    destruct (In_dec s_time_counter (events σ'0)).
    
    (* CASE [s_tc ∈ (events σ'0)] *)
    - erw_IMDS_sstore_1 <- IMDS; eauto.
      eapply vruninit_tc_ps_assign_s_tc; eauto with set.

    (* CASE [s_marking ∉ (events σ'0)], 
       then [σ("s_tc") = σ'0("s_tc")] *)
    - erw_IMDS_sstore_m <- IMDS.
      eapply vruninit_tc_ps_no_events_s_tc; eauto.
      eapply not_in_union; eauto.
      eapply vruninit_not_in_events_if_not_assigned; eauto.
      destruct 1; unfold DeclaredOf in *; mapsto_discriminate.
      simpl; cbv; lia.
  Qed.
  
  Lemma vruninit_s_tc_eq_O :
    forall Δ σ behavior σ',
      vruninit hdstore Δ σ behavior σ' ->
      forall id__t gm ipm opm σ__t' compids Δ__t σ__t,
        InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
        AreCsCompIds behavior compids -> 
        List.NoDup compids ->
        Equal (events σ) {[]} ->
        MapsTo id__t (Component Δ__t) Δ ->
        DeclaredOf Δ__t s_time_counter ->
        MapsTo id__t σ__t (compstore σ) ->
        ~NatSet.In s_time_counter (events σ__t) ->
        NatMap.MapsTo id__t σ__t' (compstore σ') ->
        NatMap.MapsTo s_time_counter (Vnat 0) (sigstore σ__t').
  Proof.
    induction 1; try (solve [inversion 1]).

    (* CASE eventful component *)
    - inversion 1; subst; subst_transition_design.
      clear IHvruninit; simpl in *.
      erewrite @MapsTo_fun with (e' := σ__c) (e := σ__t) in *; eauto.
      erewrite @MapsTo_add_eqv with (e' := σ__c'') (e := σ__t'); eauto.
      assert (e : Component Δ__t = Component Δ__c) by (eapply MapsTo_fun; eauto).
      inject_left e.
      eapply vruninit_transition_s_tc_eq_O; eauto.
      eapply mapip_not_in_events_if_not_input; eauto.
      destruct 1; unfold DeclaredOf in *; mapsto_discriminate.

    (* CASE eventless component *)
    - inversion 1; subst; subst_transition_design.
      clear IHvruninit; simpl in *.
      erewrite @MapsTo_fun with (e := σ__t') (e' := σ__c); eauto;
        [ | eapply mapop_inv_compstore; eauto].
      (* [events σ__c'' = ∅ then σ__c = σ__c'' ] *)
      erewrite mapip_eq_state_if_no_events; eauto;
        [ pattern σ__c'; erewrite vruninit_eq_state_if_no_events; eauto
        | erewrite @vruninit_eq_state_if_no_events with (σ' := σ__c''); eauto ].
      (* With no events, s_marking ⇐ initial_marking happened,
         but both already had the same value. *)
      assert (e : Component Δ__t = Component Δ__c) by (eapply MapsTo_fun; eauto).
      inject_left e.
      eapply vruninit_transition_s_tc_eq_O; eauto.
      eapply mapip_not_in_events_if_not_input; eauto.
      destruct 1; unfold DeclaredOf in *; mapsto_discriminate.
      erewrite <- @MapsTo_fun with (e := σ__t) (e' := σ__c); eauto.

    (* CASE || *)
    - inversion_clear 1;
        destruct (AreCsCompIds_ex cstmt) as (compids1, HAreCsCompIds1);
        destruct (AreCsCompIds_ex cstmt') as (compids2, HAreCsCompIds2).
      
      (* SUBCASE [comp ∈ cstmt] *)
      + intros; eapply IHvruninit1; eauto; [ solve_nodup_compids_l | solve_vruninit_par_l ].        
      (* SUBCASE [comp ∈ cstmt'] *)
      + intros; eapply IHvruninit2; eauto; [ solve_nodup_compids_r | solve_vruninit_par_r ].
  Qed.
  
End TVRunInit.

(** ** Facts about [init] and Transition Design *)

Section TInit.

  Lemma init_s_tc_eq_O :
    forall Δ σ behavior σ0,
      init hdstore Δ σ behavior σ0 ->
      forall id__t gm ipm opm compids Δ__t σ__t σ__t0,
        InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
        AreCsCompIds behavior compids -> 
        List.NoDup compids ->
        Equal (events σ) {[]} ->
        MapsTo id__t (Component Δ__t) Δ ->
        DeclaredOf Δ__t s_time_counter ->
        MapsTo id__t σ__t (compstore σ) ->
        ~NatSet.In s_time_counter (events σ__t) ->
        MapsTo id__t σ__t0 (compstore σ0) ->
        MapsTo Transition.s_time_counter (Vnat 0) (sigstore σ__t0).
  Proof.
    inversion_clear 1.
    intros *; intros.

    (* Builds [σ'(id__t) = σ'__t] *)
    edestruct (@vruninit_maps_compstore_id hdstore) as (σ'__t, MapsTo_cstore');
      eauto.
    
    (* [s_tc] value stays the same during stabilization. *)
    eapply stab_inv_s_tc; eauto.    

    (* [s_tc] takes [0] during [vruninit]. *)
    eapply vruninit_s_tc_eq_O; eauto.    
  Qed.

  Lemma init_s_rtc_eq_bprod_of_rt :
    forall Δ σ behavior σ0,
      init hdstore Δ σ behavior σ0 ->
      forall id__t gm ipm opm compids Δ__t σ__t σ__t0 b aofv,
        InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
        CsHasUniqueCompIds behavior compids ->
        Equal (events σ) {[]} ->
        MapsTo id__t (Component Δ__t) Δ ->
        MapsTo id__t σ__t (compstore σ) ->
        MapsTo id__t σ__t0 (compstore σ0) ->
        DeclaredOf Δ__t s_reinit_time_counter ->
        ~NatSet.In s_reinit_time_counter (events σ__t) ->
        MapsTo Transition.reinit_time (Varr aofv) (sigstore σ__t0) ->
        BProd_ArrOfV aofv b ->
        MapsTo Transition.s_reinit_time_counter (Vbool b) (sigstore σ__t0).
  Admitted.

  
End TInit.
