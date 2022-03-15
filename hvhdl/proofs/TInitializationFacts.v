(** * Facts about Initialization and Transition Design *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.
Require Import common.NatSet.
Require Import common.ListLib.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.proofs.HVhdlCoreFactsLib.
Require Import hvhdl.proofs.HVhdlCoreTacticsLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.proofs.HVhdlSimulationFactsLib.
Require Import hvhdl.proofs.PInitializationFacts.
Require Import hvhdl.proofs.TStabilizeFacts.
Require Import hvhdl.proofs.InitializationTactics.
Require Import hvhdl.proofs.SSEvaluationTactics.
Require Import hvhdl.proofs.ExpressionEvaluationTactics.

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
    match goal with
    | [ H: VExpr _ _ _ _ _ _, H': OVEq _ _ _, H'': MapsTo _ currv _ |- _ ] =>
      inversion H in H'; erewrite <- OVEq_eq_1 with (val2 := currv) in H''; eauto
    end.
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
    match goal with
    | [ H: VExpr _ _ _ _ _ _, H': OVEq _ _ _, H'': MapsTo _ currv _ |- _ ] =>
      inversion H in H'; erewrite <- OVEq_eq_1 with (val2 := currv) in H''; eauto
    end.
  Qed.
  
  Lemma vruninit_T_s_tc_eq_O :    
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

    (* CASE [s_tc ∉ (events σ'0)], then [σ("s_tc") = σ'0("s_tc")] *)
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
        CsHasUniqueCompIds behavior compids ->
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
      eapply vruninit_T_s_tc_eq_O; eauto.
      eapply mapip_not_in_events_if_not_input; eauto.
      destruct 1; unfold DeclaredOf in *; mapsto_discriminate.

    (* CASE eventless component *)
    - inversion 1; subst; subst_transition_design.
      clear IHvruninit; simpl in *.
      erewrite @MapsTo_fun with (e := σ__t') (e' := σ__c); eauto;
        [ | eapply mapop_inv_compstore; eauto].
      (* [events σ__c'' = ∅ then σ__c = σ__c'' ] *)
      (* erewrite mapip_eq_state_if_no_events; eauto; *)
      (*   [ pattern σ__c'; erewrite vruninit_eq_state_if_no_events; eauto *)
      (*   | erewrite @vruninit_eq_state_if_no_events with (σ' := σ__c''); eauto ]. *)
      (* With no events, s_marking ⇐ initial_marking happened,
         but both already had the same value. *)
      (* assert (e : Component Δ__t = Component Δ__c) by (eapply MapsTo_fun; eauto). *)
      (* inject_left e. *)
      (* eapply vruninit_T_s_tc_eq_O; eauto. *)
      (* eapply mapip_not_in_events_if_not_input; eauto. *)
      (* destruct 1; unfold DeclaredOf in *; mapsto_discriminate. *)
      (* erewrite <- @MapsTo_fun with (e := σ__t) (e' := σ__c); eauto. *)
      admit.
      
    (* CASE || *)
    - inversion_clear 1;
        destruct 1 as (ACCI, NoDup_cids);
        destruct (AreCsCompIds_ex cstmt) as (compids1, ACCI1);
        destruct (AreCsCompIds_ex cstmt') as (compids2, ACCI2).
      
      (* SUBCASE [comp ∈ cstmt] *)
      + intros; eapply IHvruninit1; eauto;
          [ split; eauto; solve_nodup_compids_l | solve_vruninit_par_l ].        
      (* SUBCASE [comp ∈ cstmt'] *)
      + intros; eapply IHvruninit2; eauto;
          [ split; eauto; solve_nodup_compids_r | solve_vruninit_par_r ].
  Admitted.

  Lemma vruninit_rtc_ps_assign_s_rtc :
    forall {Δ σ σ'},
      vruninit hdstore Δ σ reinit_time_counter_evaluation_ps σ' ->
      forall t n,
        MapsTo input_arcs_number (Generic t (Vnat n)) Δ ->
        forall aofv b,
          MapsTo Transition.reinit_time (Varr aofv) (sigstore σ) ->
          BProd (get_bool_at aofv) (seq 0 n) b ->
          MapsTo Transition.s_reinit_time_counter (Vbool b) (sigstore σ').
  Admitted.

  Lemma vruninit_inv_if_input :
    forall D__s Δ σ cstmt σ',
      vruninit D__s Δ σ cstmt σ' ->
      forall id, InputOf Δ id ->
                 forall v, MapsTo id v (sigstore σ) <-> MapsTo id v (sigstore σ').
  Admitted.
  
  Lemma vruninit_T_s_rtc_eq_bprod_of_rt :
    forall Δ σ σ',
      vruninit hdstore Δ σ transition_behavior σ' ->
      forall t n,
        MapsTo input_arcs_number (Generic t (Vnat n)) Δ ->
        forall aofv b,
          MapsTo Transition.reinit_time (Varr aofv) (sigstore σ') ->
          BProd (get_bool_at aofv) (seq 0 n) b ->
          MapsTo Transition.s_reinit_time_counter (Vbool b) (sigstore σ').
  Proof.
    intros *; unfold transition_behavior.
    rewrite vruninit_par_comm, <- vruninit_par_assoc,
    vruninit_par_comm, <- vruninit_par_assoc, <- vruninit_par_assoc.
    inversion_clear 1; intros; rename H3 into IMDS.

    (* 2 CASES: [s_rtc ∈ events σ'0] or [s_rtc ∉ events σ'0] *)
    destruct (In_dec s_reinit_time_counter (events σ'0)).
    
    (* CASE [s_rtc ∈ (events σ'0)] *)
    - erw_IMDS_sstore_1 <- IMDS; eauto.
      eapply vruninit_rtc_ps_assign_s_rtc; eauto with set.
      erewrite vruninit_inv_if_input; eauto; admit.
      
    (* CASE [s_rtc ∉ (events σ'0)], then [σ("s_rtc") = σ'0("s_rtc")] *)
    - (* erw_IMDS_sstore_m <- IMDS. *)
      (* eapply vruninit_rtc_ps_no_events_s_rtc; eauto. *)
      (* eapply not_in_union; eauto. *)
      (* eapply vruninit_not_in_events_if_not_assigned; eauto. *)
      (* destruct 1; unfold DeclaredOf in *; mapsto_discriminate. *)
      (* simpl; cbv; lia. *)
      admit.
  Admitted.
                 
  Lemma vruninit_TCI_s_rtc_eq_bprod_of_rt :
    forall Δ σ behavior σ',
      vruninit hdstore Δ σ behavior σ' ->
      forall id__t gm ipm opm compids Δ__t t n,
        InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
        CsHasUniqueCompIds behavior compids ->
        Equal (events σ) {[]} -> 
        MapsTo id__t (Component Δ__t) Δ ->
        MapsTo input_arcs_number (Generic t (Vnat n)) Δ__t ->
        forall σ__t' aofv b,
          MapsTo id__t σ__t' (compstore σ') ->
          MapsTo Transition.reinit_time (Varr aofv) (sigstore σ__t') ->
          BProd (get_bool_at aofv) (seq 0 n) b ->
          MapsTo Transition.s_reinit_time_counter (Vbool b) (sigstore σ__t').
  Proof.
    induction 1; try (solve [inversion 1]).

    (* CASE eventful component *)
    - inversion 1; subst; subst_transition_design.
      clear IHvruninit; simpl in *.
      erewrite @MapsTo_add_eqv with (e' := σ__c'') (e := σ__t') in *; eauto.
      assert (e : Component Δ__t = Component Δ__c) by (eapply MapsTo_fun; eauto).
      inject_left e.
      eapply vruninit_T_s_rtc_eq_bprod_of_rt; eauto.

    (* CASE eventless component *)
    - inversion 1; subst; subst_transition_design.
      clear IHvruninit; simpl in *.

      (* [events σ__c'' = ∅ then σ__c = σ__c'' ] *)
      (* assert (eq_σ : EqDState σ__c σ__c''). *)
      (* { erewrite @mapip_eq_state_if_no_events with (σ__c := σ__c) (σ__c' := σ__c'); eauto. *)
      (*   erewrite @vruninit_eq_state_if_no_events with (σ' := σ__c''); eauto. *)
      (*   reflexivity. *)
      (*   erewrite @vruninit_eq_state_if_no_events with (σ' := σ__c''); eauto. } *)
      (* [σ__c = σ__t'] *)
      (* erewrite @MapsTo_fun with (e := σ__t') (e' := σ__c) in *; eauto; *)
      (*   try (solve [eapply mapop_inv_compstore; eauto | assumption]). *)
      (* pattern σ__c; rewrite eq_σ. *)
      
      (* With no events, [s_rtc ⇐ ∏ rt(i)] happened,
         but both already had the same value. *)
      (* assert (e : Component Δ__t = Component Δ__c) by (eapply MapsTo_fun; eauto). *)
      (* inject_left e. *)
      (* eapply vruninit_T_s_rtc_eq_bprod_of_rt; eauto. *)
      (* pattern σ__c''; rewrite <- eq_σ; assumption. *)
      admit.
      
    (* CASE || *)
    - inversion_clear 1;
        destruct 1 as (ACCI, NoDup_);
        destruct (AreCsCompIds_ex cstmt) as (compids1, ACCI1);
        destruct (AreCsCompIds_ex cstmt') as (compids2, ACCI2).
      
      (* SUBCASE [comp ∈ cstmt] *)
      + intros; eapply IHvruninit1; eauto;
          [ split; eauto; solve_nodup_compids_l | solve_vruninit_par_l ].        
      (* SUBCASE [comp ∈ cstmt'] *)
      + intros; eapply IHvruninit2; eauto;
          [ split; eauto; solve_nodup_compids_r | solve_vruninit_par_r ].    
  Admitted.
  
End TVRunInit.

(** ** Facts about [init] and Transition Design *)

Section TInit.

  Lemma init_s_tc_eq_O :
    forall Δ σ behavior σ0,
      init hdstore Δ σ behavior σ0 ->
      forall id__t gm ipm opm compids Δ__t σ__t σ__t0,
        InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
        CsHasUniqueCompIds behavior compids -> 
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

  Lemma init_TCI_s_rtc_eq_bprod_of_rt :
    forall Δ σ behavior σ0,
      init hdstore Δ σ behavior σ0 ->
      forall id__t gm ipm opm compids Δ__t t n,
        InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
        CsHasUniqueCompIds behavior compids ->
        Equal (events σ) {[]} ->
        MapsTo id__t (Component Δ__t) Δ ->
        MapsTo input_arcs_number (Generic t (Vnat n)) Δ__t ->
        forall σ__t0 aofv b,
          MapsTo id__t σ__t0 (compstore σ0) ->
          MapsTo Transition.reinit_time (Varr aofv) (sigstore σ__t0) ->
          BProd (get_bool_at aofv) (seq 0 n) b ->
          MapsTo Transition.s_reinit_time_counter (Vbool b) (sigstore σ__t0).
  Proof.
    inversion_clear 1.
    intros *; do 5 intro.
    
    eapply stab_TCI_s_rtc_eq_bprod_of_rt; eauto.    
    eapply vruninit_TCI_s_rtc_eq_bprod_of_rt; eauto.
  Qed.

  Lemma init_TCI_eval_rt_0 :
    forall D__s Δ σ behavior σ0,
      init D__s Δ σ behavior σ0 ->
      forall id__t gm ipm opm σ__t0 aofv,
        InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
        MapsTo id__t σ__t0 (compstore σ0) ->
        MapsTo reinit_time (Varr aofv) (sigstore σ__t0) ->
        List.In (associp_ (reinit_time $[[0]]) false) ipm ->
        get_bool_at aofv 0 = false.
  Admitted.

  Lemma init_TCI_eval_rt_i :
    forall D__s Δ σ behavior σ0,
      init D__s Δ σ behavior σ0 ->
      forall id__t gm ipm opm σ__t0 aofv id i b ,
        InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
        MapsTo id__t σ__t0 (compstore σ0) ->
        MapsTo reinit_time (Varr aofv) (sigstore σ__t0) ->
        MapsTo id (Vbool b) (sigstore σ0) ->
        List.In (associp_ (reinit_time $[[ (e_nat i) ]]) (#id)) ipm ->
        get_bool_at aofv i = b.
  Admitted.
  
End TInit.
