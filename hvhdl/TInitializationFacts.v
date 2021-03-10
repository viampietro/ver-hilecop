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

(** ** Facts about [vruninit] and Place Design *)

Section TVRunInit.

  Lemma vruninit_transition_s_tc_eq_O :    
    forall Δ σ σ',
      vruninit hdstore Δ σ transition_behavior σ' ->
      ~NatSet.In s_time_counter (events σ) ->
      DeclaredOf Δ s_time_counter ->
      MapsTo s_time_counter (Vnat 0) (sigstore σ').
  Admitted.
  
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
  
End TInit.
