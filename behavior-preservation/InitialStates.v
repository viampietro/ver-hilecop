(** * Similar Initial States *)

Require Import String.
Require Import common.CoqLib.
(* Require Import common.proofs.CoqTactics. *)
Require Import common.GlobalTypes.
Require Import common.GlobalFacts.
Require Import common.NatMap.
Require Import common.ListLib.
Require Import common.StateAndErrorMonad.
Require Import common.proofs.StateAndErrorMonadTactics.

Require Import sitpn.SitpnLib.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.proofs.WellDefinedDesignFacts.
(* Require Import hvhdl.proofs.HVhdlCoreFactsLib. *)
(* Require Import hvhdl.proofs.HVhdlCoreTacticsLib. *)
(* Require Import hvhdl.proofs.HVhdlElaborationFactsLib. *)
(* Require Import hvhdl.HVhdlHilecopFactsLib. *)
(* Require Import hvhdl.proofs.HVhdlSimulationFactsLib. *)

(* Require Import hvhdl.proofs.DesignElaborationFacts. *)
(* Require Import hvhdl.proofs.PElaborationFacts. *)
(* Require Import hvhdl.proofs.PInitializationFacts. *)

Require Import transformation.Sitpn2HVhdl.
Require Import transformation.proofs.GenerateHVhdlFacts.
Require Import transformation.proofs.GenerateInfosFacts.

Require Import soundness.SemanticPreservationDefs.

(** ** Initial States Equal Marking Lemma *)    

Lemma init_states_eq_marking :
  forall sitpn b d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    Init hdstore Δ σ__e (AbstractSyntax.beh d) σ0 ->

    forall p id__p σ__p0,
      (* [id__p] is the identifier of the place component associated with
         place [p] by the [γ] binder. *)
      InA Pkeq (p, id__p) (p2pdi γ) ->

      (* [σ__p] is the current state of component [id__p] is the global
         design state [σ]. *)
      MapsTo id__p σ__p0 (cstore σ0) ->

      (* Marking of place [p] at state [s] equals value of signal
         [s_marking] at state [σ__p]. *)
      MapsTo Place.s_marking (Vnat (M (s0 sitpn) p)) (sstore σ__p0).
Proof.
  intros.

  (* Builds the premises of the [init_s_marking_eq_nat] lemma. *)
  
  (* Builds [comp(id__p', "place", g__p, i__p, o__p) ∈ (behavior d)] *)
  edestruct @sitpn2hvhdl_pdi_ex with (sitpn := sitpn) (p := p)
    as (id__p', (g__p, (i__p, (o__p, (Hγ, Hincs_comp))))); eauto.
  
  (* Builds [compids] and [AreCsCompIds (behavior d) compids] *)
  (* destruct (AreCsCompIds_ex (AbstractSyntax.beh d)) as (compids, HAreCsCompIds). *)

  (* Builds [id__p' ∈ Comps(Δ)] *)
  (* edestruct @elab_compid_in_comps with (D__s := hdstore) as (Δ__p, MapsTo_Δ__p); eauto. *)

  (* (* Builds [id__p' ∈ (cstore σ__e)] *) *)
  (* edestruct @elab_compid_in_cstore with (D__s := hdstore) as (σ__pe, MapsTo_σ__pe); eauto. *)

  (* (* Builds [Δ__p("s_marking") = Internal (Tnat 0 n)] *) *)
  (* edestruct @elab_PDI_Δ_s_marking as (n, MapsTo_smarking); eauto. *)

  (* (* Builds proof that [ipm] is well-formed *) *)
  (* edestruct @elab_ValidIPM as (formals, (ListIPM_ipm, CheckFormals_ipm)); eauto. *)
  
  (* To prove [σ__p0("s_marking") = M0(p)] *)
  eapply init_s_marking_eq_nat; eauto.
  
  (* (* 6 subgoals left. *) *)

  (* (* Proves [(events σ__e) = ∅] *) *)
  (* - eapply elab_empty_events; eauto. *)
    
  (* (* Proves [NoDup compids] *) *)
  (* - eapply elab_nodup_compids; eauto. *)
    
  (* (* Proves [<initial_marking => M0(p)> ∈ ipm] *) *)
  (* - eapply sitpn2hvhdl_bind_init_marking; eauto. *)

  (* (* Proves [initial_marking ∈ Ins(Δ__p) *) *)
  (* - eapply elab_PDI_Δ_init_marking; eauto. *)
    
  (* (* Proves [id__p = id__p'] *) *)
  (* - erewrite NoDupA_fs_eqk_eq with (eqk := @Peq sitpn) (b := id__p'); eauto. *)
  (*   eapply sitpn2hvhdl_nodup_p2pdi; eauto. *)

  (* (* Proves [s_marking ∉ (events σ__pe)] *) *)
  (* - erewrite elab_empty_events_for_comps; eauto with set. *)
Admitted.

(** ** Initial States Equal Time Counters *)

Lemma init_states_eq_time_counters :
  forall sitpn b d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    Init hdstore Δ σ__e (AbstractSyntax.beh d) σ0 ->
    
    forall (t : Ti sitpn) (id__t : ident) (σ__t0 : DState),
      InA Tkeq (proj1_sig t, id__t) (t2tdi γ) ->
      MapsTo id__t σ__t0 (cstore σ0) ->
      (upper t = i+ /\ TcLeLower (s0 sitpn) t -> MapsTo Transition.s_time_counter (Vnat (I (s0 sitpn) t)) (sstore σ__t0)) /\
      (upper t = i+ /\ TcGtLower (s0 sitpn) t -> MapsTo Transition.s_time_counter (Vnat (lower t)) (sstore σ__t0)) /\
      (forall pf : upper t <> i+, TcGtUpper (s0 sitpn) t ->
                   MapsTo Transition.s_time_counter (Vnat (natinf_to_natstar (upper t) pf)) (sstore σ__t0)) /\
      (upper t <> i+ /\ TcLeUpper (s0 sitpn) t -> MapsTo Transition.s_time_counter (Vnat (I (s0 sitpn) t)) (sstore σ__t0)).
Proof.
  (* intros *; intros IWD e Helab Hinit; intros t id__t σ__t0; intros InA_γ Mapsto_σ0. *)
  (* cbn; split_and. *)
  
  (* (* CASE [upper(I__s(t)) = ∞ and s0.I(t) ≤ lower(I__s(t))]  *)
  (*    and [upper(I__s(t)) ≠ ∞ and s0.I(t) ≤ upper(I__s(t))] *) *)
  (* 1,4 : *)
  (*   intros; *)

  (*   (* Builds the premises of the [init_s_tc_eq_O] lemma. *) *)
    
  (*   (* Builds [comp(id__t', "transition", gm, ipm, opm) ∈ (behavior d)] *) *)
  (*   edestruct @sitpn2hvhdl_t_comp with (sitpn := sitpn) (t := proj1_sig t) *)
  (*   as (id__t', (gm, (ipm, (opm, (InA_t2tdi, InCs_t))))); eauto; *)

  (*     (* Builds [compids] and [AreCsCompIds (behavior d) compids] *) *)
  (*     destruct (AreCsCompIds_ex (behavior d)) as (compids, AreCsCompIds_); *)
      
  (*     (* Builds [id__t' ∈ (cstore σ__e)] *) *)
  (*     edestruct @elab_compid_in_cstore with (D__s := hdstore) as (σ__te, MapsTo_σ__te); eauto; *)

  (*       (* Builds [id__t' ∈ Comps(Δ)] *) *)
  (*       edestruct @elab_compid_in_comps with (D__s := hdstore) as (Δ__t, MapsTo_Δ__t); eauto; *)
          
  (*         (* To prove [σ__t0("s_tc") = 0] *) *)
  (*         eapply init_s_tc_eq_O; eauto; *)
  (*           [(* 5 SUBGOALS left *) *)

  (*             (* Proves [CsHasUniqueCompIds (behavior d) compids] *) *)
  (*             split; eauto; eapply elab_nodup_compids; eauto *)
  (*           | *)
  (*           (* Proves [(events σ__e) = ∅] *) *)
  (*           eapply elab_empty_events; eauto *)
  (*           | *)
  (*           (* Proves [InternalOf Δ__t "s_tc"] *) *)
  (*           eapply @elab_TDI_Δ_s_tc; eauto *)
  (*           | *)
  (*           (* Proves ["s_tc" ∉ (events σ__te)] *) *)
  (*           erewrite elab_empty_events_for_comps; eauto with set *)
  (*           | *)
  (*           (* Proves [id__t = id__t'] *) *)
  (*           erewrite NoDupA_fs_eqk_eq with (eqk := Teq) (b := id__t'); eauto; *)
  (*           eapply sitpn2hvhdl_nodup_t2tdi; eauto ]. *)
  
  (* (* CASE [upper(I__s(t)) = ∞ and s0.I(t) > lower(I__s(t))] *) *)
  (* - destruct 1 as (upper_, TcGtLower_). *)
  (*   unfold TcGtLower in TcGtLower_. *)
  (*   destruct t in TcGtLower_; cbn in TcGtLower_. *)
  (*   destruct (Is x). *)
  (*   destruct (a t0). *)
  (*   cbn in TcGtLower_; lia. *)
  (*   contradiction. *)
    
  (* (* CASE [upper(I__s(t)) ≠ ∞ and s0.I(t) > upper(I__s(t))] *) *)
  (* - intros upper_ TcGtUpper_. *)
  (*   unfold TcGtUpper in TcGtUpper_; cbn in TcGtUpper_. *)
  (*   destruct t in TcGtUpper_. *)
  (*   destruct (Is x). *)
  (*   destruct (b t0) in TcGtUpper_; cbn in TcGtUpper_; lia. *)
  (*   contradiction. *)
Admitted.

Lemma init_states_eq_reset_orders :
  forall sitpn b d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    Init hdstore Δ σ__e (AbstractSyntax.beh d) σ0 ->
    
    (forall (t : Ti sitpn) (id__t : ident) (σ__t0 : DState),
        InA Tkeq (proj1_sig t, id__t) (t2tdi γ) ->
        MapsTo id__t σ__t0 (cstore σ0) ->
        MapsTo Transition.s_reinit_time_counter (Vbool (reset (s0 sitpn) t)) (sstore σ__t0)).
Proof.
  (* intros *; intros IWD e elab_ init_ t id__t σ__t0; intros. *)
  (* cbn; unfold nullb. *)

  (* (* APPLY [init_rtc_eq_bprod_of_rt] lemma. *) *)

  (* (* Building premises of [init_rtc_eq_bprod_of_rt] lemma. *) *)
  
  (* (* Builds [comp(id__t', "transition", gm, ipm, opm) ∈ (behavior d)] *)
  (*    and [(t, id__t') ∈ t2tdi γ], and rewrites [id__t'] as [id__t].  *) *)
  (* edestruct @sitpn2hvhdl_t_comp with (sitpn := sitpn) (t := proj1_sig t) *)
  (*   as (id__t', (gm, (ipm, (opm, (InA_t2tdi, InCs_t))))); eauto. *)
  (* assert (eq_id__t : id__t = id__t') by *)
  (*     (erewrite NoDupA_fs_eqk_eq with (eqk := Teq) (b := id__t'); eauto; *)
  (*      eapply sitpn2hvhdl_nodup_t2tdi; eauto). *)
  (* rewrite <- eq_id__t in *; clear eq_id__t. *)

  (* (* Builds [compids] and [AreCsCompIds (behavior d) compids] *) *)
  (* destruct (AreCsCompIds_ex (behavior d)) as (compids, ACCI). *)
  
  (* (* Builds [Δ(id__t) = Δ__t] *) *)
  (* edestruct @elab_compid_in_comps with (D__s := hdstore) as (Δ__t, MapsTo_Δ__t); eauto. *)
  
  (* (* Builds [σ__e(id__t) = σ__te] *) *)
  (* edestruct @elab_compid_in_cstore with (D__s := hdstore) as (σ__te, MapsTo_σ__te); eauto. *)

  (* (* Builds [Δ__t("in_arcs_nb") = (t, n)] *) *)
  (* edestruct @elab_TDI_Δ_in_arcs_nb_1 as (t__ian, (n, MapsTo_ian)); eauto. *)
  
  (* (* Builds [σ__t0("rt") = aofv] *) *)
  (* assert (aofv_ex : exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sstore σ__t0)). *)
  (* { edestruct @elab_TDI_σ_rt with (d := d) as (aofv, MapsTo_aofv); eauto. *)
  (*   assert (MapsTo reinit_time (Input (Tarray Tbool 0 (n - 1))) Δ__t) by *)
  (*       (eapply elab_TDI_Δ_rt; eauto). *)
  (*   assert (IsOfType (Varr aofv) (Tarray Tbool 0 (n - 1))) by *)
  (*       (eapply elab_well_typed_values_in_sstore_of_comp; eauto). *)
  (*   edestruct @init_maps_sstore_of_comp as (v', MapsTo_v'); eauto. *)
  (*   assert (IsOfType_v' : IsOfType v' (Tarray Tbool 0 (n - 1))). *)
  (*   { eapply init_inv_well_typed_values_in_sstore_of_comp; eauto. *)
  (*     eapply elab_well_typed_values_in_sstore_of_comp; eauto. } *)
  (*   inversion_clear IsOfType_v' in MapsTo_v'. *)
  (*   exists aofv0; assumption. *)
  (* } *)
  (* destruct aofv_ex as (aofv, MapsTo_rt). *)
  
  (* eapply init_TDI_s_rtc_eq_bprod_of_rt; eauto; *)
  (*   (* 3 SUBGOALS *) *)
  (*   (* Proves [CsHasUniqueCompIds (behavior d) compids] *) *)
  (*   [split; eauto; eapply elab_nodup_compids; eauto *)
  (*   | *)
  (*   (* Proves [(events σ__e) = ∅] *) *)
  (*   eapply elab_empty_events; eauto *)
  (*   | ]. *)

  (* (* LAST SUBGOAL: [∏i=0 to n-1, rt(i) = false] *) *)
  
  (* (* CASE ANALYSIS: [pinputs_of_t] where [PInputsOf t pinputs_of_t]. *) *)

  (* edestruct (@PInputsOf_ex sitpn (proj1_sig t)) as (pinputs_of_t, PInputsOf_t). *)
  (* destruct pinputs_of_t. *)

  (* (* CASE [pinputs_of_t = ∅] *) *)
  (* - replace n with 1. *)
  (*   cbn; constructor. *)
  (*   replace (get_bool_at aofv 0) with false. *)
  (*   constructor. *)
  (*   (* SUBGOAL [get_bool_at aofv 0 = false] *) *)
  (*   + symmetry; eapply init_TDI_eval_rt_0; eauto. *)
  (*     eapply sitpn2hvhdl_emp_pinputs_rt; eauto. *)

  (*   (* SUBGOAL [Δ__t("in_arcs_nb") = 1] *) *)
  (*   + assert (List.In (ga_ input_arcs_number 1) gm) *)
  (*       by (eapply sitpn2hvhdl_emp_pinputs_in_arcs_nb ; eauto). *)
  (*     edestruct @elab_wf_gmap_expr with (D__s := hdstore) as (v, vexpr_); eauto. *)
  (*     edestruct @elab_TDI_Δ_in_arcs_nb_2 with (d := d) as (t__ian0, Mapsto_ian0); eauto. *)
  (*     inversion_clear vexpr_ in Mapsto_ian0. *)
  (*     assert (e1 : Generic t__ian0 (Vnat 1) = Generic t__ian (Vnat n)) *)
  (*       by eauto with mapsto. *)
  (*     inversion e1; reflexivity. *)
      
  (* (* CASE [pinputs_of_t ≠ ∅] *) *)
  (* - apply BProd_aofv_false. *)

  (*   (* Builds [∃ id__p, comp(id__p, P, ...) ∈ d.cs] and *)
  (*      [γ(p) = id__p]. *) *)
  (*   edestruct @sitpn2hvhdl_p_comp with (sitpn := sitpn) (p := p) *)
  (*     as (id__p, (gm__p, (ipm__p, (opm__p, (γ__p, InCs_id__p))))); eauto. *)

  (*   (* Builds [TOutputsOf p toutputs_of_p]. *) *)
  (*   edestruct (@TOutputsOf_ex sitpn p) as (toutputs_of_p, TOutputsOf_p). *)

  (*   (* Builds [pre p (proj1_sig t) <> None]. *) *)
  (*   assert (pre_pt : pre p (proj1_sig t) <> None) by *)
  (*       (rewrite ((proj1 PInputsOf_t) p); auto). *)
    
  (*   edestruct @sitpn2hvhdl_connect_rtt_rt with (sitpn := sitpn) *)
  (*     as (i, (j, (id__ji, (Itval_i, (Itval_j, (In_opm__p, In_ipm__t)))))); eauto. *)

  (*   (* Builds [ i ∈ [0, Δ__t("in_arcs_nb") - 1] ] and takes i to solve the goal. *) *)
  (*   replace n with (length (p :: pinputs_of_t)). *)
  (*   exists i; split; [assumption | ]. *)

  (*   (* SUBGOAL [length (p :: pinputs_of_t) = n] (i.e, [ |input(t)| = *)
  (*      Δ__t("in_arcs_nb") ] ).  *) *)
  (*   2 : { *)
  (*     assert (List.In (ga_ input_arcs_number (length (p :: pinputs_of_t))) gm) *)
  (*       by (eapply sitpn2hvhdl_nemp_pinputs_in_arcs_nb; eauto; cbn; lia). *)
  (*     edestruct @elab_wf_gmap_expr with (D__s := hdstore) (gm := gm) as (v, vexpr_); eauto. *)
  (*     edestruct @elab_TDI_Δ_in_arcs_nb_2 with (d := d) as (t__ian0, Mapsto_ian0); eauto. *)
  (*     inversion_clear vexpr_ in Mapsto_ian0. *)
  (*     assert (e1 : Generic t__ian0 (Vnat (S (Datatypes.length pinputs_of_t))) = Generic t__ian (Vnat n)) *)
  (*       by eauto with mapsto. *)
  (*     inversion e1; reflexivity. } *)
    
  (*   (* SUBGOAL [σ__t0("rt")(i) = false] *) *)
  (*   eapply init_TDI_eval_rt_i; eauto. *)

  (*   (* Then, show [σ0("id__ji") = false] *) *)

  (*   (* Builds [σ__p0] and [σ__p0("rtt") = Varr aofv']. *) *)
  (*   edestruct @elab_compid_in_cstore *)
  (*       with (D__s := hdstore) (id__c := id__p) *)
  (*       as (σ__pe, MapsTo_σ__pe); eauto. *)
  (*   edestruct @init_maps_cstore_id with (D__s := hdstore) *)
  (*     as (σ__p0, MapsTo_σ__p0); eauto. *)
  (*   edestruct @elab_PDI_σ_rtt with (d := d) as (aofv__pe, MapsTo_rtt__e); *)
  (*     eauto. *)
  (*   assert (MapsTo_rtt0_ex: exists aofv, MapsTo reinit_transitions_time (Varr aofv) (sstore σ__p0)). *)
  (*   { edestruct @elab_compid_in_comps with (D__s := hdstore) as (Δ__p, MapsTo_Δ__p); eauto 1. *)
  (*     edestruct @elab_PDI_Δ_out_arcs_nb_1 as (t__oan, (m, MapsTo_oan)); eauto 1. *)
  (*     assert (MapsTo reinit_transitions_time (Output (Tarray Tbool 0 (m - 1))) Δ__p) by *)
  (*         (eapply elab_PDI_Δ_rtt; eauto). *)
  (*     assert (IsOfType (Varr aofv__pe) (Tarray Tbool 0 (m - 1))) by *)
  (*         (eapply elab_well_typed_values_in_sstore_of_comp; eauto). *)
  (*     edestruct @init_maps_sstore_of_comp with (D__s := hdstore) *)
  (*       as (v, MapsTo_rtt0); eauto. *)
  (*     assert (IsOfType_v : IsOfType v (Tarray Tbool 0 (m - 1))). *)
  (*     { eapply init_inv_well_typed_values_in_sstore_of_comp; eauto. *)
  (*       eapply elab_well_typed_values_in_sstore_of_comp; eauto. } *)
  (*     inversion_clear IsOfType_v in MapsTo_rtt0. *)
  (*     exists aofv0; assumption. *)
  (*   } *)
  (*   destruct MapsTo_rtt0_ex as (aofv__P0, MapsTo_rtt0). *)
    
  (*   eapply @init_PDI_eval_rtt_i; eauto 1. *)
    
  (*   (* SUBGOAL [σ__p0("rtt")(j) = false] *) *)

  (*   (* Builds premises for [init_P_rtt_eq_false] lemma. *) *)

  (*   (* Builds [Δ(id__p) = Δ__p] *) *)
  (*   edestruct @elab_compid_in_comps with (D__s := hdstore) as (Δ__p, MapsTo_Δ__p); eauto 1. *)

  (*   (* Builds [Δ__p("out_arcs_nb") = (t__oan, m)] *) *)
  (*   edestruct @elab_PDI_Δ_out_arcs_nb_1 as (t__oan, (m, MapsTo_oan)); eauto 1. *)
    
  (*   eapply @init_PDI_rtt_eq_false with (n := length toutputs_of_p) (t := t__oan); eauto. *)

  (*   (* SUBGOAL [Δ__p("out_arcs_nb") = |output(p)|] *) *)
  (*   assert (List.In (ga_ output_arcs_number (length toutputs_of_p)) gm__p). *)
  (*   { eapply sitpn2hvhdl_nemp_toutputs_out_arcs_nb; eauto. *)
  (*     eapply length_neq_O with (eqA := Teq); eauto. *)
  (*     exists (proj1_sig t). *)
  (*     rewrite <- ((proj1 TOutputsOf_p) (proj1_sig t)); assumption. } *)

  (*   edestruct @elab_wf_gmap_expr with (D__s := hdstore) (gm := gm__p) as (v, vexpr_); eauto. *)
  (*   edestruct @elab_PDI_Δ_out_arcs_nb_2 as (t__oan0, MapsTo_oan0); eauto 1. *)
  (*   inversion_clear vexpr_ in MapsTo_oan0. *)
  (*   assert (e1 : Generic t__oan (Vnat m) = Generic t__oan0 (Vnat (length toutputs_of_p))) *)
  (*     by eauto with mapsto. *)
  (*   inversion_clear e1; assumption. *)    
Admitted.

Lemma init_states_eq_actions :
  forall sitpn b d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    Init hdstore Δ σ__e (AbstractSyntax.beh d) σ0 ->

    forall (a : A sitpn) (id__a : ident),
      InA Akeq (a, id__a) (a2out γ) ->
      MapsTo id__a (Vbool (ex (s0 sitpn) (inl a))) (sstore σ0).
Admitted.

Lemma init_states_eq_functions :
  forall sitpn b d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    Init hdstore Δ σ__e (AbstractSyntax.beh d) σ0 ->

    forall (f : F sitpn) (id__f : ident),
      InA Fkeq (f, id__f) (f2out γ) ->
      MapsTo id__f (Vbool (ex (s0 sitpn) (inr f))) (sstore σ0).
Admitted.

Lemma init_states_eq_conditions :
  forall sitpn b d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    Init hdstore Δ σ__e (AbstractSyntax.beh d) σ0 ->

    forall (c : C sitpn) (id__c : ident),
      InA Ckeq (c, id__c) (c2in γ) ->
      MapsTo id__c (Vbool (cond (s0 sitpn) c)) (sstore σ0).
Admitted.

(** ** Similar initial states lemmas *)

Lemma sim_init_states :
  forall sitpn b d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    Init hdstore Δ σ__e (AbstractSyntax.beh d) σ0 ->

    (* Initial states are similar *)
    SimState sitpn γ (s0 sitpn) σ0.
Proof.
  intros; unfold SimState; unfold SimStateNoCondsNoReset.
  split. split. eapply init_states_eq_marking; eauto.
  split. eapply init_states_eq_time_counters; eauto.
  split. eapply init_states_eq_actions; eauto.
  eapply init_states_eq_functions; eauto.
  split. eapply init_states_eq_reset_orders; eauto.
  eapply init_states_eq_conditions; eauto.
Qed.

#[export] Hint Resolve sim_init_states : hilecop.

(** For all SITPN [sitpn] passed as input to the HM2T and resulting
    design [d], [d] admits an initial state [σ0] that is similar to
    the initial state of [sitpn]. *)

Lemma sim_init_state_ex :
  forall sitpn b d γ Δ σ__e,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* There exists an initial state [σ0] of [d]. *)
    exists σ0,
      Init hdstore Δ σ__e (AbstractSyntax.beh d) σ0
    
      (* Initial states are similar *)
      /\ SimState sitpn γ (s0 sitpn) σ0.
Admitted.

(** For all SITPN [sitpn] passed as input to the HM2T and resulting
    design [d], [d] admits an initial state [σ0]. *)

Lemma init_state_ex :
  forall sitpn b d γ Δ σ__e,

    (* The SITPN model [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* sitpn translates into (d, γ). *)
    sitpn2hvhdl sitpn b = (inl (d, γ)) ->

    (* An elaborated version [Δ] of [d], with a default state [σ__e] *)
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* There exists an initial state [σ0] of [d]. *)
    exists σ0, Init hdstore Δ σ__e (AbstractSyntax.beh d) σ0. 
Admitted.

#[export] Hint Resolve init_state_ex : hilecop.

