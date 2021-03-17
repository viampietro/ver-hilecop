(** * Similar Initial States *)

Require Import String.
Require Import common.CoqLib.
Require Import common.CoqTactics.
Require Import common.GlobalTypes.
Require Import common.GlobalFacts.
Require Import common.NatMap.
Require Import common.ListLib.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.

Require Import sitpn.dp.SitpnLib.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.HVhdlElaborationFactsLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlHilecopFactsLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.HVhdlSimulationFactsLib.

Require Import sitpn2hvhdl.Sitpn2HVhdl.
Require Import sitpn2hvhdl.GenerateHVhdlFacts.
Require Import sitpn2hvhdl.GenerateInfosFacts.

Require Import soundness.SoundnessDefs.

Set Nested Proofs Allowed.

(** ** Initial States Equal Marking Lemma *)    

Lemma init_states_eq_marking :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    init hdstore Δ σ__e (behavior d) σ0 ->

    forall p id__p σ__p0,
      (* [id__p] is the identifier of the place component associated with
         place [p] by the [γ] binder. *)
      InA Pkeq (p, id__p) (p2pcomp γ) ->

      (* [σ__p] is the current state of component [id__p] is the global
         design state [σ]. *)
      MapsTo id__p σ__p0 (compstore σ0) ->

      (* Marking of place [p] at state [s] equals value of signal
         [s_marking] at state [σ__p]. *)
      MapsTo Place.s_marking (Vnat (M (s0 sitpn) p)) (sigstore σ__p0).
Proof.
  intros.

  (* Builds the premises of the [init_s_marking_eq_nat] lemma. *)
  
  (* Builds [comp(id__p', "place", gm, ipm, opm) ∈ (behavior d)] *)
  edestruct @sitpn2hvhdl_p_comp with (sitpn := sitpn) (p := p)
    as (id__p', (gm, (ipm, (opm, (Hγ, Hincs_comp))))); eauto.
  
  (* Builds [compids] and [AreCsCompIds (behavior d) compids] *)
  destruct (AreCsCompIds_ex (behavior d)) as (compids, HAreCsCompIds).

  (* Builds [id__p' ∈ Comps(Δ)] *)
  edestruct @elab_compid_in_comps with (D__s := hdstore) as (Δ__p, MapsTo_Δ__p); eauto. 

  (* Builds [id__p' ∈ (compstore σ__e)] *)
  edestruct @elab_compid_in_compstore with (D__s := hdstore) as (σ__pe, MapsTo_σ__pe); eauto.

  (* Builds [Δ__p("s_marking") = Declared (Tnat 0 n)] *)
  edestruct @elab_P_Δ_s_marking as (n, MapsTo_smarking); eauto.

  (* Builds proof that [ipm] is well-formed *)
  edestruct @elab_validipm as (formals, (listipm_ipm, checkformals_ipm)); eauto.
  
  (* To prove [σ__p0("s_marking") = M0(p)] *)
  eapply init_s_marking_eq_nat; eauto.
  
  (* 6 subgoals left. *)

  (* Proves [(events σ__e) = ∅] *)
  - eapply elab_empty_events; eauto.
    
  (* Proves [NoDup compids] *)
  - eapply elab_nodup_compids; eauto.
    
  (* Proves [<initial_marking => M0(p)> ∈ ipm] *)
  - eapply sitpn2hvhdl_bind_init_marking; eauto.

  (* Proves [initial_marking ∈ Ins(Δ__p) *)
  - eapply elab_P_Δ_init_marking; eauto.
    
  (* Proves [id__p = id__p'] *)
  - erewrite NoDupA_fs_eqk_eq with (eqk := @Peq sitpn) (b := id__p'); eauto.
    eapply sitpn2hvhdl_nodup_p2pcomp; eauto.

  (* Proves [s_marking ∉ (events σ__pe)] *)
  - erewrite elab_empty_events_for_comps; eauto with set.
Qed.

(** ** Initial States Equal Time Counters *)

Lemma init_states_eq_time_counters :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    init hdstore Δ σ__e (behavior d) σ0 ->
    
    forall (t : Ti sitpn) (id__t : ident) (σ__t0 : DState),
      InA Tkeq (proj1_sig t, id__t) (t2tcomp γ) ->
      MapsTo id__t σ__t0 (compstore σ0) ->
      (upper t = i+ /\ TcLeLower (s0 sitpn) t -> MapsTo Transition.s_time_counter (Vnat (I (s0 sitpn) t)) (sigstore σ__t0)) /\
      (upper t = i+ /\ TcGtLower (s0 sitpn) t -> MapsTo Transition.s_time_counter (Vnat (lower t)) (sigstore σ__t0)) /\
      (forall pf : upper t <> i+, TcGtUpper (s0 sitpn) t ->
                   MapsTo Transition.s_time_counter (Vnat (natinf_to_natstar (upper t) pf)) (sigstore σ__t0)) /\
      (upper t <> i+ /\ TcLeUpper (s0 sitpn) t -> MapsTo Transition.s_time_counter (Vnat (I (s0 sitpn) t)) (sigstore σ__t0)).
Proof.
  intros *; intros IWD e Helab Hinit; intros t id__t σ__t0; intros InA_γ Mapsto_σ0.
  cbn; split_and.
  
  (* CASE [upper(I__s(t)) = ∞ and s0.I(t) ≤ lower(I__s(t))] 
     and [upper(I__s(t)) ≠ ∞ and s0.I(t) ≤ upper(I__s(t))] *)
  1,4 : intros;

    (* Builds the premises of the [init_s_tc_eq_O] lemma. *)
    
    (* Builds [comp(id__t', "transition", gm, ipm, opm) ∈ (behavior d)] *)
    edestruct @sitpn2hvhdl_t_comp with (sitpn := sitpn) (t := proj1_sig t)
      as (id__t', (gm, (ipm, (opm, (InA_t2tcomp, InCs_t))))); eauto;

    (* Builds [compids] and [AreCsCompIds (behavior d) compids] *)
    destruct (AreCsCompIds_ex (behavior d)) as (compids, AreCsCompIds_);
    
    (* Builds [id__t' ∈ (compstore σ__e)] *)
    edestruct @elab_compid_in_compstore with (D__s := hdstore) as (σ__te, MapsTo_σ__te); eauto;

    (* Builds [id__t' ∈ Comps(Δ)] *)
    edestruct @elab_compid_in_comps with (D__s := hdstore) as (Δ__t, MapsTo_Δ__t); eauto;
    
    (* To prove [σ__t0("s_tc") = 0] *)
    eapply init_s_tc_eq_O; eauto; [

    (* 5 SUBGOALS left *)

    (* Proves [NoDup compids] *)
    eapply elab_nodup_compids; eauto
    |
    (* Proves [(events σ__e) = ∅] *)
    eapply elab_empty_events; eauto
    |
    (* Proves [DeclaredOf Δ__t "s_tc"] *)
    eapply @elab_T_Δ_s_tc; eauto
    |
    (* Proves ["s_tc" ∉ (events σ__te)] *)
    erewrite elab_empty_events_for_comps; eauto with set
    |
    (* Proves [id__t = id__t'] *)
    erewrite NoDupA_fs_eqk_eq with (eqk := Teq) (b := id__t'); eauto;
      eapply sitpn2hvhdl_nodup_t2tcomp; eauto ].
  
  (* CASE [upper(I__s(t)) = ∞ and s0.I(t) > lower(I__s(t))] *)
  - destruct 1 as (upper_, TcGtLower_).
    unfold TcGtLower in TcGtLower_.
    destruct t in TcGtLower_; cbn in TcGtLower_.
    destruct (Is x).
    destruct (a t0).
    cbn in TcGtLower_; lia.
    contradiction.
    
  (* CASE [upper(I__s(t)) ≠ ∞ and s0.I(t) > upper(I__s(t))] *)
  - intros upper_ TcGtUpper_.
    unfold TcGtUpper in TcGtUpper_; cbn in TcGtUpper_.
    destruct t in TcGtUpper_.
    destruct (Is x).
    destruct (b t0) in TcGtUpper_; cbn in TcGtUpper_; lia.
    contradiction.
Qed.

Definition PInputsOf {sitpn} (t : T sitpn) (pinputs_of_t : list (P sitpn)) :=
  @Set_in_ListA (P sitpn) Peq (fun p => pre p t <> None) pinputs_of_t.

Definition TOutputsOf {sitpn} (p : P sitpn) (toutputs_of_p : list (T sitpn)) :=
  @Set_in_ListA (T sitpn) Teq (fun t => pre p t <> None) toutputs_of_p.
  
Lemma PInputsOf_ex : forall sitpn (t : T sitpn), exists pinputs_of_t, PInputsOf t pinputs_of_t.
  intros sitpn t; unfold PInputsOf.
Admitted.

Lemma TOutputsOf_ex : forall sitpn (p : P sitpn), exists toutputs_of_p, TOutputsOf p toutputs_of_p.
Admitted.

Lemma sitpn2hvhdl_emp_pinputs_in_arcs_nb :
  forall {sitpn decpr id__ent id__arch mm d γ},
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    IsWellDefined sitpn ->
    forall t id__t gm ipm opm,
      InA Tkeq (t, id__t) (t2tcomp γ) ->
      InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
      PInputsOf t [] ->
      List.In (assocg_ Transition.input_arcs_number 1) gm.
Admitted.

Lemma sitpn2hvhdl_emp_pinputs_rt :
  forall {sitpn decpr id__ent id__arch mm d γ},
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    IsWellDefined sitpn ->
    forall t id__t gm ipm opm,
      InA Tkeq (t, id__t) (t2tcomp γ) ->
      InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
      PInputsOf t [] ->
      List.In (associp_ (Transition.reinit_time $[[0]]) false) ipm.
Admitted.

Lemma elab_T_Δ_in_arcs_nb_1 :
  forall {d Δ σ__e id__t gm ipm opm Δ__t},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    exists t n, MapsTo input_arcs_number (Generic t (Vnat n)) Δ__t.
Admitted.

Lemma elab_T_Δ_in_arcs_nb_2 :
  forall {d Δ σ__e id__t gm ipm opm Δ__t e v},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    List.In (assocg_ input_arcs_number e) gm ->
    vexpr EmptyElDesign EmptyDState EmptyLEnv false e v ->
    exists t, MapsTo input_arcs_number (Generic t v) Δ__t.
Admitted.

Lemma elab_wf_gmap_expr :
  forall {D__s M__g d Δ σ__e id__c id__e gm ipm opm id e},
    edesign D__s M__g d Δ σ__e ->
    InCs (cs_comp id__c id__e gm ipm opm) (behavior d) ->
    List.In (assocg_ id e) gm ->
    exists v, vexpr EmptyElDesign EmptyDState EmptyLEnv false e v.
Admitted.

Lemma elab_T_σ_rt_val_is_of_type : 
  forall {d Δ σ__e id__t gm ipm opm Δ__t σ__te n t v},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t σ__te (compstore σ__e) ->
    MapsTo id__t (Component Δ__t) Δ ->
    MapsTo input_arcs_number (Generic t (Vnat n)) Δ__t ->
    MapsTo Transition.reinit_time v (sigstore σ__te) ->
    is_of_type v (Tarray Tbool 0 (n - 1)).
Admitted.

Lemma init_T_eval_rt_0 :
  forall D__s Δ σ behavior σ0,
    init D__s Δ σ behavior σ0 ->
    forall id__c id__e gm ipm opm Δ__c σ__c0 aofv,
      InCs (cs_comp id__c id__e gm ipm opm) behavior ->
      MapsTo id__c (Component Δ__c) Δ ->
      MapsTo id__c σ__c0 (compstore σ0) ->
      MapsTo reinit_time (Varr aofv) (sigstore σ__c0) ->
      List.In (associp_ (reinit_time $[[0]]) false) ipm ->
      get_bool_at aofv 0 = false.
Admitted.

Lemma init_states_eq_reset_orders :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    init hdstore Δ σ__e (behavior d) σ0 ->
    
    (forall (t : Ti sitpn) (id__t : ident) (σ__t0 : DState),
        InA Tkeq (proj1_sig t, id__t) (t2tcomp γ) ->
        MapsTo id__t σ__t0 (compstore σ0) ->
        MapsTo Transition.s_reinit_time_counter (Vbool (reset (s0 sitpn) t)) (sigstore σ__t0)).
Proof.
  intros *; intros IWD e elab_ init_ t id__t σ__t0; intros.
  cbn; unfold nullb.

  (* APPLY [init_rtc_eq_bprod_of_rt] lemma. *)

  (* Building premises *)
  
  (* Builds [comp(id__t', "transition", gm, ipm, opm) ∈ (behavior d)]
     and [(t, id__t') ∈ t2tcomp γ], and rewrites [id__t'] as [id__t].  *)
  edestruct @sitpn2hvhdl_t_comp with (sitpn := sitpn) (t := proj1_sig t)
    as (id__t', (gm, (ipm, (opm, (InA_t2tcomp, InCs_t))))); eauto.
  assert (eq_id__t : id__t = id__t').
  { erewrite NoDupA_fs_eqk_eq with (eqk := Teq) (b := id__t'); eauto;
      eapply sitpn2hvhdl_nodup_t2tcomp; eauto. }  
  rewrite <- eq_id__t in *; clear eq_id__t.
  
  (* Builds [compids] and [CsHasUniqueCompIds (behavior d) compids] *)
  destruct (AreCsCompIds_ex (behavior d)) as (compids, AreCsCompIds_).
  assert (CsHasUnCIds_ : CsHasUniqueCompIds (behavior d) compids)
    by (split; [ assumption | eapply elab_nodup_compids; eauto]).

  (* Builds [(events σ__e) = ∅] *)
  assert (Emp_ev__e : Equal (events σ__e) {[]}) by (eapply elab_empty_events; eauto).

  (* Builds [id__t ∈ Comps(Δ)] *)
  edestruct @elab_compid_in_comps with (D__s := hdstore) as (Δ__t, MapsTo_Δ__t); eauto.
  
  (* Builds [id__t ∈ (compstore σ__e)] *)
  edestruct @elab_compid_in_compstore with (D__s := hdstore) as (σ__te, MapsTo_σ__te); eauto.

  (* Builds [DeclaredOf Δ__t "s_rtc"] *)
  assert (Decl_s_rtc : DeclaredOf Δ__t s_reinit_time_counter)
    by (eapply @elab_T_Δ_s_rtc; eauto).

  (* Builds [s_rtc ∉ events σ__te] *)
  assert (nIn_events : ~NatSet.In s_reinit_time_counter (events σ__te))
    by (erewrite elab_empty_events_for_comps; eauto with set).

  (* Builds [∃ aofv, σ__t0("rt") = aofv] *)
  assert (aofv_ex : exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sigstore σ__t0)).
  { edestruct @elab_T_σ_rt with (d := d) as (aofv, MapsTo_aofv); eauto.
    eapply init_maps_sstore_of_comp_Varr; eauto. }
  destruct aofv_ex as (aofv, MapsTo_rt).

  (* Builds [∃ t n, Δ__t("in_arcs_nb") = (t, n)] *)
  edestruct @elab_T_Δ_in_arcs_nb_1 as (t__ian, (n, MapsTo_ian)); eauto. 
  
  eapply init_s_rtc_eq_bprod_of_rt; eauto.
  
  (* CASE ANALYSIS: [pinputs_of_t] where [PInputsOf t pinputs_of_t]. *)

  edestruct (@PInputsOf_ex sitpn (proj1_sig t)) as (pinputs_of_t, PInputsOf_t).
  destruct pinputs_of_t.

  (* CASE [pinputs_of_t = ∅] *)
  - replace n with 1.
    cbn; constructor.
    replace (get_bool_at aofv 0) with false.
    constructor.
    (* SUBGOAL [get_bool_at aofv 0 = false] *)
    + symmetry; eapply init_T_eval_rt_0; eauto.
      eapply sitpn2hvhdl_emp_pinputs_rt; eauto.

    (* SUBGOAL [Δ__t("in_arcs_nb") = 1] *)
    + assert (List.In (assocg_ input_arcs_number 1) gm)
        by (eapply sitpn2hvhdl_emp_pinputs_in_arcs_nb ; eauto).
      edestruct @elab_wf_gmap_expr with (D__s := hdstore) as (v, vexpr_); eauto.
      edestruct @elab_T_Δ_in_arcs_nb_2 with (d := d) as (t__ian0, Mapsto_ian0); eauto.
      inversion_clear vexpr_ in Mapsto_ian0.
      assert (e1 : Generic t__ian0 (Vnat 1) = Generic t__ian (Vnat n))
        by eauto with mapsto.
      inversion e1; reflexivity.
      
  (* CASE [pinputs_of_t ≠ ∅] *)
  - idtac.
    Lemma BProd_aofv_false : 
      forall aofv n m,
        (exists i, n <= i < m /\ get_bool_at aofv i = false) ->
        BProd (get_bool_at aofv) (seq n m) false.
    Admitted.
    apply BProd_aofv_false.

    (* Builds [∃ id__p, comp(id__p, P, ...) ∈ d.cs] and
       [γ(p) = id__p] *)
    edestruct @sitpn2hvhdl_p_comp with (sitpn := sitpn) (p := p)
      as (id__p, (gm__p, (ipm__p, (opm__p, (γ__p, InCs_id__p))))); eauto.

    (* Builds [TOutputsOf p toutputs_of_p]. *)
    edestruct (@TOutputsOf_ex sitpn p) as (toutputs_of_p, TOutputsOf_p).

    (* Builds [pre p (proj1_sig t) <> None]. *)
    assert (pre_pt : pre p (proj1_sig t) <> None) by
        (rewrite ((proj1 PInputsOf_t) p); auto).
    
    Lemma sitpn2hvhdl_connect_rtt_rt :
      forall {sitpn decpr id__ent id__arch mm d γ},
        sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
        IsWellDefined sitpn ->
        forall t id__t gm__t ipm__t opm__t p id__p gm__p ipm__p opm__p pinputs_of_t toutputs_of_p,
          @pre sitpn p t <> None ->
          PInputsOf t pinputs_of_t ->
          TOutputsOf p toutputs_of_p ->
          InA Tkeq (t, id__t) (t2tcomp γ) ->
          InCs (cs_comp id__t Petri.transition_entid gm__t ipm__t opm__t) (behavior d) ->
          InA Pkeq (p, id__p) (p2pcomp γ) ->
          InCs (cs_comp id__p Petri.place_entid gm__p ipm__p opm__p) (behavior d) ->
          exists i j id__ji,
            0 <= i < length pinputs_of_t
            /\ 0 <= j < length toutputs_of_p
            /\ List.In (assocop_idx Place.reinit_transitions_time (e_nat j) ($id__ji)) opm__p
            /\ List.In (associp_ (Transition.reinit_time $[[(e_nat i)]]) (#id__ji)) ipm__t.    
    Admitted.

    edestruct @sitpn2hvhdl_connect_rtt_rt with (sitpn := sitpn)
      as (i, (j, (id__ji, (Itval_i, (Itval_j, (In_opm__p, In_ipm__t)))))); eauto.
Admitted.

Lemma init_states_eq_actions :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    init hdstore Δ σ__e (behavior d) σ0 ->

    forall (a : A sitpn) (id__a : ident),
      InA Akeq (a, id__a) (a2out γ) ->
      MapsTo id__a (Vbool (ex (s0 sitpn) (inl a))) (sigstore σ0).
Admitted.

Lemma init_states_eq_functions :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    init hdstore Δ σ__e (behavior d) σ0 ->

    forall (f : F sitpn) (id__f : ident),
      InA Fkeq (f, id__f) (f2out γ) ->
      MapsTo id__f (Vbool (ex (s0 sitpn) (inr f))) (sigstore σ0).
Admitted.

Lemma init_states_eq_conditions :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    init hdstore Δ σ__e (behavior d) σ0 ->

    forall (c : C sitpn) (id__c : ident),
      InA Ckeq (c, id__c) (c2in γ) ->
      MapsTo id__c (Vbool (cond (s0 sitpn) c)) (sigstore σ0).
Admitted.

(** ** Similar Initial States Lemma *)

Lemma sim_init_states :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (NatMap.empty value) d Δ σ__e ->

    (* initialization d's state. *)
    init hdstore Δ σ__e (behavior d) σ0 ->

    (* init states are similar *)
    γ ⊢ (s0 sitpn) ∼ σ0.
Proof.
  intros; unfold SimState; unfold SimStateNoConds.
  split. split. eapply init_states_eq_marking; eauto.
  split. eapply init_states_eq_time_counters; eauto.
  split. eapply init_states_eq_reset_orders; eauto.
  split. eapply init_states_eq_actions; eauto.
  eapply init_states_eq_functions; eauto.
  eapply init_states_eq_conditions; eauto.
Qed.

Hint Resolve sim_init_states : hilecop.
