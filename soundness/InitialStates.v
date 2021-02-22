(** * Similar Initial States *)

Require Import String.
Require Import common.Coqlib.
Require Import common.InAndNoDup.
Require Import common.GlobalTypes.
Require Import common.NatMap.
Require Import common.FstSplit.
Require Import common.GlobalFacts.
Require Import common.SetoidListFacts.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListPlus.
Require Import common.ListMonad.
Require Import common.ListMonadFacts.
Require Import common.ListMonadTactics.
Require Import common.ListDep.

Require Import sitpn.dp.Sitpn.
Require Import sitpn.dp.SitpnTypes.
Require Import sitpn.dp.SitpnSemanticsDefs.
Require Import sitpn.dp.SitpnSemantics.
Require Import sitpn.dp.SitpnFacts.
Require Import sitpn.dp.SitpnWellDefined.
Require Import sitpn.dp.SitpnWellDefinedTactics.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.AbstractSyntaxTactics.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.Initialization.
Require Import hvhdl.Environment.
Require Import hvhdl.Place.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.Stabilize.
Require Import hvhdl.InitializationFacts.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.WellDefinedDesignFacts.
Require Import hvhdl.DesignElaborationFacts.
Require Import hvhdl.PlaceElaborationFacts.
Require Import hvhdl.PInitializationFacts.

Require Import sitpn2hvhdl.Sitpn2HVhdl.
Require Import sitpn2hvhdl.GenerateHVhdlFacts.
Require Import sitpn2hvhdl.GenerateInfosFacts.

Require Import soundness.SoundnessDefs.

(** ** Initial States Equal Marking Lemma *)    

(** [sitpn2hvhdl(sitpn) = (d,γ)] and [(p, id__p) ∈ γ] and [(p, id__p') ∈
    γ] then [id__p = id__p'] *)

Ltac rw_γp p id__p id__p' :=
  lazymatch type of p with
  | P _ =>
    let tpp := (type of p) in
    lazymatch goal with
    | [ H: sitpn_to_hvhdl ?sitpn _ _ _ _ = inl (_, ?γ), Hwd: IsWellDefined ?sitpn |- _ ] =>
      specialize (sitpn2hvhdl_nodup_p2pcomp H Hwd); intros Hnodup_p2pcomp;
      lazymatch goal with
      | [ H: InA _ (p, id__p) (p2pcomp γ), H': InA _ (p, id__p') (p2pcomp γ) |- _ ] =>
        rewrite <- (NoDupA_fs_eqk_eq (P sitpn) (Equivalence_Peq sitpn) Hnodup_p2pcomp H H');
        clear Hnodup_p2pcomp
      end
    | _ => fail "Found no term of type (sitpn_to_hvhdl ?sitpn ?decpr ?id__ent ?id__arch ?mm = inl (?d, ?γ))"
    end
  | _ =>
    let tpp := (type of p) in
    fail "Term" p "is of type" tpp
         "while it is expected to be of type P ?sitpn" 
  end.

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

  (* Builds the premises of the [init_states_eq_marking] lemma. *)
  
  (* Builds [comp(id__p', "place", gm, ipm, opm) ∈ (behavior d)] *)
  edestruct @sitpn2hvhdl_p_comp with (sitpn := sitpn) (p := p)
    as (id__p', (gm, (ipm, (opm, (Hγ, Hincs_comp))))); eauto.
  
  (* Builds [compids] and [AreCsCompIds (behavior d) compids] *)
  destruct (AreCsCompIds_ex (behavior d)) as (compids, HAreCsCompIds).

  (* Builds [id__p' ∈ Comps(Δ)] *)
  edestruct @elab_compid_in_comps with (D__s := hdstore) as (Δ__p, MapsTo_Δ__p); eauto. 

  (* Builds [id__p' ∈ (compstore σ__e)] *)
  edestruct @elab_compid_in_compstore with (D__s := hdstore) as (σ__pe, MapsTo_σ__pe); eauto.

  (* Builds [Δ__p("s_marking") = Tnat 0 n] *)
  edestruct @elab_pcomp_Δ_s_marking as (n, MapsTo_smarking); eauto.

  (* Builds proof that [ipm] is well-formed *)
  edestruct @elab_validipm as (formals, (listipm_ipm, checkformals_ipm)); eauto.
  
  (* To prove [σ__p0("s_marking") = M0(p)] *)
  eapply init_s_marking_eq_nat; eauto.
  
  (* 6 subgoals left. *)

  (* Prove [(events σ__e) = ∅] *)
  - eapply elab_empty_events; eauto.
    
  (* Prove [NoDup compids] *)
  - eapply elab_nodup_compids; eauto.
    
  (* Prove [<initial_marking => M0(p)> ∈ ipm] *)
  - eapply sitpn2hvhdl_bind_init_marking; eauto.

  (* Prove [initial_marking ∈ Ins(Δ__p) *)
  - eapply elab_pcomp_Δ_init_marking; eauto.
    
  (* Prove [id__p = id__p'] *)
  - rw_γp p id__p id__p'; assumption.

  (* Prove [s_marking ∉ (events σ__pe)] *)
  - erewrite elab_empty_events_for_comps; eauto with set.
Qed.

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
    
    forall (t : Ti sitpn) (id__t : ident) (σ__t : DState),
      InA Tkeq (proj1_sig t, id__t) (t2tcomp γ) ->
      MapsTo id__t σ__t (compstore σ0) ->
      (upper t = i+ /\ TcLeLower (s0 sitpn) t -> MapsTo Transition.s_time_counter (Vnat (I (s0 sitpn) t)) (sigstore σ__t)) /\
      (upper t = i+ /\ TcGtLower (s0 sitpn) t -> MapsTo Transition.s_time_counter (Vnat (lower t)) (sigstore σ__t)) /\
      (forall pf : upper t <> i+, TcGtUpper (s0 sitpn) t ->
                   MapsTo Transition.s_time_counter (Vnat (natinf_to_natstar (upper t) pf)) (sigstore σ__t)) /\
      (upper t <> i+ /\ TcLeUpper (s0 sitpn) t -> MapsTo Transition.s_time_counter (Vnat (I (s0 sitpn) t)) (sigstore σ__t)).
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
    
    (forall (t : Ti sitpn) (id__t : ident) (σ__t : DState),
        InA Tkeq (proj1_sig t, id__t) (t2tcomp γ) -> MapsTo id__t σ__t (compstore σ0) ->
        MapsTo Transition.s_reinit_time_counter (Vbool (reset (s0 sitpn) t)) (sigstore σ__t)).
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
