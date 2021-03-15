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

Require Import sitpn2hvhdl.Sitpn2HVhdl.
Require Import sitpn2hvhdl.GenerateHVhdlFacts.
Require Import sitpn2hvhdl.GenerateInfosFacts.

Require Import soundness.SoundnessDefs.

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
  edestruct @elab_pcomp_Δ_s_marking as (n, MapsTo_smarking); eauto.

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
  - eapply elab_pcomp_Δ_init_marking; eauto.
    
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
    edestruct @elab_compid_in_compstore with (D__s := hdstore) as (σ__pe, MapsTo_σ__pe); eauto;

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
    eapply @elab_tcomp_Δ_s_tc; eauto
    |
    (* Proves ["s_tc" ∉ (events σ__pe)] *)
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

Lemma add1_comm : forall n m, n + S m = S n + m. do 2 intro; lia. Qed.
Lemma S_mone_inv : forall n, 0 < n -> n = S (n - 1). intro; lia. Qed.

Fixpoint seq1 (start len : nat) {struct len} : 0 < start + len -> list { n : nat | n < start + len }.
  refine (match len with
          | 0 => fun _ => nil
          | S len' => fun _ => _
          end).
  refine ((exist _ start (Nat.lt_add_pos_r (S len') start (Nat.lt_0_succ len'))) :: _).
  rewrite (add1_comm start len').
  rewrite (add1_comm start len') in l.
  exact (seq1 (S start) len' l).
Defined.

Lemma length_aofv_gt_O : forall aofv : arrofvalues, 0 < length aofv.
  destruct aofv; cbn; eapply Nat.lt_0_succ; eauto.
Defined.

Definition seq_O_n (n : nat) : 0 < n -> list {m : nat | m < n }.
  rewrite <- (plus_O_n n); exact (seq1 0 n).
Defined.

Definition arrofv_idxs (aofv : arrofvalues) : list { i | i < length aofv }.
  exact (seq_O_n (length aofv) (length_aofv_gt_O aofv)).
Defined.

Definition ProdOfArrOfVBool (aofvb : arrofvalues) (bprod : bool) :=
  let f_bprod :=
      fun bprod (i : { n | n < length aofvb}) =>
        match get_at (proj1_sig i) aofvb (proj2_sig i) with
        | Vbool b => bprod && b
        | _ => bprod
        end
  in
  FoldL f_bprod (arrofv_idxs aofvb) true bprod.

Definition BProd_ArrOfVBool (aofvb : arrofvalues) (bprod : bool) :=
  let f_bprod :=
      fun i =>
        match oget_at i aofvb with
        | Some (Vbool b) => b
        | _ => true
        end
  in
  BProd f_bprod (seq 0 (length aofvb)) bprod.

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
  intros *; intros IWD e elab_ init_ t id__t σ__t0 InA_t2tcomp MapsTo_cstore0.
  cbn; unfold nullb.


  
  (* GOAL [σ__t0("s_rtc") = false] *)

  Lemma init_s_rtc_eq_bprod_of_rt :
    forall Δ σ behavior σ0,
      init hdstore Δ σ behavior σ0 ->
      forall id__t gm ipm opm compids Δ__t σ__t σ__t0,
        InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
        CsHasUniqueCompIds behavior compids ->
        Equal (events σ) {[]} ->
        MapsTo id__t (Component Δ__t) Δ ->
        MapsTo id__t σ__t (compstore σ) ->
        MapsTo id__t σ__t0 (compstore σ0) ->
        DeclaredOf Δ__t s_reinit_time_counter ->
        ~NatSet.In s_reinit_time_counter (events σ__t) ->
        
        MapsTo Transition.s_reinit_time_counter (Vbool b) (sigstore σ__t0).
  Proof.
  
  (* init_s_rtc_eq_sum *)
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
