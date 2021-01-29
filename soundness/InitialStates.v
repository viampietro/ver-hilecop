(** * Similar Initial States *)

Require Import String.
Require Import common.Coqlib.
Require Import common.InAndNoDup.
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

Require Import sitpn2hvhdl.Sitpn2HVhdl.
Require Import sitpn2hvhdl.GenerateHVhdlFacts.
Require Import sitpn2hvhdl.GenerateInfosFacts.

Require Import soundness.SoundnessDefs.

(** ** Initial States Equal Marking Lemma *)    

Lemma sitpn2hvhdl_bind_init_marking :
  forall {sitpn decpr id__ent id__arch mm d γ},
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    forall p id__p gm ipm opm,
      InA Pkeq (p, id__p) (p2pcomp γ) ->
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (behavior d) ->
      List.In (associp_ ($initial_marking) (@M0 sitpn p)) ipm.
Admitted.

Lemma elab_compid_in_compstore :
  forall {D__s M__g d Δ σ__e id__c id__e gm ipm opm},
    edesign D__s M__g d Δ σ__e ->
    InCs (cs_comp id__c id__e gm ipm opm) (behavior d) ->
    exists σ__c, MapsTo id__c σ__c (compstore σ__e).
Admitted.

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
  
  (* Builds [comp(id__p', "place", gm, ipm, opm) ∈ (behavior d)] *)
  lazymatch goal with
  | [ Hs2h: sitpn_to_hvhdl _ _ _ _ _ = _, Hwd: IsWellDefined _ |- _ ] =>
    specialize (sitpn2hvhdl_p_comp Hs2h Hwd p) as Hex;
      inversion_clear Hex as (id__p', (gm, (ipm, (opm, (Hγ, Hincs_comp)))));
      rename H into Hsitpn2hvhdl
  end.

  (* To prove [σ__p0("s_marking") = M0(p)] *)
  eapply init_s_marking_eq_nat; eauto.
  
  (* Prove [<initial_marking => M0(p)> ∈ ipm] *)
  (* eapply sitpn2hvhdl_bind_init_marking; eauto. *)

  (* [∃ σ, σ__e(id__p') = σ] *)
  (* eapply elab_compid_in_compstore; eauto. *)
  
  (* Prove [id__p = id__p'] *)
  (* rw_γp p id__p id__p'; assumption. *)    
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
  intros; unfold SimState. split.
  eapply init_states_eq_marking; eauto.
Admitted.

Hint Resolve sim_init_states : hilecop.
