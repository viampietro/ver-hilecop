(** * Facts about Initialization and Place Design *)

Require Import common.Coqlib.
Require Import common.NatMap.
Require Import common.NatMapTactics.
Require Import common.NatSet.
Require Import common.InAndNoDup.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.Initialization.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Place.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.EnvironmentTactics.
Require Import hvhdl.SSEvaluation.

Require Import hvhdl.StabilizeFacts.
Require Import hvhdl.SSEvaluationFacts.
Require Import hvhdl.PortMapEvaluationFacts.
Require Import hvhdl.EnvironmentFacts.
Require Import hvhdl.WellDefinedDesignFacts.
Require Import hvhdl.InitializationFacts.
Require Import hvhdl.PStabilizeFacts.

(** ** Facts about [vruninit] and Place Design *)

Section PVRunInit.

  Lemma vruninit_marking_ps_assign_s_marking :
    forall {Δ σ σ' n},
      vruninit hdstore Δ σ marking_ps σ' ->
      MapsTo initial_marking (Vnat n) (sigstore σ) ->
      MapsTo s_marking (Vnat n) (sigstore σ').
  Admitted.
  
  Lemma vruninit_marking_ps_no_events_s_marking :
    forall {Δ σ σ' n},
      vruninit hdstore Δ σ marking_ps σ' ->
      InputOf Δ initial_marking ->
      MapsTo initial_marking (Vnat n) (sigstore σ) ->
      ~NatSet.In s_marking (events σ') ->
      MapsTo s_marking (Vnat n) (sigstore σ).
  Proof.
    inversion_clear 1; intros.
    match goal with
    | [ H: vseq _ _ _ _ _ _ _ |- _ ] =>
      inversion_clear H; [contradiction |]
    end.
    match goal with
    | [ H: vseq _ _ _ _ _ _ _ |- _ ] =>
      inversion H; subst; simpl
    end; [
      match goal with
      | [ H: ~NatSet.In _ _ |- _ ] =>
        elimtype False; apply H; simpl; auto with set
      end
    |
    match goal with
    | [ H: vexpr _ _ _ _ _ _ |- _ ] =>
      inversion_clear H
    end
    ].
    match goal with
    | [ H: OVEq _ _ _ |- _ ] =>
      erewrite MapsTo_fun with (e := newv) (e' := Vnat n) in H; eauto;
        inversion H; subst; auto
    end.
    match goal with
    | [ H: ~NatMap.In _ _, H': InputOf _ _ |- _ ] =>
      let Hf := fresh "H" in
      elimtype False; apply H; destruct H' as (x, Hf); exists (Input x); auto
    end.
    match goal with
    | [ H: InputOf _ _ |- _ ] => destruct H; mapsto_discriminate
    end.
  Qed.
  
  Lemma vruninit_place_s_marking_eq_nat :    
    forall Δ σ σ' n m,
      vruninit hdstore Δ σ place_behavior σ' ->
      ~NatSet.In s_marking (events σ) ->
      InputOf Δ initial_marking ->
      MapsTo s_marking (Declared (Tnat 0 m)) Δ ->
      MapsTo initial_marking (Vnat n) (sigstore σ) ->
      MapsTo s_marking (Vnat n) (sigstore σ').
  Proof.
    intros *; unfold place_behavior.
    do 2 (rewrite vruninit_par_comm; rewrite <- vruninit_par_assoc);
      rewrite <- vruninit_par_assoc.
    inversion_clear 1; intros.

    (* 2 CASES: [s_marking ∈ events σ'0] or [s_marking ∉ events σ'0] *)
    destruct (In_dec s_marking (events σ'0)).

    (* CASE [s_marking ∈ (events σ'0)] *)
    - erw_IMDS_sstore_1 <- H3; eauto.
      eapply vruninit_marking_ps_assign_s_marking; eauto with set.

    (* CASE [s_marking ∉ (events σ'0)], 
       then [σ(s_marking) = σ'0(s_marking)] *)
    - erw_IMDS_sstore_m <- H3.
      eapply vruninit_marking_ps_no_events_s_marking; eauto.
      eapply not_in_union; eauto.
      eapply vruninit_not_in_events_if_not_assigned; eauto.
      destruct 1; mapsto_discriminate.
      simpl; cbv; lia.    
  Qed.

  Lemma mapip_not_in_events_if_not_input :
    forall {Δ Δ__c : ElDesign} {σ σ__c : DState} {ipm : list associp} {σ__c' : DState} {id : key},
      mapip Δ Δ__c σ σ__c ipm σ__c' -> ~InputOf Δ__c id -> ~NatSet.In id (events σ__c) -> ~NatSet.In id (events σ__c').
  Admitted.
  
  Lemma vruninit_s_marking_eq_nat :
    forall Δ σ behavior σ',
      vruninit hdstore Δ σ behavior σ' ->
      forall id__p gm ipm opm σ__p σ__p' n Δ__p compids m,
        InCs (cs_comp id__p Petri.place_entid gm ipm opm) behavior ->
        List.In (associp_ ($initial_marking) (e_nat n)) ipm ->
        MapsTo id__p (Component Δ__p) Δ ->
        MapsTo id__p σ__p (compstore σ) ->
        InputOf Δ__p initial_marking ->
        MapsTo s_marking (Declared (Tnat 0 m)) Δ__p ->
        ~NatSet.In s_marking (events σ__p) ->
        AreCsCompIds behavior compids -> 
        List.NoDup compids ->
        NatMap.MapsTo id__p σ__p' (compstore σ') ->
        NatMap.MapsTo Place.s_marking (Vnat n) (sigstore σ__p').
  Proof.
    induction 1; try (solve [inversion 1]).

    (* CASE eventful component *)
    - inversion 1; subst; subst_place_design.
      clear IHvruninit; simpl in *.
      erewrite @MapsTo_fun with (e' := σ__c) (e := σ__p) in *; eauto.
      erewrite @MapsTo_add_eqv with (e' := σ__c'') (e := σ__p'); eauto.
      assert (e : Component Δ__p = Component Δ__c) by (eapply MapsTo_fun; eauto).
      inject_left e.
      eapply vruninit_place_s_marking_eq_nat; eauto.
      eapply mapip_not_in_events_if_not_input; eauto.
      destruct 1; mapsto_discriminate.
      edestruct @mapip_eval_simpl_associp with (Δ := Δ) as (v, (vexpr_v, MapsTo_σ__c'));
        eauto; inversion vexpr_v; subst; assumption.

    (* CASE eventless component *)
    - inversion 1; subst; subst_place_design.
      clear IHvruninit; simpl in *.
      erewrite @MapsTo_fun with (e := σ__p') (e' := σ__c); eauto;
        [ | eapply mapop_inv_compstore; eauto].
      (* [events σ__c'' = ∅ then σ__c = σ__c'' ] *)
      erewrite mapip_eq_state_if_no_events; eauto;
        erewrite vruninit_eq_state_if_no_events; eauto.
      (* With no events, s_marking ⇐ initial_marking happened,
         but both already had the same value. *)
      assert (e : Component Δ__p = Component Δ__c) by (eapply MapsTo_fun; eauto).
      inject_left e.
      eapply vruninit_place_s_marking_eq_nat; eauto.
      eapply mapip_not_in_events_if_not_input; eauto.
      destruct 1; mapsto_discriminate.
      erewrite <- @MapsTo_fun with (e := σ__p) (e' := σ__c); eauto.
      edestruct @mapip_eval_simpl_associp with (Δ := Δ) as (v, (vexpr_v, MapsTo_σ__c'));
        eauto; inversion vexpr_v; subst; assumption.

    (* CASE || *)
    - inversion_clear 1;
        destruct (AreCsCompIds_ex cstmt) as (compids1, HAreCsCompIds1);
        destruct (AreCsCompIds_ex cstmt') as (compids2, HAreCsCompIds2).
      
      (* SUBCASE [comp ∈ cstmt] *)
      + intros; eapply IHvruninit1; eauto; clear IHvruninit1 IHvruninit2.

        (* Component ids are unique in [cstmt]. *)
        eapply proj1; eapply nodup_app.
        erewrite AreCsCompIds_determ; eauto.
        eapply AreCsCompIds_app; eauto.
        
        (* 2 subcases: [id__p ∈ (events σ')] or [id__p ∉ (events σ')] *)
        destruct (In_dec id__p (events σ')).

        (* [id__p ∈ (events σ')] *)
        -- decompose_IMDS;
             match goal with
             | [H: _ -> _ -> NatSet.In _ (events σ') -> _ |- _] =>
               erewrite H; eauto
             end.

        (* [id__p ∉ (events σ')] *)
        -- eapply vruninit_inv_cstate; eauto.
           decompose_IMDS; match goal with
                           | [H: _ -> _ -> ~NatSet.In _ _ -> _ |- _] =>
                             erewrite H; eauto; eapply nIn_nIn_Union; eauto
                           end.           

           (* Prove [id__p ∉ (events σ'')] *)
           eapply vruninit_compid_not_in_events; eauto.
           apply nodup_app_not_in with (l := compids1).
           { erewrite AreCsCompIds_determ; eauto; apply AreCsCompIds_app; auto. }
           { eapply (AreCsCompIds_compid_iff HAreCsCompIds1); eauto. }

      (* SUBCASE [comp ∈ cstmt'] *)
      + intros; eapply IHvruninit2; eauto; clear IHvruninit1 IHvruninit2.

        (* Component ids are unique in [cstmt]. *)
        eapply @proj2; eapply nodup_app.
        erewrite AreCsCompIds_determ; eauto.
        eapply AreCsCompIds_app; eauto.
        
        (* 2 subcases: [id__p ∈ (events σ'')] or [id__p ∉ (events σ'')] *)
        destruct (In_dec id__p (events σ'')).

        (* [id__p ∈ (events σ'')] *)
        -- decompose_IMDS;
             match goal with
             | [H: _ -> _ -> NatSet.In _ (events σ'') -> _ |- _] =>
               erewrite H; eauto
             end.

        (* [id__p ∉ (events σ'')] *)
        -- eapply vruninit_inv_cstate; eauto.
           decompose_IMDS; match goal with
                           | [H: _ -> _ -> ~NatSet.In _ _ -> _ |- _] =>
                             erewrite H; eauto; eapply nIn_nIn_Union; eauto
                           end.           

           (* Prove [id__p ∉ (events σ')] *)
           eapply vruninit_compid_not_in_events; eauto.
           eapply nodup_app_not_in with (l := compids2).
           { eapply NoDup_app_comm.
             erewrite AreCsCompIds_determ; eauto.
             apply AreCsCompIds_app; auto. }
           { eapply (AreCsCompIds_compid_iff HAreCsCompIds2); eauto. }
  Qed.
  
End PVRunInit.

(** ** Facts about [init] and Place Design *)

Section PInit.

  Lemma init_s_marking_eq_nat :
    forall Δ σ behavior σ0,
      Initialization.init hdstore Δ σ behavior σ0 ->
      forall id__p gm ipm opm σ__p σ__p0 n Δ__p compids mm,
        InCs (cs_comp id__p Petri.place_entid gm ipm opm) behavior ->
        MapsTo id__p (Component Δ__p) Δ ->
        MapsTo id__p σ__p (compstore σ) ->
        AreCsCompIds behavior compids ->
        List.NoDup compids ->
        List.In (associp_ ($initial_marking) (e_nat n)) ipm ->
        InputOf Δ__p initial_marking ->
        MapsTo id__p σ__p0 (compstore σ0) ->
        ~NatSet.In s_marking (events σ__p) ->
        MapsTo Place.s_marking (Declared (Tnat 0 mm)) Δ__p ->
        MapsTo Place.s_marking (Vnat n) (sigstore σ__p0).
  Proof.
    inversion 1.
    intros.

    (* [∃ σ__p s.t. σ(id__p)(rst ← ⊥) = σ__p] *)
    match goal with
    | [ MapsTo_σ__p: MapsTo id__p σ__p _, Hvr: vruninit _ _ _ _ _ |- _ ] =>
      specialize (vruninit_maps_compstore_id Hvr MapsTo_σ__p) as ex_MapsTo_σp';
        inversion ex_MapsTo_σp' as (σ__p', MapsTo_σ__p'); clear ex_MapsTo_σp'
    end.
    
    (* [s_marking] value stays the same during stabilization. *)
    eapply stab_inv_s_marking; eauto.    

    (* [s_marking] takes [n] during [vruninit], if [<initial_marking => n>] *)
    eapply vruninit_s_marking_eq_nat; eauto.
  Qed.
  
End PInit.



