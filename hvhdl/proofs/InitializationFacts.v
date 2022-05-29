(** * Facts about Initialization *)

Require Import common.CoqLib.
Require Import common.proofs.CoqTactics.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.
Require Import common.NatSet.
Require Import common.InAndNoDup.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.HVhdlHilecopLib.

Require Import hvhdl.proofs.StabilizeFacts.
Require Import hvhdl.proofs.SSEvaluationFacts.
Require Import hvhdl.proofs.PortMapEvaluationFacts.
Require Import hvhdl.proofs.EnvironmentFacts.
Require Import hvhdl.proofs.WellDefinedDesignFacts.
Require Import hvhdl.proofs.SSEvaluationFacts.

Require Import hvhdl.proofs.EnvironmentTactics.

(** ** Facts about [vruninit] *)

Section VRunInit.
             
  Lemma vruninit_maps_cstore_id :
    forall {D__s Δ σ behavior σ' id__c σ__c},
      vruninit D__s Δ σ behavior σ' ->
      MapsTo id__c σ__c (cstore σ) ->
      exists σ__c', MapsTo id__c σ__c' (cstore σ').
  Proof.
    induction 1.
    
    (* CASE process evaluation *)
    - exists σ__c; eapply vseq_inv_cstore; eauto.
      
    (* CASE comp evaluation with events.
       2 subcases, [id__c = compid] or [id__c ≠ compid] *)
    - simpl; destruct (Nat.eq_dec compid id__c).
      + exists σ__c''; rewrite e; apply NatMap.add_1; auto.
      + exists σ__c; apply NatMap.add_2; auto.
        eapply mapop_inv_cstore; eauto.

    (* CASE comp evaluation with no events. *)
    - exists σ__c; eapply mapop_inv_cstore; eauto.

    (* CASE null *)
    - exists σ__c; assumption.

    (* CASE par *)
    - unfold IsMergedDState in H2; apply proj2, proj1 in H2.
      unfold EqualDom in H2; rewrite <- (H2 id__c); exists σ__c; assumption.
  Qed.
  
  Lemma vruninit_maps_sstore :
    forall {D__s Δ σ behavior σ'},
      vruninit D__s Δ σ behavior σ' ->
      forall {id v},
        MapsTo id v (sstore σ) ->
        exists v', MapsTo id v' (sstore σ').
  Proof.
    induction 1.
    
    (* CASE process evaluation *)
    - eapply vseq_maps_sstore; eauto.
      
    (* CASE comp evaluation with events. *)
    - cbn; eapply mapop_maps_sstore; eauto.

    (* CASE comp evaluation with no events. *)
    - cbn; eapply mapop_maps_sstore; eauto.

    (* CASE null *)
    - do 2 intro; exists v; assumption.

    (* CASE par *)
    - rename H2 into IMDS; intros.
      apply proj1 in IMDS; unfold EqualDom in IMDS.
      rewrite <- (IMDS id); exists v; assumption.        
  Qed.

  Lemma vruninit_compid_in_events_comp_in_cs :
    forall {D__s Δ σ behavior σ'},
      vruninit D__s Δ σ behavior σ' ->
      forall {id__c},
        CompOf Δ id__c ->
        ~NatSet.In id__c (events σ) ->
        NatSet.In id__c (events σ') ->
        exists id__e gm ipm opm,
          InCs (cs_comp id__c id__e gm ipm opm) behavior.
  Proof.
    induction 1.

    (* CASE process *)
    - intros id__c CompOf_; intros; exfalso.
      eapply vseq_not_in_events_if_not_sig; eauto.
      destruct 1; destruct CompOf_; mapsto_discriminate.
      destruct 1; destruct CompOf_; mapsto_discriminate.
      
    (* CASE eventful comp *)
    - cbn; intros id__c CompOf_.
      rewrite add_iff; inversion 2.
      subst compid; exists entid, gmap, ipmap, opmap; reflexivity.
      exfalso.
      eapply mapop_not_in_events_if_not_sig; eauto.
      destruct 1; destruct CompOf_; mapsto_discriminate.
      destruct 1; destruct CompOf_; mapsto_discriminate.

    (* CASE eventless comp *)
    - cbn; intros id__c CompOf_; intros.
      exfalso.
      eapply mapop_not_in_events_if_not_sig; eauto.
      destruct 1; destruct CompOf_; mapsto_discriminate.
      destruct 1; destruct CompOf_; mapsto_discriminate.

    (* CASE cs_null *)
    - contradiction.

    (* CASE || *)
    - rename H2 into IMDS; intros id__c CompOf_.
      erw_IMDS_events_m IMDS.
      rewrite union_spec; inversion 2.
      edestruct IHvruninit1 as (id__e, (g, (i, (o, InCs_)))); eauto.
      exists id__e, g, i, o; cbn; left; assumption.
      edestruct IHvruninit2 as (id__e, (g, (i, (o, InCs_)))); eauto.
      exists id__e, g, i, o; cbn; right; assumption.
  Qed.

  Lemma vruninit_is_compof_if_in_cs :
    forall {D__s Δ σ behavior σ'},
      vruninit D__s Δ σ behavior σ' ->
      forall {id__c id__e gm ipm opm},
        InCs (cs_comp id__c id__e gm ipm opm) behavior ->
        CompOf Δ id__c.
  Proof.
    induction 1; try (solve [inversion 1]).

    (* CASE eventful comp *)
    - inversion 1; subst; unfold CompOf; eauto.

    (* CASE eventless comp *)
    - inversion 1; subst; unfold CompOf; eauto.

    (* CASE || *)
    - inversion 1; eauto.
  Qed.

  Lemma vruninit_inv_not_in_events :
    forall {D__s Δ σ cstmt σ' id},
      vruninit D__s Δ σ cstmt σ' ->
      ~NatSet.In id (events σ') ->
      ~NatSet.In id (events σ).
  Proof.
    induction 1.

    (* CASE process *)
    - eapply vseq_inv_not_in_events; eauto.
    (* CASE eventful comp *)
    - cbn; intros nIn_ev; intro.
      apply nIn_ev; rewrite add_iff; right.
      eapply mapop_inv_in_events; eauto.
    (* CASE eventless comp *)
    - cbn; intros nIn_ev; intro; apply nIn_ev.
      eapply mapop_inv_in_events; eauto.
    (* CASE cs_null *)
    - auto.
    (* CASE || *)
    - rename H2 into IMDS; erw_IMDS_events_m IMDS.
      intros nIn_U In_ev.
      edestruct not_in_union_2 as (nIn_ev', nIn_ev''); eauto.
      eapply IHvruninit1; eauto.
  Qed.
  
  Lemma vruninit_maps_sstore_of_comp :
    forall {D__s Δ σ behavior σ'},
      vruninit D__s Δ σ behavior σ' ->
      forall {id__c id__e gm ipm opm σ__c σ'__c id v},
        InCs (cs_comp id__c id__e gm ipm opm) behavior ->
        MapsTo id__c σ__c (cstore σ) ->
        MapsTo id v (sstore σ__c) ->
        MapsTo id__c σ'__c (cstore σ') ->
        exists v', MapsTo id v' (sstore σ'__c).
  Proof.
    induction 1; try (solve [inversion 1]).
    (* CASE comp evaluation with events.*)
    - inversion_clear 1; cbn; intros.
      erewrite @MapsTo_add_eqv with (e := σ'__c) (e' := σ__c''); eauto.
      edestruct @mapip_maps_sstore with (Δ := Δ); eauto.
      erewrite <- MapsTo_fun with (e := σ__c0) (e' := σ__c); eauto.
      eapply vruninit_maps_sstore; eauto.
    (* CASE comp evaluation with no events.*)
    - inversion_clear 1; cbn; intros.
      exists v.
      assert (MapsTo compid σ__c (cstore σ'))
        by (eapply mapop_inv_cstore; eauto).      
      erewrite <- MapsTo_fun with (e := σ__c) (e' := σ'__c); eauto.
      erewrite <- MapsTo_fun with (e := σ__c0) (e' := σ__c); eauto.
    (* CASE || *)
    - rename H2 into IMDS; intros until σ__c; intros σ__mc.

      (* 2 CASES: [comp ∈ cs] or [comp ∈ cs'] *)
      inversion_clear 1; intros.

      (* CASE [comp ∈ cs] *)
      + (* 2 CASES: [id__c ∈ events σ'] or [id__c ∉ events σ'] *)
        destruct (In_dec id__c (events σ')) as [ In_ev' | nIn_ev' ].
        (* CASE [id__c ∈ events σ'] *)
        -- eapply IHvruninit1; eauto.
           erw_IMDS_cstore_1 IMDS; eauto.

        (* CASE [id__c ∉ events σ'] *)
        -- (* 2 CASES: [id__c ∈ events σ''] or [id__c ∉ events σ''] *)
          destruct (In_dec id__c (events σ'')) as [ In_ev'' | nIn_ev'' ].

          (* CASE [id__c ∈ events σ''] *)
          ++ edestruct @vruninit_compid_in_events_comp_in_cs with (D__s := D__s) (id__c := id__c)
              as (id__e', (g, (i, (o, InCs_)))); eauto.
             eapply @vruninit_is_compof_if_in_cs with (behavior := cstmt); eauto.
             eapply @vruninit_inv_not_in_events  with (cstmt := cstmt); eauto.
             eapply IHvruninit2; eauto.
             erw_IMDS_cstore_2 IMDS; eauto.

          (* CASE [id__c ∉ events σ''] *)
          ++ assert (eq_cstate: σ__c = σ__mc).
             { eapply MapsTo_fun; eauto.
               erw_IMDS_cstore_m IMDS; eauto.
               eapply not_in_union; eauto. }
             rewrite <- eq_cstate; exists v; assumption.

      (* CASE [comp ∈ cs'] *)
      + (* 2 CASES: [id__c ∈ events σ''] or [id__c ∉ events σ''] *)
        destruct (In_dec id__c (events σ'')) as [ In_ev'' | nIn_ev'' ].
        (* CASE [id__c ∈ events σ''] *)
        -- eapply IHvruninit2; eauto.
           erw_IMDS_cstore_2 IMDS; eauto.

        (* CASE [id__c ∉ events σ''] *)
        -- (* 2 CASES: [id__c ∈ events σ'] or [id__c ∉ events σ'] *)
          destruct (In_dec id__c (events σ')) as [ In_ev' | nIn_ev' ].

          (* CASE [id__c ∈ events σ'] *)
          ++ edestruct @vruninit_compid_in_events_comp_in_cs
            with (D__s := D__s) (id__c := id__c) (behavior := cstmt)
              as (id__e', (g, (i, (o, InCs_)))); eauto.
             eapply @vruninit_is_compof_if_in_cs with (behavior := cstmt'); eauto.
             eapply @vruninit_inv_not_in_events  with (cstmt := cstmt'); eauto.
             eapply IHvruninit1; eauto.
             erw_IMDS_cstore_1 IMDS; eauto.

          (* CASE [id__c ∉ events σ'] *)
          ++ assert (eq_cstate: σ__c = σ__mc).
             { eapply MapsTo_fun; eauto.
               erw_IMDS_cstore_m IMDS; eauto.
               eapply not_in_union; eauto. }
             rewrite <- eq_cstate; exists v; assumption.
  Qed.
  
  Lemma vruninit_eq_state_if_no_events :
    forall {D__s Δ σ cstmt σ'},
      vruninit D__s Δ σ cstmt σ' ->
      Equal (events σ') {[]} ->
      EqDState σ σ'.
  Proof.
    induction 1; try reflexivity.
    (* CASE process *)
    intro; erewrite vseq_eq_state_if_no_events; eauto; reflexivity.
    (* CASE eventful component *)
    simpl; intros; exfalso; eapply add_empty_false; eauto.
    (* CASE eventless component *)
    intro; erewrite mapop_eq_state_if_no_events; eauto; reflexivity.
    (* CASE || *)
    rename H2 into IMDS; erw_IMDS_events_m IMDS; intros Equal_U.
    unfold EqDState; split_and.
    unfold EqSStore; intros.
    erw_IMDS_sstore_m IMDS; try reflexivity.
    intros In_empty; rewrite Equal_U in In_empty;
      rewrite empty_iff in In_empty; contradiction.
    unfold EqCStore; intros.
    erw_IMDS_cstore_m IMDS; try reflexivity.
    intros In_empty; rewrite Equal_U in In_empty;
      rewrite empty_iff in In_empty; contradiction.
    unfold EqEvs.
    erw_IMDS_events_m IMDS; rewrite Equal_U.
    rewrite IHvruninit1; apply (union_empty_l Equal_U).    
  Qed.

  Lemma vruninit_inv_cstate :
    forall {D__s Δ σ cstmt σ' id__c σ__c},
      vruninit D__s Δ σ cstmt σ' ->
      MapsTo id__c σ__c (cstore σ) ->
      ~NatSet.In id__c (events σ') ->
      MapsTo id__c σ__c (cstore σ').
  Proof.
    induction 1; auto; simpl.
    (* CASE process *)
    intros; eapply vseq_inv_cstore; eauto.
    (* CASE eventful comp *)
    intros; eapply NatMap.add_2; eauto.
    intro; subst; contrad_not_in_add.
    eapply mapop_inv_cstore; eauto.
    (* CASE eventless comp *)
    intros; eapply mapop_inv_cstore; eauto.
    (* CASE || *)
    rename H2 into IMDS; intros.
    erw_IMDS_cstore_m <- IMDS; auto.
    erw_IMDS_events_m <- IMDS; auto.
  Qed.
  
  Lemma vruninit_compid_not_in_events :
    forall {D__s Δ σ cstmt σ'},
      vruninit D__s Δ σ cstmt σ' ->
      forall {id__c Δ__c compids},
        AreCsCompIds cstmt compids ->
        Equal (events σ) {[]} ->
        MapsTo id__c (Component Δ__c) Δ ->
        ~List.In id__c compids ->
        ~NatSet.In id__c (events σ').
  Proof.
    induction 1; auto; simpl.
    (* CASE process *)
    intros *; intros AreCsCompIds_ Equal_empty; intros.
    eapply vseq_not_in_events_if_not_sig; eauto.
    rewrite Equal_empty; auto with set.
    1,2 : destruct 1; mapsto_discriminate.
    (* CASE eventful component *)
    inversion 1; subst; intros Equal_emp MapsTo_comp nIn_compid.
    rewrite add_spec; destruct 1; [subst; apply nIn_compid; auto with datatypes | ].
    eapply mapop_not_in_events_if_not_sig; eauto.
    rewrite Equal_emp; auto with set.
    1,2 : destruct 1; mapsto_discriminate.
    (* CASE eventless component *)
    inversion 1; subst; intros Equal_emp MapsTo_comp nIn_compid.
    eapply mapop_not_in_events_if_not_sig; eauto.
    rewrite Equal_emp; auto with set.
    1,2 : destruct 1; mapsto_discriminate.
    (* CASE Null *)
    do 4 intro; intros Equal_emp MapsTo_comp nIn_compid.
    rewrite Equal_emp; auto with set.
    (* CASE || *)
    intros *; intros AreCsCompIds_par Equal_emp MapsTo_comp nIn_compids.
    rename H2 into IMDS; erw_IMDS_events_m IMDS.
    edestruct @AreCsCompIds_ex_app with (cstmt1 := cstmt)
      as (compids1, (compids2, (AreCsCompIds1, (AreCsCompIds2, e))));
      eauto; subst.      
    apply not_in_union; [eapply IHvruninit1; eauto with datatypes
                        | eapply IHvruninit2; eauto with datatypes].
  Qed.

  Lemma vruninit_not_in_events_if_not_assigned :
    forall {D__s Δ σ cstmt σ' id},
      vruninit D__s Δ σ cstmt σ' ->
      ~NatSet.In id (events σ) ->
      ~CompOf Δ id ->
      ~AssignedInCs id cstmt ->
      ~NatSet.In id (events σ').
  Proof.
    induction 1; (try (solve [simpl; auto with set])).
    
    (* CASE eventful process *)
    - simpl; intros; eapply vseq_not_in_events_if_not_assigned; eauto with set.

    (* CASE eventful component *)
    - simpl; intros.
      erewrite add_spec; inversion_clear 1;
        [ subst; match goal with
                 | [ H: ~CompOf _ _ |- _ ] =>
                   apply H; exists Δ__c; auto
                 end
        | eapply mapop_not_in_events_if_not_assigned; eauto with set].

    (* CASE eventless component *)
    - simpl; intros;
        eapply mapop_not_in_events_if_not_assigned; eauto with set.

    (* CASE || *)
    - simpl; intros.
      decompose_IMDS; match goal with | [ H: Equal _ _ |- _ ] => rewrite H end.
      apply not_in_union; [ apply IHvruninit1; auto | apply IHvruninit2; auto ].
  Qed.
  
  Lemma vruninit_inv_well_typed_values_in_sstore :
    forall {D__s Δ σ behavior σ'},
      vruninit D__s Δ σ behavior σ' ->
      (forall {id t v},
          (MapsTo id (Declared t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
          MapsTo id v (sstore σ) ->
          IsOfType v t) ->
      forall {id t v},
        (MapsTo id (Declared t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
        MapsTo id v (sstore σ') ->
        IsOfType v t.
  Proof.
    induction 1; intros WT; try (solve [trivial]).
    (* CASE process *)
    - eapply vseq_inv_well_typed_values_in_sstore; eauto.
    (* CASE eventful component *)
    - cbn; eapply mapop_inv_well_typed_values_in_sstore; eauto.
    (* CASE eventless component *)
    - cbn; eapply mapop_inv_well_typed_values_in_sstore; eauto.
    (* CASE || *)
    - specialize (IHvruninit1 WT); specialize (IHvruninit2 WT).
      intros *; intros MapsTo_Δ MapsTo_sstore_m.
      rename H2 into IMDS.
      (* 2 CASES: [id ∈ events σ'] or [id ∉ events σ'] *)
      destruct (In_dec id (events σ')) as [ In_ev' | nIn_ev' ].
      (* CASE [id ∈ events σ'] *)
      + eapply IHvruninit1; eauto.
         erw_IMDS_sstore_1 IMDS; eauto.
      (* CASE [id ∉ events σ'] *)
      + (* 2 CASES: [id ∈ events σ''] or [id ∉ events σ''] *)
        destruct (In_dec id (events σ'')) as [ In_ev'' | nIn_ev'' ].
        (* CASE [id ∈ events σ''] *)
        -- eapply IHvruninit2; eauto.
           erw_IMDS_sstore_2 IMDS; eauto.
        (* CASE [id ∉ events σ''] *)
        -- eapply WT; eauto.
           erw_IMDS_sstore_m IMDS; eauto.
           eapply not_in_union; eauto.
  Qed.
  
  Lemma vruninit_inv_well_typed_values_in_sstore_of_comp :
    forall {D__s Δ σ behavior σ'},
      vruninit D__s Δ σ behavior σ' ->
      (forall {id__c Δ__c σ__c},
          MapsTo id__c (Component Δ__c) Δ ->
          MapsTo id__c σ__c (cstore σ) ->
          forall {id t v},
            (MapsTo id (Declared t) Δ__c \/ MapsTo id (Input t) Δ__c \/ MapsTo id (Output t) Δ__c) ->
            MapsTo id v (sstore σ__c) ->
            IsOfType v t) ->
      forall {id__c Δ__c σ'__c},
        MapsTo id__c (Component Δ__c) Δ ->
        MapsTo id__c σ'__c (cstore σ') ->
        forall {id t v},
          (MapsTo id (Declared t) Δ__c \/ MapsTo id (Input t) Δ__c \/ MapsTo id (Output t) Δ__c) ->
          MapsTo id v (sstore σ'__c) ->
          IsOfType v t.
  Proof.
    induction 1; intros WT; trivial.
    (* CASE process *)
    - intros; eapply WT; eauto.
      eapply vseq_inv_cstore_2; eauto.
    (* CASE eventful component *)
    - cbn; do 5 intro.
      (* 2 CASES: [id__c = compid] or [id__c ≠ compid] *)
      destruct (Nat.eq_dec id__c compid) as [ eq_ | neq_ ].
      (* CASE [id__c = compid] *)
      + rewrite eq_ in *; intros.
        assert (eq_Δ : Component Δ__c0 = Component Δ__c) by (eauto with mapsto).
        inject_left eq_Δ; eauto.
        eapply vruninit_inv_well_typed_values_in_sstore; eauto.
        eapply mapip_inv_well_typed_values_in_sstore; eauto.
        erewrite <- @MapsTo_add_eqv with (e := σ'__c) (e' := σ__c''); eauto.
      (* CASE [id__c ≠ compid] *)
      + assert (MapsTo id__c σ'__c (cstore σ)) by
         (eapply mapop_inv_cstore_2; eauto with mapsto).
        eapply WT; eauto.
    (* CASE eventless component *)
    - cbn; do 5 intro.
      assert (MapsTo id__c σ'__c (cstore σ)) by
          (eapply mapop_inv_cstore_2; eauto with mapsto).
      eapply WT; eauto.
    (* CASE || *)
    - specialize (IHvruninit1 WT); specialize (IHvruninit2 WT).
      intros *; intros MapsTo_Δ__c MapsTo_cstore_m.
      rename H2 into IMDS.
      (* 2 CASES: [id__c ∈ events σ'] or [id__c ∉ events σ'] *)
      destruct (In_dec id__c (events σ')) as [ In_ev' | nIn_ev' ].
      (* CASE [id__c ∈ events σ'] *)
      + eapply IHvruninit1; eauto.
         erw_IMDS_cstore_1 IMDS; eauto.

      (* CASE [id__c ∉ events σ'] *)
      + (* 2 CASES: [id__c ∈ events σ''] or [id__c ∉ events σ''] *)
        destruct (In_dec id__c (events σ'')) as [ In_ev'' | nIn_ev'' ].

        (* CASE [id__c ∈ events σ''] *)
        -- eapply IHvruninit2; eauto.
           erw_IMDS_cstore_2 IMDS; eauto.

        (* CASE [id__c ∉ events σ''] *)
        -- eapply WT; eauto.
           erw_IMDS_cstore_m IMDS; eauto.
           eapply not_in_union; eauto.
  Qed.  
  
  Lemma vruninit_par_comm :
    forall {D__s Δ σ cstmt cstmt' σ'},
      vruninit D__s Δ σ (cstmt // cstmt') σ' <->
      vruninit D__s Δ σ (cstmt' // cstmt) σ'.
  Proof.
    split; inversion_clear 1.
    all :
      eapply @VRunInitPar; eauto;
      [ transitivity (inter (events σ'0) (events σ'')); auto with set
      | erewrite IsMergedDState_comm; auto ].
  Qed.

  Lemma vruninit_par_assoc :
    forall {D__s Δ σ cstmt cstmt' cstmt'' σ'},
      vruninit D__s Δ σ (cstmt // cstmt' // cstmt'') σ' <->
      vruninit D__s Δ σ ((cstmt // cstmt') // cstmt'')  σ'.
  Proof.
    split.
    (* CASE A *)
    - inversion_clear 1;
        match goal with
        | [ H: vruninit _ _ _ (_ // _) _ |- _ ] => inversion_clear H
        end;
        rename σ'0 into σ0, σ'' into σ1, σ'1 into σ2, σ''0 into σ3.

      assert (Equal (inter (events σ0) (events σ2)) {[]}).
      {
        do 2 decompose_IMDS.
        assert (Equal_empty : Equal (inter (events σ0) (events σ2 U events σ3)) {[]})
          by (match goal with
              | [ H: Equal _ ?u |- Equal (_ _ ?u) _ ] => rewrite <- H
              end; assumption).
        apply empty_is_empty_1.
        rewrite inter_sym, union_inter_1, inter_sym in Equal_empty.
        eapply proj1; eapply @union_empty with (s := (inter (events σ0) (events σ2))); eauto.
      }
      destruct (@IsMergedDState_ex σ σ0 σ2) as (σ4, IsMergedDState_σ4);
        (solve [do 2 decompose_IMDS; auto] || auto).
      eapply @VRunInitPar with (σ' := σ4) (σ'' := σ3); eauto with hvhdl.
      
      (* [events σ4 ∩ events σ3 = ∅] *)
      + do 3 decompose_IMDS.
        match goal with
        | [ H: Equal ?ev _ |- Equal (_ ?ev _) _] =>
          rewrite H; rewrite union_inter_1
        end.      
        match goal with
        | [ H: Equal ?i {[]} |- Equal (_ U ?i) {[]} ] =>
          rewrite H; apply empty_union_1
        end.
        assert (Equal_empty : Equal (inter (events σ0) ((events σ2) U (events σ3))) {[]})
          by (match goal with
              | [ H: Equal _ ?A  |- Equal (inter _ ?A) _ ] =>
                rewrite <- H
              end; assumption).
        rewrite inter_sym, union_inter_1, union_sym, inter_sym in Equal_empty.
        eapply proj1; eapply union_empty; eauto.
        
      (* Associativity of IsMErgeddstate relation *)
      + eapply IsMergedDState_assoc_1; eauto.

    (* CASE B *)
    - inversion_clear 1;
        match goal with
        | [ H: vruninit _ _ _ (_ // _) _ |- _ ] => inversion_clear H
        end.
      rename σ'1 into σ0, σ''0 into σ1, σ'' into σ2, σ'0 into σ3.
      assert (Equal (inter (events σ1) (events σ2)) {[]}).
      {
        do 2 decompose_IMDS.
        assert (Equal_empty : Equal (inter (events σ0 U events σ1) (events σ2) ) {[]})
          by (match goal with
              | [ H: Equal _ ?u |- Equal (_ ?u _) _ ] => rewrite <- H
              end; assumption).
        apply empty_is_empty_1.
        rewrite union_inter_1 in Equal_empty.
        eapply proj2; eapply @union_empty; eauto.
      }
      destruct (@IsMergedDState_ex σ σ1 σ2) as (σ4, IsMergedDState_σ4);
        (solve [do 2 decompose_IMDS; auto] || auto).
      eapply @VRunInitPar with (σ' := σ0) (σ'' := σ4); eauto with hvhdl.
      
      (* [events σ0 ∩ events σ4 = ∅] *)
      + do 3 decompose_IMDS.
        match goal with
        | [ H: Equal ?ev _ |- Equal (_ _ ?ev) _ ] =>
          rewrite H; rewrite inter_sym; rewrite union_inter_1
        end.
        rewrite inter_sym, union_sym.
        match goal with
        | [ H: Equal ?i {[]} |- Equal (_ U ?i) {[]} ] =>
          rewrite H; apply empty_union_1
        end.
        rewrite inter_sym.
        assert (Equal_empty : Equal (inter (events σ0 U events σ1) (events σ2)) {[]})
          by (match goal with
              | [ H: Equal _ ?A  |- Equal (_ ?A  _) _ ] =>
                rewrite <- H
              end; assumption).
        rewrite union_inter_1 in Equal_empty.
        eapply proj1; eapply union_empty; eauto.

      (* Associativity of IsMErgeddstate relation *)
      + eapply IsMergedDState_assoc_2; eauto.
  Qed.
  
End VRunInit.

(** ** Facts about [init] *)

Section Init.

  Lemma init_maps_cstore_id :
    forall {D__s Δ σ behavior σ' id__c σ__c},
      init D__s Δ σ behavior σ' ->
      MapsTo id__c σ__c (cstore σ) ->
      exists σ__c', MapsTo id__c σ__c' (cstore σ').
  Proof.
    inversion 1; intro.
    edestruct @vruninit_maps_cstore_id with (D__s := D__s); eauto.
    eapply @stab_maps_cstore_id; eauto.
  Qed.
  
  Lemma init_maps_sstore_of_comp :
    forall {D__s Δ σ behavior σ0 id__c id__e gm ipm opm σ__c σ__c0 id v},
      init D__s Δ σ behavior σ0 ->
      InCs (cs_comp id__c id__e gm ipm opm) behavior ->
      MapsTo id__c σ__c (cstore σ) ->
      MapsTo id v (sstore σ__c) ->
      MapsTo id__c σ__c0 (cstore σ0) ->
      exists v', MapsTo id v' (sstore σ__c0).
  Proof.
    inversion_clear 1; intros.
    edestruct @vruninit_maps_cstore_id with (D__s := D__s); eauto.
    edestruct @vruninit_maps_sstore_of_comp with (D__s := D__s); eauto.
    eapply stab_maps_sstore_of_comp; eauto.    
  Qed.

  Lemma init_inv_well_typed_values_in_sstore_of_comp :
    forall {D__s Δ σ behavior σ0},
      init D__s Δ σ behavior σ0 ->
      (forall {id__c Δ__c σ__c},
          MapsTo id__c (Component Δ__c) Δ ->
          MapsTo id__c σ__c (cstore σ) ->
          forall {id t v},
            (MapsTo id (Declared t) Δ__c \/ MapsTo id (Input t) Δ__c \/ MapsTo id (Output t) Δ__c) ->
            MapsTo id v (sstore σ__c) ->
            IsOfType v t) ->
      forall {id__c Δ__c σ__c0},
        MapsTo id__c (Component Δ__c) Δ ->
        MapsTo id__c σ__c0 (cstore σ0) ->
        forall {id t v},
          (MapsTo id (Declared t) Δ__c \/ MapsTo id (Input t) Δ__c \/ MapsTo id (Output t) Δ__c) ->
          MapsTo id v (sstore σ__c0) ->
          IsOfType v t.
  Proof.
    inversion 1; intros WT.
    eapply stab_inv_well_typed_values_in_sstore_of_comp; eauto.
    eapply vruninit_inv_well_typed_values_in_sstore_of_comp; eauto.
  Qed.

End Init.
