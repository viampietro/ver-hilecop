(** * Facts about Initialization *)

Require Import common.CoqLib.
Require Import common.CoqTactics.
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
Require Import hvhdl.SSEvaluation.

Require Import hvhdl.StabilizeFacts.
Require Import hvhdl.SSEvaluationFacts.
Require Import hvhdl.PortMapEvaluationFacts.
Require Import hvhdl.EnvironmentFacts.
Require Import hvhdl.WellDefinedDesignFacts.

Require Import hvhdl.EnvironmentTactics.

(** ** Facts about [vruninit] *)

Section VRunInit.
             
  Lemma vruninit_maps_compstore_id :
    forall {D__s Δ σ behavior σ' id__c σ__c},
      vruninit D__s Δ σ behavior σ' ->
      MapsTo id__c σ__c (compstore σ) ->
      exists σ__c', MapsTo id__c σ__c' (compstore σ').
  Proof.
    induction 1.
    
    (* CASE process evaluation *)
    - exists σ__c; eapply vseq_inv_compstore; eauto.
      
    (* CASE comp evaluation with events.
       2 subcases, [id__c = compid] or [id__c ≠ compid] *)
    - simpl; destruct (Nat.eq_dec compid id__c).
      + exists σ__c''; rewrite e; apply NatMap.add_1; auto.
      + exists σ__c; apply NatMap.add_2; auto.
        eapply mapop_inv_compstore; eauto.

    (* CASE comp evaluation with no events. *)
    - exists σ__c; eapply mapop_inv_compstore; eauto.

    (* CASE null *)
    - exists σ__c; assumption.

    (* CASE par *)
    - unfold IsMergedDState in H2; apply proj2, proj1 in H2.
      unfold EqualDom in H2; rewrite <- (H2 id__c); exists σ__c; assumption.
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
      MapsTo id__c σ__c (compstore σ) ->
      ~NatSet.In id__c (events σ') ->
      MapsTo id__c σ__c (compstore σ').
  Proof.
    induction 1; auto; simpl.
    (* CASE process *)
    intros; eapply vseq_inv_compstore; eauto.
    (* CASE eventful comp *)
    intros; eapply NatMap.add_2; eauto.
    intro; subst; contrad_not_in_add.
    eapply mapop_inv_compstore; eauto.
    (* CASE eventless comp *)
    intros; eapply mapop_inv_compstore; eauto.
    (* CASE || *)
    rename H2 into IMDS; intros.
    erw_IMDS_cstore_m <- IMDS; auto.
    erw_IMDS_events_m <- IMDS; auto.
  Qed.

  Lemma AreCsCompIds_ex_app :
    forall (cstmt1 cstmt2 : cs) (compids : list ident),
      AreCsCompIds (cstmt1 // cstmt2) compids ->
      exists compids1 compids2,
        AreCsCompIds cstmt1 compids1 /\
        AreCsCompIds cstmt2 compids2 /\ 
        compids = compids1 ++ compids2.
  Admitted.
  
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
    edestruct AreCsCompIds_ex_app
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

  Lemma init_maps_compstore_id :
    forall {D__s Δ σ behavior σ' id__c σ__c},
      init D__s Δ σ behavior σ' ->
      MapsTo id__c σ__c (compstore σ) ->
      exists σ__c', MapsTo id__c σ__c' (compstore σ').
  Admitted.
  
  Lemma init_maps_sstore_of_comp_Varr :
    forall {D__s Δ σ behavior σ0 id__c id__e gm ipm opm σ__c σ__c0 id aofv},
      init D__s Δ σ behavior σ0 ->
      InCs (cs_comp id__c id__e gm ipm opm) behavior ->
      MapsTo id__c σ__c (compstore σ) ->
      MapsTo id__c σ__c0 (compstore σ0) ->
      MapsTo id (Varr aofv) (sigstore σ__c) ->
      exists aofv', MapsTo id (Varr aofv') (sigstore σ__c0).
  Admitted.

  Lemma init_inv_type_sstore :
    forall {D__s Δ σ behavior σ0 id__c id__e gm ipm opm id v v' t},
      init D__s Δ σ behavior σ0 ->
      InCs (cs_comp id__c id__e gm ipm opm) behavior ->
      MapsTo id v (sigstore σ) ->
      MapsTo id v' (sigstore σ0) ->
      is_of_type v t ->
      is_of_type v' t.
  Admitted.
  
  Lemma init_inv_type_sstore_of_comp :
    forall {D__s Δ σ behavior σ0 id__c id__e gm ipm opm σ__c σ__c0 id v v' t},
      init D__s Δ σ behavior σ0 ->
      InCs (cs_comp id__c id__e gm ipm opm) behavior ->
      MapsTo id__c σ__c (compstore σ) ->
      MapsTo id v (sigstore σ__c) ->
      MapsTo id__c σ__c0 (compstore σ0) ->
      MapsTo id v' (sigstore σ__c0) ->
      is_of_type v t ->
      is_of_type v' t.
  Admitted.
  
End Init.
