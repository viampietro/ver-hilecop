(** * Facts about Initialization *)

Require Import common.Coqlib.
Require Import common.NatMap.
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

  Lemma vseq_eq_state_if_no_events :
    forall {Δ σ Λ flag stmt σ' Λ'},
      vseq Δ σ Λ flag stmt σ' Λ' ->
      Equal (events σ') {[]} ->
      σ = σ'.
  Admitted.

  Lemma mapop_eq_state_if_no_events :
    forall {Δ Δ__c σ σ__c opmap σ'},
      mapop Δ Δ__c σ σ__c opmap σ' ->
      Equal (events σ') {[]} ->
      σ = σ'.
  Admitted.
  
  Lemma vruninit_eq_state_if_no_events :
    forall {D__s Δ σ cstmt σ'},
      vruninit D__s Δ σ cstmt σ' ->
      Equal (events σ') {[]} ->
      σ = σ'.
  Proof.
    induction 1; auto.
    (* CASE process *)
    eapply vseq_eq_state_if_no_events; eauto.
    (* CASE eventful component *)
    simpl; intros; exfalso; eapply add_empty_false; eauto.
    (* CASE eventless component *)
    eapply mapop_eq_state_if_no_events; eauto.
    (* CASE || *)
    rename H2 into IMDS; erw_IMDS_events_m IMDS; intros Equal_U.
  Admitted.

  Lemma vruninit_inv_cstate :
    forall {D__s Δ σ cstmt σ' id__c σ__c},
      vruninit D__s Δ σ cstmt σ' ->
      MapsTo id__c σ__c (compstore σ) ->
      ~NatSet.In id__c (events σ') ->
      MapsTo id__c σ__c (compstore σ').
  Admitted.

  Lemma vruninit_compid_not_in_events :
    forall {D__s Δ σ cstmt σ'},
      vruninit D__s Δ σ cstmt σ' ->
      forall {id__c Δ__c compids},
        AreCsCompIds cstmt compids ->
        MapsTo id__c (Component Δ__c) Δ ->
        ~List.In id__c compids ->
        ~NatSet.In id__c (events σ').
  Admitted.

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
        eapply proj1; eapply @empty_union_3 with (s := (inter (events σ0) (events σ2))); eauto.
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
        eapply proj1; eapply empty_union_3; eauto.
        
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
        eapply proj2; eapply @empty_union_3; eauto.
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
        eapply proj1; eapply empty_union_3; eauto.

      (* Associativity of IsMErgeddstate relation *)
      + eapply IsMergedDState_assoc_2; eauto.
  Qed.
  
End VRunInit.

(** ** Facts about [init] *)

Section Init.

  
End Init.
