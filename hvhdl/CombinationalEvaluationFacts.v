(** ** Facts about Evaluation of Combinational Concurrent Statement *)

Require Import common.Coqlib.
Require Import common.NatSet.

Require Import common.NatMap.
Require Import common.NatMapTactics.
Require Import common.InAndNoDup.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.Place.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.SSEvaluationFacts.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.PortMapEvaluationFacts.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.AbstractSyntaxTactics.
Require Import hvhdl.WellDefinedDesignFacts.
Require Import hvhdl.WellDefinedDesignTactics.
Require Import hvhdl.EnvironmentFacts.

(** ** Facts about [vcomb] *)

Lemma vcomb_maps_compstore_id :
  forall {D__s Δ σ behavior σ' id__c σ__c},
    vcomb D__s Δ σ behavior σ' ->
    MapsTo id__c σ__c (compstore σ) ->
    exists σ__c', MapsTo id__c σ__c' (compstore σ').
Proof.
  induction 1; try (simpl; exists σ__c; assumption).
  
  (* CASE process evaluation, no events in sl *)
  - exists σ__c; eapply vseq_inv_compstore_id; simpl; eauto.
    
  (* CASE comp evaluation with events.
       2 subcases, [id__c = compid] or [id__c ≠ compid] *)
  - simpl; destruct (Nat.eq_dec compid id__c).
    + exists σ__c''; rewrite e; apply NatMap.add_1; auto.
    + exists σ__c; apply NatMap.add_2; auto.
      eapply mapop_inv_compstore_id; eauto.

  (* CASE comp evaluation with no events. *)
  - exists σ__c; eapply mapop_inv_compstore_id; eauto.

  (* CASE par *)
  - unfold IsMergedDState in H2; apply proj2, proj1 in H2.
    unfold EqualDom in H2; rewrite <- (H2 id__c); exists σ__c; assumption.
Qed.

Lemma vcomb_par_comm :
  forall {D__s Δ σ cstmt cstmt' σ'},
    vcomb D__s Δ σ (cstmt // cstmt') σ' <->
    vcomb D__s Δ σ (cstmt' // cstmt) σ'.
Proof.
  split; inversion_clear 1.
  all :
    eapply @VCombPar; eauto;
    [ transitivity (inter (events σ'0) (events σ'')); auto with set
    | erewrite IsMergedDState_comm; auto ].
Qed.

Lemma vcomb_par_assoc :
  forall {D__s Δ σ cstmt cstmt' cstmt'' σ'},
    vcomb D__s Δ σ (cstmt // cstmt' // cstmt'') σ' <->
    vcomb D__s Δ σ ((cstmt // cstmt') // cstmt'')  σ'.
Proof.
  split.
  (* CASE A *)
  - inversion_clear 1;
      match goal with
      | [ H: vcomb _ _ _ (_ // _) _ |- _ ] => inversion_clear H
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
    destruct (@IsMergedDState_ex σ σ0 σ2) as (σ4, IsMergedDState_σ4).
    eapply @VCombPar with (σ' := σ4) (σ'' := σ3); eauto with hvhdl.
    
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
      | [ H: vcomb _ _ _ (_ // _) _ |- _ ] => inversion_clear H
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
    destruct (@IsMergedDState_ex σ σ1 σ2) as (σ4, IsMergedDState_σ4).
    eapply @VCombPar with (σ' := σ0) (σ'' := σ4); eauto with hvhdl.
    
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

Lemma vcomb_inv_cstate :
  forall {D__s Δ σ behavior σ' id__c σ__c},
    vcomb D__s Δ σ behavior σ' ->
    MapsTo id__c σ__c (compstore σ) ->
    ~NatSet.In id__c (events σ') ->
    MapsTo id__c σ__c (compstore σ').
Admitted.

Lemma vcomb_compid_not_in_events_1 :
  forall {D__s Δ σ cstmt σ' id__c Δ__c compids},
    vcomb D__s Δ σ cstmt σ' ->
    MapsTo id__c (Component Δ__c) Δ ->
    AreCsCompIds cstmt compids ->
    ~List.In id__c compids ->
    ~NatSet.In id__c (events σ) ->
    ~NatSet.In id__c (events σ').
Admitted.

Lemma vcomb_compid_not_in_events_2 :
  forall {D__s Δ σ cstmt σ' id__c Δ__c},
    vcomb D__s Δ σ cstmt σ' ->
    MapsTo id__c (Component Δ__c) Δ ->
    ~NatSet.In id__c (events σ') ->
    ~NatSet.In id__c (events σ).
Admitted.


