(** ** Facts about Evaluation of Combinational Concurrent Statement *)

Require Import common.Coqlib.
Require Import common.NatSet.

Require Import common.NatMap.
Require Import common.NatMapTactics.
Require Import common.InAndNoDup.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.Place.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.SSEvaluation.
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
  - exists σ__c; eapply vseq_inv_compstore; simpl; eauto.
    
  (* CASE comp evaluation with events.
       2 subcases, [id__c = compid] or [id__c ≠ compid] *)
  - simpl; destruct (Nat.eq_dec compid id__c).
    + exists σ__c''; rewrite e; apply NatMap.add_1; auto.
    + exists σ__c; apply NatMap.add_2; auto.
      eapply mapop_inv_compstore; eauto.

  (* CASE comp evaluation with no events. *)
  - exists σ__c; eapply mapop_inv_compstore; eauto.

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
      eapply proj1; eapply @union_empty with (s := (inter (events σ0) (events σ2))); eauto.
    }
    destruct (@IsMergedDState_ex σ σ0 σ2) as (σ4, IsMergedDState_σ4);
      (solve [do 2 decompose_IMDS; auto] || auto).
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
      eapply proj1; eapply union_empty; eauto.
      
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
      eapply proj2; eapply @union_empty; eauto.
    }
    destruct (@IsMergedDState_ex σ σ1 σ2) as (σ4, IsMergedDState_σ4);
      (solve [do 2 decompose_IMDS; auto] || auto).
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
      eapply proj1; eapply union_empty; eauto.

    (* Associativity of IsMErgeddstate relation *)
    + eapply IsMergedDState_assoc_2; eauto.
Qed.

Lemma vcomb_not_in_events_if_not_assigned :
  forall {D__s Δ σ cstmt σ' id},
    vcomb D__s Δ σ cstmt σ' ->
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
    apply not_in_union; [ apply IHvcomb1; auto | apply IHvcomb2; auto ].
Qed.

Lemma vcomb_inv_cstate :
  forall {D__s Δ σ behavior σ' id__c σ__c},
    vcomb D__s Δ σ behavior σ' ->
    MapsTo id__c σ__c (compstore σ) ->
    ~NatSet.In id__c (events σ') ->
    MapsTo id__c σ__c (compstore σ').
Proof.
  induction 1; auto.

  (* CASE eventful process *)
  - intros; eapply vseq_inv_compstore; eauto.

  (* CASE eventful component *)
  - simpl; intros.
    erewrite NatMap.add_neq_mapsto_iff; eauto.
    eapply mapop_inv_compstore; eauto.
    intro; subst;
    match goal with
    | [ H: ~NatSet.In _ _ |- _ ] => apply H; auto with set
    end.

  (* CASE eventless component *)
  - intros; eapply mapop_inv_compstore; eauto.

  (* CASE || *)
  - intros;
      decompose_IMDS;
      match goal with
      | [ H: _ -> _ -> ~NatSet.In _ _ -> _ <-> _, H': Equal _ _ |- _ ] =>
        erewrite <- H; auto; (assumption || (rewrite <- H'; assumption))
      end.
Qed.

Lemma vcomb_compid_not_in_events :
  forall {D__s Δ σ cstmt σ'},
    vcomb D__s Δ σ cstmt σ' ->
    forall {id__c Δ__c compids},
    AreCsCompIds cstmt compids ->
    MapsTo id__c (Component Δ__c) Δ ->
    ~List.In id__c compids ->
    ~NatSet.In id__c (events σ').
Proof.
  induction 1; auto with set.

  (* CASE eventful process *)
  - intros; eapply vseq_not_in_events_if_not_sig; simpl.
    1, 2: eauto with set.
    1, 2: destruct 1; mapsto_discriminate.

  (* CASE eventful component *)
  - simpl; inversion_clear 1; intros.
    rewrite add_spec; inversion_clear 1.
    match goal with
    | [ H: ~List.In _ _ |- _ ] =>
      apply H; firstorder
    end.
    eapply mapop_not_in_events_if_not_sig; eauto with set;
      destruct 1; mapsto_discriminate.
    
  (* CASE eventless component *)
  - intros; eapply mapop_not_in_events_if_not_sig; eauto with set;
    destruct 1; mapsto_discriminate.

  (* CASE || *)
  - destruct (AreCsCompIds_ex cstmt) as (compids1, AreCsCompIds_1);
      destruct (AreCsCompIds_ex cstmt') as (compids2, AreCsCompIds_2).
    do 4 intro;
      erewrite (AreCsCompIds_eq_app cstmt cstmt') with (compids'' := compids); eauto.
    intros; decompose_IMDS;
      match goal with
      | [ H: Equal (events ?A) _ |- ~NatSet.In _ (events ?A) ] =>
        rewrite H; apply not_in_union
      end.
    eapply IHvcomb1; eauto; eapply proj1; eapply not_app_in; eauto.
    eapply IHvcomb2; eauto; eapply proj2; eapply not_app_in; eauto.
Qed.


