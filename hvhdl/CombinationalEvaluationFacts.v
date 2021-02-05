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

Lemma IsMergedDState_comm :
  forall {σ__o σ σ' σ__m},
    IsMergedDState σ__o σ σ' σ__m <->
    IsMergedDState σ__o σ' σ σ__m.
Proof.
  split; intros;
  match goal with
  | [ H: IsMergedDState _ _ _ _ |- _ ] =>
    unfold IsMergedDState in H; decompose [and] H; clear H
  end;
  let rec solve_imds :=
    match goal with
    | |- IsMergedDState _ _ _ _ => split; solve_imds
    | |- _ /\ _ => split; [solve_imds | solve_imds]
    | |- forall (_ : _) (_ : _), ~NatSet.In _ (_ U _) -> _ -> _ =>
      intros;
      match goal with
      | [ H: forall (_ : _) (_ : _), ~NatSet.In _ _ -> _ -> MapsTo _ _ (?f _),
            H': ~NatSet.In _ _ |- MapsTo _ _ (?f _) ] =>
        apply H; auto; do 1 intro; apply H';
        match goal with
        | [ H'': NatSet.In _ (_ U _) |- _ ] =>
          rewrite union_spec in H''; inversion H'';
          rewrite union_spec; [right; assumption | left; assumption]
        end
      end
    | |- Equal _ (events ?σ U events ?σ') =>
      transitivity (events σ' U events σ); auto with set
    | _ => firstorder
    end in solve_imds.
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

Lemma IsMergedDState_ex :
  forall {σ__o σ σ'}, exists σ__m, IsMergedDState σ__o σ σ' σ__m.
Admitted.

Lemma vcomb_par_assoc :
  forall {D__s Δ σ cstmt cstmt' cstmt'' σ'},
    vcomb D__s Δ σ (cstmt // cstmt' // cstmt'') σ' <->
    vcomb D__s Δ σ ((cstmt // cstmt') // cstmt'')  σ'.
Proof.
  split.
  (* CASE A *)
  - inversion_clear 1.
    inversion_clear H1.
    rename σ'0 into σ0, σ'' into σ1, σ'1 into σ2, σ''0 into σ3.
    assert (Equal (inter (events σ0) (events σ2)) {[]}) by admit.
    destruct (@IsMergedDState_ex σ σ0 σ2) as (σ4, IsMergedDState_σ4).
    eapply @VCombPar with (σ' := σ4) (σ'' := σ3); eauto with hvhdl.
    + admit.
    + unfold IsMergedDState in *. decompose [and] H3; clear H3.
      decompose [and] IsMergedDState_σ4; clear IsMergedDState_σ4.
      decompose [and] H6; clear H6.
      split. assumption.
      split. assumption.
      split. intros *; rewrite H24.
      rewrite union_spec; inversion 1.
Admitted

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


