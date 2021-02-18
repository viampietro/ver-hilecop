(** * Facts about Port Map Validity *)

Require Import common.Coqlib.

Require Import hvhdl.Environment.
Require Import hvhdl.ValidPortMap.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.StaticExpressions.

Require Import hvhdl.ExpressionEvaluationFacts.
Require Import hvhdl.StaticExpressionsFacts.

(** ** Facts about [listipm] *)

Section ListIPM.
  
  Lemma eassocip_eq_iff_eq_sigs :
    forall {Δ1 Δ__c σ1 asip formals formals' Δ2 σ2},
      EqGens Δ1 Δ2 /\ EqSigs Δ1 Δ2 ->
      EqSStore σ1 σ2 ->
      eassocip Δ1 Δ__c σ1 formals asip formals' <->
      eassocip Δ2 Δ__c σ2 formals asip formals'.
  Proof.
    split; induction 1.
    1,3: eapply EAssocipSimple; eauto;
      erewrite vexpr_eq_iff_eq_sigs; eauto;
        try ((split; symmetry; firstorder) || (symmetry; eauto)).
    all: eapply EAssocipPartial with (t := t); eauto;
      [ erewrite is_gstatic_expr_eq_iff_eq_gens; eauto;
        try ((symmetry; firstorder) || firstorder)
      | erewrite vexpr_eq_iff_eq_sigs; eauto;
        try ((split; symmetry; firstorder) || (symmetry; eauto))
      | erewrite vexpr_eq_iff_eq_sigs; eauto;
        try ((split; symmetry; firstorder) || (symmetry; eauto))
      ].
  Qed.
  
  Lemma listipm_eq_iff_eq_sigs :
    forall {Δ1 Δ__c σ1 ipm formals formals' Δ2 σ2},
      EqGens Δ1 Δ2 /\ EqSigs Δ1 Δ2 ->
      EqSStore σ1 σ2 ->
      listipm Δ1 Δ__c σ1 formals ipm formals' <->
      listipm Δ2 Δ__c σ2 formals ipm formals'.
  Proof.
    split; induction 1; auto with hvhdl;
      eapply ListIPMCons; eauto;
        erewrite eassocip_eq_iff_eq_sigs; eauto;
          [split; symmetry; firstorder | symmetry; auto].
  Qed.
  
End ListIPM.


