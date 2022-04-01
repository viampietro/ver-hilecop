(** * Facts about Port Map Validity *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.NatSet.

Require Import hvhdl.Environment.
Require Import hvhdl.ValidPortMap.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.StaticExpressions.
Require Import hvhdl.HVhdlTypes.

Require Import hvhdl.proofs.ExpressionEvaluationFacts.
Require Import hvhdl.proofs.StaticExpressionsFacts.
Require Import hvhdl.proofs.EnvironmentFacts.

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
    all: eapply EAssocipPartial with (t := t0); eauto;
      [ erewrite IGStaticExpr_eq_iff_eq_gens; eauto;
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

  Lemma eassocip_unique_simpl_associp :
    forall {Δ Δ__c σ formals asip formals'},
      eassocip Δ Δ__c σ formals asip formals' ->
      forall {id__i : ident},
        List.In (id__i, None) formals ->
        (~(exists e, (associp_ id__i e) = asip) /\
         ~(exists e e__i, (associp_ (n_xid id__i e__i) e) = asip)).
  Proof.
    inversion 1; subst; intros id__i In_formals.
    rename H2 into nex_1.
    destruct (Nat.eq_dec id__i id) as [eq1 | neq1].
    subst; exfalso; apply nex_1; exists None; assumption.
    split.
    destruct 1 as (e0, e1); inject_left e1; contradiction.
    destruct 1 as (e0, (e__i, e1)); inversion e1. 
    destruct (Nat.eq_dec id__i id) as [eq1 | neq1].
    subst; contradiction.
    split.
    destruct 1 as (e0, e1); inversion e1.
    destruct 1 as (e0, (e__i, e1)); inject_left e1; contradiction.
  Qed.

  Lemma eassocip_inv_formals :
    forall {Δ Δ__c σ formals asip formals'},
      eassocip Δ Δ__c σ formals asip formals' ->
      forall {f : ident * option N},
        List.In f formals ->
        List.In f formals'.
  Proof. inversion 1; auto with datatypes. Qed.
  
  Lemma listipm_unique_simpl_associp :
    forall {Δ Δ__c σ ipm formals formals'},
      listipm Δ Δ__c σ formals ipm formals' ->
      forall {id__i : ident},
      List.In (id__i, None) formals ->
      (~(exists e, List.In (associp_ id__i e) ipm) /\
       ~(exists e e__i, List.In (associp_ (n_xid id__i e__i) e) ipm)).
  Proof.
    induction 1; split.
    destruct 1 as (e, In_nil); inversion In_nil.
    destruct 1 as (e, (e__i, In_nil)); inversion In_nil.
    destruct 1 as (e, [eq1 | In_lofasips]).
    edestruct @eassocip_unique_simpl_associp with (Δ := Δ) as (nex_1, nex_2); eauto.
    edestruct @IHlistipm as (nex_1, nex_2); eauto.
    eapply eassocip_inv_formals; eauto.
    destruct 1 as (e, (e__i, [eq1 | In_lofasips])).
    edestruct @eassocip_unique_simpl_associp with (Δ := Δ) as (nex_1, nex_2); eauto.
    edestruct @IHlistipm as (nex_1, nex_2); eauto.
    eapply eassocip_inv_formals; eauto.
  Qed.

End ListIPM.


