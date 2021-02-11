(** * Facts about Evaluation of Sequantial Statements *)

Require Import common.NatMap.
Require Import common.NatSet.

Require Import hvhdl.Environment.
Require Import hvhdl.SSEvaluation.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.ExpressionEvaluation.

Lemma vseq_inv_compstore :
  forall {Δ σ Λ flag stmt σ' Λ' id__c σ__c},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    MapsTo id__c σ__c (compstore σ) ->
    MapsTo id__c σ__c (compstore σ').
Proof. induction 1; try subst; auto. Qed.

Lemma vseq_not_in_events_if_not_assigned :
  forall {Δ σ Λ flag stmt σ' Λ' id},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    ~NatSet.In id (events σ) ->
    ~AssignedInSS id stmt ->
    ~NatSet.In id (events σ').
Proof.
  induction 1; subst; simpl; (auto || (try (rewrite add_spec; firstorder))).
  intros; apply IHvseq2; auto.
Qed.

Lemma vseq_not_in_events_if_not_sig :
  forall {Δ σ Λ flag stmt σ' Λ' id},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    ~NatSet.In id (events σ) ->
    ~OutputOf Δ id  ->
    ~DeclaredOf Δ id ->
    ~NatSet.In id (events σ').
Admitted.

