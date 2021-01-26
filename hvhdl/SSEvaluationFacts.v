(** * Facts about Evaluation of Sequantial Statements *)

Require Import common.NatMap.

Require Import hvhdl.Environment.
Require Import hvhdl.SSEvaluation.

Lemma vseq_inv_compstore_id :
  forall {Δ σ Λ flag stmt σ' Λ' id__c σ__c},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    MapsTo id__c σ__c (compstore σ) ->
    MapsTo id__c σ__c (compstore σ').
Proof. induction 1; try subst; auto. Qed.


