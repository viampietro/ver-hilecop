(** * Facts about Port Map Evaluation *)

Require Import common.NatMap.

Require Import hvhdl.Environment.
Require Import hvhdl.PortMapEvaluation.

(** ** Facts about Input Port Map Evaluation *)

Section IPMap.

  
End IPMap.

(** ** Facts about Output Port Map Evaluation *)

Section OPMap.

  Lemma mapop_inv_compstore_id :
    forall {Δ Δ__c σ σ__c1 ipmap σ' id__c σ__c2},
      mapop Δ Δ__c σ σ__c1 ipmap σ' ->
      MapsTo id__c σ__c2 (compstore σ) ->
      MapsTo id__c σ__c2 (compstore σ').
  Proof.
    induction 1; try subst; auto.
    induction H; try subst; auto.
  Qed.
  
End OPMap.
