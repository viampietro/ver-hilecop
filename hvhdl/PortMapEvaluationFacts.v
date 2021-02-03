(** * Facts about Port Map Evaluation *)

Require Import common.NatMap.
Require Import common.Coqlib.

Require Import hvhdl.Environment.
Require Import hvhdl.PortMapEvaluation.

(** ** Facts about Input Port Map Evaluation *)

Section IPMap.

  Lemma vassocip_inv_sigstore :
    forall {Δ Δ__c σ σ__c asip σ__c' id v},
      vassocip Δ Δ__c σ σ__c asip σ__c' -> 
      ~InputOf Δ__c id ->
      MapsTo id v (sigstore σ__c) ->
      MapsTo id v (sigstore σ__c').
  Proof.
    inversion 1; subst; simpl; auto; intros.
    all :
      destruct (Nat.eq_dec id id0) as [e1 | ne1]; try subst;
      [ elimtype False;
        match goal with
        | [ H: ~InputOf _ _, H': MapsTo _ (Input ?t) _ |- _ ] =>
          apply H; exists t; assumption
        end
      | eapply add_2; eauto ].
  Qed.
  
  Lemma mapip_inv_sigstore :
    forall {Δ Δ__c σ σ__c ipm σ__c' id v},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      ~InputOf Δ__c id ->
      MapsTo id v (sigstore σ__c) ->
      MapsTo id v (sigstore σ__c').
  Proof.
    induction 1; intros; auto.
    apply IHmapip; auto.
    eapply vassocip_inv_sigstore; eauto.
  Qed.
  
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
