(** * Facts about Stabilization *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.NatSet.
Require Import common.ListPlus.

Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Stabilize.
Require Import hvhdl.Place.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.WellDefinedDesign.

Require Import hvhdl.proofs.CombinationalEvaluationFacts.


Lemma last_no_event :
  forall D__s Δ σ behavior σ',
    Stabilize D__s Δ σ behavior σ' ->
    events σ' = {[]}.
Proof.
  induction 1; assumption.
Qed.

Lemma stab_maps_cstore_id :
  forall {D__s Δ σ behavior σ'},
    Stabilize D__s Δ σ behavior σ' ->
    forall {id__c σ__c},
    MapsTo id__c σ__c (cstore σ) ->
    exists σ__c', MapsTo id__c σ__c' (cstore σ').
Proof.
  induction 1; intros.
  exists σ__c; assumption.
  edestruct @vcomb_maps_cstore_id with (D__s := D__s); eauto.
Qed.

Lemma stab_maps_sstore_of_comp :
  forall {D__s Δ σ behavior σ'},
    Stabilize D__s Δ σ behavior σ' ->
    forall {id__c id__e gm ipm opm σ__c σ'__c id v},
      InCs (cs_comp id__c id__e gm ipm opm) behavior ->
      MapsTo id__c σ__c (cstore σ) ->
      MapsTo id v (sstore σ__c) ->
      MapsTo id__c σ'__c (cstore σ') ->
      exists v', MapsTo id v' (sstore σ'__c).
Proof.
  induction 1.

  (* CASE stable *)
  - intros; exists v.
    erewrite @MapsTo_fun with (e := σ'__c) (e' := σ__c); eauto.

  (* CASE loop *)
  - intros.
    edestruct @vcomb_maps_cstore_id; eauto.
    edestruct @vcomb_maps_sstore_of_comp with (D__s := D__s); eauto.
Qed.

Lemma stab_inv_well_typed_values_in_sstore_of_comp :
  forall {D__s Δ σ behavior σ'},
    Stabilize D__s Δ σ behavior σ' ->
    (forall {id__c Δ__c σ__c},
        MapsTo id__c (Component Δ__c) Δ ->
        MapsTo id__c σ__c (cstore σ) ->
        forall {id t v},
          (MapsTo id (Internal t) Δ__c \/ MapsTo id (Input t) Δ__c \/ MapsTo id (Output t) Δ__c) ->
          MapsTo id v (sstore σ__c) ->
          IsOfType v t) ->
    forall {id__c Δ__c σ'__c},
      MapsTo id__c (Component Δ__c) Δ ->
      MapsTo id__c σ'__c (cstore σ') ->
      forall {id t v},
        (MapsTo id (Internal t) Δ__c \/ MapsTo id (Input t) Δ__c \/ MapsTo id (Output t) Δ__c) ->
        MapsTo id v (sstore σ'__c) ->
        IsOfType v t.
Proof.
  induction 1; try (solve [trivial]).
  intros WT; eapply IHStabilize; eauto.
  eapply vcomb_inv_well_typed_values_in_sstore_of_comp; eauto.
Admitted.

