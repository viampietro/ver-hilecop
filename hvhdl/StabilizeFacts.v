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

Require Import hvhdl.CombinationalEvaluationFacts.

Lemma is_last_of_trace :
  forall D__s Δ σ behavior θ σ',
    stabilize D__s Δ σ behavior θ σ' ->
    (Last θ σ' \/ σ = σ').
Proof.
  induction 1.

  (* BASE CASE. *)
  - right; reflexivity. 

  (* IND. CASE. *)
  - destruct θ.
    + lazymatch goal with
      | [ H: stabilize _ _ _ _ [] _ |- _ ] =>
        inversion H; left; apply Last_singleton
      end.
    + inversion_clear IHstabilize as [Hlast | Heq].
      -- left; apply Last_cons; assumption.
      -- rewrite Heq in H0; inversion H0; contradiction.
Qed.

Lemma last_no_event :
  forall D__s Δ σ behavior θ σ',
    stabilize D__s Δ σ behavior θ σ' ->
    Last θ σ' ->
    events σ' = {[]}.
Proof.
  induction 1.
  - inversion 1.
  - intros Hlast.
    destruct θ.
    assumption.
    assert (Hconsl : d :: θ <> nil) by inversion 1.
    apply (IHstabilize (last_cons_inv Hconsl Hlast)).
Qed.

Lemma stab_maps_compstore_id :
  forall {D__s Δ σ behavior θ σ'},
    stabilize D__s Δ σ behavior θ σ' ->
    forall {id__c σ__c},
    MapsTo id__c σ__c (compstore σ) ->
    exists σ__c', MapsTo id__c σ__c' (compstore σ').
Proof.
  induction 1; intros.
  exists σ__c; assumption.
  edestruct @vcomb_maps_compstore_id with (D__s := D__s); eauto.
Qed.
