(** * Facts about Stabilization and Place Design *)

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
Require Import hvhdl.proofs.PCombinationalEvaluationFacts.

(** Value of signal [s_marking] in a given P component [id__p] is
    invariant during stabilization. *)

Lemma stab_inv_s_marking :
  forall Δ σ behavior σ',
    Stabilize hdstore Δ σ behavior σ' ->
    forall id__p gm ipm opm σ__p σ__p' v Δ__p compids mm,
      InCs (cs_comp id__p Petri.place_id gm ipm opm) behavior ->
      MapsTo id__p (Component Δ__p) Δ ->
      AreCsCompIds behavior compids ->
      List.NoDup compids ->
      MapsTo id__p σ__p (cstore σ) ->
      MapsTo s_marking v (sstore σ__p) ->
      MapsTo s_marking (Internal (Tnat 0 mm)) Δ__p ->
      MapsTo id__p σ__p' (cstore σ') ->
      MapsTo s_marking v (sstore σ__p').
Proof.
  induction 1; intros.

  (* CASE No events, [σ = σ'] *)
  - erewrite <- MapsTo_fun with (e := σ__p) (e' := σ__p'); eauto.

  (* CASE Events *)
  - edestruct @vcomb_maps_cstore_id with (Δ := Δ) as (σ__pi, MapsTo_σ__pi); eauto.
    eapply IHStabilize; eauto.
    eapply vcomb_inv_s_marking; eauto.
Qed.
