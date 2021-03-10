(** * Facts about Stabilization and Transition Design *)

Require Import common.CoqLib.
Require Import common.NatMap.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.HVhdlSimulationFactsLib.
Require Import hvhdl.TCombinationalEvaluationFacts.

(** Value of signal [s_tc] in a given T component [id__t] is
      invariant during stabilization. *)

Lemma stab_inv_s_tc :
  forall Δ σ behavior θ σ',
    stabilize hdstore Δ σ behavior θ σ' ->
    forall id__t gm ipm opm Δ__t σ__t σ__t' v compids,
      InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
      AreCsCompIds behavior compids -> 
      List.NoDup compids ->
      MapsTo id__t (Component Δ__t) Δ ->
      DeclaredOf Δ__t s_time_counter ->
      MapsTo id__t σ__t (compstore σ) ->
      MapsTo s_time_counter v (sigstore σ__t) ->
      MapsTo id__t σ__t' (compstore σ') ->
      MapsTo s_time_counter v (sigstore σ__t').
Proof.
  induction 1; intros.

  (* CASE No events, [σ = σ'] *)
  - erewrite <- MapsTo_fun with (e := σ__t) (e' := σ__t'); eauto.

  (* CASE Events *)
  - edestruct @vcomb_maps_compstore_id with (Δ := Δ) as (σ__ti, MapsTo_σ__ti); eauto.
    eapply IHstabilize; eauto.
    eapply vcomb_inv_s_tc; eauto.
Qed.
