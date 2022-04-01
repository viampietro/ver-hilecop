(** * Facts about Stabilization and Transition Design *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.ListLib.
Require Import common.GlobalTypes.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.proofs.HVhdlSimulationFactsLib.
Require Import hvhdl.proofs.TCombinationalEvaluationFacts.

(** Value of signal [s_tc] in a given T component [id__t] is
      invariant during stabilization. *)

Lemma stab_inv_s_tc :
  forall Δ σ behavior σ',
    stabilize hdstore Δ σ behavior σ' ->
    forall id__t gm ipm opm Δ__t σ__t σ__t' v compids,
      InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
      CsHasUniqueCompIds behavior compids -> 
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

Lemma stab_TCI_s_rtc_eq_bprod_of_rt :
  forall Δ σ behavior σ',
    stabilize hdstore Δ σ behavior σ' ->
    forall id__t gm ipm opm Δ__t t n,
      InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
      MapsTo id__t (Component Δ__t) Δ ->
      MapsTo input_arcs_number (Generic t (Vnat n)) Δ__t ->
      (forall σ__t aofv b,
          MapsTo id__t σ__t (compstore σ) ->
          MapsTo Transition.reinit_time (Varr aofv) (sigstore σ__t) ->
          BProd (get_bool_at aofv) (seq 0 n) b ->
          MapsTo Transition.s_reinit_time_counter (Vbool b) (sigstore σ__t)) ->
      forall σ__t' aofv' b,
        MapsTo id__t σ__t' (compstore σ') ->
        MapsTo Transition.reinit_time (Varr aofv') (sigstore σ__t') ->
        BProd (get_bool_at aofv') (seq 0 n) b ->
        MapsTo Transition.s_reinit_time_counter (Vbool b) (sigstore σ__t').
Proof.
  induction 1.

  (* BASE CASE *)
  - intros *; do 3 intro; intros s_rtc; eapply s_rtc; eauto.
Admitted.
