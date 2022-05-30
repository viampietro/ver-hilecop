(** * Facts about the elaboration of the Transition design's ports *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.proofs.HVhdlElaborationFactsLib.
Require Import hvhdl.proofs.ExpressionEvaluationTactics.
Require Import hvhdl.proofs.HVhdlElaborationTacticsLib.

(** ** Facts about the [reinit_time] input port *)

Lemma EPort_σ_rt :
  forall {Δ σ Δ' σ'},
    EPort Δ σ (pdecl_in reinit_time (bool_vector_t 0 (# input_arcs_number @- 1))) Δ' σ' ->
    exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sstore σ').
Proof. intros; eapply EPort_Varr_in_sstore; eauto. Qed.

Lemma EPorts_T_σ_rt :
  forall {Δ σ Δ' σ'},
    EPorts Δ σ transition_ports Δ' σ' ->
    exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sstore σ').
Proof.
  inversion_clear 1.
  do 5 (match goal with
        | [ H: EPorts _ _ _ _ _ |- _ ] =>
          inversion_clear H
        end).
  edestruct @EPort_σ_rt with (Δ := Δ'4) as (aofv, MapsTo_rt); eauto.
  exists aofv; eapply EPorts_inv_sstore; eauto.
Qed.

Lemma EPort_Δ_rt :
  forall {Δ σ Δ' σ' t n},
    EPort Δ σ (pdecl_in reinit_time (bool_vector_t 0 (# input_arcs_number @- 1))) Δ' σ' ->
    MapsTo input_arcs_number (Generic t (Vnat n)) Δ ->
    MapsTo Transition.reinit_time (Input (Tarray Tbool 0 (n - 1))) Δ'.
Proof.
  inversion_clear 1.
  intros MapsTo_ian.
  eapply MapsTo_add_eqv_2; eauto.
  do 2 ETypeinv_cl.
  econstrinv_cl.
  repeat vexprinv_cl.
  mapsto_discriminate.
  mapsto_not_in_contrad.
  assert (eq_gen : Generic t0 (Vnat n) = Generic t3 (Vnat n1)) by
      (eapply MapsTo_fun; eauto).
  inject_left eq_gen; reflexivity.
Qed.

Lemma EPorts_T_Δ_rt :
  forall {Δ σ Δ' σ'},
    EPorts Δ σ transition_ports Δ' σ' ->
    forall {t n},
      MapsTo input_arcs_number (Generic t (Vnat n)) Δ ->
      MapsTo Transition.reinit_time (Input (Tarray Tbool 0 (n - 1))) Δ'.
Proof.
  inversion_clear 1.
  do 5 (match goal with
        | [ H: EPorts _ _ _ _ _ |- _ ] =>
          inversion_clear H
        end).
  intros t n MapsTo_ian.
  eapply EPorts_inv_Δ; eauto.
  eapply EPort_Δ_rt; eauto.
  do 5 (eapply EPort_inv_Δ; eauto).
Qed.

