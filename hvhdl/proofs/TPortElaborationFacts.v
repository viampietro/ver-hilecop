(** * Facts about the elaboration of the Transition design's ports *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.HVhdlElaborationFactsLib.
Require Import hvhdl.ExpressionEvaluationTactics.
Require Import hvhdl.HVhdlElaborationTacticsLib.

(** ** Facts about the [reinit_time] input port *)

Lemma eport_σ_rt :
  forall {Δ σ Δ' σ'},
    eport Δ σ (pdecl_in reinit_time (bool_vector_t 0 (# input_arcs_number @- 1))) Δ' σ' ->
    exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sigstore σ').
Proof. intros; eapply eport_Varr_in_sigstore; eauto. Qed.

Lemma eports_T_σ_rt :
  forall {Δ σ Δ' σ'},
    eports Δ σ transition_ports Δ' σ' ->
    exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sigstore σ').
Proof.
  inversion_clear 1.
  do 5 (match goal with
        | [ H: eports _ _ _ _ _ |- _ ] =>
          inversion_clear H
        end).
  edestruct @eport_σ_rt with (Δ := Δ'4) as (aofv, MapsTo_rt); eauto.
  exists aofv; eapply eports_inv_sigstore; eauto.
Qed.

Lemma eport_Δ_rt :
  forall {Δ σ Δ' σ' t n},
    eport Δ σ (pdecl_in reinit_time (bool_vector_t 0 (# input_arcs_number @- 1))) Δ' σ' ->
    MapsTo input_arcs_number (Generic t (Vnat n)) Δ ->
    MapsTo Transition.reinit_time (Input (Tarray Tbool 0 (n - 1))) Δ'.
Proof.
  inversion_clear 1.
  intros MapsTo_ian.
  eapply MapsTo_add_eqv_2; eauto.
  do 2 etypeinv_cl.
  econstrinv_cl.
  repeat vexprinv_cl.
  mapsto_discriminate.
  mapsto_not_in_contrad.
  assert (eq_gen : Generic t0 (Vnat n) = Generic t3 (Vnat n1)) by
      (eapply MapsTo_fun; eauto).
  inject_left eq_gen; reflexivity.
Qed.

Lemma eports_T_Δ_rt :
  forall {Δ σ Δ' σ'},
    eports Δ σ transition_ports Δ' σ' ->
    forall {t n},
      MapsTo input_arcs_number (Generic t (Vnat n)) Δ ->
      MapsTo Transition.reinit_time (Input (Tarray Tbool 0 (n - 1))) Δ'.
Proof.
  inversion_clear 1.
  do 5 (match goal with
        | [ H: eports _ _ _ _ _ |- _ ] =>
          inversion_clear H
        end).
  intros t n MapsTo_ian.
  eapply eports_inv_Δ; eauto.
  eapply eport_Δ_rt; eauto.
  do 5 (eapply eport_inv_Δ; eauto).
Qed.

