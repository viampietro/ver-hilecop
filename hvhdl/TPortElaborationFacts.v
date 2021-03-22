(** * Facts about the elaboration of the Transition design's ports *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.NatMapTactics.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.HVhdlElaborationFactsLib.

(** ** Facts about the [reinit_time] input port *)

Lemma eport_rt :
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
  edestruct @eport_rt with (Δ := Δ'4) as (aofv, MapsTo_rt); eauto.
  exists aofv; eapply eports_inv_sigstore; eauto.
Qed.
