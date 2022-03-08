(** * Facts about the elaboration of the Transition design's generic constants *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.proofs.HVhdlElaborationFactsLib.

(** ** Facts about the [input_arcs_number] generic constant *)

Lemma egen_in_arcs_nb_1 :
  forall {Δ M__g Δ'},
    egen Δ M__g (gdecl_ Transition.input_arcs_number (tind_natural 0 NATMAX) 1) Δ' ->
    exists t n, MapsTo Transition.input_arcs_number (Generic t (Vnat n)) Δ'.
Proof.
  inversion_clear 1.
  inversion_clear H2 in H3.
  inversion_clear H3 in H4.
  inversion_clear H4 in H6.
  exists (Tnat l u), n; eauto with mapsto.
  inversion_clear H2.
  exists t0, 1; eauto with mapsto.
Qed.

Lemma egens_T_Δ_in_arcs_nb_1 :
  forall {Δ M__g Δ'},
    egens Δ M__g transition_gens Δ' ->
    exists t n, MapsTo Transition.input_arcs_number (Generic t (Vnat n)) Δ'.
Proof.
  inversion_clear 1.
  inversion_clear H1.
  edestruct @egen_in_arcs_nb_1 with (Δ := Δ'0) as (t, (n, MapsTo_ian)); eauto.
  exists t, n; eapply egens_inv_Δ; eauto.
Qed.
