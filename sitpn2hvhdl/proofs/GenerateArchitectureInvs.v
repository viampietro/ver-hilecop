(** * Architecture Generation and State Invariants *)

Require Import String.
Require Import common.CoqLib.
Require Import common.StateAndErrorMonad.
Require Import common.ListLib.
Require Import common.proofs.ListTacticsLib.
Require Import common.proofs.StateAndErrorMonadTactics.

Require Import sitpn.Sitpn.
Require Import sitpn.SitpnFacts.

Require Import hvhdl.Place.
Require Import hvhdl.AbstractSyntax.

Require Import sitpn2hvhdl.Sitpn2HVhdl.

(** ** Facts about Architecture Generation Function *)

Lemma gen_arch_inv_lofPs :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    lofPs s = lofPs s'.
Proof.
  intros until s'; intros e; monadFullInv e.
  transitivity (lofPs s1).
  eapply gen_pmap_entry_inv_lofPs; eauto.
  change (lofPs s4) with (lofPs s); transitivity (lofPs s5).
  solve_listm EQ1; intros; eapply gen_tmap_entry_inv_lofPs; eauto.
  change (lofPs s5) with (lofPs s1).
  solve_listm EQ3; intros; eapply interconnect_p_inv_lofPs; eauto.
Qed.

Lemma gen_arch_inv_lofTs :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    lofTs s = lofTs s'.
Proof.
  intros until s'; intros e; monadFullInv e.
  shelf_state EQ1; shelf_state EQ3.
  transitivity (lofTs s4).
  solve_listm EQ; intros; eapply gen_pmap_entry_inv_lofTs; eauto.
  change (lofTs s4) with (lofTs s); transitivity (lofTs s5).
  solve_listm EQ1; intros; eapply gen_tmap_entry_inv_lofTs; eauto.
  change (lofTs s5) with (lofTs s1).
  solve_listm EQ3; intros; eapply interconnect_p_inv_lofTs; eauto.
Qed.
