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
Require Import sitpn2hvhdl.proofs.SInvTactics.

(** ** Facts about Architecture Generation Function *)

Lemma gen_arch_inv_lofPs :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    lofPs s = lofPs s'.
Proof. intros; solve_sinv. Qed.

Lemma gen_arch_inv_lofTs :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    lofTs s = lofTs s'.
Proof. intros; solve_sinv. Qed.
