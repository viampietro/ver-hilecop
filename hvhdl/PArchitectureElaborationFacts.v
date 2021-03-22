(** * Facts about the Elaboration of Place Design Architecture *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.InAndNoDup.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.AbstractSyntaxFacts.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.WellDefinedDesignFacts.
Require Import hvhdl.Place.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.ArchitectureElaborationFacts.
Require Import hvhdl.DesignElaborationFacts.

(** ** Place Declared Signal Elaboration *)

Lemma edecl_s_marking :
  forall {Δ σ Δ' σ'},
    edecl Δ σ (sdecl_ s_marking local_weight_t) Δ' σ' ->
    exists n, MapsTo s_marking (Declared (Tnat 0 n)) Δ'.
Proof.
  inversion 1.
  match goal with | [ H: etype _ _ _ |- _ ] => inversion H end.
  match goal with | [ H: econstr _ _ _ _ _ |- _ ] => inversion H end.
  match goal with | [ H: vexpr _ _ _ _ _ (Vnat n) |- _ ] => inversion H end.
  exists n'; apply add_1; auto.
Qed.

Lemma edecls_P_Δ_s_marking :
  forall {Δ σ Δ' σ'},
    edecls Δ σ place_sigs Δ' σ' ->
    exists n, MapsTo s_marking (Declared (Tnat 0 n)) Δ'.
Proof.
  inversion_clear 1.
  inversion_clear H1.
  edestruct @edecl_s_marking with (Δ := Δ'0); eauto.
  exists x; eapply edecls_inv_Δ; eauto.
Qed.
