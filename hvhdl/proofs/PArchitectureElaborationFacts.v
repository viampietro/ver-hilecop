(** * Facts about the Elaboration of Place Design Architecture *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.InAndNoDup.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.proofs.AbstractSyntaxFacts.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.proofs.WellDefinedDesignFacts.
Require Import hvhdl.Place.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.proofs.ArchitectureElaborationFacts.
Require Import hvhdl.proofs.DesignElaborationFacts.

(** ** Place Declared Signal Elaboration *)

Lemma EDecl_s_marking :
  forall {Δ σ Δ' σ'},
    EDecl Δ σ (sdecl_ s_marking local_weight_t) Δ' σ' ->
    exists n, MapsTo s_marking (Declared (Tnat 0 n)) Δ'.
Proof.
  inversion 1.
  match goal with | [ H: EType _ _ _ |- _ ] => inversion H end.
  match goal with | [ H: EConstr _ _ _ _ _ |- _ ] => inversion H end.
  match goal with | [ H: VExpr _ _ _ _ _ (Vnat n) |- _ ] => inversion H end.
  exists n'; apply add_1; auto.
Qed.

Lemma EDecls_P_Δ_s_marking :
  forall {Δ σ Δ' σ'},
    EDecls Δ σ place_sigs Δ' σ' ->
    exists n, MapsTo s_marking (Declared (Tnat 0 n)) Δ'.
Proof.
  inversion_clear 1.
  inversion_clear H1.
  edestruct @EDecl_s_marking with (Δ := Δ'0); eauto.
  exists x; eapply EDecls_inv_Δ; eauto.
Qed.
