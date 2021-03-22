(** * Facts about the elaboration of H-VHDL design generic constants *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.NatMapTactics.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.HVhdlElaborationLib.

Lemma egen_inv_Δ : 
  forall {Δ M__g gd Δ' id sobj},
    egen Δ M__g gd Δ' ->
    MapsTo id sobj Δ ->
    MapsTo id sobj Δ'.
Proof.
  inversion_clear 1; intros; auto;
    destruct (Nat.eq_dec id idg) as [eq_ | neq_]; try subst;
      [mapsto_not_in_contrad | apply add_2; auto
       | mapsto_not_in_contrad | apply add_2; auto ].
Qed.

Lemma egens_inv_Δ : 
  forall {Δ M__g gens Δ' id sobj},
    egens Δ M__g gens Δ' ->
    MapsTo id sobj Δ ->
    MapsTo id sobj Δ'.
Proof.
  induction 1; intros; auto.
  apply IHegens; eapply egen_inv_Δ; eauto.
Qed.
