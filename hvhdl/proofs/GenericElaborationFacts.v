(** * Facts about the elaboration of H-VHDL design generic constants *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.

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

Lemma egen_inv_Δ_if_not_gen : 
  forall {Δ M__g gd Δ'},
    egen Δ M__g gd Δ' ->
    forall {id sobj},
      (~exists t v, sobj = Generic t v) ->
      MapsTo id sobj Δ' <-> MapsTo id sobj Δ.
Proof.
  split; [ | eapply egen_inv_Δ; eauto].
  induction H.
  all : destruct (Nat.eq_dec idg id) as [eq_ | neq_];
    [ rewrite eq_; intros; exfalso;
      match goal with
      | [ H1: ~(_), H2: MapsTo ?k _ (add ?k (Generic ?t ?v) _)  |- _ ] =>
        apply H1; exists t, v; eauto with mapsto
      end
    | eauto with mapsto ].
Qed.

Lemma egens_inv_Δ_if_not_gen : 
  forall {Δ M__g gens Δ'},
    egens Δ M__g gens Δ' ->
    forall {id sobj},
      (~exists t v, sobj = Generic t v) ->
      MapsTo id sobj Δ' <-> MapsTo id sobj Δ.
Proof.
  induction 1; try (solve [reflexivity]).
  intros; erewrite <- @egen_inv_Δ_if_not_gen with (Δ := Δ); eauto.
Qed.

