(** Facts about Evaluation of the Place Design Behavior *)

Require Import common.NatMap.

Require Import hvhdl.Environment.
Require Import hvhdl.Place.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.HilecopDesignStore.

Lemma vcomb_place_inv_s_marking :
  forall {Δ σ σ' v},
    vcomb hdstore Δ σ place_behavior σ' ->
    MapsTo s_marking v (sigstore σ) ->
    MapsTo s_marking v (sigstore σ').
Proof.
  inversion 1; try subst.
  do 6 (match goal with
        | [ H: vcomb _ _ _ (_ // _) _ |- _ ] =>
          inversion H; try subst
        end).
Admitted.

