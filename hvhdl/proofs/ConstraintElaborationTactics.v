(** * Tactics for constraint elaboration *)

Require Import hvhdl.ConstraintElaboration.

Ltac econstrinv_cl1 H :=
  match type of H with
  | EConstr _ _ _ _ _ =>
    inversion_clear H
  end.

Ltac econstrinv_cl :=
  match goal with
  | [ H: EConstr _ _ _ _ _ |- _] =>
    econstrinv_cl1 H
  end.
