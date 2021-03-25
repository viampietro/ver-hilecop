(** * Tactics for constraint elaboration *)

Require Import hvhdl.ConstraintElaboration.

Ltac econstrinv_cl1 H :=
  match type of H with
  | econstr _ _ _ _ _ =>
    inversion_clear H
  end.

Ltac econstrinv_cl :=
  match goal with
  | [ H: econstr _ _ _ _ _ |- _] =>
    econstrinv_cl1 H
  end.
