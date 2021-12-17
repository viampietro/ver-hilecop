(** * Tactics for Expression Evaluation *)

Require Import hvhdl.ExpressionEvaluation.

Ltac vexprinv_cl1 H :=
  match type of H with
  | vexpr _ _ _ _ _ _ =>
    inversion_clear H
  end.

Ltac vexprinv_cl :=
  match goal with
  | [ H: vexpr _ _ _ _ _ _ |- _] =>
    vexprinv_cl1 H
  end.
