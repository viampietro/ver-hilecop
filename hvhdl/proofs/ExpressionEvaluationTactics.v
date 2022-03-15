(** * Tactics for Expression Evaluation *)

Require Import hvhdl.ExpressionEvaluation.

Ltac vexprinv_cl1 H :=
  match type of H with
  | VExpr _ _ _ _ _ _ =>
    inversion_clear H
  end.

Ltac vexprinv_cl :=
  match goal with
  | [ H: VExpr _ _ _ _ _ _ |- _] =>
    vexprinv_cl1 H
  end.
