(** * Tactics for Sequential Statement Evaluation *)

Require Import hvhdl.SSEvaluation.

Ltac vseqinv_cl1 H :=
  match type of H with
  | vseq _ _ _ _ _ _ _ =>
    inversion_clear H
  end.

Ltac vseqinv_cl :=
  match goal with
  | [ H: vseq _ _ _ _ _ _ _ |- _] =>
    vseqinv_cl1 H
  end.
