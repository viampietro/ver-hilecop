(** * Tactics for Sequential Statement Evaluation *)

Require Import hvhdl.SSEvaluation.

Ltac VSeqinv_cl1 H :=
  match type of H with
  | VSeq _ _ _ _ _ _ _ _ =>
    inversion_clear H
  end.

Ltac VSeqinv_cl :=
  match goal with
  | [ H: VSeq _ _ _ _ _ _ _ _ |- _] =>
    VSeqinv_cl1 H
  end.

Ltac VSeqinv1 H :=
  match type of H with
  | VSeq _ _ _ _ _ _ _ _ =>
    inversion H
  end.

Ltac VSeqinv :=
  match goal with
  | [ H: VSeq _ _ _ _ _ _ _ _ |- _] =>
    VSeqinv1 H
  end.
