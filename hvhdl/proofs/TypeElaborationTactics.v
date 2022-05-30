(** * Tactics for type elaboration *)

Require Import hvhdl.TypeElaboration.

Ltac ETypeinv_cl1 H :=
  match type of H with
  | EType _ _ _ =>
    inversion_clear H
  end.

Ltac ETypeinv_cl :=
  match goal with
  | [ H: EType _ _ _ |- _] =>
    ETypeinv_cl1 H
  end.
