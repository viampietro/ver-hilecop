(** * Tactics for type elaboration *)

Require Import hvhdl.TypeElaboration.

Ltac etypeinv_cl1 H :=
  match type of H with
  | etype _ _ _ =>
    inversion_clear H
  end.

Ltac etypeinv_cl :=
  match goal with
  | [ H: etype _ _ _ |- _] =>
    etypeinv_cl1 H
  end.
