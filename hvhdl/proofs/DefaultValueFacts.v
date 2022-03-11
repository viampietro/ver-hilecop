(** * Facts about default values of H-VHDL types *)

Require Import common.CoqLib.

Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.DefaultValue.

Lemma DefaultV_is_well_typed :
  forall t v,
    DefaultV t v -> IsOfType v t.
Proof.
  induction 1.
  constructor.
  constructor; lia.
  constructor; auto.
  induction (u - l).
  cbn; constructor.
  simpl; constructor; auto.
Qed.

