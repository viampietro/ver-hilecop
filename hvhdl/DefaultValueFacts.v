(** * Facts about default values of H-VHDL types *)

Require Import common.CoqLib.

Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.DefaultValue.

Lemma defaultv_is_well_typed :
  forall t v,
    defaultv t v -> is_of_type v t.
Proof.
  induction 1.
  constructor.
  constructor; lia.
  constructor.
  induction (u - l).
  cbn; constructor.
  simpl; constructor; auto.
Qed.

