(** * Facts about default values of H-VHDL types *)

Require Import common.CoqLib.

Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.DefaultValue.

Lemma ArrIsOfType_create_arr:
  forall (n : nat) (t : type) (v : value) (gt_n_O : (n > 0)%nat),
    IsOfType v t -> ArrIsOfType (create_arr n v gt_n_O) n t.
Proof.
  destruct n.
  inversion gt_n_O.
  cbn; induction n.
  constructor; assumption.
  constructor;
    [ assumption
    | apply IHn; [ lia | assumption ] ].
Qed.

Lemma DefaultV_is_well_typed :
  forall t v,
    DefaultV t v -> IsOfType v t.
Proof.
  induction 1.
  constructor.
  constructor; [assumption | inversion H; lia ].
  constructor; [assumption | ].
  revert size.
  cbv zeta.
  generalize (u - l).
  intro.
  generalize (Nat.lt_0_succ (N.to_nat n)).
  rewrite <- N2Nat.inj_succ with (a := n).
  intro.
  eapply ArrIsOfType_create_arr; assumption.
Qed.

