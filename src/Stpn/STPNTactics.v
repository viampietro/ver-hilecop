Require Import Hilecop.STPN.

Ltac decide_are_well_formed_chronos :=
  match goal with
  | |- AreWellFormedChronos _ =>
    unfold AreWellFormedChronos;
    simpl;
    intros chrono Hchronos;
    decompose [or] Hchronos;
    match goal with
    | [ H: False |- _ ] => elim H
    | [ H: None = Some _ |- _ ] => inversion H
    | [ H: Some ?chr = Some ?chr' |- _ ] =>
      injection H;  clear H; intros Heq; rewrite <- Heq; simpl; (omega || auto)
    end
  end.