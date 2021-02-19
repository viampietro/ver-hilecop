(** * Tactics for H-VHDL Environment *)

Require Import hvhdl.Environment.

(** ** [IsMergedDState] Relation Tactics  *)

Ltac erw_left_IMDS_sstore_m H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 8 (apply proj2 in H');
     apply proj1 in H';
     erewrite H'; clear H')
  end.

Ltac erw_right_IMDS_sstore_m H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 8 (apply proj2 in H');
     apply proj1 in H';
     erewrite <- H'; clear H')
  end.

Tactic Notation "erw_IMDS_sstore_m" constr(H) := erw_left_IMDS_sstore_m H.
Tactic Notation "erw_IMDS_sstore_m" "<-" constr(H) := erw_right_IMDS_sstore_m H.

Ltac erw_left_IMDS_sstore_1 H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 6 (apply proj2 in H');
     apply proj1 in H';
     erewrite H'; clear H')
  end.

Ltac erw_right_IMDS_sstore_1 H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 6 (apply proj2 in H');
     apply proj1 in H';
     erewrite <- H'; clear H')
  end.

Tactic Notation "erw_IMDS_sstore_1" constr(H) := erw_left_IMDS_sstore_1 H.
Tactic Notation "erw_IMDS_sstore_1" "<-" constr(H) := erw_right_IMDS_sstore_1 H.

Ltac erw_left_IMDS_events_m H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 12 (apply proj2 in H');
     erewrite H'; clear H')
  end.

Ltac erw_right_IMDS_events_m H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 12 (apply proj2 in H');
     erewrite <- H'; clear H')
  end.

Tactic Notation "erw_IMDS_events_m" hyp(H) := erw_left_IMDS_events_m H.
Tactic Notation "erw_IMDS_events_m" "<-" hyp(H) := erw_right_IMDS_events_m H.
