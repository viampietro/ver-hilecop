(** * Tactics for H-VHDL Environment *)

Require Import common.NatMap.
Require Import common.NatSet.
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

Ltac erw_left_IMDS_cstore_m H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 11 (apply proj2 in H');
     apply proj1 in H';
     erewrite H'; clear H')
  end.

Ltac erw_right_IMDS_cstore_m H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 11 (apply proj2 in H');
     apply proj1 in H';
     erewrite <- H'; clear H')
  end.

Tactic Notation "erw_IMDS_cstore_m" hyp(H) := erw_left_IMDS_cstore_m H.
Tactic Notation "erw_IMDS_cstore_m" "<-" hyp(H) := erw_right_IMDS_cstore_m H.

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

Ltac erw_left_IMDS_cstore_1 H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 9 (apply proj2 in H');
     apply proj1 in H';
     erewrite H'; clear H')
  end.

Ltac erw_right_IMDS_cstore_1 H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 9 (apply proj2 in H');
     apply proj1 in H';
     erewrite <- H'; clear H')
  end.

Tactic Notation "erw_IMDS_cstore_1" hyp(H) := erw_left_IMDS_cstore_1 H.
Tactic Notation "erw_IMDS_cstore_1" "<-" hyp(H) := erw_right_IMDS_cstore_1 H.

Ltac erw_left_IMDS_sstore_2 H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 7 (apply proj2 in H');
     apply proj1 in H';
     erewrite H'; clear H')
  end.

Ltac erw_right_IMDS_sstore_2 H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 7 (apply proj2 in H');
     apply proj1 in H';
     erewrite <- H'; clear H')
  end.

Tactic Notation "erw_IMDS_sstore_2" constr(H) := erw_left_IMDS_sstore_2 H.
Tactic Notation "erw_IMDS_sstore_2" "<-" constr(H) := erw_right_IMDS_sstore_2 H.

Ltac erw_left_IMDS_cstore_2 H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 10 (apply proj2 in H');
     apply proj1 in H';
     erewrite H'; clear H')
  end.

Ltac erw_right_IMDS_cstore_2 H :=
  match type of H with
  | IsMergedDState _ _ _ _ =>
    let H' := fresh H in
    (set (H' := H);
     do 10 (apply proj2 in H');
     apply proj1 in H';
     erewrite <- H'; clear H')
  end.

Tactic Notation "erw_IMDS_cstore_2" constr(H) := erw_left_IMDS_cstore_2 H.
Tactic Notation "erw_IMDS_cstore_2" "<-" constr(H) := erw_right_IMDS_cstore_2 H.

Ltac gen_eq_cstate_from_IMDS Heq :=
  match goal with
  | [
    IMDS: IsMergedDState ??? ???' ???'' ???__m,
    MapsTo_??: MapsTo ?id__c ???__c (cstore ???),
    MapsTo_??__m: MapsTo ?id__c ???__mc (cstore ???__m)
    |- _
  ] =>
    assert (Heq : ??__c = ??__mc) by (eapply MapsTo_fun; eauto;
                                erw_IMDS_cstore_m IMDS;
                                eauto; eapply not_in_union; eauto)
  | [
    IMDS: IsMergedDState ??? ???' ???'' ???__m,
    MapsTo_??': MapsTo ?id__c ???__c (cstore ???'),
    MapsTo_??__m: MapsTo ?id__c ???__mc (cstore ???__m)
    |- _
  ] =>
    assert (Heq : ??__c = ??__mc)
      by (eapply MapsTo_fun; eauto;
          erw_IMDS_cstore_m IMDS;
          eauto)
  | [
    IMDS: IsMergedDState ??? ???' ???'' ???__m,
    MapsTo_??'': MapsTo ?id__c ???__c (cstore ???''),
    MapsTo_??__m: MapsTo ?id__c ???__mc (cstore ???__m)
    |- _
  ] =>
    assert (Heq : ??__c = ??__mc)
      by (eapply MapsTo_fun; eauto;
          erw_IMDS_cstore_m IMDS;
          eauto)
  end.

Ltac gen_eq_val_from_IMDS Heq :=
  match goal with
  | [
    IMDS: IsMergedDState ??? ???' ???'' ???__m,
    MapsTo_??: MapsTo ?id ?v (sstore ???),
    MapsTo_??__m: MapsTo ?id ?v__m (sstore ???__m)
    |- _
  ] =>
    assert (Heq : v = v__m) by (eapply MapsTo_fun; eauto;
                              erw_IMDS_sstore_m IMDS;
                              eauto; eapply not_in_union; eauto)
  | [
    IMDS: IsMergedDState ??? ???' ???'' ???__m,
    MapsTo_??': MapsTo ?id ?v' (sstore ???'),
    MapsTo_??__m: MapsTo ?id ?v__m (sstore ???__m)
    |- _
  ] =>
    assert (Heq : v' = v__m)
      by (eapply MapsTo_fun; eauto;
          erw_IMDS_sstore_m IMDS;
          eauto)
  | [
    IMDS: IsMergedDState ??? ???' ???'' ???__m,
    MapsTo_??'': MapsTo ?id ?v'' (sstore ???''),
    MapsTo_??__m: MapsTo ?id ?v__m (sstore ???__m)
    |- _
  ] =>
    assert (Heq : v'' = v__m)
      by (eapply MapsTo_fun; eauto;
          erw_IMDS_sstore_m IMDS;
          eauto)
  end.
