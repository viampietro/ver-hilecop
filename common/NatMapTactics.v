(** * Facts about NatMap *)

Require Import common.Coqlib.
Require Import NatMap.

(** Looks for two MapsTo proofs where the same key maps to two
    different values that are structurally different (i.e, built from
    two different constructors). *)

Ltac mapsto_discriminate_simpl :=
  lazymatch goal with
  | [ H1: MapsTo ?k ?v1 ?m, H2: MapsTo ?k ?v2 ?m |- _ ] =>
    generalize (MapsTo_fun H1 H2); intros e;
    tryif (assert_fails (discriminate e))
    then fail "Term" v1 "=" v2 "is not discriminable"
    else discriminate e
  | [ H: MapsTo ?k ?v1 (add ?k ?v2 ?m) |- _] =>
    generalize (MapsTo_add_eqv H); intros e;
    tryif (assert_fails (discriminate e))
    then fail "Term" v1 "=" v2 "is not discriminable"
    else discriminate e
  | _ => fail "MapsTo proofs not found"
  end.

Ltac mapsto_discriminate_or :=
  lazymatch goal with
  | [ H: MapsTo ?k ?v ?m \/ MapsTo ?k ?v' ?m |- _ ] =>
    inversion H; mapsto_discriminate_simpl
  | _ => fail "Found no term matching MapsTo ?k ?v ?m \/ MapsTo ?k ?v' ?m"
  end.

Ltac mapsto_discriminate := mapsto_discriminate_simpl || mapsto_discriminate_or.

Ltac rw_mapsto :=
  match goal with
  | [ H: _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?a <-> MapsTo _ _ ?b ] =>
    erewrite H; eauto; try (reflexivity)
  | [ H: _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?b <-> MapsTo _ _ ?a ] => 
    erewrite <- H; eauto; try (reflexivity)
  | [ H: _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?a ] => 
    erewrite H; eauto; try (reflexivity)
  | [ H: _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?b ] => 
    erewrite <- H; eauto; try (reflexivity)
  | [ H: _ -> _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?a <-> MapsTo _ _ ?b ] =>
    erewrite H; eauto; try (reflexivity)
  | [ H: _ -> _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?b <-> MapsTo _ _ ?a ] =>
    erewrite <- H; eauto; try (reflexivity)
  | [ H: _ -> _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?a ] => 
    erewrite H; eauto; try (reflexivity)
  | [ H: _ -> _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?b ] => 
    erewrite <- H; eauto; try (reflexivity)
  | [ H: _ -> _ -> _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?a <-> MapsTo _ _ ?b ] =>
    erewrite H; eauto; try (reflexivity)
  | [ H: _ -> _ -> _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?b <-> MapsTo _ _ ?a ] =>
    erewrite <- H; eauto; try (reflexivity)
  | [ H: _ -> _ -> _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?a ] => 
    erewrite H; eauto; try (reflexivity)
  | [ H: _ -> _ -> _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?b ] => 
    erewrite <- H; eauto; try (reflexivity)
  end.

Ltac mapsto_not_in_contrad :=
  match goal with
  | [ H1: ~NatMap.In ?k ?m, H2: NatMap.MapsTo ?k ?v ?m |- _ ] =>
    elimtype False; apply H1; exists v; auto
  end.

Ltac solve_mapsto_iff :=
  match goal with
  | |- MapsTo ?k1 ?v1 ?m <-> MapsTo ?k1 ?v1 (add ?k2 ?v2 ?m) =>
    split; intros; destruct (Nat.eq_dec k1 k2);
    [ subst; mapsto_not_in_contrad
    | eauto with mapsto
    | subst; mapsto_discriminate
    | eauto with mapsto ]
  | |- MapsTo ?k1 ?v1 (add ?k2 ?v2 ?m) <-> MapsTo ?k1 ?v1 ?m =>
    split; intros; destruct (Nat.eq_dec k1 k2);
    [ subst; mapsto_discriminate
    | eauto with mapsto
    | subst; mapsto_not_in_contrad
    | eauto with mapsto ]
  end.
