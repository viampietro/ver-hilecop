(** * Facts about NatMap *)

Require Import NatMap.

(** Looks for two MapsTo proofs where the same key maps to two
    different values that are structurally different (i.e, built from
    two different constructors). *)

Ltac mapsto_discriminate_simpl :=
  lazymatch goal with
  | [ H: MapsTo ?k ?v ?m, H': MapsTo ?k ?v' ?m |- _ ] =>
    generalize (MapsTo_fun H H'); intros Heq;
    tryif (assert_fails (discriminate Heq))
    then fail "Term" v "=" v' "is not discriminable"
    else discriminate Heq
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
  | [ H: _ -> _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?a <-> MapsTo _ _ ?b ] =>
    erewrite H; eauto; try (reflexivity)
  | [ H: _ -> _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?b <-> MapsTo _ _ ?a ] =>
    erewrite <- H; eauto; try (reflexivity)
  | [ H: _ -> _ -> _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?a <-> MapsTo _ _ ?b ] =>
    erewrite H; eauto; try (reflexivity)
  | [ H: _ -> _ -> _ -> MapsTo _ _ ?a <-> MapsTo _ _ ?b |- MapsTo _ _ ?b <-> MapsTo _ _ ?a ] =>
    erewrite <- H; eauto; try (reflexivity)
  end.
