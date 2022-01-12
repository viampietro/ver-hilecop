(** * Tactis for List Monad Functions *)

Require Import ListMonad.
Require Import ListMonadFacts.
Require Import StateAndErrorMonad.
Require Import StateAndErrorMonadTactics.

Ltac solveSInv H :=
  match type of H with
  | (OK _ _ = OK _ _) => try (minv H)
  | (Get _ = OK _ _) => try (minv H)
  | (Put _ _ = OK _ _) => try (minv H)
  | (Ret _ _ = OK _ _) => try (minv H)
  | (Err _ _ = OK _ _) => try (minv H)
  | (Error _ = OK _ _) => try (minv H)
  | (Bind ?F ?G ?S = OK ?X ?S') =>
    let x := fresh "x" in
    let s := fresh "s" in
    let EQ1 := fresh "EQ" in
    let EQ2 := fresh "EQ" in
    destruct (Bind_inversion _ _ _ F G X S S' H) as [x [s [EQ1 EQ2]]];
    clear H;
    match type of EQ1 with
    | _ = OK _ ?s2 =>
      (transitivity s2; [ try (solveSInv EQ1) | try (solveSInv EQ2) ])
      || (try (solveSInv EQ1); try (solveSInv EQ2))
    end
  | (if ?c then _ else _) _ = OK _ _ => destruct c; try (solveSInv H)
  | (tmap _ _ _ ?s = OK _ ?s') =>
    pattern s, s'; eapply (tmap_inv_state H); eauto with typeclass_instances
  | (map _ _ ?s = OK _ ?s') =>
    pattern s, s'; eapply (map_inv_state H); eauto with typeclass_instances
  | (iter ?f _ ?s = OK _ ?s') =>
    pattern s, s'; eapply (iter_inv_state H); eauto with typeclass_instances
  | (fold_left ?f _ _ ?s = OK _ ?s') =>
    pattern s, s'; eapply (foldl_inv_state H); eauto with typeclass_instances
  | (foreach ?f _ ?s = OK _ ?s') =>
    pattern s, s'; eapply (foreach_inv_state H); eauto with typeclass_instances
  | (getv _ _ _ ?s = OK _ ?s') => rewrite (getv_inv_state H); auto
  | (?F _ _ _ _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); try (solveSInv H)
  | (?F _ _ _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); try (solveSInv H)
  | (?F _ _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); try (solveSInv H)
  | (?F _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); try (solveSInv H)
  | (?F _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); try (solveSInv H)
  | (?F _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); try (solveSInv H)
  | (?F _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); try (solveSInv H)
  | (?F _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); try (solveSInv H)
  end.

Ltac solve_listm H :=
  match type of H with
  | (tmap _ _ _ ?s = OK _ ?s') =>
    pattern s, s'; eapply (tmap_inv_state H); eauto with typeclass_instances; clear H
  | (map _ _ ?s = OK _ ?s') =>
    pattern s, s'; eapply (map_inv_state H); eauto with typeclass_instances; clear H
  | (iter ?f _ ?s = OK _ ?s') =>
    pattern s, s'; eapply (iter_inv_state H); eauto with typeclass_instances; clear H
  | (fold_left ?f _ _ ?s = OK _ ?s') =>
    pattern s, s'; eapply (foldl_inv_state H); eauto with typeclass_instances; clear H
  | (find ?f _ ?s = OK _ ?s') =>
    pattern s, s'; eapply (find_inv_state H); eauto with typeclass_instances; clear H
  | (foreach ?f _ ?s = OK _ ?s') =>
    pattern s, s'; eapply (foreach_inv_state H); eauto with typeclass_instances; clear H
  | (getv _ _ _ ?s = OK _ ?s') => rewrite (getv_inv_state H); clear H; try reflexivity                                                              
  end.

  
