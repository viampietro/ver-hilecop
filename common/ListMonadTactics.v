(** * Tactis for List Monad Functions *)

Require Import ListMonad.
Require Import ListMonadFacts.
Require Import StateAndErrorMonad.
Require Import StateAndErrorMonadTactics.

Ltac solveSInv H :=
  match type of H with
  | (OK _ _ = OK _ _) => try (minv1 H)
  | (Get _ = OK _ _) => try (minv1 H)
  | (Put _ _ = OK _ _) => try (minv1 H)
  | (Ret _ _ = OK _ _) => try (minv1 H)
  | (Err _ _ = OK _ _) => try (minv1 H)
  | (Error _ = OK _ _) => try (minv1 H)
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
      || auto
    end    
  | (if ?c then _ else _) _ = OK _ _ => destruct c; try (solveSInv H)
  | iter ?f _ _ = OK _ _ =>
    eapply iter_inv_state; eauto with typeclass_instances
  | titer ?f _ _ _ = OK _ _ =>
    eapply titer_inv_state; eauto with typeclass_instances
  | foreach ?f _ _ = OK _ _ =>
    eapply foreach_inv_state; eauto with typeclass_instances
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

Definition NatCounter := @Mon nat.

Require Import List.
Import ListNotations.

Definition suml (l : list nat) (x : { n : nat | n > 0 }) : NatCounter unit :=
  let (m, gt0m) := x in
  do _ <- iter (fun n s => OK tt (n + s)) l;
  iter (fun n s => OK tt (n + s)) (l ++ [m]).

Compute (suml [1; 2; 3; 4] (exist _ 1 (Gt.gt_Sn_O 0)) 0).

Lemma suml_inv_S :
  forall {l x s v s'},
    suml l x s = OK v s' ->
    ((fun s1 s2 => s1 > 0 -> s2 > 0) s s').
Proof.
  intros until s'; intros e.
  cbv beta.
  pattern s, s'.
Admitted.
  
