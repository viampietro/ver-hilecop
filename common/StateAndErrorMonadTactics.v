(** * Tactics for the State-and-Error Monad *)

Require Import common.StateAndErrorMonad.

Remark Bind_inversion:
  forall (state A B : Type) (f: Mon A) (g: A -> Mon B)
         (y: B) (s1 s3: state),
    Bind f g s1 = OK y s3 ->
    exists x, exists s2,
        f s1 = OK x s2 /\ g x s2 = OK y s3.
Proof.
  intros *. unfold Bind. destruct (f s1); intros.
  discriminate.
  exists a; exists s.
  destruct (g a s); inversion H; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (OK _ _ = OK _ _) =>
    inversion H; clear H; try subst
  | (Get _ = OK _ _) =>
    inversion H; clear H; try subst
  | (Put _ _ = OK _ _) =>
    inversion H; clear H; try subst
  | (Ret _ _ = OK _ _) =>
    inversion H; clear H; try subst
  | (Err _ _ = OK _ _) =>
    discriminate
  | (Error _ = OK _ _) =>
    discriminate
  | (Bind ?F ?G ?S = OK ?X ?S') =>
    let x := fresh "x" in
    let s := fresh "s" in
    let EQ1 := fresh "EQ" in
    let EQ2 := fresh "EQ" in
    destruct (Bind_inversion _ _ _ F G X S S' H) as [x [s [EQ1 EQ2]]];
    clear H;
    try (monadInv1 EQ2)
  end.

Ltac monadInv H :=
  match type of H with
  | (Get _ = OK _ _) => monadInv1 H
  | (Put _ = OK _ _) => monadInv1 H
  | (Ret _ _ = OK _ _) => monadInv1 H
  | (Err _ _ = OK _ _) => monadInv1 H
  | (Error _ = OK _ _) => monadInv1 H
  | (Bind ?F ?G ?S = OK ?X ?S') => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

Ltac monadFullInv H :=
  match type of H with
  | (Get _ = OK _ _) => monadInv1 H
  | (Put _ _ = OK _ _) => monadInv1 H
  | (Ret _ _ = OK _ _) => monadInv1 H
  | (Err _ _ = OK _ _) => monadInv1 H
  | (Error _ = OK _ _) => monadInv1 H
  | (Bind ?F ?G ?S = OK ?X ?S') =>
    let x := fresh "x" in
    let s := fresh "s" in
    let EQ1 := fresh "EQ" in
    let EQ2 := fresh "EQ" in
    destruct (Bind_inversion _ _ _ F G X S S' H) as [x [s [EQ1 EQ2]]];
    clear H;
    try (monadFullInv EQ2);
    try (monadFullInv EQ1)
  | (?F _ _ _ _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadFullInv H
  | (?F _ _ _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadFullInv H
  | (?F _ _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadFullInv H
  | (?F _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadFullInv H
  | (?F _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadFullInv H
  | (?F _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadFullInv H
  | (?F _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadFullInv H
  | (?F _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); monadFullInv H
  end.

Ltac minv1 H :=
  match type of H with
  | (OK _ _ = OK _ _) =>
    inversion H; clear H; try subst
  | (Get _ = OK _ _) =>
    inversion H; clear H; try subst
  | (Put _ _ = OK _ _) =>
    inversion H; clear H; try subst
  | (Ret _ _ = OK _ _) =>
    inversion H; clear H; try subst
  | (Err _ _ = OK _ _) =>
    discriminate
  | (Error _ = OK _ _) =>
    discriminate
  end.

Ltac destrm H :=
  lazymatch type of H with
  | ((if ?c then _ else _) _ = OK _ _) => destruct c; destrm H
  | ((let '_ := ?y in _) _ = OK _ _) => destruct y; destrm H
  | ((let _ := ?y in _) _ = OK _ _) => destruct y; destrm H
  | _ => idtac
  end.

Ltac minv H :=
  lazymatch type of H with
  | (OK _ _ = OK _ _) => inversion H; clear H; try subst (* try (minv1 H) *)
  | (Get _ = OK _ _) => inversion H; clear H; try subst (* try (minv1 H) *)
  | (Put _ _ = OK _ _) => inversion H; clear H; try subst (* try (minv1 H) *)
  | (Ret _ _ = OK _ _) => inversion H; clear H; try subst (* try (minv1 H) *)
  | (Err _ _ = OK _ _) => inversion H; clear H; try subst (* try (minv1 H) *)
  | (Error _ = OK _ _) => inversion H; clear H; try subst (* try (minv1 H) *)
  | (Bind ?F ?G ?S = OK ?X ?S') =>
    let x := fresh "x" in
    let s := fresh "s" in
    let EQ1 := fresh "EQ" in
    let EQ2 := fresh "EQ" in
    destruct (Bind_inversion _ _ _ F G X S S' H) as [x [s [EQ1 EQ2]]];
    clear H;
    try (minv EQ2);
    try (minv EQ1)
  | ((if ?c then _ else _) _ = OK _ _) => destrm H; minv H (* destruct c; try (minv H) *)
  | ((let '_ := ?y in _) _ = OK _ _) => destrm H; minv H (* destruct y; try (minv H) *)
  | ((let _ := ?y in _) _ = OK _ _) => destrm H; minv H (* destruct y; try (minv H) *)
  | (?F _ _ _ _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); minv H
  | (?F _ _ _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); minv H
  | (?F _ _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); minv H
  | (?F _ _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); minv H
  | (?F _ _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); minv H
  | (?F _ _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); minv H
  | (?F _ _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); minv H
  | (?F _ = OK _ _) =>
    ((progress simpl in H) || unfold F in H); minv H
  end.


