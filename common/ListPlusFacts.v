(** * More Facts about Lists *)

Require Import common.Coqlib.
Require Import common.ListsPlus.

(** ** Facts about [Map] *)

Section Map.

  Lemma Map_in :
    forall {A B : Type} {f : A -> B} {lofAs lofBs},
      Map f lofAs lofBs ->
      forall {a},
        List.In a lofAs ->
        List.In (f a) lofBs.
  Proof.
    induction 1.
    - contradiction.
    - inversion 1.
      + lazymatch goal with | [ H: _ = _ |- _] => rewrite H; apply in_eq end.
      + apply in_cons; apply IHMap; auto.
  Defined.
  
End Map.


(** ** Facts about [FoldL] *)

Section FoldL.

  Lemma FoldL_in_acc :
    forall {A B : Type}
           (f : list A -> B -> list A)
           (l : list B)
           (acc acc' : list A)
           (a : A),
      FoldL f l acc acc' ->
      List.In a acc ->
      (forall m b, List.In a m -> List.In a (f m b)) ->
      List.In a acc'.
  Proof.
    induction 1; intros;
      [ assumption | apply IHFoldL; auto].
  Qed.
  
  
End FoldL.
