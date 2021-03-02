(** * More Facts about Lists *)

Require Import common.Coqlib.
Require Import common.InAndNoDup.
Require Import common.FstSplit.
Require Import common.ListPlus.
Require Import common.SetoidListFacts.
Require Import common.GlobalFacts.

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

(** ** Facts about [Sig_in_List] *)

Section SIL.

  Lemma SIL_fs_setv :
    forall {A B : Type} {P : A -> Prop}
           {eqA_dec : forall x y : A, {x = y} + {x <> y}}
           {x : {a | P a} } {v : B}
           {l : list ({ a : A | P a} * B)},
      Sig_in_List (fs l) -> Sig_in_List (fs (setv (seqdec eqA_dec) x v l)).
  Proof.
    intros until l; functional induction (setv (seqdec eqA_dec) x v l) using setv_ind.
    (* CASE l = [] *)
    intros SIL; destruct SIL as (InA_, NoDupA_); specialize (InA_ x).
    inversion InA_.
    (* CASE [eqk x a] *)
    rewrite fs_eq_cons_app; intros SIL; cbn in SIL.
    rewrite fs_eq_cons_app; cbn.
    destruct SIL as (InA_, NoDupA_).
    split.
    intros y; specialize (InA_ y).
    inversion_clear InA_;
      [ eapply InA_cons_hd; unfold seq; rewrite _x; assumption | eauto ].
    constructor; [  | eauto with setoidl ].
    inversion_clear NoDupA_; clear e1; symmetry in _x; eauto 2 with setoidl typeclass_instances.    
    (* CASE [~eqk x a] *)
    rewrite fs_eq_cons_app; intros SIL; cbn in SIL.
    rewrite fs_eq_cons_app; cbn.
    destruct SIL as (InA_, NoDupA_).
    split.
    intros y; specialize (InA_ y).
    inversion_clear InA_;
      [ eapply InA_cons_hd; unfold seq; rewrite H; reflexivity | eauto with setoidl ].
    eapply InA_cons_tl; eauto with setoidl.
    eapply InA_fs_InA_fs_setv; eauto with typeclass_instances.
    constructor; inversion NoDupA_; eauto 2 with setoidl typeclass_instances.
  Qed.

  
End SIL.
