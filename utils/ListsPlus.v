(** Exports all modules pertaining to lists and defines new lists
    predicates.  The predicates are useful in the formalization 
    and the proofs.
 *)

Require Import Coqlib.
Require Import Omega.
Require Import Classical_Prop.

Require Export FstSplit.
Require Export InAndNoDup.

(** ** Predicates IsDecListCons, IsDecListApp and facts. *)

Set Implicit Arguments.

Section DecreasedList.

  (** List l is a decreased or equal version of list l'. 
      l' is built from l by adding elements in the front (cons).
       
      Useful for proof involving recursion on lists.  *)
  
  Inductive IsDecListCons {A: Type} : list A -> list A -> Prop :=
  | IsDecListCons_refl : forall l : list A, IsDecListCons l l
  | IsDecListCons_eq : forall (a : A) (l : list A), IsDecListCons l (a :: l)
  | IsDecListCons_cons :
      forall (a : A) (l l' : list A),
      IsDecListCons l l' ->      
      IsDecListCons l (a :: l').

  (** Facts about IsDecListCons. *)
  
  Lemma is_dec_list_cons_nil {A : Type} :
    forall (l : list A), IsDecListCons [] l.
  Proof.
    induction l.
    - apply IsDecListCons_refl.
    - apply IsDecListCons_cons; assumption.
  Qed.

  Lemma is_dec_list_cons_app_eq {A : Type} :
    forall (l l' : list A),
      IsDecListCons l (l' ++ l).
  Proof.
    induction l'.

    (* BASE CASE *)
    - simpl; apply IsDecListCons_refl.

    (* INDUCTION CASE *)
    - rewrite <- app_comm_cons;
        apply IsDecListCons_cons;
        assumption.
  Qed.
  
  Lemma is_dec_list_cons_incl {A : Type} :
    forall l' l : list A, IsDecListCons l l' -> incl l l'.
  Proof.
    induction l'.
    - intros l His_dec x Hin_l.
      inversion His_dec.
      rewrite H0 in Hin_l.
      inversion Hin_l.
    - intros l His_dec; inversion His_dec.
      + apply incl_refl.
      + intros x Hin_l'; apply in_cons; assumption.
      + apply IHl' in H1.
        intros x Hin_l.
        apply H1 in Hin_l.
        apply in_cons with (a := a) in Hin_l.
        assumption.      
  Qed.

  Lemma is_dec_list_cons_cons {A : Type} :
    forall (a : A) (l' l : list A), IsDecListCons (a :: l) l' -> IsDecListCons l l'.
  Proof.
    intros a l'.
    induction l'.
    - intros l His_dec; inversion His_dec.
    - intros l His_dec; inversion His_dec.
      + apply IsDecListCons_eq.
      + apply IsDecListCons_cons; apply IsDecListCons_eq.
      + apply IsDecListCons_cons; apply (IHl' l H1).
  Qed.

  (** If l' has no duplicates and l is a decreased version of l' then
      l has no duplicates. *)
  
  Lemma nodup_is_dec_list_cons {A : Type} :
    forall (l' l : list A),
      NoDup l' ->
      IsDecListCons l l' ->
      NoDup l.
  Proof.
    induction l'; intros l Hnodup_l' His_dec.
    
    (* BASE CASE *)
    - inversion His_dec; apply NoDup_nil.

    (* INDUCTION CASE *)
    - inversion His_dec.
      
      (* Case IsDecListCons_refl *)
      + assumption.

      (* Case IsDecListCons_eq *)
      + rewrite NoDup_cons_iff in Hnodup_l';
          apply proj2 in Hnodup_l';
          assumption.

      (* Case IsDecListCons_cons *)
      + rewrite NoDup_cons_iff in Hnodup_l';
          apply proj2 in Hnodup_l';
          apply (IHl' l Hnodup_l' H1).
  Qed.

  (** If IsDecListCons l l' then it's possible to
      decompose l' in (m ++ l). *)
  
  Lemma is_dec_list_cons_exists_app {A : Type} :
    forall (l' l : list A),
      IsDecListCons l l' -> exists l'' : list A, l' = l'' ++ l.
  Proof.
    induction l'; intros l His_dec.

    (* BASE CASE *)
    - inversion His_dec.
      exists []; rewrite app_nil_r; auto.

    (* INDUCTION CASE *)
    - inversion His_dec.
      + exists []. simpl. reflexivity.
      + exists [a]. simpl. reflexivity.
      + specialize (IHl' l H1) as Hex.
        inversion_clear Hex as (m & Heq_l'_ml).
        rewrite Heq_l'_ml.
        exists (a :: m).
        auto.
  Qed.

  (** concat is a morphism for IsDecListCons. *)
  
  Lemma is_dec_list_cons_concat {A : Type} :
    forall (ll ll' : list (list A)),
      IsDecListCons ll ll' -> IsDecListCons (concat ll) (concat ll').
  Proof.
    intros ll ll' His_dec.
    specialize (is_dec_list_cons_exists_app His_dec) as Hex_l''.
    inversion_clear Hex_l'' as (l'' & Heq_l'_ll'').
    rewrite Heq_l'_ll''.
    rewrite concat_app.
    apply is_dec_list_cons_app_eq.
  Qed.
  
  (** List l is a decreased or equal version of list l'. 
      l' is built from l by adding elements in the front (cons).
       
      Useful for proof involving recursion on lists.  *)

  Inductive IsDecListApp {A : Type} : list A -> list A -> Prop :=
  | IsDecListApp_refl : forall l : list A, IsDecListApp l l
  | IsDecListApp_eq : forall (a : A) (l : list A), IsDecListApp l (l ++ [a])
  | IsDecListApp_cons :
      forall (a : A) (l l' : list A),
        IsDecListApp l l' ->
        IsDecListApp l (l' ++ [a]).
  
End DecreasedList.

(** ** Predicate IsPredInList and facts. *)

Section PredInList.

  Variable A : Type.
    
  (** Tells if x is a predecessor of y in list l. 
      x and y are possibly equal and list l
      possibly contains duplicates. *)
  
  Inductive IsPredInList (x y : A) : list A -> Prop :=
  | IsPredInList_eq :
      forall l : list A, IsPredInList x y (x :: y :: l)
  | IsPredInList_rm_snd :
      forall (a : A) (l : list A), IsPredInList x y (x :: l) ->
                                   IsPredInList x y (x :: a :: l)
  | IsPredInList_rm_fst : 
      forall (a : A) (l : list A), IsPredInList x y l ->
                                   IsPredInList x y (a :: l).

  (** IsPredInList with no duplicates in list l, x and y different. *)
  
  Definition IsPredInNoDupList (x y : A) (l : list A) :=
    x <> y /\ NoDup l /\ IsPredInList x y l.

  (** Facts about IsPredInList and IsPredInNoDuplist. *)
  
  Lemma not_is_pred_in_list_nil :
    forall (x y : A), ~IsPredInList x y [].
  Proof.
    intros x y His_pred.
    inversion His_pred.
  Qed.

  Lemma is_pred_in_list_in_tail :
    forall (x y : A) (l : list A), In y l -> IsPredInList x y (x :: l).
  Proof.
    induction l.
    - intro Hnot_in; inversion Hnot_in.
    - intro Hin_y_l; inversion Hin_y_l.
      + rewrite H; apply IsPredInList_eq.
      + apply IsPredInList_rm_snd; apply (IHl H).
  Qed.
  
  Theorem is_pred_in_dec_list :
    forall (l l' : list A) (x y : A),
      IsPredInList x y l -> IsDecListCons l l' -> NoDup l' -> IsPredInList x y l'.
  Proof.
    induction l'.
    - intros x y His_pred His_dec Hnodup.
      induction l.
      + inversion His_pred.
      + inversion His_dec.
    - intros x y His_pred His_dec Hnodup.
      inversion His_dec.
      + rewrite <- H0; assumption.
      + rewrite <- H2; apply IsPredInList_rm_fst; assumption. 
      + apply IsPredInList_rm_fst.
        -- apply NoDup_cons_iff in Hnodup; apply proj2 in Hnodup.
           apply (IHl' x y His_pred H1 Hnodup).
  Qed.

  Lemma is_pred_cons_diff :
    forall (l : list A) (x y a : A) , IsPredInList x y (a :: l) ->
                                      x <> a ->
                                      IsPredInList x y l.
  Proof.
    induction l; intros x y a' His_pred Hdiff.
    - inversion His_pred; inversion H0.
    - inversion His_pred.
      + contradiction.
      + contradiction.
      + assumption.
  Qed.

  Lemma is_pred_in_tail :
    forall (l : list A) (x y : A) , IsPredInNoDupList x y (x :: l) -> In y l.
  Proof.
    induction l; intros x y His_pred;
      unfold IsPredInNoDupList in His_pred; decompose [and] His_pred.
    - inversion H2; inversion H3.
    - inversion H2.
      + apply in_eq.
      + apply NoDup_remove with (l := [x]) in H1.
        apply proj1 in H1.
        unfold IsPredInNoDupList in IHl.
        specialize (IHl x y (conj H (conj H1 H3))) as Hin_y_l.
        apply in_cons.
        assumption.
      + inversion H1.
        apply not_in_cons in H7.
        apply proj1 in H7.
        specialize (is_pred_cons_diff H3 H7) as His_pred_in_l.
        apply IsPredInList_rm_fst with (a := x) in His_pred_in_l.
        apply in_cons.
        apply NoDup_remove with (l := [x]) in H1.
        apply proj1 in H1.
        unfold IsPredInNoDupList in IHl.
        specialize (IHl x y (conj H (conj H1 His_pred_in_l))) as Hin_y_l.
        assumption.
  Qed.

  Theorem not_is_pred_in_list_if_hd :
    forall (l : list A) (x y : A) , ~IsPredInNoDupList x y (y :: l).
  Proof.
    induction l; intros x y His_pred.
    - unfold IsPredInNoDupList in His_pred.
      decompose [and] His_pred.
      inversion H2; inversion H3.
    - unfold IsPredInNoDupList in His_pred.
      decompose [and] His_pred.
      inversion H2.
      + contradiction.
      + contradiction.
      + assert (Hvee := classic (x = a)).
        elim Hvee.
        -- intro Heq_xa.
           rewrite Heq_xa in H3.
           rewrite Heq_xa in H.
           apply NoDup_cons_iff in H1.
           elim H1; intros Hnot_in_y Hnodup.
           specialize (is_pred_in_tail (conj H (conj Hnodup H3))) as Hin_y_l.
           apply in_cons with (a := a) in Hin_y_l.
           contradiction.
        -- intro Hneq_xa.
           specialize (is_pred_cons_diff H3 Hneq_xa) as His_pred_in_l.
           apply IsPredInList_rm_fst with (a := y) in His_pred_in_l.
           apply NoDup_remove with (l := [y]) in H1.
           apply proj1 in H1.
           unfold IsPredInNoDupList in IHl.
           apply (IHl x y (conj H (conj H1 His_pred_in_l))).
  Qed.

  Theorem not_is_pred_in_dec_list :
    forall (l' l : list A) (x y : A),
      IsDecListCons (y :: l) l' ->
      In x l ->
      ~IsPredInNoDupList x y l'.
  Proof.
    induction l'; intros l x y His_dec Hin_x_l.
    - inversion His_dec.
    - intro His_pred.
      unfold IsPredInNoDupList in His_pred; decompose [and] His_pred.
      rename H into Hneq_xy; rename H1 into Hnodup; clear His_pred; rename H2 into His_pred.
      inversion His_pred.
      + inversion His_dec.
        -- rewrite <- H3 in H0; contradiction.
        -- rewrite <- H4 in Hnodup.
           rewrite <- H0 in Hnodup.
           apply in_cons with (a := y) in Hin_x_l.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
        -- apply is_dec_list_cons_cons in H3.
           apply is_dec_list_cons_incl in H3.
           apply H3 in Hin_x_l.
           rewrite <- H0 in Hnodup.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
      + inversion His_dec.
        -- rewrite <- H4 in H; contradiction.
        -- rewrite <- H5 in Hnodup.
           rewrite <- H in Hnodup.
           apply in_cons with (a := y) in Hin_x_l.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
        -- apply is_dec_list_cons_cons in H4.
           apply is_dec_list_cons_incl in H4.
           apply H4 in Hin_x_l.
           rewrite <- H in Hnodup.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
      + inversion His_dec.
        -- assert (Hnot_is_pred : ~IsPredInNoDupList x y (y :: l))
            by apply not_is_pred_in_list_if_hd.
           rewrite <- H4 in His_pred; rewrite <- H4 in Hnodup.
           rewrite <- H5 in His_pred; rewrite <- H5 in Hnodup.
           specialize (conj Hneq_xy (conj Hnodup His_pred)) as His_pred'.
           contradiction.
        -- assert (Hnot_is_pred : ~IsPredInNoDupList x y (y :: l))
            by apply not_is_pred_in_list_if_hd.
           rewrite <- H5 in Hnodup; rewrite <- H5 in H0.
           apply NoDup_cons_iff in Hnodup.
           apply proj2 in Hnodup.
           specialize (conj Hneq_xy (conj Hnodup H0)) as His_pred'.
           contradiction.
        -- apply NoDup_cons_iff in Hnodup.
           apply proj2 in Hnodup.
           apply (IHl' l x y H4 Hin_x_l (conj Hneq_xy (conj Hnodup H0))).
  Qed.
  
End PredInList.



