Require Import Hilecop.SPN.
Require Import Omega.
Require Import Classical_Prop.

Set Implicit Arguments.

(*! ============================= !*)
(*! ======= Spn Semantics ======= !*)
(*! ============================= !*)

(** * Preliminary definitions *)

(** ** Predicate IsDecreasedList and facts. *)

Section DecreasedList.

  Variable A : Type.
  
  (** List l is a decreased version of list l'. Useful for proof involving recursion on lists.  *)

  Inductive IsDecreasedList : list A -> list A -> Prop :=
  | IsDecreasedList_refl : forall l : list A, IsDecreasedList l l
  | IsDecreasedList_eq : forall (a : A) (l : list A), IsDecreasedList l (a :: l)
  | IsDecreasedList_cons :
      forall (a : A) (l l' : list A),
      IsDecreasedList l l' ->      
      IsDecreasedList l (a :: l').
    
  Lemma is_decreased_list_nil :
    forall (l : list A), IsDecreasedList [] l.
  Proof.
    induction l.
    - apply IsDecreasedList_refl.
    - apply IsDecreasedList_cons; assumption.
  Qed.
  
  Lemma is_decreased_list_incl :
    forall l' l : list A, IsDecreasedList l l' -> incl l l'.
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

  Lemma is_decreased_list_cons :
    forall (a : A) (l' l : list A), IsDecreasedList (a :: l) l' -> IsDecreasedList l l'.
  Proof.
    intros a l'.
    induction l'.
    - intros l His_dec; inversion His_dec.
    - intros l His_dec; inversion His_dec.
      + apply IsDecreasedList_eq.
      + apply IsDecreasedList_cons; apply IsDecreasedList_eq.
      + apply IsDecreasedList_cons; apply (IHl' l H1).
  Qed.

End DecreasedList.

(** ** Predicate IsPredInList and facts. *)

Section PredInList.

  Variable A : Type.
    
  (** Predicate, true if x is a predecessor of y in list l. *)
  
  Inductive IsPredInList (x y : A) : list A -> Prop :=
  | IsPredInList_eq :
      forall l : list A, IsPredInList x y (x :: y :: l)
  | IsPredInList_rm_snd :
      forall (a : A) (l : list A), IsPredInList x y (x :: l) -> IsPredInList x y (x :: a :: l)
  | IsPredInList_rm_fst : 
      forall (a : A) (l : list A), IsPredInList x y l ->
                                   IsPredInList x y (a :: l).

  Definition IsPredInNoDupList (x y : A) (l : list A) :=
    x <> y /\ NoDup l /\ IsPredInList x y l.
  
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
      IsPredInList x y l -> IsDecreasedList l l' -> NoDup l' -> IsPredInList x y l'.
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
      IsDecreasedList (y :: l) l' ->
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
        -- apply is_decreased_list_cons in H3.
           apply is_decreased_list_incl in H3.
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
        -- apply is_decreased_list_cons in H4.
           apply is_decreased_list_incl in H4.
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

(** In all the following definitions, (IsWellDefinedSpn spn) is a necessary condition. *)

(** HasHigherPriority: ∀ t ∈ T, t' ∈ T/{t}, t ≻ t' *)

Definition HasHigherPriority
           (spn : Spn)
           (t t' : Trans)
           (pgroup : list Trans) :=
    IsWellDefinedSpn spn /\
    In pgroup spn.(priority_groups) /\
    In t pgroup /\
    In t' pgroup /\
    IsPredInNoDupList t t' pgroup.

(** PreSum: Sums all weight of edges coming from place p to transitions of the l list. *)

Fixpoint pre_sum (spn : Spn) (p : Place) (l : list Trans) {struct l} : nat :=
  match l with
  | t :: tail => (pre spn t p) + pre_sum spn p tail
  | [] => 0
  end.

Functional Scheme pre_sum_ind := Induction for pre_sum Sort Prop.

Inductive PreSum (spn : Spn) (p : Place) : list Trans -> nat -> Prop :=
| PreSum_nil :
    PreSum spn p [] 0
| PreSum_cons :
    forall (l : list Trans)
           (t : Trans)
           (sum : nat),
      PreSum spn p l sum ->
      PreSum spn p (t :: l) ((pre spn t p) + sum).

(** PreSum with some conditions about well-definedness. *)

Definition PreSumWD (spn : Spn) (p : Place) (l : list Trans) (sum : nat) :=
  IsWellDefinedSpn spn /\ In p spn.(places) /\ incl l spn.(transs) /\
  PreSum spn p l sum. 

(** PostSum: Sums all weight of edges coming from transitions of the l list to place p. *)

Inductive PostSum (spn : Spn) (p : Place) : list Trans -> nat -> Prop :=
| PostSum_nil :
    PostSum spn p [] 0
| PostSum_cons :
    forall (l : list Trans)
      (t : Trans)
      (sum : nat),
      PostSum spn p l sum ->
      PostSum spn p (t :: l) ((post spn t p) + sum).

(** PostSum with some conditions about well-definedness. *)

Definition PostSumWD (spn : Spn) (p : Place) (l : list Trans) (sum : nat) :=
  IsWellDefinedSpn spn /\ In p spn.(places) /\ incl l spn.(transs) /\
  PostSum spn p l sum. 

(** IsSensitized:
    ∀ t ∈ T, marking m, t ∈ sens(m) if
    ∀ p ∈ P, m(p) ≥ Pre(p, t) ∧ 
             m(p) ≥ Pre_t(p, t) ∧ 
             (m(p) < Pre_i(p, t) ∨ Pre_i(p, t) = 0) *)

Definition IsSensitized
           (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans) : Prop :=
  IsWellDefinedSpn spn /\
  MarkingHaveSameStruct spn.(initial_marking) marking /\
  In t spn.(transs) /\
  forall (p : Place)
         (n : nat),
    In (p, n) marking ->
    (pre spn t p) <= n  /\
    (test spn t p) <= n  /\
    (n < (inhib spn t p) \/ (inhib spn t p) = 0).

(** SpnIsFirable:
 
      ∀ t ∈ T, state s = (m), marking m, t ∈ firable(s) if 
      t ∈ sens(m) *)

Definition SpnIsFirable
           (spn : Spn)
           (state : SpnState)
           (t : Trans) :=
  IsWellDefinedSpn spn /\
  IsWellDefinedSpnState spn state /\
  In t spn.(transs) /\
  IsSensitized spn state.(marking) t.

(** * Semantics definition *)

(** Represents the two clock events regulating the Spn evolution. *)

Inductive Clock : Set :=
| falling_edge : Clock
| raising_edge : Clock.

(** Represents the Spn Semantics  *)

Inductive SpnSemantics (spn : Spn) (s s' : SpnState) : Clock -> Prop :=
  
(* ↓clock : s = (Fired, M) ⇝ s' = (Fired', M) *)
| SpnSemantics_falling_edge :
    
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    (* Marking stays the same between state s and s'. *)
    s.(marking) = s'.(marking) ->
    (* ∀ t ∉ firable(s') ⇒ t ∉ Fired'  
       All un-firable transitions are not fired. *)
    (forall (pgroup : list Trans) (t : Trans),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        ~SpnIsFirable spn s' t ->
        ~In t s'.(fired)) ->
    (* ∀ t ∈ firable(s'), (∀ t', t' ≻ t ⇒ t' ∉ firable(s')) ⇒ t ∈ Fired' 
       If all transitions with a higher firing priority than t are not firable,
       then t is fired. *)
    (forall (pgroup : list Trans) (t : Trans),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        SpnIsFirable spn s' t ->
        (forall (t' : Trans),
            In t' pgroup ->
            HasHigherPriority spn t' t pgroup ->
            ~SpnIsFirable spn s' t') ->
        In t s'.(fired)) ->
    (* ∀ t ∈ firable(s'), t ∈ sens(M - ∑ pre(t'), ∀ t'∈ Pr(t)) ⇒ t ∈ Fired' 
       If t is sensitized by the residual marking, result of the firing of
       all higher priority transitions, then t is fired. *)
    (forall (pgroup : list Trans)
       (t : Trans)
       (residual_marking : list (Place * nat)),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s' t ->
        (forall (p : Place)
                (n preSum : nat)
                (pr : list Trans),
            (forall t' : Trans,
                HasHigherPriority spn t' t pgroup /\ In t' s'.(fired) <-> In t' pr) ->
            In (p, n) s'.(marking) ->
            PreSumWD spn p pr preSum ->
            In (p, n - preSum) residual_marking) ->
        IsSensitized spn residual_marking t ->
        In t s'.(fired)) ->
    (* ∀ t ∈ firable(s'), t ∉ sens(M - ∑ pre(t'), ∀ t' ∈ Pr(t)) ⇒ t ∉ Fired' 
       If t is not sensitized by the residual marking, result of the firing of
       all higher priority transitions, then t is not fired. *)
    (forall (pgroup : list Trans)
       (t : Trans)
       (residual_marking : list (Place * nat)),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s' t ->
        (forall (p : Place)
                (n preSum : nat)
                (pr : list Trans),
            (forall t' : Trans,
                HasHigherPriority spn t' t pgroup /\ In t' s'.(fired) <-> In t' pr) ->
            In (p, n) s'.(marking) ->
            PreSumWD spn p pr preSum ->
            In (p, n - preSum) residual_marking) ->
        ~IsSensitized spn residual_marking t ->
        ~In t s'.(fired)) ->
    
    SpnSemantics spn s s' falling_edge
    
(* ↓clock : s = (Fired, M) ⇝ s' = (Fired, M') *)    
| SpnSemantics_raising_edge :
    
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    (* Fired stays the same between state s and s'. *)
    s.(fired) = s'.(fired) ->
    (* M' = M - ∑ (pre(t_i) - post(t_i)), ∀ t_i ∈ Fired *)
    (forall (p : Place)
            (n preSum postSum : nat),
        In (p, n) s.(marking) ->
        PreSumWD spn p s.(fired) preSum ->
        PostSumWD spn p s.(fired) postSum ->
        In (p, n - preSum + postSum) s'.(marking)) ->
    
    SpnSemantics spn s s' raising_edge.

Lemma exists_unique_pre_sum :
    forall (spn : Spn) (p : Place) (l : list Trans),
    exists! (sum : nat), PreSum spn p l sum.
    induction l.
    - exists 0.
      split.
      + apply PreSum_nil.
      + intros. inversion H. reflexivity.
    - elim IHl.
      intros.
      elim H.
      intros.
      exists ((pre spn a p) + x).
      split.
      + apply PreSum_cons.
        assumption.
      + intros.
        inversion H2.
        apply H1 in H6.
        rewrite H6.
        reflexivity.
  Qed.