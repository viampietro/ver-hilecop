Require Import Hilecop.SPN.
Require Import Omega.

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
      forall (a : A) (l : list A), IsPredInList x y l -> IsPredInList x y (a :: l).

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
      + apply NoDup_cons_iff in Hnodup.
        elim Hnodup; intros Hnot_in Hnodup_l'.
        apply IsPredInList_rm_fst.
        apply (IHl' x y His_pred H1 Hnodup_l').
  Qed.

End PredInList.

(** In all the following definitions, (IsWellDefinedSpn spn) is a necessary condition. *)

(** HasHigherPriority: ∀ t ∈ T, t' ∈ T/{t}, t ≻ t' *)

Definition HasHigherPriority
           (spn : Spn)
           (t t' : Trans)
           (pgroup : list Trans) :=
    IsWellDefinedSpn spn ->
    In pgroup spn.(priority_groups) ->
    In t pgroup ->
    In t' pgroup ->
    IsPredInList t t' pgroup.

(** IsPr: t' ∈ Pr(t) ⇒ t' ∈ s.(fired) ∧ t' ≻ t. *)

Definition IsPr (spn : Spn) (s : SpnState) (pgroup : list Trans) (t t' : Trans) : Prop :=
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    In pgroup spn.(priority_groups) ->
    In t pgroup ->
    In t' pgroup ->
    HasHigherPriority spn t' t pgroup /\ In t' s.(fired).

(** PreSum: Sums all weight of edges coming from place p to transitions of the l list. *)

Inductive PreSum (spn : Spn) (p : Place) : list Trans -> nat -> Prop :=
| PreSum_nil :
    IsWellDefinedSpn spn ->
    In p spn.(places) ->
    PreSum spn p [] 0
| PreSum_cons :
    forall (l : list Trans)
           (t : Trans)
           (sum : nat),
      IsWellDefinedSpn spn ->
      In p spn.(places) ->
      In t spn.(transs) ->
      incl l spn.(transs) ->
      PreSum spn p l sum ->
      PreSum spn p (t :: l) ((pre spn t p) + sum).

(** PostSum: Sums all weight of edges coming from transitions of the l list to place p. *)

Inductive PostSum (spn : Spn) (p : Place) : list Trans -> nat -> Prop :=
| PostSum_nil :
    IsWellDefinedSpn spn ->
    In p spn.(places) ->
    PostSum spn p [] 0
| PostSum_cons :
    forall (l : list Trans)
      (t : Trans)
      (sum : nat),
      IsWellDefinedSpn spn ->
      In p spn.(places) ->
      In t spn.(transs) ->
      incl l spn.(transs) ->
      PostSum spn p l sum ->
      PostSum spn p (t :: l) ((post spn t p) + sum).

(** IsSensitized:
    ∀ t ∈ T, marking m, t ∈ sens(m) if
    ∀ p ∈ P, m(p) ≥ Pre(p, t) ∧ 
             m(p) ≥ Pre_t(p, t) ∧ 
             (m(p) < Pre_i(p, t) ∨ Pre_i(p, t) = 0) *)

Definition IsSensitized
           (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans) : Prop :=
  IsWellDefinedSpn spn ->
  MarkingHaveSameStruct spn.(initial_marking) marking ->
  In t spn.(transs) ->
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
  IsWellDefinedSpn spn ->
  IsWellDefinedSpnState spn state ->
  In t spn.(transs) ->
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
            (forall t' : Trans, IsPr spn s' pgroup t t' <-> In t' pr) ->
            In (p, n) s'.(marking) ->
            PreSum spn p pr preSum ->
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
            (forall t' : Trans, IsPr spn s' pgroup t t' <-> In t' pr) ->
            In (p, n) s'.(marking) ->
            PreSum spn p pr preSum ->
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
        PreSum spn p s.(fired) preSum ->
        PostSum spn p s.(fired) postSum ->
        In (p, n - preSum + postSum) s'.(marking)) ->
    
    SpnSemantics spn s s' raising_edge.