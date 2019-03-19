Require Import Hilecop.SPN.
Require Import Omega.
        
(*! ============================= !*)
(*! ======= Spn Semantics ======= !*)
(*! ============================= !*)

(** * Preliminary definitions *)

Section DecreasedList.

  (** List l is a decreased version of list l'. Useful for proof involving recursion on lists.  *)

  Inductive IsDecreasedList {A : Type} (l l' : list A) : Prop :=
  | IsDecreasedList_cons :
      length l <= length l' ->
      firstn (length l) (rev l') = (rev l) ->
      IsDecreasedList l l'.
  
  Lemma is_decreased_list_nil {A : Type} :
    forall (l : list A), IsDecreasedList [] l.
  Proof.
    intro l; apply IsDecreasedList_cons.
    - simpl; auto; generalize (length l); apply Nat.le_0_l.
    - simpl; auto.
  Qed.

  Lemma is_decreased_list_cons {A : Type} :
    forall (a : A) (l l' : list A), IsDecreasedList l l' -> IsDecreasedList l (a :: l').
  Proof.
    intros a l l' His_dec; inversion His_dec; apply IsDecreasedList_cons.
    - simpl; auto.
    - simpl.
      rewrite (firstn_app (length l)).
      assert (Hleq_sub_0 : forall n m : nat, n <= m -> n - m = 0).
      { intros n m; omega. }
      rewrite rev_length.
      specialize (Hleq_sub_0 (length l) (length l') H) as Hlength_sub_0.
      rewrite Hlength_sub_0.
      simpl.
      rewrite <- app_nil_end.
      assumption.
  Qed.

End DecreasedList.

Section PredInList.

  Inductive IsPredInList {A : Type} (a b : A) : list A -> Prop :=
  | IsPredInList_app:
      forall l l' : list A,
        In a l ->
        In b l' ->
        NoDup (l ++ l') -> 
        IsPredInList a b (l ++ l')
  | IsPredInList_cons:
      forall l: list A,
        In b l ->
        NoDup (a :: l) ->
        IsPredInList a b (a :: l).

  Lemma is_pred_in_list_not_head_cons {A : Type} :
    forall (x y a : A) (l : list A),
      IsPredInList x y (a :: l) -> 
  
  Theorem is_pred_in_dec_list {A : Type} :
    forall (l l' : list A) (x y : A),
      IsPredInList x y l -> IsDecreasedList l l' -> IsPredInList x y l'.
  Proof.
    induction l; intros l' x y His_pred His_dec.
    - inversion His_pred.
      apply app_eq_nil in H.
      elim H; intros Heq_nil_l Heq_nil_cons.
      rewrite Heq_nil_l in H0; inversion H0.
    - inversion His_pred.
      apply is_decreased_list_cons with (a := a0) in His_dec.
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

(** Pr: pr contains the list of fired transitions with a higher priority than t. *)

Definition Pr
           (spn : Spn)
           (s : SpnState)
           (pgroup : list Trans)
           (t : Trans)
           (pr : list Trans) : Prop :=
  forall (t' : Trans),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    In pgroup spn.(priority_groups) ->
    In t pgroup ->
    In t' pgroup ->
    In t' pr ->
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
    (* ∀ t ∈ firable(s'), t ∈ sens(M - ∑ pre(t_i), ∀ t_i ∈ Pr(t)) ⇒ t ∈ Fired' 
       If t is sensitized by the residual marking, result of the firing of
       all higher priority transitions, then t is fired. *)
    (forall (pgroup : list Trans)
       (t : Trans)
       (residual_marking : list (Place * nat))
       (pr : list Trans),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s' t ->
        Pr spn s' pgroup t pr ->
        (forall (p : Place)
                (n preSum : nat),
            In (p, n) s'.(marking) ->
            PreSum spn p pr preSum ->
            In (p, n - preSum) residual_marking) ->
        IsSensitized spn residual_marking t ->
        In t s'.(fired)) ->
    (* ∀ t ∈ firable(s'), t ∉ sens(M - ∑ pre(t_i), ∀ t_i ∈ Pr(t)) ⇒ t ∉ Fired' 
       If t is not sensitized by the residual marking, result of the firing of
       all higher priority transitions, then t is not fired. *)
    (forall (pgroup : list Trans)
       (t : Trans)
       (residual_marking : list (Place * nat))
       (pr : list Trans),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s' t ->
        Pr spn s' pgroup t pr ->
        (forall (p : Place)
                (n preSum : nat),
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