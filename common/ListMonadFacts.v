(** * Facts about List Monad Functions *)

Require Import common.Coqlib.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListMonad.

Functional Scheme getv_ind := Induction for getv Sort Prop.

Lemma getv_inv_state :
  forall {state A B : Type} {eqk}
         {eqk_dec : forall x y, {eqk x y} + {~eqk x y}}
         {x : A} {l : list (A * B)} {s : state} {v s'},
    getv eqk_dec x l s = OK v s' ->
    s = s'.
Proof.
  intros until s.
  functional induction (@getv state A B eqk eqk_dec x l) using getv_ind;
    intros v s' e; (try monadInv e; auto || eapply IHm; eauto).
Qed.

Hint Resolve getv_inv_state : listmonad.

Remark foldl_inv_state :
  forall {state A B : Type} {f : B -> A -> Mon B} {l b0} {s : state} {v s'}
         {Q : state -> state -> Prop},
    fold_left f l b0 s = OK v s' ->
    Reflexive Q ->
    Transitive Q ->
    (forall b a s0 v0 s0', f b a s0 = OK v0 s0' -> Q s0 s0') ->
    Q s s'.
Proof.
  induction l; simpl; intros b0 s v s' Q e; monadInv e; intros Qrefl Qtrans f_inv;
    [ apply Qrefl
    | apply Qtrans with (y := s0);
      [apply (f_inv b0 a s x s0 EQ)
      | apply IHl with (b0 := x) (v := v); auto]].
Qed.

Remark iter_inv_state :
  forall {state A : Type} {f : A -> Mon unit} {l} {s : state} {v s'}
         {Q : state -> state -> Prop},
    iter f l s = OK v s' ->
    Reflexive Q ->
    Transitive Q ->
    (forall a s1 x s2, f a s1 = OK x s2 -> Q s1 s2) ->
    Q s s'.
Proof.
  intros until l; functional induction (iter f l) using iter_ind;
    intros s v s' Q e; monadFullInv e; intros Qrefl Qtrans f_inv;
      [ apply Qrefl |
        apply Qtrans with (y := s0);
        [ eapply IHm; eauto | apply (f_inv b s0 v s' EQ0) ] ].
Qed.

Remark titer_inv_state :
  forall {state A B : Type} {f : B -> Mon unit} {l : list A} {Inl2B} {s : state} {v s'}
         {Q : state -> state -> Prop},
    titer f l Inl2B s = OK v s' ->
    Reflexive Q ->
    Transitive Q ->
    (forall b s1 x s2, f b s1 = OK x s2 -> Q s1 s2) ->
    Q s s'.
Proof.
  intros until Inl2B; functional induction (titer f l Inl2B) using titer_ind;
    intros s v s' Q e; monadFullInv e; intros Qrefl Qtrans f_inv;
      [ apply Qrefl
      | apply Qtrans with (y := s0);
        [ eapply IHm; eauto | apply (f_inv (pf a (in_eq a tl)) s0 v s' EQ0) ] ].
Qed.

Remark foreach_aux_inv_state :
  forall {state A : Type} {f : A -> list A -> Mon unit} {rght lft : list A} {s : state} {v s'}
         {Q : state -> state -> Prop},
    foreach_aux state A f lft rght s = OK v s' ->
    Reflexive Q ->
    Transitive Q ->
    (forall a lofAs s1 x s2, f a lofAs s1 = OK x s2 -> Q s1 s2) ->
    Q s s'.
Proof.
  induction rght; simpl; intros lft s v s' Q e Qrefl Qtrans f_inv; monadInv e.
  apply Qrefl.
  apply Qtrans with (y := s0).
  eapply f_inv; eauto.
  eapply IHrght; eauto.
Qed.

Remark foreach_inv_state :
  forall {state A : Type} {f : A -> list A -> Mon unit} {l : list A} {s : state} {v s'}
         {Q : state -> state -> Prop},
    foreach f l s = OK v s' ->
    Reflexive Q ->
    Transitive Q ->
    (forall a lofAs s1 x s2, f a lofAs s1 = OK x s2 -> Q s1 s2) ->
    Q s s'.
Proof.
  intros; eapply foreach_aux_inv_state; eauto.
Qed.

Remark find_inv_state :
  forall {state A : Type} {f : A -> Mon bool} {l : list A} {s : state} {v s'}
         {Q : state -> state -> Prop},
    find f l s = OK v s' ->
    Reflexive Q ->
    Transitive Q ->
    (forall a s1 x s2, f a s1 = OK x s2 -> Q s1 s2) ->
    Q s s'.
Proof.
  induction l; simpl; intros s v s' Q e Qrefl Qtrans f_inv; minv e.
  apply Qrefl.
  eapply f_inv; eauto.
  apply Qtrans with (y := s0);
  [ eapply f_inv; eauto | eapply IHl; eauto ].
Qed.

Remark map_aux_inv_state :
  forall {state B C : Type} {l} {f : B -> Mon C} {m} {s : state} {v s'}
         {Q : state -> state -> Prop},
    map_aux f l m s = OK v s' ->
    Reflexive Q ->
    Transitive Q ->
    (forall b s1 c s2, f b s1 = OK c s2 -> Q s1 s2) ->
    Q s s'.
Proof.
  induction l; simpl; intros f m s v s' Q e Qrefl Qtrans f_inv; minv e.
  apply Qrefl.
  apply Qtrans with (y := s0).
  eapply f_inv; eauto.
  eapply IHl; eauto.
Qed.

Remark map_inv_state :
  forall {state B C : Type} {l} {f : B -> Mon C} {s : state} {v s'}
         {Q : state -> state -> Prop},
    map f l s = OK v s' ->
    Reflexive Q ->
    Transitive Q ->
    (forall b s1 c s2, f b s1 = OK c s2 -> Q s1 s2) ->
    Q s s'.
Proof. intros; eapply map_aux_inv_state; eauto. Qed.

Remark tmap_aux_inv_state :
  forall {state A B C : Type} {l : list A} {f : B -> Mon C} {m Inl2B} {s : state} {v s'}
         {Q : state -> state -> Prop},
    tmap_aux f l m Inl2B s = OK v s' ->
    Reflexive Q ->
    Transitive Q ->
    (forall b s1 c s2, f b s1 = OK c s2 -> Q s1 s2) ->
    Q s s'.
Proof.
  induction l; simpl; intros f m Inl2B s v s' Q e Qrefl Qtrans f_inv; minv e.
  apply Qrefl.
  apply Qtrans with (y := s0).
  eapply f_inv; eauto.
  eapply IHl; eauto.
Qed.

Remark tmap_inv_state :
  forall {state A B C : Type} {l : list A} {f : B -> Mon C} {Inl2B} {s : state} {v s'}
         {Q : state -> state -> Prop},
    tmap f l Inl2B s = OK v s' ->
    Reflexive Q ->
    Transitive Q ->
    (forall b s1 c s2, f b s1 = OK c s2 -> Q s1 s2) ->
    Q s s'.
Proof. intros; eapply tmap_aux_inv_state; eauto. Qed.
