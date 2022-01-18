(** * Facts about List Monad Functions *)

Require Import String.
Require Import common.CoqLib.
Require Import common.ListPlus.
Require Import common.StateAndErrorMonad.
Require Import common.ListMonad.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import common.proofs.SetoidListFacts.

(** ** Facts about [getv] *)

Section GetV.

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
  
  Lemma getv_compl :
    forall {state A B : Type} {l : list (A * B)}
           {eqk} {eqk_dec : forall x y, {eqk x y} + {~eqk x y}}
           {x : A} {s : state} {v},
      let eqkv := fun x y => eqk (fst x) (fst y) /\ snd x = snd y in
      InA eqkv (x, v) l ->
      NoDupA eqk (fs l) ->
      Equivalence eqk ->
      getv eqk_dec x l s = OK v s.
  Proof.
    induction l; try (solve [inversion 1]).
    (* IND. CASE *)
    inversion_clear 1; cbn.
    (* SUBCASE eqkv (x, v) a *)
    destruct a; intro NoDupA_fs; destruct (eqk_dec x a).
    (* eqk x a *)
    destruct H0 as (eqk_, eqv_); simpl in eqv_; rewrite eqv_.
    reflexivity.
    (* ~eqk x a *)
    destruct H0 as (eqk_, eqv_); contradiction.
    (* SUBCASE [InA eqkv (x, v) l] *)
    destruct a; intro NoDupA_fs; destruct (eqk_dec x a).
    (* eqk x a *)
    intros; exfalso; eauto with setoidl.
    (* ~eqk x a *)
    eapply IHl; eauto with setoidl.
  Qed.

  Lemma getv_correct :
    forall {A B state : Type} {eqk} {eqk_dec : forall x y : A, {eqk x y} + {~eqk x y}}
           {x : A} {l : list (A * B)} {s : state} {v s'},
      let eqkv := fun x0 y0 : A * B => eqk (fst x0) (fst y0) /\ eq (snd x0) (snd y0) in
      ListMonad.getv eqk_dec x l s = OK v s' -> InA eqkv (x, v) l.
  Proof.
    intros until l;
      functional induction (@getv state A B eqk eqk_dec x l) using @getv_ind;
      intros *; intros e; [ minv e | minv e; eauto with setoidl | eauto ].
  Qed.

End GetV.

Hint Resolve getv_inv_state : listmonad.
Hint Resolve getv_compl : listmonad.
Hint Resolve getv_correct : listmonad.

(** ** Facts about [foldl] *)

Section FoldL.

  Remark foldl_inv_state :
    forall {state A B : Type} {f : B -> A -> Mon B} {l b0} {s : state} {v s'}
           (Q : state -> state -> Prop),
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

  Remark foldl_build_list_by_app :
    forall {state A B : Type} {f : list B -> A -> Mon (list B)} {lofAs lofBs1 lofBs2} {s : state} {s'},
      fold_left f lofAs lofBs1 s = OK lofBs2 s' ->
      (forall lofBs3 a s1 lofBs5 s2,
          f lofBs3 a s1 = OK lofBs5 s2 ->
          exists lofBs4, lofBs5 = lofBs3 ++ lofBs4) ->
      forall b, In b lofBs1 -> In b lofBs2.
  Proof.
    induction lofAs; simpl; intros *; intros e; monadInv e.
    (* BASE CASE *)
    trivial.
    (* IND. CASE *)
    intros; eapply IHlofAs; eauto.
    edestruct H; eauto; subst; auto.
  Qed.

  Remark foldl_inv_val :
    forall {state A B : Type}
           {f : B -> A -> Mon B}
           {lofAs b1 b2} {s : state} {s'}
           (Q : B -> B -> Prop),
      fold_left f lofAs b1 s = OK b2 s' ->
      Reflexive Q ->
      Transitive Q ->
      (forall b3 a s1 b4 s2, f b3 a s1 = OK b4 s2 -> Q b3 b4) ->
      Q b1 b2.
  Admitted.
  
End FoldL.

(** ** Facts about [iter] *)

Section Iter.

  Remark iter_inv_state :
    forall {state A : Type} {f : A -> Mon unit} {l} {s : state} {v s'}
           (Q : state -> state -> Prop),
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

  Remark iter_prop_A_state :
    forall {state A : Type} {f : A -> Mon unit} {l} (eqA : A -> A -> Prop) {s : state} {v s'}
           {Q : A -> state -> Prop},
      iter f l s = OK v s' ->
      (forall a b s, eqA a b -> Q a s <-> Q b s) ->
      (forall a s1 x s2, f a s1 = OK x s2 -> Q a s2) ->
      (forall a s1 x s2, f a s1 = OK x s2 -> forall b, Q b s1 -> Q b s2) ->
      forall a, InA eqA a l -> Q a s'.
  Proof.
    intros until l; functional induction (iter f l) using iter_ind;
      intros eqA s v s' Q e; monadFullInv e; intros Qequiv Qprop Qinv.
    - inversion 1.
    - inversion_clear 1; [ erewrite Qequiv; eauto | (eapply Qinv; eauto; eapply IHm; eauto) ].
  Qed.

  
End Iter.


Remark titer_inv_state :
  forall {state A B : Type} {f : B -> Mon unit} {l : list A} {Inl2B} {s : state} {v s'}
         (Q : state -> state -> Prop),
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
         (Q : state -> state -> Prop),
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
         (Q : state -> state -> Prop),
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
         (Q : state -> state -> Prop),
    find f l s = OK v s' ->
    Reflexive Q ->
    Transitive Q ->
    (forall a s1 x s2, f a s1 = OK x s2 -> Q s1 s2) ->
    Q s s'.
Proof.
  induction l; simpl; intros s v s' Q e Qrefl Qtrans f_inv; monadInv e.
  apply Qrefl.
  destrm EQ0; [ monadInv EQ0; eapply f_inv; eauto
              | apply Qtrans with (y := s0);
                [ eapply f_inv; eauto | eapply IHl; eauto ] ].
Qed.

(** ** Facts about [map] *)

Section Map.

  Remark map_aux_inv_state :
    forall {state B C : Type} {l} {f : B -> Mon C} {m} {s : state} {v s'}
           (Q : state -> state -> Prop),
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
           (Q : state -> state -> Prop),
      map f l s = OK v s' ->
      Reflexive Q ->
      Transitive Q ->
      (forall b s1 c s2, f b s1 = OK c s2 -> Q s1 s2) ->
      Q s s'.
  Proof. intros; eapply map_aux_inv_state; eauto. Qed.

  Lemma map_aux_inv_acc :
    forall {state A B : Type} {l : list A} {f : A -> Mon B}
           {m : list B} {s : state} {m' s'}
           {eqB : B -> B -> Prop},
      map_aux f l m s = OK m' s' ->
      forall b, InA eqB b m -> InA eqB b m'.
  Proof.
    induction l; intros *; intros e; minv e;
      [ auto | intros; eapply IHl; eauto;
               rewrite InA_app_iff; left; assumption ].
  Qed.
  
End Map.

Remark tmap_aux_inv_state :
  forall {state A B C : Type} {l : list A} {f : B -> Mon C} {m Inl2B} {s : state} {v s'}
         (Q : state -> state -> Prop),
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
         (Q : state -> state -> Prop),
    tmap f l Inl2B s = OK v s' ->
    Reflexive Q ->
    Transitive Q ->
    (forall b s1 c s2, f b s1 = OK c s2 -> Q s1 s2) ->
    Q s s'.
Proof. intros; eapply tmap_aux_inv_state; eauto. Qed.
