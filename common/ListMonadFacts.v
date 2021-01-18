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

Lemma foldl_idle :
  forall {state A B : Type} {f : B -> A -> Mon B} {l b0} {s : state} {v s'},
    fold_left f l b0 s = OK v s' ->
    (forall b a s0 v0 s0', f b a s0 = OK v0 s0' -> s0 = s0') ->
    s = s'.
Proof.
  induction l; simpl; intros b0 s v s' e; monadInv e; intros f_idle.
  auto.
  apply IHl with (b0 := x) (v := v); auto.
  rewrite <- (f_idle b0 a s x s0 EQ) in EQ0; assumption.
Qed.
