(** * More Facts about Setoid Lists *)

Require Import common.Coqlib.
Require Import common.FstSplit.

Lemma setoidl_eq_in :
  forall {A B : Type} l {eqk : A -> A -> Prop} {eqv : B -> B -> Prop} a a' b ,
    Equivalence eqk -> 
    eqk a a' ->
    let eqkv := (fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y)) in
    InA eqkv (a, b) l ->
    InA eqkv (a', b) l.
Proof.
  induction l.

  - inversion 3.
  - intros; destruct a.
    apply InA_cons.
    inversion_clear H1.
    + left; firstorder.
    + right; apply IHl with (a := a0); auto.
Qed.

Lemma NoDupA_fs_eqk_eq (A : Type) {B : Type} :
  forall {eqk : A -> A -> Prop} {l : list (A * B)} {a b b'},
    Equivalence eqk ->
    NoDupA eqk (fs l) ->
    let eqkv := (fun x y => eqk (fst x) (fst y) /\ eq (snd x) (snd y)) in
    InA eqkv (a, b) l ->
    InA eqkv (a, b') l ->
    eq b b'.
Proof.
  induction l.
  
  (* BASE CASE *)
  - inversion 3.

  (* IND. CASE *)
  - intros.
    lazymatch goal with
    | [ H: NoDupA _ _ |- _ ] =>
      rewrite fs_eq_cons_app in H; destruct a as (a1, b1);
        simpl in H; inversion_clear H
    end.

    lazymatch goal with
    | [ H: InA _ (a0, b) _, H': InA _ (a0, b') _ |- _ ] =>
      inversion_clear H; inversion_clear H'
    end.

    (* 4 subgoals *)

    (* [(a0, b) = (a1, b1)] and [(a0, b') = (a1, b1)] *)
    + firstorder; transitivity b1; auto.

    (* [(a0, b) = (a1, b1)] and [(a0, b') ∈ l]. 
       Then, [eqk a0 a1], then [(a1, b') ∈ l], then [a1 ∈ (fs l)].
       Contradicts [a1 ∉ (fs l)].  *)
    + elimtype False; lazymatch goal with
                      | [ H: ~InA _ _ _ |- _ ] =>
                        apply H
                      end.
      apply (@setoidl_in_fst_split A B eqk eq a1 l b').
      eapply setoidl_eq_in with (a := a0); eauto.
      firstorder.

    + elimtype False; lazymatch goal with
                      | [ H: ~InA _ _ _ |- _ ] =>
                        apply H
                      end.
      apply (@setoidl_in_fst_split A B eqk eq a1 l b).
      eapply setoidl_eq_in with (a := a0); eauto.
      firstorder.

    + eapply IHl; eauto.
Qed.

Hint Rewrite NoDupA_fs_eqk_eq : core.
