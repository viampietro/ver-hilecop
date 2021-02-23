(** * More Facts about Setoid Lists *)

Require Import common.Coqlib.
Require Import common.ListPlus.
Require Import common.FstSplit.

(** ** Facts about [InA] *)

(** If a couple (a, b) is in the list of couples l 
    then a is in (fst (split l)). *)

Lemma InA_fst_split {A B : Type} :
  forall {eqk : A -> A -> Prop} {eqv : B -> B -> Prop} {a l} (b : B),
    let eqkv := (fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y)) in
    InA eqkv (a, b) l -> InA eqk a (fst (split l)).
Proof.
  induction l.
  - intros; inversion H.
  - elim a0; intros; rewrite fst_split_cons_app; simpl.
    inversion_clear H; apply InA_cons.
    + firstorder.
    + right; apply IHl with (b := b0); auto.
Qed.

Hint Resolve InA_fst_split : setoidl.

(* Version of [not_in_fst_split] for setoid lists. *)

Lemma not_InA_fst_split {A B : Type} :
  forall {l : list (A * B)} {eqk : A -> A -> Prop} {eqv : B -> B -> Prop} {a : A},
    ~InA eqk a (fst (split l)) ->
    let eqkv := (fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y)) in
    (forall b : B, ~InA eqkv (a, b) l).
Proof.
  induction l.
  - intros; intros Hin; inversion Hin.
  - elim a; intros; intros Hin.
    specialize (InA_fst_split b0 Hin) as Hnotin_a1.
    contradiction.
Qed.

Hint Resolve not_InA_fst_split : setoidl.

Lemma InA_eqk :
  forall {A B : Type} {eqk : A -> A -> Prop} (eqv : B -> B -> Prop) {x y z l},
    eqk x y ->
    Equivalence eqk ->
    let eqkv := fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y) in
    InA eqkv (x, z) l ->
    InA eqkv (y, z) l.
Proof.
  induction 3;
    [ destruct y0 as (a, b); apply InA_cons_hd; firstorder
    | apply InA_cons_tl; auto].
Qed.

Hint Resolve InA_eqk : setoidl.
Hint Extern 1 (InA _ (_, _) _) => eapply InA_eqk; eauto : setoidl.

Lemma InA_setv_inv :
  forall {A B : Type} {x y : A} {z v : B} {eqk eqv l} {eqk_dec : forall x y, {eqk x y} + {~eqk x y}},
    let eqkv := (fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y)) in
    InA eqkv (x, z) l ->
    ~eqk x y ->
    Equivalence eqk ->
    InA eqkv (x, z) (setv eqk_dec y v l).
Proof.
  induction 1.
  
  all: destruct y0; intros; simpl; destruct (eqk_dec y a); auto.
  destruct H as (Heqk, Heqv); simpl in Heqk.
  apply (Equivalence_Symmetric y a) in e.
  apply (Equivalence_Transitive x a y) in e; [contradiction | auto].
Qed.

Hint Resolve InA_setv_inv : setoidl.

Lemma InA_setv :
  forall {A B : Type} {x : A} {z : B} {eqk eqv} {eqk_dec : forall x y, {eqk x y} + {~eqk x y}} {l},
    let eqkv := (fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y)) in
    Equivalence eqk ->
    Equivalence eqv ->
    InA eqkv (x, z) (setv eqk_dec x z l).
Proof.
  intros until l.
  functional induction (setv eqk_dec x z l) using setv_ind; intros.
  1, 2: apply InA_cons_hd; firstorder.
  apply InA_cons_tl; apply IHl0; auto.
Qed.

Hint Resolve InA_setv : setoidl.

Lemma InA_notin_fs_setv_inv {A B : Type} :
  forall {eqk : A -> A -> Prop} {eqk_dec : forall x y, {eqk x y} + {~eqk x y}}
         {y} (b : B) {l : list (A * B)} {x},
    Equivalence eqk ->
    ~InA eqk x (fs l) ->
    ~eqk y x ->
    ~InA eqk x (fs (setv eqk_dec y b l)).
Proof.
  intros until l; functional induction (setv eqk_dec y b l) using setv_ind;
    rewrite fs_eq_cons_app ; simpl; intros; (rewrite fs_eq_cons_app; simpl; inversion_clear 1) || inversion_clear 1;
      [ apply Equivalence_Symmetric in H3; contradiction
      | apply H0; assumption
      | apply Equivalence_Symmetric in H3; contradiction
      | apply H0; auto
      | apply H0; auto
      | generalize H3; apply IHl0; auto
      ].
Qed.

Hint Resolve InA_notin_fs_setv_inv : setoidl.

Lemma InA_neqA {A : Type} :
  forall {eqA : A -> A -> Prop} {x y} {l : list A},
    Equivalence eqA ->
    InA eqA x l ->
    ~InA eqA y l ->
    ~eqA x y.
Proof. intros; intro; specialize (InA_eqA H H2 H0); contradiction. Qed.

Hint Resolve InA_neqA : setoidl.
     
(** ** Facts about [NoDupA] *)

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
      apply (@InA_fst_split A B eqk eq a1 l b').
      eapply InA_eqk; eauto; firstorder.

    + elimtype False; lazymatch goal with
                      | [ H: ~InA _ _ _ |- _ ] =>
                        apply H
                      end.
      apply (@InA_fst_split A B eqk eq a1 l b).
      eapply InA_eqk; eauto; firstorder.

    + eapply IHl; eauto.
Qed.

Hint Rewrite NoDupA_fs_eqk_eq : setoidl.

Lemma NoDupA_setv_cons (A : Type) {B : Type} :
  forall {eqk : A -> A -> Prop} {eqk_dec : forall x y, {eqk x y} + {~eqk x y}} {a b} {l : list (A * B)},
    Equivalence eqk ->
    ~InA eqk a (fs l) ->
    NoDupA eqk (fs l) ->
    NoDupA eqk (fs (setv eqk_dec a b l)).
Proof.  
  intros until l; functional induction (setv eqk_dec a b l) using setv_ind.
  - intros; apply NoDupA_singleton.
  - intros Heq Hnin; elimtype False; apply Hnin.
    rewrite fs_eq_cons_app; simpl; apply InA_cons_hd; assumption.
  - do 2 (rewrite fs_eq_cons_app; simpl).
    intros; apply NoDupA_cons;
      lazymatch goal with
      | [ H: NoDupA _ (_ :: _) |- _ ] =>
        inversion_clear H as [  | x l Hnin Hnd ];
          (apply InA_notin_fs_setv_inv; auto) || (apply IHl0; auto)
      end.
Qed.

Hint Resolve NoDupA_setv_cons : setoidl.

Lemma NoDupA_tl (A : Type) :
  forall {eqA : A -> A -> Prop} {a : A} {l : list A},
    NoDupA eqA (a :: l) ->
    NoDupA eqA l.
Proof. inversion 1; auto. Qed.

Hint Resolve NoDupA_tl : setoidl.
