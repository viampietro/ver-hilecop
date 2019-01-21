Require Export Arith Omega List Bool Bool.Sumbool Bool.Bool Coq.Lists.ListDec FunInd Coq.Logic.Classical_Prop.
Require Export Coq.Sorting.Sorting.
Require Export Coq.Program.Equality.

Export ListNotations.
Export Permutation.

(** * Helper lemmas for the Hilecop program *)

(*===================================================*  
 *                                                   *
 *         HELPER LEMMAS FOR THE HILECOP PROGRAM     *
 *                                                   *
 *===================================================*)

(** Proves a property over the combination of fst and split functions. *)

Lemma fst_split_cons_app {A B : Type} :
  forall (a : (A * B)) (l : list (A * B)),
    fst (split (a :: l)) = (fst (split [a])) ++ (fst (split l)).
Proof.
  intros.
  elim a; simpl.
  elim split; simpl.
  auto.
Qed.

(** Proves a property over the combination of snd and split functions. *)

Lemma snd_split_cons_app {A B : Type} :
  forall (a : (A * B)) (l : list (A * B)),
    snd (split (a :: l)) = (snd (split [a])) ++ (snd (split l)).
Proof.
  intros.
  elim a; simpl.
  elim split; simpl.
  auto.
Qed.

(** Proves that applying the combination of [fst] and [split] on the concatenation
    of list [l] and [l'] is the same as applying separately [fst] and [split] on each list,
    and then concatenating the result. 
 *)

Lemma fst_split_app {A B : Type} :
  forall (l l' : list (A * B)),
    (fst (split (l ++ l'))) = fst (split l) ++ fst (split l').
Proof.
  intros.
  elim l; intros.
  - simpl; auto.
  - rewrite fst_split_cons_app.
    rewrite <- app_comm_cons.
    rewrite fst_split_cons_app.
    rewrite H.
    rewrite app_assoc_reverse.
    reflexivity.
Qed.

(** Proves that applying the combination of [snd] and [split] on the concatenation
    of list [l] and [l'] is the same as applying separately [snd] and [split] on each list,
    and then concatenating the result. 
 *)

Lemma snd_split_app {A B : Type} :
  forall (l l' : list (A * B)),
    (snd (split (l ++ l'))) = snd (split l) ++ snd (split l').
Proof.
  intros.
  elim l; intros.
  - simpl; auto.
  - rewrite snd_split_cons_app.
    rewrite <- app_comm_cons.
    rewrite snd_split_cons_app.
    rewrite H.
    rewrite app_assoc_reverse.
    reflexivity.
Qed.

(** For all list of pairs l and element a, if a is not in [(fst (split l))], 
    then there is no pair in l containing a as first element. *)

Lemma not_in_fst_split {A B : Type} :
  forall (l : list (A * B)) (a : A),
    ~In a (fst (split l)) -> (forall b : B, ~In (a, b) l).
Proof.
  induction l.
  - intros; intro; elim H0.
  - elim a; intros.
    rewrite fst_split_cons_app in H.
    simpl in H.
    apply Decidable.not_or in H.
    elim H; intros.
    apply not_in_cons.
    split.
    + injection; intros.
      symmetry in H4.
      contradiction.
    + generalize (IHl a1 H1); intro.
      apply H2.
Qed.

(** For all pairs in l, in there are no duplicates in the first 
    elements of the pairs in l, then there are no duplicates in l. *)

Lemma nodup_fst_split {A B : Type} :
  forall l : list (A * B), NoDup (fst (split l)) -> NoDup l.
Proof.
  induction l.
  - intro. apply NoDup_nil.
  - elim a.
    intros.
    rewrite fst_split_cons_app in H.
    simpl in H.
    apply NoDup_cons_iff in H.
    elim H; intros.
    apply IHl in H1.
    generalize (not_in_fst_split l a0 H0 b); intro.
    generalize (conj H2 H1); intro.
    apply <- NoDup_cons_iff in H3.
    auto.
Qed.

(** If a couple (a, b) is in the list of couples l 
    then a is in (fst (split l)). *)

Lemma in_fst_split {A B : Type} :
  forall  (a : A) (b : B) (l : list (A * B)),
    In (a, b) l -> In a (fst (split l)).
Proof.
  induction l.
  - auto.
  - elim a0.
    intros.
    rewrite fst_split_cons_app.
    simpl.
    apply in_inv in H.
    elim H; intros.
    + injection H0; intros.
      left; auto.
    + apply IHl in H0; right; auto.
Qed.

(** Modus ponens for [in_eq] implies P. *)

Lemma in_eq_impl {A : Type} :
  forall (a : A) (l : list A) (P : Prop),
    (In a (a :: l) -> P) -> P.
Proof.
  intros.
  apply H; apply in_eq.
Qed.

(** If a is in list l and l is in list of lists ll then a is in (concat ll).
    The result of (concat ll) is one list corresponding
    to the concatenation of all lists in ll. *)

Lemma in_concat {A : Type} :
  forall (a : A) (l : list A) (ll : list (list A)),
    In a l -> In l ll -> In a (concat ll).
Proof.
  intros.
  induction ll.
  (* Base case, ll = []. *)
  - elim H0.
  (* Inductive case. *)
  - apply in_inv in H0; elim H0; intros.
    + rewrite <- H1 in H.
      apply or_introl with (B := In a (concat ll)) in H.
      apply in_or_app in H.
      rewrite concat_cons.
      auto.
    + apply IHll in H1.
      apply or_intror with (A := In a a0) in H1.
      apply in_or_app in H1.
      rewrite concat_cons.
      auto.
Qed.

(** If one element a is not in the list l and another element b 
    is in the list l then a and b are different. *)

Lemma not_in_in_diff {A : Type} :
  forall (a b : A) (l : list A), ~In a l /\ In b l -> a <> b.
Proof.
  intros.
  elim H; intros.
  intro.
  rewrite H2 in H0.
  contradiction.
Qed.

(** If the two elements are different then
    all pairs built with these elements are different. *)

Lemma fst_diff_pair_diff {A B : Type} :
  forall (a x : A),
    a <> x -> (forall (b y : B), (a, b) <> (x, y)).
Proof.
  intros.
  injection; intros.
  contradiction.
Qed.