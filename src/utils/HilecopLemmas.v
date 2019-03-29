(** To use [dependent induction] *)

Require Export Coq.Program.Equality.
Require Import Omega.

(** To use [list] and its notations. *)

Require Export List.
Export ListNotations.

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

(** If a ∈ (fst (split l)) then
    ∃ b | (a,b) ∈ l. 
 *)
Lemma in_fst_split_in_pair {A B : Type} :
  forall  (a : A) (l : list (A * B)),
    In a (fst (split l)) -> exists b : B, In (a, b) l.
Proof.
  intros.
  induction l.
  - elim H.
  - dependent induction a0.
    rewrite fst_split_cons_app in H; simpl in H.
    elim H; intro.
    + exists b; rewrite H0; apply in_eq.
    + apply IHl in H0; elim H0; intros.
      exists x; apply in_cons; assumption.
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

(** ∀ l, l', NoDup (l ++ l') ⇒ NoDup l ∧ NoDup l'. *)

Lemma nodup_app {A : Type} :
  forall l l' : list A,
    NoDup (l ++ l') -> NoDup l /\ NoDup l'.
Proof.
  intros l l'; intro Hnodup_app; split.
  - induction l.
    + apply NoDup_nil.
    + apply NoDup_cons;
        simpl in Hnodup_app;
        apply NoDup_cons_iff in Hnodup_app;
        elim Hnodup_app; intros Hnot_in_concat Hnodup_app'.
      -- intro.
         apply or_introl with (B := In a l') in H.
         apply in_app_iff in H.
         elim Hnot_in_concat; assumption.
      -- apply (IHl Hnodup_app').
         
  - induction l'.
    + apply NoDup_nil.
    + apply NoDup_cons;
        apply NoDup_remove in Hnodup_app;
        elim Hnodup_app; intros Hnodup_app' Hnot_in_concat.
      -- intro.
         apply or_intror with (A := In a l) in H.
         apply in_app_iff in H.
         elim Hnot_in_concat; assumption.
      -- apply (IHl' Hnodup_app').
         
Qed.

(** ∀ l, ll, NoDup (l ++ l') ⇒ 
    ∀ a ∈ l ⇒ a ∉ l'. *)

Lemma nodup_app_not_in {A : Type} :
  forall l l': list A,
    NoDup (l ++ l') ->
    forall a : A, In a l -> ~In a l'.
Proof.
  intros l l' Hnodup a Hin.
  induction l'.
  - simpl; auto.
  - apply not_in_cons.
    apply NoDup_remove in Hnodup.
    elim Hnodup; intros Hnodup_app Hnot_in.
    split.
    + intro; elim Hnot_in; apply in_or_app; left.
      rewrite <- H; assumption.
    + apply IHl'; assumption.
Qed.

(** ∀ ll : list (list), NoDup (concat ll) ⇒ ∀ l ∈ ll, NoDup l. *)

Lemma nodup_concat_gen {A : Type} :
  forall ll : list (list A),
    NoDup (concat ll) ->
    forall l : list A, In l ll -> NoDup l.
Proof.
  intros ll Hnodup_concat l Hin.
  induction ll.
  - inversion Hin.
  - apply in_inv in Hin;
      elim Hin;
      rewrite concat_cons in Hnodup_concat;
      apply nodup_app in Hnodup_concat;
      elim Hnodup_concat;
      intros Hnodup_a Hnodup_concat'.
    + intro Heq; rewrite Heq in Hnodup_a; assumption.
    + intro Hin_ll; apply (IHll Hnodup_concat' Hin_ll).
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

(** ∀ a, a ∉ l ∧ a ∉ l' ⇒ a ∉ (l ++ l') *)

Lemma not_in_app {A : Type} :
  forall (a : A) (l l' : list A),
    ~In a l /\ ~In a l' -> ~In a (l ++ l').
Proof.
  intros a l l' Hnot_in.
  elim Hnot_in; intros Hnot_in_l Hnot_in_l'.
  intro Hin_app.
  apply in_app_or in Hin_app.
  elim Hin_app.
  - intro Hin_l; elim Hnot_in_l; assumption.
  - intro Hin_l'; elim Hnot_in_l'; assumption.
Qed.

(** ∀ a, a ∉ (l ++ l') ⇒ a ∉ l ∧ a ∉ l' *)

Lemma not_app_in {A : Type} :
  forall (a : A) (l l' : list A),
    ~In a (l ++ l') -> ~In a l /\ ~In a l'.
Proof.
  intros a l l' Hnot_in_app.
  split.
  - induction l.
    + apply in_nil.
    + apply not_in_cons. split.
      -- intro Heq.
         elim Hnot_in_app.
         apply in_or_app.
         left.
         rewrite Heq; apply in_eq.
      -- simpl in Hnot_in_app.
         apply Decidable.not_or in Hnot_in_app.
         elim Hnot_in_app; intros Hdiff Hnot_in_app'.
         apply (IHl Hnot_in_app').
  - induction l.
    + simpl in Hnot_in_app; assumption.
    + simpl in Hnot_in_app.
      apply Decidable.not_or in Hnot_in_app.
      elim Hnot_in_app; intros Hdiff Hnot_in_app'.
      apply (IHl Hnot_in_app').
Qed.

(** ∀ a, b, a ≠ b ⇒ a ∉ [b] *)

Lemma diff_not_in {A : Type} :
  forall a b : A, a <> b -> ~In a [b].
Proof.
  intros a b Hdiff.
  intro Hin.
  simpl in Hin.
  elim Hin; [ intro Heq; symmetry in Heq; contradiction | auto].
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

(** 
    ∀ l : A ⨱ B, NoDup (fst (split l)) ⇒     
    ∀ p, p' ∈ l, fst p = fst p' ⇒ p = p'    

    If there are no duplicates in the first elements
    of l, then all pairs with the same first element
    are equal.
 *)

Lemma nodup_same_pair {A B : Type} :
  forall (l : list (A * B)),
    NoDup (fst (split l)) ->
    forall (p p' : A * B),
      In p l -> In p' l -> fst p = fst p' -> p = p'.
Proof.
  intro.
  induction l; intros.
  - inversion H0.
  - dependent induction a.
    rewrite fst_split_cons_app in H; simpl in H.
    apply NoDup_cons_iff in H; elim H; intros.
    apply in_inv in H0; elim H0; intros.
    + apply in_inv in H1.
      elim H1; intros.
      -- rewrite <- H5; rewrite <- H6; reflexivity.
      -- rewrite <- H5 in H2.
         dependent destruction p'.
         simpl in H2.
         apply in_fst_split in H6.
         rewrite <- H2 in H6.
         contradiction.
    + apply in_inv in H1.
      elim H1; intros.
      -- rewrite <- H6 in H2.
         dependent destruction p.
         simpl in H2.
         apply in_fst_split in H5.
         rewrite H2 in H5.
         contradiction.
      -- generalize (IHl H4); intro.
         apply (H7 p p' H5 H6 H2).
Qed.

(** incl (a :: l) l' ⇒ incl l l' *)

Lemma incl_cons_inv {A : Type} :
  forall (a : A) (l l' : list A), incl (a :: l) l' -> incl l l'.
Proof.
  intros a l l' Hincl_cons.
  induction l.
  - unfold incl; intros a' Hin_nil; inversion Hin_nil.
  - apply incl_cons.
    + unfold incl in Hincl_cons.
      assert (In a0 (a :: a0 :: l)) by (apply in_cons; apply in_eq).
      apply (Hincl_cons a0 H).
    + apply IHl. unfold incl.
      intros a' Hin_cons.
      apply in_inv in Hin_cons; elim Hin_cons.
      -- intro Heq; unfold incl in Hincl_cons.
         assert (Hin_cons' : In a (a :: a0 :: l)) by apply in_eq.
         rewrite <- Heq; apply (Hincl_cons a Hin_cons').
      -- intro Hin.
         apply in_cons with (a := a0) in Hin.
         apply in_cons with (a := a) in Hin.
         apply (Hincl_cons a' Hin).
Qed.

(** NoDup (l ++ l') ⇒ NoDup (l' ++ l) *)

Lemma NoDup_app_comm {A : Type} :
  forall (l l' : list A), NoDup (l ++ l') -> NoDup (l' ++ l).
Proof.
  intros l l' Hnodup.
  induction l'.
  - simpl; rewrite <- app_nil_end in Hnodup; assumption.
  - rewrite <- app_comm_cons. apply NoDup_cons.
    + apply NoDup_remove_2 in Hnodup.
      apply not_app_in in Hnodup.
      apply not_in_app.
      apply and_comm.
      assumption.
    + apply NoDup_remove in Hnodup; elim Hnodup; intros Hnodup' Hnot_in.
      apply (IHl' Hnodup').
Qed.

(** (l ++ l') ⊆ m ⇒ (l ⊆ m ∧ l' ⊆ m) *)

Lemma incl_app_inv {A : Type} :
  forall (l l' m : list A), incl (l ++ l') m -> incl l m /\ incl l' m.
Proof.
  intros l l' m Hincl_app. split.
  + unfold incl. induction l.
    -- intros a Hin_nil; inversion Hin_nil.
    -- intros a' Hin_cons.
       unfold incl in Hincl_app.
       apply or_introl with (B := In a' l') in Hin_cons.
       apply in_or_app in Hin_cons.
       apply (Hincl_app a' Hin_cons).
  + induction l'.
    -- intros a Hin_nil; inversion Hin_nil.
    -- apply incl_cons.
       ++ unfold incl in Hincl_app.
          assert (In a (l ++ a :: l')) by (apply in_or_app; right; apply in_eq).
          apply (Hincl_app a H).
       
       ++ unfold incl. intros a' Hin.
          apply in_cons with (a := a) in Hin.
          apply or_intror with (A := In a' l) in Hin.
          apply in_or_app in Hin.
          apply (Hincl_app a' Hin).
       
Qed.

(** NoDup (l ++ m ++ n) ∧ NoDup o ∧ o ⊆ m ⇒ NoDup (l ++ o ++ n) *)

Theorem nodup_app_incl {A : Type} :
  forall (l m n o : list A),
    NoDup (l ++ m ++ n) ->
    NoDup o ->
    incl o m ->
    NoDup (l ++ o ++ n).
Proof.
  intros l m n o Hnodup_lmn Hnodup_o Hincl_om.
  induction o.
  - simpl.
    apply NoDup_app_comm with (l' := (m ++ n)) in Hnodup_lmn.
    rewrite <- app_assoc in Hnodup_lmn.
    apply NoDup_app_comm with (l' := (n ++ l)) in Hnodup_lmn.
    apply nodup_app in Hnodup_lmn.
    elim Hnodup_lmn; intros Hnodup_ln Hnodup_m.
    apply NoDup_app_comm in Hnodup_ln.
    assumption.
  - apply NoDup_app_comm.
    rewrite <- app_assoc.
    rewrite <- app_comm_cons.
    apply NoDup_cons.
    + apply NoDup_cons_iff in Hnodup_o; elim Hnodup_o; intros Hnot_in_o Hnodup_o'.
      apply NoDup_app_comm with (l' := (m ++ n)) in Hnodup_lmn.
      rewrite <- app_assoc in Hnodup_lmn.
      specialize (nodup_app_not_in m (n ++ l) Hnodup_lmn) as Hin_m_not_in_nl.
      assert (Hin_ao : In a (a :: o)) by apply in_eq.
      specialize (Hincl_om a Hin_ao) as Hin_am.
      specialize (Hin_m_not_in_nl a Hin_am) as Hnot_in_nl.
      apply (not_in_app a o (n ++ l) (conj Hnot_in_o Hnot_in_nl)).
    + apply incl_cons_inv in Hincl_om.
      apply NoDup_cons_iff in Hnodup_o; elim Hnodup_o; intros Hnot_in Hnodup_o'.
      specialize (IHo Hnodup_o' Hincl_om) as Hnodup_lon.
      apply NoDup_app_comm in Hnodup_lon.
      rewrite app_assoc.
      assumption.      
Qed.

Theorem sub_exists :
  forall n m : nat, exists o : nat, n = o - m.
Proof.
  intros n m.
  exists (n + m).
  omega.
Qed.

Theorem exists_if_fs_eq {A B : Type} :
  forall (l l' : list (A * B)) (a : A) (b : B),
    In (a, b) l ->
    (fst (split l)) = (fst (split l')) ->
    exists b' : B, In (a, b') l'.
    