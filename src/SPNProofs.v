Require Import Hilecop.SPN Hilecop.SPNAnimator Hilecop.SPNSemantics Hilecop.SPNTactics.
Require Import Hilecop.Utils.HilecopLemmas.
Require Import Classical_Prop.

(** ** Lemmas on the Spn structure. *)

(*!========================================!*)
(*!=========== LEMMAS ON Spn ==============!*)
(*!========================================!*)

Section SpnLemmas.
  
  (** For all well-defined Spn, If a Place p ∈ neighbourhood of Trans t,
      such that (t, neigh_of_t) ∈ spn.(lneighbours), then 
      p ∈ (flatten_lneighbours spn.(lneighbours))  ∀ *)

  Lemma in_neigh_in_flatten :
    forall (spn : Spn) (t : Trans) (neigh_of_t : Neighbours) (p : Place),
      IsWellDefinedSpn spn ->
      In (t, neigh_of_t) spn.(lneighbours) ->
      In p (flatten_neighbours neigh_of_t) ->
      In p (flatten_lneighbours spn.(lneighbours)).
  Proof.
    intros spn t neigh_of_t p; intros.
    functional induction (flatten_lneighbours (lneighbours spn))
               using flatten_lneighbours_ind; intros.
    - elim H0.
    - apply in_or_app.
      apply in_inv in H0; elim H0; intros.
      + injection H2; intros; rewrite H3; left; assumption.
      + apply IHl0 in H2; right; assumption.
  Qed.

  (** ∀ s, s', s.(marking) = s'.(marking) ⇒ SpnIsFirable spn s t ⇔ SpnIsfirable spn s' t *)

  Lemma state_same_marking_firable_iff :
    forall (spn : Spn) (s s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      IsWellDefinedSpnState spn s' -> 
      s.(marking) = s'.(marking) ->
      forall t : Trans, SpnIsFirable spn s t <-> SpnIsFirable spn s' t.
  Proof.
    intros spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s' Heq_marking t.
    split;
      intros His_firable;
      unfold SpnIsFirable in *;
      (rewrite <- Heq_marking || rewrite Heq_marking);
      decompose [and] His_firable;
      intros.
    split; [assumption | split; [ assumption | split; [assumption | assumption]]].
    split; [assumption | split; [ assumption | split; [assumption | assumption]]].
  Qed.
  
End SpnLemmas.

(** ** Lemmas on get_m. *)

(*!=================!*)
(*! LEMMAS ON get_m !*)
(*!=================!*)

Section GetM.

  (** Correctness proof for get_m. *)

  Lemma get_m_correct :
    forall (marking : list (Place * nat)) (p : Place) (n : nat),
      get_m marking p = Some n -> In (p, n) marking.
  Proof.
    intros marking p; functional induction (get_m marking p) using get_m_ind; intros.
    - inversion H.
    - apply beq_nat_true in e1; rewrite e1.
      injection H; intro; rewrite H0.
      apply in_eq.
    - apply in_cons; apply IHo; assumption.
  Qed.

  (** Completeness proof for get_m. *)

  Lemma get_m_complete :
    forall (marking : list (Place * nat)) (p : Place) (n : nat),
      NoDup (fst (split marking)) ->
      In (p, n) marking -> get_m marking p = Some n.
  Proof.
    intros marking p n; intros.
    functional induction (get_m marking p) using get_m_ind; intros.
    - elim H0.
    - rewrite fst_split_cons_app in H; simpl in H.
      apply NoDup_cons_iff in H.
      apply in_inv in H0.
      elim H0; intro.
      + injection H1; intros; rewrite H2; reflexivity.
      + elim H; intros.
        apply beq_nat_true in e1; rewrite e1 in H1.
        apply in_fst_split in H1; contradiction.
    - apply IHo.
      + rewrite fst_split_cons_app in H; simpl in H.
        apply NoDup_cons_iff in H.
        elim H; auto.
      + apply in_inv in H0.
        elim H0; intro.
        -- injection H1; intros; symmetry in H3.
           apply beq_nat_false in e1; contradiction.
        -- assumption.
  Qed.

End GetM.

(** ** Lemmas on map_check functions. *)

(*!===============================!*)
(*! LEMMAS ON map_check functions !*)
(*!===============================!*)

Section MapCheckFunctions.

  (** Correctness proof for check_pre. *)

  Lemma check_pre_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (p : Place)
      (t : Trans)
      (n : nat),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (p, n) marking ->
      check_pre spn marking p t = Some true ->
      (pre spn t p) <= n.
  Proof.
    intros spn marking p t;
      functional induction (check_pre spn marking p t) using check_pre_ind;
      intros.
    (* General case, all went well. *)
    - apply get_m_correct in e.
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold MarkingHaveSameStruct in H0.
      unfold NoUnmarkedPlace in H15.
      unfold NoDupPlaces in H3.
      rewrite H0 in H15; rewrite H15 in H3.
      assert (fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).
      generalize (nodup_same_pair marking H3 (p, n) (p, nboftokens) H1 e H); intro.
      injection H14; intro.
      rewrite <- H16 in H2; injection H2; intro.
      apply (leb_complete (pre spn t p) n H17).
    - inversion H2.
  Qed.

  (** Completeness proof for check_pre. *)

  Lemma check_pre_complete :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (p : Place)
      (t : Trans)
      (n : nat),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (p, n) marking ->
      (pre spn t p) <= n ->
      check_pre spn marking p t = Some true.
  Proof.
    intros spn marking p t n; intros.
    unfold check_pre.
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_m_complete. *)
    unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
    unfold NoDupPlaces in H3.
    unfold MarkingHaveSameStruct in H0.
    unfold NoUnmarkedPlace in H15.
    rewrite H15 in H3; rewrite H0 in H3.
    generalize (get_m_complete marking p n H3 H1); intro.
    rewrite H.
    apply leb_correct in H2; rewrite H2; reflexivity.
  Qed.

  (** ∀ spn, marking, pre_places, t, b,
      map_check_pre_aux spn marking pre_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_pre_aux_true_if_true :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (pre_places : list Place)
      (t : Trans)
      (b : bool),
      map_check_pre_aux spn marking pre_places t b = Some true ->
      b = true.
  Proof.
    intros spn marking pre_places t b;
      functional induction (map_check_pre_aux spn marking pre_places t b)
                 using map_check_pre_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  (** Correctness proof for map_check_pre_aux. *)

  Lemma map_check_pre_aux_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (pre_places : list Place)
      (t : Trans)
      (b : bool)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      incl pre_places (pre_pl neighbours_of_t) ->
      map_check_pre_aux spn marking pre_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p pre_places -> In (p, n) marking -> (pre spn t p) <= n.
  Proof.
    intros spn marking pre_places t b;
      functional induction (map_check_pre_aux spn marking pre_places t b)
                 using map_check_pre_aux_ind;
      intros.
    - inversion H4.
    - apply in_inv in H4; elim H4; intro.
      + apply map_check_pre_aux_true_if_true in H3.
        apply andb_prop in H3; elim H3; intros.
        rewrite H7 in e0.
        rewrite H6 in e0.
        generalize (check_pre_correct spn marking p0 t n H H0 H5 e0); intro.
        assumption.
      + apply IHo with (neighbours_of_t := neighbours_of_t);
          (assumption ||
           unfold incl in H2;
           unfold incl; intros;
           apply in_cons with (a := p) in H7;
           apply (H2 a H7)).
    - inversion H3.
  Qed.

  (** Completeness proof for map_check_pre_aux. *)

  Lemma map_check_pre_aux_complete :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (pre_places : list Place)
      (t : Trans)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      incl pre_places (pre_pl neighbours_of_t) ->
      (forall (p : Place) (n : nat),
          In p pre_places -> In (p, n) marking -> (pre spn t p) <= n) ->
      map_check_pre_aux spn marking pre_places t true = Some true.
  Proof.
    intros spn marking pre_places t.
    functional induction (map_check_pre_aux spn marking pre_places t true)
               using map_check_pre_aux_ind;
      intros.
    - simpl; reflexivity.
    - simpl.
      (* Deduces hypotheses necessary to apply check_pre_complete. *)
      assert (In p (p :: tail)) by apply in_eq.
      generalize (H2 p H4); intro.
      assert (In p (flatten_neighbours neighbours_of_t))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).
      generalize (in_neigh_in_flatten spn t neighbours_of_t p H H1 H6); intro.
      assert (H' := H).
      unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold NoUnknownPlaceInNeighbours in H13.
      unfold incl in H13.
      apply (H13 p) in H7.
      unfold NoUnmarkedPlace in H20; rewrite H20 in H7.
      unfold MarkingHaveSameStruct in H0; rewrite H0 in H7.
      generalize (in_fst_split_in_pair p marking H7); intro.
      elim H; intros; generalize (H3 p x H4 H19); intro.
      (* Applies check_pre_complete, then the induction hypothesis. *)
      generalize (check_pre_complete spn marking p t x H' H0 H19 H21); intro.
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite H22 in e0; injection e0; intro.
      rewrite <- H23 in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- H23; rewrite andb_comm; rewrite andb_true_r.
      apply IHo with (neighbours_of_t := neighbours_of_t).
      + assumption.
      + assumption.
      + assumption.
      + unfold incl; intros.
        unfold incl in H2.
        apply in_cons with (a := p) in H24.
        apply (H2 a H24).
      + intros; apply in_cons with (a := p) in H24.
        apply (H3 p0 n H24 H25).
    (* Deduces hypotheses necessary to apply check_pre_complete. *)
    - assert (In p (p :: tail)) by apply in_eq.
      generalize (H2 p H4); intro.
      assert (In p (flatten_neighbours neighbours_of_t))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).
      generalize (in_neigh_in_flatten spn t neighbours_of_t p H H1 H6); intro.
      assert (H' := H); unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold NoUnknownPlaceInNeighbours in H13; unfold incl in H13; apply (H13 p) in H7.
      unfold NoUnmarkedPlace in H20; rewrite H20 in H7.
      unfold MarkingHaveSameStruct in H0; rewrite H0 in H7.
      generalize (in_fst_split_in_pair p marking H7); intro; elim H; intros.
      generalize (H3 p x H4 H19); intro.
      generalize (check_pre_complete spn marking p t x H' H0 H19 H21); intro.
      (* Then, shows a contradiction. *)
      rewrite e0 in H22; inversion H22.
  Qed.

  (** Correctness proof for map_check_pre. *)

  Lemma map_check_pre_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (t : Trans)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      map_check_pre spn marking (pre_pl neighbours_of_t) t = Some true ->
      forall (p : Place) (n : nat), In (p, n) marking -> (pre spn t p) <= n.
  Proof.
    intros spn marking t neighbours_of_t.
    functional induction (map_check_pre spn marking (pre_pl neighbours_of_t) t)
               using map_check_pre_ind;
      intros.
    assert (incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t)) by apply incl_refl.
    (* Proof in two stages. *)
    assert (H' := classic (In p (pre_pl neighbours_of_t))).
    elim H'; intro.
    (* First stage, p ∈ pre_places, then we apply map_check_pre_aux_correct. *)
    - generalize (map_check_pre_aux_correct
                    spn marking (pre_pl neighbours_of_t) t true neighbours_of_t
                    H H0 H1 H4 H2); intro. 
      apply (H6 p n H5 H3).
    (* Second stage, p ∉ pre_places, then (pre spn t p) = 0 *)
    - unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold AreWellDefinedPreEdges in H14.
      generalize (H14 t neighbours_of_t p H1); intro.
      elim H; clear H; intros.
      generalize (H17 H5); intro; rewrite H19; apply Peano.le_0_n.
  Qed.

  (** Correctness proof for map_check_pre. *)

  Lemma map_check_pre_complete :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (t : Trans)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (pre spn t p) <= n) ->
      map_check_pre spn marking (pre_pl neighbours_of_t) t = Some true.
  Proof.
    intros spn marking t neighbours_of_t.
    functional induction (map_check_pre spn marking (pre_pl neighbours_of_t) t)
               using map_check_pre_ind;
      intros.
    (* Hypothesis : incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t) 
       for map_check_pre_aux_complete. *)
    assert (incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t)) by apply incl_refl.
    (* Apply map_check_pre_aux_complete. *)
    apply map_check_pre_aux_complete with (neighbours_of_t := neighbours_of_t).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - intros; apply (H2 p n H5).
  Qed.

  (** Correctness proof for check_test. *)

  Lemma check_test_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (p : Place)
      (t : Trans)
      (n : nat),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (p, n) marking ->
      check_test spn marking p t = Some true ->
      (test spn t p) <= n.
  Proof.
    intros spn marking p t;
      functional induction (check_test spn marking p t) using check_test_ind;
      intros.
    (* General case, all went well. *)
    - apply get_m_correct in e.
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold MarkingHaveSameStruct in H0.
      unfold NoUnmarkedPlace in H15.
      unfold NoDupPlaces in H3.
      rewrite H0 in H15; rewrite H15 in H3.
      assert (fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).
      generalize (nodup_same_pair marking H3 (p, n) (p, nboftokens) H1 e H); intro.
      injection H14; intro.
      rewrite <- H16 in H2; injection H2; intro.
      apply (leb_complete (test spn t p) n H17).
    - inversion H2.
  Qed.

  (** Completeness proof for check_test. *)

  Lemma check_test_complete :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (p : Place)
      (t : Trans)
      (n : nat),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (p, n) marking ->
      (test spn t p) <= n ->
      check_test spn marking p t = Some true.
  Proof.
    intros spn marking p t n; intros.
    unfold check_test.
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_m_complete. *)
    unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
    unfold NoDupPlaces in H3.
    unfold MarkingHaveSameStruct in H0.
    unfold NoUnmarkedPlace in H15.
    rewrite H15 in H3; rewrite H0 in H3.
    generalize (get_m_complete marking p n H3 H1); intro.
    rewrite H.
    apply leb_correct in H2; rewrite H2; reflexivity.
  Qed.

  (** ∀ spn, marking, test_places, t, b,
      map_check_test_aux spn marking test_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_test_aux_true_if_true :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (test_places : list Place)
      (t : Trans)
      (b : bool),
      map_check_test_aux spn marking test_places t b = Some true ->
      b = true.
  Proof.
    intros spn marking test_places t b;
      functional induction (map_check_test_aux spn marking test_places t b)
                 using map_check_test_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  (** Correctness proof for map_check_test_aux. *)

  Lemma map_check_test_aux_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (test_places : list Place)
      (t : Trans)
      (b : bool)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      incl test_places (test_pl neighbours_of_t) ->
      map_check_test_aux spn marking test_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p test_places -> In (p, n) marking -> (test spn t p) <= n.
  Proof.
    intros spn marking test_places t b;
      functional induction (map_check_test_aux spn marking test_places t b)
                 using map_check_test_aux_ind;
      intros.
    - inversion H4.
    - apply in_inv in H4; elim H4; intro.
      + apply map_check_test_aux_true_if_true in H3.
        apply andb_prop in H3; elim H3; intros.
        rewrite H7 in e0.
        rewrite H6 in e0.
        generalize (check_test_correct spn marking p0 t n H H0 H5 e0); intro.
        assumption.
      + apply IHo with (neighbours_of_t := neighbours_of_t);
          (assumption ||
           unfold incl in H2;
           unfold incl; intros;
           apply in_cons with (a := p) in H7;
           apply (H2 a H7)).
    - inversion H3.
  Qed.

  (** Completeness proof for map_check_test_aux. *)

  Lemma map_check_test_aux_complete :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (test_places : list Place)
      (t : Trans)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      incl test_places (test_pl neighbours_of_t) ->
      (forall (p : Place) (n : nat),
          In p test_places -> In (p, n) marking -> (test spn t p) <= n) ->
      map_check_test_aux spn marking test_places t true = Some true.
  Proof.
    intros spn marking test_places t.
    functional induction (map_check_test_aux spn marking test_places t true)
               using map_check_test_aux_ind;
      intros.
    - simpl; reflexivity.
    - simpl.
      (* Deduces hypotheses necessary to apply check_test_complete. *)
      assert (In p (p :: tail)) by apply in_eq.
      generalize (H2 p H4); intro.
      assert (In p (flatten_neighbours neighbours_of_t))
        by (unfold flatten_neighbours; apply in_or_app; right; apply in_or_app; left; assumption).
      generalize (in_neigh_in_flatten spn t neighbours_of_t p H H1 H6); intro.
      assert (H' := H).
      unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold NoUnknownPlaceInNeighbours in H13.
      unfold incl in H13.
      apply (H13 p) in H7.
      unfold NoUnmarkedPlace in H20; rewrite H20 in H7.
      unfold MarkingHaveSameStruct in H0; rewrite H0 in H7.
      generalize (in_fst_split_in_pair p marking H7); intro.
      elim H; intros; generalize (H3 p x H4 H19); intro.
      (* Applies check_test_complete, then the induction hypothesis. *)
      generalize (check_test_complete spn marking p t x H' H0 H19 H21); intro.
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite H22 in e0; injection e0; intro.
      rewrite <- H23 in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- H23; rewrite andb_comm; rewrite andb_true_r.
      apply IHo with (neighbours_of_t := neighbours_of_t).
      + assumption.
      + assumption.
      + assumption.
      + unfold incl; intros.
        unfold incl in H2.
        apply in_cons with (a := p) in H24.
        apply (H2 a H24).
      + intros; apply in_cons with (a := p) in H24.
        apply (H3 p0 n H24 H25).
    (* Deduces hypotheses necessary to apply check_test_complete. *)
    - assert (In p (p :: tail)) by apply in_eq.
      generalize (H2 p H4); intro.
      (* p ∈ (flatten_neighbours neighbours_of_t) *)
      assert (In p (flatten_neighbours neighbours_of_t))
        by (unfold flatten_neighbours; apply in_or_app; right; apply in_or_app; left; assumption).
      (* p ∈ (flatten_neighbours neighbours_of_t) ⇒ p ∈ (flatten spn.(lneighbours)) *)
      generalize (in_neigh_in_flatten spn t neighbours_of_t p H H1 H6); intro.
      assert (H' := H); unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold NoUnknownPlaceInNeighbours in H13; unfold incl in H13; apply (H13 p) in H7.
      unfold NoUnmarkedPlace in H20; rewrite H20 in H7.
      unfold MarkingHaveSameStruct in H0; rewrite H0 in H7.
      (* ∃ n, (p, n) ∈ marking *)
      generalize (in_fst_split_in_pair p marking H7); intro; elim H; intros.
      (* Applies the completeness hypothesis. *)
      generalize (H3 p x H4 H19); intro.
      (* Applies check_test_complete *)
      generalize (check_test_complete spn marking p t x H' H0 H19 H21); intro.
      (* Then, shows a contradiction. *)
      rewrite e0 in H22; inversion H22.
  Qed.

  (** Correctness proof for map_check_test. *)

  Lemma map_check_test_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (t : Trans)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      map_check_test spn marking (test_pl neighbours_of_t) t = Some true ->
      forall (p : Place) (n : nat), In (p, n) marking -> (test spn t p) <= n.
  Proof.
    intros spn marking t neighbours_of_t.
    functional induction (map_check_test spn marking (test_pl neighbours_of_t) t)
               using map_check_test_ind;
      intros.
    assert (incl (test_pl neighbours_of_t) (test_pl neighbours_of_t)) by apply incl_refl.
    (* Proof in two stages. *)
    assert (H' := classic (In p (test_pl neighbours_of_t))).
    elim H'; intro.
    (* First stage, p ∈ test_places, then we apply map_check_test_aux_correct. *)
    - generalize (map_check_test_aux_correct
                    spn marking (test_pl neighbours_of_t) t true neighbours_of_t
                    H H0 H1 H4 H2); intro. 
      apply (H6 p n H5 H3).
    (* Second stage, p ∉ test_places, then (test spn t p) = 0 *)
    - unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold AreWellDefinedTestEdges in H15.
      generalize (H15 t neighbours_of_t p H1); intro.
      elim H; clear H; intros.
      generalize (H17 H5); intro; rewrite H19; apply Peano.le_0_n.
  Qed.

  (** Correctness proof for map_check_test. *)

  Lemma map_check_test_complete :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (t : Trans)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (test spn t p) <= n) ->
      map_check_test spn marking (test_pl neighbours_of_t) t = Some true.
  Proof.
    intros spn marking t neighbours_of_t.
    unfold map_check_test; intros.
    assert (incl (test_pl neighbours_of_t) (test_pl neighbours_of_t)) by apply incl_refl.
    (* Apply map_check_test_aux_complete. *)
    apply map_check_test_aux_complete with (neighbours_of_t := neighbours_of_t).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - intros; apply (H2 p n H5).
  Qed.
  

  (** Correctness proof for check_inhib. *)

  Lemma check_inhib_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (p : Place)
      (t : Trans)
      (n : nat),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (p, n) marking ->
      check_inhib spn marking p t = Some true ->
      (n < (inhib spn t p) \/ (inhib spn t p) = 0).
  Proof.
    intros spn marking p t;
      functional induction (check_inhib spn marking p t) using check_inhib_ind;
      intros.
    (* General case, all went well. *)
    - apply get_m_correct in e.
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold MarkingHaveSameStruct in H0.
      unfold NoUnmarkedPlace in H15.
      unfold NoDupPlaces in H3.
      rewrite H0 in H15; rewrite H15 in H3.
      assert (fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).
      (* Determines n = nboftokens *)
      generalize (nodup_same_pair marking H3 (p, n) (p, nboftokens) H1 e H); intro.
      injection H14; intro.
      rewrite <- H16 in H2; injection H2; intro.
      apply orb_prop in H17.
      (* First case: n < (inhib spn t p), second case: (inhib spn t p) = 0 *)
      elim H17; intro.
      + left; apply Nat.ltb_lt; assumption.
      + right; apply Nat.eqb_eq; assumption.
    - inversion H2.
  Qed.

  (** Completeness proof for check_inhib. *)

  Lemma check_inhib_complete :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (p : Place)
      (t : Trans)
      (n : nat),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (p, n) marking ->
      (n < (inhib spn t p) \/ (inhib spn t p) = 0) ->
      check_inhib spn marking p t = Some true.
  Proof.
    intros spn marking p t n; intros.
    unfold check_inhib.
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_m_complete. *)
    unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
    unfold NoDupPlaces in H3.
    unfold MarkingHaveSameStruct in H0.
    unfold NoUnmarkedPlace in H15.
    rewrite H15 in H3; rewrite H0 in H3.
    (* Applies get_m_complte *)
    generalize (get_m_complete marking p n H3 H1); intro.
    rewrite H; elim H2; intros.
    - apply Nat.ltb_lt in H14; rewrite H14.
      rewrite orb_true_l; reflexivity.
    - apply Nat.eqb_eq in H14; rewrite H14.
      rewrite orb_comm; rewrite orb_true_l; reflexivity.
  Qed.

  (** ∀ spn, marking, inhib_places, t, b,
      map_check_inhib_aux spn marking inhib_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_inhib_aux_true_if_true :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (inhib_places : list Place)
      (t : Trans)
      (b : bool),
      map_check_inhib_aux spn marking inhib_places t b = Some true ->
      b = true.
  Proof.
    intros spn marking inhib_places t b;
      functional induction (map_check_inhib_aux spn marking inhib_places t b)
                 using map_check_inhib_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  (** Correctness proof for map_check_inhib_aux. *)

  Lemma map_check_inhib_aux_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (inhib_places : list Place)
      (t : Trans)
      (b : bool)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      incl inhib_places (inhib_pl neighbours_of_t) ->
      map_check_inhib_aux spn marking inhib_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p inhib_places ->
        In (p, n) marking ->
        (n < (inhib spn t p) \/ (inhib spn t p) = 0).
  Proof.
    intros spn marking inhib_places t b;
      functional induction (map_check_inhib_aux spn marking inhib_places t b)
                 using map_check_inhib_aux_ind;
      intros.
    - inversion H4.
    - apply in_inv in H4; elim H4; intro.
      + apply map_check_inhib_aux_true_if_true in H3.
        apply andb_prop in H3; elim H3; intros.
        rewrite H7 in e0.
        rewrite H6 in e0.
        generalize (check_inhib_correct spn marking p0 t n H H0 H5 e0); intro.
        assumption.
      + apply IHo with (neighbours_of_t := neighbours_of_t);
          (assumption ||
           unfold incl in H2;
           unfold incl; intros;
           apply in_cons with (a := p) in H7;
           apply (H2 a H7)).
    - inversion H3.
  Qed.

  (** Completeness proof for map_check_inhib_aux. *)

  Lemma map_check_inhib_aux_complete :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (inhib_places : list Place)
      (t : Trans)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      incl inhib_places (inhib_pl neighbours_of_t) ->
      (forall (p : Place) (n : nat),
          In p inhib_places -> In (p, n) marking ->
          (n < (inhib spn t p) \/ (inhib spn t p) = 0)) ->
      map_check_inhib_aux spn marking inhib_places t true = Some true.
  Proof.
    intros spn marking inhib_places t.
    functional induction (map_check_inhib_aux spn marking inhib_places t true)
               using map_check_inhib_aux_ind;
      intros.
    - simpl; reflexivity.
    - simpl.
      (* Deduces hypotheses necessary to apply check_inhib_complete. *)
      assert (In p (p :: tail)) by apply in_eq.
      generalize (H2 p H4); intro.
      (* p ∈ (flatten_neighbours neighbours_of_t) *)
      assert (In p (flatten_neighbours neighbours_of_t))
        by (unfold flatten_neighbours;
            do 2 (apply in_or_app; right);
            apply in_or_app; left; assumption).
      (* p ∈ (flatten_neighbours neighbours_of_t) ⇒ p ∈ (flatten spn.(lneighbours)) *)
      generalize (in_neigh_in_flatten spn t neighbours_of_t p H H1 H6); intro.
      assert (H' := H).
      unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold NoUnknownPlaceInNeighbours in H13.
      unfold incl in H13.
      apply (H13 p) in H7.
      unfold NoUnmarkedPlace in H20; rewrite H20 in H7.
      unfold MarkingHaveSameStruct in H0; rewrite H0 in H7.
      (* ∃ n, (p, n) ∈ marking *)
      generalize (in_fst_split_in_pair p marking H7); intro; elim H; intros.
      (* Applies the completeness hypothesis. *)
      generalize (H3 p x H4 H19); intro.
      (* Applies check_inhib_complete, then the induction hypothesis. *)
      generalize (check_inhib_complete spn marking p t x H' H0 H19 H21); intro.
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite H22 in e0; injection e0; intro.
      rewrite <- H23 in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- H23; rewrite andb_comm; rewrite andb_true_r.
      apply IHo with (neighbours_of_t := neighbours_of_t).
      + assumption.
      + assumption.
      + assumption.
      + unfold incl; intros.
        unfold incl in H2.
        apply in_cons with (a := p) in H24.
        apply (H2 a H24).
      + intros; apply in_cons with (a := p) in H24.
        apply (H3 p0 n H24 H25).
    (* Deduces hypotheses necessary to apply check_inhib_complete. *)
    - assert (In p (p :: tail)) by apply in_eq.
      generalize (H2 p H4); intro.
      (* p ∈ (flatten_neighbours neighbours_of_t) *)
      assert (In p (flatten_neighbours neighbours_of_t))
        by (unfold flatten_neighbours;
            do 2 (apply in_or_app; right);
            apply in_or_app; left; assumption).
      (* p ∈ (flatten_neighbours neighbours_of_t) ⇒ p ∈ (flatten spn.(lneighbours)) *)
      generalize (in_neigh_in_flatten spn t neighbours_of_t p H H1 H6); intro.
      assert (H' := H); unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold NoUnknownPlaceInNeighbours in H13; unfold incl in H13; apply (H13 p) in H7.
      unfold NoUnmarkedPlace in H20; rewrite H20 in H7.
      unfold MarkingHaveSameStruct in H0; rewrite H0 in H7.
      (* ∃ n, (p, n) ∈ marking *)
      generalize (in_fst_split_in_pair p marking H7); intro; elim H; intros.
      (* Applies the completeness hypothesis. *)
      generalize (H3 p x H4 H19); intro.
      (* Applies check_inhib_complete *)
      generalize (check_inhib_complete spn marking p t x H' H0 H19 H21); intro.
      (* Then, shows a contradiction. *)
      rewrite e0 in H22; inversion H22.
  Qed.
  
  (** Correctness proof for map_check_inhib. *)

  Lemma map_check_inhib_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (t : Trans)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      map_check_inhib spn marking (inhib_pl neighbours_of_t) t = Some true ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> (n < (inhib spn t p) \/ (inhib spn t p) = 0).
  Proof.
    intros spn marking t neighbours_of_t.
    functional induction (map_check_inhib spn marking (inhib_pl neighbours_of_t) t)
               using map_check_inhib_ind;
      intros.
    assert (incl (inhib_pl neighbours_of_t) (inhib_pl neighbours_of_t)) by (apply incl_refl).
    (* Proof in two stages. *)
    assert (H' := classic (In p (inhib_pl neighbours_of_t))).
    elim H'; intro.
    (* First stage, p ∈ inhib_places, then we apply map_check_inhib_aux_correct. *)
    - generalize (map_check_inhib_aux_correct
                    spn marking (inhib_pl neighbours_of_t) t true neighbours_of_t
                    H H0 H1 H4 H2); intro. 
      apply (H6 p n H5 H3).
    (* Second stage, p ∉ inhib_places, then (inhib spn t p) = 0 *)
    - unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold AreWellDefinedInhibEdges in H16.
      generalize (H16 t neighbours_of_t p H1); intro.
      elim H; clear H; intros.
      generalize (H17 H5); intro; right; assumption.
  Qed.

  (** Correctness proof for map_check_inhib. *)

  Lemma map_check_inhib_complete :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (t : Trans)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      (forall (p : Place) (n : nat),
          In (p, n) marking -> (n < (inhib spn t p) \/ (inhib spn t p) = 0)) ->
      map_check_inhib spn marking (inhib_pl neighbours_of_t) t = Some true.
  Proof.
    intros spn marking t neighbours_of_t.
    unfold map_check_inhib; intros.
    assert (incl (inhib_pl neighbours_of_t) (inhib_pl neighbours_of_t)) by apply incl_refl.
    (* Apply map_check_inhib_aux_complete. *)
    apply map_check_inhib_aux_complete with (neighbours_of_t := neighbours_of_t).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - intros; apply (H2 p n H5).
  Qed.

End MapCheckFunctions.

(** ** Lemmas on is_sensitized. *)

(*!=========================!*)
(*! LEMMAS ON is_sensitized !*)
(*!=========================!*)

Section IsSensitized.

  (** Correctness proof for is_sensitized and IsSensitized *)

  Theorem is_sensitized_correct :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      is_sensitized spn marking neighbours_of_t t = Some true ->
      IsSensitized spn marking t.
  Proof.
    do 4 intro;
      functional induction (is_sensitized spn marking neighbours_of_t t)
                 using is_sensitized_ind;
      intros Hwell_def_spn Hsame_struct Hin_lneigh Hfun.
    (* GENERAL CASE *)
    - injection Hfun; intro Heq_check.
      apply andb_prop in Heq_check; elim Heq_check; intros Heq_check' Heq_inhib.
      apply andb_prop in Heq_check'; elim Heq_check'; intros Heq_pre Heq_test.
      (* Determines ∀ (p, n) ∈ marking, (pre spn t p) <= n *)
      rewrite Heq_pre in e.
      specialize (map_check_pre_correct
                    spn marking t neighbours_of_t
                    Hwell_def_spn Hsame_struct Hin_lneigh e)
        as Hmap_pre.
      (* Determines ∀ (p, n) ∈ marking, (test spn t p) <= n *)
      rewrite Heq_test in e0.
      specialize (map_check_test_correct
                    spn marking t neighbours_of_t
                    Hwell_def_spn Hsame_struct Hin_lneigh e0)
        as Hmap_test.
      (* Determines ∀ (p, n) ∈ marking, n < (inhib spn t p) ∨ (inhib spn t p) = 0 *)
      rewrite Heq_inhib in e1.
      specialize (map_check_inhib_correct
                    spn marking t neighbours_of_t
                    Hwell_def_spn Hsame_struct Hin_lneigh e1)
        as Hmap_inhib.
      (* Unfolds IsSensitized and applies all previous lemmas. *)
      unfold IsSensitized; intros.
      repeat (assumption || split).
      + explode_well_defined_spn.
        apply in_fst_split in Hin_lneigh.
        unfold NoUnknownTransInLNeighbours in *.
        rewrite <- Hunk_tr_neigh in *.
        assumption.
      + apply (Hmap_pre p n H).
      + apply (Hmap_test p n H).
      + apply (Hmap_inhib p n H).
    (* ERROR CASES *)
    - inversion Hfun.
    - inversion Hfun.
    - inversion Hfun.
  Qed.

  (** Completeness proof for is_sensitized and IsSensitized *)

  Theorem is_sensitized_complete :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      IsSensitized spn marking t ->
      is_sensitized spn marking neighbours_of_t t = Some true.
  Proof.
    intros spn marking t neighbours_of_t;
      functional induction (is_sensitized spn marking neighbours_of_t t)
                 using is_sensitized_ind;
      intros Hwell_defined_spn Hmarking_same_struct Hin_lneigh Hspec;
      unfold IsSensitized in Hspec;
      (* Builds t ∈ spn.(transs), and cleans up the context. *)
      assert (Hin_lneigh' := Hin_lneigh);
      apply in_fst_split in Hin_lneigh;
      assert (Hwell_defined_spn' := Hwell_defined_spn);
      explode_well_defined_spn;
      unfold NoUnknownTransInLNeighbours in Hunk_tr_neigh;
      rewrite <- Hunk_tr_neigh in Hin_lneigh;
      rename Hin_lneigh into Hin_transs;
      (* Applies Hspec, then clears it. *)
      decompose [and] Hspec; clear Hspec;
        clear H H1 H0; rename H3 into Hspec;
      (* Builds ∀ (p,n) ∈ marking, (pre spn t p) ≤ n, 
         then applies map_check_pre_complete.
       *)
      assert (Hmap_check_pre :
                forall (p : Place) (n : nat), In (p, n) marking -> pre spn t p <= n) by
          (intros p n Hin_m; generalize (Hspec p n Hin_m) as Hend; intro; elim Hend; auto);
      generalize (map_check_pre_complete spn marking t neighbours_of_t
                                         Hwell_defined_spn
                                         Hmarking_same_struct
                                         Hin_lneigh'
                                         Hmap_check_pre) as Hmap_check_pre';
      intro;
      (* Builds ∀ (p,n) ∈ marking, (test spn t p) ≤ n, 
         then applies map_check_test_complete.
       *)
      assert (Hmap_check_test :
                forall (p : Place) (n : nat), In (p, n) marking -> test spn t p <= n)
        by (intros p n Hin_m;
            generalize (Hspec p n Hin_m) as Hend;
            intro; decompose [and] Hend; auto);
      generalize (map_check_test_complete spn marking t neighbours_of_t
                                          Hwell_defined_spn
                                          Hmarking_same_struct
                                          Hin_lneigh'
                                          Hmap_check_test) as Hmap_check_test';
      intro;
      (* Builds ∀ (p,n) ∈ marking, (inhib spn t p) ≤ n, 
         then applies map_check_inhib_complete.
       *)
      assert (Hmap_check_inhib :
                forall (p : Place) (n : nat),
                  In (p, n) marking -> (n < (inhib spn t p) \/ (inhib spn t p) = 0))
        by (intros p n Hin_m;
            generalize (Hspec p n Hin_m) as Hend;
            intro; decompose [and] Hend; auto);
      generalize (map_check_inhib_complete spn marking t neighbours_of_t
                                           Hwell_defined_spn
                                           Hmarking_same_struct
                                           Hin_lneigh'
                                           Hmap_check_inhib) as Hmap_check_inhib';
      intro.
    (* General case, all went well. 
       Using IsSensitized to prove that all the map_check functions
       return true. *)
    (* Rewrites the results of map_check functions, then reflexivity. *)
    - rewrite Hmap_check_pre' in e;
        rewrite Hmap_check_test' in e0;
        rewrite Hmap_check_inhib' in e1.
      injection e as e_check_pre_value;
        injection e0 as e_check_test_value;
        injection e1 as e_check_inhib_value.
      rewrite <- e_check_inhib_value;
        rewrite <- e_check_pre_value;
        rewrite <- e_check_test_value.
      do 2 rewrite andb_true_r; reflexivity.
    (* CASE map_check_inhib returns None, impossible regarding the hypotheses. *)
    - rewrite Hmap_check_inhib' in e1; inversion e1.
    (* CASE map_check_test returns None, impossible regarding the hypotheses. *)
    - rewrite Hmap_check_test' in e0; inversion e0.
    (* CASE map_check_pre returns None, impossible regarding the hypotheses. *)
    - rewrite Hmap_check_pre' in e; inversion e.
  Qed.

End IsSensitized.

(** ** Lemmas on spn_is_firable. *)

(*!==========================!*)
(*! LEMMAS ON spn_is_firable !*)
(*!==========================!*)

Section SpnIsFirable.
  
  (** Correctness proof between spn_is_firable and SpnIsfirable. *)

  Theorem spn_is_firable_correct :
    forall (spn : Spn)
           (state : SpnState)
           (neigh_of_t : Neighbours)
           (t : Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn state ->
      In (t, neigh_of_t) spn.(lneighbours) ->
      spn_is_firable spn state neigh_of_t t = Some true ->
      SpnIsFirable spn state t.
  Proof.
    intros spn state neigh_of_t t
           Hwell_def_spn
           Hwell_def_state
           Hin_lneigh
           Hfun.
    unfold spn_is_firable in Hfun.
    unfold SpnIsFirable; intros.
    explode_well_defined_spn_state.
    explode_well_defined_spn.
    (* Builds In t (transs spn) *)
    unfold NoUnknownTransInLNeighbours in *.
    assert (Hin_lneigh' := Hin_lneigh).
    apply in_fst_split in Hin_lneigh'.
    rewrite <- Hunk_tr_neigh in *.
    rename Hin_lneigh' into Hin_transs.
    (* Builds IsSensitized *)
    generalize (is_sensitized_correct spn (marking state) t neigh_of_t Hwell_def_spn
                                      Hsame_marking_spn Hin_lneigh Hfun) as His_sens; intro.
    apply (conj Hwell_def_spn (conj Hwell_def_state (conj Hin_transs His_sens))).
  Qed.

  (** Completeness proof between spn_is_firable and SpnIsfirable. *)

  Theorem spn_is_firable_complete :
    forall (spn : Spn)
           (state : SpnState)
           (neigh_of_t : Neighbours)
           (t : Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn state ->
      In (t, neigh_of_t) spn.(lneighbours) ->
      SpnIsFirable spn state t ->
      spn_is_firable spn state neigh_of_t t = Some true.
  Proof.
    intros spn state neigh_of_t t
           Hwell_def_spn
           Hwell_def_state
           Hin_lneigh
           Hspec.
    unfold SpnIsFirable in Hspec; unfold spn_is_firable.
    apply is_sensitized_complete.
    - assumption.
    - unfold IsWellDefinedSpnState in Hwell_def_state; elim Hwell_def_state; auto.
    - assumption.
    - decompose [and] Hspec; auto.
  Qed.

  (** Correctness and completeness conjunction for spn_is_firable. *)
  
  Theorem spn_is_firable_iff :
    forall (spn : Spn)
           (state : SpnState)
           (neigh_of_t : Neighbours)
           (t : Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn state ->
      In (t, neigh_of_t) spn.(lneighbours) ->
      spn_is_firable spn state neigh_of_t t = Some true <-> SpnIsFirable spn state t.
  Proof.
    intros; split.
    - apply (spn_is_firable_correct spn state neigh_of_t t H H0 H1).
    - apply (spn_is_firable_complete spn state neigh_of_t t H H0 H1).
  Qed.

End SpnIsFirable.

(*!================================!*)
(*!=== LEMMAS ON get_neighbours ===!*)
(*!================================!*)

(** ** Lemmas on get_neighbours. *)

Section GetNeighbours.

  (** Correctness proof for get_neighbours. *)
  
  Lemma get_neighbours_correct :
    forall (lneighbours : list (Trans * Neighbours)) (t : Trans) (neigh_of_t : Neighbours),
      get_neighbours lneighbours t = Some neigh_of_t -> In (t, neigh_of_t) lneighbours.
  Proof.
    intros lneighbours t;
      functional induction (get_neighbours lneighbours t)
                 using get_neighbours_ind;
      intros neigh_of_t Hfun.
    - inversion Hfun.
    - apply beq_nat_true in e1; rewrite e1.
      injection Hfun; intros Heq; rewrite Heq; apply in_eq.
    - apply in_cons; apply IHo; assumption.
  Qed.

  (** Completeness proof for get_neighbours. *)

  Lemma get_neighbours_complete :
    forall (lneighbours : list (Trans * Neighbours)) (t : Place) (neigh_of_t : Neighbours),
      NoDup (fst (split lneighbours)) ->
      In (t, neigh_of_t) lneighbours ->
      get_neighbours lneighbours t = Some neigh_of_t.
  Proof.
    intros lneighbours t neigh_of_t;
      functional induction (get_neighbours lneighbours t) using get_neighbours_ind;
      intros Hnodup Hspec;
      (rewrite fst_split_cons_app in Hnodup;
       simpl in Hnodup;
       apply NoDup_cons_iff in Hnodup)
      || auto.
    - elim Hspec.
    - apply in_inv in Hspec; elim Hspec; intro Heq.
      + injection Heq; intros Heq_neigh Heq_t; rewrite Heq_neigh; reflexivity.
      + elim Hnodup; intros Hnot_in Hnodup_tail.
        apply beq_nat_true in e1; rewrite e1 in Hnot_in.
        apply in_fst_split in Heq; contradiction.
    - apply IHo.
      + elim Hnodup; auto.
      + apply in_inv in Hspec; elim Hspec; intro Heq.
        -- injection Heq; intros Heq_neigh Heq_t.
           apply beq_nat_false in e1; contradiction.
        -- assumption.
  Qed.
  
End GetNeighbours.

(*!===========================================!*)
(*!=== LEMMAS ON spn_fire and spn_map_fire ===!*)
(*!===========================================!*)

(** ** Lemmas on spn_fire and spn_map_fire. *)

(** *** Proof spn_map_fire returns a well-defined SpnState. *)

Section SpnMapFireWellDefinedState.

  (** Under some hypotheses, all fired transitions returned by spn_fire_aux
      are included in [spn.(transs)]. *)

  Lemma spn_fire_aux_incl_fired_transs :
    forall (spn : Spn)
      (s : SpnState)
      (residual_marking : list (Place * nat))
      (fired : list Trans)
      (pg : list Trans)
      (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      incl (fired ++ pg) spn.(transs) ->
      spn_fire_aux spn s residual_marking fired pg = Some final_fired ->
      incl final_fired spn.(transs).
  Proof.
    intros spn s residual_marking fired pg;
      functional induction (spn_fire_aux spn s residual_marking fired pg)
                 using spn_fire_aux_ind;
      intros final_fired Hwell_def_spn Hwell_def_state Hincl_f_pg Hfun.
    (* BASE CASE *)
    - injection Hfun;
        intro Heq_fired;
        rewrite <- Heq_fired;
        rewrite <- app_nil_end in Hincl_f_pg; assumption.
    (* GENERAL CASE, the strategy is to apply the induction hypothesis. *)
    - rewrite <- app_assoc in IHo.
      apply (IHo final_fired Hwell_def_spn Hwell_def_state Hincl_f_pg Hfun).
    (* CASE update_residual_marking = None. *)
    - inversion Hfun.
    (* CASE is_sensitized = Some false, the strategy is to apply IH. *)
    (* First, builds incl (fired ++ tail) (transs spn) *)
    - apply incl_app_inv in Hincl_f_pg; elim Hincl_f_pg; intros Hincl_f Hincl_pg.
      apply incl_cons_inv in Hincl_pg.
      specialize (incl_app Hincl_f Hincl_pg) as Hincl_f_tail.
      (* Applies IHo *)
      apply (IHo final_fired Hwell_def_spn Hwell_def_state Hincl_f_tail Hfun).
    (* CASE is_sensitized returns None. *)
    - inversion Hfun.
    (* CASE spn_is_firable returns Some false. *)
    (* First, builds incl (fired ++ tail) (transs spn) *)
    - apply incl_app_inv in Hincl_f_pg; elim Hincl_f_pg; intros Hincl_f Hincl_pg.
      apply incl_cons_inv in Hincl_pg.
      specialize (incl_app Hincl_f Hincl_pg) as Hincl_f_tail.
      (* Applies IHo *)
      apply (IHo final_fired Hwell_def_spn Hwell_def_state Hincl_f_tail Hfun).
    (* CASE spn_is_firable returns None. *)
    - inversion Hfun.
    (* CASE get_neighbours returns None. *)
    - inversion Hfun.
  Qed.  
  
  (** Under some hypotheses, all fired transitions returned by spn_fire
      are included in [spn.(transs)]. *)
  
  Lemma spn_fire_incl_fired_transs :
    forall (spn : Spn)
           (s : SpnState)
           (pgroup : list Trans)
           (fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      In pgroup spn.(priority_groups) ->
      spn_fire spn s pgroup = Some fired ->
      incl fired spn.(transs).
  Proof.
    intros spn s pgroup fired Hwell_def_spn Hwell_def_state Hin_spn_pgs Hfun.
    unfold spn_fire in Hfun.
    (* Builds incl ([] ++ pgroup) (transs spn)) *)
    explode_well_defined_spn.
    unfold NoUnknownInPriorityGroups in *.
    assert (Hincl_pg_transs : incl pgroup (transs spn))
      by (intros t Hin_pgroup;
          specialize (in_concat t pgroup (priority_groups spn) Hin_pgroup Hin_spn_pgs)
            as Hin_concat_pgs;
          rewrite Hno_unk_pgroups; assumption).
    rewrite <- app_nil_l with (l := pgroup) in Hincl_pg_transs.
    (* Apply spn_fire_aux_incl_fired_transs *)
    apply (spn_fire_aux_incl_fired_transs
             spn s (marking s) [] pgroup fired
             Hwell_def_spn Hwell_def_state Hincl_pg_transs Hfun).
  Qed.
  
  (** Under some hypotheses, all fired transitions returned by 
      [spn_map_fire_aux spn s fired pgroups] are included
      in the list of transitions [spn.(transs)]. *)
  
  Lemma spn_map_fire_aux_incl_fired_transs :
    forall (spn : Spn)
      (s : SpnState)
      (fired : list Trans)
      (pgroups : list (list Trans))
      (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      incl pgroups spn.(priority_groups) ->
      incl fired spn.(transs) ->
      spn_map_fire_aux spn s fired pgroups = Some final_fired ->
      incl final_fired spn.(transs).
  Proof.
    intros spn s fired pgroups;
      functional induction (spn_map_fire_aux spn s fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hwell_def_spn Hwell_def_state Hincl_pgs Hincl_fired Hfun.
    (* BASE CASE *)
    - injection Hfun; intro Heq_fired; rewrite <- Heq_fired; assumption.
    (* GENERAL CASE, applying induction hypothesis. *)
    - specialize (incl_cons_inv pgroup pgroups_tail (priority_groups spn) Hincl_pgs) as Hincl_pgs'.
      (* Builds incl (fired_transitions ++ fired_trs) (transs spn). 
         First, we need (incl fired_trs (transs spn)), then apply incl_app. *)
      assert (Hin_pgs_tail : In pgroup (pgroup :: pgroups_tail)) by apply in_eq.
      specialize (Hincl_pgs pgroup Hin_pgs_tail) as Hin_spn_pgs.
      specialize (spn_fire_incl_fired_transs
                    spn s pgroup fired_trs Hwell_def_spn
                    Hwell_def_state Hin_spn_pgs e0) as Hincl_fired'.
      specialize (incl_app Hincl_fired Hincl_fired') as Hincl_app.
      apply (IHo final_fired Hwell_def_spn Hwell_def_state Hincl_pgs' Hincl_app Hfun).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (* Under some hypotheses, the list of fired transitions returned by 
     [spn_fire_aux spn s pgroup] contains no duplicate and is included in [pgroup]. *)

  Lemma spn_fire_aux_nodup_fired :
    forall (spn : Spn)
           (s : SpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg : list Trans)
           (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      NoDup (fired ++ pg) ->
      spn_fire_aux spn s residual_marking fired pg = Some final_fired ->
      NoDup final_fired /\ incl final_fired (fired ++ pg). 
  Proof.
    intros spn s residual_marking fired pg final_fired;
      functional induction (spn_fire_aux spn s residual_marking fired pg)
                 using spn_fire_aux_ind;
      intros Hwell_def_spn Hwell_def_state Hnodup_app Hfun.
    (* BASE CASE, pg = [] *)
    - rewrite <- app_nil_end in Hnodup_app.
      assert (Hincl_refl : incl final_fired final_fired) by apply incl_refl.
      rewrite <- app_nil_end.
      injection Hfun; intros Heq; rewrite Heq in *.
      apply (conj Hnodup_app Hincl_refl).
    (* GENERAL CASE *)
    - rewrite <- app_assoc in IHo.
      apply (IHo Hwell_def_spn Hwell_def_state Hnodup_app Hfun).
    (* ERROR CASE, update_residual_marking returns None *)
    - inversion Hfun.
    (* CASE is_sensitized = Some false *)
    - apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.
      specialize (IHo Hwell_def_spn Hwell_def_state Hnodup_app Hfun) as Hw.
      elim Hw; intros Hnodup_ff Hincl_ftail.
      split.
      + assumption.
      + intros a Hin_ff. specialize (Hincl_ftail a Hin_ff) as Hin_ftail.
        apply in_or_app.
        apply in_app_or in Hin_ftail; elim Hin_ftail; intro Hin.
        -- auto.
        -- apply in_cons with (a := t) in Hin; auto.
    (* ERROR CASE, is_sensitized = None *)
    - inversion Hfun.
    (* CASE spn_is_firable = Some false *)
    - apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.
      specialize (IHo Hwell_def_spn Hwell_def_state Hnodup_app Hfun) as Hw.
      elim Hw; intros Hnodup_ff Hincl_ftail.
      split.
      + assumption.
      + intros a Hin_ff. specialize (Hincl_ftail a Hin_ff) as Hin_ftail.
        apply in_or_app.
        apply in_app_or in Hin_ftail; elim Hin_ftail; intro Hin.
        -- auto.
        -- apply in_cons with (a := t) in Hin; auto.
    (* ERROR CASE *)
    - inversion Hfun.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.
      
  (* Under some hypotheses, the list of fired transitions returned by 
     [spn_fire spn s pgroup] contains no duplicate and is included in [pgroup]. *)
  
  Lemma spn_fire_nodup_fired :
    forall (spn : Spn)
           (s : SpnState)
           (pgroup : list Trans)
           (fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      NoDup pgroup ->
      spn_fire spn s pgroup = Some fired ->
      NoDup fired /\ incl fired pgroup.
  Proof.
    intros spn s pgroup fired Hwell_def_spn Hwell_def_state Hnodup_pg Hfun.
    unfold spn_fire in Hfun.
    rewrite <- app_nil_l in Hnodup_pg.
    apply (spn_fire_aux_nodup_fired spn s (marking s) [] pgroup fired
                                    Hwell_def_spn Hwell_def_state Hnodup_pg Hfun).
  Qed.
  
  (** Under some hypotheses, the list of fired transitions returned by 
      [spn_map_fire_aux spn s fired pgroups] contains no duplicate. *)
  
  Lemma spn_map_fire_aux_nodup_fired :
    forall (spn : Spn)
           (s : SpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      NoDup (fired ++ (concat pgroups)) ->
      spn_map_fire_aux spn s fired pgroups = Some final_fired ->
      NoDup final_fired.
  Proof.
    intros spn s fired pgroups;
      functional induction (spn_map_fire_aux spn s fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hwell_def_spn Hwell_def_state Hnodup_fired_pgs Hfun.
    (* BASE CASE, pgroups = []. *)
    - simpl in Hnodup_fired_pgs;
        rewrite <- app_nil_end with (l := fired_transitions) in Hnodup_fired_pgs.
      injection Hfun; intros Heq_fired; rewrite <- Heq_fired; assumption.
    (* GENERAL CASE *)
    (* Builds (NoDup pgroup) to apply spn_fire_nodup_fired. *)
    - rewrite concat_cons in Hnodup_fired_pgs.
      specialize (nodup_app fired_transitions (pgroup ++ concat pgroups_tail) Hnodup_fired_pgs)
        as Hnodup_fpgs_wedge.
      elim Hnodup_fpgs_wedge; intros Hnodup_fired Hnodup_pg.
      apply nodup_app in Hnodup_pg; apply proj1 in Hnodup_pg. 
      specialize (spn_fire_nodup_fired spn s pgroup fired_trs Hwell_def_spn Hwell_def_state
                                       Hnodup_pg e0) as Hnodup_f_w_incl.
      (* Applies nodup_app_incl to get 
         NoDup ((fired_transitions ++ fired_trs) ++ concat pgroups_tail) *)
      elim Hnodup_f_w_incl; intros Hnodup_ftrs Hincl_fpg.
      specialize (nodup_app_incl fired_transitions pgroup (concat pgroups_tail) fired_trs
                                 Hnodup_fired_pgs Hnodup_ftrs Hincl_fpg)
        as Hnodup_ff_concat.
      rewrite app_assoc in Hnodup_ff_concat.
      (* Applies IHo *)
      apply (IHo final_fired Hwell_def_spn Hwell_def_state Hnodup_ff_concat Hfun).
    (* CASE spn_fire returns None. *)
    - inversion Hfun.
  Qed.

  (** ∀ spn, s, such that IsWelldefinedspn spn ∧ IsWelldefinedspnstate spn s,
      spn_map_fire spn s = Some s' ⇒ IsWelldefinedspnstate spn s' *)
  
  Lemma spn_map_fire_well_defined_state :
    forall (spn : Spn) (s s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      spn_map_fire spn s = Some s' ->
      IsWellDefinedSpnState spn s'.
  Proof.
    intros spn s;
      functional induction (spn_map_fire spn s) using spn_map_fire_ind;
      intros s' Hwell_def_spn Hwell_def_s Hfun.
    (* GENERAL CASE *)
    - unfold IsWellDefinedSpnState; split.
      (* Proves MarkingHaveSameStruct (initial_marking spn) (marking s'). 
         Easy because marking is not updated between s and s'. *)
      + explode_well_defined_spn_state.
        injection Hfun; intro Heq_s'; rewrite <- Heq_s'; simpl; assumption.
      + split;
          assert (Hincl_pgs : incl spn.(priority_groups) spn.(priority_groups))
          by (apply incl_refl);
          assert (Hincl_nil : incl [] spn.(transs)) by (intros a Hin_nil; inversion Hin_nil);
          injection Hfun; intro Heq_s'; rewrite <- Heq_s'; simpl.
        (* Proves (incl s'.(fired) spn.(transs)) *)
        -- apply (spn_map_fire_aux_incl_fired_transs
                    spn s [] (priority_groups spn) fired Hwell_def_spn Hwell_def_s
                    Hincl_pgs Hincl_nil e).
        (* Proves (NoDup s'.(fired)) *)
        -- explode_well_defined_spn.
           unfold NoIntersectInPriorityGroups in *.
           rewrite <- app_nil_l in Hno_inter. 
           apply (spn_map_fire_aux_nodup_fired
                   spn s [] (priority_groups spn) fired Hwell_def_spn Hwell_def_s
                   Hno_inter e).
    (* CASE OF ERROR *)
    - inversion Hfun.
  Qed.
  
End SpnMapFireWellDefinedState.

(** *** First part of correctness proof *)
  
(** The goal in this part is to prove: 

    spn_map_fire = Some s' ⇒ ∀ t ∉ firable(s') ⇒ t ∉ Fired'  

    All un-firable transitions are not fired. *)
  
Section SpnNotFirableNotFired.

  (** ∀ t ∈ fired, 
      spn_fire_aux spn state residual_marking fired group = Some final_fired ⇒ 
      t ∈ final_fired *)
  
  Lemma spn_fire_aux_in_fired :
    forall (spn : Spn)
      (state : SpnState)
      (residual_marking : list (Place * nat))
      (fired : list Trans)
      (pgroup : list Trans)
      (final_fired : list Trans)
      (t : Trans),
      In t fired ->
      spn_fire_aux spn state residual_marking fired pgroup = Some final_fired ->
      In t final_fired.
  Proof.
    intros spn state residual_marking fired pgroup;
      functional induction (spn_fire_aux spn state residual_marking fired pgroup)
                 using spn_fire_aux_ind;
      intros final_fired t' Hin_t_fired Hfun.
    (* BASE CASE *)
    - injection Hfun; intro Heq; rewrite <- Heq; assumption.
    (* GENERAL CASE *)
    - apply or_introl with (B := In t' [t]) in Hin_t_fired.
      apply in_or_app in Hin_t_fired.
      apply (IHo final_fired t' Hin_t_fired Hfun).
    (* ERROR CASE, update_residual_marking = None. *)
    - inversion Hfun.
    (* CASE is_sensitized = Some false. *)
    - apply (IHo final_fired t' Hin_t_fired Hfun).
    (* ERROR CASE, is_sensitized = None. *)
    - inversion Hfun.
    (* CASE spn_is_firable = Some false. *)
    - apply (IHo final_fired t' Hin_t_fired Hfun).
    (* ERROR CASE, spn_is_firable = None. *)
    - inversion Hfun.
    (* ERROR CASE, get_neighbours = None. *)
    - inversion Hfun.
  Qed.
  
  (** ∀ t ∉ pgroup, t ∉ fired, 
      spn_fire_aux spn state residual_marking fired group = Some final_fired ⇒ 
      t ∉ final_fired *)
  
  Lemma spn_fire_aux_not_in_not_fired :
    forall (spn : Spn)
      (state : SpnState)
      (residual_marking : list (Place * nat))
      (fired : list Trans)
      (pgroup : list Trans)
      (final_fired : list Trans)
      (t : Trans),
      ~In t fired ->
      ~In t pgroup ->
      spn_fire_aux spn state residual_marking fired pgroup = Some final_fired ->
      ~In t final_fired.
  Proof.
    intros spn state residual_marking fired pgroup;
      functional induction (spn_fire_aux spn state residual_marking fired pgroup)
                 using spn_fire_aux_ind;
      intros final_fired t' Hnot_in_fired Hnot_in_pg Hfun.
    (* Base case, pgroup = []. *)
    - injection Hfun; intro Heq; rewrite <- Heq; assumption.
    (* General case, all went well. *)
    - apply not_in_cons in Hnot_in_pg.
      elim Hnot_in_pg; intros Hneq_t Hnot_in_tail.
      assert (Hnot_in_tt: ~In t' [t])
        by (apply (diff_not_in t' t Hneq_t)).
      assert (Hnot_in_app : ~In t' (fired ++ [t]))
        by (apply (not_in_app t' fired [t] (conj Hnot_in_fired Hnot_in_tt))).
      apply (IHo final_fired t' Hnot_in_app Hnot_in_tail Hfun).
    - inversion Hfun.
    (* Case is_sensitized = Some false, apply induction hypothesis. *)
    - apply not_in_cons in Hnot_in_pg; elim Hnot_in_pg; intros Hdiff_tt Hnot_in_tail.
      apply (IHo final_fired t' Hnot_in_fired Hnot_in_tail Hfun).
    - inversion Hfun.
    (* Case spn_is_firable = Some false, apply induction hypothesis. *)
    - apply not_in_cons in Hnot_in_pg; elim Hnot_in_pg; intros Hdiff_tt Hnot_in_tail.
      apply (IHo final_fired t' Hnot_in_fired Hnot_in_tail Hfun).
    - inversion Hfun.
    - inversion Hfun.
  Qed.

  (** ∀ t ∈ pgroup, t ∉ fired, t ∉ firable(state),
      spn_fire_aux spn state residual_marking fired group = Some final_fired ⇒ 
      t ∉ final_fired *)
  
  Theorem spn_fire_aux_not_firable_not_fired :
    forall (spn : Spn)
      (state : SpnState)
      (residual_marking : list (Place * nat))
      (fired : list Trans)
      (pg : list Trans)
      (pgroup : list Trans)
      (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn state ->
      In pgroup spn.(priority_groups) ->
      NoDup pg ->
      incl pg pgroup ->
      spn_fire_aux spn state residual_marking fired pg = Some final_fired ->
      (forall t : Trans,
          In t pg ->
          ~In t fired ->
          ~SpnIsFirable spn state t ->
          ~In t final_fired).
  Proof.
    intros spn state residual_marking fired pg;
      functional induction (spn_fire_aux spn state residual_marking fired pg)
                 using spn_fire_aux_ind;
      intros pgroup final_fired Hwell_def_spn Hwell_def_state Hin_pgroups
             Hnodup_pg Hincl_pg Hfun t' Hin_pg Hnot_in_fired Hnot_firable.
    (* Base case, pg = []. *)
    - inversion Hin_pg.
    (* Case spn_is_firable = Some true, impossible regarding
       the hypotheses. *)
    - apply in_inv in Hin_pg; elim Hin_pg.
      (* Case t' = t. We have to show ~SpnIsFirable -> spn_is_firable = Some false,
         then show a contradiction. *)
      + intro Heq_t.
        elimtype False; apply Hnot_firable.
        (* Builds In (t, neighbours_of_t) spn.(lneighbours), 
           necessary to apply spn_is_firable_correct. *)
        generalize (get_neighbours_correct spn.(lneighbours) t neighbours_of_t e0)
          as Hin_lneigh; intro.
        (* Generalizes spn_is_firable_correct. *)
        generalize (spn_is_firable_correct
                      spn state neighbours_of_t t Hwell_def_spn Hwell_def_state
                      Hin_lneigh e1) as Hfirable; intro.
        rewrite <- Heq_t; assumption.
      (* Induction case. *)
      + intro Hin_tail.
        apply IHo with (pgroup := pgroup).
        -- assumption.
        -- assumption.
        -- assumption.
        -- apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg; auto.
        -- unfold incl; intros t'' Hin_tail'; apply in_cons with (a := t) in Hin_tail'.
           apply (Hincl_pg t'' Hin_tail').
        -- assumption.
        -- assumption.
        -- intro Hin_fired_app; apply in_app_or in Hin_fired_app; elim Hin_fired_app.
           { intro Hin_fired; apply (Hnot_in_fired Hin_fired). }
           { intro Hin_tt; apply in_inv in Hin_tt; elim Hin_tt.
             ++ intro Heq_tt.
                apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg.
                intros Hnot_in_tail Hnodup_tail.
                rewrite Heq_tt in Hnot_in_tail; apply (Hnot_in_tail Hin_tail).
             ++ auto.
           }
        -- assumption.
    (* Case update_residual_marking returns None. *)
    - inversion Hfun.
    (* Case is_sensitized returns Some false. *)
    - apply IHo with (pgroup := pgroup).
      + assumption.
      + assumption.
      + assumption.
      + apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg; auto.
      + unfold incl; intros t'' Hin_tail'; apply in_cons with (a := t) in Hin_tail'.
           apply (Hincl_pg t'' Hin_tail').
      + assumption.
      + apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg.
        intros Hnot_in_tail Hnodup_tail.
        apply in_inv in Hin_pg; elim Hin_pg.
        -- intro Heq_t.
           elimtype False; apply Hnot_firable.
           (* Builds In (t, neighbours_of_t) spn.(lneighbours), 
              necessary to apply spn_is_firable_correct. *)
           generalize (get_neighbours_correct spn.(lneighbours) t neighbours_of_t e0)
             as Hin_lneigh; intro.
           (* Generalizes spn_is_firable_correct. *)
           generalize (spn_is_firable_correct
                         spn state neighbours_of_t t Hwell_def_spn Hwell_def_state
                         Hin_lneigh e1) as Hfirable; intro.
           rewrite <- Heq_t; assumption.
        -- auto.
      + assumption.
      + assumption.
    (* Case is_sensitized returns None. *)
    - inversion Hfun.
    (* Case spn_is_firable returns Some false. *)
    - apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg; intros Hnot_in_tail Hnodup_tail.
      apply in_inv in Hin_pg; elim Hin_pg.
      (* When t = t', then t ∉ fired and t ∉ tail ⇒ t ∉ final_fired 
         thanks to lemma spn_fire_aux_not_in_not_fired. *)
      + intro Heq_tt. rewrite Heq_tt in Hnot_in_tail.
        apply (spn_fire_aux_not_in_not_fired
                 spn state residual_marking fired tail final_fired t'
                 Hnot_in_fired Hnot_in_tail Hfun).
      + intro Hin_tail; apply IHo with (pgroup := pgroup).
        -- assumption.
        -- assumption.
        -- assumption.
        -- apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg; auto.
        -- unfold incl; intros t'' Hin_tail'; apply in_cons with (a := t) in Hin_tail'.
           apply (Hincl_pg t'' Hin_tail').
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
    (* Case spn_is_firable = None *)
    - inversion Hfun.
    (* Case get_neighbours = None *)
    - inversion Hfun.
  Qed.

  (** ∀ pgroup ∈ spn.(priority_groups),
      spn_fire spn state pgroup = Some fired ⇒ 
      ∀ t ∈ pgroup, t ∉ firable(state) ⇒ t ∉ fired. *)
  
  Theorem spn_fire_not_firable_not_fired :
    forall (spn : Spn)
           (state : SpnState)
           (pgroup : list Trans)
           (fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn state ->
      In pgroup spn.(priority_groups) ->
      spn_fire spn state pgroup = Some fired ->
      (forall t : Trans,
          In t pgroup ->
          ~SpnIsFirable spn state t ->
          ~In t fired).
  Proof.
    unfold spn_fire.
    intros spn state pgroup fired Hwell_def_spn Hwell_def_state
           Hin_pgroups Hfun t Hin_pgroup Hnot_firable.
    (* Builds (incl pgroup pgroup). *)
    assert (Hincl_pgroup : incl pgroup pgroup) by (apply incl_refl).
    (* Builds NoDup pgroup. *)
    unfold IsWellDefinedSpn in Hwell_def_spn;
      decompose [and] Hwell_def_spn; intros; rename_well_defined_spn.
    unfold NoDupTranss in *.
    unfold NoUnknownInPriorityGroups in *.
    rewrite Hno_unk_pgroups in Hnodup_transs.
    generalize (nodup_concat_gen spn.(priority_groups) Hnodup_transs pgroup Hin_pgroups)
      as Hnodup_pgroup; intro.              
    (* Applies spn_fire_aux_not_firable_not_fired. *)
    generalize (spn_fire_aux_not_firable_not_fired
                  spn state state.(marking) [] pgroup pgroup fired Hwell_def_spn
                  Hwell_def_state Hin_pgroups Hnodup_pgroup Hincl_pgroup Hfun) as Hspec; intro.
    assert (Hnot_in : ~In t []) by (apply in_nil).
    apply (Hspec t Hin_pgroup Hnot_in Hnot_firable). 
  Qed.

  (** spn_map_fire_aux spn state fired pgroups = Some final_fired ⇒ 
      ∀ t ∉ fired ∧ t ∉ (concat pgroups) ⇒ t ∉ final_fired *)
  
  Theorem spn_map_fire_aux_not_in_not_fired :
    forall (spn : Spn)
      (state : SpnState)
      (fired : list Trans)
      (pgroups : list (list Trans))
      (final_fired : list Trans),
      spn_map_fire_aux spn state fired pgroups = Some final_fired ->
      forall t : Trans, ~In t fired -> ~In t (concat pgroups) -> ~In t final_fired.
  Proof.
    intros spn state fired pgroups;
      functional induction (spn_map_fire_aux spn state fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hfun t Hnot_in_fired Hnot_in_concat.
    (* Base case, pgroups = [] *)
    - injection Hfun; intro Heq; rewrite Heq in *; assumption.
    (* General case *)
    - unfold spn_fire in e0.
      (* Builds (~In t []) to apply spn_fire_aux_not_in_not_fired. *)
      assert (Hnot_in_nil : ~In t []) by apply in_nil.
      (* Builds (~In t pgroup) to apply spn_fire_aux_not_in_not_fired. *)
      simpl in Hnot_in_concat.
      generalize (not_app_in t pgroup (concat pgroups_tail) Hnot_in_concat)
        as Hnot_in_wedge; intro.
      elim Hnot_in_wedge; intros Hnot_in_pg Hnot_in_concat'.
      (* Applies spn_fire_aux_not_in_not_fired *)
      generalize (spn_fire_aux_not_in_not_fired
                    spn state (marking state) [] pgroup fired_trs t
                    Hnot_in_nil Hnot_in_pg e0) as Hnot_in_ff; intro.
      (* Builds ~In t (fired_transitions ++ fired_trs) to apply IHo. *)
      generalize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_ff))
                 as Hnot_in_all_ff; intro.
      (* Applies induction hypothesis. *)
      apply (IHo final_fired Hfun t Hnot_in_all_ff Hnot_in_concat').
    (* Case spn_fire returns None. *)
    - inversion Hfun.
  Qed.

  (** spn_map_fire_aux spn state fired pgroups = Some final_fired ⇒ 
      ∀ t ∈ fired ⇒ t ∈ final_fired *)
  
  Theorem spn_map_fire_aux_in_fired :
    forall (spn : Spn)
      (state : SpnState)
      (fired : list Trans)
      (pgroups : list (list Trans))
      (final_fired : list Trans),
      spn_map_fire_aux spn state fired pgroups = Some final_fired ->
      forall t : Trans, In t fired -> In t final_fired.
  Proof.
    intros spn state fired pgroups;
      functional induction (spn_map_fire_aux spn state fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hfun t Hin_t_fired.
    (* BASE CASE *)
    - injection Hfun; intro Heq; rewrite Heq in *; assumption.
    (* GENERAL CASE *)
    - apply or_introl with (B := In t fired_trs) in Hin_t_fired.
      apply in_or_app in Hin_t_fired.
      apply (IHo final_fired Hfun t Hin_t_fired).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.
  
  (** spn_map_fire_aux spn s fired pgroups = Some final_fired ⇒ 
      ∀ pgroup ∈ pgroups, ∀ t ∈ pgroup, 
      t ∉ fired ⇒ t ∉ firable(s) ⇒ t ∉ final_fired 
      
      N.B. firable(s) ≡ firable(s'), because s.(marking) = s'.(marking). *)
  
  Theorem spn_map_fire_aux_not_firable_not_fired :
    forall (spn : Spn)
      (state : SpnState)
      (fired : list Trans)
      (pgroups : list (list Trans))
      (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn state ->
      NoDup (concat pgroups) ->
      incl pgroups spn.(priority_groups) ->
      spn_map_fire_aux spn state fired pgroups = Some final_fired ->
      (forall (pgroup : list Trans) (t : Trans),
          In pgroup pgroups ->
          In t pgroup ->
          ~In t fired ->
          ~SpnIsFirable spn state t ->
          ~In t final_fired).
  Proof.
    intros spn state fired pgroups;
      functional induction (spn_map_fire_aux spn state fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hwell_def_spn Hwell_def_state Hnodup_concat Hincl_pgs Hfun pgroup' t
             Hin_pgs Hin_pg Hnot_in_fired Hnot_firable.
    (* Base case, pgroups = []. *)
    - inversion Hin_pgs.
    (* General case *)
    - apply in_inv in Hin_pgs; elim Hin_pgs.
      (* CASE pgroup = pgroup' *)
      + intro Heq_pg.
        (* Builds ~In t (concat pgroups_tail) to apply 
           spn_map_fire_aux_not_in_not_fired *)
        rewrite concat_cons in Hnodup_concat.
        rewrite Heq_pg in Hnodup_concat.
        generalize (nodup_app_not_in
                      pgroup' (concat pgroups_tail) Hnodup_concat
                      t Hin_pg) as Hnot_in_concat; intro.
        (* Builds In pgroup spn.(priority_groups) to apply 
           spn_fire_not_firable_not_fired *)
        assert (Hin_pgs' : In pgroup (pgroup :: pgroups_tail)) by apply in_eq.
        generalize (Hincl_pgs pgroup Hin_pgs') as Hin_spn_pgs; intro.
        (* Builds (~In t fired_trs) by applying spn_fire_not_firable_not_fired. *)
        rewrite <- Heq_pg in Hin_pg.
        generalize (spn_fire_not_firable_not_fired
                      spn state pgroup fired_trs Hwell_def_spn Hwell_def_state
                      Hin_spn_pgs e0 t Hin_pg Hnot_firable) as Hnot_in_fired'; intro.
        (* Builds (~In t (fired_transitions ++ fired_trs)) *)
        generalize (not_in_app t fired_transitions fired_trs
                               (conj Hnot_in_fired Hnot_in_fired')) as Hnot_in_fired_app; intro.
        (* Applies spn_map_fire_aux_not_in_not_fired *)
        apply (spn_map_fire_aux_not_in_not_fired
                 spn state (fired_transitions ++ fired_trs) pgroups_tail final_fired Hfun
                 t Hnot_in_fired_app Hnot_in_concat).
      (* CASE In pgroup' pgroups_tail, then apply IHo. *)
      + intro Hin_pgs_tail.
        (* Builds NoDup (concat pgroups_tail). *)
        rewrite concat_cons in Hnodup_concat.
        generalize (nodup_app pgroup (concat pgroups_tail) Hnodup_concat)
          as Hnodup_concat_wedge; intro.
        elim Hnodup_concat_wedge; intros Hnodup_pg Hnodup_concat_tail.
        (* Builds (incl pgroups_tail (priority_groups spn)). *)
        generalize (incl_cons_inv
                      pgroup pgroups_tail
                      spn.(priority_groups) Hincl_pgs) as Hincl_pgs'; intro.
        (* Builds ~In t (fired_transitions ++ fired_trs). 

           First, we need (~In t pgroup) to apply spn_fire_aux_not_in_not_fired. *)
        specialize (NoDup_app_comm pgroup (concat pgroups_tail) Hnodup_concat)
          as Hnodup_concat_inv.
        specialize (nodup_app_not_in (concat pgroups_tail) pgroup Hnodup_concat_inv)
          as Hfall_not_in_pg.
        specialize (in_concat t pgroup' pgroups_tail Hin_pg Hin_pgs_tail) as Hin_concat.
        specialize (Hfall_not_in_pg t Hin_concat) as Hnot_in_pg.
        (* Second, we need to build (~In t fired_trs) by 
           applying spn_fire_aux_not_in_not_fired. *)
        unfold spn_fire in e0.
        assert (Hnot_in_nil : ~In t []) by apply in_nil.
        specialize (spn_fire_aux_not_in_not_fired
                      spn state (marking state) [] pgroup fired_trs t
                      Hnot_in_nil Hnot_in_pg e0) as Hnot_in_fired'.
        (* Finally, builds (~In t (fired_transitions ++ fired_trs)) *)
        specialize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_fired'))
          as Hnot_in_fired_app.
        (* Applies IHo. *)
        apply (IHo final_fired Hwell_def_spn Hwell_def_state
                   Hnodup_concat_tail Hincl_pgs' Hfun pgroup' t Hin_pgs_tail
                   Hin_pg  Hnot_in_fired_app Hnot_firable).
    (* Case spn_fire returns None. *)
    - inversion Hfun.
  Qed.

  (** spn_map_fire spn s = Some s' ⇒  
      ∀ pgroup ∈ spn.(priority_groups), t ∈ pgroup,
      t ∉ firable(s') ⇒ t ∉ s'.(fired) *)

  Theorem spn_map_fire_not_firable_not_fired :
    forall (spn : Spn) (s s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      spn_map_fire spn s = Some s' ->
      forall (pgroup : list Trans) (t : Trans),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        ~SpnIsFirable spn s' t ->
        ~In t s'.(fired).
  Proof.
    intros spn s s' Hwell_def_spn Hwell_def_s Hfun.
    (* Builds IsWellDefined spn s', needed to apply spn_map_fire_aux_not_firable_not_fired *)
    specialize (spn_map_fire_well_defined_state spn s s' Hwell_def_spn Hwell_def_s Hfun)
      as Hwell_def_s'.
    functional induction (spn_map_fire spn s) using spn_map_fire_ind;
      intros pgroup' t Hin_spn_pgs Hin_pg Hnot_firable.
    (* GENERAL CASE: the strategy is to apply spn_map_fire_aux_not_firable_not_fired. 
                     First, we need to build a few hypotheses. *)
    - explode_well_defined_spn.
      (* Builds NoDup (concat spn.(priority_groups)). *)
      unfold NoIntersectInPriorityGroups in Hno_inter.
      (* Builds (incl spn.(pgs) spn.(pgs)) *)
      assert (Hincl_spn_pgs : incl spn.(priority_groups) spn.(priority_groups))
        by apply incl_refl.
      (* Builds ~In t [] *)
      assert (Hnot_in_nil : ~In t []) by apply in_nil.
      (* Builds (~SpnIsFirable spn s t) *)
      assert (Heq_marking : s.(marking) = s'.(marking))
        by (injection Hfun; intro Heq; rewrite <- Heq; reflexivity). 
      specialize (state_same_marking_firable_iff
                    spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s' Heq_marking t)
        as Hnot_firable_iff.
      rewrite <- Hnot_firable_iff in Hnot_firable.
      (* Rewrites the goal. *)
      injection Hfun; intro Heq_s'; rewrite <- Heq_s'; simpl.
      (* Applies spn_map_fire_aux_not_firable_not_fired. *)
      apply (spn_map_fire_aux_not_firable_not_fired
               spn s [] (priority_groups spn) fired Hwell_def_spn Hwell_def_s
               Hno_inter Hincl_spn_pgs e pgroup' t Hin_spn_pgs Hin_pg Hnot_in_nil Hnot_firable).
    (* ERROR CASE, spn_map_fire_aux returns None. *)
    - inversion Hfun.
  Qed.
  
End SpnNotFirableNotFired.

(** *** Second part of correctness proof *)
  
(** The goal in this part is to prove: 

    spn_map_fire = Some s' ⇒ 
    ∀ t ∈ firable(s'), (∀ t'|t' ≻ t, t' ∉ firable(s')) ⇒ t ∉ Fired' *)

Section SpnHigherPriorityNotFirable.

  (** spn_fire_aux spn s residual_markng fired pgroup  = Some final_fired ⇒
      (marking s) = residual_marking) ⇒
      ∀ t ∈ pgroup, t ∈ firable(s), (∀ t'|t' ≻ t, t' ∉ firable(s)) ⇒ t ∈ final_fired 
      
      Here, we make the hypothesis the (marking s) = residual_marking, because all transitions
      with a higher priority than t (predecessors in list pgroup) were not fired, then
      the marking was never updated. *)

  Theorem spn_fire_aux_higher_priority_not_firable :
    forall (spn : Spn)
      (s : SpnState)
      (residual_marking : list (Place * nat))
      (fired : list Trans)
      (pg pgroup : list Trans)
      (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      residual_marking = (marking s) ->
      In pgroup spn.(priority_groups) ->
      IsDecreasedList pg pgroup ->
      NoDup pg ->
      spn_fire_aux spn s residual_marking fired pg = Some final_fired ->
      forall (t : Trans),
        In t pg ->
        SpnIsFirable spn s t ->
        (forall (t' : Trans), In t' pg ->
                              HasHigherPriority spn t' t pgroup ->
                              ~SpnIsFirable spn s t') ->
        In t final_fired. 
  Proof.
    intros spn s residual_marking fired pg;
      functional induction (spn_fire_aux spn s residual_marking fired pg)
                 using spn_fire_aux_ind;
      intros pgroup final_fired Hwell_def_spn Hwell_def_s Heq_marking
             Hin_spn_pgs Hdec_list Hnodup_pg Hfun t' Hin_t_pg Hfirable_t Hhas_high.
    (* BASE CASE *)
    - inversion Hin_t_pg.
    (* GENERAL CASE *)
    (* Two cases, either t' is head of pg, or is in tail. *)
    - elim Hin_t_pg.
      (* Case t = t' *)
      + intro Heq_tt'.
        (* Builds In t (fired ++ [t]) to apply spn_fire_aux_in_fired. *)
        assert (Hin_fired_t : In t (fired ++ [t])) by (apply in_or_app; right; simpl; auto).
        rewrite <- Heq_tt'.
        apply (spn_fire_aux_in_fired
                 spn s residual_marking' (fired ++ [t]) tail final_fired t
                 Hin_fired_t Hfun).
      (* Case In t' tail. *)
      + intro Hin_t'_tail.
        (* Builds ~SpnIsFirable t in the context, and shows a contradiction with e1. *)
        (* Obviously, if t' ∈ tail ∧ NoDup (t :: tail), 
           then IsPredInNoDupList t t' (t :: tail) ⇒ IsPredInNoDupList t t' pgroup      
                                                   ⇒ t ≻ t' *)
        specialize (is_pred_in_list_in_tail t t' tail Hin_t'_tail) as His_pred.
        (* Builds NoDup pgroup. *)
        explode_well_defined_spn.
        unfold NoIntersectInPriorityGroups in *.
        specialize (nodup_concat_gen (priority_groups spn) Hno_inter pgroup Hin_spn_pgs)
          as Hnodup_pg'.
        (* Builds IsPredInList t t' pgroup. *)
        specialize (is_pred_in_dec_list His_pred Hdec_list Hnodup_pg') as His_pred_in_pg.
        assert (Hhas_high_t : HasHigherPriority spn t t' pgroup).
        {
          unfold HasHigherPriority.
          apply is_decreased_list_incl in Hdec_list.
          repeat (assumption || split).
          - assert (Hin_eq : In t (t :: tail)) by apply in_eq.
            apply (Hdec_list t Hin_eq).
          - apply (Hdec_list t' Hin_t_pg).
          - intro.
            rewrite <- H in Hin_t'_tail.
            apply NoDup_cons_iff in Hnodup_pg.
            apply proj1 in Hnodup_pg; contradiction.
        }
        specialize (Hhas_high t (in_eq t tail) Hhas_high_t) as Hnot_firable_t.
        apply (get_neighbours_correct (lneighbours spn) t neighbours_of_t) in e0.
        apply (spn_is_firable_correct spn s neighbours_of_t t Hwell_def_spn Hwell_def_s e0) in e1.
        contradiction.
    (* ERROR CASE, update_residual_marking = None. *)
    - inversion Hfun.
    (* CASE is_sensitized = Some false. *)
    - elim Hin_t_pg.
      (* First case, t' is head of (t :: tail). 
         then as t' is firable, and residual_marking equals (marking s),
         then t' must be sensitized by residual_marking.
         Shows a contradiction with the hypotheses. *)
      + intro Heq_tt'.
        rewrite <- Heq_tt' in Hfirable_t.
        (* Builds is_sensitized = Some true in Hfirable_t. *)
        unfold SpnIsFirable in Hfirable_t; decompose [and] Hfirable_t.
        clear H H1 H0; rename H3 into His_sens.
        explode_well_defined_spn_state.
        specialize (get_neighbours_correct (lneighbours spn) t neighbours_of_t e0)
                   as Hin_lneigh.
        specialize (is_sensitized_complete
                      spn (marking s) t neighbours_of_t Hwell_def_spn Hsame_marking_spn
                      Hin_lneigh His_sens) as His_sens_true.
        rewrite Heq_marking in e3.
        rewrite e3 in His_sens_true.
        inversion His_sens_true.
        (* Second case, t' ∈ tail ∧ NoDup (t :: tail) ⇒ t ≻ t' ⇒ t ∉ firable(s). 
           Then, contradicts e1: spn_is_firable = Some true. *)
      + intro Hin_t'_tail.
        specialize (is_pred_in_list_in_tail t t' tail Hin_t'_tail) as His_pred.
        (* Builds NoDup pgroup. *)
        explode_well_defined_spn.
        unfold NoIntersectInPriorityGroups in *.
        specialize (nodup_concat_gen (priority_groups spn) Hno_inter pgroup Hin_spn_pgs)
          as Hnodup_pg'.
        (* Builds IsPredInList t t' pgroup. *)
        specialize (is_pred_in_dec_list His_pred Hdec_list Hnodup_pg') as His_pred_in_pg.
        assert (Hhas_high_t : HasHigherPriority spn t t' pgroup).
        {
          unfold HasHigherPriority;
          repeat (assumption || split);
          apply is_decreased_list_incl in Hdec_list.
          - assert (Hin_eq : In t (t :: tail)) by apply in_eq.
            apply (Hdec_list t Hin_eq).
          - apply (Hdec_list t' Hin_t_pg).
          - intro.
            rewrite <- H in Hin_t'_tail.
            apply NoDup_cons_iff in Hnodup_pg.
            apply proj1 in Hnodup_pg; contradiction.
        }
        specialize (Hhas_high t (in_eq t tail) Hhas_high_t) as Hnot_firable_t.
        apply (get_neighbours_correct (lneighbours spn) t neighbours_of_t) in e0.
        apply (spn_is_firable_correct spn s neighbours_of_t t Hwell_def_spn Hwell_def_s e0) in e1.
        contradiction.
    (* ERROR CASE, is_sensitized = None. *)
    - inversion Hfun.
    (* CASE spn_is_firable = Some false *)
    - elim Hin_t_pg.
      (* First case, t = t', then Hfirable_t is in contradiction with e1. *)
      + intro Heq_tt'.
        rewrite <- Heq_tt' in Hfirable_t.
        apply (get_neighbours_correct (lneighbours spn) t neighbours_of_t) in e0.
        apply (spn_is_firable_complete spn s neighbours_of_t t Hwell_def_spn Hwell_def_s e0)
          in Hfirable_t.
        rewrite e1 in Hfirable_t.
        inversion Hfirable_t.
      (* Second case, applies the induction hypothesis. *)
      + intro Hin_t'_tail.
        (* Builds Hhas_high' to apply IHo. *)
        assert (Hhas_high' :
                  forall t'0 : Trans,
                   In t'0 tail -> HasHigherPriority spn t'0 t' pgroup -> ~ SpnIsFirable spn s t'0).
        {
          intros t'0 Hin_t'0_tail Hhas_high_t'0.
          apply in_cons with (a := t) in Hin_t'0_tail.
          apply (Hhas_high t'0 Hin_t'0_tail Hhas_high_t'0).
        }
        (* Builds NoDup tail and IsDecreasedList tail pgroup. *)
        apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg; intros Hnot_in_tail Hnodup_tail.
        apply is_decreased_list_cons in Hdec_list.
        apply (IHo pgroup final_fired Hwell_def_spn Hwell_def_s Heq_marking Hin_spn_pgs
                   Hdec_list Hnodup_tail Hfun t' Hin_t'_tail Hfirable_t Hhas_high').
    (* ERROR CASE, spn_is_firable = None. *)
    - inversion Hfun.
    (* ERROR CASE, get_neighbours = None. *)
    - inversion Hfun.
  Qed.
  
  (** spn_map_fire_aux spn s fired pgroups = Some fired ⇒ 
      ∀ pgroup ∈ pgroups, t ∈ pgroup, t ∈ firable(s), 
        (∀ t'|t' ≻ t, t' ∉ firable(s)) ⇒ t ∈ fired *)
  
  Theorem spn_map_fire_aux_higher_priority_not_firable :
    forall (spn : Spn)
      (s : SpnState)
      (fired_transitions : list Trans)
      (pgroups : list (list Trans))
      (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      incl pgroups (priority_groups spn) ->
      spn_map_fire_aux spn s fired_transitions pgroups = Some final_fired ->
      forall (pgroup : list Trans) (t : Trans),
          In pgroup pgroups ->
          In t pgroup ->
          SpnIsFirable spn s t ->
          (forall (t' : Trans),
              In t' pgroup ->
              HasHigherPriority spn t' t pgroup ->
              ~SpnIsFirable spn s t') ->
          In t final_fired.
  Proof.
    intros spn s fired_transitions pgroups;
      functional induction (spn_map_fire_aux spn s fired_transitions pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hwell_def_spn Hwell_def_s Hincl_pgs Hfun
             pgroup' t Hin_pgs Hin_pg Hfirable_t Hhas_high.
    (* BASE CASE, pgroups = [] *)
    - inversion Hin_pgs.
    (* GENERAL CASE *)
    - elim Hin_pgs.
      (* First case, pgroup = pgroup'. *)
      + intro Heq_pg.
        rewrite Heq_pg in *.
        (* Builds pgroup' ∈ (priority_groups spn). *)
        specialize (Hincl_pgs pgroup' Hin_pgs) as Hin_spn_pgs.
        (* Builds NoDup pgroup'. *)
        explode_well_defined_spn.
        unfold NoIntersectInPriorityGroups in *.
        specialize (nodup_concat_gen (priority_groups spn)
                                     Hno_inter pgroup' Hin_spn_pgs) as Hnodup_pg.
        (* Builds In t fired_trs. *)
        unfold spn_fire in *.
        specialize (spn_fire_aux_higher_priority_not_firable
                      spn s (marking s) [] pgroup' pgroup' fired_trs
                      Hwell_def_spn Hwell_def_s
                      (eq_refl (marking s)) Hin_spn_pgs (IsDecreasedList_refl pgroup')
                      Hnodup_pg
                      e0 t Hin_pg
                      Hfirable_t Hhas_high) as Hin_fired.
        (* Applies spn_map_fire_aux_in_fired *)
        specialize (in_or_app fired_transitions fired_trs t
                              (or_intror (In t fired_transitions) Hin_fired))
          as Hin_fired_app.
        apply (spn_map_fire_aux_in_fired
                 spn s (fired_transitions ++ fired_trs) pgroups_tail final_fired
                 Hfun t Hin_fired_app).
      (* Second case, pgroup' ∈ pgroups_tail, then apply IHo. *)
      + intro Hin_pgs_tail.
        apply (IHo final_fired Hwell_def_spn Hwell_def_s
                   (incl_cons_inv pgroup pgroups_tail (priority_groups spn) Hincl_pgs)
                   Hfun pgroup' t Hin_pgs_tail Hin_pg Hfirable_t Hhas_high).
    (* ERROR CASE, spn_map_fire_aux returns None. *)
    - inversion Hfun.
  Qed.
  
  (** spn_map_fire spn s = Some s' ⇒ 
      ∀ t ∈ firable(s'), (∀ t'|t' ≻ t, t' ∉ firable(s')) ⇒ t ∈ s'.(fired) *)

  Theorem spn_map_fire_higher_priority_not_firable :
    forall (spn : Spn)
      (s s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      spn_map_fire spn s = Some s' ->
      (forall (pgroup : list Trans) (t : Trans),
          In pgroup spn.(priority_groups) ->
          In t pgroup ->
          SpnIsFirable spn s' t ->
          (forall (t' : Trans),
              In t' pgroup ->
              HasHigherPriority spn t' t pgroup ->
              ~SpnIsFirable spn s' t') ->
          In t s'.(fired)).
  Proof.
    
    intros spn s s' Hwell_def_spn Hwell_def_s Hfun;
      specialize (spn_map_fire_well_defined_state
                    spn s s' Hwell_def_spn Hwell_def_s Hfun) as Hwell_def_s'.
    functional induction (spn_map_fire spn s) using spn_map_fire_ind;
      intros pgroup t Hin_pgs Hin_t_pg Hfirable_t Hnot_firable_high.
    (* GENERAL CASE *)
    - injection Hfun; intro Heq_state; rewrite <- Heq_state; simpl.
      
      (* Builds (marking s) = (marking s') *)
      assert (Heq_marking_state : (marking s) = (marking s'))
        by (rewrite <- Heq_state; simpl; auto).
      (* Transforms SpnIsFirable spn s t in SpnIsFirable spn s' t. *)
      specialize (state_same_marking_firable_iff
                    spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s'
                    Heq_marking_state) as Hfirable_iff.
      assert (Hhas_high :
                forall t' : Trans,
                  In t' pgroup ->
                  HasHigherPriority spn t' t pgroup -> ~ SpnIsFirable spn s t').
      {
        intros t' Hin_t'_pgroup Hhas_high. 
        rewrite Hfirable_iff with (t := t').
        apply (Hnot_firable_high t' Hin_t'_pgroup Hhas_high).
      }
      rewrite <- Hfirable_iff in *.
      apply (spn_map_fire_aux_higher_priority_not_firable
               spn s [] (priority_groups spn) fired
               Hwell_def_spn Hwell_def_s (incl_refl (priority_groups spn))
               e pgroup t Hin_pgs Hin_t_pg Hfirable_t Hhas_high).
    (* ERROR CASE, spn_map_fire_aux returns None. *)
    - inversion Hfun.
  Qed.
  
End SpnHigherPriorityNotFirable.

(** *** Third part of correctness proof *)
  
(** The goal in this part is to prove: 

    spn_map_fire = Some s' ⇒ 
    ∀ t ∈ firable(s'), t ∈ sens(M - ∑ pre(t'), ∀ t'∈ Pr(t)) ⇒ t ∈ Fired' *)

Section SpnSensitizedByResidual.

  Theorem spn_fire_aux_final_fired_vee :
    forall (spn : Spn)
           (s : SpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg : list Trans)
           (final_fired : list Trans)
           (t : Trans),
      NoDup (fired ++ pg) ->
      In t final_fired ->
      spn_fire_aux spn s residual_marking fired pg = Some final_fired ->
      In t fired \/ In t pg.
  Proof.
    intros spn s residual_marking fired pg;
      functional induction (spn_fire_aux spn s residual_marking fired pg)
                 using spn_fire_aux_ind;
      intros final_fired t' Hnodup_app Hin_t_ff Hfun.
    (* BASE CASE, pg = []. *)
    - injection Hfun as Heq_fired; left; rewrite Heq_fired; assumption.
    (* GENERAL CASE *)
    - rewrite <- app_assoc in IHo.
      specialize (IHo final_fired t' Hnodup_app Hin_t_ff Hfun) as H_ff_vee'.
      elim H_ff_vee'.
      + intro Hin_t_fired_app.
        apply in_app_or in Hin_t_fired_app.
        elim Hin_t_fired_app.
        -- auto.
        -- intro Hin_tt; simpl in Hin_tt.
           elim Hin_tt; [ intro Heq_tt; rewrite <- Heq_tt; right; apply in_eq |
                          intro Hfalse; inversion Hfalse].
      + intro Hin_t_tail; apply in_cons with (a := t) in Hin_t_tail; right; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
    (* CASE is_sensitized = Some false *)
    - apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.
      specialize (IHo final_fired t' Hnodup_app Hin_t_ff Hfun) as Hin_vee.
      elim Hin_vee.
      + intro Hin_t_fired; left; assumption.
      + intro Hin_t_tail; right; apply in_cons with (a := t) in Hin_t_tail; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
    (* CASE spn_is_firable = Some false *)
    - apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.
      specialize (IHo final_fired t' Hnodup_app Hin_t_ff Hfun) as Hin_vee.
      elim Hin_vee.
      + intro Hin_t_fired; left; assumption.
      + intro Hin_t_tail; right; apply in_cons with (a := t) in Hin_t_tail; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.
  
  Theorem spn_fire_aux_sens_by_residual :
    forall (spn : Spn)
           (s : SpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg pgroup : list Trans)
           (final_fired : list Trans),
      (* Misc. hypotheses. *)
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      (* Hypotheses on pgroup. *)
      In pgroup spn.(priority_groups) ->
      (* Hypotheses on pg. *)
      IsDecreasedList pg pgroup ->
      NoDup (fired ++ pg) ->
      (* Hypotheses on residual_marking. *)
      (forall (p : Place) (n : nat) ,
                (exists preSum : nat, PreSum spn p fired preSum /\
                                      In (p, n + preSum) s.(marking)) <->
                In (p, n) residual_marking) ->
      MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
      (* Function ⇒ Specification *)
      spn_fire_aux spn s residual_marking fired pg = Some final_fired ->
      forall (t : Trans)
             (res_marking : list (Place * nat)),
        (* Hypotheses on t. *)
        In t pg ->
        SpnIsFirable spn s t ->
        IsSensitized spn res_marking t ->
        (* Hypotheses on fired *)
        (forall t'' : Trans, In t'' fired -> HasHigherPriority spn t'' t pgroup /\
                                             In t'' final_fired) ->
        (* Hypotheses on res_marking. *)
        MarkingHaveSameStruct spn.(initial_marking) res_marking ->
        (forall (pr : list Trans),
            (forall t' : Trans,
                HasHigherPriority spn t' t pgroup /\ In t' final_fired <->
                In t' pr) ->
            (forall (p : Place) (n : nat) ,
                (exists preSum : nat, PreSum spn p pr preSum /\
                                      In (p, n + preSum) s.(marking)) <->
                In (p, n) res_marking)) ->
        In t final_fired.
  Proof.
    intros spn s residual_marking fired pg;
      functional induction (spn_fire_aux spn s residual_marking fired pg)
                 using spn_fire_aux_ind;
      intros pgroup final_fired Hwell_def_spn Hwell_def_s
             Hin_spn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct Hfun
             t' res_marking Hin_t_pg Hfirable_t Hsens_t Hhigh_in_fired Hsame_struct' Hres_m.
    (* BASE CASE, pg = []. *)
    - inversion Hin_t_pg.
    (* GENERAL CASE, with two subcases. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].
      (* First subcase, t = t' then t' ∈ (fired ++ [t]) ⇒ t' ∈ final_fired. *)
      + assert (Hin_t_fired : In t (fired ++ [t])) by (apply in_or_app; right; apply in_eq).
        rewrite <- Heq_tt'.
        apply (spn_fire_aux_in_fired spn s residual_marking' (fired ++ [t]) tail final_fired t
                                     Hin_t_fired Hfun).
      (* Second subcase, In t' tail then apply the induction hypothesis. *)
      + admit.        
    (* ERROR CASE, update_residual_marking = None. *)
    - inversion Hfun.
    (* CASE, is_sensitized = Some false. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].
      (* First subcase, t = t'. *)
      (* What we want to show is a contradiction between is_sensitized = Some false 
         and IsSensitized spn t' res_marking. *)
      (* Then, we need to show that we have IsSensitized spn t' residual_marking.
         We can deduce it from Hsens_t. *)
      + assert (Hpr_is_fired :
                  forall t'' : Trans, 
                   HasHigherPriority spn t'' t' pgroup /\ In t'' final_fired -> In t'' fired). 
        {
          intros t'' Hw; elim Hw; intros Hhas_high Hin_ts_ff; clear Hw.
          specialize (NoDup_remove fired tail t Hnodup_pg) as Hnodup_app;
            apply proj1 in Hnodup_app.
          specialize (spn_fire_aux_final_fired_vee
                        spn s residual_marking fired tail final_fired t''
                        Hnodup_app Hin_ts_ff Hfun) as Hin_ts_vee.
          elim Hin_ts_vee.
          - auto.
          (* If t'' ∈ tail, then ~IsPredInNoDupList t'' t' (t' :: tail) ⇒ 
             ~IsPredInNoDupList t'' t' pgroup, then contradiction. *)
          - intro Hin_ts_tail.
            unfold HasHigherPriority in Hhas_high.
            (* Builds ~IsPredInNoDuplist t'' t' (t' :: tail) *)
            assert (Hnot_is_pred : ~IsPredInNoDupList t'' t' (t' :: tail)) by
                apply not_is_pred_in_list_if_hd.
            rewrite Heq_tt' in Hdec_list.
            specialize (not_is_pred_in_dec_list Hdec_list Hin_ts_tail) as Hnot_is_pred_in_pg.
            decompose [and] Hhas_high; contradiction.
        }
        (* Now we have Hpr_is_fired, we can specialize Hres_m. *)
        assert (Hpr_iff :
                  forall t'' : Trans,
                    HasHigherPriority spn t'' t' pgroup /\ In t'' final_fired <-> In t'' fired)
          by (intros t'0; split; [apply (Hpr_is_fired t'0) | apply (Hhigh_in_fired t'0)]).
        specialize (Hres_m fired Hpr_iff).
        (* Now we can show the equivalence between residual_marking and res_marking. *)
        assert (Hequiv_m : forall (x : Place * nat), In x res_marking <-> In x residual_marking).
        {
          intros x.
          split.
          - intro Hin_res_m.
            induction x. 
            rewrite <- (Hres_m a b) in Hin_res_m.
            rewrite (Hresid_m a b) in Hin_res_m.
            assumption.
          - intro Hin_resid_m.
            induction x. 
            rewrite <- (Hresid_m a b) in Hin_resid_m.
            rewrite (Hres_m a b) in Hin_resid_m.
            assumption.
        }
        (* Then, we deduce IsSensitized spn residual_marking t' from Hequiv_m. *)
        assert (Hsens_t_in_residual_m : IsSensitized spn residual_marking t').
        {
          unfold IsSensitized.
          split. assumption.
          split. assumption.
          split. apply get_neighbours_correct in e0.
          apply in_fst_split in e0.
          explode_well_defined_spn.
          unfold NoUnknownTransInLNeighbours in *.
          rewrite <- Hunk_tr_neigh in e0.
          rewrite <- Heq_tt'; assumption.
          intros p n Hin_resid_m.
          rewrite <- Hequiv_m in Hin_resid_m.
          unfold IsSensitized in Hsens_t.
          decompose [and] Hsens_t.
          apply (H3 p n Hin_resid_m).
        }
        (* Then we apply is_sensitized_complete to show the contradiction with e3. *)
        apply get_neighbours_correct in e0.
        rewrite Heq_tt' in e0.
        specialize (is_sensitized_complete
                      spn residual_marking t' neighbours_of_t
                      Hwell_def_spn Hsame_struct e0 Hsens_t_in_residual_m) as Hsens_t_false.
        rewrite Heq_tt' in e3.
        rewrite Hsens_t_false in e3; inversion e3.
      (* Second subcase, In t' tail then apply the induction hypothesis. *)
      + apply is_decreased_list_cons in Hdec_list. 
        apply NoDup_remove in Hnodup_pg; apply proj1 in Hnodup_pg.
        apply (IHo pgroup final_fired Hwell_def_spn Hwell_def_s 
                   Hin_spn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct
                   Hfun t' res_marking
                   Hin_t'_tail Hfirable_t Hsens_t Hhigh_in_fired Hsame_struct' Hres_m).
    (* ERROR CASE, is_sensitized = None. *)
    - inversion Hfun.
    (* CASE, spn_is_firable = Some false. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].
      (* First subcase t = t', show a contradiction between e1 and Hfirable_t. *)
      + rewrite <- Heq_tt' in Hfirable_t.
        apply get_neighbours_correct in e0.
        apply (spn_is_firable_complete
                 spn s neighbours_of_t t Hwell_def_spn Hwell_def_s e0) in Hfirable_t.
        rewrite Hfirable_t in e1; inversion e1.
      (* Second subcase, In t' tail, then apply induction hypothesis. *)
      + apply is_decreased_list_cons in Hdec_list. 
        apply NoDup_remove in Hnodup_pg; apply proj1 in Hnodup_pg.
        apply (IHo pgroup final_fired Hwell_def_spn Hwell_def_s 
                   Hin_spn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct
                   Hfun t' res_marking
                   Hin_t'_tail Hfirable_t Hsens_t Hhigh_in_fired Hsame_struct' Hres_m).
    (* ERROR CASE, spn_is_firable = None. *)
    - inversion Hfun.
      (* ERROR CASE, get_neighbours = None. *)
  Admitted.

  Lemma pr_is_unique :
    forall (spn : Spn)
           (s : SpnState)
           (residual_marking : list (Place * nat))
           (pgroup : list Trans)
           (fired : list Trans)
           (fired' : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans)
           (t : Trans)
           (pr : list Trans),
      NoDup (fired' ++ pgroup ++ concat pgroups) ->
      spn_fire_aux spn s residual_marking [] pgroup = Some fired ->
      spn_map_fire_aux spn s (fired' ++ fired) pgroups = Some final_fired ->
      (forall t' : Trans, HasHigherPriority spn t' t pgroup /\ In t' fired <-> In t' pr) ->
      (forall t' : Trans, HasHigherPriority spn t' t pgroup /\ In t' final_fired <-> In t' pr).
  Proof.
    intros spn s residual_marking pgroup fired fired' pgroups final_fired t pr
           Hnodup_app Hfun_fire Hfun_map_fire Hin_pr t'.
    split.
    (* CASE, in context t' ≻ t ∧ t' ∈ final_fired *)
    - intro Hpr_wedge.
      (* Two subcases, either t' ∈ fired ∨ t' ∉ fired *)
      specialize (classic (In t' fired)) as Hin_fired_vee.
      inversion_clear Hin_fired_vee as [Hin_t'_fired | Hnot_in_t'_fired].
      (* First subcase, t' ∈ fired *)
      + elim Hpr_wedge; intros Hhas_high Hin_t'_ff.
        specialize (conj Hhas_high Hin_t'_fired) as Hpr_wedge'.
        rewrite Hin_pr in Hpr_wedge'.
        assumption.
      (* Second subcase, 
            t' ∈ pgroup ⇒ 
            t' ∉ fired' ∧ t' ∉ concat pgroups ∧ t' ∉ fired ⇒
            t' ∉ final_fired, contradicts Hpr_wedge. *)
      (* Builds In t' pgroup *)
      + elim Hpr_wedge; intros Hhas_high Hin_ff.
        unfold HasHigherPriority in Hhas_high; decompose [and] Hhas_high.
        clear H H1 H2 H4; rename H0 into Hin_t'_pg.
        (* Builds ~In t' fired /\ ~In t' concat pgroups *)
        apply NoDup_app_comm in Hnodup_app.
        rewrite <- app_assoc in Hnodup_app.
        specialize (nodup_app_not_in pgroup ((concat pgroups) ++ fired') Hnodup_app t' Hin_t'_pg)
          as Hnot_in_t'_app.
        apply not_app_in  in Hnot_in_t'_app.
        elim Hnot_in_t'_app; intros Hnot_in_concat Hnot_t'_in_fired.
        (* Builds ~In t' (fired' ++ fired) *)
        specialize (not_in_app t' fired' fired (conj Hnot_t'_in_fired Hnot_in_t'_fired))
          as Hnot_in_app.
        specialize (spn_map_fire_aux_not_in_not_fired
                      spn s (fired' ++ fired) pgroups final_fired Hfun_map_fire
                      t' Hnot_in_app Hnot_in_concat) as Hnot_in_ff.
        contradiction.
    (* CASE, in context t' ∈ pr *)
    - intro Hin_t'_pr.
      split.
      + rewrite <- Hin_pr in Hin_t'_pr.
        elim Hin_t'_pr; auto.
      (* t' ∈ fired ⇒ t' ∈ final_fired. *)
      + rewrite <- Hin_pr in Hin_t'_pr.
        elim Hin_t'_pr; intros Hhash_high Hin_t'_fired.
        (* Builds In t' (fired' ++ fired) to apply spn_map_fire_aux_in_fired. *)
        specialize (or_intror (In t' fired') Hin_t'_fired) as Hin_t'_vee.
        specialize (in_or_app fired' fired t' Hin_t'_vee) as Hin_t'_app.
        (* Applies spn_map_fire_aux_in_fired. *)
        apply (spn_map_fire_aux_in_fired
                 spn s (fired' ++ fired) pgroups final_fired
                 Hfun_map_fire t' Hin_t'_app).
  Qed.
        
  Theorem spn_map_fire_aux_sens_by_residual :
    forall (spn : Spn)
      (s : SpnState)
      (fired : list Trans)
      (pgroups : list (list Trans))
      (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      incl pgroups (priority_groups spn) ->
      NoDup (fired ++ concat pgroups) ->
      spn_map_fire_aux spn s fired pgroups = Some final_fired ->
      forall (pgroup : list Trans)
        (t : Trans)
        (residual_marking : list (Place * nat)),
        In pgroup pgroups ->
        In t pgroup ->
        ~In t fired ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s t ->
        (forall (p : Place)
                (n preSum : nat)
                (pr : list Trans),
            (forall t' : Trans,
                HasHigherPriority spn t' t pgroup /\ In t' final_fired <-> In t' pr) ->
            In (p, n) s.(marking) ->
            PreSum spn p pr preSum ->
            In (p, n - preSum) residual_marking) ->
        IsSensitized spn residual_marking t ->
        In t final_fired.
  Proof.
    intros spn s fired pgroups;
      functional induction (spn_map_fire_aux spn s fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hwell_def_spn Hwell_def_s Hincl_pgs Hnodup_concat_pgs
             Hfun pgroup' t residual_marking Hin_pgs Hin_t_pg Hnot_in_fired
             Hmark_struct Hfirable_t Hres_mark Hsens_t.
    (* BASE CASE *)
    - inversion Hin_pgs.
    (* GENERAL CASE, two subcases. *)
    - inversion Hin_pgs as [Heq_pg | Hin_pgtail].
      (* First subcase, pgroup = pgroup'. *)
      + unfold spn_fire in *.
        rewrite Heq_pg in *.
        (* Builds pgroup' ∈ (priority_groups spn). *)
        specialize (Hincl_pgs pgroup' Hin_pgs) as Hin_spn_pgs.
        (* Builds NoDup pgroup'. *)
        explode_well_defined_spn.
        unfold NoIntersectInPriorityGroups in *.
        specialize (nodup_concat_gen (priority_groups spn)
                                     Hno_inter pgroup' Hin_spn_pgs) as Hnodup_pg.
        (* Builds an hypothesis close to Hres_mark, except final_fired is replaced by fired_trs. 
           Necessary to apply spn_fire_aux_sens_by_residual. *)
        assert (Hres_mark' :
                  forall (p : Place) (n preSum : nat) (pr : list Trans),
                    (forall t' : Trans,
                        HasHigherPriority spn t' t pgroup' /\ In t' fired_trs <-> In t' pr) ->
                    In (p, n) (marking s) ->
                    PreSum spn p pr preSum ->
                    In (p, n - preSum) residual_marking).
        {
          intros p n preSum pr Hin_pr Hin_m_s Hpre_sum.
          (* Builds hypotheses necessary to apply pr_is_unique. *)
          rewrite concat_cons in Hnodup_concat_pgs.
          (* Applies pr_is_unique. *)
          specialize (pr_is_unique
                        spn s (marking s) pgroup' fired_trs fired_transitions
                        pgroups_tail final_fired t pr Hnodup_concat_pgs e0 Hfun Hin_pr) as Hin_pr'.
          apply (Hres_mark p n preSum pr Hin_pr' Hin_m_s Hpre_sum).
        }
        (* Builds In t fired_trs. *)
        specialize (spn_fire_aux_sens_by_residual
                      spn s (marking s) [] pgroup' pgroup' fired_trs
                      Hwell_def_spn Hwell_def_s Hin_spn_pgs (IsDecreasedList_refl pgroup')
                      Hnodup_pg e0 t residual_marking Hin_t_pg Hmark_struct Hfirable_t Hsens_t
                      Hres_mark') as Hin_t_fired.
        (* Then if t ∈ fired_trs ⇒ t ∈ (fired_transitions ++ fired_trs) ⇒ t ∈ final_fired *)
        assert (Hin_fired_app : In t (fired_transitions ++ fired_trs))
          by (apply in_or_app; right; assumption).
        apply (spn_map_fire_aux_in_fired
                 spn s (fired_transitions ++ fired_trs) pgroups_tail
                 final_fired Hfun t Hin_fired_app).
      (* Second subcase, pgroup' ∈ pgroups_tail, then apply the induction hypothesis *)
      (* Builds incl pgroups_tail (priority_groups spn) *)
      + apply incl_cons_inv in Hincl_pgs. 
        (* Builds ~In t fired_trs to build ~In t (fired_transitions ++ fired_trs). *)
        (* But first, builds ~In t pgroup, because ~In t pgroup ⇒ ~In t fired_trs *)
        assert (Hnodup_concat_pgs_copy := Hnodup_concat_pgs).
        rewrite concat_cons in Hnodup_concat_pgs.
        apply NoDup_app_comm in Hnodup_concat_pgs.
        apply nodup_app in Hnodup_concat_pgs.
        elim Hnodup_concat_pgs; intros Hnodup_app Hnodup_fired.
        apply NoDup_app_comm in Hnodup_app.
        specialize (nodup_app_not_in (concat pgroups_tail) pgroup Hnodup_app)
          as Hnot_in_pgroup.
        specialize (in_concat t pgroup' pgroups_tail Hin_t_pg Hin_pgtail) as Hin_t_concat.
        specialize (Hnot_in_pgroup t Hin_t_concat) as Hnot_in_pgroup.
        unfold spn_fire in e0.
        assert (Hnot_in_nil : ~In t []) by apply in_nil.
        specialize (spn_fire_aux_not_in_not_fired
                      spn s (marking s) [] pgroup fired_trs t
                      Hnot_in_nil Hnot_in_pgroup e0) as Hnot_in_fired'.
        specialize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_fired'))
          as Hnot_in_app.
        (* Builds NoDup ((fired_transitions ++ fired_trs) ++ concat pgroups_tail). *)
        rewrite concat_cons in Hnodup_concat_pgs_copy.
        
        (* First, we need NoDup fired_trs /\ incl fired_trs ([] ++ pgroup) *)
        apply nodup_app in Hnodup_app; elim Hnodup_app; intros Hnodup_concat_pgs' Hnodup_pg.
        rewrite <- app_nil_l in Hnodup_pg.
        specialize (spn_fire_aux_nodup_fired spn s (marking s) [] pgroup fired_trs
                                             Hwell_def_spn Hwell_def_s Hnodup_pg e0)
          as Hnodup_incl.
        elim Hnodup_incl; intros Hnodup_fired_trs Hincl_fired.
        rewrite app_nil_l in Hincl_fired.
        specialize (nodup_app_incl
                      fired_transitions pgroup (concat pgroups_tail) fired_trs
                      Hnodup_concat_pgs_copy Hnodup_fired_trs Hincl_fired) as Hnodup_app'.
        rewrite app_assoc in Hnodup_app'.
        (* Finally applies the induction hypothesis. *)
        apply (IHo final_fired Hwell_def_spn Hwell_def_s
                   Hincl_pgs Hnodup_app' Hfun pgroup' t residual_marking
                   Hin_pgtail Hin_t_pg Hnot_in_app Hmark_struct Hfirable_t Hres_mark Hsens_t).
    (* ERROR CASE. *)
    - inversion Hfun.
  Qed.
  
  Theorem spn_map_fire_sens_by_residual :
    forall (spn : Spn)
           (s s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      spn_map_fire spn s = Some s' ->
      forall (pgroup : list Trans)
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
            PreSum spn p pr preSum ->
            In (p, n - preSum) residual_marking) ->
        IsSensitized spn residual_marking t ->
        In t s'.(fired).
  Proof.
    intros spn s s' Hwell_def_spn Hwell_def_s Hfun;
      specialize (spn_map_fire_well_defined_state
                    spn s s' Hwell_def_spn Hwell_def_s Hfun) as Hwell_def_s';
      functional induction (spn_map_fire spn s) using spn_map_fire_ind;
      intros pgroup t residual_marking Hin_spn_pgs Hin_t_pg Hmark_struct Hfirable_t.
    (* Need to rewrite (SPN.fired s') with fired, (marking s') with (marking s) and
       SpnIsFirable spn s' t with SpnIsFirable spn s t. *)
    - injection Hfun; intro Heq_s'.
      assert (Heq_marking : (marking s) = (marking s')) by (rewrite <- Heq_s'; simpl; auto).
      specialize (state_same_marking_firable_iff
                    spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s' Heq_marking)
        as Heq_firable.
      rewrite <- Heq_s'; simpl.
      rewrite <- Heq_firable in Hfirable_t.
      (* Need of few hypotheses. *)
      explode_well_defined_spn.
      unfold NoIntersectInPriorityGroups in *.
      assert (Hnot_in_nil : ~In t []) by apply in_nil.
      revert H10 H12.
      (* Applies spn_map_fire_aux_sens_by_residual *)
      apply (spn_map_fire_aux_sens_by_residual 
               spn s [] (priority_groups spn) fired Hwell_def_spn Hwell_def_s
               (incl_refl (priority_groups spn)) Hno_inter e pgroup t
               residual_marking Hin_spn_pgs Hin_t_pg Hnot_in_nil Hmark_struct Hfirable_t). 
    - inversion Hfun.    
  Qed.
  
End SpnSensitizedByResidual.

(** Correctness proof between spn_cycle and SpnSemantics_falling_edge. *)

Theorem spn_semantics_falling_edge_correct :
  forall (spn : Spn)
    (s s' s'' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    spn_cycle spn s = Some (s', s'') ->
    SpnSemantics spn s s' falling_edge.
Proof.
  do 2 intro;
    functional induction (spn_cycle spn s) using spn_cycle_ind;
    intros s' s'' Hwell_def_spn Hwell_def_state Hfun.
  (* GENERAL CASE *)
  - apply SpnSemantics_falling_edge.
    (* Trivial proof, IsWellDefinedSpn. *)
    + assumption.
    (* Trivial proof, IsWellDefinedSpnState. *)
    + assumption.
    (* Proves IsWellDefinedSpnState spn s'. *)
    + injection Hfun; intros Heq_fstate Heq_istate; rewrite <- Heq_istate.
      apply (spn_map_fire_well_defined_state
               spn s inter_state Hwell_def_spn Hwell_def_state e).           
    (* Proves s.(marking) = s'.(marking) *)
    + apply spn_map_fire_same_marking in e.
      injection Hfun; intros Heq_fstate Heq_istate; rewrite <- Heq_istate; assumption.
    (* Proves ∀ t ∉ firable(s') ⇒ t ∉ Fired' *)
    + injection Hfun; intros Heq_fstate Heq_istate; rewrite <- Heq_istate.
      apply (spn_map_fire_not_firable_not_fired
               spn s inter_state Hwell_def_spn Hwell_def_state e).
    (* Proves ∀ t ∈ firable(s'), ∀ t' ∈ T|t' ≻ t, t' ∉ firable(s') ⇒ t ∈ Fired' *)
    + injection Hfun; intros Heq_fstate Heq_istate; rewrite <- Heq_istate.
      apply (spn_map_fire_higher_priority_not_firable
               spn s inter_state Hwell_def_spn Hwell_def_state e).
    (* Proves ∀ t ∈ firable(s'), t ∈ sens(m - ∑ pre(t_i)) ⇒ t ∈ Fired'  *)
    +
  - inversion H3.
  - inversion H3.
Qed.

(** Correctness proof between spn_cycle and SpnSemantics_raising_edge. *)

Theorem spn_semantics_raising_edge_correct :
  forall (spn : Spn)
    (s s' s'' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    IsWellDefinedSpnState spn s'' ->
    spn_cycle spn s = Some (s', s'') ->
    SpnSemantics spn s' s'' raising_edge.
Proof.
  do 2 intro.
  functional induction (spn_cycle spn s) using spn_cycle_ind; intros.
Qed.