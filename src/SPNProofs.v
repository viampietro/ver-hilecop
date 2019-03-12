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
    p ∈ (flatten_lneighbours spn.(lneighbours)) *)

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
          In p inhib_places -> In (p, n) marking -> (n < (inhib spn t p) \/ (inhib spn t p) = 0)) ->
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
      intros.
    - injection H2; intros.
      do 2 (apply andb_prop in H3; elim H3; clear H3; intros).
      (* Determines ∀ (p, n) ∈ marking, (pre spn t p) <= n *)
      rewrite H3 in e.
      generalize (map_check_pre_correct spn marking t neighbours_of_t
                                        H H0 H1 e); intro.
      (* Determines ∀ (p, n) ∈ marking, (test spn t p) <= n *)
      rewrite H5 in e0.
      generalize (map_check_test_correct spn marking t neighbours_of_t
                                         H H0 H1 e0); intro.
      (* Determines ∀ (p, n) ∈ marking, n < (inhib spn t p) ∨ (inhib spn t p) = 0 *)
      rewrite H4 in e1.
      generalize (map_check_inhib_correct spn marking t neighbours_of_t
                                          H H0 H1 e1); intro.
      (* Unfolds IsSensitized and applies all previous lemmas. *)
      unfold IsSensitized; intros.
      generalize (H6 p n H12); generalize (H7 p n H12); generalize (H8 p n H12); intros.
      apply (conj H15 (conj H14 H13)).
    - inversion H2.
    - inversion H2.
    - inversion H2.
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
      unfold IsWellDefinedSpn in Hwell_defined_spn;
      decompose [and] Hwell_defined_spn;
      clear Hwell_defined_spn;
      intros;
      rename_well_defined_spn;
      unfold NoUnknownTransInLNeighbours in Hunk_tr_neigh;
      rewrite <- Hunk_tr_neigh in Hin_lneigh;
      rename Hin_lneigh into Hin_transs;
      (* Applies Hspec, then clears it. *)
      generalize (Hspec Hwell_defined_spn'
                        Hmarking_same_struct
                        Hin_transs) as Hspec';
      intro;
      clear Hspec;
      (* Builds ∀ (p,n) ∈ marking, (pre spn t p) ≤ n, 
         then applies map_check_pre_complete.
       *)
      assert (Hmap_check_pre :
                forall (p : Place) (n : nat), In (p, n) marking -> pre spn t p <= n) by
          (intros p n Hin_m; generalize (Hspec' p n Hin_m) as Hend; intro; elim Hend; auto);
      generalize (map_check_pre_complete spn marking t neighbours_of_t
                                         Hwell_defined_spn'
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
            generalize (Hspec' p n Hin_m) as Hend;
            intro; decompose [and] Hend; auto);
      generalize (map_check_test_complete spn marking t neighbours_of_t
                                          Hwell_defined_spn'
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
            generalize (Hspec' p n Hin_m) as Hend;
            intro; decompose [and] Hend; auto);
      generalize (map_check_inhib_complete spn marking t neighbours_of_t
                                           Hwell_defined_spn'
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
    apply is_sensitized_correct with (neighbours_of_t := neigh_of_t).
    - assumption.
    - unfold IsWellDefinedSpnState in Hwell_def_state; elim Hwell_def_state; auto.
    - assumption.
    - assumption.
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
    - apply in_fst_split in Hin_lneigh;
        assert (Hwell_def_spn' := Hwell_def_spn);
        unfold IsWellDefinedSpn in Hwell_def_spn;
        decompose [and] Hwell_def_spn;
        clear Hwell_def_spn;
        intros;
        rename_well_defined_spn;
        unfold NoUnknownTransInLNeighbours in Hunk_tr_neigh;
        rewrite <- Hunk_tr_neigh in Hin_lneigh;
        rename Hin_lneigh into Hin_transs.
      apply (Hspec Hwell_def_spn' Hwell_def_state Hin_transs).
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

Section SpnFire.

  (** *** First part of correctness proof *)
  
  (** The goal in this part is to prove: 

      spn_map_fire = Some s' ⇒ ∀ t ∉ firable(s') ⇒ t ∉ Fired'  

      All un-firable transitions are not fired. *)

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
        unfold SpnIsFirable in Hnot_firable; elimtype False; apply Hnot_firable.
        intros Hwell_def_spn' Hwell_def_state' Hin_transs.
        (* Builds In (t, neighbours_of_t) spn.(lneighbours), 
           necessary to apply spn_is_firable_correct. *)
        generalize (get_neighbours_correct spn.(lneighbours) t neighbours_of_t e0)
          as Hin_lneigh; intro.
        (* Generalizes spn_is_firable_correct. *)
        generalize (spn_is_firable_correct
                      spn state neighbours_of_t t Hwell_def_spn Hwell_def_state
                      Hin_lneigh e1) as Hfirable; intro.
        (* Unfols SpnIsFirable and shows the assumption. *)
        unfold SpnIsFirable in Hfirable; rewrite Heq_t in *.
        apply (Hfirable Hwell_def_spn Hwell_def_state Hin_transs).
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
           unfold SpnIsFirable in Hnot_firable; elimtype False; apply Hnot_firable.
           intros Hwell_def_spn' Hwell_def_state' Hin_transs.
           (* Builds In (t, neighbours_of_t) spn.(lneighbours), 
                necessary to apply spn_is_firable_correct. *)
           generalize (get_neighbours_correct spn.(lneighbours) t neighbours_of_t e0)
             as Hin_lneigh; intro.
           (* Generalizes spn_is_firable_correct. *)
           generalize (spn_is_firable_correct
                         spn state neighbours_of_t t Hwell_def_spn Hwell_def_state
                         Hin_lneigh e1) as Hfirable; intro.
           (* Unfols SpnIsFirable and shows the assumption. *)
           unfold SpnIsFirable in Hfirable; rewrite Heq_t in *.
           apply (Hfirable Hwell_def_spn Hwell_def_state Hin_transs).            
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
    unfold IsWellDefinedSpn in Hwell_def_spn; decompose [and] Hwell_def_spn; intros; rename_well_defined_spn.
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
  
End SpnFire.

(** Correctness proof between spn_cycle and SpnSemantics_falling_edge. *)

Theorem spn_semantics_falling_edge_correct :
  forall (spn : Spn)
    (s s' s'' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    IsWellDefinedSpnState spn s'' ->
    spn_cycle spn s = Some (s', s'') ->
    SpnSemantics spn s s' falling_edge.
Proof.
  do 2 intro;
    functional induction (spn_cycle spn s) using spn_cycle_ind;
    intros.
  - apply SpnSemantics_falling_edge.
    (* Trivial proof, IsWellDefinedSpn. *)
    + assumption.
    (* Trivial proof, IsWellDefinedSpnState. *)
    + assumption.
    (* Trivial proof, IsWellDefinedSpnState. *)
    + assumption.
    (* Proves s.(marking) = s'.(marking) *)
    + apply spn_map_fire_same_marking in e.
      injection H3; intros; rewrite <- H5; assumption.
    (*  *)
    + 
      injection H3; intros; rewrite <- H5.
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