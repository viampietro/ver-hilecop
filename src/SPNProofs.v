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

  (** ∀ s, s', s.(marking) = s'.(marking) ⇒ SpnIsFirable spn s t ⇒ SpnIsfirable spn s' t *)

  Lemma firable_if_same_marking :
    forall (spn : Spn) (s s' : SpnState) (t : Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      IsWellDefinedSpnState spn s' -> 
      s.(marking) = s'.(marking) ->
      SpnIsFirable spn s t ->
      SpnIsFirable spn s' t.
  Proof.
    intros spn s s' t Hwell_def_spn Hwell_def_s Hwell_def_s' Heq_marking His_firable.
    unfold SpnIsFirable in *. intros Hwell_def_spn' Hwell_def_s'0 Hin_transs.
    rewrite <- Heq_marking.
    apply (His_firable Hwell_def_spn Hwell_def_s Hin_transs).
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
        (* Unfolds SpnIsFirable and shows the assumption. *)
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
    intros spn s;
      functional induction (spn_map_fire spn s) using spn_map_fire_ind;
      intros s' Hwell_def_spn Hwell_def_s Hfun pgroup' t
             Hin_spn_pgs Hin_pg Hnot_firable.
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
      (* Builds ~SpnIsFirable spn s t *)
      unfold SpnIsFirable in *.
      (* Applies spn_map_fire_aux_not_firable_not_fired. *)
      apply (spn_map_fire_aux_not_firable_not_fired
               spn s [] (priority_groups spn) fired Hwell_def_spn Hwell_def_state
               Hno_inter Hincl_spn_pgs e pgroup' t Hin_spn_pgs Hin_pg Hnot_in_nil
                                              
                                              
      
  Admitted.
  
End SpnNotFirableNotFired.

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
  - apply SpnSemantics_falling_edge.
    (* Trivial proof, IsWellDefinedSpn. *)
    + assumption.
    (* Trivial proof, IsWellDefinedSpnState. *)
    + assumption.
    (* Trivial proof, IsWellDefinedSpnState. *)
    + assumption.
    (* Proves s.(marking) = s'.(marking) *)
    + apply spn_map_fire_same_marking in e.
      injection Hfun; intros Heq_fstate Heq_istate; rewrite <- Heq_istate; assumption.
    (* Proves ∀ t ∉ firable(s') ⇒ t ∉ Fired' *)
    + injection Hfun; intros Heq_fstate Heq_istate; rewrite <- Heq_istate.
      apply (spn_map_fire_not_firable_not_fired
               spn s inter_state Hwell_def_spn Hwell_def_state e).
    (* Proves ∀ t ∈ firable(s'), ∀ t' ∈ T|t' ≻ t, t' ∉ firable(s') ⇒ t ∈ Fired' *)
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