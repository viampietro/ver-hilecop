Require Import Hilecop.Spn.Spn Hilecop.Spn.SpnAnimator.
Require Import Hilecop.Spn.SpnSemantics Hilecop.Spn.SpnTactics.
Require Import Hilecop.Utils.HilecopLemmas.
Require Import Omega.
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
      intros n Hwell_def_spn Hsame_struct Hin_m Hfun.
    (* General case, all went well. *)
    - apply get_m_correct in e.
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_spn.
      unfold MarkingHaveSameStruct in Hsame_struct.
      unfold NoUnmarkedPlace in Hunm_place.
      unfold NoDupPlaces in Hnodup_places.
      rewrite Hsame_struct in Hunm_place; rewrite Hunm_place in Hnodup_places.
      assert (Heq_pp : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).
      generalize (nodup_same_pair
                    marking Hnodup_places (p, n) (p, nboftokens)
                    Hin_m e Heq_pp) as Heq_nnb; intro.
      injection Heq_nnb as Heq_nnb.
      rewrite <- Heq_nnb in Hfun; injection Hfun as Hfun.
      apply (leb_complete (pre spn t p) n Hfun).
    - inversion Hfun.
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
    intros spn marking p t n Hwell_def_spn Hsame_struct Hin_m Hspec.
    unfold check_pre.
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_m_complete. *)
    explode_well_defined_spn.
    unfold NoDupPlaces in Hnodup_places.
    unfold MarkingHaveSameStruct in Hsame_struct.
    unfold NoUnmarkedPlace in Hunm_place.
    rewrite Hunm_place in Hnodup_places; rewrite Hsame_struct in Hnodup_places.
    specialize (get_m_complete marking p n Hnodup_places Hin_m) as Hget_m.
    rewrite Hget_m.
    apply leb_correct in Hspec; rewrite Hspec; reflexivity.
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
      intros neigh_of_t Hwell_def_spn Hsame_struct Hin_lneigh Hincl_pre_pl
             Hfun p' n Hin_pre_pl Hin_m.
    - inversion Hin_pre_pl.
    - inversion Hin_pre_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_pre_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_pre_correct
                 spn marking p' t n
                 Hwell_def_spn Hsame_struct Hin_m e0).
      + apply incl_cons_inv in Hincl_pre_pl.
        apply (IHo neigh_of_t
                   Hwell_def_spn Hsame_struct Hin_lneigh Hincl_pre_pl
                   Hfun p' n Hin_p'_tail Hin_m).
    - inversion Hfun.
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
      intros neigh_of_t Hwell_def_spn Hsame_struct Hin_lneigh
             Hincl_pre_pl Hspec.
    - reflexivity.
    - (* Builds ∃ x, (p, x) ∈ marking to apply check_pre_complete. *)
      assert (Hin_pre_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_pre_pl p Hin_pre_pl) as Hin_pre_pl_t.
      assert (Hin_flat : In p (flatten_neighbours neigh_of_t))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).
      specialize (in_neigh_in_flatten
                    spn t neigh_of_t p
                    Hwell_def_spn Hin_lneigh Hin_flat) as Hin_flat_lneigh.
      explode_well_defined_spn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      unfold NoUnmarkedPlace in Hunm_place; rewrite Hunm_place in Hin_flat_lneigh.
      unfold MarkingHaveSameStruct in Hsame_struct; rewrite Hsame_struct in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m'); specialize (Hspec p x Hin_pre_pl Hin_m') as Hpre_le.
      (* Applies check_pre_complete, then the induction hypothesis. *)
      specialize (check_pre_complete
                    spn marking p t x
                    Hwell_def_spn Hsame_struct Hin_m' Hpre_le) as Hcheck_pre.
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_pre in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_pre_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail -> In (p, n) marking -> pre spn t p <= n)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo neigh_of_t Hwell_def_spn Hsame_struct Hin_lneigh Hincl_pre_pl Hspec').
    (* Deduces hypotheses necessary to apply check_pre_complete. *)
    - (* Builds ∃ x, (p, x) ∈ marking to apply check_pre_complete. *)
      assert (Hin_pre_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_pre_pl p Hin_pre_pl) as Hin_pre_pl_t.
      assert (Hin_flat : In p (flatten_neighbours neigh_of_t))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).
      specialize (in_neigh_in_flatten
                    spn t neigh_of_t p
                    Hwell_def_spn Hin_lneigh Hin_flat) as Hin_flat_lneigh.
      explode_well_defined_spn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      unfold NoUnmarkedPlace in Hunm_place; rewrite Hunm_place in Hin_flat_lneigh.
      unfold MarkingHaveSameStruct in Hsame_struct; rewrite Hsame_struct in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m'); specialize (Hspec p x Hin_pre_pl Hin_m') as Hpre_le.
      (* Applies check_pre_complete, then the induction hypothesis. *)
      specialize (check_pre_complete
                    spn marking p t x
                    Hwell_def_spn Hsame_struct Hin_m' Hpre_le) as Hcheck_pre.
      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_pre; inversion Hcheck_pre.
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
      intros Hwell_def_spn Hsame_struct Hin_lneigh Hfun p n Hin_m.
    assert (Hincl_refl : incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t))
      by apply incl_refl.
    (* Proof in two stages. *)
    assert (Hvee_in_pre_pl := classic (In p (pre_pl neighbours_of_t))).
    inversion Hvee_in_pre_pl as [Hin_pre_pl | Hnotin_pre_pl]; clear Hvee_in_pre_pl.
    (* First stage, p ∈ pre_places, then we apply map_check_pre_aux_correct. *)
    - apply (map_check_pre_aux_correct
               spn marking (pre_pl neighbours_of_t) t true neighbours_of_t
               Hwell_def_spn Hsame_struct Hin_lneigh Hincl_refl Hfun p n
               Hin_pre_pl Hin_m). 
    (* Second stage, p ∉ pre_places, then (pre spn t p) = 0 *)
    - explode_well_defined_spn.
      unfold AreWellDefinedPreEdges in Hwell_def_pre.
      specialize (Hwell_def_pre t neighbours_of_t p Hin_lneigh)
        as Hw_pre.
      apply proj2 in Hw_pre.
      specialize (Hw_pre Hnotin_pre_pl) as Hw_pre; rewrite Hw_pre; apply Peano.le_0_n.
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
      intros Hwell_def_spn Hsame_struct Hin_lneigh Hspec.
    (* Hypothesis : incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t) 
       for map_check_pre_aux_complete. *)
    assert (incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t)) by apply incl_refl.
    (* Apply map_check_pre_aux_complete. *)
    apply map_check_pre_aux_complete with (neighbours_of_t := neighbours_of_t).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - intros p n Hin_pre_pl Hin_m; apply (Hspec p n Hin_m).
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
      intros n Hwell_def_spn Hsame_struct Hin_m Hfun.
    (* General case, all went well. *)
    - apply get_m_correct in e.
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_spn.
      unfold MarkingHaveSameStruct in Hsame_struct.
      unfold NoUnmarkedPlace in Hunm_place.
      unfold NoDupPlaces in Hnodup_places.
      rewrite Hsame_struct in Hunm_place; rewrite Hunm_place in Hnodup_places.
      assert (Heq_pp : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).
      generalize (nodup_same_pair
                    marking Hnodup_places (p, n) (p, nboftokens)
                    Hin_m e Heq_pp) as Heq_nnb; intro.
      injection Heq_nnb as Heq_nnb.
      rewrite <- Heq_nnb in Hfun; injection Hfun as Hfun.
      apply (leb_complete (test spn t p) n Hfun).
    - inversion Hfun.
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
    intros spn marking p t n Hwell_def_spn Hsame_struct Hin_m Hspec.
    unfold check_test.
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_m_complete. *)
    explode_well_defined_spn.
    unfold NoDupPlaces in Hnodup_places.
    unfold MarkingHaveSameStruct in Hsame_struct.
    unfold NoUnmarkedPlace in Hunm_place.
    rewrite Hunm_place in Hnodup_places; rewrite Hsame_struct in Hnodup_places.
    specialize (get_m_complete marking p n Hnodup_places Hin_m) as Hget_m.
    rewrite Hget_m.
    apply leb_correct in Hspec; rewrite Hspec; reflexivity.
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
      intros neigh_of_t Hwell_def_spn Hsame_struct Hin_lneigh Hincl_test_pl
             Hfun p' n Hin_test_pl Hin_m.
    - inversion Hin_test_pl.
    - inversion Hin_test_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_test_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_test_correct
                 spn marking p' t n
                 Hwell_def_spn Hsame_struct Hin_m e0).
      + apply incl_cons_inv in Hincl_test_pl.
        apply (IHo neigh_of_t
                   Hwell_def_spn Hsame_struct Hin_lneigh Hincl_test_pl
                   Hfun p' n Hin_p'_tail Hin_m).
    - inversion Hfun.
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
      intros neigh_of_t Hwell_def_spn Hsame_struct Hin_lneigh
             Hincl_test_pl Hspec.
    - reflexivity.
    - (* Builds ∃ x, (p, x) ∈ marking to apply check_test_complete. *)
      assert (Hin_test_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_test_pl p Hin_test_pl) as Hin_test_pl_t.
      assert (Hin_flat : In p (flatten_neighbours neigh_of_t))
        by (unfold flatten_neighbours;
            apply in_or_app; right;
            apply in_or_app; left; assumption).
      specialize (in_neigh_in_flatten
                    spn t neigh_of_t p
                    Hwell_def_spn Hin_lneigh Hin_flat) as Hin_flat_lneigh.
      explode_well_defined_spn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      unfold NoUnmarkedPlace in Hunm_place; rewrite Hunm_place in Hin_flat_lneigh.
      unfold MarkingHaveSameStruct in Hsame_struct; rewrite Hsame_struct in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m'); specialize (Hspec p x Hin_test_pl Hin_m') as Htest_le.
      (* Applies check_test_complete, then the induction hypothesis. *)
      specialize (check_test_complete
                    spn marking p t x
                    Hwell_def_spn Hsame_struct Hin_m' Htest_le) as Hcheck_test.
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_test in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_test_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail -> In (p, n) marking -> test spn t p <= n)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo neigh_of_t Hwell_def_spn Hsame_struct Hin_lneigh Hincl_test_pl Hspec').
    (* Deduces hypotheses necessary to apply check_test_complete. *)
    - (* Builds ∃ x, (p, x) ∈ marking to apply check_test_complete. *)
      assert (Hin_test_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_test_pl p Hin_test_pl) as Hin_test_pl_t.
      assert (Hin_flat : In p (flatten_neighbours neigh_of_t))
        by (unfold flatten_neighbours;
            apply in_or_app; right;
            apply in_or_app; left; assumption).
      specialize (in_neigh_in_flatten
                    spn t neigh_of_t p
                    Hwell_def_spn Hin_lneigh Hin_flat) as Hin_flat_lneigh.
      explode_well_defined_spn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      unfold NoUnmarkedPlace in Hunm_place; rewrite Hunm_place in Hin_flat_lneigh.
      unfold MarkingHaveSameStruct in Hsame_struct; rewrite Hsame_struct in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m'); specialize (Hspec p x Hin_test_pl Hin_m') as Htest_le.
      (* Applies check_test_complete, then the induction hypothesis. *)
      specialize (check_test_complete
                    spn marking p t x
                    Hwell_def_spn Hsame_struct Hin_m' Htest_le) as Hcheck_test.
      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_test; inversion Hcheck_test.
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
      intros Hwell_def_spn Hsame_struct Hin_lneigh Hfun p n Hin_m.
    assert (Hincl_refl : incl (test_pl neighbours_of_t) (test_pl neighbours_of_t))
      by apply incl_refl.
    (* Proof in two stages. *)
    assert (Hvee_in_test_pl := classic (In p (test_pl neighbours_of_t))).
    inversion Hvee_in_test_pl as [Hin_test_pl | Hnotin_test_pl]; clear Hvee_in_test_pl.
    (* First stage, p ∈ test_places, then we apply map_check_test_aux_correct. *)
    - apply (map_check_test_aux_correct
               spn marking (test_pl neighbours_of_t) t true neighbours_of_t
               Hwell_def_spn Hsame_struct Hin_lneigh Hincl_refl Hfun p n
               Hin_test_pl Hin_m). 
    (* Second stage, p ∉ test_places, then (test spn t p) = 0 *)
    - explode_well_defined_spn.
      unfold AreWellDefinedTestEdges in Hwell_def_test.
      specialize (Hwell_def_test t neighbours_of_t p Hin_lneigh)
        as Hw_test.
      apply proj2 in Hw_test.
      specialize (Hw_test Hnotin_test_pl) as Hw_test; rewrite Hw_test; apply Peano.le_0_n.
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
    functional induction (map_check_test spn marking (test_pl neighbours_of_t) t)
               using map_check_test_ind;
      intros Hwell_def_spn Hsame_struct Hin_lneigh Hspec.
    (* Hypothesis : incl (test_pl neighbours_of_t) (test_pl neighbours_of_t) 
       for map_check_test_aux_complete. *)
    assert (incl (test_pl neighbours_of_t) (test_pl neighbours_of_t)) by apply incl_refl.
    (* Apply map_check_test_aux_complete. *)
    apply map_check_test_aux_complete with (neighbours_of_t := neighbours_of_t).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - intros p n Hin_test_pl Hin_m; apply (Hspec p n Hin_m).
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
      intros n Hwell_def_spn Hsame_struct Hin_m Hfun.
    (* GENERAL CASE, all went well. *)
    - apply get_m_correct in e.
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_spn.
      unfold MarkingHaveSameStruct in Hsame_struct.
      unfold NoUnmarkedPlace in Hunm_place.
      unfold NoDupPlaces in Hnodup_places.
      rewrite Hsame_struct in Hunm_place; rewrite Hunm_place in Hnodup_places.
      assert (Heq_pair : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).
      (* Determines n = nboftokens *)
      specialize (nodup_same_pair
                    marking Hnodup_places (p, n) (p, nboftokens)
                    Hin_m e Heq_pair) as Heq_pair'.
      injection Heq_pair' as Heq_pair'.
      rewrite <- Heq_pair' in Hfun; injection Hfun as Hfun.
      apply orb_prop in Hfun.
      (* First case: n < (inhib spn t p), second case: (inhib spn t p) = 0 *)
      inversion Hfun as [Hinhib_lt | Hinhib_eq_0].
      + left; apply Nat.ltb_lt; assumption.
      + right; apply Nat.eqb_eq; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
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
    intros spn marking p t n Hwell_def_spn  Hsame_struct Hin_m Hspec.
    unfold check_inhib.
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_m_complete. *)
    explode_well_defined_spn.
    unfold NoDupPlaces in Hnodup_places.
    unfold MarkingHaveSameStruct in Hsame_struct.
    unfold NoUnmarkedPlace in Hunm_place.
    rewrite Hunm_place in Hnodup_places; rewrite Hsame_struct in Hnodup_places.
    (* Applies get_m_complte *)
    specialize (get_m_complete marking p n Hnodup_places Hin_m) as Hget_m.
    rewrite Hget_m; inversion Hspec as [Hinhib_lt | Hinhib_eq_0].
    - apply Nat.ltb_lt in Hinhib_lt; rewrite Hinhib_lt.
      rewrite orb_true_l; reflexivity.
    - apply Nat.eqb_eq in Hinhib_eq_0; rewrite Hinhib_eq_0.
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
      intros neigh_of_t Hwell_def_spn Hsame_struct Hin_lneigh Hincl_inhib_pl Hfun
             p' n Hin_inhib_pl Hin_m.
    (* BASE CASE *)
    - inversion Hin_inhib_pl.
    (* GENERAL CASE *)
    - inversion Hin_inhib_pl as [Heq_pp' | Hin_inhib_tl]; clear Hin_inhib_pl.
      + apply map_check_inhib_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_inhib_correct
                 spn marking p' t n
                 Hwell_def_spn Hsame_struct Hin_m e0).
      + apply IHo with (neighbours_of_t := neigh_of_t);
          (assumption ||
           apply incl_cons_inv in Hincl_inhib_pl; assumption).
    (* ERROR CASE *)
    - inversion Hfun.
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
    intros spn marking inhib_places t;
      functional induction (map_check_inhib_aux spn marking inhib_places t true)
                 using map_check_inhib_aux_ind;
      intros neigh_of_t Hwell_def_spn Hsame_struct Hin_lneigh Hincl_inhib_pl Hspec.
    (* BASE CASE *)
    - reflexivity.
    (* GENERAL CASE *)
    - (* Deduces hypotheses necessary to apply check_inhib_complete. *)
      assert (Hin_inhib_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_inhib_pl p Hin_inhib_pl) as Hin_inhib_pl_t.
      (* p ∈ (flatten_neighbours neighbours_of_t) *)
      assert (Hin_flat : In p (flatten_neighbours neigh_of_t))
        by (unfold flatten_neighbours;
            do 2 (apply in_or_app; right);
            apply in_or_app; left; assumption).
      (* p ∈ (flatten_neighbours neighbours_of_t) ⇒ p ∈ (flatten spn.(lneighbours)) *)
      specialize (in_neigh_in_flatten spn t neigh_of_t p Hwell_def_spn Hin_lneigh Hin_flat)
        as Hin_flat_spn.
      explode_well_defined_spn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_spn.
      unfold NoUnmarkedPlace in Hunm_place; rewrite Hunm_place in Hin_flat_spn.
      unfold MarkingHaveSameStruct in Hsame_struct; rewrite Hsame_struct in Hin_flat_spn.
      (* ∃ n, (p, n) ∈ marking *)
      specialize (in_fst_split_in_pair p marking Hin_flat_spn) as Hex_in_m;
        inversion Hex_in_m as (x & Hin_m).
      (* Applies the completeness hypothesis. *)
      specialize (Hspec p x Hin_inhib_pl Hin_m) as Hinhib_spec.
      (* Applies check_inhib_complete, then the induction hypothesis. *)
      specialize (check_inhib_complete
                    spn marking p t x
                    Hwell_def_spn Hsame_struct Hin_m Hinhib_spec) as Hcheck_inhib.
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_inhib in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      apply IHo with (neighbours_of_t := neigh_of_t).
      + assumption.
      + assumption.
      + assumption.
      + unfold incl; intros a Hin_tl.
        unfold incl in Hincl_inhib_pl.
        apply in_cons with (a := p) in Hin_tl.
        apply (Hincl_inhib_pl a Hin_tl).
      + intros p0 n Hin_tl Hin_m'; apply in_cons with (a := p) in Hin_tl.
        apply (Hspec p0 n Hin_tl Hin_m').
    (* Deduces hypotheses necessary to apply check_inhib_complete. *)
    - (* Deduces hypotheses necessary to apply check_inhib_complete. *)
      assert (Hin_inhib_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_inhib_pl p Hin_inhib_pl) as Hin_inhib_pl_t.
      (* p ∈ (flatten_neighbours neighbours_of_t) *)
      assert (Hin_flat : In p (flatten_neighbours neigh_of_t))
        by (unfold flatten_neighbours;
            do 2 (apply in_or_app; right);
            apply in_or_app; left; assumption).
      (* p ∈ (flatten_neighbours neighbours_of_t) ⇒ p ∈ (flatten spn.(lneighbours)) *)
      specialize (in_neigh_in_flatten spn t neigh_of_t p Hwell_def_spn Hin_lneigh Hin_flat)
        as Hin_flat_spn.
      explode_well_defined_spn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_spn.
      unfold NoUnmarkedPlace in Hunm_place; rewrite Hunm_place in Hin_flat_spn.
      unfold MarkingHaveSameStruct in Hsame_struct; rewrite Hsame_struct in Hin_flat_spn.
      (* ∃ n, (p, n) ∈ marking *)
      specialize (in_fst_split_in_pair p marking Hin_flat_spn) as Hex_in_m;
        inversion Hex_in_m as (x & Hin_m).
      (* Applies the completeness hypothesis. *)
      specialize (Hspec p x Hin_inhib_pl Hin_m) as Hinhib_spec.
      (* Applies check_inhib_complete, then the induction hypothesis. *)
      specialize (check_inhib_complete
                    spn marking p t x
                    Hwell_def_spn Hsame_struct Hin_m Hinhib_spec) as Hcheck_inhib.
      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_inhib; inversion Hcheck_inhib.
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
    intros spn marking t neigh_of_t.
    functional induction (map_check_inhib spn marking (inhib_pl neigh_of_t) t)
               using map_check_inhib_ind;
      intros Hwell_def_spn Hsame_struct Hin_lneigh Hfun p n Hin_m.
    assert (Hincl_refl : incl (inhib_pl neigh_of_t) (inhib_pl neigh_of_t)) by (apply incl_refl).
    (* Proof in two stages. *)
    assert (Hvee_in_inhib_pl := classic (In p (inhib_pl neigh_of_t))).
    inversion Hvee_in_inhib_pl as [Hin_inhib | Hnotin_inhib]; clear Hvee_in_inhib_pl.
    (* First stage, p ∈ inhib_places, then we apply map_check_inhib_aux_correct. *)
    - apply (map_check_inhib_aux_correct
               spn marking (inhib_pl neigh_of_t) t true neigh_of_t
               Hwell_def_spn Hsame_struct Hin_lneigh Hincl_refl Hfun
               p n Hin_inhib Hin_m).
    (* Second stage, p ∉ inhib_places, then (inhib spn t p) = 0 *)
    - explode_well_defined_spn.
      unfold AreWellDefinedInhibEdges in Hwell_def_inhib.
      generalize (Hwell_def_inhib t neigh_of_t p Hin_lneigh) as Hw_inhib; intro.
      apply proj2 in Hw_inhib.
      generalize (Hw_inhib Hnotin_inhib); intro; right; assumption.
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
    intros spn marking t neigh_of_t Hwell_def_spn Hsame_struct Hin_lneigh Hspec.
    unfold map_check_inhib.
    assert (Hincl_refl : incl (inhib_pl neigh_of_t) (inhib_pl neigh_of_t)) by apply incl_refl.
    (* Apply map_check_inhib_aux_complete. *)
    apply map_check_inhib_aux_complete with (neighbours_of_t := neigh_of_t).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - intros p n Hin_inhib_pl Hin_m; apply (Hspec p n Hin_m).
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
                                      Hsame_marking_state_spn Hin_lneigh Hfun) as His_sens; intro.
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
