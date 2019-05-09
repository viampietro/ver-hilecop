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

  (* No error lemma for get_m. *)

  Lemma get_m_no_error :
    forall (marking : list (Place * nat)) (p : Place),
      In p (fst (split marking)) ->
      exists n : nat, get_m marking p = Some n.
  Proof.
    intros marking p Hin_fs.
    induction marking.
    - simpl in Hin_fs; inversion Hin_fs.
    - dependent induction a; simpl; case_eq (p =? a).
      + intro; exists b; reflexivity.
      + intro Heq_false; rewrite fst_split_cons_app in Hin_fs.
        simpl in Hin_fs.
        inversion_clear Hin_fs as [Heq_ap | Hin_p_tl].
        -- symmetry in Heq_ap; apply beq_nat_false in Heq_false; contradiction.
        -- apply (IHmarking Hin_p_tl).
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

  (* No error lemma for check_pre. *)

  Lemma check_pre_no_error :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans),
      In p (fst (split marking)) ->
      exists b : bool,
        check_pre spn marking p t = Some b.
  Proof.
    intros spn marking p t Hin_fs.
    unfold check_pre.
    specialize (get_m_no_error marking p Hin_fs) as Hget_m_ex.
    inversion_clear Hget_m_ex as (nboftokens & Hget_m).
    rewrite Hget_m; exists (pre spn t p <=? nboftokens).
    reflexivity.
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

  (** No error lemma for map_check_pre_aux. *)

  Lemma map_check_pre_aux_no_error :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (check_result : bool),
      incl pre_places (fst (split marking)) ->
      exists b : bool,
        map_check_pre_aux spn marking pre_places t check_result = Some b.
  Proof.
    intros spn marking t; induction pre_places; intros check_result Hincl_prepl.
    (* BASE CASE *)
    - simpl; exists check_result; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_a_fs: In a (a :: pre_places)) by apply in_eq.
      apply (Hincl_prepl a) in Hin_a_fs.
      specialize (check_pre_no_error spn marking a t Hin_a_fs) as Hcheck_pre_ex.
      inversion_clear Hcheck_pre_ex as (b & Hcheck_pre).
      rewrite Hcheck_pre.
      apply incl_cons_inv in Hincl_prepl.
      apply (IHpre_places (b && check_result) Hincl_prepl).
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

  (** No error lemma for map_check_pre. *)

  Lemma map_check_pre_no_error :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place),
      incl pre_places (fst (split marking)) ->
      exists b : bool,
        map_check_pre spn marking pre_places t = Some b.
  Proof.
    intros spn marking t pre_places Hincl_prepl.
    unfold map_check_pre.
    apply (map_check_pre_aux_no_error spn marking t pre_places true Hincl_prepl).
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

  (* No error lemma for check_test. *)

  Lemma check_test_no_error :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans),
      In p (fst (split marking)) ->
      exists b : bool,
        check_test spn marking p t = Some b.
  Proof.
    intros spn marking p t Hin_fs.
    unfold check_test.
    specialize (get_m_no_error marking p Hin_fs) as Hget_m_ex.
    inversion_clear Hget_m_ex as (nboftokens & Hget_m).
    rewrite Hget_m; exists (test spn t p <=? nboftokens).
    reflexivity.
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

  (** No error lemma for map_check_test_aux. *)

  Lemma map_check_test_aux_no_error :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (test_places : list Place)
           (check_result : bool),
      incl test_places (fst (split marking)) ->
      exists b : bool,
        map_check_test_aux spn marking test_places t check_result = Some b.
  Proof.
    intros spn marking t; induction test_places; intros check_result Hincl_testpl.
    (* BASE CASE *)
    - simpl; exists check_result; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_a_fs: In a (a :: test_places)) by apply in_eq.
      apply (Hincl_testpl a) in Hin_a_fs.
      specialize (check_test_no_error spn marking a t Hin_a_fs) as Hcheck_test_ex.
      inversion_clear Hcheck_test_ex as (b & Hcheck_test).
      rewrite Hcheck_test.
      apply incl_cons_inv in Hincl_testpl.
      apply (IHtest_places (b && check_result) Hincl_testpl).
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

  (** No error lemma for map_check_test. *)

  Lemma map_check_test_no_error :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (test_places : list Place),
      incl test_places (fst (split marking)) ->
      exists b : bool,
        map_check_test spn marking test_places t = Some b.
  Proof.
    intros spn marking t test_places Hincl_testpl.
    unfold map_check_test.
    apply (map_check_test_aux_no_error spn marking t test_places true Hincl_testpl).
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

  (* No error lemma for check_inhib. *)

  Lemma check_inhib_no_error :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans),
      In p (fst (split marking)) ->
      exists b : bool,
        check_inhib spn marking p t = Some b.
  Proof.
    intros spn marking p t Hin_fs.
    unfold check_inhib.
    specialize (get_m_no_error marking p Hin_fs) as Hget_m_ex.
    inversion_clear Hget_m_ex as (nboftokens & Hget_m).
    rewrite Hget_m; exists ((nboftokens <? inhib spn t p) || (inhib spn t p =? 0)).
    reflexivity.
  Qed.
  
  (** No error lemma for map_check_inhib_aux. *)

  Lemma map_check_inhib_aux_no_error :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (inhib_places : list Place)
           (check_result : bool),
      incl inhib_places (fst (split marking)) ->
      exists b : bool,
        map_check_inhib_aux spn marking inhib_places t check_result = Some b.
  Proof.
    intros spn marking t; induction inhib_places; intros check_result Hincl_inhibpl.
    (* BASE CASE *)
    - simpl; exists check_result; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_a_fs: In a (a :: inhib_places)) by apply in_eq.
      apply (Hincl_inhibpl a) in Hin_a_fs.
      specialize (check_inhib_no_error spn marking a t Hin_a_fs) as Hcheck_inhib_ex.
      inversion_clear Hcheck_inhib_ex as (b & Hcheck_inhib).
      rewrite Hcheck_inhib.
      apply incl_cons_inv in Hincl_inhibpl.
      apply (IHinhib_places (b && check_result) Hincl_inhibpl).
  Qed.
  
  (** No error lemma for map_check_inhib. *)

  Lemma map_check_inhib_no_error :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (inhib_places : list Place),
      incl inhib_places (fst (split marking)) ->
      exists b : bool,
        map_check_inhib spn marking inhib_places t = Some b.
  Proof.
    intros spn marking t inhib_places Hincl_inhibpl.
    unfold map_check_inhib.
    apply (map_check_inhib_aux_no_error spn marking t inhib_places true Hincl_inhibpl).
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

  (** No error lemma for is_sensitized. *)

  Theorem is_sensitized_no_error :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      incl (flatten_neighbours neighbours_of_t) (fst (split marking)) ->
      exists b : bool,
        is_sensitized spn marking neighbours_of_t t = Some b.
  Proof.
    intros spn marking t neighbours_of_t Hincl_flat.
    unfold is_sensitized.

    (* Prepares hypotheses to apply no error lemmas. *)
    assert (Hincl_prepl : incl (pre_pl neighbours_of_t) (fst (split marking))).
    {
      intros p Hin_prepl.
      apply or_introl
        with (B := In p ((test_pl neighbours_of_t)
                           ++ (inhib_pl neighbours_of_t)
                           ++ (post_pl neighbours_of_t)))
        in Hin_prepl.
      apply in_or_app in Hin_prepl.
      apply (Hincl_flat p Hin_prepl).      
    }

    assert (Hincl_testpl : incl (test_pl neighbours_of_t) (fst (split marking))).
    {
      intros p Hin_testpl.
      apply or_intror
        with (A := In p (pre_pl neighbours_of_t))
        in Hin_testpl.
      apply in_or_app in Hin_testpl.
      apply or_introl
        with (B := In p ((inhib_pl neighbours_of_t) ++ (post_pl neighbours_of_t)))
        in Hin_testpl.
      apply in_or_app in Hin_testpl.
      rewrite <- app_assoc in Hin_testpl.
      apply (Hincl_flat p Hin_testpl).      
    }

    assert (Hincl_inhibpl : incl (inhib_pl neighbours_of_t) (fst (split marking))).
    {
      intros p Hin_inhibpl.
      apply or_intror
        with (A := In p ((pre_pl neighbours_of_t) ++ (test_pl neighbours_of_t)))
        in Hin_inhibpl.
      apply in_or_app in Hin_inhibpl.
      apply or_introl
        with (B := In p (post_pl neighbours_of_t))
        in Hin_inhibpl.
      apply in_or_app in Hin_inhibpl.
      do 2 (rewrite <- app_assoc in Hin_inhibpl).
      apply (Hincl_flat p Hin_inhibpl).      
    }

    specialize (map_check_pre_no_error spn marking t (pre_pl neighbours_of_t) Hincl_prepl)
      as Hmap_check_pre_ex.

    specialize (map_check_test_no_error spn marking t (test_pl neighbours_of_t) Hincl_testpl)
      as Hmap_check_test_ex.

    specialize (map_check_inhib_no_error spn marking t (inhib_pl neighbours_of_t) Hincl_inhibpl)
      as Hmap_check_inhib_ex.

    inversion_clear Hmap_check_pre_ex as (check_pre_result & Hmap_check_pre).
    inversion_clear Hmap_check_test_ex as (check_test_result & Hmap_check_test).
    inversion_clear Hmap_check_inhib_ex as (check_inhib_result & Hmap_check_inhib).

    rewrite Hmap_check_pre, Hmap_check_test, Hmap_check_inhib.

    exists (check_pre_result && check_test_result && check_inhib_result); reflexivity.

  Qed.

  (** Conjunction of correction and completeness for is_sensitized. *)

  Theorem is_sensitized_iff :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      is_sensitized spn marking neighbours_of_t t = Some true <->
      IsSensitized spn marking t.
  Proof.
    intros spn marking t neighbours_of_t Hwell_def_spn Hsame_struct Hin_lneigh.
    split;
      [ intro Hfun;
        apply (is_sensitized_correct spn marking t neighbours_of_t
                                     Hwell_def_spn Hsame_struct
                                     Hin_lneigh Hfun)
      | intro Hspec;
        apply (is_sensitized_complete spn marking t neighbours_of_t
                                      Hwell_def_spn Hsame_struct
                                      Hin_lneigh Hspec) ].
  Qed.

  (** Conjunction of correction and completeness for ~is_sensitized. *)

  Theorem not_is_sensitized_iff :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      is_sensitized spn marking neighbours_of_t t = Some false <->
      ~IsSensitized spn marking t.
  Proof.
    intros spn marking t neighbours_of_t Hwell_def_spn Hsame_struct Hin_lneigh.
    split.
    
    - intros Hfun Hspec;
        rewrite <- (is_sensitized_iff spn marking t neighbours_of_t
                                      Hwell_def_spn Hsame_struct Hin_lneigh)
        in Hspec.
      rewrite Hfun in Hspec; inversion Hspec.

    - intro Hspec; case_eq (is_sensitized spn marking neighbours_of_t t).
      + dependent induction b.
        -- intros His_sens_fun.
           rewrite <- (is_sensitized_iff spn marking t neighbours_of_t
                                         Hwell_def_spn Hsame_struct Hin_lneigh)
             in Hspec.
           contradiction.
        -- intros; reflexivity.
      + intros Hsens_fun.
        
        (* Specializes is_sensitized_no_error to solve the subgoal. *)
        explode_well_defined_spn.
        unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
        assert (Hincl_flat_lneigh : incl (flatten_neighbours neighbours_of_t)
                                         (flatten_lneighbours (lneighbours spn))).
        {
          intros p Hin_p_flat;
            apply (in_neigh_in_flatten spn t neighbours_of_t p
                                       Hwell_def_spn Hin_lneigh Hin_p_flat).
        }
        specialize (incl_tran Hincl_flat_lneigh Hunk_pl_neigh) as Hincl_fl_m.
        rewrite Hunm_place in Hincl_fl_m.
        rewrite Hsame_struct in Hincl_fl_m.

        specialize (is_sensitized_no_error spn marking t neighbours_of_t Hincl_fl_m)
          as Hsens_ex.
        inversion_clear Hsens_ex as (b & Hsens).
        rewrite Hsens_fun in Hsens; inversion Hsens.
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
    explode_well_defined_spn_state Hwell_def_state.
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
  
  (** No error lemma for is_sensitized. *)

  Theorem spn_is_firable_no_error :
    forall (spn : Spn)
           (s : SpnState)
           (t : Trans)
           (neigh_of_t : Neighbours),
      incl (flatten_neighbours neigh_of_t) (fst (split (marking s))) ->
      exists b : bool,
        spn_is_firable spn s neigh_of_t t = Some b.
  Proof.
    intros spn s t neigh_of_t Hincl_ms.
    unfold spn_is_firable.
    apply (is_sensitized_no_error spn (marking s) t neigh_of_t Hincl_ms).
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

  (** Correctness and completeness conjunction for ~spn_is_firable. *)
  
  Theorem not_spn_is_firable_iff :
    forall (spn : Spn)
           (state : SpnState)
           (neigh_of_t : Neighbours)
           (t : Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn state ->
      In (t, neigh_of_t) spn.(lneighbours) ->
      spn_is_firable spn state neigh_of_t t = Some false <-> ~SpnIsFirable spn state t.
  Proof.
    intros spn s neigh_of_t t Hwell_def_spn Hwell_def_s Hin_lneigh; split.
    - intros Hfirable_fun Hfirable_spec.
      rewrite <- (spn_is_firable_iff
                    spn s neigh_of_t t Hwell_def_spn Hwell_def_s Hin_lneigh) in Hfirable_spec.
      rewrite Hfirable_fun in Hfirable_spec.
      inversion_clear Hfirable_spec.
    - case_eq (spn_is_firable spn s neigh_of_t t).
      + dependent induction b.
        -- intros Hfirable_fun Hfirable_spec.
           rewrite <- (spn_is_firable_iff spn s neigh_of_t t Hwell_def_spn Hwell_def_s Hin_lneigh)
             in Hfirable_spec.
           contradiction.
        -- intros; reflexivity.
      + intros Hfirable_fun Hfirable_spec.
        
        (* Specializes spn_is_firable_no_error to solve the subgoal. *)
        explode_well_defined_spn.
        unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
        assert (Hincl_flat_lneigh : incl (flatten_neighbours neigh_of_t)
                                         (flatten_lneighbours (lneighbours spn))).
        {
          intros p Hin_p_flat;
            apply (in_neigh_in_flatten spn t neigh_of_t p Hwell_def_spn Hin_lneigh Hin_p_flat).
        }
        specialize (incl_tran Hincl_flat_lneigh Hunk_pl_neigh) as Hincl_fl_m.
        rewrite Hunm_place in Hincl_fl_m.
        explode_well_defined_spn_state Hwell_def_s.
        rewrite Hsame_marking_state_spn in Hincl_fl_m.
        clear Hsame_marking_state_spn Hincl_state_fired_transs Hnodup_state_fired.
        specialize (spn_is_firable_no_error spn s t neigh_of_t Hincl_fl_m) as Hfirable_ex.
        inversion_clear Hfirable_ex as (b & Hfirable).
        rewrite Hfirable in Hfirable_fun; inversion Hfirable_fun.
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

  (* No error lemma for get_neighbours. *)

  Lemma get_neighbours_no_error :
    forall (lneighbours : list (Trans * Neighbours))
           (t : Trans),
      In t (fst (split lneighbours)) ->
      exists neigh_of_t : Neighbours,
        get_neighbours lneighbours t = Some neigh_of_t.
  Proof.
    intros lneighbours t Hin_fs.
    induction lneighbours.
    - simpl in Hin_fs; inversion Hin_fs.
    - dependent induction a; simpl; case_eq (a =? t).
      + intro; exists b; reflexivity.
      + intro Heq_false; rewrite fst_split_cons_app in Hin_fs.
        simpl in Hin_fs.
        inversion_clear Hin_fs as [Heq_at | Hin_t_tl].
        -- apply beq_nat_false in Heq_false; contradiction.
        -- apply (IHlneighbours Hin_t_tl).
  Qed.
  
End GetNeighbours.

Section ReplaceOcc.

  (** If occ ∈ l, then repl ∈ l' *)

  Lemma replace_occ_if_in {A : Type} :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (occ : A)
           (repl : A)
           (l : list A)
           (l' : list A),
      replace_occ eq_dec occ repl l = l' ->
      In occ l ->
      In repl l'.
  Proof.
    intros eq_dec occ repl l;
      functional induction (replace_occ eq_dec occ repl l) using replace_occ_ind;
      intros l' Hfun Hin_l.
    (* BASE CASE *)
    - inversion Hin_l.
    (* CASE occ = hd l *)
    - rewrite <- Hfun; apply in_eq.
    (* CASE occ <> hd l *)
    - inversion Hin_l.
      + contradiction.
      + induction l'.
        -- inversion Hfun.
        -- injection Hfun as Heq_xa Heq_fun.
           apply in_cons.
           apply (IHl0 l' Heq_fun H).
  Qed.

  Lemma replace_occ_if_not_in {A : Type} :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (occ : A)
           (repl : A)
           (l : list A)
           (l' : list A),
      replace_occ eq_dec occ repl l = l' ->
      In repl l' ->
      ~In repl l ->
      In occ l.
  Proof.
    intros eq_dec occ repl l;
      functional induction (replace_occ eq_dec occ repl l) using replace_occ_ind;
      intros l' Hfun Hin_l' Hnot_in_l.
    (* BASE CASE *)
    - rewrite <- Hfun in Hin_l'; inversion  Hin_l'.
    (* CASE occ = hd l *)
    - apply in_eq.
    (* CASE occ <> hd l *)
    - induction l'.
      + inversion Hin_l'.
      + inversion Hin_l' as [Heq_repla | Hin_repl_l'].
        -- injection Hfun as Heq_xa Heq_fun.
           apply not_in_cons in Hnot_in_l; apply proj1 in Hnot_in_l.
           rewrite Heq_xa in Hnot_in_l; symmetry in Heq_repla; contradiction.
        -- injection Hfun as Heq_xa Heq_fun.
           apply not_in_cons in Hnot_in_l; apply proj2 in Hnot_in_l.
           apply in_cons.
           apply (IHl0 l' Heq_fun Hin_repl_l' Hnot_in_l).
  Qed.

  (* Lemma : Proves that replace_occ preserves structure
   *         of a marking m passed as argument when 
   *         (fst occ) = (fst repl).
   *)
  Lemma replace_occ_same_struct :
    forall (m : list (Place * nat))
           (p : Place)
           (n n' : nat),
      MarkingHaveSameStruct (replace_occ prodnat_eq_dec (p, n) (p, n') m) m.
  Proof.
    do 4 intro.
    unfold MarkingHaveSameStruct.
    functional induction (replace_occ prodnat_eq_dec (p, n) (p, n') m)
               using replace_occ_ind;
      intros.
    (* Base case. *)
    - auto.
    (* Case (p,n) is hd of list. *)
    - intros.
      rewrite fst_split_cons_app.
      symmetry.
      rewrite fst_split_cons_app.
      rewrite IHl.
      simpl.
      auto.
    (* Case (p, n) not hd of list. *)
    - rewrite fst_split_cons_app.
      symmetry.
      rewrite fst_split_cons_app.
      rewrite IHl.
      auto.
  Qed.

  Lemma replace_occ_in_if_diff {A : Type} :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (occ : A)
           (repl : A)
           (l : list A)
           (l' : list A),
      replace_occ eq_dec occ repl l = l' ->
      forall a : A, a <> occ -> a <> repl -> In a l <-> In a l'.
  Proof.
    intros eq_dec occ repl l;
      functional induction (replace_occ eq_dec occ repl l)
                 using replace_occ_ind;
      intros l' Hfun a Hdiff_occ Hdiff_repl.
    (* BASE CASE *)
    - rewrite <- Hfun; reflexivity.
    (* CASE occ = hd l *)
    - split.
      + intro Hin_a_l.
        inversion Hin_a_l as [Heq_aocc | Hin_a_tl].
        -- symmetry in Heq_aocc; contradiction.
        -- induction l'.
           ++ inversion Hfun.
           ++ injection Hfun as Heq_repla Heq_fun.
              apply in_cons.
              specialize (IHl0 l' Heq_fun a Hdiff_occ) as Hequiv.
              rewrite <- Hequiv; assumption.
      + intro Hin_a_l'; induction l'.
        -- inversion Hfun.
        -- injection Hfun as Heq_repla Heq_fun.
           apply in_cons.
           inversion Hin_a_l' as [Heq_aa0 | Hin_a_l''].
           ++ rewrite Heq_aa0 in Heq_repla; symmetry in Heq_repla; contradiction. 
           ++ specialize (IHl0 l' Heq_fun a Hdiff_occ Hdiff_repl) as Hequiv;
                rewrite Hequiv; assumption.
    (* CASE occ <> hd l *)
    - induction l'.
      + inversion Hfun.
      + injection Hfun as Heq_xa0 Heq_fun.
        specialize (IHl0 l' Heq_fun a Hdiff_occ Hdiff_repl) as Hequiv.
        split.
        -- intro Hin_a_l.
           inversion Hin_a_l as [Heq_ax | Hin_a_tl].
           ++ rewrite <- Heq_ax; rewrite Heq_xa0; apply in_eq.
           ++ apply in_cons; rewrite <- Hequiv; assumption.
        -- intro Hin_a_l'.
           inversion Hin_a_l' as [Heq_aa0 | Hin_a_tll'].
           ++ rewrite Heq_xa0; rewrite Heq_aa0; apply in_eq.
           ++ apply in_cons; rewrite Hequiv; assumption.
  Qed.

End ReplaceOcc.

Section ModifyM.
  
  (** Correctness proof for [modify_m]. 
      
      Needed in update_residual_marking_aux_correct. *)
  
  Lemma modify_m_correct :
    forall (marking : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat)
           (final_marking : list (Place * nat)),
      NoDup (fst (split marking)) ->
      modify_m marking p op nboftokens = Some final_marking ->
      forall n : nat, In (p, n) marking -> In (p, op n nboftokens) final_marking.
  Proof.
    intros marking p op nboftokens;
      functional induction (modify_m marking p op nboftokens) using modify_m_ind;
      intros final_marking Hnodup Hfun n' Hin_n'_m.
    (* GENERAL CASE *)
    - injection Hfun as Hfun.
      apply get_m_correct in e.
      specialize (replace_occ_if_in
                    prodnat_eq_dec (p, n) (p, op n nboftokens) marking
                    final_marking Hfun e) as Hin_final.
      assert (Heq_p : fst (p, n) = fst (p, n')) by (simpl; reflexivity).
      specialize (nodup_same_pair marking Hnodup (p, n) (p, n') e Hin_n'_m Heq_p) as Heq_pp.
      injection Heq_pp as Heq_nn'.
      rewrite <- Heq_nn'; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma modify_m_in_if_diff :
    forall (marking : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat)
           (final_marking : list (Place * nat)),
      modify_m marking p op nboftokens = Some final_marking ->
      forall (p' : Place) (n : nat), p <> p' -> In (p', n) marking <-> In (p', n) final_marking.
  Proof.
    intros marking p op nboftokens;
      functional induction (modify_m marking p op nboftokens) using modify_m_ind;
      intros final_marking Hfun p'' n' Hdiff_pp.
    (* GENERAL CASE *)
    - injection Hfun as Hfun.
      apply not_eq_sym in Hdiff_pp.
      specialize (fst_diff_pair_diff p'' p Hdiff_pp n' n) as Hdiff_nn0.
      specialize (fst_diff_pair_diff p'' p Hdiff_pp n' (op n nboftokens)) as Hdiff_nnb.
      specialize (replace_occ_in_if_diff
                    prodnat_eq_dec (p, n) (p, op n nboftokens) marking final_marking
                    Hfun (p'', n') Hdiff_nn0 Hdiff_nnb) as Hequiv.
      assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Proves that modify_m preserves the structure of the marking m
      passed as argument. *)
  
  Lemma modify_m_same_struct :
    forall (m m' : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat),
      modify_m m p op nboftokens = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    do 5 intro.
    functional induction (modify_m m p op nboftokens)
               using modify_m_ind;
      intros.
    - injection H; intros.
      rewrite <- H0.
      unfold MarkingHaveSameStruct; symmetry.
      apply replace_occ_same_struct.
    - inversion H.
  Qed.

  (** No error lemma for modify_m. *)

  Lemma modify_m_no_error :
    forall (m : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat),
      In p (fst (split m)) ->
      exists m' : list (Place * nat),
        modify_m m p op nboftokens = Some m'.
  Proof.
    intros m p op nboftokens Hin_m_fs.
    unfold modify_m.
    specialize (get_m_no_error m p Hin_m_fs) as Hget_m_ex.
    inversion_clear Hget_m_ex as (n & Hget_m).
    rewrite Hget_m.
    exists (replace_occ prodnat_eq_dec (p, n) (p, op n nboftokens) m).
    reflexivity.
  Qed.
  
End ModifyM.

Section UpdateResidualMarking.

  (** Proves that update_residual_marking_aux preserves marking structure. *)
  
  Lemma update_residual_marking_aux_same_struct :
    forall (spn : Spn)
           (residual_marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (final_marking : list (Place * nat)),
      update_residual_marking_aux spn residual_marking t pre_places = Some final_marking ->
      MarkingHaveSameStruct residual_marking final_marking.
    intros spn residual_marking t pre_places;
      functional induction (update_residual_marking_aux spn residual_marking t pre_places)
                 using update_residual_marking_aux_ind;
      intros final_marking Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply modify_m_same_struct in e0.
      apply IHo in Hfun.
      unfold MarkingHaveSameStruct in e0;
        unfold MarkingHaveSameStruct in Hfun;
        rewrite <- e0 in Hfun; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Needed to prove update_marking_aux_correct. *)
  
  Lemma update_residual_marking_aux_not_in_pre_places :
    forall (spn : Spn)
           (residual_marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (final_marking : list (Place * nat)),
      update_residual_marking_aux spn residual_marking t pre_places = Some final_marking ->
      forall (p : Place),
        ~In p pre_places ->
        forall (n : nat), In (p, n) residual_marking <-> In (p, n) final_marking.
  Proof.
    intros spn residual_marking t pre_places;
      functional induction (update_residual_marking_aux spn residual_marking t pre_places)
                 using update_residual_marking_aux_ind;
      intros final_marking Hfun p' Hnot_in_pre n.
    (* BASE CASE *)
    - injection Hfun as Hfun.
      rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply not_in_cons in Hnot_in_pre.
      elim Hnot_in_pre; intros Hdiff_pp' Hnot_in_tl.
      apply not_eq_sym in Hdiff_pp'.
      specialize (modify_m_in_if_diff
                    residual_marking p Nat.sub (pre spn t p) residual_marking'
                    e0 p' n Hdiff_pp') as Hequiv.
      rewrite Hequiv.
      apply (IHo final_marking Hfun p' Hnot_in_tl n).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.
  
  (** Correctness proof for [update_residual_marking_aux].
      Express the structure of the returned [residual_marking'] regarding the structure
      of [residual_marking]. 

      Needed to prove update_residual_marking_correct. *)
  
  Lemma update_residual_marking_aux_correct :
    forall (spn : Spn)
           (residual_marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (neigh_of_t : Neighbours)
           (final_marking : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split residual_marking)) ->
      In (t , neigh_of_t) (lneighbours spn) ->
      NoDup pre_places ->
      incl pre_places (pre_pl neigh_of_t) ->
      update_residual_marking_aux spn residual_marking t pre_places = Some final_marking ->
      forall (p : Place) (n : nat),
        In p pre_places ->
        In (p, n) residual_marking ->
        In (p, n - (pre spn t p)) final_marking.
  Proof.
    intros spn residual_marking t pre_places;
      functional induction (update_residual_marking_aux spn residual_marking t pre_places)
                 using update_residual_marking_aux_ind;
      intros neigh_of_t final_marking Hwell_def_spn Hnodup_m
             Hin_lneigh Hnodup_pre_pl Hincl_pre_pl Hfun p' n Hin_pre_pl Hin_resid.
    (* BASE CASE, pre_places = []. *)
    - inversion Hin_pre_pl.
    (* GENERAL CASE *)
    - inversion Hin_pre_pl as [Heq_pp' | Hin_p'_tail].
      (* First subcase, p = p'. *)
      + rewrite <- Heq_pp' in Hin_pre_pl.
        rewrite <- Heq_pp' in Hin_resid.
        specialize (modify_m_correct
                      residual_marking p Nat.sub (pre spn t p) residual_marking'
                      Hnodup_m e0 n Hin_resid) as Hin_resid'.
        apply NoDup_cons_iff in Hnodup_pre_pl.
        elim Hnodup_pre_pl; intros Hnot_in_tl Hnodup_tl.
        rewrite Heq_pp' in Hnot_in_tl.
        specialize (update_residual_marking_aux_not_in_pre_places
                      spn residual_marking' t tail final_marking
                      Hfun p' Hnot_in_tl (n - pre spn t p)) as Hin_equiv'.
        rewrite Heq_pp' in Hin_resid'.
        rewrite Heq_pp' in Hin_equiv'.
        rewrite Hin_equiv' in Hin_resid'; assumption.
      (* Second subcase, In p' tail, then apply induction hypothesis. *)
      (* But we need to show NoDup (fst (split residual')) first. *)
      + specialize (modify_m_same_struct
                      residual_marking residual_marking' p Nat.sub  (pre spn t p) e0)
          as Hsame_struct.
        unfold MarkingHaveSameStruct in Hsame_struct.
        rewrite Hsame_struct in Hnodup_m.
        (* Builds the other hypotheses, needed to specialize IHo. *)
        apply NoDup_cons_iff in Hnodup_pre_pl;
          elim Hnodup_pre_pl;
          intros Hnot_in_tl Hnodup_tl.
        apply incl_cons_inv in Hincl_pre_pl.        
        (* Then specializes the induction hypothesis. *)
        specialize (IHo neigh_of_t final_marking Hwell_def_spn Hnodup_m
                        Hin_lneigh Hnodup_tl Hincl_pre_pl Hfun
                        p' n Hin_p'_tail) as Himpl.
        specialize (not_in_in_diff p p' tail (conj Hnot_in_tl Hin_p'_tail))
          as Hdiff_pp.
        specialize (modify_m_in_if_diff
                      residual_marking p Nat.sub (pre spn t p)
                      residual_marking' e0 p' n Hdiff_pp) as Hequiv'.
        rewrite <- Hequiv' in Himpl.
        apply (Himpl Hin_resid).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for update_residual_marking_aux. *)
  
  Lemma update_residual_marking_aux_no_error :
    forall (spn : Spn)
           (t : Trans)
           (pre_places : list Place)
           (residual_marking : list (Place * nat)),
      incl pre_places (fst (split residual_marking)) ->
      exists final_marking : list (Place * nat),
        update_residual_marking_aux spn residual_marking t pre_places = Some final_marking.
  Proof.
    intros spn t; induction pre_places; intros residual_marking Hincl_pre.
    (* BASE CASE *)
    - simpl; exists residual_marking; reflexivity.
    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: pre_places)) by apply in_eq.
      specialize (Hincl_pre a Hin_eq) as Hin_a_res.
      specialize (modify_m_no_error residual_marking a Nat.sub (pre spn t a) Hin_a_res)
        as Hmodify_ex.
      inversion_clear Hmodify_ex as (m' & Hmodify).
      rewrite Hmodify.
      apply incl_cons_inv in Hincl_pre.
      specialize (modify_m_same_struct residual_marking m' a Nat.sub (pre spn t a) Hmodify)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_pre.
      apply (IHpre_places m' Hincl_pre).
  Qed.
      
  (** Correctness proof for [update_residual_marking]. 

      Needed to prove GENERAL CASE in spn_fire_aux_sens_by_residual. *)
  
  Lemma update_residual_marking_correct :
    forall (spn : Spn)
           (residual_marking : list (Place * nat))
           (t : Trans)
           (neigh_of_t : Neighbours)
           (final_marking : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split residual_marking)) ->
      In (t , neigh_of_t) (lneighbours spn) ->
      update_residual_marking spn residual_marking neigh_of_t t = Some final_marking ->
      forall (p : Place) (n : nat),
        In (p, n) residual_marking -> In (p, n - (pre spn t p)) final_marking.
  Proof.
    intros spn residual_marking t neigh_of_t final_marking
           Hwell_def_spn Hnodup_resm Hin_lneigh Hfun p n Hin_resm.
    unfold update_residual_marking in Hfun.
    (* Two cases, either p ∈ (pre_pl neigh_of_t), or
       p ∉ (pre_pl neigh_of_t). *)
    assert (Hvee_in_pre_pl := classic (In p (pre_pl neigh_of_t))).
    inversion Hvee_in_pre_pl as [Hin_p_pre | Hnotin_p_pre]; clear Hvee_in_pre_pl.
    (* First case, p ∈ pre_pl, then applies update_residual_marking_aux_correct. *)
    - explode_well_defined_spn.
      (* Builds NoDup pre_pl. *)
      assert (Hin_flat : In p (flatten_neighbours neigh_of_t))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).      
      unfold NoDupInNeighbours in Hnodup_neigh.
      specialize (Hnodup_neigh t neigh_of_t Hin_lneigh) as Hnodup_flat.
      apply proj1 in Hnodup_flat;
        apply nodup_app in Hnodup_flat;
        apply proj1 in Hnodup_flat.
      (* Then, applies update_residual_marking_aux_correct. *)
      apply (update_residual_marking_aux_correct
               spn residual_marking t (pre_pl neigh_of_t) neigh_of_t final_marking
               Hwell_def_spn Hnodup_resm Hin_lneigh Hnodup_flat
               (incl_refl (pre_pl neigh_of_t)) Hfun p n Hin_p_pre Hin_resm).
    (* Second case, p ∉ pre_pl, then applies 
       update_residual_marking_aux_not_in_pre_places. *)
    - explode_well_defined_spn.
      unfold AreWellDefinedPreEdges in Hwell_def_pre.
      specialize (Hwell_def_pre t neigh_of_t p Hin_lneigh) as Hw_pre_edges.
      apply proj2 in Hw_pre_edges; specialize (Hw_pre_edges Hnotin_p_pre).
      rewrite Hw_pre_edges; rewrite Nat.sub_0_r.
      specialize (update_residual_marking_aux_not_in_pre_places
                    spn residual_marking t (pre_pl neigh_of_t) final_marking
                    Hfun p Hnotin_p_pre n) as Hequiv.
      rewrite <- Hequiv; assumption.
  Qed.

  (** No error lemma for update_residual_marking. *)
  
  Lemma update_residual_marking_no_error :
    forall (spn : Spn)
           (t : Trans)
           (neigh_of_t : Neighbours)
           (residual_marking : list (Place * nat)),
      incl (pre_pl neigh_of_t) (fst (split residual_marking)) ->
      exists final_marking : list (Place * nat),
        update_residual_marking spn residual_marking neigh_of_t t = Some final_marking.
  Proof.
    intros spn t neigh_of_t residual_marking Hincl_pre.
    apply (update_residual_marking_aux_no_error
             spn t (pre_pl neigh_of_t) residual_marking Hincl_pre).
  Qed.
  
End UpdateResidualMarking.

(** Lemmas on update_marking_pre and update_marking_post functions, and  
 *  their mapped versions. *)

Section SpnUpdateMarking.

  (** [update_marking_pre_aux] preserves marking structure. *)
  
  Lemma update_marking_pre_aux_same_marking :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (m' : list (Place * nat)),
      update_marking_pre_aux spn m t pre_places = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros spn m t pre_places;
      functional induction (update_marking_pre_aux spn m t pre_places)
                 using update_marking_pre_aux_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply modify_m_same_struct in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** [update_marking_pre] preserves marking structure. *)
  
  Lemma update_marking_pre_same_marking :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (m' : list (Place * nat)),
      update_marking_pre spn m t = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros spn m t;
      functional induction (update_marking_pre spn m t) using update_marking_pre_ind;
      intros m' Hfun.
    (* GENERAL CASE *)
    - apply update_marking_pre_aux_same_marking in Hfun; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Needed to prove update_marking_pre_aux_correct. *)

  Lemma update_marking_pre_aux_not_in_pre_places :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (m' : list (Place * nat)),
      update_marking_pre_aux spn m t pre_places = Some m' ->
      forall (p : Place),
        ~In p pre_places ->
        forall (n : nat), In (p, n) m <-> In (p, n) m'.
  Proof.
    intros spn m t pre_places;
      functional induction (update_marking_pre_aux spn m t pre_places)
                 using update_marking_pre_aux_ind;
      intros fm Hfun p' Hnot_in_pre n.
    (* BASE CASE *)
    - injection Hfun as Hfun.
      rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply not_in_cons in Hnot_in_pre.
      elim Hnot_in_pre; intros Hdiff_pp' Hnot_in_tl.
      apply not_eq_sym in Hdiff_pp'.
      specialize (modify_m_in_if_diff
                    marking p Nat.sub (pre spn t p) m'
                    e0 p' n Hdiff_pp') as Hequiv.
      rewrite Hequiv.
      apply (IHo fm Hfun p' Hnot_in_tl n).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Correctness proof for [update_marking_pre_aux].
    Express the structure of the returned [m'] regarding the structure
    of [m]. 

    Needed to prove update_marking_pre_correct. *)

  Lemma update_marking_pre_aux_correct :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (neigh_of_t : Neighbours)
           (m' : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split m)) ->
      In (t , neigh_of_t) (lneighbours spn) ->
      NoDup pre_places ->
      incl pre_places (pre_pl neigh_of_t) ->
      update_marking_pre_aux spn m t pre_places = Some m' ->
      forall (p : Place) (n : nat),
        In p pre_places ->
        In (p, n) m ->
        In (p, n - (pre spn t p)) m'.
  Proof.
    intros spn m t pre_places;
      functional induction (update_marking_pre_aux spn m t pre_places)
                 using update_marking_pre_aux_ind;
      intros neigh_of_t fm Hwell_def_spn Hnodup_m
             Hin_lneigh Hnodup_pre_pl Hincl_pre_pl Hfun p' n Hin_pre_pl Hin_resid.
    (* BASE CASE, pre_places = []. *)
    - inversion Hin_pre_pl.
    (* GENERAL CASE *)
    - inversion Hin_pre_pl as [Heq_pp' | Hin_p'_tail].
      (* First subcase, p = p'. *)
      + rewrite <- Heq_pp' in Hin_pre_pl.
        rewrite <- Heq_pp' in Hin_resid.
        specialize (modify_m_correct
                      marking p Nat.sub (pre spn t p) m'
                      Hnodup_m e0 n Hin_resid) as Hin_resid'.
        apply NoDup_cons_iff in Hnodup_pre_pl.
        elim Hnodup_pre_pl; intros Hnot_in_tl Hnodup_tl.
        rewrite Heq_pp' in Hnot_in_tl.
        specialize (update_marking_pre_aux_not_in_pre_places
                      spn m' t tail fm
                      Hfun p' Hnot_in_tl (n - pre spn t p)) as Hin_equiv'.
        rewrite Heq_pp' in Hin_resid'.
        rewrite Heq_pp' in Hin_equiv'.
        rewrite Hin_equiv' in Hin_resid'; assumption.
      (* Second subcase, In p' tail, then apply induction hypothesis. *)
      (* But we need to show NoDup (fst (split residual')) first. *)
      + specialize (modify_m_same_struct
                      marking m' p Nat.sub  (pre spn t p) e0)
          as Hsame_struct.
        unfold MarkingHaveSameStruct in Hsame_struct.
        rewrite Hsame_struct in Hnodup_m.
        (* Builds the other hypotheses, needed to specialize IHo. *)
        apply NoDup_cons_iff in Hnodup_pre_pl;
          elim Hnodup_pre_pl;
          intros Hnot_in_tl Hnodup_tl.
        apply incl_cons_inv in Hincl_pre_pl.        
        (* Then specializes the induction hypothesis. *)
        specialize (IHo neigh_of_t fm Hwell_def_spn Hnodup_m
                        Hin_lneigh Hnodup_tl Hincl_pre_pl Hfun
                        p' n Hin_p'_tail) as Himpl.
        specialize (not_in_in_diff p p' tail (conj Hnot_in_tl Hin_p'_tail))
          as Hdiff_pp.
        specialize (modify_m_in_if_diff
                      marking p Nat.sub (pre spn t p)
                      m' e0 p' n Hdiff_pp) as Hequiv'.
        rewrite <- Hequiv' in Himpl.
        apply (Himpl Hin_resid).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for update_marking_pre_aux. *)
  
  Lemma update_marking_pre_aux_no_error :
    forall (spn : Spn)
           (t : Trans)
           (pre_places : list Place)
           (m : list (Place * nat)),
      incl pre_places (fst (split m)) ->
      exists m' : list (Place * nat),
        update_marking_pre_aux spn m t pre_places = Some m'.
  Proof.
    intros spn t; induction pre_places; intros residual_marking Hincl_pre.
    (* BASE CASE *)
    - simpl; exists residual_marking; reflexivity.
    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: pre_places)) by apply in_eq.
      specialize (Hincl_pre a Hin_eq) as Hin_a_res.
      specialize (modify_m_no_error residual_marking a Nat.sub (pre spn t a) Hin_a_res)
        as Hmodify_ex.
      inversion_clear Hmodify_ex as (m' & Hmodify).
      rewrite Hmodify.
      apply incl_cons_inv in Hincl_pre.
      specialize (modify_m_same_struct residual_marking m' a Nat.sub (pre spn t a) Hmodify)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_pre.
      apply (IHpre_places m' Hincl_pre).
  Qed.

  (** Correctness proof for [update_marking_pre]. 

      Needed to prove GENERAL CASE in spn_fire_aux_sens_by_residual. *)
  
  Lemma update_marking_pre_correct :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (final_marking : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split marking)) ->
      update_marking_pre spn marking t = Some final_marking ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> In (p, n - (pre spn t p)) final_marking.
  Proof.
    intros spn marking t;
      functional induction (update_marking_pre spn marking t)
                 using update_marking_pre_ind;
      intros final_marking Hwell_def_spn Hnodup_resm Hfun p n Hin_resm.
    (* GENERAL CASE *)
    - (* Two cases, either p ∈ (pre_pl neigh_of_t), or
       p ∉ (pre_pl neigh_of_t). *)
      assert (Hvee_in_pre_pl := classic (In p (pre_pl neighbours_of_t))).
      inversion_clear Hvee_in_pre_pl as [Hin_p_pre | Hnotin_p_pre];
        specialize (get_neighbours_correct (lneighbours spn) t neighbours_of_t e) as Hin_lneigh.
      (* First case, p ∈ pre_pl, then applies update_marking_pre_aux_correct. *)
      + explode_well_defined_spn.
        (* Builds NoDup pre_pl. *)
        assert (Hin_flat : In p (flatten_neighbours neighbours_of_t))
          by (unfold flatten_neighbours; apply in_or_app; left; assumption).      
        unfold NoDupInNeighbours in Hnodup_neigh.
        specialize (Hnodup_neigh t neighbours_of_t Hin_lneigh) as Hnodup_flat.
        apply proj1 in Hnodup_flat;
          apply nodup_app in Hnodup_flat;
          apply proj1 in Hnodup_flat.
        (* Then, applies update_marking_pre_aux_correct. *)
        apply (update_marking_pre_aux_correct
                 spn marking t (pre_pl neighbours_of_t) neighbours_of_t final_marking
                 Hwell_def_spn Hnodup_resm Hin_lneigh Hnodup_flat
                 (incl_refl (pre_pl neighbours_of_t)) Hfun p n Hin_p_pre Hin_resm).
      (* Second case, p ∉ pre_pl, then applies 
       update_marking_pre_aux_not_in_pre_places. *)
      + explode_well_defined_spn.
        unfold AreWellDefinedPreEdges in Hwell_def_pre.
        specialize (Hwell_def_pre t neighbours_of_t p Hin_lneigh) as Hw_pre_edges.
        apply proj2 in Hw_pre_edges; specialize (Hw_pre_edges Hnotin_p_pre).
        rewrite Hw_pre_edges; rewrite Nat.sub_0_r.
        specialize (update_marking_pre_aux_not_in_pre_places
                      spn marking t (pre_pl neighbours_of_t) final_marking
                      Hfun p Hnotin_p_pre n) as Hequiv.
        rewrite <- Hequiv; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for [update_marking_pre]. *)
  
  Lemma update_marking_pre_no_error :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (neigh_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      In (t, neigh_of_t) (lneighbours spn) ->
      incl (flatten_neighbours neigh_of_t) (fst (split marking)) ->
      exists final_marking : list (Place * nat),
        update_marking_pre spn marking t = Some final_marking.
  Proof.
    intros spn marking t neigh_of_t Hwell_def_spn Hin_t_fs Hincl_flat.
    explode_well_defined_spn.
    unfold NoUnknownTransInLNeighbours in Hunk_tr_neigh.
    unfold NoDupTranss in Hnodup_transs.
    rewrite Hunk_tr_neigh in Hnodup_transs.
    specialize (get_neighbours_complete (lneighbours spn) t neigh_of_t Hnodup_transs Hin_t_fs)
      as Hget_neigh.
    unfold update_marking_pre.
    rewrite Hget_neigh.
    assert (Hincl_prepl : incl (pre_pl neigh_of_t) (fst (split marking))).
    {
      intros x Hin_x_pre.
      apply or_introl
        with (B := In x ((test_pl neigh_of_t)
                           ++ (inhib_pl neigh_of_t)
                           ++ (post_pl neigh_of_t)))
        in Hin_x_pre.
      apply in_or_app in Hin_x_pre.
      apply (Hincl_flat x Hin_x_pre).
    }
    apply (update_marking_pre_aux_no_error spn t (pre_pl neigh_of_t) marking Hincl_prepl).
  Qed.

  (** [map_update_marking_pre] preserves marking structure. *)
  
  Lemma map_update_marking_pre_same_marking :
    forall (spn : Spn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      map_update_marking_pre spn m fired = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros spn m fired;
      functional induction (map_update_marking_pre spn m fired) using map_update_marking_pre_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply update_marking_pre_same_marking in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** 
   * Correctness lemma for [map_update_marking_pre].
   * 
   * map_update_marking_pre spn m fired = m' ⇒ m' = m - ∑ pre(t), ∀ t ∈ fired
   * 
   * [map_update_marking_pre] substracts tokens in the pre-places 
   *  of all transitions ∈ fired. 
   *  
   *)
  
  Lemma map_update_marking_pre_sub_pre :
    forall (spn : Spn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split m)) ->
      map_update_marking_pre spn m fired = Some m' ->
      forall (p : Place) (n : nat),
        In (p, n) m -> In (p, n - pre_sum spn p fired) m'.
  Proof.
    intros spn m fired;
      functional induction (map_update_marking_pre spn m fired) using map_update_marking_pre_ind;
      intros fm Hwell_def_spn Hnodup_m Hfun p n Hin_m.
    (* BASE CASE *)
    - injection Hfun as Heq_marking; rewrite <- Heq_marking.
      simpl; rewrite Nat.sub_0_r; assumption.
    (* GENERAL CASE *)
    - simpl. 
      rewrite Nat.sub_add_distr.
      specialize (update_marking_pre_correct
                    spn marking t m' Hwell_def_spn Hnodup_m e0 p n Hin_m) as Hin_m'.
      apply update_marking_pre_same_marking in e0;
        unfold MarkingHaveSameStruct in e0;
        rewrite e0 in Hnodup_m.
      apply (IHo fm Hwell_def_spn Hnodup_m Hfun p (n - pre spn t p) Hin_m').
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for [map_update_marking_pre]. *)

  Lemma map_update_marking_pre_no_error :
    forall (spn : Spn)
           (fired : list Trans)
           (m : list (Place * nat)),
      IsWellDefinedSpn spn ->
      incl fired (fst (split (lneighbours spn))) ->
      (forall (t : Trans)
              (neigh_of_t : Neighbours),
          In (t, neigh_of_t) (lneighbours spn) ->
          incl (flatten_neighbours neigh_of_t) (fst (split m))) ->
      exists m' : list (Place * nat),
        map_update_marking_pre spn m fired = Some m'.
  Proof.
    intros spn; induction fired; intros m Hwell_def_spn Hincl_f_lneigh Hincl_fl_m.

    (* BASE CASE *)
    - simpl; exists m; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: fired)) by apply in_eq.
      specialize (Hincl_f_lneigh a Hin_eq) as Hin_a_fs_ln.
      specialize (in_fst_split_in_pair a (lneighbours spn) Hin_a_fs_ln)
        as Hin_fs_ln.
      inversion_clear Hin_fs_ln as ( neigh_of_a & Hin_ln ).
      specialize (Hincl_fl_m a neigh_of_a Hin_ln) as Hincl_flat.
      specialize (update_marking_pre_no_error
                    spn m a neigh_of_a Hwell_def_spn Hin_ln Hincl_flat)
        as Hupdate_pre_ex.
      inversion_clear Hupdate_pre_ex as ( final_marking & Hupdate_pre ).
      rewrite Hupdate_pre.
      apply incl_cons_inv in Hincl_f_lneigh.
      specialize (update_marking_pre_same_marking spn m a final_marking Hupdate_pre)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_fl_m.
      apply (IHfired final_marking Hwell_def_spn Hincl_f_lneigh Hincl_fl_m).
  Qed.
  
  (** ----------------------------------------------------------- **)
  (** ----------------------------------------------------------- **)

  (** [update_marking_post_aux] preserves marking structure. *)
  
  Lemma update_marking_post_aux_same_marking :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (post_places : list Place)
           (m' : list (Place * nat)),
      update_marking_post_aux spn m t post_places = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros spn m t post_places;
      functional induction (update_marking_post_aux spn m t post_places)
                 using update_marking_post_aux_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply modify_m_same_struct in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** [update_marking_post] preserves marking structure. *)
  
  Lemma update_marking_post_same_marking :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (m' : list (Place * nat)),
      update_marking_post spn m t = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros spn m t;
      functional induction (update_marking_post spn m t) using update_marking_post_ind;
      intros m' Hfun.
    (* GENERAL CASE *)
    - apply update_marking_post_aux_same_marking in Hfun; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Needed to prove update_marking_post_aux_correct. *)

  Lemma update_marking_post_aux_not_in_post_places :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (post_places : list Place)
           (m' : list (Place * nat)),
      update_marking_post_aux spn m t post_places = Some m' ->
      forall (p : Place),
        ~In p post_places ->
        forall (n : nat), In (p, n) m <-> In (p, n) m'.
  Proof.
    intros spn m t post_places;
      functional induction (update_marking_post_aux spn m t post_places)
                 using update_marking_post_aux_ind;
      intros fm Hfun p' Hnot_in_post n.
    (* BASE CASE *)
    - injection Hfun as Hfun.
      rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply not_in_cons in Hnot_in_post.
      elim Hnot_in_post; intros Hdiff_pp' Hnot_in_tl.
      apply not_eq_sym in Hdiff_pp'.
      specialize (modify_m_in_if_diff
                    marking p Nat.add (post spn t p) m'
                    e0 p' n Hdiff_pp') as Hequiv.
      rewrite Hequiv.
      apply (IHo fm Hfun p' Hnot_in_tl n).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Correctness proof for [update_marking_post_aux].
    Express the structure of the returned [m'] regarding the structure
    of [m]. 

    Needed to prove update_marking_post_correct. *)

  Lemma update_marking_post_aux_correct :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (post_places : list Place)
           (neigh_of_t : Neighbours)
           (m' : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split m)) ->
      In (t , neigh_of_t) (lneighbours spn) ->
      NoDup post_places ->
      incl post_places (post_pl neigh_of_t) ->
      update_marking_post_aux spn m t post_places = Some m' ->
      forall (p : Place) (n : nat),
        In p post_places ->
        In (p, n) m ->
        In (p, n + (post spn t p)) m'.
  Proof.
    intros spn m t post_places;
      functional induction (update_marking_post_aux spn m t post_places)
                 using update_marking_post_aux_ind;
      intros neigh_of_t fm Hwell_def_spn Hnodup_m
             Hin_lneigh Hnodup_post_pl Hincl_post_pl Hfun p' n Hin_post_pl Hin_resid.
    (* BASE CASE, post_places = []. *)
    - inversion Hin_post_pl.
    (* GENERAL CASE *)
    - inversion Hin_post_pl as [Heq_pp' | Hin_p'_tail].
      (* First subcase, p = p'. *)
      + rewrite <- Heq_pp' in Hin_post_pl.
        rewrite <- Heq_pp' in Hin_resid.
        specialize (modify_m_correct
                      marking p Nat.add (post spn t p) m'
                      Hnodup_m e0 n Hin_resid) as Hin_resid'.
        apply NoDup_cons_iff in Hnodup_post_pl.
        elim Hnodup_post_pl; intros Hnot_in_tl Hnodup_tl.
        rewrite Heq_pp' in Hnot_in_tl.
        specialize (update_marking_post_aux_not_in_post_places
                      spn m' t tail fm
                      Hfun p' Hnot_in_tl (n + post spn t p)) as Hin_equiv'.
        rewrite Heq_pp' in Hin_resid'.
        rewrite Heq_pp' in Hin_equiv'.
        rewrite Hin_equiv' in Hin_resid'; assumption.
      (* Second subcase, In p' tail, then apply induction hypothesis. *)
      (* But we need to show NoDup (fst (split residual')) first. *)
      + specialize (modify_m_same_struct
                      marking m' p Nat.add (post spn t p) e0)
          as Hsame_struct.
        unfold MarkingHaveSameStruct in Hsame_struct.
        rewrite Hsame_struct in Hnodup_m.
        (* Builds the other hypotheses, needed to specialize IHo. *)
        apply NoDup_cons_iff in Hnodup_post_pl;
          elim Hnodup_post_pl;
          intros Hnot_in_tl Hnodup_tl.
        apply incl_cons_inv in Hincl_post_pl.        
        (* Then specializes the induction hypothesis. *)
        specialize (IHo neigh_of_t fm Hwell_def_spn Hnodup_m
                        Hin_lneigh Hnodup_tl Hincl_post_pl Hfun
                        p' n Hin_p'_tail) as Himpl.
        specialize (not_in_in_diff p p' tail (conj Hnot_in_tl Hin_p'_tail))
          as Hdiff_pp.
        specialize (modify_m_in_if_diff
                      marking p Nat.add (post spn t p)
                      m' e0 p' n Hdiff_pp) as Hequiv'.
        rewrite <- Hequiv' in Himpl.
        apply (Himpl Hin_resid).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for update_marking_post_aux. *)
  
  Lemma update_marking_post_aux_no_error :
    forall (spn : Spn)
           (t : Trans)
           (post_places : list Place)
           (m : list (Place * nat)),
      incl post_places (fst (split m)) ->
      exists m' : list (Place * nat),
        update_marking_post_aux spn m t post_places = Some m'.
  Proof.
    intros spn t; induction post_places; intros residual_marking Hincl_post.
    (* BASE CASE *)
    - simpl; exists residual_marking; reflexivity.
    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: post_places)) by apply in_eq.
      specialize (Hincl_post a Hin_eq) as Hin_a_res.
      specialize (modify_m_no_error residual_marking a Nat.add (post spn t a) Hin_a_res)
        as Hmodify_ex.
      inversion_clear Hmodify_ex as (m' & Hmodify).
      rewrite Hmodify.
      apply incl_cons_inv in Hincl_post.
      specialize (modify_m_same_struct residual_marking m' a Nat.add (post spn t a) Hmodify)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_post.
      apply (IHpost_places m' Hincl_post).
  Qed.

  (** No error lemma for [update_marking_post]. *)
  
  Lemma update_marking_post_no_error :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (neigh_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      In (t, neigh_of_t) (lneighbours spn) ->
      incl (flatten_neighbours neigh_of_t) (fst (split marking)) ->
      exists final_marking : list (Place * nat),
        update_marking_post spn marking t = Some final_marking.
  Proof.
    intros spn marking t neigh_of_t Hwell_def_spn Hin_t_fs Hincl_flat.
    explode_well_defined_spn.
    unfold NoUnknownTransInLNeighbours in Hunk_tr_neigh.
    unfold NoDupTranss in Hnodup_transs.
    rewrite Hunk_tr_neigh in Hnodup_transs.
    specialize (get_neighbours_complete (lneighbours spn) t neigh_of_t Hnodup_transs Hin_t_fs)
      as Hget_neigh.
    unfold update_marking_post.
    rewrite Hget_neigh.
    assert (Hincl_postpl : incl (post_pl neigh_of_t) (fst (split marking))).
    {
      intros x Hin_x_post.
      apply or_intror
        with (A := In x (pre_pl neigh_of_t ++ test_pl neigh_of_t ++ inhib_pl neigh_of_t))
        in Hin_x_post.
      apply in_or_app in Hin_x_post.
      rewrite <- app_assoc in Hin_x_post.
      rewrite <- app_assoc in Hin_x_post.
      apply (Hincl_flat x Hin_x_post).
    }
    apply (update_marking_post_aux_no_error spn t (post_pl neigh_of_t) marking Hincl_postpl).
  Qed.
  
  (** Correctness proof for [update_marking_post]. 

      Needed to prove GENERAL CASE in spn_fire_aux_sens_by_residual. *)
  
  Lemma update_marking_post_correct :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (final_marking : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split marking)) ->
      update_marking_post spn marking t = Some final_marking ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> In (p, n + (post spn t p)) final_marking.
  Proof.
    intros spn marking t;
      functional induction (update_marking_post spn marking t)
                 using update_marking_post_ind;
      intros final_marking Hwell_def_spn Hnodup_resm Hfun p n Hin_resm.
    (* GENERAL CASE *)
    - (* Two cases, either p ∈ (post_pl neigh_of_t), or
       p ∉ (post_pl neigh_of_t). *)
      assert (Hvee_in_post_pl := classic (In p (post_pl neighbours_of_t))).
      inversion_clear Hvee_in_post_pl as [Hin_p_post | Hnotin_p_post];
        specialize (get_neighbours_correct (lneighbours spn) t neighbours_of_t e) as Hin_lneigh.
      (* First case, p ∈ post_pl, then applies update_marking_post_aux_correct. *)
      + explode_well_defined_spn.
        (* Builds NoDup post_pl. *)
        assert (Hin_flat : In p (flatten_neighbours neighbours_of_t))
          by (unfold flatten_neighbours; do 3 (apply in_or_app; right); assumption).
        unfold NoDupInNeighbours in Hnodup_neigh.
        specialize (Hnodup_neigh t neighbours_of_t Hin_lneigh) as Hnodup_flat.
        apply proj2 in Hnodup_flat.
        (* Then, applies update_marking_post_aux_correct. *)
        apply (update_marking_post_aux_correct
                 spn marking t (post_pl neighbours_of_t) neighbours_of_t final_marking
                 Hwell_def_spn Hnodup_resm Hin_lneigh Hnodup_flat
                 (incl_refl (post_pl neighbours_of_t)) Hfun p n Hin_p_post Hin_resm).
      (* Second case, p ∉ post_pl, then applies 
       update_marking_post_aux_not_in_post_places. *)
      + explode_well_defined_spn.
        unfold AreWellDefinedPostEdges in Hwell_def_post.
        specialize (Hwell_def_post t neighbours_of_t p Hin_lneigh) as Hw_post_edges.
        apply proj2 in Hw_post_edges; specialize (Hw_post_edges Hnotin_p_post).
        rewrite Hw_post_edges; rewrite Nat.add_0_r.
        specialize (update_marking_post_aux_not_in_post_places
                      spn marking t (post_pl neighbours_of_t) final_marking
                      Hfun p Hnotin_p_post n) as Hequiv.
        rewrite <- Hequiv; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** [map_update_marking_post] preserves marking structure. *)
  
  Lemma map_update_marking_post_same_marking :
    forall (spn : Spn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      map_update_marking_post spn m fired = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros spn m fired;
      functional induction (map_update_marking_post spn m fired) using map_update_marking_post_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply update_marking_post_same_marking in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.  

  Lemma map_update_marking_post_add_post :
    forall (spn : Spn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split m)) ->
      map_update_marking_post spn m fired = Some m' ->
      forall (p : Place) (n : nat),
        In (p, n) m -> In (p, n + post_sum spn p fired) m'.
  Proof.
    intros spn m fired;
      functional induction (map_update_marking_post spn m fired) using map_update_marking_post_ind;
      intros fm Hwell_def_spn Hnodup_m Hfun p n Hin_m.
    (* BASE CASE *)
    - injection Hfun as Heq_marking; rewrite <- Heq_marking.
      simpl; rewrite Nat.add_0_r; assumption.
    (* GENERAL CASE *)
    - simpl.
      rewrite Nat.add_assoc.
      specialize (update_marking_post_correct
                    spn marking t m' Hwell_def_spn Hnodup_m e0 p n Hin_m) as Hin_m'.
      apply update_marking_post_same_marking in e0;
        unfold MarkingHaveSameStruct in e0;
        rewrite e0 in Hnodup_m.
      apply (IHo fm Hwell_def_spn Hnodup_m Hfun p (n + post spn t p) Hin_m').
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for [map_update_marking_post]. *)

  Lemma map_update_marking_post_no_error :
    forall (spn : Spn)
           (fired : list Trans)
           (m : list (Place * nat)),
      IsWellDefinedSpn spn ->
      incl fired (fst (split (lneighbours spn))) ->
      (forall (t : Trans)
              (neigh_of_t : Neighbours),
          In (t, neigh_of_t) (lneighbours spn) ->
          incl (flatten_neighbours neigh_of_t) (fst (split m))) ->
      exists m' : list (Place * nat),
        map_update_marking_post spn m fired = Some m'.
  Proof.
    intros spn; induction fired; intros m Hwell_def_spn Hincl_f_lneigh Hincl_fl_m.

    (* BASE CASE *)
    - simpl; exists m; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: fired)) by apply in_eq.
      specialize (Hincl_f_lneigh a Hin_eq) as Hin_a_fs_ln.
      specialize (in_fst_split_in_pair a (lneighbours spn) Hin_a_fs_ln)
        as Hin_fs_ln.
      inversion_clear Hin_fs_ln as ( neigh_of_a & Hin_ln ).
      specialize (Hincl_fl_m a neigh_of_a Hin_ln) as Hincl_flat.
      specialize (update_marking_post_no_error
                    spn m a neigh_of_a Hwell_def_spn Hin_ln Hincl_flat)
        as Hupdate_post_ex.
      inversion_clear Hupdate_post_ex as ( final_marking & Hupdate_post ).
      rewrite Hupdate_post.
      apply incl_cons_inv in Hincl_f_lneigh.
      specialize (update_marking_post_same_marking spn m a final_marking Hupdate_post)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_fl_m.
      apply (IHfired final_marking Hwell_def_spn Hincl_f_lneigh Hincl_fl_m).
  Qed.
  
End SpnUpdateMarking.
