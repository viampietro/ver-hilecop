(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import Sitpn tactics, and misc. lemmas. *)

Require Import Hilecop.Sitpn.SitpnTactics.
Require Import Hilecop.Utils.HilecopLemmas.

Set Implicit Arguments.

(** * Sitpn Core Lemmas. *)

(** ** Lemmas on the Sitpn structure. *)

Section SitpnLemmas.
  
  (** For all well-defined Sitpn, If a Place p ∈ neighbourhood of Trans t, then 
      p ∈ (flatten_lneighbours sitpn.(lneighbours)). *)

  Lemma in_neigh_in_flatten :
    forall (sitpn : Sitpn) (t : Trans) (p : Place),
      IsWellDefinedSitpn sitpn ->
      In p (flatten_neighbours (lneighbours sitpn t)) ->
      In p (flatten_lneighbours sitpn (transs sitpn)).
  Proof.
    intros sitpn t p;
      functional induction (flatten_lneighbours sitpn (transs sitpn))
                 using flatten_lneighbours_ind;
      intros Hwell_def_sitpn Hin_p_flatn.

    (*  *)
    - elim H0.
      
    - apply in_or_app.
      apply in_inv in H0; elim H0; intros.
      + injection H2; intros; rewrite H3; left; assumption.
      + apply IHl0 in H2; right; assumption.
  Qed.
  
End SitpnLemmas.

(** ** Lemmas on [get_value] function. *)

Section GetValueLemmas.

  Variable A B : Type.

  Lemma get_value_correct :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (key : A)
           (l : list (A * B))
           (value : B),
      get_value eq_dec key l = Some value ->
      In (key, value) l.
  Proof.
    intros eq_dec key l;
      functional induction (get_value eq_dec key l) using get_value_ind;
      intros v Hfun.

    (* BASE CASE. *)
    - inversion Hfun.

    (* CASE key is in head couple. *)
    - injection Hfun as Heq_v; rewrite Heq_v; apply in_eq.

    (* CASE key is not in head couple. *)
    - apply in_cons; apply IHo; assumption.
  Qed.
  
  Lemma get_value_complete :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (key : A)
           (l : list (A * B))
           (value : B),
      NoDup (fst (split l)) ->
      In (key, value) l ->
      get_value eq_dec key l = Some value.
  Proof.
    intros eq_dec key l;
      functional induction (get_value eq_dec key l) using get_value_ind;
      intros v Hnodup_fs_l Hin_kv_l.

    (* BASE CASE *)
    - inversion Hin_kv_l.

    (* CASE key is in head couple. *)
    - rewrite fst_split_cons_app in Hnodup_fs_l; simpl in Hnodup_fs_l.
      apply NoDup_cons_iff in Hnodup_fs_l.

      (* Two cases, (key, v) = (key, value) or (key, v) ∈ tl. *)
      inversion_clear Hin_kv_l as [Heq_kv | Hin_kv_tl].

      (* Case (key, v) = (key, value) *)
      + injection Heq_kv as Heq_v; rewrite Heq_v; reflexivity.

      (* Case (key, v) ∈ tl *)
      + apply proj1 in Hnodup_fs_l.
        apply in_fst_split in Hin_kv_tl; contradiction.

    (* CASE key not in head couple. *)
    - apply IHo.
      + rewrite fst_split_cons_app in Hnodup_fs_l; simpl in Hnodup_fs_l.
        apply NoDup_cons_iff in Hnodup_fs_l.
        apply proj2 in Hnodup_fs_l; assumption.
      + inversion_clear Hin_kv_l as [Heq_kv_xv | Hin_kv_tl].
        -- injection Heq_kv_xv as Heq_xk Heq_vv; contradiction.
        -- assumption.
  Qed.

  (** No error lemma for get_value. *)

  Lemma get_value_no_error :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (key : A)
           (l : list (A * B)),
      In key (fst (split l)) ->
      exists value : B, get_value eq_dec key l = Some value.
  Proof.
    intros eq_dec key l Hin_k_fsl.
    induction l.
    - simpl in Hin_k_fsl; inversion Hin_k_fsl.
    - dependent induction a; simpl; case (eq_dec a key).
      + intro; exists b; reflexivity.
      + intro Heq_false; rewrite fst_split_cons_app in Hin_k_fsl.
        simpl in Hin_k_fsl.
        inversion_clear Hin_k_fsl as [Heq_ak | Hin_k_tl].
        -- contradiction.
        -- apply (IHl Hin_k_tl).
  Qed.
  
End GetValueLemmas.

(** ** Lemmas on map_check functions. *)

Section MapCheckFunctions.

  (** Correctness proof for [check_pre]. *)

  Lemma check_pre_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = (fst (split marking)) ->
      In (p, n) marking ->
      check_pre sitpn marking p t = Some true ->
      (pre sitpn t p) <= n.
  Proof.
    intros sitpn marking p t;
      functional induction (check_pre sitpn marking p t) using check_pre_ind;
      intros n Hwel_def_sitpn Heq_pls_fsm Hin_m Hfun.
    
    (* GENERAL CASE, all went well. *)
    - apply get_value_correct in e.
      
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_sitpn.
      unfold NoDupPlaces in Hnodup_places.
      assert (Hnodup_fs_m := Hnodup_places).
      rewrite Heq_pls_fsm in Hnodup_fs_m.
      assert (Heq_pp : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).

      specialize (nodup_same_pair
                    marking Hnodup_fs_m (p, n) (p, nboftokens)
                    Hin_m e Heq_pp) as Heq_nnb.
      injection Heq_nnb as Heq_nnb.
      rewrite <- Heq_nnb in Hfun; injection Hfun as Hfun.
      apply (leb_complete (pre sitpn t p) n Hfun).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for [check_pre]. *)

  Lemma check_pre_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      In (p, n) marking ->
      (pre sitpn t p) <= n ->
      check_pre sitpn marking p t = Some true.
  Proof.
    intros sitpn marking p t n Hwell_def_sitpn Heq_pls_fsm Hin_m Hspec.
    unfold check_pre.
    
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_value_complete. *)
    explode_well_defined_sitpn.
    unfold NoDupPlaces in Hnodup_places.
    assert (Hnodup_fs_m := Hnodup_places).
    rewrite Heq_pls_fsm in Hnodup_fs_m.

    (* Specializes get_value_complete. *)
    specialize (get_value_complete Nat.eq_dec p marking n Hnodup_fs_m Hin_m) as Hget_m.
    rewrite Hget_m.
    apply leb_correct in Hspec; rewrite Hspec; reflexivity.
  Qed.

  (* No error lemma for check_pre. *)

  Lemma check_pre_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans),
      In p (fst (split marking)) ->
      exists b : bool,
        check_pre sitpn marking p t = Some b.
  Proof.
    intros sitpn marking p t Hin_fs.
    unfold check_pre.
    specialize (get_value_no_error Nat.eq_dec p marking Hin_fs) as Hget_m_ex.
    inversion_clear Hget_m_ex as (nboftokens & Hget_m).
    rewrite Hget_m; exists (pre sitpn t p <=? nboftokens).
    reflexivity.
  Qed.
  
  (** ∀ sitpn, marking, pre_places, t, b,
      map_check_pre_aux sitpn marking pre_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_pre_aux_true_if_true :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans)
           (b : bool),
      map_check_pre_aux sitpn marking pre_places t b = Some true ->
      b = true.
  Proof.
    intros sitpn marking pre_places t b;
      functional induction (map_check_pre_aux sitpn marking pre_places t b)
                 using map_check_pre_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  (** Correctness proof for map_check_pre_aux. *)

  Lemma map_check_pre_aux_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans)
           (b : bool),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      incl pre_places (pre_pl (lneighbours sitpn t)) ->
      map_check_pre_aux sitpn marking pre_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p pre_places -> In (p, n) marking -> (pre sitpn t p) <= n.
  Proof.
    intros sitpn marking pre_places t b;
      functional induction (map_check_pre_aux sitpn marking pre_places t b)
                 using map_check_pre_aux_ind;
      intros Hwell_def_sitpn Heq_pls_fsm Hincl_pre_pl
             Hfun p' n Hin_pre_pl Hin_m.
    
    (* BASE CASE *)
    - inversion Hin_pre_pl.

    (* INDUCTION CASE *)
    - inversion Hin_pre_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_pre_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_pre_correct
                 marking p' t n
                 Hwell_def_sitpn Heq_pls_fsm Hin_m e0).
      + apply incl_cons_inv in Hincl_pre_pl.
        apply (IHo Hwell_def_sitpn Heq_pls_fsm Hincl_pre_pl
                   Hfun p' n Hin_p'_tail Hin_m).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for map_check_pre_aux. *)

  Lemma map_check_pre_aux_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      incl pre_places (pre_pl (lneighbours sitpn t)) ->
      (forall (p : Place) (n : nat),
          In p pre_places -> In (p, n) marking -> (pre sitpn t p) <= n) ->
      map_check_pre_aux sitpn marking pre_places t true = Some true.
  Proof.
    intros sitpn marking pre_places t;
      functional induction (map_check_pre_aux sitpn marking pre_places t true)
                 using map_check_pre_aux_ind;
      intros Hwell_def_sitpn Heq_pls_fsm Hincl_pre_pl Hspec.

    (* BASE CASE *)
    - reflexivity.

    (* GENERAL CASE *)
    - (* Builds ∃ x, (p, x) ∈ marking to apply check_pre_complete. *)
      assert (Hin_pre_pl : In p (p :: tail)) by apply in_eq.
      
      specialize (Hincl_pre_pl p Hin_pre_pl) as Hin_pre_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).
      specialize (in_neigh_in_flatten
                    sitpn t neigh_of_t p
                    Hwell_def_sitpn Hin_lneigh Hin_flat) as Hin_flat_lneigh.
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      unfold NoUnmarkedPlace in Hunm_place; rewrite Hunm_place in Hin_flat_lneigh.
      unfold MarkingHaveSameStruct in Hsame_struct; rewrite Hsame_struct in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m'); specialize (Hspec p x Hin_pre_pl Hin_m') as Hpre_le.
      
      (* Applies check_pre_complete, then the induction hypothesis. *)
      specialize (check_pre_complete
                    sitpn marking p t x
                    Hwell_def_sitpn Hsame_struct Hin_m' Hpre_le) as Hcheck_pre.
      
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_pre in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_pre_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail -> In (p, n) marking -> pre sitpn t p <= n)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo neigh_of_t Hwell_def_sitpn Hsame_struct Hin_lneigh Hincl_pre_pl Hspec').
      
    (* Deduces hypotheses necessary to apply check_pre_complete. *)
    - (* Builds ∃ x, (p, x) ∈ marking to apply check_pre_complete. *)
      assert (Hin_pre_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_pre_pl p Hin_pre_pl) as Hin_pre_pl_t.
      assert (Hin_flat : In p (flatten_neighbours neigh_of_t))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).
      specialize (in_neigh_in_flatten
                    sitpn t neigh_of_t p
                    Hwell_def_sitpn Hin_lneigh Hin_flat) as Hin_flat_lneigh.
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      unfold NoUnmarkedPlace in Hunm_place; rewrite Hunm_place in Hin_flat_lneigh.
      unfold MarkingHaveSameStruct in Hsame_struct; rewrite Hsame_struct in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m'); specialize (Hspec p x Hin_pre_pl Hin_m') as Hpre_le.
      
      (* Applies check_pre_complete, then the induction hypothesis. *)
      specialize (check_pre_complete
                    sitpn marking p t x
                    Hwell_def_sitpn Hsame_struct Hin_m' Hpre_le) as Hcheck_pre.
      
      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_pre; inversion Hcheck_pre.
  Qed.

  (** Correctness proof for map_check_pre. *)

  Lemma map_check_pre_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      map_check_pre sitpn marking (pre_pl neighbours_of_t) t = Some true ->
      forall (p : Place) (n : nat), In (p, n) marking -> (pre sitpn t p) <= n.
  Proof.
    intros sitpn marking t neighbours_of_t.
    functional induction (map_check_pre sitpn marking (pre_pl neighbours_of_t) t)
               using map_check_pre_ind;
      intros Hwell_def_sitpn Hsame_struct Hin_lneigh Hfun p n Hin_m.
    assert (Hincl_refl : incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t))
      by apply incl_refl.
    (* Proof in two stages. *)
    assert (Hvee_in_pre_pl := classic (In p (pre_pl neighbours_of_t))).
    inversion Hvee_in_pre_pl as [Hin_pre_pl | Hnotin_pre_pl]; clear Hvee_in_pre_pl.
    (* First stage, p ∈ pre_places, then we apply map_check_pre_aux_correct. *)
    - apply (map_check_pre_aux_correct
               sitpn marking (pre_pl neighbours_of_t) t true neighbours_of_t
               Hwell_def_sitpn Hsame_struct Hin_lneigh Hincl_refl Hfun p n
               Hin_pre_pl Hin_m). 
    (* Second stage, p ∉ pre_places, then (pre sitpn t p) = 0 *)
    - explode_well_defined_sitpn.
      unfold AreWellDefinedPreEdges in Hwell_def_pre.
      specialize (Hwell_def_pre t neighbours_of_t p Hin_lneigh)
        as Hw_pre.
      apply proj2 in Hw_pre.
      specialize (Hw_pre Hnotin_pre_pl) as Hw_pre; rewrite Hw_pre; apply Peano.le_0_n.
  Qed.

  (** No error lemma for map_check_pre_aux. *)

  Lemma map_check_pre_aux_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (check_result : bool),
      incl pre_places (fst (split marking)) ->
      exists b : bool,
        map_check_pre_aux sitpn marking pre_places t check_result = Some b.
  Proof.
    intros sitpn marking t; induction pre_places; intros check_result Hincl_prepl.
    (* BASE CASE *)
    - simpl; exists check_result; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_a_fs: In a (a :: pre_places)) by apply in_eq.
      apply (Hincl_prepl a) in Hin_a_fs.
      specialize (check_pre_no_error sitpn marking a t Hin_a_fs) as Hcheck_pre_ex.
      inversion_clear Hcheck_pre_ex as (b & Hcheck_pre).
      rewrite Hcheck_pre.
      apply incl_cons_inv in Hincl_prepl.
      apply (IHpre_places (b && check_result) Hincl_prepl).
  Qed.
  
  (** Correctness proof for map_check_pre. *)

  Lemma map_check_pre_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (pre sitpn t p) <= n) ->
      map_check_pre sitpn marking (pre_pl neighbours_of_t) t = Some true.
  Proof.
    intros sitpn marking t neighbours_of_t.
    functional induction (map_check_pre sitpn marking (pre_pl neighbours_of_t) t)
               using map_check_pre_ind;
      intros Hwell_def_sitpn Hsame_struct Hin_lneigh Hspec.
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
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place),
      incl pre_places (fst (split marking)) ->
      exists b : bool,
        map_check_pre sitpn marking pre_places t = Some b.
  Proof.
    intros sitpn marking t pre_places Hincl_prepl.
    unfold map_check_pre.
    apply (map_check_pre_aux_no_error sitpn marking t pre_places true Hincl_prepl).
  Qed.
  
  (** Correctness proof for check_test. *)

  Lemma check_test_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (p, n) marking ->
      check_test sitpn marking p t = Some true ->
      (test sitpn t p) <= n.
  Proof.
    intros sitpn marking p t;
      functional induction (check_test sitpn marking p t) using check_test_ind;
      intros n Hwell_def_sitpn Hsame_struct Hin_m Hfun.
    (* General case, all went well. *)
    - apply get_m_correct in e.
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_sitpn.
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
      apply (leb_complete (test sitpn t p) n Hfun).
    - inversion Hfun.
  Qed.

  (** Completeness proof for check_test. *)

  Lemma check_test_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (p, n) marking ->
      (test sitpn t p) <= n ->
      check_test sitpn marking p t = Some true.
  Proof.
    intros sitpn marking p t n Hwell_def_sitpn Hsame_struct Hin_m Hspec.
    unfold check_test.
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_m_complete. *)
    explode_well_defined_sitpn.
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
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans),
      In p (fst (split marking)) ->
      exists b : bool,
        check_test sitpn marking p t = Some b.
  Proof.
    intros sitpn marking p t Hin_fs.
    unfold check_test.
    specialize (get_m_no_error marking p Hin_fs) as Hget_m_ex.
    inversion_clear Hget_m_ex as (nboftokens & Hget_m).
    rewrite Hget_m; exists (test sitpn t p <=? nboftokens).
    reflexivity.
  Qed.
  
  (** ∀ sitpn, marking, test_places, t, b,
      map_check_test_aux sitpn marking test_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_test_aux_true_if_true :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (b : bool),
      map_check_test_aux sitpn marking test_places t b = Some true ->
      b = true.
  Proof.
    intros sitpn marking test_places t b;
      functional induction (map_check_test_aux sitpn marking test_places t b)
                 using map_check_test_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  (** Correctness proof for map_check_test_aux. *)

  Lemma map_check_test_aux_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (b : bool)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      incl test_places (test_pl neighbours_of_t) ->
      map_check_test_aux sitpn marking test_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p test_places -> In (p, n) marking -> (test sitpn t p) <= n.
  Proof.
    intros sitpn marking test_places t b;
      functional induction (map_check_test_aux sitpn marking test_places t b)
                 using map_check_test_aux_ind;
      intros neigh_of_t Hwell_def_sitpn Hsame_struct Hin_lneigh Hincl_test_pl
             Hfun p' n Hin_test_pl Hin_m.
    - inversion Hin_test_pl.
    - inversion Hin_test_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_test_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_test_correct
                 sitpn marking p' t n
                 Hwell_def_sitpn Hsame_struct Hin_m e0).
      + apply incl_cons_inv in Hincl_test_pl.
        apply (IHo neigh_of_t
                   Hwell_def_sitpn Hsame_struct Hin_lneigh Hincl_test_pl
                   Hfun p' n Hin_p'_tail Hin_m).
    - inversion Hfun.
  Qed.

  (** Completeness proof for map_check_test_aux. *)

  Lemma map_check_test_aux_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      incl test_places (test_pl neighbours_of_t) ->
      (forall (p : Place) (n : nat),
          In p test_places -> In (p, n) marking -> (test sitpn t p) <= n) ->
      map_check_test_aux sitpn marking test_places t true = Some true.
  Proof.
    intros sitpn marking test_places t.
    functional induction (map_check_test_aux sitpn marking test_places t true)
               using map_check_test_aux_ind;
      intros neigh_of_t Hwell_def_sitpn Hsame_struct Hin_lneigh
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
                    sitpn t neigh_of_t p
                    Hwell_def_sitpn Hin_lneigh Hin_flat) as Hin_flat_lneigh.
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      unfold NoUnmarkedPlace in Hunm_place; rewrite Hunm_place in Hin_flat_lneigh.
      unfold MarkingHaveSameStruct in Hsame_struct; rewrite Hsame_struct in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m'); specialize (Hspec p x Hin_test_pl Hin_m') as Htest_le.
      (* Applies check_test_complete, then the induction hypothesis. *)
      specialize (check_test_complete
                    sitpn marking p t x
                    Hwell_def_sitpn Hsame_struct Hin_m' Htest_le) as Hcheck_test.
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_test in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_test_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail -> In (p, n) marking -> test sitpn t p <= n)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo neigh_of_t Hwell_def_sitpn Hsame_struct Hin_lneigh Hincl_test_pl Hspec').
    (* Deduces hypotheses necessary to apply check_test_complete. *)
    - (* Builds ∃ x, (p, x) ∈ marking to apply check_test_complete. *)
      assert (Hin_test_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_test_pl p Hin_test_pl) as Hin_test_pl_t.
      assert (Hin_flat : In p (flatten_neighbours neigh_of_t))
        by (unfold flatten_neighbours;
            apply in_or_app; right;
            apply in_or_app; left; assumption).
      specialize (in_neigh_in_flatten
                    sitpn t neigh_of_t p
                    Hwell_def_sitpn Hin_lneigh Hin_flat) as Hin_flat_lneigh.
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      unfold NoUnmarkedPlace in Hunm_place; rewrite Hunm_place in Hin_flat_lneigh.
      unfold MarkingHaveSameStruct in Hsame_struct; rewrite Hsame_struct in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m'); specialize (Hspec p x Hin_test_pl Hin_m') as Htest_le.
      (* Applies check_test_complete, then the induction hypothesis. *)
      specialize (check_test_complete
                    sitpn marking p t x
                    Hwell_def_sitpn Hsame_struct Hin_m' Htest_le) as Hcheck_test.
      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_test; inversion Hcheck_test.
  Qed.

  (** No error lemma for map_check_test_aux. *)

  Lemma map_check_test_aux_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (test_places : list Place)
           (check_result : bool),
      incl test_places (fst (split marking)) ->
      exists b : bool,
        map_check_test_aux sitpn marking test_places t check_result = Some b.
  Proof.
    intros sitpn marking t; induction test_places; intros check_result Hincl_testpl.
    (* BASE CASE *)
    - simpl; exists check_result; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_a_fs: In a (a :: test_places)) by apply in_eq.
      apply (Hincl_testpl a) in Hin_a_fs.
      specialize (check_test_no_error sitpn marking a t Hin_a_fs) as Hcheck_test_ex.
      inversion_clear Hcheck_test_ex as (b & Hcheck_test).
      rewrite Hcheck_test.
      apply incl_cons_inv in Hincl_testpl.
      apply (IHtest_places (b && check_result) Hincl_testpl).
  Qed.
  
  (** Correctness proof for map_check_test. *)

  Lemma map_check_test_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      map_check_test sitpn marking (test_pl neighbours_of_t) t = Some true ->
      forall (p : Place) (n : nat), In (p, n) marking -> (test sitpn t p) <= n.
  Proof.
    intros sitpn marking t neighbours_of_t.
    functional induction (map_check_test sitpn marking (test_pl neighbours_of_t) t)
               using map_check_test_ind;
      intros Hwell_def_sitpn Hsame_struct Hin_lneigh Hfun p n Hin_m.
    assert (Hincl_refl : incl (test_pl neighbours_of_t) (test_pl neighbours_of_t))
      by apply incl_refl.
    (* Proof in two stages. *)
    assert (Hvee_in_test_pl := classic (In p (test_pl neighbours_of_t))).
    inversion Hvee_in_test_pl as [Hin_test_pl | Hnotin_test_pl]; clear Hvee_in_test_pl.
    (* First stage, p ∈ test_places, then we apply map_check_test_aux_correct. *)
    - apply (map_check_test_aux_correct
               sitpn marking (test_pl neighbours_of_t) t true neighbours_of_t
               Hwell_def_sitpn Hsame_struct Hin_lneigh Hincl_refl Hfun p n
               Hin_test_pl Hin_m). 
    (* Second stage, p ∉ test_places, then (test sitpn t p) = 0 *)
    - explode_well_defined_sitpn.
      unfold AreWellDefinedTestEdges in Hwell_def_test.
      specialize (Hwell_def_test t neighbours_of_t p Hin_lneigh)
        as Hw_test.
      apply proj2 in Hw_test.
      specialize (Hw_test Hnotin_test_pl) as Hw_test; rewrite Hw_test; apply Peano.le_0_n.
  Qed.

  (** Correctness proof for map_check_test. *)

  Lemma map_check_test_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (test sitpn t p) <= n) ->
      map_check_test sitpn marking (test_pl neighbours_of_t) t = Some true.
  Proof.
    intros sitpn marking t neighbours_of_t.
    functional induction (map_check_test sitpn marking (test_pl neighbours_of_t) t)
               using map_check_test_ind;
      intros Hwell_def_sitpn Hsame_struct Hin_lneigh Hspec.
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
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (test_places : list Place),
      incl test_places (fst (split marking)) ->
      exists b : bool,
        map_check_test sitpn marking test_places t = Some b.
  Proof.
    intros sitpn marking t test_places Hincl_testpl.
    unfold map_check_test.
    apply (map_check_test_aux_no_error sitpn marking t test_places true Hincl_testpl).
  Qed.
  
  (** Correctness proof for check_inhib. *)

  Lemma check_inhib_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (p, n) marking ->
      check_inhib sitpn marking p t = Some true ->
      (n < (inhib sitpn t p) \/ (inhib sitpn t p) = 0).
  Proof.
    intros sitpn marking p t;
      functional induction (check_inhib sitpn marking p t) using check_inhib_ind;
      intros n Hwell_def_sitpn Hsame_struct Hin_m Hfun.
    (* GENERAL CASE, all went well. *)
    - apply get_m_correct in e.
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_sitpn.
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
      (* First case: n < (inhib sitpn t p), second case: (inhib sitpn t p) = 0 *)
      inversion Hfun as [Hinhib_lt | Hinhib_eq_0].
      + left; apply Nat.ltb_lt; assumption.
      + right; apply Nat.eqb_eq; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for check_inhib. *)

  Lemma check_inhib_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (p, n) marking ->
      (n < (inhib sitpn t p) \/ (inhib sitpn t p) = 0) ->
      check_inhib sitpn marking p t = Some true.
  Proof.
    intros sitpn marking p t n Hwell_def_sitpn  Hsame_struct Hin_m Hspec.
    unfold check_inhib.
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_m_complete. *)
    explode_well_defined_sitpn.
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

  (** ∀ sitpn, marking, inhib_places, t, b,
      map_check_inhib_aux sitpn marking inhib_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_inhib_aux_true_if_true :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (b : bool),
      map_check_inhib_aux sitpn marking inhib_places t b = Some true ->
      b = true.
  Proof.
    intros sitpn marking inhib_places t b;
      functional induction (map_check_inhib_aux sitpn marking inhib_places t b)
                 using map_check_inhib_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  (** Correctness proof for map_check_inhib_aux. *)

  Lemma map_check_inhib_aux_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (b : bool)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      incl inhib_places (inhib_pl neighbours_of_t) ->
      map_check_inhib_aux sitpn marking inhib_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p inhib_places ->
        In (p, n) marking ->
        (n < (inhib sitpn t p) \/ (inhib sitpn t p) = 0).
  Proof.
    intros sitpn marking inhib_places t b;
      functional induction (map_check_inhib_aux sitpn marking inhib_places t b)
                 using map_check_inhib_aux_ind;
      intros neigh_of_t Hwell_def_sitpn Hsame_struct Hin_lneigh Hincl_inhib_pl Hfun
             p' n Hin_inhib_pl Hin_m.
    (* BASE CASE *)
    - inversion Hin_inhib_pl.
    (* GENERAL CASE *)
    - inversion Hin_inhib_pl as [Heq_pp' | Hin_inhib_tl]; clear Hin_inhib_pl.
      + apply map_check_inhib_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_inhib_correct
                 sitpn marking p' t n
                 Hwell_def_sitpn Hsame_struct Hin_m e0).
      + apply IHo with (neighbours_of_t := neigh_of_t);
          (assumption ||
           apply incl_cons_inv in Hincl_inhib_pl; assumption).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for map_check_inhib_aux. *)

  Lemma map_check_inhib_aux_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      incl inhib_places (inhib_pl neighbours_of_t) ->
      (forall (p : Place) (n : nat),
          In p inhib_places -> In (p, n) marking ->
          (n < (inhib sitpn t p) \/ (inhib sitpn t p) = 0)) ->
      map_check_inhib_aux sitpn marking inhib_places t true = Some true.
  Proof.
    intros sitpn marking inhib_places t;
      functional induction (map_check_inhib_aux sitpn marking inhib_places t true)
                 using map_check_inhib_aux_ind;
      intros neigh_of_t Hwell_def_sitpn Hsame_struct Hin_lneigh Hincl_inhib_pl Hspec.
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
      (* p ∈ (flatten_neighbours neighbours_of_t) ⇒ p ∈ (flatten sitpn.(lneighbours)) *)
      specialize (in_neigh_in_flatten sitpn t neigh_of_t p Hwell_def_sitpn Hin_lneigh Hin_flat)
        as Hin_flat_sitpn.
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_sitpn.
      unfold NoUnmarkedPlace in Hunm_place; rewrite Hunm_place in Hin_flat_sitpn.
      unfold MarkingHaveSameStruct in Hsame_struct; rewrite Hsame_struct in Hin_flat_sitpn.
      (* ∃ n, (p, n) ∈ marking *)
      specialize (in_fst_split_in_pair p marking Hin_flat_sitpn) as Hex_in_m;
        inversion Hex_in_m as (x & Hin_m).
      (* Applies the completeness hypothesis. *)
      specialize (Hspec p x Hin_inhib_pl Hin_m) as Hinhib_spec.
      (* Applies check_inhib_complete, then the induction hypothesis. *)
      specialize (check_inhib_complete
                    sitpn marking p t x
                    Hwell_def_sitpn Hsame_struct Hin_m Hinhib_spec) as Hcheck_inhib.
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
      (* p ∈ (flatten_neighbours neighbours_of_t) ⇒ p ∈ (flatten sitpn.(lneighbours)) *)
      specialize (in_neigh_in_flatten sitpn t neigh_of_t p Hwell_def_sitpn Hin_lneigh Hin_flat)
        as Hin_flat_sitpn.
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_sitpn.
      unfold NoUnmarkedPlace in Hunm_place; rewrite Hunm_place in Hin_flat_sitpn.
      unfold MarkingHaveSameStruct in Hsame_struct; rewrite Hsame_struct in Hin_flat_sitpn.
      (* ∃ n, (p, n) ∈ marking *)
      specialize (in_fst_split_in_pair p marking Hin_flat_sitpn) as Hex_in_m;
        inversion Hex_in_m as (x & Hin_m).
      (* Applies the completeness hypothesis. *)
      specialize (Hspec p x Hin_inhib_pl Hin_m) as Hinhib_spec.
      (* Applies check_inhib_complete, then the induction hypothesis. *)
      specialize (check_inhib_complete
                    sitpn marking p t x
                    Hwell_def_sitpn Hsame_struct Hin_m Hinhib_spec) as Hcheck_inhib.
      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_inhib; inversion Hcheck_inhib.
  Qed.
  
  (** Correctness proof for map_check_inhib. *)

  Lemma map_check_inhib_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      map_check_inhib sitpn marking (inhib_pl neighbours_of_t) t = Some true ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> (n < (inhib sitpn t p) \/ (inhib sitpn t p) = 0).
  Proof.
    intros sitpn marking t neigh_of_t.
    functional induction (map_check_inhib sitpn marking (inhib_pl neigh_of_t) t)
               using map_check_inhib_ind;
      intros Hwell_def_sitpn Hsame_struct Hin_lneigh Hfun p n Hin_m.
    assert (Hincl_refl : incl (inhib_pl neigh_of_t) (inhib_pl neigh_of_t)) by (apply incl_refl).
    (* Proof in two stages. *)
    assert (Hvee_in_inhib_pl := classic (In p (inhib_pl neigh_of_t))).
    inversion Hvee_in_inhib_pl as [Hin_inhib | Hnotin_inhib]; clear Hvee_in_inhib_pl.
    (* First stage, p ∈ inhib_places, then we apply map_check_inhib_aux_correct. *)
    - apply (map_check_inhib_aux_correct
               sitpn marking (inhib_pl neigh_of_t) t true neigh_of_t
               Hwell_def_sitpn Hsame_struct Hin_lneigh Hincl_refl Hfun
               p n Hin_inhib Hin_m).
    (* Second stage, p ∉ inhib_places, then (inhib sitpn t p) = 0 *)
    - explode_well_defined_sitpn.
      unfold AreWellDefinedInhibEdges in Hwell_def_inhib.
      generalize (Hwell_def_inhib t neigh_of_t p Hin_lneigh) as Hw_inhib; intro.
      apply proj2 in Hw_inhib.
      generalize (Hw_inhib Hnotin_inhib); intro; right; assumption.
  Qed.

  (** Correctness proof for map_check_inhib. *)

  Lemma map_check_inhib_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      (forall (p : Place) (n : nat),
          In (p, n) marking -> (n < (inhib sitpn t p) \/ (inhib sitpn t p) = 0)) ->
      map_check_inhib sitpn marking (inhib_pl neighbours_of_t) t = Some true.
  Proof.
    intros sitpn marking t neigh_of_t Hwell_def_sitpn Hsame_struct Hin_lneigh Hspec.
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
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans),
      In p (fst (split marking)) ->
      exists b : bool,
        check_inhib sitpn marking p t = Some b.
  Proof.
    intros sitpn marking p t Hin_fs.
    unfold check_inhib.
    specialize (get_m_no_error marking p Hin_fs) as Hget_m_ex.
    inversion_clear Hget_m_ex as (nboftokens & Hget_m).
    rewrite Hget_m; exists ((nboftokens <? inhib sitpn t p) || (inhib sitpn t p =? 0)).
    reflexivity.
  Qed.
  
  (** No error lemma for map_check_inhib_aux. *)

  Lemma map_check_inhib_aux_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (inhib_places : list Place)
           (check_result : bool),
      incl inhib_places (fst (split marking)) ->
      exists b : bool,
        map_check_inhib_aux sitpn marking inhib_places t check_result = Some b.
  Proof.
    intros sitpn marking t; induction inhib_places; intros check_result Hincl_inhibpl.
    (* BASE CASE *)
    - simpl; exists check_result; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_a_fs: In a (a :: inhib_places)) by apply in_eq.
      apply (Hincl_inhibpl a) in Hin_a_fs.
      specialize (check_inhib_no_error sitpn marking a t Hin_a_fs) as Hcheck_inhib_ex.
      inversion_clear Hcheck_inhib_ex as (b & Hcheck_inhib).
      rewrite Hcheck_inhib.
      apply incl_cons_inv in Hincl_inhibpl.
      apply (IHinhib_places (b && check_result) Hincl_inhibpl).
  Qed.
  
  (** No error lemma for map_check_inhib. *)

  Lemma map_check_inhib_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (inhib_places : list Place),
      incl inhib_places (fst (split marking)) ->
      exists b : bool,
        map_check_inhib sitpn marking inhib_places t = Some b.
  Proof.
    intros sitpn marking t inhib_places Hincl_inhibpl.
    unfold map_check_inhib.
    apply (map_check_inhib_aux_no_error sitpn marking t inhib_places true Hincl_inhibpl).
  Qed.
  
End MapCheckFunctions.

(** ** Lemmas on [is_sensitized] function and its spec. *)

Section IsSensitized.

  (** Correctness proof for is_sensitized and IsSensitized *)

  Theorem is_sensitized_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      is_sensitized sitpn marking neighbours_of_t t = Some true ->
      IsSensitized sitpn marking t.
  Proof.
    do 4 intro;
      functional induction (is_sensitized sitpn marking neighbours_of_t t)
                 using is_sensitized_ind;
      intros Hwell_def_sitpn Hsame_struct Hin_lneigh Hfun.
    (* GENERAL CASE *)
    - injection Hfun; intro Heq_check.
      apply andb_prop in Heq_check; elim Heq_check; intros Heq_check' Heq_inhib.
      apply andb_prop in Heq_check'; elim Heq_check'; intros Heq_pre Heq_test.
      (* Determines ∀ (p, n) ∈ marking, (pre sitpn t p) <= n *)
      rewrite Heq_pre in e.
      specialize (map_check_pre_correct
                    sitpn marking t neighbours_of_t
                    Hwell_def_sitpn Hsame_struct Hin_lneigh e)
        as Hmap_pre.
      (* Determines ∀ (p, n) ∈ marking, (test sitpn t p) <= n *)
      rewrite Heq_test in e0.
      specialize (map_check_test_correct
                    sitpn marking t neighbours_of_t
                    Hwell_def_sitpn Hsame_struct Hin_lneigh e0)
        as Hmap_test.
      (* Determines ∀ (p, n) ∈ marking, n < (inhib sitpn t p) ∨ (inhib sitpn t p) = 0 *)
      rewrite Heq_inhib in e1.
      specialize (map_check_inhib_correct
                    sitpn marking t neighbours_of_t
                    Hwell_def_sitpn Hsame_struct Hin_lneigh e1)
        as Hmap_inhib.
      (* Unfolds IsSensitized and applies all previous lemmas. *)
      unfold IsSensitized; intros p n Hin_m.
      split;
        [apply (Hmap_pre p n Hin_m)
        | split; [ apply (Hmap_test p n Hin_m) |
                   apply (Hmap_inhib p n Hin_m) ]].
    (* ERROR CASES *)
    - inversion Hfun.
    - inversion Hfun.
    - inversion Hfun.
  Qed.

  (** Completeness proof for is_sensitized and IsSensitized *)

  Theorem is_sensitized_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      IsSensitized sitpn marking t ->
      is_sensitized sitpn marking neighbours_of_t t = Some true.
  Proof.
    intros sitpn marking t neighbours_of_t;
      functional induction (is_sensitized sitpn marking neighbours_of_t t)
                 using is_sensitized_ind;
      intros Hwell_defined_sitpn Hmarking_same_struct Hin_lneigh Hspec;
      unfold IsSensitized in Hspec;
      (* Builds t ∈ sitpn.(transs), and cleans up the context. *)
      assert (Hin_lneigh' := Hin_lneigh);
      apply in_fst_split in Hin_lneigh;
      assert (Hwell_defined_sitpn' := Hwell_defined_sitpn);
      explode_well_defined_sitpn;
      unfold NoUnknownTransInLNeighbours in Hunk_tr_neigh;
      rewrite <- Hunk_tr_neigh in Hin_lneigh;
      rename Hin_lneigh into Hin_transs;
      (* Builds ∀ (p,n) ∈ marking, (pre sitpn t p) ≤ n, 
         then applies map_check_pre_complete.
       *)
      assert (Hmap_check_pre :
                forall (p : Place) (n : nat), In (p, n) marking -> pre sitpn t p <= n) by
          (intros p n Hin_m; generalize (Hspec p n Hin_m) as Hend; intro; elim Hend; auto);
      generalize (map_check_pre_complete sitpn marking t neighbours_of_t
                                         Hwell_defined_sitpn
                                         Hmarking_same_struct
                                         Hin_lneigh'
                                         Hmap_check_pre) as Hmap_check_pre';
      intro;
      (* Builds ∀ (p,n) ∈ marking, (test sitpn t p) ≤ n, 
         then applies map_check_test_complete.
       *)
      assert (Hmap_check_test :
                forall (p : Place) (n : nat), In (p, n) marking -> test sitpn t p <= n)
        by (intros p n Hin_m;
            generalize (Hspec p n Hin_m) as Hend;
            intro; decompose [and] Hend; auto);
      generalize (map_check_test_complete sitpn marking t neighbours_of_t
                                          Hwell_defined_sitpn
                                          Hmarking_same_struct
                                          Hin_lneigh'
                                          Hmap_check_test) as Hmap_check_test';
      intro;
      (* Builds ∀ (p,n) ∈ marking, (inhib sitpn t p) ≤ n, 
         then applies map_check_inhib_complete.
       *)
      assert (Hmap_check_inhib :
                forall (p : Place) (n : nat),
                  In (p, n) marking -> (n < (inhib sitpn t p) \/ (inhib sitpn t p) = 0))
        by (intros p n Hin_m;
            generalize (Hspec p n Hin_m) as Hend;
            intro; decompose [and] Hend; auto);
      generalize (map_check_inhib_complete sitpn marking t neighbours_of_t
                                           Hwell_defined_sitpn
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
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      incl (flatten_neighbours neighbours_of_t) (fst (split marking)) ->
      exists b : bool,
        is_sensitized sitpn marking neighbours_of_t t = Some b.
  Proof.
    intros sitpn marking t neighbours_of_t Hincl_flat.
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

    specialize (map_check_pre_no_error sitpn marking t (pre_pl neighbours_of_t) Hincl_prepl)
      as Hmap_check_pre_ex.

    specialize (map_check_test_no_error sitpn marking t (test_pl neighbours_of_t) Hincl_testpl)
      as Hmap_check_test_ex.

    specialize (map_check_inhib_no_error sitpn marking t (inhib_pl neighbours_of_t) Hincl_inhibpl)
      as Hmap_check_inhib_ex.

    inversion_clear Hmap_check_pre_ex as (check_pre_result & Hmap_check_pre).
    inversion_clear Hmap_check_test_ex as (check_test_result & Hmap_check_test).
    inversion_clear Hmap_check_inhib_ex as (check_inhib_result & Hmap_check_inhib).

    rewrite Hmap_check_pre, Hmap_check_test, Hmap_check_inhib.

    exists (check_pre_result && check_test_result && check_inhib_result); reflexivity.

  Qed.

  (** Conjunction of correction and completeness for is_sensitized. *)

  Theorem is_sensitized_iff :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      is_sensitized sitpn marking neighbours_of_t t = Some true <->
      IsSensitized sitpn marking t.
  Proof.
    intros sitpn marking t neighbours_of_t Hwell_def_sitpn Hsame_struct Hin_lneigh.
    split;
      [ intro Hfun;
        apply (is_sensitized_correct sitpn marking t neighbours_of_t
                                     Hwell_def_sitpn Hsame_struct
                                     Hin_lneigh Hfun)
      | intro Hspec;
        apply (is_sensitized_complete sitpn marking t neighbours_of_t
                                      Hwell_def_sitpn Hsame_struct
                                      Hin_lneigh Hspec) ].
  Qed.

  (** Conjunction of correction and completeness for ~is_sensitized. *)

  Theorem not_is_sensitized_iff :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSitpn sitpn ->
      MarkingHaveSameStruct sitpn.(initial_marking) marking ->
      In (t, neighbours_of_t) sitpn.(lneighbours) ->
      is_sensitized sitpn marking neighbours_of_t t = Some false <->
      ~IsSensitized sitpn marking t.
  Proof.
    intros sitpn marking t neighbours_of_t Hwell_def_sitpn Hsame_struct Hin_lneigh.
    split.
    
    - intros Hfun Hspec;
        rewrite <- (is_sensitized_iff sitpn marking t neighbours_of_t
                                      Hwell_def_sitpn Hsame_struct Hin_lneigh)
        in Hspec.
      rewrite Hfun in Hspec; inversion Hspec.

    - intro Hspec; case_eq (is_sensitized sitpn marking neighbours_of_t t).
      + dependent induction b.
        -- intros His_sens_fun.
           rewrite <- (is_sensitized_iff sitpn marking t neighbours_of_t
                                         Hwell_def_sitpn Hsame_struct Hin_lneigh)
             in Hspec.
           contradiction.
        -- intros; reflexivity.
      + intros Hsens_fun.
        
        (* Specializes is_sensitized_no_error to solve the subgoal. *)
        explode_well_defined_sitpn.
        unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
        assert (Hincl_flat_lneigh : incl (flatten_neighbours neighbours_of_t)
                                         (flatten_lneighbours (lneighbours sitpn))).
        {
          intros p Hin_p_flat;
            apply (in_neigh_in_flatten sitpn t neighbours_of_t p
                                       Hwell_def_sitpn Hin_lneigh Hin_p_flat).
        }
        specialize (incl_tran Hincl_flat_lneigh Hunk_pl_neigh) as Hincl_fl_m.
        rewrite Hunm_place in Hincl_fl_m.
        rewrite Hsame_struct in Hincl_fl_m.

        specialize (is_sensitized_no_error sitpn marking t neighbours_of_t Hincl_fl_m)
          as Hsens_ex.
        inversion_clear Hsens_ex as (b & Hsens).
        rewrite Hsens_fun in Hsens; inversion Hsens.
  Qed.
  
End IsSensitized.
