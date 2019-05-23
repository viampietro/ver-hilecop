(* Import Spn's types, program and specification. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Spn.SpnTokenPlayer.
Require Import Hilecop.Spn.SpnSemantics.

(* Import useful tactics and general-purpose lemmas. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Spn.SpnTactics.

(* Import core lemmas necessary for Spn's correctness proof. *)

Require Import Hilecop.Spn.SpnCoreLemmas.

(* Import lemmas about spn_map_fire's completeness. *)

Require Import Hilecop.Spn.SpnMapFireComplete.

(** Completeness lemma for spn_update_marking. *)

Lemma spn_update_marking_complete :
  forall (spn : Spn) (s : SpnState) (s' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    SpnSemantics spn s s' rising_edge ->
    exists state : SpnState,
      spn_update_marking spn s = Some state /\
      spnstate_eq s' state.
Proof.
  intros spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s' Hspec.
  unfold spn_update_marking.

  (* Builds hyps to specialize map_update_marking_pre_no_error. *)

  explode_well_defined_spn.
  explode_well_defined_spn_state Hwell_def_s.
  
  (* Hyp. incl (s fired) (fst (split lneighbours)) *)
 
  unfold NoUnknownTransInLNeighbours in Hunk_tr_neigh.
  assert (Hincl_fired := Hincl_state_fired_transs);
    rewrite Hunk_tr_neigh in Hincl_fired.

  (* Hyp. forall t, neigh_of_t, In (t, neigh_of_t) (lneighbours spn) -> ... *)

  unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
  unfold NoIsolatedPlace in Hiso_place.
  assert (Hincl_flatten :
            forall (t : Trans) (neigh_of_t : Neighbours),
              In (t, neigh_of_t) (lneighbours spn) ->
              incl (flatten_neighbours neigh_of_t) (fst (split (marking s)))).
  {
    intros t neigh_of_t Hin_lneigh p Hin_p_flat.
    specialize (in_neigh_in_flatten spn t neigh_of_t p Hwell_def_spn Hin_lneigh Hin_p_flat)
      as Hin_p_lflat.
    apply Hunk_pl_neigh in Hin_p_lflat.
    rewrite <- Hsame_marking_state_spn.
    unfold NoUnmarkedPlace in Hunm_place.
    rewrite Hunm_place in Hin_p_lflat.
    assumption.
  }
  
  (* Specializes map_update_marking_pre_no_error and rewrite 
     the goal, skipping error case. *)
  
  specialize (map_update_marking_pre_no_error
                spn (fired s) (marking s)
                Hwell_def_spn Hincl_fired Hincl_flatten) as Hmap_up_pre_ex.
  inversion Hmap_up_pre_ex as (m' & Hmap_up_pre).
  rewrite Hmap_up_pre.

  (* Builds hyps. to specialize map_update_marking_post_no_error. *)
  
  specialize (map_update_marking_pre_same_marking spn (marking s) (fired s) m' Hmap_up_pre)
    as Hsame_struct.
  rewrite Hsame_struct in Hincl_flatten.
          
  (* Specializes map_update_marking_post_no_error and rewrite 
     the goal, skipping error case. *)
  
  specialize (map_update_marking_post_no_error
                spn (fired s) m'
                Hwell_def_spn Hincl_fired Hincl_flatten) as Hmap_up_post_ex.
  inversion Hmap_up_post_ex as (m'' & Hmap_up_post).
  rewrite Hmap_up_post.

  (* Instantiates state returned by spn_update_marking function, 
   * and proves each branch of the conjunction. *)

  exists {| fired := fired s; marking := m'' |}.
  split.
  - reflexivity.

  (* Proves that the returned state verifies spnstate_eq relation. *)
    
  - unfold spnstate_eq.
    inversion Hspec.
    clear H H0 H1.
    rename H2 into Heq_fired, H3 into Hup_mark.

    (* Proves 2 branches of the spnstate_eq relation. *)
    split.
    + simpl.

      (* Builds hyps. to apply NoDup_Permutation. *)

      (* Hyp. NoDup (marking s'). *)
      (* Explodes and renames IsWelldefinedspnstate predicates. *)
      
      rename Hsame_marking_state_spn into Hsame_marking_s_spn,
             Hincl_state_fired_transs into Hincl_s_fired_transs,
             Hnodup_state_fired into Hnodup_s_fired,
             Hwell_def_state into Hwell_def_s.
      
      explode_well_defined_spn_state Hwell_def_s'.
      
      rename Hsame_marking_state_spn into Hsame_marking_s'_spn,
             Hincl_state_fired_transs into Hincl_s'_fired_transs,
             Hnodup_state_fired into Hnodup_s'_fired,
             Hwell_def_state into Hwell_def_s'.

      assert (Hnodup_m_s' := Hnodup_places).
      
      unfold NoUnmarkedPlace in *.
      unfold NoDupPlaces in *.
      rewrite Hunm_place in Hnodup_m_s'.
      rewrite Hsame_marking_s'_spn in Hnodup_m_s'.
      assert (Hnodup_m'' := Hnodup_m_s'). (* Useful for next hyp. *)
      apply nodup_fst_split in Hnodup_m_s'.
      
      (* Hyp. NoDup m''. *)

      specialize (map_update_marking_post_same_marking spn m' (fired s) m'' Hmap_up_post)
        as Hsame_struct'.
      rewrite <- Hsame_marking_s'_spn in Hnodup_m''.
      rewrite Hsame_marking_s_spn in Hnodup_m''.
      rewrite Hsame_struct in Hnodup_m''.
      rewrite Hsame_struct' in Hnodup_m''.
      apply nodup_fst_split in Hnodup_m''.
      
      (* Hyp. In (p, n) (marking s') <-> In (p, n) m'' *)

      assert (Heq_ms'_m'' : forall (c : (Place * nat)), In c (marking s') <-> In c m'').
      {
        intro c; induction c; split.
        
        (* In (p, n) (marking s') -> In (p, n) m'' *)
        - intros Hin_ms'.

          (* Builds In (a, x) (marking s) *)
          
          specialize (in_fst_split a b (marking s') Hin_ms') as Hin_ms_ex.
          rewrite <- Hsame_marking_s'_spn in Hin_ms_ex.
          rewrite Hsame_marking_s_spn in Hin_ms_ex.
          apply in_fst_split_in_pair in Hin_ms_ex.

          inversion Hin_ms_ex as (x & Hin_ms).

          (* Specializes map_pre and map_post to get 
             hyp. In (a, x - pre + post) m'' *)
          
          assert (Hnodup_fs_ms := Hnodup_places).
          rewrite Hunm_place in Hnodup_fs_ms.
          rewrite Hsame_marking_s_spn in Hnodup_fs_ms.
          
          specialize (map_update_marking_pre_sub_pre
                        spn (marking s) (fired s) m'
                        Hwell_def_spn Hnodup_fs_ms Hmap_up_pre a x Hin_ms)
            as Hin_m'.

          assert (Hnodup_fs_m' := Hnodup_fs_ms).
          rewrite Hsame_struct in Hnodup_fs_m'.

          specialize (map_update_marking_post_add_post
                        spn m' (fired s) m''
                        Hwell_def_spn Hnodup_fs_m' Hmap_up_post a
                        (x - pre_sum spn a (fired s)) Hin_m')
            as Hin_m''.

          (* Specializes Hup_mark and nodup_same_pair 
             to get (x - pre + post) = b *)

          specialize (Hup_mark a x Hin_ms) as Hin_ms'_bis.
          assert (Hnodup_fs_ms' := Hnodup_fs_ms).
          rewrite <- Hsame_marking_s_spn in Hnodup_fs_ms'.
          rewrite Hsame_marking_s'_spn in Hnodup_fs_ms'.
          assert (Hfst_eq :
                    fst (a, b) = fst (a, x - pre_sum spn a (fired s) + post_sum spn a (fired s)))
            by (simpl; reflexivity).
          specialize (nodup_same_pair
                        (marking s') Hnodup_fs_ms'
                        (a, b)
                        (a, x - pre_sum spn a (fired s) + post_sum spn a (fired s))
                        Hin_ms' Hin_ms'_bis Hfst_eq)
            as Heq_pair.
          injection Heq_pair as Heq_bx.
          rewrite Heq_bx; assumption.

        (* In (p, n) m'' -> In (p, n) (marking s') *)
        - intros Hin_m''.

          (* Builds In (a, x) (marking s) *)
          
          specialize (in_fst_split a b m'' Hin_m'') as Hin_ms_ex.
          rewrite <- Hsame_struct' in Hin_ms_ex.
          rewrite <- Hsame_struct in Hin_ms_ex.
          apply in_fst_split_in_pair in Hin_ms_ex.
          inversion Hin_ms_ex as (x & Hin_ms).

          (* Specializes map_pre and map_post to get 
             hyp. In (a, x - pre + post) m'' *)
          
          assert (Hnodup_fs_ms := Hnodup_places).
          rewrite Hunm_place in Hnodup_fs_ms.
          rewrite Hsame_marking_s_spn in Hnodup_fs_ms.
          
          specialize (map_update_marking_pre_sub_pre
                        spn (marking s) (fired s) m'
                        Hwell_def_spn Hnodup_fs_ms Hmap_up_pre a x Hin_ms)
            as Hin_m'.

          assert (Hnodup_fs_m' := Hnodup_fs_ms).
          rewrite Hsame_struct in Hnodup_fs_m'.

          specialize (map_update_marking_post_add_post
                        spn m' (fired s) m''
                        Hwell_def_spn Hnodup_fs_m' Hmap_up_post a
                        (x - pre_sum spn a (fired s)) Hin_m')
            as Hin_m''_bis.

          (* Specializes nodup_same_pair to get (x - pre + post) = b *)

          assert (Hnodup_fs_m'' := Hnodup_fs_m').
          rewrite Hsame_struct' in Hnodup_fs_m''.
          assert (Hfst_eq :
                    fst (a, b) = fst (a, x - pre_sum spn a (fired s) + post_sum spn a (fired s)))
            by (simpl; reflexivity).
          specialize (nodup_same_pair
                        m'' Hnodup_fs_m''
                        (a, b)
                        (a, x - pre_sum spn a (fired s) + post_sum spn a (fired s))
                        Hin_m'' Hin_m''_bis Hfst_eq)
            as Heq_pair.
          injection Heq_pair as Heq_bx.
          rewrite Heq_bx.
          apply (Hup_mark a x Hin_ms).
      }

      (* Applies NoDUp_Permutation to complete the goal. *)
      apply (NoDup_Permutation Hnodup_m_s' Hnodup_m'' Heq_ms'_m'').
      
    + simpl; rewrite Heq_fired; reflexivity.      
Qed.

(** No error lemma for spn_update_marking. *)

Lemma spn_update_marking_no_error :
  forall (spn : Spn) (s : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    exists state : SpnState,
      spn_update_marking spn s = Some state.
Proof.
  intros spn s Hwell_def_spn Hwell_def_s.
  unfold spn_update_marking.

  (* Builds hyps to specialize map_update_marking_pre_no_error. *)

  explode_well_defined_spn.
  explode_well_defined_spn_state Hwell_def_s.

  (* Hyp. incl (s fired) (fst (split lneighbours)) *)
  
  unfold NoUnknownTransInLNeighbours in Hunk_tr_neigh.
  assert (Hincl_fired := Hincl_state_fired_transs);
    rewrite Hunk_tr_neigh in Hincl_fired.

  (* Hyp. forall t, neigh_of_t, In (t, neigh_of_t) (lneighbours spn) -> ... *)

  unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
  unfold NoIsolatedPlace in Hiso_place.
  assert (Hincl_flatten :
            forall (t : Trans) (neigh_of_t : Neighbours),
              In (t, neigh_of_t) (lneighbours spn) ->
              incl (flatten_neighbours neigh_of_t) (fst (split (marking s)))).
  {
    intros t neigh_of_t Hin_lneigh p Hin_p_flat.
    specialize (in_neigh_in_flatten spn t neigh_of_t p Hwell_def_spn Hin_lneigh Hin_p_flat)
      as Hin_p_lflat.
    apply Hunk_pl_neigh in Hin_p_lflat.
    rewrite <- Hsame_marking_state_spn.
    unfold NoUnmarkedPlace in Hunm_place.
    rewrite Hunm_place in Hin_p_lflat.
    assumption.
  }
  
  (* Specializes map_update_marking_pre_no_error and rewrite 
     the goal, skipping error case. *)
  
  specialize (map_update_marking_pre_no_error
                spn (fired s) (marking s)
                Hwell_def_spn Hincl_fired Hincl_flatten) as Hmap_up_pre_ex.
  inversion Hmap_up_pre_ex as (m' & Hmap_up_pre).
  rewrite Hmap_up_pre.

  (* Builds hyps. to specialize map_update_marking_post_no_error. *)
  
  specialize (map_update_marking_pre_same_marking spn (marking s) (fired s) m' Hmap_up_pre)
    as Hsame_struct.
  rewrite Hsame_struct in Hincl_flatten.
  
  (* Specializes map_update_marking_post_no_error and rewrite 
     the goal, skipping error case. *)
  
  specialize (map_update_marking_post_no_error
                spn (fired s) m'
                Hwell_def_spn Hincl_fired Hincl_flatten) as Hmap_up_post_ex.
  inversion Hmap_up_post_ex as (m'' & Hmap_up_post).
  rewrite Hmap_up_post.

  (* Instantiates the resulting state and conclude. *)
  exists {| fired := fired s; marking := m'' |}.
  reflexivity.
Qed.


(* [spn_update_marking] preserves marking structure. *)

Lemma spn_update_marking_same_marking :
  forall (spn : Spn)
         (s s' : SpnState),
    spn_update_marking spn s = Some s' ->
    MarkingHaveSameStruct s.(marking) s'.(marking).
Proof.
  intros spn s s' Hfun.

  functional induction (spn_update_marking spn s) using spn_update_marking_ind;
    intros.

  (* GENERAL CASE *)
  - specialize (map_update_marking_pre_same_marking
                spn (marking s) (fired s) m' e)
      as Hsame_struct.

    specialize (map_update_marking_post_same_marking
                  spn m' (fired s) m'' e0)
      as Hsame_struct'.

    (* Rewrite the goal with s' value. *)
    injection Hfun as Hfun.
    rewrite <- Hfun; simpl.

    transitivity (fst (split m')); [assumption | assumption].

  (* Error case. *)
  - inversion Hfun.

  (* Error case. *)
  - inversion Hfun.

Qed.
