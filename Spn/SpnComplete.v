(* Import Spn's types, program and specification. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Spn.SpnTokenPlayer.
Require Import Hilecop.Spn.SpnSemantics.

(* Import useful tactics and general-purpose lemmas. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Spn.SpnTactics.

(* Import core lemmas necessary for Spn's correctness proof. *)

Require Import Hilecop.Spn.SpnCoreLemmas.

(* Import lemmas about spn_map_fire's completeness and correctness. *)

Require Import Hilecop.Spn.SpnMapFireCorrect.
Require Import Hilecop.Spn.SpnMapFireComplete.

(* Import lemmas about spn_update_marking's completeness. *)

Require Import Hilecop.Spn.SpnUpdateMarkingCorrect.
Require Import Hilecop.Spn.SpnUpdateMarkingComplete.

(** [spn_update_marking] is (almost) a morphism from [spnstate_eq] to [spnstate_eq]. 
 *  Almost because [spn_update_marking] returns an [option SpnState], and not a [SpnState]. 
 *  
 *  Needed to prove [spn_semantics_complete].
 *)

Lemma spn_update_marking_spnstate_eq_morph :
  forall (spn : Spn)
    (s s' state state' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn state ->
    spnstate_eq s state ->
    spn_update_marking spn s = Some s' ->
    spn_update_marking spn state = Some state' ->
    spnstate_eq s' state'.
Proof.
  intros spn s s' state state' Hwell_def_spn Hwell_def_s Hwell_def_st
         Hsteq_s_state Hup_mark_s Hup_mark_state.

  unfold spnstate_eq; split.
  
  (* CASE Permutation (marking s') (marking state') *)
  - explode_well_defined_spn.
    explode_well_defined_spn_state Hwell_def_s.
    rename Hsame_marking_state_spn into Hsame_marking_s_spn,
           Hincl_state_fired_transs into Hincl_s_fired_transs,
           Hnodup_state_fired into Hnodup_s_fired,
           Hwell_def_state into Hwell_def_s.
    explode_well_defined_spn_state Hwell_def_st.
    
    (* Builds hyps. to specialize NoDup_Permutation. *)

    (* Hyps. MarkingHaveSameStruct from spn_update_marking. *)

    specialize (spn_update_marking_same_marking spn s s' Hup_mark_s)
      as Hsame_struct_ss'.
    specialize (spn_update_marking_same_marking spn state state' Hup_mark_state)
      as Hsame_struct_sstate'.
    
    (* Hyp. NoDup (marking s') *)
    
    assert (Hnodup_m_s' := Hnodup_places).
      
    unfold NoUnmarkedPlace in *.
    unfold NoDupPlaces in *.
    rewrite Hunm_place in Hnodup_m_s'.
    rewrite Hsame_marking_s_spn in Hnodup_m_s'.
    rewrite Hsame_struct_ss' in Hnodup_m_s'.
    assert (Hnodup_fs_m_s' := Hnodup_m_s').
    apply nodup_fst_split in Hnodup_m_s'.

    (* Hyp. NoDup (marking state') *)

    assert (Hnodup_m_st' := Hnodup_places).
    rewrite Hunm_place in Hnodup_m_st'.
    rewrite Hsame_marking_state_spn in Hnodup_m_st'.
    rewrite Hsame_struct_sstate' in Hnodup_m_st'.
    assert (Hnodup_fs_m_st' := Hnodup_m_st').
    apply nodup_fst_split in Hnodup_m_st'.

    (* Hyp. In (p, n) (marking s') <-> In (p, n) (marking state') *)

    assert (Heq_ms'_mst' :
              forall (c : (Place * nat)), In c (marking s') <-> In c (marking state')).
    {
      intro c; induction c; split.
      
      (* In (p, n) (marking s') -> In (p, n) (marking state') *)
      - intros Hin_ms'.

        (* Specializes spn_update_marking_sub_pre_add_post. *)

        specialize (spn_update_marking_sub_pre_add_post
                      spn s s' Hwell_def_spn Hwell_def_s Hup_mark_s)
          as Hspec_ms'.
        specialize (spn_update_marking_sub_pre_add_post
                      spn state state' Hwell_def_spn Hwell_def_state Hup_mark_state)
          as Hspec_mstate'.
        
        (* Builds In (a, x) (marking s) *)
        
        specialize (in_fst_split a b (marking s') Hin_ms') as Hin_ms_ex.
        rewrite <- Hsame_struct_ss' in Hin_ms_ex.
        apply in_fst_split_in_pair in Hin_ms_ex.
        inversion Hin_ms_ex as (x & Hin_ms).

        (* Specializes Hspec_ms' to get In (a, x - pre + post) (marking s') *)
        specialize (Hspec_ms' a x Hin_ms) as Hin_ms'_bis.

        (* Builds b = x - pre + post *)
        assert (Hfst_eq :
                  fst (a, b) = fst (a, x - pre_sum spn a (fired s) + post_sum spn a (fired s)))
          by (simpl; reflexivity).
        specialize (nodup_same_pair
                      (marking s') Hnodup_fs_m_s'
                      (a, b)
                      (a, x - pre_sum spn a (fired s) + post_sum spn a (fired s))
                      Hin_ms' Hin_ms'_bis Hfst_eq)
          as Heq_pair.
        injection Heq_pair as Heq_bx.
        inversion Hsteq_s_state as (Hperm_m & Hperm_fired).

        (* Builds In (a, x) (marking state) by rewriting Hperm_m. *)
        assert (Hin_mstate := Hin_ms).
        rewrite Hperm_m in Hin_mstate.
        specialize (Hspec_mstate' a x Hin_mstate) as Hin_mstate'.
        
        (* Builds pre_sum (fired s) = pre_sum (fired state). 
         * Deduced from Permutation (fired s) (fired state). *)
        
        assert (Hequiv_fired: forall t : Trans, In t (fired s) <-> In t (fired state)) by
            (intros t; rewrite Hperm_fired; reflexivity).
        
        specialize (pre_sum_eq_iff_incl
                      spn a (fired s) (fired state)
                      Hnodup_s_fired Hnodup_state_fired Hequiv_fired)
          as Heq_presum.

        (* Builds post_sum (fired s) = post_sum (fired state). 
         * Deduced from Permutation (fired s) (fired state). *)

        specialize (post_sum_eq_iff_incl
                      spn a (fired s) (fired state)
                      Hnodup_s_fired Hnodup_state_fired Hequiv_fired)
          as Heq_postsum.
        
        (* Rewrites the goal, then concludes. *)
        rewrite Heq_bx, Heq_presum, Heq_postsum. assumption.
        
      (* In (p, n) (marking state') -> In (p, n) (marking s') *)
      - intros Hin_mstate'.

        (* Specializes spn_update_marking_sub_pre_add_post. *)

        specialize (spn_update_marking_sub_pre_add_post
                      spn s s' Hwell_def_spn Hwell_def_s Hup_mark_s)
          as Hspec_ms'.
        specialize (spn_update_marking_sub_pre_add_post
                      spn state state' Hwell_def_spn Hwell_def_state Hup_mark_state)
          as Hspec_mstate'.
        
        (* Builds In (a, x) (marking state) *)
        
        specialize (in_fst_split a b (marking state') Hin_mstate') as Hin_mstate_ex.
        rewrite <- Hsame_struct_sstate' in Hin_mstate_ex.
        apply in_fst_split_in_pair in Hin_mstate_ex.
        inversion Hin_mstate_ex as (x & Hin_mstate).

        (* Specializes Hspec_mstate' to get 
           In (a, x - pre + post) (marking state') *)
        specialize (Hspec_mstate' a x Hin_mstate) as Hin_mstate'_bis.

        (* Builds b = x - pre + post *)
        assert (Hfst_eq :
                  fst (a, b) = fst (a, x - pre_sum spn a (fired s) + post_sum spn a (fired s)))
          by (simpl; reflexivity).
        specialize (nodup_same_pair
                      (marking state') Hnodup_fs_m_st'
                      (a, b)
                      (a, x - pre_sum spn a (fired state) + post_sum spn a (fired state))
                      Hin_mstate' Hin_mstate'_bis Hfst_eq)
          as Heq_pair.
        injection Heq_pair as Heq_bx.
        inversion Hsteq_s_state as (Hperm_m & Hperm_fired).

        (* Builds In (a, x) (marking s) by rewriting Hperm_m. *)
        assert (Hin_ms := Hin_mstate).
        rewrite <- Hperm_m in Hin_ms.
        specialize (Hspec_ms' a x Hin_ms) as Hin_ms'.
        
        (* Builds pre_sum (fired s) = pre_sum (fired state). 
         * Deduced from Permutation (fired s) (fired state). *)
        
        assert (Hequiv_fired: forall t : Trans, In t (fired s) <-> In t (fired state)) by
            (intros t; rewrite Hperm_fired; reflexivity).
        
        specialize (pre_sum_eq_iff_incl
                      spn a (fired s) (fired state)
                      Hnodup_s_fired Hnodup_state_fired Hequiv_fired)
          as Heq_presum.

        (* Builds post_sum (fired s) = post_sum (fired state). 
         * Deduced from Permutation (fired s) (fired state). *)

        specialize (post_sum_eq_iff_incl
                      spn a (fired s) (fired state)
                      Hnodup_s_fired Hnodup_state_fired Hequiv_fired)
          as Heq_postsum.
        
        (* Rewrites the goal, then concludes. *)
        rewrite Heq_bx, <- Heq_presum, <- Heq_postsum. assumption.
    }

    (* Applies NoDUp_Permutation to complete the goal. *)
    apply (NoDup_Permutation Hnodup_m_s' Hnodup_m_st' Heq_ms'_mst').

  (* CASE Permutation (fired s') (fired state') *)
  - inversion Hsteq_s_state as (Hperm_m & Hperm_fired).
    (* Builds (fired s) = (fired s') and 
       (fired state) = (fired state') *)
    specialize (spn_update_marking_same_fired
                  spn s s' Hup_mark_s)
      as Heq_fired_ss'.
    specialize (spn_update_marking_same_fired
                  spn state state' Hup_mark_state)
      as Heq_fired_sstate'.

    rewrite <- Heq_fired_ss', <- Heq_fired_sstate'.
    assumption.    
Qed.

(** * Completeness proof between spn_cycle and SpnSemantics. *)

Theorem spn_semantics_complete :
  forall (spn : Spn)
    (s s' s'' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    IsWellDefinedSpnState spn s'' ->
    SpnSemantics spn s s' falling_edge ->
    SpnSemantics spn s' s'' rising_edge ->
    exists (istate fstate : SpnState),
      spn_cycle spn s = Some (istate, fstate) /\
      spnstate_eq s' istate /\
      spnstate_eq s'' fstate.
Proof.
  intros spn s s' s'' Hwell_def_spn Hwell_def_s
         Hwell_def_s' Hwell_def_s'' Hfalling_edge Hrising_edge.

  unfold spn_cycle.

  (* Specializes spn_map_fire_complete and rewrite the goal,
     therefore skipping the error case. *)
  specialize (spn_map_fire_complete spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s' Hfalling_edge)
    as Hspn_map_fire_ex.
  inversion Hspn_map_fire_ex as (istate & Hspn_map_fire_w).
  inversion Hspn_map_fire_w as (Hspn_map_fire & Hsteq_s').
  rewrite Hspn_map_fire.

  (* Specializes spn_update_marking_no_error and rewrite the goal,
     therefore skipping the error case. *)

  (* Need hyp. IsWellDefinedSpnState spn istate. *)
  specialize (spn_map_fire_well_defined_state spn s istate Hwell_def_spn Hwell_def_s Hspn_map_fire)
    as Hwell_def_istate.

  specialize (spn_update_marking_no_error spn istate Hwell_def_spn Hwell_def_istate)
    as Hup_mark_ex.
  inversion Hup_mark_ex as (fstate & Hup_mark_istate).
  rewrite Hup_mark_istate.

  (* Instantiates state couple with istate and fstate. *)
  exists istate, fstate.

  (* Splits and solves each branch of the conjucntion. *)
  split. reflexivity. split.

  (* Solves spnstate_eq s' istate, trivial. *)
  - assumption.

  (* Solves spnstate_eq s'' fstate, harder. *)
  - clear Hup_mark_ex Hspn_map_fire_ex Hspn_map_fire_w.
    
    (* Specializes spn_update_marking_complete. *)
    specialize (spn_update_marking_complete
                  spn s' s'' Hwell_def_spn Hwell_def_s' Hwell_def_s'' Hrising_edge)
      as Hspn_update_marking_ex.
    inversion Hspn_update_marking_ex as (final_state & Hspn_update_marking_w).
    inversion Hspn_update_marking_w as (Hspn_update_marking & Hsteq_s'').
    clear Hspn_update_marking_ex Hspn_update_marking_w.

    (* We need to specialize [spn_update_marking_spnstate_eq_morph] 
     * to deduce spnstate_eq fstate final_state, 
     * then deduce the goal by transitivity. *)
    specialize (spn_update_marking_spnstate_eq_morph
                  spn s' final_state istate fstate
                  Hwell_def_spn Hwell_def_s' Hwell_def_istate
                  Hsteq_s'
                  Hspn_update_marking
                  Hup_mark_istate) as Hsteq_s'_istate.
    transitivity final_state; [assumption | assumption].                  
Qed.
    
