(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.
Require Import Hilecop.Sitpn.SitpnTactics.

(* Import misc. lemmas, tactics and definitions. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Utils.HilecopDefinitions.

(* Import lemmas about marking. *)

Require Import Hilecop.Sitpn.SitpnWellDefMarking.
Require Import Hilecop.Sitpn.SitpnRisingEdgeMarkingComplete.

(* Import lemmas about time. *)

Require Import Hilecop.Sitpn.SitpnRisingEdgeTimeComplete.

(** * Completeness of [sitpn_rising_edge]. *)

Lemma sitpn_rising_edge_complete :
  forall (sitpn : Sitpn)
         (s s' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool)
         (istate : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn s' ->
    SitpnSemantics sitpn s s' time_value env rising_edge ->
    sitpn_state_eq s istate ->
    exists fstate : SitpnState,
      sitpn_rising_edge sitpn istate = Some fstate /\
      sitpn_state_eq s' fstate.
Proof.
  intros sitpn s s' time_value env istate
         Hwell_def_sitpn Hwell_def_s Hwell_def_s'
         Hspec Hsteq_s_istate.

  unfold sitpn_rising_edge.

  (* Specializes map_update_marking_pre_complete, then rewrites the goal. *)

  assert (Hperm_mistate : Permutation (places sitpn) (HilecopDefinitions.fs (marking istate))).
  {
    explode_well_defined_sitpn_state Hwell_def_s.
    apply proj1 in Hsteq_s_istate.
    rewrite Hwf_state_marking.
    rewrite <- Hsteq_s_istate.
    unfold HilecopDefinitions.fs.
    reflexivity. 
  }
  
  assert (Hincl_fistate : incl (fired istate) (fired s)).
  {
    explode_well_defined_sitpn_state Hwell_def_s.
    unfold sitpn_state_eq in Hsteq_s_istate.
    apply proj2, proj1 in Hsteq_s_istate.
    intros a Hin_fistate.
    rewrite <- Hsteq_s_istate in Hin_fistate.
    assumption.
  }
  
  assert (Hnodup_fistate : NoDup (fired istate)).
  {
    explode_well_defined_sitpn_state Hwell_def_s.
    unfold sitpn_state_eq in Hsteq_s_istate.
    apply proj2, proj1 in Hsteq_s_istate.
    rewrite Hsteq_s_istate in Hnodup_state_fired.
    assumption.
  }  
  
  specialize (map_update_marking_pre_complete
                sitpn s s' time_value env (fired istate) (marking istate)
                Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                Hperm_mistate Hincl_fistate Hnodup_fistate)
    as Hex_map_up_mark_pre.

  inversion_clear Hex_map_up_mark_pre as (transient_marking & Hw).
  inversion_clear Hw as (Hmap_up_mark_pre & Hdef_tm).

  rewrite Hmap_up_mark_pre.

  (* Specializes map_update_marking_post_complete, then rewrites the goal. *)

  assert (Hperm_tm : Permutation (places sitpn) (fs transient_marking)).
  {
    specialize (map_update_marking_pre_same_marking
                  sitpn (marking istate) (fired istate)
                  transient_marking Hmap_up_mark_pre)
      as Heq_fsmi_fstm.
    unfold fs.
    rewrite <- Heq_fsmi_fstm.
    assumption.
  }
  
  specialize (map_update_marking_post_complete
                sitpn s s' time_value env (fired istate) transient_marking
                Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                Hperm_tm Hincl_fistate Hnodup_fistate)
    as Hex_map_up_mark_post.

  inversion_clear Hex_map_up_mark_post as (final_marking & Hw).
  inversion_clear Hw as (Hmap_up_mark_post & Hdef_fm).

  rewrite Hmap_up_mark_post.
  
  (* Specializes get_blocked_and_reset_complete, then rewrites the goal. *)

  specialize (get_blocked_and_reset_complete
                sitpn s s' time_value env Hwell_def_sitpn
                Hwell_def_s Hwell_def_s' Hspec
                istate (d_intervals istate) transient_marking [] []
                Hsteq_s_istate) as Hex_get_bl_and_reset.
  simpl in Hex_get_bl_and_reset.

  (* Builds hypotheses to deeper specialize get_blocked_and_reset_complete *)

  unfold sitpn_state_eq in Hsteq_s_istate.
  
  assert (Hincl_ditstate_ds : incl (d_intervals istate) (d_intervals s)).
  {
    do 2 (apply proj2 in Hsteq_s_istate); apply proj1 in Hsteq_s_istate.
    intros p Hin_distate; rewrite Hsteq_s_istate; assumption.
  }

  assert (Hperm_fs_ditvals : Permutation (fs (d_intervals istate)) (fs (d_intervals s'))).
  {
    do 2 (apply proj2 in Hsteq_s_istate); apply proj1 in Hsteq_s_istate.
    rewrite <- Hsteq_s_istate.

    (* Strategy: apply NoDup_Permutation. *)

    assert (Hnodup_ditvals_s : NoDup (fs (d_intervals s)))
      by (explode_well_defined_sitpn_state Hwell_def_s; assumption).

    assert (Hnodup_ditvals_s' : NoDup (fs (d_intervals s')))
      by (explode_well_defined_sitpn_state Hwell_def_s'; assumption).

    assert (Hequiv_ditvals : forall t : Trans, In t (fs (d_intervals s)) <-> In t (fs (d_intervals s'))).
    {
      intros t; split; intros Hin;
        (explode_well_defined_sitpn_state Hwell_def_s;
         rewrite <- (Hwf_state_ditvals t) in Hin;
         clear_well_defined_sitpn_state;
         explode_well_defined_sitpn_state Hwell_def_s';
         rewrite (Hwf_state_ditvals t) in Hin)
        ||
        (explode_well_defined_sitpn_state Hwell_def_s';
         rewrite <- (Hwf_state_ditvals t) in Hin;
         clear_well_defined_sitpn_state;
         explode_well_defined_sitpn_state Hwell_def_s;
         rewrite (Hwf_state_ditvals t) in Hin);
        assumption.
    }

    apply (NoDup_Permutation Hnodup_ditvals_s Hnodup_ditvals_s' Hequiv_ditvals).
  }

  assert (Hincl_nil_ditvals : incl [] (d_intervals s'))
    by (intros t Hin_nil; inversion Hin_nil).

  assert (Hnodup_fs_ditvals : NoDup (fs (d_intervals istate))).
  {
    explode_well_defined_sitpn_state Hwell_def_s.
    do 2 (apply proj2 in Hsteq_s_istate); apply proj1 in Hsteq_s_istate.
    rewrite <- Hsteq_s_istate.
    assumption.
  }

  assert (Hperm_fs_reset_s' : Permutation (fs (d_intervals istate)) (fs (reset s'))).
  {
    do 2 (apply proj2 in Hsteq_s_istate); apply proj1 in Hsteq_s_istate.

    (* Strategy: apply NoDup_Permutation. *)

    assert (Hnodup_ditvals_istate : NoDup (fs (d_intervals istate)))
      by (explode_well_defined_sitpn_state Hwell_def_s;
          rewrite <- Hsteq_s_istate;
          assumption).

    assert (Hnodup_reset_s' : NoDup (fs (reset s')))
      by (explode_well_defined_sitpn_state Hwell_def_s'; assumption).

    assert (Hequiv_ditvals : forall t : Trans, In t (fs (d_intervals istate)) <-> In t (fs (reset s'))).
    {
      intros t; split; intros Hin;
      (rewrite <- Hsteq_s_istate in Hin;
       explode_well_defined_sitpn_state Hwell_def_s;
       rewrite <- (Hwf_state_ditvals t) in Hin;
       clear_well_defined_sitpn_state;
       explode_well_defined_sitpn_state Hwell_def_s';
         rewrite (Hwf_state_reset t) in Hin)
      ||
      (rewrite <- Hsteq_s_istate;
       explode_well_defined_sitpn_state Hwell_def_s';
       rewrite <- (Hwf_state_reset t) in Hin;
       clear_well_defined_sitpn_state;
       explode_well_defined_sitpn_state Hwell_def_s;
       rewrite (Hwf_state_ditvals t) in Hin);
      assumption.
    }

    apply (NoDup_Permutation Hnodup_ditvals_istate Hnodup_reset_s' Hequiv_ditvals).
  }

  assert (Hincl_nil_reset : incl [] (reset s'))
    by (intros t Hin_nil; inversion Hin_nil).

  assert (Hperm_fs_m_tm : Permutation (fs (marking s)) (fs transient_marking)).
  {
    explode_well_defined_sitpn_state Hwell_def_s.
    unfold fs.
    rewrite <- Hwf_state_marking.
    assumption.
  }
  
  specialize (Hex_get_bl_and_reset
                Hincl_ditstate_ds Hperm_fs_ditvals Hincl_nil_ditvals Hnodup_fs_ditvals
                Hperm_fs_reset_s' Hincl_nil_reset Hnodup_fs_ditvals Hperm_fs_m_tm Hdef_tm).

  (* Explodes the newly-built hypothesis and rewrites the goal. *)
  inversion_clear Hex_get_bl_and_reset as (ditvals' & Hex_get_bl_and_reset').
  inversion_clear Hex_get_bl_and_reset' as (reset' & Hw).
  inversion_clear Hw as (Hget_bl_and_reset & Hw_perm).
  inversion_clear Hw_perm as (Hperm_reset' & Hperm_ditvals').
  rewrite Hget_bl_and_reset.

  (* Instantiates fstate. *)
  exists ({|
             fired := fired istate;
             marking := final_marking;
             d_intervals := ditvals';
             reset := reset';
             cond_values := cond_values istate;
             exec_a := exec_a istate;
             exec_f := get_function_states sitpn istate (functions sitpn) [] |}).

  (* Then proves each branch of the goal. *)
  repeat split; simpl.

  (* Case Permutation (marking s') final_marking *)
  
  - specialize (map_update_marking_complete
                  sitpn s s' time_value env (fired istate) (marking istate)
                  transient_marking final_marking Hwell_def_sitpn Hwell_def_s
                  Hwell_def_s' Hspec Hdef_tm Hdef_fm) as Hmap_up_mark.

    (* Builds more hypotheses to deeper specialize map_update_marking_complete *)

    specialize (proj1 Hsteq_s_istate) as Hperm_marking.
    specialize (proj1 (proj2 Hsteq_s_istate)) as Hperm_fired.

    assert (Heq_fsfm_fsmis : fs final_marking = fs (marking istate)).
    {
      specialize (map_update_marking_pre_same_marking
                    sitpn (marking istate) (fired istate)
                    transient_marking Hmap_up_mark_pre) as Heq_fsmis_fstm.
      specialize (map_update_marking_post_same_marking
                    sitpn transient_marking (fired istate)
                    final_marking Hmap_up_mark_post) as Heq_fstm_fsfm.
      symmetry.
      transitivity (fst (split transient_marking)); [assumption|assumption].
    }

    assert (Hnodup_fm : NoDup final_marking).
    {
      explode_well_defined_sitpn.
      explode_well_defined_sitpn_state Hwell_def_s.
      unfold NoDupPlaces in *.
      rewrite Hwf_state_marking in Hnodup_places.
      assert (Hnodup_fs : NoDup (fs (marking s))) by (unfold fs; assumption).
      clear_well_defined_sitpn.
      clear_well_defined_sitpn_state.
      rewrite Hperm_marking in Hnodup_fs.
      rewrite <- Heq_fsfm_fsmis in Hnodup_fs.
      apply (nodup_fst_split final_marking Hnodup_fs).
    }

    (* Then applies to the goal. *)
    symmetry.
    apply (Hmap_up_mark Hperm_marking Hperm_fired Heq_fsfm_fsmis Hnodup_fm).
Admitted.

