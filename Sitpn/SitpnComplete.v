(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import falling edge and rising edge completeness lemmas. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeComplete.
Require Import Hilecop.Sitpn.SitpnRisingEdgeComplete.

(* Import lemmas on SITPN and states well-definition. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeWellDef.

(** * Completeness proof between [sitpn_cycle] and [SitpnSemantics]. *)

Theorem sitpn_cycle_complete :
  forall (sitpn : Sitpn)
         (s s' s'' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn s' ->
    IsWellDefinedSitpnState sitpn s'' ->
    SitpnSemantics sitpn s s' time_value env falling_edge ->
    SitpnSemantics sitpn s' s'' time_value env rising_edge ->
    exists (istate fstate : SitpnState),
      sitpn_cycle sitpn s time_value env = Some (istate, fstate) /\
      sitpn_state_eq s' istate /\
      sitpn_state_eq s'' fstate.
Proof.
  intros sitpn s s' s'' t env
         Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hwell_def_s''
         Hfall_spec Hrising_spec.

  (* Let's dig the function!! *)
  unfold sitpn_cycle.

  (* Specializes sitpn_falling_edge_complete then rewrites the goal *)
  specialize (sitpn_falling_edge_complete
                sitpn s s' t env Hwell_def_sitpn
                Hwell_def_s Hwell_def_s' Hfall_spec)
    as Hex_fall_fun.
  inversion_clear Hex_fall_fun as (istate & Hw_fall_fun).
  inversion_clear Hw_fall_fun as (Hfall_fun & Hsteq_s'_istate).
  rewrite Hfall_fun.
  
  (* Specializes sitpn_rising_no_error, then rewrites the goal. 
     Cannot directly rewrite the goal by specializing sitpn_rising_edge_complete. *)

  (* Builds premise IsWellDefinedSitpnState sitpn inter_state 
     to specialize sitpn_rising_edge_no_error. *)
  specialize (sitpn_falling_edge_well_def_state
                sitpn s istate t env Hwell_def_sitpn Hwell_def_s Hfall_fun)
    as Hwell_def_istate.
  specialize (sitpn_rising_edge_no_error sitpn istate Hwell_def_sitpn Hwell_def_istate)
    as Hex_rising_fun_noerr.
  inversion_clear Hex_rising_fun_noerr as (fstate & Hrising_fun_noerr).
  rewrite Hrising_fun_noerr.
  
  (* Specializes sitpn_rising_edge_complete, then shows
     that the fstate and fs verify the sitpn_state_eq relation. *)

  specialize (sitpn_rising_edge_complete
                sitpn s' s'' t env Hwell_def_sitpn Hwell_def_s'
                Hwell_def_s'' Hrising_spec)
    as Hex_rising_fun.
  inversion_clear Hex_rising_fun as (fs & Hw_rising_fun).
  inversion_clear Hw_rising_fun as (Hrising_fun & Hsteq_s''_fs).

  specialize (sitpn_rising_edge_state_eq
                sitpn s' fs istate fstate Hsteq_s'_istate
                Hrising_fun Hrising_fun_noerr)
    as Hsteq_fs_fstate.
  
  (* Instantiates states, and proves the goal. *)
  exists istate, fstate.
  split; [reflexivity |
          split; [ assumption | rewrite <- Hsteq_fs_fstate; assumption]
         ].  
Qed.
