(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import lemmas about time. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeTimeComplete.

(* Import lemmas about fired. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeFiredComplete.

(** * Completeness of [sitpn_falling_edge]. *)

Lemma sitpn_falling_edge_complete :
  forall (sitpn : Sitpn)
         (s s' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn s' ->
    SitpnSemantics sitpn s s' time_value env falling_edge ->
    exists istate : SitpnState,
      sitpn_falling_edge sitpn s time_value env = Some istate /\
      sitpn_state_eq s' istate.
Proof.
  intros sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s
         Hwell_def_s' Hspec.

  (* Digs the function sitpn_falling_edge. *)
  unfold sitpn_falling_edge.

  (* Specializes update_time_intervals_complete, and
     rewrites the goal. *)  
  specialize (update_time_intervals_complete
                sitpn s s' time_value env (d_intervals s) []
                Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec)
    as Hex_update_t_itvals.
  inversion_clear Hex_update_t_itvals as (ditvals' & Hw_update_t_itvals).
  inversion_clear Hw_update_t_itvals as (Hupdate_t_itvals & Hperm_ditvals).
  rewrite Hupdate_t_itvals.

  (* Makes the goal more readable. *)
  set (tmp_state := {|
            fired := [];
            marking := marking s;
            d_intervals := ditvals';
            reset := reset s;
            cond_values := get_condition_values (conditions sitpn) time_value env [];
            exec_a := get_action_states sitpn s (actions sitpn) [];
            exec_f := exec_f s |}).
  
Admitted.
