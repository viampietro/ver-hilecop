(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(** * No error lemma for [sitpn_rising_edge]. *)

Lemma sitpn_rising_edge_no_error :
  forall (sitpn : Sitpn)
         (s : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    exists fstate : SitpnState,
      sitpn_rising_edge sitpn s = Some fstate.
Admitted.

(** * Completeness of [sitpn_rising_edge]. *)

Lemma sitpn_rising_edge_complete :
  forall (sitpn : Sitpn)
         (s s' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn s' ->
    SitpnSemantics sitpn s s' time_value env rising_edge ->
    exists fstate : SitpnState,
      sitpn_rising_edge sitpn s = Some fstate /\
      sitpn_state_eq s' fstate.
Admitted.

