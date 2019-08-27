(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

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
  inversion Hspec.
Admitted.

