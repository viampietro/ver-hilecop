(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.


(** * Correctness of sitpn_rising_edge function. *)

Lemma sitpn_rising_edge_correct :
  forall (sitpn : Sitpn)
         (s s' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    sitpn_rising_edge sitpn s = Some s' ->
    SitpnSemantics sitpn s s' time_value env rising_edge.
Proof.
Admitted.
