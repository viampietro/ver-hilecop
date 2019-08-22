(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Misc. imports. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Omega.
Require Import Classical_Prop.

(** * Completeness of [sitpn_map_fire]. *)

Section SitpnMapFireComplete.

  (** Completeness lemma for sitpn_map_fire. *)

  Lemma sitpn_map_fire_complete :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (tmp_state : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env falling_edge ->

      (* Properties and well-definition of tmp_state. *)
      IsWellDefinedSitpnState sitpn tmp_state ->
      (marking tmp_state) = (marking s) ->
      Permutation (d_intervals tmp_state) (d_intervals s') ->
      Permutation (cond_values tmp_state) (cond_values s') ->
      
      exists final_fired : list Trans,
        sitpn_map_fire sitpn tmp_state = Some final_fired
        /\ Permutation final_fired (fired s').
  Proof.
  Admitted.
  
End SitpnMapFireComplete.

        
