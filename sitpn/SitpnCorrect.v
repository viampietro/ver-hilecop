(* Import Sitpn material. *)

Require Import Sitpn.
Require Import SitpnTokenPlayer.
Require Import SitpnSemantics.

(* Import falling edge correctness lemmas. *)

Require Import SitpnFallingEdgeCorrect.
Require Import SitpnFallingEdgeWellDef.

(* Import rising edge correctness lemmas. *)

Require Import SitpnRisingEdgeCorrect.

(** * Correctness theorem for SITPN token player program. *)

Theorem sitpn_cycle_correct :
  forall (sitpn : Sitpn)
         (s s' s'' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    sitpn_cycle sitpn s time_value env = Some (s', s'') ->
    SitpnSemantics sitpn s s' time_value env falling_edge /\
    SitpnSemantics sitpn s' s'' time_value env rising_edge.
Proof.
  intros sitpn s s' s'' time_value env Hwell_def_sitpn Hwell_def_s Hfun.
  functional induction (sitpn_cycle sitpn s time_value env) using sitpn_cycle_ind.
  (* GENERAL CASE, all went well. *)
  - injection Hfun as Heq_s' Heq_s''.
    split.
    
    (* CASE falling edge correct. *)
    + rewrite <- Heq_s'.
      apply (sitpn_falling_edge_correct sitpn s s'0 time_value env
                                        Hwell_def_sitpn Hwell_def_s e).
      
    (* CASE rising edge correct. *)
    + specialize (sitpn_falling_edge_well_def_state
                    sitpn s s'0 time_value env Hwell_def_sitpn Hwell_def_s e)
        as Hwell_def_s'.
      rewrite <- Heq_s', <- Heq_s''.
      apply (sitpn_rising_edge_correct
               sitpn s'0 s''0 time_value env Hwell_def_sitpn Hwell_def_s' e0).
      
  (* ERROR CASE. *)
  - inversion Hfun.
    
  (* ERROR CASE. *)
  - inversion Hfun.
Qed.
