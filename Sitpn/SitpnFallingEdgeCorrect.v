(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import sitpn falling edge well-defined state. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeWellDef.
Require Import Hilecop.Sitpn.SitpnWellDefTime.

(* Import lemmas about interpretation-related semantics rules. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeInterpretation.

(* Import lemmas about time-related semantics rules. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeTime.

(* Import lemmas about firing semantics rules. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeFired.

(** * Correctness of sitpn_falling_edge function. *)

Lemma sitpn_falling_edge_correct :
  forall (sitpn : Sitpn)
         (s s' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    sitpn_falling_edge sitpn s time_value env = Some s' ->
    SitpnSemantics sitpn s s' time_value env falling_edge.
Proof.
  intros sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s Hfun.
  apply SitpnSemantics_falling_edge.

  (* CASE IsWellDefinedSitpn. *)
  - assumption.

  (* CASE IsWellDefinedSitpnState sitpn s. *)
  - assumption.

  (* CASE IsWellDefinedSitpnState sitpn s'. *)
  - apply (sitpn_falling_edge_well_def_state
             sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE marking s = marking s' *)
  - apply (sitpn_falling_edge_same_marking sitpn s s' time_value env Hfun).

  (* CASE ∀ c ∈ C, cond'(c) = env(c) *)
  - apply (sitpn_falling_edge_get_condv sitpn s time_value env s' Hfun).

  (* CASE ∀a ∈ A, ∃p ∈ P, ... ⇒ ex'(a) = 1. *)
  - apply (sitpn_falling_edge_activate_actions sitpn s time_value env s' Hfun).

  (* CASE ∀a ∈ A, ∀p ∈ P, ... ⇒ ex'(a) = 0. *)
  - apply (sitpn_falling_edge_deactivate_actions sitpn s time_value env s' Hfun).

  (* CASE t ∉ sens(M) ∨ (t ∈ sens(M) ∧ (reset(t) = 1 ∨ t ∈ Fired)) ⇒ I'(t) = Is(t) - 1 *)
  - apply (sitpn_falling_edge_reset_ditvals sitpn s time_value env s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE reset(t) = 0 ∧ t ∉ Fired ∧ I(t) ≠ ψ ⇒ I'(t) = I(t) - 1 *)
  - apply (sitpn_falling_edge_inc_ditvals sitpn s time_value env s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE reset(t) = 0 ∧ t ∉ Fired ∧ I(t) = ψ ⇒ I'(t) = I(t) *)
  - apply (sitpn_falling_edge_same_blocked sitpn s time_value env s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE reset s = reset s' *)
  - apply (sitpn_falling_edge_same_reset sitpn s s' time_value env Hfun).

  (* CASE t ∉ firable(s') ⇒ t ∉ Fired' *)
  - apply (sitpn_falling_edge_not_firable_not_fired sitpn s time_value env s' Hwell_def_sitpn Hwell_def_s Hfun).
    
  (* CASE t ∈ firable(s') ∧ t ∈ sens(M -∑pre) ⇒ t ∈ Fired' *)
  - apply (sitpn_falling_edge_sens_by_residual sitpn s time_value env s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE t ∈ firable(s') ∧ t ∉ sens(M -∑pre) ⇒ t ∉ Fired' *)
  - apply (sitpn_falling_edge_not_sens_by_residual sitpn s time_value env s' Hwell_def_sitpn Hwell_def_s Hfun).
    
Qed.

