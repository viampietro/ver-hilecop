(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import lemmas about well-definition. *)

Require Import Hilecop.Sitpn.SitpnRisingEdgeWellDef.
Require Import Hilecop.Sitpn.SitpnWellDefFired.
Require Import Hilecop.Sitpn.SitpnWellDefInterpretation.

(* Import lemmas about marking *)

Require Import Hilecop.Sitpn.SitpnRisingEdgeMarking.

(* Import lemmas about time *)

Require Import Hilecop.Sitpn.SitpnRisingEdgeTime.

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
  intros sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s Hfun.
  apply SitpnSemantics_rising_edge.

  (* CASE IsWellDefinedSitpn *)
  - assumption.

  (* CASE IsWellDefinedSitpnState sitpn s *)
  - assumption.

  (* CASE IsWellDefinedSitpnState sitpn s' *)
  - apply (sitpn_rising_edge_well_def_state
             sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE fired s = fired s' *)
  - apply (sitpn_rising_edge_same_fired sitpn s s' Hfun).

  (* CASE M' = M - pre + post *)
  - apply (sitpn_rising_edge_sub_pre_add_post sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE not sens by transient ⇒ reset' = true *)
  - apply (sitpn_rising_edge_decide_reset sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE sens by transient ⇒ reset' = false *)
  - apply (sitpn_rising_edge_decide_no_reset sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE 0 ∈ I(t) ∧ t ∉ fired ⇒ I'(t) = ψ *)
  - apply (sitpn_rising_edge_decide_blocked sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE 0 ∉ I(t) ∨ t ∈ fired ⇒ I'(t) = I(t) *)
  - apply (sitpn_rising_edge_decide_not_blocked sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE cond_values s = cond_values s' *)
  - apply (sitpn_rising_edge_same_condv sitpn s s' Hfun).

  (* CASE exec_a s = exec_a s' *)
  - apply (sitpn_rising_edge_same_actions sitpn s s' Hfun).

  (* CASE ∀f, ∃t ∈ T, F(t, f) = true ∧ t ∈ fired ⇒ ex'(f) = true *)
  - admit.

  (* CASE ∀f, ∀t ∈ T, F(t, f) = false ∨ t ∉ fired ⇒ ex'(f) = true *)
  - admit.
    
Admitted.
