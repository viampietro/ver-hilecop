(* Import Sitpn material. *)

Require Import simpl.Sitpn.
Require Import simpl.SitpnTokenPlayer.
Require Import simpl.SitpnSemantics.

(* Import misc. lemmas and tactics. *)

Require Import simpl.SitpnTactics.

(* Import lemmas about fired and well-definedness *)

Require Import simpl.SitpnWellDefFired.
Require Import simpl.SitpnWellDefMarking.
Require Import simpl.SitpnWellDefTime.
Require Import simpl.SitpnWellDefInterpretation.

(** * sitpn_rising_edge and well-definedness of states. *)

(** [sitpn_rising_edge] returns a SitpnState that is well-defined. *)

Lemma sitpn_rising_edge_well_def_state :
  forall (sitpn : Sitpn)
         (s s' : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    sitpn_rising_edge sitpn s = Some s' ->
    IsWellDefinedSitpnState sitpn s'.
Proof.
  intros sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun.
  unfold IsWellDefinedSitpnState.

  (* CASE incl (fired s') (transs sitpn) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_rising_edge_same_fired sitpn s s' Hfun) as Heq_fired.
  rewrite <- Heq_fired; assumption.

  (* CASE NoDup (fired s') *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_rising_edge_same_fired sitpn s s' Hfun) as Heq_fired.
  rewrite <- Heq_fired; assumption.

  (* CASE places = fst (split (marking s')) *)
  split.
  apply (sitpn_rising_edge_same_struct_marking sitpn s s' Hwell_def_s Hfun).

  (* CASE t ∈ (d_intervals s') ⇔ t ∈ Ti *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_rising_edge_same_struct_ditvals sitpn s s' Hfun)
    as Heq_fs_ditvals.
  rewrite <- Heq_fs_ditvals; assumption.

  (* CASE NoDup (fst (split (d_intervals s'))) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_rising_edge_same_struct_ditvals sitpn s s' Hfun)
    as Heq_fs_ditvals.
  rewrite <- Heq_fs_ditvals; assumption.

  (* CASE t ∈ (reset s') ⇔ t ∈ Ti *)
  split.
  apply (sitpn_rising_edge_reset_incl_transs sitpn s s' Hwell_def_s Hfun).

  (* CASE NoDup (fst (split (reset s'))) *)
  split.
  apply (sitpn_rising_edge_nodup_reset sitpn s s' Hwell_def_s Hfun).
  
  (* CASE C = fst (split (cond_values s')) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_rising_edge_same_condv sitpn s s' Hfun)
    as Heq_fs_condv;
    rewrite <- Heq_fs_condv;
    assumption.
  
  (* CASE A = fst (split (exec_a s')) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_rising_edge_same_actions sitpn s s' Hfun)
    as Heq_fs_actions;
    rewrite <- Heq_fs_actions;
    assumption.

  (* CASE F = fst (split (exec_f s')) *)
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_rising_edge_same_struct_functions sitpn s s' Hfun) as Heq_execf.
  assumption.
  
Qed.
