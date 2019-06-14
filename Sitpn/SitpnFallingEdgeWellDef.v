(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import lemmas on synchronous execution rules. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeFired.

(* Import Sitpn tactics. *)

Require Import Hilecop.Sitpn.SitpnTactics.

(* Import lemmas on time rules. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeTime.

(* Import lemmas on interpretation rules. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeInterpretation.

(** * sitpn_falling_edge and well-definedness of states. *)

(** [sitpn_falling_edge] returns a SitpnState with the same marking 
    as the starting state. *)

Lemma sitpn_falling_edge_same_marking :
  forall (sitpn : Sitpn)
         (s s' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    sitpn_falling_edge sitpn s time_value env = Some s' ->
    (marking s) = (marking s').
Proof.
  intros sitpn s s' time_value env Hfun.
  functional induction (sitpn_falling_edge sitpn s time_value env)
             using sitpn_falling_edge_ind.

  (* GENERAL CASE, all went well. *)
  - simpl in Hfun; injection Hfun as Heq_s'; rewrite <- Heq_s'.
    simpl; reflexivity.

  (* ERROR CASE *)
  - inversion Hfun.

  (* ERROR CASE *)
  - inversion Hfun.
Qed.
  
(** [sitpn_falling_edge] returns a SitpnState that is well-defined. *)

Lemma sitpn_falling_edge_well_def_state :
  forall (sitpn : Sitpn)
         (s s' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    sitpn_falling_edge sitpn s time_value env = Some s' ->
    IsWellDefinedSitpnState sitpn s'.
Proof.
  intros sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s Hfun.
  unfold IsWellDefinedSitpnState.
  
  (* CASE incl (fired s') (transs sitpn) *)
  split.
  apply (sitpn_falling_edge_incl_fired
           sitpn s s' time_value env Hwell_def_sitpn Hfun).

  (* CASE NoDup (fired s') *)
  split.
  apply (sitpn_falling_edge_nodup_fired
           sitpn s s' time_value env Hwell_def_sitpn Hfun).           

  (* CASE places = fst (split (marking s')) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_marking sitpn s s' time_value env Hfun) as Heq_m.
  rewrite <- Heq_m; assumption.

  (* CASE t ∈ (d_intervals s') ⇔ t ∈ Ti *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_struct_ditvals sitpn s s' time_value env Hfun)
    as Heq_fs_ditvals.
  rewrite <- Heq_fs_ditvals; assumption.

  (* CASE NoDup (fst (split (d_intervals s'))) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_struct_ditvals sitpn s s' time_value env Hfun)
    as Heq_fs_ditvals.
  rewrite <- Heq_fs_ditvals; assumption.

  (* CASE t ∈ (reset s') ⇔ t ∈ Ti *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_reset sitpn s s' time_value env Hfun)
    as Heq_reset.
  rewrite <- Heq_reset; assumption.

  (* CASE NoDup (fst (split (reset s'))) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_reset sitpn s s' time_value env Hfun)
    as Heq_reset.
  rewrite <- Heq_reset; assumption.

  (* CASE C = fst (split (cond_values s')) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_struct_condv sitpn s time_value env s' Hfun)
    as Heq_fs_condv; assumption.
  
  (* CASE A = fst (split (exec_a s')) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_struct_actions sitpn s time_value env s' Hfun)
    as Heq_fs_actions; assumption.

  (* CASE F = fst (split (exec_f s')) *)
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_functions sitpn s time_value env s' Hfun) as Heq_execf.
  rewrite <- Heq_execf; assumption.
Qed.
