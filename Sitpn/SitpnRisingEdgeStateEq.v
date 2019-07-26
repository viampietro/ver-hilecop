(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import lemmas on fired transitions. *)

Require Import Hilecop.Sitpn.SitpnWellDefFired.

(* Import lemmas on interpretation. *)

Require Import Hilecop.Sitpn.SitpnWellDefInterpretation.

(* Import lemmas on marking. *)

Require Import Hilecop.Sitpn.SitpnRisingEdgeMarking.

(* Import lemmas on well-definition. *)

Require Import Hilecop.Sitpn.SitpnRisingEdgeWellDef.

(* Import misc. tactics and lemmas. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Sitpn.SitpnTactics.

(** * [sitpn_rising_edge] and [sitpn_state_eq] relation. *)

(** ** [sitpn_state_eq], [sitpn_rising_edge] and marking. *)

Lemma sitpn_rising_edge_state_eq_perm_marking :
  forall (sitpn : Sitpn)
         (s s' state state' : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn state ->
    sitpn_state_eq s state ->
    sitpn_rising_edge sitpn s = Some s' ->
    sitpn_rising_edge sitpn state = Some state' ->
    Permutation (marking s') (marking state').
Proof.
  intros sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
         Hwell_def_state Hsteq_sstate Hrising_s Hrising_state.

  (* Stategy is to apply NoDup_Permutation, then we need: 
     - NoDup (marking s')
     - NoDup (marking state')
     - ∀(p, n) ∈ (marking s') ⇔ (p, n) (marking state'). *)

  (* Builds NoDup (marking s') and NoDup (marking state') *)
  specialize (sitpn_rising_edge_well_def_state
                sitpn s s' Hwell_def_sitpn Hwell_def_s Hrising_s)
    as Hwell_def_s'.  
  deduce_nodup_state_marking for s'.

  specialize (sitpn_rising_edge_well_def_state
                sitpn state state' Hwell_def_sitpn Hwell_def_state Hrising_state)
    as Hwell_def_state'.
  deduce_nodup_state_marking for state'.

  rename Hnodup_fs_ms into Hnodup_ms.
  rename Hnodup_fs_ms0 into Hnodup_mstate.

  apply nodup_fst_split in Hnodup_ms.
  apply nodup_fst_split in Hnodup_mstate.
  
  (* Specializes sitpn_rising_edge_sub_pre_add_post for 
     Hrising_s and Hrising_state. *)
  specialize (sitpn_rising_edge_sub_pre_add_post
                sitpn s s' Hwell_def_sitpn Hwell_def_s Hrising_s)
    as Hdef_marking_s'.
  specialize (sitpn_rising_edge_sub_pre_add_post
                sitpn state state' Hwell_def_sitpn Hwell_def_state Hrising_state)
    as Hdef_marking_state'.
Admitted.
  
(** ** [sitpn_state_eq], [sitpn_rising_edge] and action states. *)

Lemma sitpn_rising_edge_state_eq_perm_actions :
  forall (sitpn : Sitpn)
         (s s' state state' : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn state ->
    sitpn_state_eq s state ->
    sitpn_rising_edge sitpn s = Some s' ->
    sitpn_rising_edge sitpn state = Some state' ->
    Permutation (exec_a s') (exec_a state').
Proof.
  intros sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
         Hwell_def_state Hsteq_sstate Hrising_s Hrising_state.

  (* Specializes sitpn_rising_edge_same_actions for 
     Hrising_s and Hrising_state. *)
  specialize (sitpn_rising_edge_same_actions sitpn s s' Hrising_s)
    as Heq_actions_s.
  specialize (sitpn_rising_edge_same_actions sitpn state state' Hrising_state)
    as Heq_actions_state.

  (* Decomposes sitpn_state_eq s state to 
     get Permutation (cond_values s) (cond_values state) *)
  unfold sitpn_state_eq in Hsteq_sstate.
  do 5 (apply proj2 in Hsteq_sstate).
  specialize (proj1 Hsteq_sstate) as Hperm_actions.

  (* Rewrites the goal and concludes. *)
  rewrite Heq_actions_s, Heq_actions_state in Hperm_actions; assumption.
Qed.

(** ** [sitpn_state_eq], [sitpn_rising_edge] and condition values. *)

Lemma sitpn_rising_edge_state_eq_perm_condv :
  forall (sitpn : Sitpn)
         (s s' state state' : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn state ->
    sitpn_state_eq s state ->
    sitpn_rising_edge sitpn s = Some s' ->
    sitpn_rising_edge sitpn state = Some state' ->
    Permutation (cond_values s') (cond_values state').
Proof.
  intros sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
         Hwell_def_state Hsteq_sstate Hrising_s Hrising_state.

  (* Specializes sitpn_rising_edge_same_condv for 
     Hrising_s and Hrising_state. *)
  specialize (sitpn_rising_edge_same_condv sitpn s s' Hrising_s)
    as Heq_condv_s.
  specialize (sitpn_rising_edge_same_condv sitpn state state' Hrising_state)
    as Heq_condv_state.

  (* Decomposes sitpn_state_eq s state to 
     get Permutation (cond_values s) (cond_values state) *)
  unfold sitpn_state_eq in Hsteq_sstate.
  do 4 (apply proj2 in Hsteq_sstate).
  specialize (proj1 Hsteq_sstate) as Hperm_condv.

  (* Rewrites the goal and concludes. *)
  rewrite Heq_condv_s, Heq_condv_state in Hperm_condv; assumption.
Qed.

(** ** [sitpn_state_eq], [sitpn_rising_edge] and fired transitions. *)

Lemma sitpn_rising_edge_state_eq_perm_fired :
  forall (sitpn : Sitpn)
         (s s' state state' : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn state ->
    sitpn_state_eq s state ->
    sitpn_rising_edge sitpn s = Some s' ->
    sitpn_rising_edge sitpn state = Some state' ->
    Permutation (fired s') (fired state').
Proof.
  intros sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
         Hwell_def_state Hsteq_sstate Hrising_s Hrising_state.

  (* Specializes sitpn_rising_edge_same_fired for 
     Hrising_s and Hrising_state. *)
  specialize (sitpn_rising_edge_same_fired sitpn s s' Hrising_s)
    as Heq_fired_s.
  specialize (sitpn_rising_edge_same_fired sitpn state state' Hrising_state)
    as Heq_fired_state.

  (* Decomposes sitpn_state_eq s state to 
     get Permutation (fired s) (fired state) *)
  unfold sitpn_state_eq in Hsteq_sstate.
  specialize (proj1 (proj2 Hsteq_sstate)) as Hperm_fired. 

  (* Rewrites the goal and concludes. *)
  rewrite Heq_fired_s, Heq_fired_state in Hperm_fired; assumption.
Qed.
  
(** ** [sitpn_rising_edge] and [sitpn_state_eq]. *)

Lemma sitpn_rising_edge_state_eq :
  forall (sitpn : Sitpn)
         (s s' state state' : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn state ->
    sitpn_state_eq s state ->
    sitpn_rising_edge sitpn s = Some s' ->
    sitpn_rising_edge sitpn state = Some state' ->
    sitpn_state_eq s' state'.
Proof.
  intros sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
         Hwell_def_state Hsteq_sstate Hrising_s Hrising_state.
  unfold sitpn_state_eq.
  repeat split.

  (* CASE Permutation (marking s') (marking state') *)
  - admit.

  (* CASE Permutation (fired s') (fired state') *)
  - apply (sitpn_rising_edge_state_eq_perm_fired
             sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
             Hwell_def_state Hsteq_sstate Hrising_s Hrising_state).

  (* CASE Permutation (d_intervals s') (d_intervals state') *)
  - admit.

  (* CASE Permutation (reset s') (reset state') *)
  - admit.

  (* CASE (cond_values s') (cond_values state') *)
  - apply (sitpn_rising_edge_state_eq_perm_condv
             sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
             Hwell_def_state Hsteq_sstate Hrising_s Hrising_state).

  (* CASE (exec_a s') (exec_a state') *)
  - apply (sitpn_rising_edge_state_eq_perm_actions
             sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
             Hwell_def_state Hsteq_sstate Hrising_s Hrising_state).

  (* CASE (exec_f s') (exec_f state') *)
  - admit.
Admitted.
