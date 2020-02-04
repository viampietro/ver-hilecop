(** Import Spn's types, program and specification. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Spn.SpnTokenPlayer.
Require Import Hilecop.Spn.SpnSemantics.

(** Import useful tactics and general-purpose lemmas. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Spn.SpnTactics.

(** Import core lemmas necessary for Spn's correctness proof. *)

Require Import Hilecop.Spn.SpnCoreLemmas.

(** Import lemmas about spn_map_fire's correctness. *)

Require Import Hilecop.Spn.SpnMapFireCorrect.

(** Import lemmas about spn_update_marking's correctness. *)

Require Import Hilecop.Spn.SpnUpdateMarkingCorrect.

(** * Correctness proof between spn_cycle and SpnSemantics_falling_edge. *)

Theorem spn_semantics_falling_edge_correct :
  forall (spn : Spn)
    (s s' s'' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    spn_cycle spn s = Some (s', s'') ->
    SpnSemantics spn s s' falling_edge.
Proof.
  do 2 intro;
    functional induction (spn_cycle spn s) using spn_cycle_ind;
    intros s' s'' Hwell_def_spn Hwell_def_state Hfun.
  (* GENERAL CASE *)
  - apply SpnSemantics_falling_edge.
    (* Trivial proof, IsWellDefinedSpn. *)
    + assumption.
    (* Trivial proof, IsWellDefinedSpnState. *)
    + assumption.
    (* Proves IsWellDefinedSpnState spn s'. *)
    + injection Hfun; intros Heq_fstate Heq_istate; rewrite <- Heq_istate.
      apply (spn_map_fire_well_defined_state
               spn s inter_state Hwell_def_spn Hwell_def_state e).           
    (* Proves s.(marking) = s'.(marking) *)
    + apply spn_map_fire_same_marking in e.
      injection Hfun; intros Heq_fstate Heq_istate; rewrite <- Heq_istate; assumption.
    (* Proves ∀ t ∉ firable(s') ⇒ t ∉ Fired' *)
    + injection Hfun; intros Heq_fstate Heq_istate; rewrite <- Heq_istate.
      apply (spn_map_fire_not_firable_not_fired
               spn s inter_state Hwell_def_spn Hwell_def_state e).
    (* Proves ∀ t ∈ firable(s'), t ∈ sens(m - ∑ pre(t_i)) ⇒ t ∈ Fired'  *)
    + injection Hfun as Heq_istate Heq_fstate; rewrite <- Heq_istate.
      apply (spn_map_fire_sens_by_residual
               spn s inter_state Hwell_def_spn Hwell_def_state e).
    (* Proves ∀ t ∈ firable(s'), t ∉ sens(m - ∑ pre(t_i)) ⇒ t ∉ Fired'  *)
    + injection Hfun as Heq_istate Heq_fstate; rewrite <- Heq_istate.
      apply (spn_map_fire_not_sens_by_residual
               spn s inter_state Hwell_def_spn Hwell_def_state e).
  (* ERROR CASE *)
  - inversion Hfun.
  (* ERROR CASE *)
  - inversion Hfun.
Qed.

(** * Correctness proof between spn_cycle and SpnSemantics_rising_edge. *)

Theorem spn_semantics_rising_edge_correct :
  forall (spn : Spn)
    (s s' s'' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    spn_cycle spn s = Some (s', s'') ->
    SpnSemantics spn s' s'' rising_edge.
Proof.
  do 2 intro;
    functional induction (spn_cycle spn s) using spn_cycle_ind;
    intros s' s'' Hwell_def_spn Hwell_def_s Hfun.
  (* GENERAL CASE *)
  - apply SpnSemantics_rising_edge.
    (* Trivial proof IsWellDefinedSpn *)
    + assumption.
    (* Proves IsWellDefinedSpnState spn s'. *)
    + injection Hfun; intros Heq_fstate Heq_istate; rewrite <- Heq_istate.
      apply (spn_map_fire_well_defined_state
               spn s inter_state Hwell_def_spn Hwell_def_s e).
    (* Proves IsWellDefinedSpnState spn s''. *)
    + injection Hfun as Heq_istate Heq_fstate; rewrite <- Heq_fstate.
      apply (spn_map_fire_well_defined_state
               spn s inter_state Hwell_def_spn Hwell_def_s) in e.
      apply (spn_update_marking_well_defined
               spn inter_state final_state Hwell_def_spn e e0).
    (* Proves fired s' = fired s'' *)
    + apply spn_update_marking_same_fired in e0.
      injection Hfun as Heq_istate Heq_fstate;
        rewrite <- Heq_istate, <- Heq_fstate; assumption.
    (* Proves M' = M - ∑ pre(t) + ∑ post(t), forall t ∈ fired s' *)
    + specialize (spn_map_fire_well_defined_state
                    spn s inter_state Hwell_def_spn Hwell_def_s e)
        as Hwell_def_s'.
      injection Hfun as Heq_istate Heq_fstate;
        rewrite <- Heq_istate, <- Heq_fstate.
      apply (spn_update_marking_sub_pre_add_post
               spn inter_state final_state Hwell_def_spn Hwell_def_s' e0).
  (* ERROR CASE *)
  - inversion Hfun.
  (* ERROR CASE *)
  - inversion Hfun.
Qed.

(** * Correctness proof between [spn_cycle] and [SpnSemantics].
      
      Conjunction of the two previous theorems. *)

Theorem spn_semantics_correct :
  forall (spn : Spn)
         (s s' s'' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    spn_cycle spn s = Some (s', s'') ->
    SpnSemantics spn s s' falling_edge /\ SpnSemantics spn s' s'' rising_edge.
Proof.
  intros spn s s' s'' Hwell_def_spn Hwell_def_s Hfun.
  specialize (spn_semantics_falling_edge_correct
                spn s s' s'' Hwell_def_spn Hwell_def_s Hfun) as Hfalling_edge.
  specialize (spn_semantics_rising_edge_correct
                spn s s' s'' Hwell_def_spn Hwell_def_s Hfun) as Hrising_edge.
  apply (conj Hfalling_edge Hrising_edge).
Qed.
