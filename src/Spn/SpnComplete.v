(* Import Spn's types, program and specification. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Spn.SpnAnimator.
Require Import Hilecop.Spn.SpnSemantics.

(* Import useful tactics and general-purpose lemmas. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Spn.SpnTactics.

(* Import core lemmas necessary for Spn's correctness proof. *)

Require Import Hilecop.Spn.SpnCoreLemmas.

(* Import lemmas about spn_map_fire's completeness and soundness. *)

Require Import Hilecop.Spn.SpnMapFireCorrect.
Require Import Hilecop.Spn.SpnMapFireComplete.

(* Import lemmas about spn_update_marking's completeness. *)

Require Import Hilecop.Spn.SpnUpdateMarkingComplete.

(*! [spnstate_eq] preserves [SpnSemantics] relation on raising edge. !*)

Lemma spn_update_marking_spnstate_eq_morph :
  forall (spn : Spn)
    (s s' state state' : SpnState),
    spnstate_eq s state ->
    spn_update_marking spn s = Some s' ->
    spn_update_marking spn state = Some state' ->
    spnstate_eq s' state'.
Proof.
Admitted.

(*! Completeness proof between spn_cycle and SpnSemantics_falling_edge. !*)

Theorem spn_semantics_complete :
  forall (spn : Spn)
    (s s' s'' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    IsWellDefinedSpnState spn s'' ->
    SpnSemantics spn s s' falling_edge ->
    SpnSemantics spn s' s'' raising_edge ->
    exists (istate fstate : SpnState),
      spn_cycle spn s = Some (istate, fstate) /\
      spnstate_eq s' istate /\
      spnstate_eq s'' fstate.
Proof.
  intros spn s s' s'' Hwell_def_spn Hwell_def_s
         Hwell_def_s' Hwell_def_s'' Hfalling_edge Hraising_edge.

  unfold spn_cycle.

  (* Specializes spn_map_fire_complete and rewrite the goal,
     therefore skipping the error case. *)
  specialize (spn_map_fire_complete spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s' Hfalling_edge)
    as Hspn_map_fire_ex.
  inversion Hspn_map_fire_ex as (istate & Hspn_map_fire_w).
  inversion Hspn_map_fire_w as (Hspn_map_fire & Hsteq_s').
  rewrite Hspn_map_fire.

  (* Specializes spn_update_marking_no_error and rewrite the goal,
     therefore skipping the error case. *)

  (* Need hyp. IsWellDefinedSpnState spn istate. *)
  specialize (spn_map_fire_well_defined_state spn s istate Hwell_def_spn Hwell_def_s Hspn_map_fire)
    as Hwell_def_istate.

  specialize (spn_update_marking_no_error spn istate Hwell_def_spn Hwell_def_istate)
    as Hup_mark_ex.
  inversion Hup_mark_ex as (fstate & Hup_mark_istate).
  rewrite Hup_mark_istate.

  (* Instantiates state couple with istate and fstate. *)
  exists istate, fstate.

  (* Splits and solves each branch of the conjucntion. *)
  split. reflexivity. split.

  (* Solves spnstate_eq s' istate, trivial. *)
  - assumption.

  (* Solves spnstate_eq s'' fstate, harder. *)
  - clear Hup_mark_ex Hspn_map_fire_ex Hspn_map_fire_w.
    
    (* Specializes spn_update_marking_complete. *)
    specialize (spn_update_marking_complete
                  spn s' s'' Hwell_def_spn Hwell_def_s' Hwell_def_s'' Hraising_edge)
      as Hspn_update_marking_ex.
    inversion Hspn_update_marking_ex as (final_state & Hspn_update_marking_w).
    inversion Hspn_update_marking_w as (Hspn_update_marking & Hsteq_s'').
    clear Hspn_update_marking_ex Hspn_update_marking_w.

    (* We need to specialize [spn_update_marking_spnstate_eq_morph] 
     * to deduce spnstate_eq fstate final_state, 
     * then deduce the goal by transitivity. *)
    
Qed.
    