(* Import Spn's types, program and specification. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Spn.SpnAnimator.
Require Import Hilecop.Spn.SpnSemantics.

(* Import useful tactics and general-purpose lemmas. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Spn.SpnTactics.

(* Import core lemmas necessary for Spn's correctness proof. *)

Require Import Hilecop.Spn.SpnCoreLemmas.

(* Import lemmas about spn_map_fire's completeness. *)

Require Import Hilecop.Spn.SpnMapFireComplete.

(* Import lemmas about spn_update_marking's completeness. *)

Require Import Hilecop.Spn.SpnUpdateMarkingComplete.

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
    spn_cycle spn s = Some (s', s'').
Proof.
  intros spn s s' s'' Hwell_def_spn Hwell_def_s
         Hwell_def_s' Hwell_def_s'' Hfalling_edge Hraising_edge.
   
  (* Functional induction on spn_cycle. *)
  functional induction (spn_cycle spn s) using spn_cycle_ind.

  (* GENERAL CASE, apply spn_map_fire_complete and spn_update_marking_complete. *)
  - (* Specializes spn_map_fire_complete, and then shows inter_state = s'. *)
    specialize (spn_map_fire_complete spn s s' Hwell_def_spn Hwell_def_s Hfalling_edge)
      as Hspn_map_fire.
    rewrite Hspn_map_fire in e;
      injection e as Heq_s'_istate;
      rewrite Heq_s'_istate.

    (* Specializes spn_update_marking_complete, and then shows final_state = s''. *)
    specialize (spn_update_marking_complete spn s' s'' Hwell_def_spn Hwell_def_s' Hraising_edge)
      as Hspn_update_marking.
    rewrite <- Heq_s'_istate in e0;
      rewrite Hspn_update_marking in e0;
      injection e0 as Heq_s''_fstate;
      rewrite Heq_s''_fstate.
    reflexivity.

  (* ERROR CASE, spn_update_marking = None. *)
  - specialize (spn_map_fire_complete spn s s' Hwell_def_spn Hwell_def_s Hfalling_edge)
      as Hspn_map_fire.
    rewrite Hspn_map_fire in e;
      injection e as Heq_s'_istate;
      rewrite <- Heq_s'_istate in e0.
    specialize (spn_update_marking_complete spn s' s'' Hwell_def_spn Hwell_def_s' Hraising_edge)
      as Hspn_update_marking.
    rewrite Hspn_update_marking in e0; inversion e0.

  (* ERROR CASE, spn_map_fire = None *)
  - specialize (spn_map_fire_complete spn s s' Hwell_def_spn Hwell_def_s Hfalling_edge)
      as Hspn_map_fire.
    rewrite Hspn_map_fire in e; inversion e.
Qed.

(* Renames hypotheses introduced by inversion of Hfalling_edge. *)
(* inversion_clear Hfalling_edge; *)
(*   clear H H0; *)
(*   rename H1 into Hwell_def_s'; *)
(*   rename H2 into Heq_marking; *)
(*   rename H3 into Hnot_firable_not_fired; *)
(*   rename H4 into Hnot_firable_succ; *)
(*   rename H5 into Hsens_by_res; *)
(*   rename H6 into Hnot_sens_by_res. *)

(* Rename hypotheses introduced by inversion of Hraising_edge. *)
(* inversion_clear Hraising_edge; *)
(*   clear H H0 H1; *)
(*   rename H2 into Heq_fired; *)
(*   rename H3 into Hsub_pre_add_post. *)
