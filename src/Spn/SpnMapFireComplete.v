(* Import Spn's types, program and specification. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Spn.SpnAnimator.
Require Import Hilecop.Spn.SpnSemantics.

(* Import useful tactics and general-purpose lemmas. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Spn.SpnTactics.

(* Import core lemmas necessary for Spn's correctness proof. *)

Require Import Hilecop.Spn.SpnCoreLemmas.

(* Misc. imports. *)

Require Import Omega.
Require Import Classical_Prop.

(** Completeness lemma for spn_map_fire_aux. *)

Lemma spn_map_fire_aux_complete :
  forall (spn : Spn)
         (s : SpnState)
         (fired_transitions : list Trans)
         (pgroups : list (list Trans))
         (s' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    SpnSemantics spn s s' falling_edge ->
    spn_map_fire_aux spn s fired_transitions pgroups = Some (fired s').
Proof.
  intros spn s fired_transitions pgroups;
    functional induction (spn_map_fire_aux spn s fired_transitions pgroups)
               using spn_map_fire_aux_ind;
    intros s' Hwell_def_spn Hwell_def_s Hfalling_edge.
Admitted.

(** Completeness lemma for spn_map_fire. *)

Lemma spn_map_fire_complete :
  forall (spn : Spn) (s : SpnState) (s' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    SpnSemantics spn s s' falling_edge ->
    spn_map_fire spn s = Some s'.
Proof.
  intros spn s;
    (* Functional induction on spn_map_fire. *)
    functional induction (spn_map_fire spn s) using spn_map_fire_ind;
    intros s' Hwell_def_spn Hwell_def_s Hfalling_edge.
  (* GENERAL CASE *)
  - (* Specializes spn_map_fire_aux_complete. *)
    specialize (spn_map_fire_aux_complete
                  spn s [] (priority_groups spn) s'
                  Hwell_def_spn Hwell_def_s Hfalling_edge) as Hmap_fire_aux.
    rewrite e in Hmap_fire_aux; injection Hmap_fire_aux as Hmap_fire_aux.
    rewrite Hmap_fire_aux.

    (* Renames hypotheses introduced by inversion of Hfalling_edge. *)
    inversion_clear Hfalling_edge;
      clear H H0 H1 H3 H4 H5 H6; rename H2 into Heq_marking.
    rewrite Heq_marking.
    destruct s'; simpl; reflexivity.

  (* ERROR CASE *)
  - (* Specializes spn_map_fire_aux_complete. *)
    specialize (spn_map_fire_aux_complete
                  spn s [] (priority_groups spn) s'
                  Hwell_def_spn Hwell_def_s Hfalling_edge) as Hmap_fire_aux.
    rewrite Hmap_fire_aux in e; inversion e.    
Qed.