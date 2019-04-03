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

(** Completeness lemma for spn_update_marking. *)

Lemma spn_update_marking_complete :
  forall (spn : Spn) (s : SpnState) (s' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    SpnSemantics spn s s' raising_edge ->
    spn_update_marking spn s = Some s'.
Proof.
Admitted.