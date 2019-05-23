(* Import Spn's types, program and specification. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Spn.SpnTokenPlayer.
Require Import Hilecop.Spn.SpnSemantics.

(* Import useful tactics and general-purpose lemmas. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Spn.SpnTactics.

(* Import core lemmas necessary for Spn's correctness proof. *)

Require Import Hilecop.Spn.SpnCoreLemmas.

(* Import lemmas about spn_map_fire. *)

Require Import Hilecop.Spn.SpnMapFireCorrect.

(* Misc. imports. *)

Require Import Omega.
Require Import Classical_Prop.

(** *** Last part of correctness proof (rising_edge) *)

(** The goal in this part is to prove: 
    spn_cycle spn s = (s', s'') ⇒ SpnSemantics spn s' s'' rising_edge. 
    
    Multiple subproofs :
    
    1. spn_update_marking spn s' = s'' ⇒ IsWelldefinedspnstate s''.
    2. M' = M - ∑ pre(t) + ∑ post(t), forall t ∈ fired s'.
 *)

(** First subproof: spn_update_marking spn s' = s'' ⇒ IsWelldefinedspnstate s''. *)

Section SpnUpdateMarkingWellDefinedState.

  Lemma spn_update_marking_well_defined :
    forall (spn : Spn) (s : SpnState) (s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      spn_update_marking spn s = Some s' ->
      IsWellDefinedSpnState spn s'.
  Proof.
    intros spn s;
      functional induction (spn_update_marking  spn s) using spn_update_marking_ind;
      intros s' Hwell_def_spn Hwell_def_s Hfun.
    (* GENERAL CASE *)
    - unfold IsWellDefinedSpnState.
      split.
      (* Proves that marking s' structure = initial. *)
      + (* First we need Markinghavesamestruct (marking s) m'
         from map_update_marking_pre_same_marking. *)
        apply map_update_marking_pre_same_marking in e.
        (* Then, we need Markinghavesamestruct m' m'' 
       from map_update_marking_post_same_marking. *)
        apply map_update_marking_post_same_marking in e0.
        (* Then, the goal is deduced. *)
        injection Hfun as Heq_ss; rewrite <- Heq_ss; simpl.
        explode_well_defined_spn_state Hwell_def_s.
        unfold MarkingHaveSameStruct in *.
        rewrite Hsame_marking_state_spn.
        transitivity (fst (split m')); [assumption | assumption].
      + unfold IsWellDefinedSpnState in Hwell_def_s.
        apply proj2 in Hwell_def_s.
        injection Hfun as Heq_ss; rewrite <- Heq_ss; simpl; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

End SpnUpdateMarkingWellDefinedState.

(** Second subproof: M' = M - ∑ pre(t) + ∑ post(t), forall t ∈ fired s'. *)

Section SpnUpdateMarkingPrePost.

  Lemma spn_update_marking_sub_pre_add_post :
    forall (spn : Spn)
           (s : SpnState)
           (s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      spn_update_marking spn s = Some s' ->
      (forall (p : Place)
              (n : nat),
          In (p, n) s.(marking) ->
          In (p, n - (pre_sum spn p s.(fired)) + (post_sum spn p s.(fired))) s'.(marking)).
  Proof.
    intros spn s;
      functional induction (spn_update_marking spn s) using spn_update_marking_ind;
      intros s' Hwell_def_spn Hwell_def_s Hfun p n Hin_ms.
    (* GENERAL CASE *)
    - (* We need ∀ (p, n) ∈ (marking s) ⇒ (p, n - presum) ∈ m'. 
       map_update_marking_pre_sub_pre gives it. *)

      (* Builds NoDup (fst (split (marking s)) 
         to apply map_update_marking_pre_sub_pre *)
      explode_well_defined_spn; explode_well_defined_spn_state Hwell_def_s.
      unfold NoUnmarkedPlace in *.
      unfold NoDupPlaces in *.
      assert (Hnodup_ms := Hnodup_places).
      rewrite Hunm_place in Hnodup_ms.
      rewrite Hsame_marking_state_spn in Hnodup_ms.
      
      (* Specializes map_update_marking_pre_sub_pre. *)
      specialize (map_update_marking_pre_sub_pre
                    spn (marking s) (fired s) m'
                    Hwell_def_spn Hnodup_ms e p n Hin_ms)
        as Hin_mp.

      (* Builds NoDup (fst (split m') to specialize 
         map_update_marking_post_add_post *)
      specialize (map_update_marking_pre_same_marking
                    spn (marking s) (fired s) m' e)
        as Hsame_struct_mm'.
      rewrite Hsame_struct_mm' in Hnodup_ms.

      (* Specializes map_update_marking_post_add_post. *)
      specialize (map_update_marking_post_add_post
                    spn m' (fired s) m''
                    Hwell_def_spn Hnodup_ms e0 p
                    (n - pre_sum spn p (fired s)) Hin_mp)
        as Hin_msec.
      (* Rewrite (marking s') then assumption. *)
      injection Hfun as Hfun.
      rewrite <- Hfun; simpl; assumption.
      
    (* ERROR CASE *)
    - inversion Hfun.

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

End SpnUpdateMarkingPrePost.
