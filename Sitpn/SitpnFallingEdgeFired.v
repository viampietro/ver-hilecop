(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import misc. lemmas and tactics. *)

Require Import Hilecop.Sitpn.SitpnCoreLemmas.
Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Sitpn.SitpnTactics.

(* Import lemmas on well-definition. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeWellDef.

(** * Falling edge lemmas about synchronous execution rules. *)

(** ** Transitions that are not firable are not fired. *)

Section SitpnFallingEdgeNotFirableNotFired.

  (** All transitions that are not firable at state [s] are not in the
      list [to_be_fired] returned by the [sitpn_map_fire] function. *)
  
  Lemma sitpn_map_fire_not_firable_not_fired :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (to_be_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_map_fire sitpn s = Some to_be_fired ->
      forall (pgroup : list Trans)
             (t : Trans),
        In pgroup (priority_groups sitpn) ->
        In t pgroup ->
        ~ SitpnIsFirable sitpn s t ->
        ~ In t to_be_fired.
  Proof.
  Admitted.
           
  (** All transitions that are not firable at state [s'] 
      are not in [(fired s')] where [s'] is the state
      returned by the [sitpn_falling_edge] function. *)

  Lemma sitpn_falling_edge_not_firable_not_fired :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      forall (pgroup : list Trans)
             (t : Trans),
        In pgroup (priority_groups sitpn) ->
        In t pgroup ->
        ~ SitpnIsFirable sitpn s' t ->
        ~ In t (fired s').
  Proof.
    intros sitpn s time_value env s' Hwell_def_sitpn Hwell_def_s Hfun.

    (* We need to build IsWellDefinedSitpnState sitpn s' before
       functional induction. *)
    specialize (sitpn_falling_edge_well_def_state
                  sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s Hfun)
      as Hwell_def_s'.

    (* Fun ind. on sitpn_falling_edge. *)
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind.

    (* GENERAL CASE. *)
    - simpl in Hfun;
        injection Hfun as Heq_s';

        (* Rewrites s' in the goal. *)
        rewrite <- Heq_s';
        simpl.

      (* Simplifies e0 with tmp_state. *)
      set (tmp_state :=
             {|
               fired := [];
               marking := marking s;
               d_intervals := d_intervals';
               reset := reset s;
               cond_values := get_condition_values (conditions sitpn) time_value env [];
               exec_a := get_action_states sitpn s (actions sitpn) [];
               exec_f := exec_f s
             |}) in e0.

      (* We need to introduce t and pgroup in the context to
         specialize sitpn_is_firable_iff_eq. *)
      intros pgroup t.

      (* Builds premises of sitpn_is_firable_iff_eq. *)
      assert (Heq_m : (marking tmp_state = marking s')) by (rewrite <- Heq_s'; reflexivity).
      assert (Heq_ditvals : (d_intervals tmp_state = d_intervals s')) by (rewrite <- Heq_s'; reflexivity).
      assert (Heq_condv : (cond_values tmp_state = cond_values s')) by (rewrite <- Heq_s'; reflexivity).

      (* Specializes sitpn_is_firable_iff to get: 
         SitpnIsfirable tmp_state t = SitpnIsfirable s' t *)
      specialize (sitpn_is_firable_iff_eq sitpn tmp_state s' t Heq_m Heq_ditvals Heq_condv)
        as Heq_sitpn_is_firable.

      (* Rewrites SitpnIsFirable sitpn s' t by SitpnIsfirable sitpn
         tmp_state t in the goal and generalizes pgroup and t to match
         conclusion of lemma sitpn_map_fire_not_firable_not_fired. *)
      rewrite Heq_s'.
      rewrite <- Heq_sitpn_is_firable.
      generalize pgroup, t. (* Revert previously introduced pgroup and t. *)

      (* Gets IsWellDefinedSitpnState tmp_state before applying lemma. *)
      assert (Hnil_fired_s': fired tmp_state = []) by auto.
      assert (Heq_reset: reset s' = reset tmp_state) by (rewrite <- Heq_s'; auto).
      assert (Heq_execa: exec_a s' = exec_a tmp_state) by (rewrite <- Heq_s'; auto).
      assert (Heq_execf: exec_f s' = exec_f tmp_state) by (rewrite <- Heq_s'; auto).

      (* Specializes well-definition on tmp_state. *)
      specialize (is_well_def_tmp_state
                    sitpn s' tmp_state Hnil_fired_s' (eq_sym Heq_m) (eq_sym Heq_ditvals)
                    Heq_reset (eq_sym Heq_condv) Heq_execa Heq_execf Hwell_def_s')
        as Hwell_def_tmp.                                        
      
      (* Applies sitpn_map_fire_not_firable_not_fired to complete the
         subgoal. *)
      apply (sitpn_map_fire_not_firable_not_fired
               sitpn tmp_state trs_2b_fired Hwell_def_sitpn Hwell_def_tmp e0).

    (* ERROR CASE *)
    - inversion Hfun.
    - inversion Hfun.
  Qed.

  
End SitpnFallingEdgeNotFirableNotFired.

