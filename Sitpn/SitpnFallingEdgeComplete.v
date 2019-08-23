(* Import Sitpn core material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.
Require Import Hilecop.Sitpn.SitpnTactics.

(* Import misc. lemmas, tactics and definitions. *)

Require Import Hilecop.Utils.HilecopDefinitions.

(* Import lemmas about time, fired and interpretation. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeTimeComplete.
Require Import Hilecop.Sitpn.SitpnFallingEdgeFiredComplete.
Require Import Hilecop.Sitpn.SitpnFallingEdgeInterpretationComplete.

(** * Completeness of [sitpn_falling_edge]. *)

Lemma sitpn_falling_edge_complete :
  forall (sitpn : Sitpn)
         (s s' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn s' ->
    SitpnSemantics sitpn s s' time_value env falling_edge ->
    exists istate : SitpnState,
      sitpn_falling_edge sitpn s time_value env = Some istate /\
      sitpn_state_eq s' istate.
Proof.
  intros sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s
         Hwell_def_s' Hspec.

  (* Digs the function sitpn_falling_edge. *)
  unfold sitpn_falling_edge.

  (* Specializes update_time_intervals_complete, and
     rewrites the goal. 
     
     To do so, we have to build some premises. *)
  
  assert (His_dec_ditvals : IsDecListCons (d_intervals s) (d_intervals s)) by (apply IsDecListCons_refl).
  assert (Hperm_ds_ds' : Permutation (fs ([] ++ (d_intervals s))) (fs (d_intervals s'))).
  {
    rewrite app_nil_l.
    explode_well_defined_sitpn_state Hwell_def_s.
    explode_well_defined_sitpn_state Hwell_def_s'.

    assert (Hequiv_ditvals : forall t : Trans, In t (fs (d_intervals s)) <-> In t (fs (d_intervals s'))).
    {
      intros t; split;
        [
          intros Hin_ditvals;
          rewrite <- (Hwf_state_ditvals t) in Hin_ditvals;
          rewrite Hwf_state_ditvals0 in Hin_ditvals;
          assumption |
          intros Hin_ditvals;
          rewrite <- Hwf_state_ditvals0 in Hin_ditvals;
          rewrite (Hwf_state_ditvals t) in Hin_ditvals;
          assumption
        ].
    }

    apply (NoDup_Permutation Hnodup_state_ditvals Hnodup_state_ditvals0 Hequiv_ditvals).
  }
  assert (Hincl_nil : incl [] (d_intervals s')) by (intros a Hin_nil; inversion Hin_nil).
  assert (Hnodup_app_nil : NoDup (fs ([] ++ (d_intervals s)))).
  {
    rewrite app_nil_l.
    explode_well_defined_sitpn_state Hwell_def_s.
    assumption.
  }
  
  specialize (update_time_intervals_complete
                sitpn s s' time_value env (d_intervals s) []
                Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                His_dec_ditvals Hperm_ds_ds' Hincl_nil Hnodup_app_nil)
    as Hex_update_t_itvals.
  inversion_clear Hex_update_t_itvals as (ditvals' & Hw_update_t_itvals).
  inversion_clear Hw_update_t_itvals as (Hupdate_t_itvals & Hperm_ditvals).
  rewrite Hupdate_t_itvals.

  (* Makes the goal more readable. *)
  set (tmp_state := {|
            fired := [];
            marking := marking s;
            d_intervals := ditvals';
            reset := reset s;
            cond_values := get_condition_values (conditions sitpn) time_value env [];
            exec_a := get_action_states sitpn s (actions sitpn) [];
            exec_f := exec_f s |}).

  (* Specializes get_condition_values_complete, to get the hypothesis: 
     Permutation (cond_values tmp_state) (cond_values s').

     Necessary to prove sitpn_state_eq s' istate and to 
     specialize sitpn_map_fire_complete.  
   *)
  
  assert (His_dec_conds : IsDecListCons (conditions sitpn) (conditions sitpn)) by (apply IsDecListCons_refl).
  assert (Hperm_conds_cs' : Permutation ((@fs Condition bool []) ++ (conditions sitpn)) (fs (cond_values s'))).
  {
    rewrite app_nil_l.
    explode_well_defined_sitpn_state Hwell_def_s'.
    rewrite Hwf_state_condv.
    auto.
  }
  assert (Hincl_nil_condv : incl [] (cond_values s')) by (intros a Hin_nil; inversion Hin_nil).
  assert (Hnodup_app_nil_conds : NoDup ((@fs Condition bool []) ++ (conditions sitpn))).
  {
    rewrite app_nil_l.
    explode_well_defined_sitpn.
    assumption.
  }

  specialize (get_condition_values_complete
                sitpn s s' time_value env (conditions sitpn) []
                Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                His_dec_conds Hperm_conds_cs' Hincl_nil_condv Hnodup_app_nil_conds)
    as Hperm_condv.
  
  
Admitted.
