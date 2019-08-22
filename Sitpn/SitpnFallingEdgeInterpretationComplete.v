(* Import Sitpn core material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.
Require Import Hilecop.Sitpn.SitpnTactics.
Require Import Hilecop.Sitpn.SitpnCoreLemmas.

(* Import Hilecop utils. *)

Require Import Hilecop.Utils.HilecopDefinitions.
Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Utils.HilecopTactics.


(** * Completeness of [get_condition_values]. *)

Section GetCondValuesComplete.

  (** Completeness lemma for [get_condition_values]. *)
  
  Lemma get_condition_values_complete :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (conds : list Condition)
           (new_conds : list (Condition * bool)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env falling_edge ->
      IsDecListCons conds (conditions sitpn) ->
      Permutation ((fs new_conds) ++ conds) (fs (cond_values s')) ->
      incl new_conds (cond_values s') ->
      NoDup ((fs new_conds) ++ conds) ->
      Permutation (get_condition_values conds time_value env new_conds) (cond_values s').
  Proof.
    intros sitpn s s' time_value env;
      induction conds;
      intros new_conds Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
             His_dec_list Hperm_app Hincl_newc Hnodup_app.

    (* BASE CASE, conds = []. *)
    - simpl.

      (* Proves Permutation new_conds (cond_values s'). 
         Strategy: use lemma [permutation_fs_permutation]. *)

      (* Builds premises to apply [permutation_fs_permutation] *)

      (* Builds NoDup (fs new_conds) *)
      rewrite app_nil_r in Hnodup_app.

      (* Builds NoDup (fs (d_intervals s')) *)
      explode_well_defined_sitpn_state Hwell_def_s'.
      explode_well_defined_sitpn.
      unfold NoDupConditions in Hnodup_cond.
      rewrite Hwf_state_condv in Hnodup_cond.
      rename Hnodup_cond into Hnodup_fs_condv_s'.
      clear_well_defined_sitpn.
      clear_well_defined_sitpn_state.
      
      (* Builds Permutation (fs new_conds) (fs (d_intervals s')) *)
      rewrite app_nil_r in Hperm_app.

      (* Applies [permutation_fs_permutation]. *)
      apply (permutation_fs_permutation
               new_conds (cond_values s')
               Hnodup_app Hnodup_fs_condv_s'
               Hincl_newc Hperm_app).

    (* INDUCTION CASE, a :: conds *)
    - simpl.
      specialize (IHconds (new_conds ++ [(a, env a time_value)])).

      (* Strategy: apply IHconds, then we need premises. *)

      (* Builds incl (new_conds ++ [(a, env a time_value)]) (cond_values s') 
         To do that, we need to show (a, env a time_value) ∈ (cond_values s') 
         using Hspec.
       *)
      assert (Hin_a_condvs' : In (a, env a time_value) (cond_values s')).
      {
        
        (* Strategy: get the right Sitpn semantics rule from
                               Hspec and specialize it. *)
        inversion Hspec.
        clear H H0 H1 H2 H4 H5 H6 H7 H8 H9 H10 H11 H12.
        rename H3 into Hcondv.

        (* Gets In a (conditions sitpn) *)
        deduce_in_from_is_dec_list_cons His_dec_list as Hin_a_conds.
        
        apply (Hcondv a Hin_a_conds).
      }
      
      (* Then, we can deduce incl (new_conds ++ [(a, env)]) (cond_values s') *)
      assert (Hincl_newc_app : incl (new_conds ++ [(a, env a time_value)]) (cond_values s')).
      {
        intros x Hin_app.
        apply in_app_or in Hin_app.
        inversion_clear Hin_app as [Hin_x_newc | Heq_x_a];
          [ apply (Hincl_newc x Hin_x_newc) |
            inversion_clear Heq_x_a as [Heq | Hin_nil];
            [ rewrite <- Heq; assumption |
              inversion Hin_nil
            ]
          ].
      }

      (* Builds IsDecListCons conds (conditions sitpn) *)
      apply is_dec_list_cons_cons in His_dec_list.
      
      (* Builds Permutation and NoDup hyps by rewriting IH. *) 
            
      unfold fs in IHconds.
      rewrite fst_split_app in IHconds.
      simpl in IHconds.
      rewrite <- app_assoc in IHconds.

      (* Applies IHconds *)
      apply (IHconds Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                     His_dec_list Hperm_app Hincl_newc_app Hnodup_app).
  Qed.
  
End GetCondValuesComplete.
