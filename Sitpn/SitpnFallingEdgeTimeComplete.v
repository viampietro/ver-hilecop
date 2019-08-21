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


(** * Completeness of [update_time_intervals]. *)

Section UpdateTimeIntervalsComplete.

  (** Completeness lemma for [update_time_intervals]. *)

  Lemma update_time_intervals_complete :
    forall (sitpn : Sitpn)
           (s s': SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (ditvals new_ditvals : list (Trans * DynamicTimeInterval)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env falling_edge ->

      (* Hypotheses on ditvals and new_ditvals. *)
      IsDecListCons ditvals (d_intervals s) ->
      Permutation (fs (new_ditvals ++ ditvals)) (fs (d_intervals s')) ->
      incl new_ditvals (d_intervals s') ->
      NoDup (fs (new_ditvals ++ ditvals)) ->

      (* Conclusion. *)
      exists ditvals' : list (Trans * DynamicTimeInterval),
        update_time_intervals sitpn s ditvals new_ditvals = Some ditvals'
        /\ Permutation ditvals' (d_intervals s').
  Proof.
    intros sitpn s s' time_value env ditvals.
    induction ditvals;
      intros new_ditvals Hwell_def_sitpn Hwell_def_s Hwell_def_s'
             Hspec His_dec_list Hperm_app Hincl_newd Hnodup_fs_newd.

    (* BASE CASE, ditvals = []. *)
    - simpl; exists new_ditvals; split.

      (* Proves equality. *)
      + trivial.

      (* Proves Permutation new_ditvals (d_intervals s'). 
         Strategy: use lemma [permutation_fs_permutation]. *)
      +
        (* Builds premises to apply [permutation_fs_permutation] *)

        (* Builds NoDup (fs new_ditvals) *)
        rewrite app_nil_r in Hnodup_fs_newd.

        (* Builds NoDup (fs (d_intervals s')) *)
        explode_well_defined_sitpn_state Hwell_def_s'.
        assert (H := Hnodup_state_ditvals).
        clear_well_defined_sitpn_state.
        rename Hnodup_state_ditvals into Hnodup_fs_ditvals_s'.

        (* Builds Permutation (fs new_ditvals) (fs (d_intervals s')) *)
        rewrite app_nil_r in Hperm_app.

        (* Applies [permutation_fs_permutation]. *)
        apply (permutation_fs_permutation
                 new_ditvals (d_intervals s') Hnodup_fs_newd Hnodup_fs_ditvals_s'
                 Hincl_newd Hperm_app).

    (* INDUCTION CASE. *)
    - simpl; destruct a; case_eq (s_intervals sitpn t).

      (* CASE (s_intervals sitpn t) = Some stc_itval *)
      + intros sitval Heq_some_sitval.
        case_eq (is_sensitized sitpn (marking s) (lneighbours sitpn t) t).

        (* CASE (is_sensitized sitpn (marking s) (lneighbours sitpn t) t) = Some b *)
        * intros b His_sens; destruct b.
           
          (* CASE (is_sensitized sitpn (marking s) (lneighbours sitpn t) t) = Some true *)
          -- case_eq (in_list Nat.eq_dec (fired s) t); intros Hin_list.

             (* CASE in_list Nat.eq_dec (fired s) t = true *)
             ++ specialize (IHditvals (new_ditvals ++ [(t, active (dec_itval sitval))])).

                (* Strategy: apply IHditvals, then we need premises. *)

                (* Builds IsDecListCons ditvals (d_intervals s) *)
                apply is_dec_list_cons_cons in His_dec_list.


                (* Builds incl (new_ditvals ++ [(t, active (dec_itval sitval))]) (d_intervals s') 
                   To do that, we need to show (t, active (dec_itval sitval)) ∈ (d_intervals s') using
                   Hspec.
                 *)
                assert (Hin_t_ditvalss' : In (t, active (dec_itval sitval)) (d_intervals s')).
                { admit. }

                (* Then, we can deduce incl (new_ditvals ++ [(t, active (dec_itval sitval))]) (d_intervals s') *)
                assert (Hincl_newd_app : incl (new_ditvals ++ [(t, active (dec_itval sitval))]) (d_intervals s')).
                { admit. }

                (* Builds Permutation and NoDup hyps by rewriting IH. *) 
                
                unfold fs in IHditvals.
                rewrite fst_split_app in IHditvals.
                rewrite fst_split_app in IHditvals.
                simpl in IHditvals.
                
        (* CASE (is_sensitized sitpn (marking s) (lneighbours sitpn t) t) = None, 
           impossible regarding the hypotheses.
         *)
        * intros His_sens_eq_none.
           
           (* Strategy: specialize [is_sensitized_no_error] then contradiction. 
         
              To specialize [is_sensitized_no_error], we need:
              incl (flatten_neighbours (lneighbours sitpn t)) (fs (marking s))
            *)

           deduce_in_from_is_dec_list_cons His_dec_list as Hin_td_sditvals.
           specialize (in_fst_split t d (d_intervals s) Hin_td_sditvals) as Hin_fs_sditvals.
           explode_well_defined_sitpn_state Hwell_def_s.
           rewrite <- (Hwf_state_ditvals t) in Hin_fs_sditvals.
           apply proj1 in Hin_fs_sditvals.
           rename Hin_fs_sditvals into Hin_t_transs.
           clear_well_defined_sitpn_state.

           (* Specializes in_transs_incl_flatten *)
           specialize (in_transs_incl_flatten t Hwell_def_sitpn Hin_t_transs)
             as Hincl_fl_fls.

           (* Gets incl (flatten_ln) places from IsWDSitpn, then use transitivity 
              to get incl flatten_n flatten_ln.
            *)
           explode_well_defined_sitpn.     
           unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
           specialize (incl_tran Hincl_fl_fls Hunk_pl_neigh) as Hincl_fn_fln.

           (* Gets places = (fs (marking s)) from IsWDSitpnState sitpn s *)
           explode_well_defined_sitpn_state Hwell_def_s.
           rewrite Hwf_state_marking in Hincl_fn_fln.

           (* Finally specializes is_sensitized_no_error *)
           specialize (is_sensitized_no_error sitpn (marking s) t Hincl_fn_fln)
             as Hex_is_sens.
           inversion_clear Hex_is_sens as (b & His_sens_eq_some).
           rewrite His_sens_eq_none in His_sens_eq_some; inversion His_sens_eq_some.
           
      (* CASE (s_intervals sitpn t) = None, 
         impossible regarding [IsWellDefinedSitpnState sitpn s]. 
       *)
      + intros Heq_none_sitval.
        explode_well_defined_sitpn_state Hwell_def_s.
        deduce_in_from_is_dec_list_cons His_dec_list as Hin_td_sditvals.
        specialize (in_fst_split t d (d_intervals s) Hin_td_sditvals) as Hin_fs_sditvals.
        rewrite <- (Hwf_state_ditvals t) in Hin_fs_sditvals.
        apply proj2 in Hin_fs_sditvals.
        contradiction.
  Admitted.
           
           
End UpdateTimeIntervalsComplete.
