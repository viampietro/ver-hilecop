(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.
Require Import Hilecop.Sitpn.SitpnTactics.
Require Import Hilecop.Sitpn.SitpnCoreLemmas.

(* Import misc. lemmas, tactics and definitions. *)

Require Import Hilecop.Utils.HilecopDefinitions.
Require Import Hilecop.Utils.HilecopLemmas.

(* Misc. imports. *)

Require Import Omega.
Require Import Classical_Prop.

(** * Completeness of [sitpn_map_fire]. *)

Section SitpnMapFireComplete.

  (** Completeness lemma for sitpn_fire_aux. *)
  
  Lemma sitpn_fire_aux_complete :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (tmp_state : SitpnState)
           (pg pgroup : list Trans)
           (fired_transitions : list Trans)
           (residual_marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env falling_edge ->

      (* Properties of tmp_state. *)
      (marking tmp_state) = (marking s) ->
      Permutation (d_intervals tmp_state) (d_intervals s') ->
      Permutation (cond_values tmp_state) (cond_values s') ->
      
      (* Hypotheses on pg, pgroup and fired_transitions *)
      In pgroup sitpn.(priority_groups) ->
      (forall t : Trans, In t pgroup /\ In t (fired s') ->
                         In t (fired_transitions ++ pg)) ->
      IsDecListCons pg pgroup ->
      NoDup (fired_transitions ++ pg) ->
      incl fired_transitions (fired s') ->
      (forall t : Trans,
          In t pg ->
          forall t' : Trans,
            In t' fired_transitions ->
            HasHigherPriority t' t pgroup /\ In t' (fired s')) ->
        
      (* Hypotheses on residual_marking. *)
      (forall (p : Place) (n : nat),
          In (p, n) (marking tmp_state) ->
          In (p, n - (pre_sum sitpn p fired_transitions)) residual_marking) ->
      (places sitpn) =  (fs residual_marking) ->

      (* Conclusion *)
      exists final_fired : list Trans,
        sitpn_fire_aux sitpn tmp_state residual_marking fired_transitions pg = Some final_fired /\
        incl final_fired s'.(fired) /\
        (forall t : Trans, In t pg /\ In t s'.(fired) -> In t final_fired).
  Proof.
    intros sitpn s s' time_value env tmp_state.
    induction pg;
      intros pgroup fired_transitions residual_marking
             Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
             Heq_m_tmp Hperm_ditvals_tmp Hperm_conds_tmp
             Hin_pgs Hin_fpg_app His_dec Hnodup_app
             Hincl_sf Hhigh_w_sf Hresid_m Hsame_struct.
    
    (* BASE CASE *)
    - exists fired_transitions; simpl.
      split; [ reflexivity | split; [assumption | intros t Hw; apply proj1 in Hw; inversion Hw]].

    (* INDUCTION CASE *)
    - simpl sitpn_fire_aux.
      
      (* First, apply get_neighbours_complete. 
         To do so, we need (a, neigh_of_a) ∈ (lneighbours sitpn) ∧ NoDup (lneighbours sitpn) *)

      (* explode_well_defined_sitpn. *)
      (* assert (Hnodup_lneighbours := Hnodup_transs). *)
      (* unfold NoDupTranss in Hnodup_lneighbours. *)
      (* rewrite Hunk_tr_neigh in Hnodup_lneighbours. *)

      (* Builds In a (concat (priority_groups sitpn)) *)

      (* specialize (is_dec_list_cons_incl His_dec) as Hin_a_pg. *)
      (* assert (Hin_eq : In a (a :: pg)) by apply in_eq. *)
      (* specialize (Hin_a_pg a Hin_eq); clear Hin_eq. *)
      (* specialize (in_concat a pgroup (priority_groups sitpn) Hin_a_pg Hin_pgs) as Hin_a_concat. *)
      (* unfold NoUnknownInPriorityGroups in Hno_unk_pgroups. *)
      (* rewrite <- Hno_unk_pgroups in Hin_a_concat. *)
      (* rewrite Hunk_tr_neigh in Hin_a_concat. *)
      (* specialize (in_fst_split_in_pair a (lneighbours sitpn) Hin_a_concat) as Hin_lneigh_ex. *)
      (* inversion_clear Hin_lneigh_ex as (neigh_of_a & Hin_lneigh). *)

      (* Specializes get_neighbours_complete, then rewrite the goal. *)

      (* specialize (get_neighbours_complete *)
      (*               (lneighbours sitpn) a neigh_of_a Hnodup_lneighbours Hin_lneigh) *)
      (*   as Hget_neigh. *)
      (* rewrite Hget_neigh. *)    

      (* Specializes sitpn_is_firable_no_error to skip the error case
         when rewriting the goal. *)

      assert (Hincl_fl_m : incl (flatten_neighbours (lneighbours sitpn a)) (fs (marking tmp_state))).
      {
        explode_well_defined_sitpn;
          unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
        assert (Hincl_flat_lneigh : incl (flatten_neighbours (lneighbours sitpn a))
                                         (flatten_lneighbours sitpn (transs sitpn))).
        {
            deduce_in_transs; apply (in_transs_incl_flatten a Hwell_def_sitpn Hin_t_transs).
        }
        
        specialize (incl_tran Hincl_flat_lneigh Hunk_pl_neigh) as Hincl_fl_m.
        explode_well_defined_sitpn_state Hwell_def_s.
        rewrite Hwf_state_marking in Hincl_fl_m.
        rewrite <- Heq_m_tmp in Hincl_fl_m.
        assumption.
      }

      assert (Hin_t_fs_ditvals : s_intervals sitpn a = None \/ In a (fs (d_intervals tmp_state))).
      {
        assert (Hv_sitvals := classic ((s_intervals sitpn a) = None)).
        inversion_clear Hv_sitvals as [Heq_none_sitvals | Heq_some_sitvals].
        - left; assumption.
        - deduce_in_transs; explode_well_defined_sitpn_state Hwell_def_s'.
          assert (Hw_intranss_sitvals := conj Hin_t_transs Heq_some_sitvals).
          rewrite (Hwf_state_ditvals a) in Hw_intranss_sitvals.
          apply (in_fst_split_in_pair a (d_intervals s')) in Hw_intranss_sitvals.
          inversion_clear Hw_intranss_sitvals as (ditval & Hin_ditvals_s').
          right.
          apply in_fst_split with (b := ditval).
          rewrite Hperm_ditvals_tmp.
          assumption.
      }
      
      specialize (sitpn_is_firable_no_error sitpn tmp_state a Hincl_fl_m Hin_t_fs_ditvals) as Hfirable_ex.
      inversion_clear Hfirable_ex as (b & Hfirable).
      rewrite Hfirable.

      (* Two cases, either sitpn_is_firable = Some true or Some false. *)
      dependent induction b.

      (* CASE sitpn_is_firable = Some true, then continues to dig the function. *)
      
      + (* Specializes is_sensitized_no_error to skip the error case
           when rewriting the goal. *)
        explode_well_defined_sitpn_state Hwell_def_state.
        rewrite <- Hsame_marking_state_sitpn in Hincl_fl_m.
        rewrite Hsame_struct in Hincl_fl_m.
        specialize (is_sensitized_no_error
                      sitpn residual_marking a neigh_of_a Hincl_fl_m)
          as Hsens_ex.
        inversion_clear Hsens_ex as (b & Hsens).
        rewrite Hsens.

        (* Two cases, either is_sensitized = Some true or Some false. *)
        dependent induction b.

        (* CASE is_sensitized = Some true, then continues to dig the function. *)
        -- (* Specializes update_residual_marking_no_error to skip the 
            error case when rewriting the goal. *)
          assert (Hincl_pre_m : incl (pre_pl neigh_of_a) (fst (split residual_marking))).
          {
            intros x Hin_x_pre.
            apply or_introl
              with (B := In x ((test_pl neigh_of_a)
                                 ++ (inhib_pl neigh_of_a)
                                 ++ (post_pl neigh_of_a)))
              in Hin_x_pre.
            apply in_or_app in Hin_x_pre.
            apply (Hincl_fl_m x Hin_x_pre).
          }
          specialize (update_residual_marking_no_error
                        sitpn a neigh_of_a residual_marking Hincl_pre_m)
            as Hupdate_res_ex.
          inversion_clear Hupdate_res_ex as (residual_marking' & Hupdate_res).
          
          (* Rewrites update_residual_marking in the goal. *)
          rewrite Hupdate_res.

          (* Then, inversion Hspec and specialization of one of the spec rule,
           to obtain In a (fired s'). *)
          inversion Hspec.
          clear H H0 H1 H3 H5; rename H2 into Heq_marking, H4 into Hsens_by_res.

          (* Builds SitpnIsfirable sitpn s' a *)
          rewrite (sitpn_is_firable_iff
                     sitpn s neigh_of_a a Hwell_def_sitpn Hwell_def_state Hin_lneigh)
            in Hfirable.
          rewrite (state_same_marking_firable_iff
                     sitpn s s' Hwell_def_sitpn Hwell_def_state Hwell_def_s'
                     Heq_marking a) in Hfirable.

          (* Builds IsSensitized sitpn residual_marking a *)
          apply (is_sensitized_correct sitpn residual_marking a neigh_of_a Hwell_def_sitpn
                                       Hsame_struct Hin_lneigh) in Hsens.

          (* Builds ∀ t', t' ≻ a /\ t' ∈ (fired s') ⇔ t' ∈ fired_transitions *)
          assert (Hin_eq_a_pg : In a (a :: pg)) by apply in_eq.
          specialize (Hhigh_w_sf a Hin_eq_a_pg) as Hhigh_w_sf_a.
          assert (Hsf_w_high :
                    forall t : Trans,
                      HasHigherPriority sitpn t a pgroup /\ In t (fired s') ->
                      In t fired_transitions).
          {
            intros t Hw; elim Hw; intros Hhas_high Hin_t_ff; clear Hw.
            specialize (NoDup_remove fired_transitions pg a Hnodup_app) as Hnodup_app_rm;
              apply proj1 in Hnodup_app_rm.

            (* Exploded HasHigherpriority to obtain In t pgroup. *)
            unfold HasHigherPriority in Hhas_high.
            apply proj2 in Hhas_high.
            inversion_clear Hhas_high as (Hin_t_pg & His_pred).
            apply proj2 in His_pred.

            (* Then, specializes Hin_fpg_app. *)
            specialize (Hin_fpg_app t (conj Hin_t_pg Hin_t_ff)) as Hin_t_app.
            apply in_app_or in Hin_t_app; inversion_clear Hin_t_app as [Hin_t_ftrs | Hin_t_cpg].

            (* Two cases, either t ∈ fired_transitions or t ∈ (a :: pg) *)
            - assumption.
              
            (* If t ∈ (a :: pg), then two cases. 
             - t = a
             - t ∈ pg
             In both cases, contradicts IsPredInNodupList t a pgroup. *)
            - inversion_clear Hin_t_cpg as [Heq_ta | Hin_t_tl].

              (* Case t = a *)
              + unfold IsPredInNoDupList in His_pred.
                rewrite Heq_ta in His_pred;
                  apply proj1 in His_pred;
                  elim His_pred; reflexivity.

              (* Case In t pg. *)
              + (* Builds ~IsPredInNoDuplist t a (a :: pg) *)
                assert (Hnot_is_pred : ~IsPredInNoDupList t a (a :: pg)) by
                    apply not_is_pred_in_list_if_hd.
                specialize (not_is_pred_in_dec_list His_dec Hin_t_tl) as Hnot_is_pred_in_pg.
                contradiction.
          }
          assert (Hhigh_sf_iff :
                    forall t : Trans,
                      HasHigherPriority sitpn t a pgroup /\ In t (fired s') <->
                      In t fired_transitions) by (intros t'; split; [ auto | auto ]).
          clear Hsf_w_high.

          (* Builds NoDup fired_transitions *)
          specialize (nodup_app fired_transitions (a :: pg) Hnodup_app) as Hnodup_ftrs;
            apply proj1 in Hnodup_ftrs.
          
          (* Builds residual marking definition hypothesis. *)
          rewrite Heq_marking in Hresid_m.
          assert (Hresm_def :
                    forall pr : list Trans,
                      NoDup pr ->
                      (forall t' : Trans,
                          HasHigherPriority sitpn t' a pgroup /\ In t' (fired s') <-> In t' pr) ->
                      forall (p : Place) (n : nat),
                        In (p, n) (marking s') -> In (p, n - pre_sum sitpn p pr) residual_marking).
          {
            intros pr Hnodup_pr Hpr_def p n Hin_m'.
            specialize (Hresid_m p n Hin_m') as Hin_resm.
            assert (Heq_pr_ftrs: forall t : Trans, In t pr <-> In t fired_transitions).
            {
              intros t; split.
              - intro Hin_pr.
                rewrite <- Hpr_def with (t' := t) in Hin_pr.
                rewrite Hhigh_sf_iff with (t := t) in Hin_pr.
                assumption.
              - intro Hin_ftrs.
                rewrite <- Hhigh_sf_iff with (t := t) in Hin_ftrs.
                rewrite Hpr_def with (t' := t) in Hin_ftrs.
                assumption.
            }
            specialize (pre_sum_eq_iff_incl
                          sitpn p pr fired_transitions Hnodup_pr
                          Hnodup_ftrs Heq_pr_ftrs)
              as Heq_presum.
            rewrite Heq_presum.
            assumption.
          }
          
          (* Specializes the spec rule in Hsens_by_res to obtain In a (fired s'). *)
          specialize (Hsens_by_res
                        pgroup a residual_marking Hin_pgs Hin_a_pg Hsame_struct
                        Hfirable Hresm_def Hsens) as Hin_a_sf.
          
          (* Next step, specializes IH with fired_transitions := fired_transitions ++ [a] 
           and residual_marking := residual_marking'. *)

          (* First, we need all hypotheses. *)
          
          (* Builds IsDecListCons pg pgroup *)
          specialize (is_dec_list_cons_cons His_dec) as His_dec_tl.

          (* Builds incl (fired_transitions ++ [a]) (fired s'). *)
          assert (Hincl_a_sf : incl (fired_transitions ++ [a]) (fired s')).
          {
            intros x Hin_x_app;
              apply in_app_or in Hin_x_app;
              inversion_clear Hin_x_app as [ Hin_x_ftrs | Hin_x_a ];
              [ apply (Hincl_sf x Hin_x_ftrs) |
                inversion_clear Hin_x_a as [ Heq_xa | Hin_nil ];
                [ rewrite Heq_xa in Hin_a_sf; assumption | inversion Hin_nil ] ].
          }
          
          (* Builds ∀ t ∈ pgroup, 
                  ∀ t' ∈ fired_transitions ⇒ t' ≻ t ∧ t' ∈ (fired s') *)
          assert (Hhigh_w_sf' :
                    forall t : Trans,
                      In t pg ->
                      forall t' : Trans,
                        In t' (fired_transitions ++ [a]) ->
                        HasHigherPriority sitpn t' t pgroup /\ In t' (fired s')).
          {
            intros t Hin_t_pg t' Hin_tp_app.
            apply in_app_or in Hin_tp_app;
              inversion_clear Hin_tp_app as [ Hin_tp_ftrs | Hin_tp_a ].
            - apply in_cons with (a := a) in Hin_t_pg.
              apply (Hhigh_w_sf t Hin_t_pg t' Hin_tp_ftrs).
            - inversion_clear Hin_tp_a as [ Heq_tpa | Hin_nil].
              + rewrite <- Heq_tpa; split.
                (* a ≻ t *)
                -- assert (Hsucc_a_t : HasHigherPriority sitpn a t pgroup).
                   {
                     unfold HasHigherPriority.
                     specialize (is_dec_list_cons_incl His_dec) as Hincl.
                     split. assumption.
                     split. assumption.
                     split. apply in_cons with (a := a) in Hin_t_pg. apply (Hincl t Hin_t_pg).
                     unfold IsPredInNoDupList.
                     split.
                     (* Proves a <> t. *)
                     apply NoDup_remove_2 in Hnodup_app.
                     apply not_app_in in Hnodup_app; apply proj2 in Hnodup_app.
                     apply (not_in_in_diff a t pg (conj Hnodup_app Hin_t_pg)).
                     split.
                     (* Proves NoDup pgroup. *)
                     unfold NoIntersectInPriorityGroups in Hno_inter.
                     apply (nodup_concat_gen (priority_groups sitpn) Hno_inter
                                             pgroup Hin_pgs).
                     (* Proves IsPredInlist *)
                     specialize (is_pred_in_list_in_tail a t pg Hin_t_pg) as His_pred'.
                     unfold NoIntersectInPriorityGroups in Hno_inter.
                     specialize (nodup_concat_gen (priority_groups sitpn) Hno_inter
                                                  pgroup Hin_pgs) as Hnodup_pgroup.
                     apply (is_pred_in_dec_list His_pred' His_dec Hnodup_pgroup).
                   }
                   assumption.
                (* a ∈ (fired s') *)
                -- assumption.
              + inversion Hin_nil.
          }

          (* Builds ∀ (p, n) ∈ (marking s) ⇒ (p, n - pre_sum (fired_transitions ++ [a]))  *)
          
          (* We need ∀ (p, n) ∈ residual_marking ⇒ 
                     (p, n - pre_sum sitpn p [t]) ∈ residual_marking' *)
          
          (* Builds (fs (marking s)) = (fs res_marking) *)
          unfold MarkingHaveSameStruct in *.
          assert (Hsame_residm_sm : fst (split residual_marking) = fst (split (marking s)))
            by (rewrite <- Hsame_marking_state_sitpn; rewrite <- Hsame_struct; reflexivity).
          
          (* Builds NoDup (fs residual_marking) to apply nodup_same_pair. *)
          unfold NoUnmarkedPlace in Hunm_place; unfold NoDupPlaces in Hnodup_places.
          rewrite Hunm_place in Hnodup_places;
            rewrite Hsame_marking_state_sitpn in Hnodup_places;
            rewrite <- Hsame_residm_sm in Hnodup_places.
          
          (* Builds In (t, neigh_of_t) (lneighbours sitpn) *)
          specialize (update_residual_marking_correct
                        sitpn residual_marking a neigh_of_a residual_marking'
                        Hwell_def_sitpn Hnodup_places Hin_lneigh Hupdate_res) as Hin_res_in_fin.
          
          (* Then we need pre_sum_app_add *)
          specialize (pre_sum_app_add sitpn) as Heq_presum.
          
          (* Finally, deduces the hypothesis. *)
          assert (
              Hresid'_m :
                (forall (p : Place) (n : nat),
                    In (p, n) (marking s) ->
                    In (p, n - pre_sum sitpn p (fired_transitions ++ [a])) residual_marking')
            ).
          {
            intros p n Hin_ms.
            rewrite <- Heq_marking in Hresid_m.
            apply Hresid_m in Hin_ms.
            apply Hin_res_in_fin with (n := n - pre_sum sitpn p fired_transitions) in Hin_ms.
            assert (Heq_presum' : pre_sum sitpn p [a] = pre sitpn a p) by (simpl; auto).
            rewrite <- Nat.sub_add_distr in Hin_ms.
            specialize (Heq_presum p fired_transitions a).
            rewrite <- Heq_presum' in Hin_ms.
            rewrite Heq_presum in Hin_ms.
            assumption.
          }

          (* Builds MarkingHaveSameStruct (initial_marking sitpn) residual_marking' *)
          specialize (update_residual_marking_aux_same_struct
                        sitpn residual_marking a (pre_pl neigh_of_a) residual_marking' Hupdate_res)
            as Hsame_struct'.
          rewrite Hsame_struct' in Hsame_struct.
          
          (* Finally, specializes IHpg. *)
          specialize (IHpg pgroup (fired_transitions ++ [a]) residual_marking').
          rewrite <- app_assoc in IHpg.
          specialize (IHpg Hin_pgs Hin_fpg_app His_dec_tl Hnodup_app
                           Hincl_a_sf Hhigh_w_sf' Hresid'_m Hsame_struct) as Hsitpn_fire_aux_ex.

          (* Explodes Hsitpn_fire_aux_ex. *)
          inversion_clear Hsitpn_fire_aux_ex as (final_fired & Hsitpn_fire_aux_w).
          decompose [and] Hsitpn_fire_aux_w;
            clear Hsitpn_fire_aux_w;
            rename H into Hsitpn_fire_aux, H1 into Hincl_ff_sf, H2 into Hin_ff.

          (* Instantiates the existantial variable in the goal. *)
          exists final_fired.

          split. assumption. 
          split. assumption. 
          intros t Hin_t_w.
          inversion_clear Hin_t_w as (Hin_t_apg & Hin_t_fs).
          inversion_clear Hin_t_apg as [ Heq_ta | Hin_t_pg ].
          {
            assert (Hin_a_fired : In a (fired_transitions ++ [a]))
              by (apply in_or_app; right; apply in_eq).
            specialize (sitpn_fire_aux_in_fired sitpn s residual_marking' (fired_transitions ++ [a])
                                              pg final_fired a Hin_a_fired Hsitpn_fire_aux)
              as Hin_a_ff.
            rewrite <- Heq_ta; assumption.
          }
          { apply (Hin_ff t (conj Hin_t_pg Hin_t_fs)). }
          
        (* CASE is_sensitized = Some false, then apply IHpg *)
        -- (* First, we have to specialize one of the spec rules to show
            that a ∉ (fired s'). Very useful in the following proof. *)

          inversion Hspec.
          clear H H0 H1 H3 H4; rename H2 into Heq_marking, H5 into Hnot_sens_by_res.

          (* Builds SitpnIsfirable sitpn s' a *)
          rewrite (sitpn_is_firable_iff
                     sitpn s neigh_of_a a Hwell_def_sitpn Hwell_def_state Hin_lneigh)
            in Hfirable.
          rewrite (state_same_marking_firable_iff
                     sitpn s s' Hwell_def_sitpn Hwell_def_state Hwell_def_s'
                     Heq_marking a) in Hfirable.

          (* Builds ~IsSensitized sitpn residual_marking a *)
          rewrite (not_is_sensitized_iff sitpn residual_marking a neigh_of_a
                                         Hwell_def_sitpn Hsame_struct Hin_lneigh) in Hsens.

          (* Builds ∀ t', t' ≻ a /\ t' ∈ (fired s') ⇔ t' ∈ fired_transitions *)
          assert (Hin_eq_a_pg : In a (a :: pg)) by apply in_eq.
          specialize (Hhigh_w_sf a Hin_eq_a_pg) as Hhigh_w_sf_a.
          assert (Hsf_w_high :
                    forall t : Trans,
                      HasHigherPriority sitpn t a pgroup /\ In t (fired s') ->
                      In t fired_transitions).
          {
            intros t Hw; elim Hw; intros Hhas_high Hin_t_ff; clear Hw.
            specialize (NoDup_remove fired_transitions pg a Hnodup_app) as Hnodup_app_rm;
              apply proj1 in Hnodup_app_rm.

            (* Exploded HasHigherpriority to obtain In t pgroup. *)
            unfold HasHigherPriority in Hhas_high.
            apply proj2 in Hhas_high.
            inversion_clear Hhas_high as (Hin_t_pg & His_pred).
            apply proj2 in His_pred.

            (* Then, specializes Hin_fpg_app. *)
            specialize (Hin_fpg_app t (conj Hin_t_pg Hin_t_ff)) as Hin_t_app.
            apply in_app_or in Hin_t_app; inversion_clear Hin_t_app as [Hin_t_ftrs | Hin_t_cpg].

            (* Two cases, either t ∈ fired_transitions or t ∈ (a :: pg) *)
            - assumption.
              
            (* If t ∈ (a :: pg), then two cases. 
             - t = a
             - t ∈ pg
             In both cases, contradicts IsPredInNodupList t a pgroup. *)
            - inversion_clear Hin_t_cpg as [Heq_ta | Hin_t_tl].

              (* Case t = a *)
              + unfold IsPredInNoDupList in His_pred.
                rewrite Heq_ta in His_pred;
                  apply proj1 in His_pred;
                  elim His_pred; reflexivity.

              (* Case In t pg. *)
              + (* Builds ~IsPredInNoDuplist t a (a :: pg) *)
                assert (Hnot_is_pred : ~IsPredInNoDupList t a (a :: pg)) by
                    apply not_is_pred_in_list_if_hd.
                specialize (not_is_pred_in_dec_list His_dec Hin_t_tl) as Hnot_is_pred_in_pg.
                contradiction.
          }
          assert (Hhigh_sf_iff :
                    forall t : Trans,
                      HasHigherPriority sitpn t a pgroup /\ In t (fired s') <->
                      In t fired_transitions) by (intros t'; split; [ auto | auto ]).
          clear Hsf_w_high.

          (* Builds NoDup fired_transitions *)
          specialize (nodup_app fired_transitions (a :: pg) Hnodup_app) as Hnodup_ftrs;
            apply proj1 in Hnodup_ftrs.

          (* Builds residual marking definition hypothesis. *)
          rewrite Heq_marking in Hresid_m.
          assert (Hresm_def :
                    forall pr : list Trans,
                      NoDup pr ->
                      (forall t' : Trans,
                          HasHigherPriority sitpn t' a pgroup /\ In t' (fired s') <-> In t' pr) ->
                      forall (p : Place) (n : nat),
                        In (p, n) (marking s') -> In (p, n - pre_sum sitpn p pr) residual_marking).
          {
            intros pr Hnodup_pr Hpr_def p n Hin_m'.
            specialize (Hresid_m p n Hin_m') as Hin_resm.
            assert (Heq_pr_ftrs: forall t : Trans, In t pr <-> In t fired_transitions).
            {
              intros t; split.
              - intro Hin_pr.
                rewrite <- Hpr_def with (t' := t) in Hin_pr.
                rewrite Hhigh_sf_iff with (t := t) in Hin_pr.
                assumption.
              - intro Hin_ftrs.
                rewrite <- Hhigh_sf_iff with (t := t) in Hin_ftrs.
                rewrite Hpr_def with (t' := t) in Hin_ftrs.
                assumption.
            }
            specialize (pre_sum_eq_iff_incl
                          sitpn p pr fired_transitions Hnodup_pr
                          Hnodup_ftrs Heq_pr_ftrs)
              as Heq_presum.
            rewrite Heq_presum.
            assumption.
          }
          
          (* Specializes the spec rule in Hnot_sens_by_res to obtain ~In a (fired s'). *)
          specialize (Hnot_sens_by_res
                        pgroup a residual_marking Hin_pgs Hin_a_pg Hsame_struct
                        Hfirable Hresm_def Hsens) as Hnot_in_a_sf.
          
          (* Builds hypotheses to specialize IH. *)

          specialize (is_dec_list_cons_cons His_dec) as His_dec_tl.
          apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.

          assert (Hin_fpg_app' :
                    forall t : Trans, In t pgroup /\ In t (fired s') ->
                                      In t (fired_transitions ++ pg)).
          {
            intros t Hin_t_w.
            specialize (Hin_fpg_app t Hin_t_w) as Hin_t_fpg.
            apply in_app_or in Hin_t_fpg.
            inversion_clear Hin_t_fpg as [ Hin_t_ftrs | Hin_t_pg ].
            - apply in_or_app; left; assumption.
            - inversion_clear Hin_t_pg as [ Heq_ta | Hin_t_pgtl ].
              + inversion_clear Hin_t_w as ( Hin_t_pg & Hin_t_fs ).
                rewrite Heq_ta in Hnot_in_a_sf; contradiction.
              + apply in_or_app; right; assumption.
          }

          assert (Hhigh_w_sf' :
                    forall t : Trans,
                      In t pg ->
                      forall t' : Trans,
                        In t' fired_transitions ->
                        HasHigherPriority sitpn t' t pgroup /\ In t' (fired s')).
          {
            intros t Hin_t_pg;
              apply in_cons with (a := a) in Hin_t_pg;
              apply (Hhigh_w_sf t Hin_t_pg).
          }

          rewrite <- Heq_marking in Hresid_m.
          
          specialize (IHpg pgroup fired_transitions residual_marking Hin_pgs
                           Hin_fpg_app' His_dec_tl Hnodup_app Hincl_sf
                           Hhigh_w_sf' Hresid_m Hsame_struct) as Hfire_aux_ex.

          inversion_clear Hfire_aux_ex as (final_fired & Hfire_aux_w).
          exists final_fired.
          elim Hfire_aux_w; clear Hfire_aux_w; intros Hfire_aux Hfire_aux_w.
          elim Hfire_aux_w; clear Hfire_aux_w; intros Hincl_ff Hin_ff.
          split; [assumption | split; [assumption | auto]].
          intros t Hin_t_w; elim Hin_t_w; clear Hin_t_w; intros Hin_t_pg Hin_t_fs.

          inversion_clear Hin_t_pg as [Heq_ta | Hin_t_tl].
          ++ rewrite Heq_ta in Hnot_in_a_sf; contradiction.
          ++ apply (Hin_ff t (conj Hin_t_tl Hin_t_fs)).
             
      (* CASE sitpn_is_firable = Some false. *)
      + (* First, we have to specialize one of the spec rules to show
            that a ∉ (fired s'). Very useful in the following proof. *)

        inversion Hspec.
        clear H H0 H1 H4 H5.
        rename H3 into Hnot_firable, H2 into Heq_marking.
        rewrite (not_sitpn_is_firable_iff
                   sitpn s neigh_of_a a Hwell_def_sitpn Hwell_def_state Hin_lneigh)
          in Hfirable.
        rewrite (state_same_marking_firable_iff
                   sitpn s s' Hwell_def_sitpn Hwell_def_state Hwell_def_s'
                   Heq_marking a) in Hfirable.
        specialize (Hnot_firable pgroup a Hin_pgs Hin_a_pg Hfirable) as Hnot_in_a_sf.
        
        (* Build hypotheses to specialize IHpg *)
        
        specialize (is_dec_list_cons_cons His_dec) as His_dec_tl.
        apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.

        assert (Hin_fpg_app' :
                  forall t : Trans, In t pgroup /\ In t (fired s') ->
                                    In t (fired_transitions ++ pg)).
        {
          intros t Hin_t_w.
          specialize (Hin_fpg_app t Hin_t_w) as Hin_t_fpg.
          apply in_app_or in Hin_t_fpg.
          inversion_clear Hin_t_fpg as [ Hin_t_ftrs | Hin_t_pg ].
          - apply in_or_app; left; assumption.
          - inversion_clear Hin_t_pg as [ Heq_ta | Hin_t_pgtl ].
            + inversion_clear Hin_t_w as ( Hin_t_pg & Hin_t_fs ).
              rewrite Heq_ta in Hnot_in_a_sf; contradiction.
            + apply in_or_app; right; assumption.
        }
        
        assert (Hhigh_w_sf' :
                  forall t : Trans,
                    In t pg ->
                    forall t' : Trans,
                      In t' fired_transitions ->
                      HasHigherPriority sitpn t' t pgroup /\ In t' (fired s')).
        {
          intros t Hin_t_pg;
            apply in_cons with (a := a) in Hin_t_pg;
            apply (Hhigh_w_sf t Hin_t_pg).
        }
        
        specialize (IHpg pgroup fired_transitions residual_marking Hin_pgs
                         Hin_fpg_app' His_dec_tl Hnodup_app Hincl_sf
                         Hhigh_w_sf' Hresid_m Hsame_struct) as Hfire_aux_ex.
        
        inversion_clear Hfire_aux_ex as (final_fired & Hfire_aux_w).
        exists final_fired.
        elim Hfire_aux_w; clear Hfire_aux_w; intros Hfire_aux Hfire_aux_w.
        elim Hfire_aux_w; clear Hfire_aux_w; intros Hincl_ff Hin_ff.
        split; [assumption | split; [assumption | auto]].
        intros t Hin_t_w; elim Hin_t_w; clear Hin_t_w; intros Hin_t_pg Hin_t_fs.
        
        inversion_clear Hin_t_pg as [Heq_ta | Hin_t_tl].
        
        (* Using spec to prove that t ∉ (fired s'). *)
        -- rewrite Heq_ta in Hnot_in_a_sf; contradiction.
           
        (* Applies result for IHpg. *)
        -- apply (Hin_ff t (conj Hin_t_tl Hin_t_fs)).
  Qed.
  
  (** Completeness lemma for sitpn_map_fire_aux. *)

  Lemma sitpn_map_fire_complete_aux :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (tmp_state : SitpnState)
           (pgroups : list (list Trans))
           (fired_trs : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env falling_edge ->
      
      (* Properties of tmp_state. *)
      (marking tmp_state) = (marking s) ->
      Permutation (d_intervals tmp_state) (d_intervals s') ->
      Permutation (cond_values tmp_state) (cond_values s') ->

      (* Properties of fired_trs and pgroups. *)
      IsDecListCons pgroups (priority_groups sitpn) ->
      NoDup (fired_trs ++ concat pgroups) ->
      incl s'.(fired) (fired_trs ++ concat pgroups) ->
      incl fired_trs s'.(fired) ->
      
      exists final_fired : list Trans,
        sitpn_map_fire_aux sitpn tmp_state fired_trs pgroups = Some final_fired
        /\ Permutation final_fired (fired s').
  Proof.
    intros sitpn s s' time_value env tmp_state pgroups;
      induction pgroups;
      intros fired_trs Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
             Heq_m_tmp Hperm_ditvals_tmp Hperm_conds_tmp
             His_dec Hnodup_app Hincl_sf Hincl_f.
    
    (* BASE CASE, pgroups = []. *)
    - simpl; exists fired_trs.
      split.
      + reflexivity.
      + simpl in Hincl_sf; rewrite app_nil_r in Hincl_sf.
        simpl in Hnodup_app; rewrite app_nil_r in Hnodup_app.
        explode_well_defined_sitpn_state Hwell_def_s'.

        (* NoDup l ∧ NoDup l' ∧ incl l l' ∧ incl l' l ⇒ Permutation l l' *)
        assert (Hincl_iff : forall a : Trans, In a fired_trs <-> In a (fired s'))
          by (intros a; split; [ specialize (Hincl_f a); assumption |
                                 specialize (Hincl_sf a); assumption ]). 
        apply (NoDup_Permutation Hnodup_app Hnodup_state_fired Hincl_iff).

    (* INDUCTION CASE *)
    - admit.
  Admitted.
    
  (** Completeness lemma for sitpn_map_fire. *)

  Lemma sitpn_map_fire_complete :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (tmp_state : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env falling_edge ->
      
      (* Properties of tmp_state. *)
      (marking tmp_state) = (marking s) ->
      Permutation (d_intervals tmp_state) (d_intervals s') ->
      Permutation (cond_values tmp_state) (cond_values s') ->
      
      exists final_fired : list Trans,
        sitpn_map_fire sitpn tmp_state = Some final_fired
        /\ Permutation final_fired (fired s').
  Proof.
    intros sitpn s s' time_value env tmp_state Hwell_def_sitpn
           Hwell_def_s Hwell_def_s' Hspec Heq_m_tmp
           Hperm_ditvals_tmp Hperm_conds_tmp.

    unfold sitpn_map_fire.

    (* Strategy: build premises to apply sitpn_map_fire_aux_complete. *)

    assert (His_dec_refl : IsDecListCons (priority_groups sitpn) (priority_groups sitpn))
      by (apply IsDecListCons_refl).
    assert (Hnodup_app : NoDup ([] ++ concat (priority_groups sitpn))).
    {
      explode_well_defined_sitpn;
        assert (Hnodup_app := Hno_inter);
        unfold NoIntersectInPriorityGroups in Hnodup_app;
        rewrite <- app_nil_l in Hnodup_app;
        assumption.
    }        
    assert (Hincl_f_concat : incl (fired s') (concat (priority_groups sitpn))).
    {
      explode_well_defined_sitpn;
        explode_well_defined_sitpn_state Hwell_def_s';
        unfold NoUnknownInPriorityGroups in Hno_unk_pgroups;
        intros a Hin_fired_sp;
        apply Hincl_state_fired_transs in Hin_fired_sp;
        rewrite <- Hno_unk_pgroups;
        assumption.
    }
    assert (Hincl_nil : incl [] (fired s')) by (intros a Hin_nil; inversion Hin_nil).
    
    (* Applies sitpn_map_fire_aux with then newly-built premises. *)
    apply (sitpn_map_fire_complete_aux
             sitpn s s' time_value env tmp_state (priority_groups sitpn) []
             Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
             Heq_m_tmp Hperm_ditvals_tmp Hperm_conds_tmp
             His_dec_refl Hnodup_app Hincl_f_concat Hincl_nil).
  Qed.
  
End SitpnMapFireComplete.

        
