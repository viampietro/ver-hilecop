(* Import Spn's types, program and specification. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Spn.SpnAnimator.
Require Import Hilecop.Spn.SpnSemantics.

(* Import useful tactics and general-purpose lemmas. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Spn.SpnTactics.

(* Import lemmas necessary from Spn's correctness proof. *)

Require Import Hilecop.Spn.SpnCoreLemmas.
Require Import Hilecop.Spn.SpnMapFireCorrect.

(* Misc. imports. *)

Require Import Omega.
Require Import Classical_Prop.

(** Let Pr(t) be the set of transitions t' such that :
    t' ≻ t ∧ t' ∈ Fired
   
   residual_marking = initial_marking - ∑ pre(ti), ∀ ti ∈ Pr(t). *)

Definition IsResidualMarking
           (spn : Spn)
           (initial_marking : list (Place * nat))
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (t : Trans)
           (pgroup : list Trans) :=
  forall (pr : list Trans),
    NoDup pr ->
    (forall t' : Trans,
        HasHigherPriority spn t' t pgroup /\ In t' fired <-> In t' pr) ->
    forall (p : Place)
           (n : nat),
      In (p, n) initial_marking ->
      In (p, n - pre_sum spn p pr) residual_marking.  

Lemma pre_sum_eq_iff_incl :
  forall (spn : Spn)
         (p : Place)
         (l l' : list Trans),
    NoDup l ->
    NoDup l' ->
    (forall t : Trans, In t l <-> In t l') ->
    pre_sum spn p l = pre_sum spn p l'.
Proof.
  intros spn p l;
    functional induction (pre_sum spn p l) using pre_sum_ind;
    intros l' Hnodup_l Hnodup_l' Hequiv.
  (* BASE CASE *)
  - functional induction (pre_sum spn p l') using pre_sum_ind.
    + reflexivity.
    + assert (Hin_eq : In t (t :: tail)) by apply in_eq.
      rewrite <- Hequiv in Hin_eq; inversion Hin_eq.
  (* GENERAL CASE *)
  - admit.
Admitted.
    
Lemma spn_fire_aux_not_in_final_if :
  forall (spn : Spn)
         (s : SpnState)
         (residual_marking : list (Place * nat))
         (fired : list Trans)
         (pg pgroup : list Trans)
         (final_fired : list Trans),
    (* Misc. hypotheses. *)
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->

    (* Hypotheses on pgroup. *)
    In pgroup spn.(priority_groups) ->

    (* Hypotheses on pg. *)
    IsDecListCons pg pgroup ->
    NoDup (fired ++ pg) ->

    (* Hypotheses on residual_marking. *)
    (forall (p : Place) (n : nat),
        In (p, n) (marking s) -> In (p, n - (pre_sum spn p fired)) residual_marking) ->
    MarkingHaveSameStruct spn.(initial_marking) residual_marking ->

    (* Function hypothesis. *)
    spn_fire_aux spn s residual_marking fired pg = Some final_fired ->

    forall (t : Trans),
      In t pg ->
      ~In t final_fired ->
      (forall t'' : Trans,
          In t'' fired -> HasHigherPriority spn t'' t pgroup /\ In t'' final_fired) ->
      ~SpnIsFirable spn s t \/
      (SpnIsFirable spn s t /\
       exists res_m : list (Place * nat),
         MarkingHaveSameStruct spn.(initial_marking) res_m /\
         IsResidualMarking spn (marking s) res_m final_fired t pgroup /\
         ~IsSensitized spn res_m t).
Proof.
  intros spn s residual_marking fired pg;
    functional induction (spn_fire_aux spn s residual_marking fired pg)
               using spn_fire_aux_ind;
    intros pgroup final_fired
           Hwell_def_spn Hwell_def_s
           Hin_spn_pgs Hdec_list Hnodup_pg
           Hresid_m Hsame_struct Hfun
           t' Hin_t_pg Hnot_in_ff Hhigh_w_ff.
  (* BASE CASE *)
  - inversion Hin_t_pg.
  (* GENERAL CASE *)
  - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].
    + assert (Hin_t_fired : In t (fired ++ [t])) by (apply in_or_app; right; apply in_eq).
      rewrite Heq_tt' in Hfun, Hin_t_fired.
      specialize (spn_fire_aux_in_fired
                    spn s residual_marking' (fired ++ [t']) tail final_fired t'
                    Hin_t_fired Hfun) as Hin_t_ff.
      contradiction.
    (* Second subcase, In t' tail then apply the induction hypothesis. *)
    + (* Builds condition 1: 
           ∀ (p, n) ∈ (marking s) -> 
             (p, n - pre_sum spn p (fired ++ [t])) ∈ residual_marking' *)
      (* We need ∀ (p, n) ∈ residual_marking ⇒ 
                     (p, n - pre_sum spn p [t]) ∈ residual_marking' *)
      (* Builds (fs (marking s)) = (fs res_marking) *)
      explode_well_defined_spn_state.
      unfold MarkingHaveSameStruct in *.
      assert (Hsame_residm_sm : fst (split residual_marking) = fst (split (marking s)))
        by (rewrite <- Hsame_marking_state_spn; rewrite <- Hsame_struct; reflexivity).
      (* Builds NoDup (fs residual_marking) to apply nodup_same_pair. *)
      explode_well_defined_spn.
      unfold NoUnmarkedPlace in Hunm_place; unfold NoDupPlaces in Hnodup_places.
      rewrite Hunm_place in Hnodup_places;
        rewrite Hsame_marking_state_spn in Hnodup_places;
        rewrite <- Hsame_residm_sm in Hnodup_places.
      (* Builds In (t, neigh_of_t) (lneighbours spn) *)
      specialize (get_neighbours_correct (lneighbours spn) t neighbours_of_t e0)
        as Hin_lneigh.
      specialize (update_residual_marking_correct
                    spn residual_marking t neighbours_of_t residual_marking'
                    Hwell_def_spn Hnodup_places Hin_lneigh e5) as Hin_res_in_fin.
      (* Then we need pre_sum_app_add *)
      specialize (pre_sum_app_add spn) as Heq_presum.
      (* Finally, deduces condition 1. *)
      assert (
          Hresid'_m :
            (forall (p : Place) (n : nat),
                In (p, n) (marking s) ->
                In (p, n - pre_sum spn p (fired ++ [t])) residual_marking')
        ).
      {
        intros p n Hin_ms.
        apply Hresid_m in Hin_ms.
        apply Hin_res_in_fin with (n := n - pre_sum spn p fired) in Hin_ms.
        assert (Heq_presum' : pre_sum spn p [t] = pre spn t p) by (simpl; auto).
        rewrite <- Nat.sub_add_distr in Hin_ms.
        specialize (Heq_presum p fired t).
        rewrite <- Heq_presum' in Hin_ms.
        rewrite Heq_presum in Hin_ms.
        assumption.
      }
      (* Builds condition 2: 
           ∀ t'' ∈ (fired ++ [t]), t'' ≻ t' ∧ t'' ∈ final_fired. *)
      assert(Hhigh_w_ff' :
               forall t'' : Trans, In t'' (fired ++ [t]) ->
                                   HasHigherPriority spn t'' t' pgroup /\ In t'' final_fired).
      {
        intros t'' Hin_fired_app;
          apply in_app_or in Hin_fired_app;
          inversion Hin_fired_app as [Hin_fired | Heq_tst]; clear Hin_fired_app.
        - apply (Hhigh_w_ff t'' Hin_fired).
        - inversion Heq_tst as [Heq_tt | Hin_nil].
          (* Two things to build, t'' ≻ t' and t'' ∈ ff. *)
          + (* First, t'' ∈ ff *)
            assert (Hin_fired_app : In t (fired ++ [t]))
              by (apply in_or_app; right; apply in_eq).
            specialize (spn_fire_aux_in_fired
                          spn s residual_marking' (fired ++ [t]) tail final_fired t
                          Hin_fired_app Hfun) as Hin_ff.
            (* Second, t'' ≻ t' *)
            assert (Hsucc_ts_tp : HasHigherPriority spn t t' pgroup).
            {
              unfold HasHigherPriority.
              specialize (is_dec_list_cons_incl Hdec_list) as Hincl.
              split. assumption. split. assumption.
              split. unfold incl in Hincl. apply (Hincl t (in_eq t tail)).
              split. unfold incl in Hincl. apply (Hincl t' (in_cons t t' tail Hin_t'_tail)).
              unfold IsPredInNoDupList.
              split.
              (* Proves t <> t'. *)
              apply NoDup_remove_2 in Hnodup_pg.
              apply not_app_in in Hnodup_pg; apply proj2 in Hnodup_pg.
              apply (not_in_in_diff t t' tail (conj Hnodup_pg Hin_t'_tail)).
              split.
              (* Proves NoDup pgroup. *)
              unfold NoIntersectInPriorityGroups in Hno_inter.
              apply (nodup_concat_gen (priority_groups spn) Hno_inter
                                      pgroup Hin_spn_pgs).
              (* Proves IsPredInlist *)
              specialize (is_pred_in_list_in_tail t t' tail Hin_t'_tail) as His_pred.
              unfold NoIntersectInPriorityGroups in Hno_inter.
              specialize (nodup_concat_gen (priority_groups spn) Hno_inter
                                           pgroup Hin_spn_pgs) as Hnodup_pgroup.
              apply (is_pred_in_dec_list His_pred Hdec_list Hnodup_pgroup).
            }
            rewrite <- Heq_tt.
            apply (conj Hsucc_ts_tp Hin_ff).
          + inversion Hin_nil.
      }
      (* Builds a few other hypotheses, and then applies IHo. *)
      apply update_residual_marking_aux_same_struct in e5.
      rewrite e5 in Hsame_struct.
      rewrite <- app_assoc in IHo.
      apply (IHo pgroup final_fired
                 Hwell_def_spn Hwell_def_state Hin_spn_pgs (is_dec_list_cons_cons Hdec_list)
                 Hnodup_pg Hresid'_m Hsame_struct Hfun t'
                 Hin_t'_tail Hnot_in_ff Hhigh_w_ff').
  (* ERROR CASE update_residual_marking = None. *)
  - inversion Hfun.
  (* CASE, is_sensitized = Some false. *)
  - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].
    (* First subcase, t = t'. *)
    + right; split.

      (* Proves IsFirable t'. *)
      apply get_neighbours_correct in e0.
      apply (spn_is_firable_correct
               spn s neighbours_of_t t
               Hwell_def_spn Hwell_def_s e0) in e1.
      rewrite <- Heq_tt'; assumption.

      (* Proves ∃ res_m, ... *)
      exists residual_marking.
      split. assumption.

      (* Proves IsResidualMarking residual_marking *)
      split. unfold IsResidualMarking.
      assert (Hpr_is_fired :
                forall t'' : Trans, 
                  HasHigherPriority spn t'' t' pgroup /\ In t'' final_fired ->
                  In t'' fired). 
      {
        intros t'' Hw; elim Hw; intros Hhas_high Hin_ts_ff; clear Hw.
        specialize (spn_fire_aux_final_fired_vee
                      spn s residual_marking fired tail final_fired t'')
          as Hff_vee.
        specialize (NoDup_remove_1 fired tail t Hnodup_pg) as Hnodup_app.
        specialize (Hff_vee Hnodup_app Hin_ts_ff Hfun) as Hin_ts_vee; clear Hff_vee.
        inversion_clear Hin_ts_vee as [Hin_fired | Hin_ts_tail].
        - assumption.
        (* If t'' ∈ tail, then ~IsPredInNoDupList t'' t' (t' :: tail) ⇒ 
             ~IsPredInNoDupList t'' t' pgroup, then contradiction. *)
        - unfold HasHigherPriority in Hhas_high.
          (* Builds ~IsPredInNoDuplist t'' t' (t' :: tail) *)
          assert (Hnot_is_pred : ~IsPredInNoDupList t'' t' (t' :: tail)) by
              apply not_is_pred_in_list_if_hd.
          rewrite Heq_tt' in Hdec_list.
          specialize (not_is_pred_in_dec_list Hdec_list Hin_ts_tail) as Hnot_is_pred_in_pg.
          decompose [and] Hhas_high; contradiction.
      }
      (* Now we can build Hpr_iff to show that pre_sum p pr = pre_sum p fired. *)
      assert (Hpr_iff :
                forall t'' : Trans,
                  HasHigherPriority spn t'' t' pgroup /\ In t'' final_fired <-> In t'' fired)
        by (intros t'0; split; [apply (Hpr_is_fired t'0) | apply (Hhigh_w_ff t'0)]).
      clear Hhigh_w_ff Hpr_is_fired.
      intros pr Hnodup_pr Hdef_pr p n Hin_m_state.
      assert (Hequiv_pr_fired : forall t : Trans, In t fired <-> In t pr).
      {
        intro t0.
        split.
        + intro Hin_t0_fired.
          rewrite <- (Hpr_iff t0) in Hin_t0_fired.
          rewrite (Hdef_pr t0) in Hin_t0_fired; assumption.
        + intro Hin_t0_pr.
          rewrite <- (Hdef_pr t0) in Hin_t0_pr.
          rewrite (Hpr_iff t0) in Hin_t0_pr; assumption.
      }
      (* NoDup fired is necessary to apply pre_sum_eq_iff_incl. *)
      specialize (nodup_app fired (t :: tail) Hnodup_pg) as Hnodup_f; apply proj1 in Hnodup_f.
      specialize (pre_sum_eq_iff_incl spn p fired pr Hnodup_f Hnodup_pr Hequiv_pr_fired)
        as Heq_pre_sum.
      rewrite <- Heq_pre_sum.
      apply (Hresid_m p n Hin_m_state).

      (* Proves ~IsSensitized spn residual t'. *)
      intro Hsens_t'.
      apply get_neighbours_correct in e0.
      rewrite <- Heq_tt' in Hsens_t'.
      specialize (is_sensitized_complete spn residual_marking t neighbours_of_t
                                         Hwell_def_spn Hsame_struct e0 Hsens_t')
        as Hsens_true.
      rewrite Hsens_true in e3; injection e3 as Heq_t_f.
      inversion Heq_t_f.
    (* Second subcase, In t' tail, apply induction hypothesis. *)
    + apply is_dec_list_cons_cons in Hdec_list. 
      apply NoDup_remove in Hnodup_pg; apply proj1 in Hnodup_pg.
      apply (IHo pgroup final_fired Hwell_def_spn Hwell_def_s 
                 Hin_spn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct
                 Hfun t' Hin_t'_tail Hnot_in_ff Hhigh_w_ff).
  (* ERROR CASE, is_sensitized = None. *)
  - inversion Hfun.
  (* CASE spn_is_firable = Some false. *)
  - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].
    (* First subcase, t = t'. *)
    + left.
      intros Hfira_t.
      rewrite <- Heq_tt' in Hfira_t.
      apply get_neighbours_correct in e0.
      specialize (spn_is_firable_complete spn s neighbours_of_t t Hwell_def_spn Hwell_def_s
                                          e0 Hfira_t) as Hfira_true.
      rewrite Hfira_true in e1; injection e1 as Heq_t_f.
      inversion Heq_t_f.
    (* Second subcase, In t' tail, apply induction hypothesis. *)
    + apply is_dec_list_cons_cons in Hdec_list. 
      apply NoDup_remove in Hnodup_pg; apply proj1 in Hnodup_pg.
      apply (IHo pgroup final_fired Hwell_def_spn Hwell_def_s 
                 Hin_spn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct
                 Hfun t' Hin_t'_tail Hnot_in_ff Hhigh_w_ff).
  (* ERROR CASE, spn_is_firable = None. *)
  - inversion Hfun.
  (* ERROR CASE, get_neighbours = None. *)
  - inversion Hfun.
Qed.

(** Completeness lemma for spn_map_fire_aux. *)

Lemma spn_map_fire_aux_complete :
  forall (spn : Spn)
         (s : SpnState)
         (fired_transitions : list Trans)
         (pgroups : list (list Trans))
         (final_fired : list Trans),
    
    (* Hypotheses on final_fired. *)
    
    (* ∀ t ∉ firable(s') ⇒ t ∉ Fired'  
       All un-firable transitions are not fired. *)
    (forall (pgroup : list Trans) (t : Trans),
        In pgroup pgroups ->
        In t pgroup ->
        ~SpnIsFirable spn s t ->
        ~In t final_fired) ->
    (* ∀ t ∈ firable(s'), t ∈ sens(M - ∑ pre(t'), ∀ t'∈ Pr(t)) ⇒ t ∈ Fired' 
       If t is sensitized by the residual marking, result of the firing of
       all higher priority transitions, then t is fired. *)
    (forall (pgroup : list Trans)
            (t : Trans)
            (residual_marking : list (Place * nat)),
        In pgroup pgroups ->
        In t pgroup ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s t ->
        IsResidualMarking spn (marking s) residual_marking final_fired t pgroup ->
        IsSensitized spn residual_marking t ->
        In t final_fired) ->
    (* ∀ t ∈ firable(s'), t ∉ sens(M - ∑ pre(t'), ∀ t' ∈ Pr(t)) ⇒ t ∉ Fired' 
       If t is not sensitized by the residual marking, result of the firing of
       all higher priority transitions, then t is not fired. *)
    (forall (pgroup : list Trans)
            (t : Trans)
            (residual_marking : list (Place * nat)),
        In pgroup pgroups ->
        In t pgroup ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s t ->
        IsResidualMarking spn (marking s) residual_marking final_fired t pgroup ->
        ~IsSensitized spn residual_marking t ->
        ~In t final_fired) ->
    
    (* Misc Hypotheses. *)
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    incl pgroups (priority_groups spn) ->
    NoDup (fired_transitions ++ concat pgroups) ->
    NoDup final_fired ->
    incl final_fired (fired_transitions ++ concat pgroups) ->
    IsDecListApp fired_transitions final_fired ->

    (* Conclusion *)
    spn_map_fire_aux spn s fired_transitions pgroups = Some final_fired.
Proof.
  intros spn s fired_transitions pgroups;
    functional induction (spn_map_fire_aux spn s fired_transitions pgroups)
               using spn_map_fire_aux_ind;
    intros final_fired Hnot_fira_not_fired
           Hsens_by_res Hnot_sens_by_res Hwell_def_spn
           Hwell_def_s Hincl_pgs Hnodup_f_pgs Hnodup_ff
           Hincl_ff_app His_dec_f_ff.
  (* BASE CASE *)
  - simpl in Hnodup_f_pgs; simpl in Hincl_ff_app.
    rewrite app_nil_r in Hnodup_f_pgs; rewrite app_nil_r in Hincl_ff_app.
    specialize (is_dec_list_app_eq_if_incl
                  Hnodup_f_pgs Hnodup_ff
                  His_dec_f_ff Hincl_ff_app) as Heq_f_ff.
    rewrite Heq_f_ff; reflexivity.
  (* GENERAL CASE *)
  - apply IHo.
    (* Subcase: not firable ⇒ not fired. *)
    + intros pgroup' t Hin_pgs_tl Hin_t_pg Hnot_fira.
      apply in_cons with (a := pgroup) in Hin_pgs_tl.
      apply (Hnot_fira_not_fired pgroup' t Hin_pgs_tl Hin_t_pg Hnot_fira).
    (* Subcase: sensitized by residual *)
    + intros pgroup' t residual_marking Hin_pgs_tl Hin_t_pg Hsame_struct
             Hfira His_res Hsens.
      apply in_cons with (a := pgroup) in Hin_pgs_tl.
      apply (Hsens_by_res pgroup' t residual_marking Hin_pgs_tl Hin_t_pg
                          Hsame_struct Hfira His_res Hsens).
    (* Subcase: not sensitized by residual *)
    + intros pgroup' t residual_marking Hin_pgs_tl Hin_t_pg Hsame_struct
             Hfira His_res Hnot_sens.
      apply in_cons with (a := pgroup) in Hin_pgs_tl.
      apply (Hnot_sens_by_res pgroup' t residual_marking Hin_pgs_tl Hin_t_pg
                              Hsame_struct Hfira His_res Hnot_sens).
    (* Subcase: IsWelldefinedspn *)
    + assumption.
    (* Subcase: IsWelldefinedspnstate *)
    + assumption.
    (* Subcase: incl pgroups_tail (priority_groups spn) *)
    + apply incl_cons_inv in Hincl_pgs; assumption.
    (* Subcase: NoDup (fired_transitions ++ fired_trs ++ concat pgroups_tail) *)
    + specialize (NoDup_app_comm
                    fired_transitions (concat (pgroup :: pgroups_tail)) Hnodup_f_pgs)
        as Hnodup_pg.
      rewrite concat_cons in Hnodup_pg.
      rewrite <- app_assoc in Hnodup_pg.
      apply nodup_app in Hnodup_pg; apply proj1 in Hnodup_pg.
      specialize (spn_fire_nodup_fired
                    spn s pgroup fired_trs Hwell_def_spn Hwell_def_s
                    Hnodup_pg e0) as Hw_nodup_incl.
      inversion Hw_nodup_incl as (Hnodup_fired_trs & Hincl_f_pg).
      rewrite <- app_assoc. 
      apply (nodup_app_incl fired_transitions pgroup (concat pgroups_tail) fired_trs 
                            Hnodup_f_pgs Hnodup_fired_trs Hincl_f_pg).
    (* Subcase: NoDup final_fired *)
    + assumption.
      
    (* Subcase: ffired ⊆ (fired_transitions ++ fired_trs ++ concat pgroups_tail) *)
    + intros a Hin_ff.
      rewrite <- app_assoc.
      apply in_or_app.
      specialize (Hincl_ff_app a Hin_ff) as Hin_f_concat.
      specialize (in_app_or fired_transitions (concat (pgroup :: pgroups_tail))
                            a Hin_f_concat) as Hv_f_concat.
      inversion_clear Hv_f_concat as [Hin_a_f | Hin_a_concat].
      -- left; assumption.
      -- rewrite concat_cons in Hin_a_concat;
           specialize (in_app_or pgroup (concat pgroups_tail) a Hin_a_concat) as Hv_pg_concat;
           clear Hin_a_concat;
           inversion_clear Hv_pg_concat as [Hin_a_pg | Hin_a_concat].
         (* Difficult case, t ∈ pgroup ∧ t ∈ ff ⇒ t ∈ fired_trs. *)
         ++ right; apply in_or_app; left.
            unfold spn_fire in e0.
            assert (Hv_in_ftrs := classic (In a fired_trs)).
            inversion_clear Hv_in_ftrs as [Hin_a_ftrs | Hnot_in_ftrs].
            { assumption. }
            {
              (* Prepares hypotheses to specialize spn_fire_aux_not_in_final_if *)
              
            }
         ++ right; apply in_or_app; right; assumption.
            
    (* Subcase: IsDeclistapp (fired_transitions ++ fired_trs) final_fired *)
    + admit.
  (*  *)
  -
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