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

Lemma pre_sum_add_rm : 
  forall (spn : Spn)
         (p : Place)
         (l : list Trans)
         (t : Trans),
    In t l -> NoDup l -> pre_sum spn p l = pre spn t p + pre_sum spn p (remove eq_nat_dec t l).
Proof.
  intros spn p l;
    functional induction (pre_sum spn p l) using pre_sum_ind;
    intros a Hin_a_l Hnodup_l.
  - inversion Hin_a_l.
  - inversion_clear Hin_a_l as [Heq_at | Hin_a_tl].
    + rewrite <- Heq_at.
      simpl; case (Nat.eq_dec t t).
      -- intro Heq_refl.
         rewrite NoDup_cons_iff in Hnodup_l; apply proj1 in Hnodup_l.
         specialize (not_in_remove_eq Nat.eq_dec t tail Hnodup_l) as Heq_rm.
         rewrite Heq_rm; reflexivity.
      -- intro Heq_diff; elim Heq_diff; reflexivity.
    + simpl; case (Nat.eq_dec a t).
      -- rewrite NoDup_cons_iff in Hnodup_l; apply proj1 in Hnodup_l.
         specialize (not_in_in_diff t a tail (conj Hnodup_l Hin_a_tl)) as Hdiff_ta.
         intro Heq_at; symmetry in Heq_at; contradiction.
      -- intro Hdiff_at.
         simpl; symmetry; rewrite Nat.add_comm.
         rewrite <- Nat.add_assoc.
         rewrite Nat.add_cancel_l; symmetry; rewrite Nat.add_comm.
         rewrite NoDup_cons_iff in Hnodup_l; apply proj2 in Hnodup_l.
         apply (IHn a Hin_a_tl Hnodup_l).
Qed.

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
  - assert (Hin_eq : In t (t :: tail)) by apply in_eq.
    rewrite Hequiv in Hin_eq.
    specialize (pre_sum_add_rm spn p l' t Hin_eq Hnodup_l') as Heq_presum.
    rewrite Heq_presum.
    rewrite Nat.add_cancel_l.
    assert (Hequiv_tl : forall t0 : Trans, In t0 tail <-> In t0 (remove Nat.eq_dec t l')).
    {
      intro t0; split.
      - intro Hin_tl; specialize (in_cons t t0 tail Hin_tl) as Hin_t0_ctl.
        rewrite NoDup_cons_iff in Hnodup_l.
        apply proj1 in Hnodup_l.
        specialize (not_in_in_diff t t0 tail (conj Hnodup_l Hin_tl)) as Hdiff_tt0.
        apply not_eq_sym in Hdiff_tt0.
        rewrite Hequiv in Hin_t0_ctl.
        rewrite in_remove_iff; apply (conj Hin_t0_ctl Hdiff_tt0).
      - intro Hin_rm.
        rewrite in_remove_iff in Hin_rm.
        elim Hin_rm; clear Hin_rm; intros Hin_t0_l' Hdiff_t0t.
        rewrite <- Hequiv in Hin_t0_l'.
        inversion_clear Hin_t0_l' as [Heq_t0t | Hin_t0_tl].
        + symmetry in Heq_t0t; contradiction.
        + assumption.
    }
    rewrite NoDup_cons_iff in Hnodup_l; apply proj2 in Hnodup_l.
    specialize (nodup_if_remove l' Hnodup_l' t Nat.eq_dec) as Hnodup_rm.
    apply (IHn (remove Nat.eq_dec t l') Hnodup_l Hnodup_rm Hequiv_tl). 
Qed.

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
      explode_well_defined_spn_state Hwell_def_s.
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

Lemma is_residual_marking_same_pr:
  forall (spn : Spn)
         (s : SpnState)
         (fired_transitions pgroup : list Trans)
         (pgroups_tail : list (list Trans))
         (fired_trs : list Trans),
    spn_fire_aux spn s (marking s) [] pgroup = Some fired_trs ->
    forall final_fired : list Trans,
      IsWellDefinedSpn spn ->
      NoDup (fired_transitions ++ concat (pgroup :: pgroups_tail)) ->
      NoDup final_fired ->
      incl final_fired (fired_transitions ++ concat (pgroup :: pgroups_tail)) ->
      IsDecListApp fired_transitions final_fired ->
      forall a : Trans,
        In a final_fired ->
        In a (fired_transitions ++ concat (pgroup :: pgroups_tail)) ->
        In a pgroup ->
        forall res_m : list (Place * nat),
          IsResidualMarking spn (marking s) res_m fired_trs a pgroup ->
          IsResidualMarking spn (marking s) res_m final_fired a pgroup.
Proof.
  intros spn s fired_transitions pgroup pgroups_tail fired_trs e0
         final_fired Hwell_def_spn Hnodup_f_pgs Hnodup_ff Hincl_ff_app
         His_dec_f_ff a Hin_ff Hin_f_concat Hin_a_pg res_m His_res.
  unfold IsResidualMarking in *.
  intros pr Hnodup_pr Hhas_high p n Hin_ms.
  assert (Hhas_high_ftrs :
            forall t' : Trans,
              HasHigherPriority spn t' a pgroup /\ In t' fired_trs <-> In t' pr).
  {
    intro t'; split.
    - intro Hw_has_high; elim Hw_has_high; clear Hw_has_high;
        intros Hhas_high_tp_a Hin_tp_ftrs.
      rewrite <- (Hhas_high t'); split.
      + assumption.
      + admit.
    - admit.
  }
  apply (His_res pr Hnodup_pr Hhas_high_ftrs p n Hin_ms).
Admitted.

(** Completeness lemma for spn_map_fire_aux. *)

Lemma spn_map_fire_aux_complete :
  forall (spn : Spn)
         (s s' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    SpnSemantics spn s s' falling_edge ->    
    forall (pgroups : list (list Trans))
           (fired_transitions : list Trans),
      IsDecListCons pgroups (priority_groups spn) ->
      NoDup (fired_transitions ++ concat pgroups) ->
      incl s'.(fired) (fired_transitions ++ concat pgroups) ->
      incl fired_transitions s'.(fired) ->
      exists final_fired : list Trans,
        spn_map_fire_aux spn s fired_transitions pgroups = Some final_fired /\
        Permutation final_fired s'.(fired).
Proof.
  intros spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s' Hspec pgroups.
  induction pgroups; intros fired_transitions His_dec Hnodup_app Hincl_sf Hincl_f.
  
  (* BASE CASE, pgroups = []. *)
  - simpl; exists fired_transitions.
    split.
    + reflexivity.
    + simpl in Hincl_sf; rewrite app_nil_r in Hincl_sf.
      simpl in Hnodup_app; rewrite app_nil_r in Hnodup_app.
      explode_well_defined_spn_state Hwell_def_s'.
      (* NoDup l ∧ NoDup l' ∧ incl l l' ∧ incl l' l ⇒ Permutation l l' *)
      
Admitted.        

(* Proof. *)
(*   intros spn s fired_transitions pgroups. *)
(*   functional induction (spn_map_fire_aux spn s fired_transitions pgroups) *)
(*              using spn_map_fire_aux_ind; *)
(*     intros final_fired Hnot_fira_not_fired *)
(*            Hsens_by_res Hnot_sens_by_res Hwell_def_spn *)
(*            Hwell_def_s Hincl_pgs Hnodup_f_pgs Hnodup_ff *)
(*            Hincl_ff_app His_dec_f_ff. *)
(*   (* BASE CASE *) *)
(*   - simpl in Hnodup_f_pgs; simpl in Hincl_ff_app. *)
(*     rewrite app_nil_r in Hnodup_f_pgs; rewrite app_nil_r in Hincl_ff_app. *)
(*     specialize (is_dec_list_app_eq_if_incl *)
(*                   Hnodup_f_pgs Hnodup_ff *)
(*                   His_dec_f_ff Hincl_ff_app) as Heq_f_ff. *)
(*     rewrite Heq_f_ff; reflexivity. *)
(*   (* GENERAL CASE *) *)
(*   - apply IHo. *)
(*     (* Subcase: not firable ⇒ not fired. *) *)
(*     + intros pgroup' t Hin_pgs_tl Hin_t_pg Hnot_fira. *)
(*       apply in_cons with (a := pgroup) in Hin_pgs_tl. *)
(*       apply (Hnot_fira_not_fired pgroup' t Hin_pgs_tl Hin_t_pg Hnot_fira). *)
(*     (* Subcase: sensitized by residual *) *)
(*     + intros pgroup' t residual_marking Hin_pgs_tl Hin_t_pg Hsame_struct *)
(*              Hfira His_res Hsens. *)
(*       apply in_cons with (a := pgroup) in Hin_pgs_tl. *)
(*       apply (Hsens_by_res pgroup' t residual_marking Hin_pgs_tl Hin_t_pg *)
(*                           Hsame_struct Hfira His_res Hsens). *)
(*     (* Subcase: not sensitized by residual *) *)
(*     + intros pgroup' t residual_marking Hin_pgs_tl Hin_t_pg Hsame_struct *)
(*              Hfira His_res Hnot_sens. *)
(*       apply in_cons with (a := pgroup) in Hin_pgs_tl. *)
(*       apply (Hnot_sens_by_res pgroup' t residual_marking Hin_pgs_tl Hin_t_pg *)
(*                               Hsame_struct Hfira His_res Hnot_sens). *)
(*     (* Subcase: IsWelldefinedspn *) *)
(*     + assumption. *)
(*     (* Subcase: IsWelldefinedspnstate *) *)
(*     + assumption. *)
(*     (* Subcase: incl pgroups_tail (priority_groups spn) *) *)
(*     + apply incl_cons_inv in Hincl_pgs; assumption. *)
(*     (* Subcase: NoDup (fired_transitions ++ fired_trs ++ concat pgroups_tail) *) *)
(*     + specialize (NoDup_app_comm *)
(*                     fired_transitions (concat (pgroup :: pgroups_tail)) Hnodup_f_pgs) *)
(*         as Hnodup_pg. *)
(*       rewrite concat_cons in Hnodup_pg. *)
(*       rewrite <- app_assoc in Hnodup_pg. *)
(*       apply nodup_app in Hnodup_pg; apply proj1 in Hnodup_pg. *)
(*       specialize (spn_fire_nodup_fired *)
(*                     spn s pgroup fired_trs Hwell_def_spn Hwell_def_s *)
(*                     Hnodup_pg e0) as Hw_nodup_incl. *)
(*       inversion Hw_nodup_incl as (Hnodup_fired_trs & Hincl_f_pg). *)
(*       rewrite <- app_assoc.  *)
(*       apply (nodup_app_incl fired_transitions pgroup (concat pgroups_tail) fired_trs  *)
(*                             Hnodup_f_pgs Hnodup_fired_trs Hincl_f_pg). *)
(*     (* Subcase: NoDup final_fired *) *)
(*     + assumption. *)
      
(*     (* Subcase: ffired ⊆ (fired_transitions ++ fired_trs ++ concat pgroups_tail) *) *)
(*     (* Three subcases:  *)
(*        a ∈ fired_transitions ∨ a ∈ pgroup ∨ a ∈ concat pgroups_tail *) *)
(*     + intros a Hin_ff. *)
(*       rewrite <- app_assoc. *)
(*       apply in_or_app. *)
(*       specialize (Hincl_ff_app a Hin_ff) as Hin_f_concat. *)
(*       specialize (in_app_or fired_transitions (concat (pgroup :: pgroups_tail)) *)
(*                             a Hin_f_concat) as Hv_f_concat. *)
(*       inversion_clear Hv_f_concat as [Hin_a_f | Hin_a_concat]. *)
(*       (* a ∈ fired_transitions *) *)
(*       -- left; assumption. *)
         
(*       (* a ∈ pgroup *) *)
(*       -- rewrite concat_cons in Hin_a_concat; *)
(*            specialize (in_app_or pgroup (concat pgroups_tail) a Hin_a_concat) as Hv_pg_concat; *)
(*            clear Hin_a_concat; *)
(*            inversion_clear Hv_pg_concat as [Hin_a_pg | Hin_a_concat]. *)
         
(*          (* Difficult case, a ∈ pgroup ∧ a ∈ ff ⇒ a ∈ fired_trs. *) *)
(*          ++ right; apply in_or_app; left. *)
(*             unfold spn_fire in e0. *)
(*             assert (Hv_in_ftrs := classic (In a fired_trs)). *)
(*             inversion_clear Hv_in_ftrs as [Hin_a_ftrs | Hnot_in_ftrs]. *)
(*             { assumption. } *)
(*             { *)
(*               (* Prepares hypotheses to specialize spn_fire_aux_not_in_final_if *) *)

(*               (* Builds In pgroup (priority_groups spn) *) *)
(*               assert (Hin_pg_pgs : In pgroup (pgroup :: pgroups_tail)) by apply in_eq. *)
(*               apply Hincl_pgs in Hin_pg_pgs. *)

(*               (* Builds IsDecListCons pgroup pgroup. *) *)
(*               assert (His_dec_cons : IsDecListCons pgroup pgroup) by apply IsDecListCons_refl. *)

(*               (* Builds NoDup ([] ++ pgroup) *) *)
(*               assert (Hnodup_nil_pg := Hnodup_f_pgs). *)
(*               rewrite concat_cons in Hnodup_nil_pg. *)
(*               apply nodup_app in Hnodup_nil_pg; apply proj2 in Hnodup_nil_pg. *)
(*               apply nodup_app in Hnodup_nil_pg; apply proj1 in Hnodup_nil_pg. *)
(*               rewrite <- app_nil_l in Hnodup_nil_pg. *)

(*               (* Builds In (p, n) (marking s) -> In (p, n - pre_sum spn p []) (marking s) *) *)
(*               assert (Hresid_m : *)
(*                         forall (p : Place) (n : nat), *)
(*                           In (p, n) (marking s) -> *)
(*                           In (p, n - pre_sum spn p []) (marking s)) *)
(*                 by (intros p n Hin_ms; simpl; rewrite Nat.sub_0_r; assumption). *)

(*               (* Builds Markinghavesamestruct (initial_marking spn) (marking s) *) *)
(*               explode_well_defined_spn_state. *)

(*               (* Builds In t'' fired -> HasHigherPriority spn t'' t pgroup /\ In t'' final_fired *) *)
(*               assert (Hf_has_high : *)
(*                         forall t : Trans, *)
(*                           In t [] -> HasHigherPriority spn t a pgroup /\ In t fired_trs) *)
(*                 by (intros t Hin_nil; inversion Hin_nil). *)

(*               (* Finally, specializes spn_fire_aux_not_in_final_if *) *)
(*               specialize (spn_fire_aux_not_in_final_if *)
(*                             spn s (marking s) [] pgroup pgroup fired_trs *)
(*                             Hwell_def_spn Hwell_def_state Hin_pg_pgs His_dec_cons *)
(*                             Hnodup_nil_pg Hresid_m Hsame_marking_state_spn *)
(*                             e0 a Hin_a_pg Hnot_in_ftrs Hf_has_high) as Hv_not_in_ff. *)

(*               (* Then uses Hv_not_in_ff and spec hypotheses  *)
(*                  to show contradictions with In a final_fired. *) *)
(*               inversion_clear Hv_not_in_ff as [Hnot_fira_a | Hnot_sens_by_res_a]. *)
(*               - assert (Hin_pg_eq : In pgroup (pgroup :: pgroups_tail)) by apply in_eq.  *)
(*                 specialize (Hnot_fira_not_fired pgroup a Hin_pg_eq Hin_a_pg Hnot_fira_a) *)
(*                   as Hnot_in_ff. *)
(*                 contradiction. *)
(*               - specialize (proj1 Hnot_sens_by_res_a) as Hfira_a. *)
(*                 apply proj2 in Hnot_sens_by_res_a. *)
(*                 inversion_clear Hnot_sens_by_res_a as (res_m & Hnot_sens_by_resm_a). *)
(*                 elim Hnot_sens_by_resm_a; intros Hsame_struct_resm H; clear Hnot_sens_by_resm_a; *)
(*                   elim H; intros His_res_resm Hnot_sens_resm_a; clear H. *)
(*                 assert (Hin_pg_eq : In pgroup (pgroup :: pgroups_tail)) by apply in_eq. *)

(*                 specialize (is_residual_marking_same_pr *)
(*                               spn s fired_transitions pgroup pgroups_tail fired_trs *)
(*                               e0 final_fired Hwell_def_spn Hnodup_f_pgs Hnodup_ff *)
(*                               Hincl_ff_app His_dec_f_ff a Hin_ff Hin_f_concat *)
(*                               Hin_a_pg res_m His_res_resm) as His_res_resm'. *)
(*                 specialize (Hnot_sens_by_res *)
(*                               pgroup a res_m Hin_pg_eq Hin_a_pg *)
(*                               Hsame_struct_resm Hfira_a His_res_resm' Hnot_sens_resm_a) *)
(*                   as Hnot_in_ff. *)
(*                 contradiction. *)
(*             } *)
(*          (* a ∈ concat pgroups_tail. *) *)
(*          ++ right; apply in_or_app; right; assumption. *)
            
(*     (* Subcase: IsDeclistapp (fired_transitions ++ fired_trs) final_fired *) *)
(*     + admit. *)
      
(*   (*  *) *)
(*   - *)
(* Admitted. *)

(** Completeness lemma for spn_map_fire. *)

Lemma spn_map_fire_complete :
  forall (spn : Spn) (s : SpnState) (s' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    SpnSemantics spn s s' falling_edge ->
    exists state : SpnState,
      spn_map_fire spn s = Some state /\ spnstate_eq s' state.
Proof.
  intros spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s' Hspec.
  unfold spn_map_fire.
  
  (* Builds hypotheses to apply spn_map_fire_aux_complete. *)
  specialize (IsDecListCons_refl (priority_groups spn)) as His_dec_refl.
  explode_well_defined_spn.
  assert (Hnodup_app := Hno_inter).
  unfold NoIntersectInPriorityGroups in Hnodup_app.
  rewrite <- app_nil_l in Hnodup_app.
  explode_well_defined_spn_state.
  unfold NoUnknownInPriorityGroups in Hno_unk_pgroups.
  assert (Hincl_f_concat : incl (fired s') (concat (priority_groups spn))).
  {
    intros a Hin_fired_sp;
      apply Hincl_state_fired_transs in Hin_fired_sp;
      rewrite <- Hno_unk_pgroups;
      assumption.
  }
  assert (Hincl_nil : incl [] (fired s')) by (intros a Hin_nil; inversion Hin_nil). 

  (* Specializes spn_map_fire_aux_complete. *)
  specialize (spn_map_fire_aux_complete
                spn s s' Hwell_def_spn Hwell_def_s Hwell_def_state Hspec
                (priority_groups spn) [] His_dec_refl Hnodup_app
                Hincl_f_concat Hincl_nil) as Hmap_fire_aux.
  
  (* Explodes then hypotheses introduced by spn_map_fire_aux_complete. *)
  inversion Hmap_fire_aux as (final_fired & Hmap_fire_aux_w).
  elim Hmap_fire_aux_w; clear Hmap_fire_aux_w; intros Hmap_fire_aux_ff Hperm_ff.
  rewrite Hmap_fire_aux_ff; exists {| fired := final_fired; marking := marking s |}.
  
  split.
  - reflexivity.
  - split.
    (* Renames hypotheses introduced by inversion of Hfalling_edge. *)
    + inversion_clear Hspec; clear H H0 H1 H3 H4 H5; rename H2 into Heq_marking.
      rewrite <- Heq_marking; simpl; reflexivity.
    + simpl; symmetry; assumption.
Qed.