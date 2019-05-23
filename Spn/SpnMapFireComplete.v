(* Import Spn's types, program and specification. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Spn.SpnTokenPlayer.
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

(** * Lemmas on [pre_sum] and [post_sum] functions. *)

(** ∀ t, ∀ l, t ∈ l ∧ NoDup l ⇒ pre_sum l = pre t + pre_sum (l - {t}) 
 *  Needed to prove pre_sum_eq_iff_incl. *)

Lemma pre_sum_add_rm : 
  forall (spn : Spn)
    (p : Place)
    (l : list Trans)
    (t : Trans),
    In t l ->
    NoDup l ->
    pre_sum spn p l = pre spn t p + pre_sum spn p (remove eq_nat_dec t l).
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

(** For all list of transitions l and l', if l is a permutation 
 *  of l', then pre_sum l = pre_sum l'. *)

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

(** ∀ t, ∀ l, t ∈ l ∧ NoDup l ⇒ post_sum l = post t + post_sum (l - {t}) 
 *  Needed to prove post_sum_eq_iff_incl. *)

Lemma post_sum_add_rm : 
  forall (spn : Spn)
         (p : Place)
         (l : list Trans)
         (t : Trans),
    In t l -> NoDup l -> post_sum spn p l = post spn t p + post_sum spn p (remove eq_nat_dec t l).
Proof.
  intros spn p l;
    functional induction (post_sum spn p l) using post_sum_ind;
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

(** For all list of transitions l and l', if l is a permutation 
 *  of l', then post_sum l = post_sum l'. *)

Lemma post_sum_eq_iff_incl :
  forall (spn : Spn)
         (p : Place)
         (l l' : list Trans),
    NoDup l ->
    NoDup l' ->
    (forall t : Trans, In t l <-> In t l') ->
    post_sum spn p l = post_sum spn p l'.
Proof.
  intros spn p l;
    functional induction (post_sum spn p l) using post_sum_ind;
    intros l' Hnodup_l Hnodup_l' Hequiv.
  (* BASE CASE *)
  - functional induction (post_sum spn p l') using post_sum_ind.
    + reflexivity.
    + assert (Hin_eq : In t (t :: tail)) by apply in_eq.
      rewrite <- Hequiv in Hin_eq; inversion Hin_eq.
  (* GENERAL CASE *)
  - assert (Hin_eq : In t (t :: tail)) by apply in_eq.
    rewrite Hequiv in Hin_eq.
    specialize (post_sum_add_rm spn p l' t Hin_eq Hnodup_l') as Heq_postsum.
    rewrite Heq_postsum.
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

(** * Completeness lemma for spn_fire_aux. *)

Lemma spn_fire_aux_complete :
  forall (spn : Spn)
         (s s' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    SpnSemantics spn s s' falling_edge ->
    forall (pg pgroup : list Trans)
           (fired_transitions : list Trans)
           (residual_marking : list (Place * nat)),
      
      (* Hypotheses on pg, pgroup and fired_transitions *)
      In pgroup spn.(priority_groups) ->
      (forall t : Trans, In t pgroup /\ In t (fired s') ->
                         In t (fired_transitions ++ pg)) ->
      IsDecListCons pg pgroup ->
      NoDup (fired_transitions ++ pg) ->
      incl fired_transitions (fired s') ->
      (forall t : Trans,
          In t pg ->
          forall t' : Trans,
            In t' fired_transitions ->
            HasHigherPriority spn t' t pgroup /\ In t' (fired s')) ->
      
      (* Hypotheses on residual_marking. *)
      (forall (p : Place) (n : nat),
          In (p, n) (marking s) ->
          In (p, n - (pre_sum spn p fired_transitions)) residual_marking) ->
      MarkingHaveSameStruct spn.(initial_marking) residual_marking ->

      (* Conclusion *)
      exists final_fired : list Trans,
        spn_fire_aux spn s residual_marking fired_transitions pg = Some final_fired /\
        incl final_fired s'.(fired) /\
        (forall t : Trans, In t pg /\ In t s'.(fired) -> In t final_fired).
Proof.
  intros spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s' Hspec.
  induction pg;
    intros pgroup fired_transitions residual_marking Hin_pgs Hin_fpg_app His_dec Hnodup_app
           Hincl_sf Hhigh_w_sf Hresid_m Hsame_struct.
  
  (* BASE CASE *)
  - exists fired_transitions; simpl.
    split; [ reflexivity | split; [assumption | intros t Hw; apply proj1 in Hw; inversion Hw]].

  (* INDUCTION CASE *)
  - simpl spn_fire_aux.
    
    (* First, apply get_neighbours_complete. 
       To do so, we need (a, neigh_of_a) ∈ (lneighbours spn) ∧ NoDup (lneighbours spn) *)
    explode_well_defined_spn.
    assert (Hnodup_lneighbours := Hnodup_transs).
    unfold NoDupTranss in Hnodup_lneighbours.
    rewrite Hunk_tr_neigh in Hnodup_lneighbours.

    (* Builds In a (concat (priority_groups spn)) *)
    specialize (is_dec_list_cons_incl His_dec) as Hin_a_pg.
    assert (Hin_eq : In a (a :: pg)) by apply in_eq.
    specialize (Hin_a_pg a Hin_eq); clear Hin_eq.
    specialize (in_concat a pgroup (priority_groups spn) Hin_a_pg Hin_pgs) as Hin_a_concat.
    unfold NoUnknownInPriorityGroups in Hno_unk_pgroups.
    rewrite <- Hno_unk_pgroups in Hin_a_concat.
    rewrite Hunk_tr_neigh in Hin_a_concat.
    specialize (in_fst_split_in_pair a (lneighbours spn) Hin_a_concat) as Hin_lneigh_ex.
    inversion_clear Hin_lneigh_ex as (neigh_of_a & Hin_lneigh).

    (* Specializes get_neighbours_complete, then rewrite the goal. *)
    specialize (get_neighbours_complete
                  (lneighbours spn) a neigh_of_a Hnodup_lneighbours Hin_lneigh)
      as Hget_neigh.
    rewrite Hget_neigh.    

    (* Specializes spn_is_firable_no_error to skip the error case
       when rewriting the goal. *)
    unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
    assert (Hincl_flat_lneigh : incl (flatten_neighbours neigh_of_a)
                                     (flatten_lneighbours (lneighbours spn))).
    {
      intros p Hin_p_flat;
        apply (in_neigh_in_flatten spn a neigh_of_a p Hwell_def_spn Hin_lneigh Hin_p_flat).
    }
    specialize (incl_tran Hincl_flat_lneigh Hunk_pl_neigh) as Hincl_fl_m.
    rewrite Hunm_place in Hincl_fl_m.
    explode_well_defined_spn_state Hwell_def_s.
    rewrite Hsame_marking_state_spn in Hincl_fl_m.
    clear Hsame_marking_state_spn Hincl_state_fired_transs Hnodup_state_fired.
    specialize (spn_is_firable_no_error spn s a neigh_of_a Hincl_fl_m) as Hfirable_ex.
    inversion_clear Hfirable_ex as (b & Hfirable).
    rewrite Hfirable.

    (* Two cases, either spn_is_firable = Some true or Some false. *)
    dependent induction b.

    (* CASE spn_is_firable = Some true, then continues to dig the function. *)
    + (* Specializes is_sensitized_no_error to skip the error case
         when rewriting the goal. *)
      explode_well_defined_spn_state Hwell_def_state.
      rewrite <- Hsame_marking_state_spn in Hincl_fl_m.
      rewrite Hsame_struct in Hincl_fl_m.
      specialize (is_sensitized_no_error
                    spn residual_marking a neigh_of_a Hincl_fl_m)
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
                      spn a neigh_of_a residual_marking Hincl_pre_m)
          as Hupdate_res_ex.
        inversion_clear Hupdate_res_ex as (residual_marking' & Hupdate_res).
        
        (* Rewrites update_residual_marking in the goal. *)
        rewrite Hupdate_res.

        (* Then, inversion Hspec and specialization of one of the spec rule,
           to obtain In a (fired s'). *)
        inversion Hspec.
        clear H H0 H1 H3 H5; rename H2 into Heq_marking, H4 into Hsens_by_res.

        (* Builds SpnIsfirable spn s' a *)
        rewrite (spn_is_firable_iff
                   spn s neigh_of_a a Hwell_def_spn Hwell_def_state Hin_lneigh)
          in Hfirable.
        rewrite (state_same_marking_firable_iff
                   spn s s' Hwell_def_spn Hwell_def_state Hwell_def_s'
                   Heq_marking a) in Hfirable.

        (* Builds IsSensitized spn residual_marking a *)
        apply (is_sensitized_correct spn residual_marking a neigh_of_a Hwell_def_spn
                                     Hsame_struct Hin_lneigh) in Hsens.

        (* Builds ∀ t', t' ≻ a /\ t' ∈ (fired s') ⇔ t' ∈ fired_transitions *)
        assert (Hin_eq_a_pg : In a (a :: pg)) by apply in_eq.
        specialize (Hhigh_w_sf a Hin_eq_a_pg) as Hhigh_w_sf_a.
        assert (Hsf_w_high :
                  forall t : Trans,
                    HasHigherPriority spn t a pgroup /\ In t (fired s') ->
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
                    HasHigherPriority spn t a pgroup /\ In t (fired s') <->
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
                        HasHigherPriority spn t' a pgroup /\ In t' (fired s') <-> In t' pr) ->
                    forall (p : Place) (n : nat),
                      In (p, n) (marking s') -> In (p, n - pre_sum spn p pr) residual_marking).
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
                        spn p pr fired_transitions Hnodup_pr
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
                      HasHigherPriority spn t' t pgroup /\ In t' (fired s')).
        {
          intros t Hin_t_pg t' Hin_tp_app.
          apply in_app_or in Hin_tp_app;
            inversion_clear Hin_tp_app as [ Hin_tp_ftrs | Hin_tp_a ].
          - apply in_cons with (a := a) in Hin_t_pg.
            apply (Hhigh_w_sf t Hin_t_pg t' Hin_tp_ftrs).
          - inversion_clear Hin_tp_a as [ Heq_tpa | Hin_nil].
            + rewrite <- Heq_tpa; split.
              (* a ≻ t *)
              -- assert (Hsucc_a_t : HasHigherPriority spn a t pgroup).
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
                  apply (nodup_concat_gen (priority_groups spn) Hno_inter
                                          pgroup Hin_pgs).
                  (* Proves IsPredInlist *)
                  specialize (is_pred_in_list_in_tail a t pg Hin_t_pg) as His_pred'.
                  unfold NoIntersectInPriorityGroups in Hno_inter.
                  specialize (nodup_concat_gen (priority_groups spn) Hno_inter
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
                     (p, n - pre_sum spn p [t]) ∈ residual_marking' *)
        (* Builds (fs (marking s)) = (fs res_marking) *)
        unfold MarkingHaveSameStruct in *.
        assert (Hsame_residm_sm : fst (split residual_marking) = fst (split (marking s)))
          by (rewrite <- Hsame_marking_state_spn; rewrite <- Hsame_struct; reflexivity).
        (* Builds NoDup (fs residual_marking) to apply nodup_same_pair. *)
        unfold NoUnmarkedPlace in Hunm_place; unfold NoDupPlaces in Hnodup_places.
        rewrite Hunm_place in Hnodup_places;
          rewrite Hsame_marking_state_spn in Hnodup_places;
          rewrite <- Hsame_residm_sm in Hnodup_places.
        (* Builds In (t, neigh_of_t) (lneighbours spn) *)
        specialize (update_residual_marking_correct
                      spn residual_marking a neigh_of_a residual_marking'
                      Hwell_def_spn Hnodup_places Hin_lneigh Hupdate_res) as Hin_res_in_fin.
        (* Then we need pre_sum_app_add *)
        specialize (pre_sum_app_add spn) as Heq_presum.
        (* Finally, deduces the hypothesis. *)
        assert (
            Hresid'_m :
              (forall (p : Place) (n : nat),
                  In (p, n) (marking s) ->
                  In (p, n - pre_sum spn p (fired_transitions ++ [a])) residual_marking')
          ).
        {
          intros p n Hin_ms.
          rewrite <- Heq_marking in Hresid_m.
          apply Hresid_m in Hin_ms.
          apply Hin_res_in_fin with (n := n - pre_sum spn p fired_transitions) in Hin_ms.
          assert (Heq_presum' : pre_sum spn p [a] = pre spn a p) by (simpl; auto).
          rewrite <- Nat.sub_add_distr in Hin_ms.
          specialize (Heq_presum p fired_transitions a).
          rewrite <- Heq_presum' in Hin_ms.
          rewrite Heq_presum in Hin_ms.
          assumption.
        }

        (* Builds MarkingHaveSameStruct (initial_marking spn) residual_marking' *)
        specialize (update_residual_marking_aux_same_struct
                      spn residual_marking a (pre_pl neigh_of_a) residual_marking' Hupdate_res)
          as Hsame_struct'.
        rewrite Hsame_struct' in Hsame_struct.
        
        (* Finally, specializes IHpg. *)
        specialize (IHpg pgroup (fired_transitions ++ [a]) residual_marking').
        rewrite <- app_assoc in IHpg.
        specialize (IHpg Hin_pgs Hin_fpg_app His_dec_tl Hnodup_app
                         Hincl_a_sf Hhigh_w_sf' Hresid'_m Hsame_struct) as Hspn_fire_aux_ex.

        (* Explodes Hspn_fire_aux_ex. *)
        inversion_clear Hspn_fire_aux_ex as (final_fired & Hspn_fire_aux_w).
        decompose [and] Hspn_fire_aux_w;
          clear Hspn_fire_aux_w;
          rename H into Hspn_fire_aux, H1 into Hincl_ff_sf, H2 into Hin_ff.

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
          specialize (spn_fire_aux_in_fired spn s residual_marking' (fired_transitions ++ [a])
                                            pg final_fired a Hin_a_fired Hspn_fire_aux)
            as Hin_a_ff.
          rewrite <- Heq_ta; assumption.
        }
        { apply (Hin_ff t (conj Hin_t_pg Hin_t_fs)). }
        
      (* CASE is_sensitized = Some false, then apply IHpg *)
      -- (* First, we have to specialize one of the spec rules to show
            that a ∉ (fired s'). Very useful in the following proof. *)

        inversion Hspec.
        clear H H0 H1 H3 H4; rename H2 into Heq_marking, H5 into Hnot_sens_by_res.

        (* Builds SpnIsfirable spn s' a *)
        rewrite (spn_is_firable_iff
                   spn s neigh_of_a a Hwell_def_spn Hwell_def_state Hin_lneigh)
          in Hfirable.
        rewrite (state_same_marking_firable_iff
                   spn s s' Hwell_def_spn Hwell_def_state Hwell_def_s'
                   Heq_marking a) in Hfirable.

        (* Builds ~IsSensitized spn residual_marking a *)
        rewrite (not_is_sensitized_iff spn residual_marking a neigh_of_a
                                       Hwell_def_spn Hsame_struct Hin_lneigh) in Hsens.

        (* Builds ∀ t', t' ≻ a /\ t' ∈ (fired s') ⇔ t' ∈ fired_transitions *)
        assert (Hin_eq_a_pg : In a (a :: pg)) by apply in_eq.
        specialize (Hhigh_w_sf a Hin_eq_a_pg) as Hhigh_w_sf_a.
        assert (Hsf_w_high :
                  forall t : Trans,
                    HasHigherPriority spn t a pgroup /\ In t (fired s') ->
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
                    HasHigherPriority spn t a pgroup /\ In t (fired s') <->
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
                        HasHigherPriority spn t' a pgroup /\ In t' (fired s') <-> In t' pr) ->
                    forall (p : Place) (n : nat),
                      In (p, n) (marking s') -> In (p, n - pre_sum spn p pr) residual_marking).
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
                        spn p pr fired_transitions Hnodup_pr
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
                      HasHigherPriority spn t' t pgroup /\ In t' (fired s')).
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
           
    (* CASE spn_is_firable = Some false. *)
    + (* First, we have to specialize one of the spec rules to show
            that a ∉ (fired s'). Very useful in the following proof. *)

      inversion Hspec.
      clear H H0 H1 H4 H5.
      rename H3 into Hnot_firable, H2 into Heq_marking.
      rewrite (not_spn_is_firable_iff
                 spn s neigh_of_a a Hwell_def_spn Hwell_def_state Hin_lneigh)
        in Hfirable.
      rewrite (state_same_marking_firable_iff
                 spn s s' Hwell_def_spn Hwell_def_state Hwell_def_s'
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
                    HasHigherPriority spn t' t pgroup /\ In t' (fired s')).
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
      assert (Hincl_iff : forall a : Trans, In a fired_transitions <-> In a (fired s'))
             by (intros a; split; [ specialize (Hincl_f a); assumption |
                                    specialize (Hincl_sf a); assumption ]).               
      apply (NoDup_Permutation Hnodup_app Hnodup_state_fired Hincl_iff).
      
  (* INDUCTION CASE, pgroups = a :: pgroups *)
  - simpl; unfold spn_fire.
    (* We need to specialize spn_fire_aux_complete to rewrite spn_fire_aux
       in the goal. Then, we'll apply IHpgroups. *)

    (* To specialize spn_fire_aux_complete, we need a few hypotheses: *)
    
    (* Builds In a (priority_groups spn) *)
    specialize (is_dec_list_cons_incl His_dec) as Hincl_a_pgs.
    assert (Hin_eq : In a (a :: pgroups)) by apply in_eq.
    specialize (Hincl_a_pgs a Hin_eq) as Hin_a_pgs; clear Hin_eq; clear Hincl_a_pgs.

    (* Builds IsDeclistcons a a *)
    assert (His_dec_refl : IsDecListCons a a) by apply IsDecListCons_refl.

    (* Builds NoDup ([] ++ a) *)
    specialize (nodup_app fired_transitions (concat (a :: pgroups)) Hnodup_app) as Hnodup_a.
    apply proj2 in Hnodup_a.
    rewrite concat_cons in Hnodup_a.
    apply (nodup_app a (concat pgroups)) in Hnodup_a.
    apply proj1 in Hnodup_a.
    rewrite <- app_nil_l in Hnodup_a.

    (* Builds incl [] (fired s'). *)
    assert (Hincl_nil : incl [] (fired s')) by (intros x Hin_nil; inversion Hin_nil).

    (* Builds ∀ t ∈ a ⇒ t' ∈ [] ⇒ t' ≻ t ∧ t' ∈ (fired s'). *)
    assert (Hhigh_w_fired :
              forall t : Trans,
                In t a ->
                forall t' : Trans,
                  In t' [] ->
                  HasHigherPriority spn t' t a /\ In t' (fired s'))
      by (intros t Hin_a t' Hin_nil; inversion Hin_nil).

    (* Builds ∀ (p, n) ∈ (marking s) ⇒ (p, n - pre_sum spn p []) ∈ (marking s) *)
    assert (Hresid_m :
              forall (p : Place) (n : nat),
                In (p, n) (marking s) -> In (p, n - pre_sum spn p []) (marking s))
      by (simpl; intros; rewrite Nat.sub_0_r; assumption).

    (* Builds MarkingHaveSameStruct (initial_marking spn) (marking s) *)
    explode_well_defined_spn_state Hwell_def_s.
    clear Hincl_state_fired_transs Hnodup_state_fired.
    rename Hsame_marking_state_spn into Hsame_struct.

    (* Builds ∀ t, t ∈ pgroup ∧ t ∈ (fired s') ⇒ t ∈ (fired_transitions ++ pg) *)
    assert (Hin_fpg_app :
              forall t : Trans,
                In t a /\ In t (fired s') ->
                In t ([] ++ a)) by (intros t Hin_t_a; apply proj1 in Hin_t_a; auto).

    (* Then, specialize spn_fire_aux *)
    specialize (spn_fire_aux_complete
                  spn s s' Hwell_def_spn Hwell_def_state Hwell_def_s' Hspec
                  a a [] (marking s) Hin_a_pgs Hin_fpg_app His_dec_refl Hnodup_a Hincl_nil
                  Hhigh_w_fired Hresid_m Hsame_struct) as Hspn_fire_aux_ex.

    (* Inversion of Hspn_fire_aux_ex to rewrite spn_fire_aux. *)
    inversion_clear Hspn_fire_aux_ex as (fired_trs & Hspn_fire_aux_w).
    elim Hspn_fire_aux_w; clear Hspn_fire_aux_w; intros Hspn_fire_aux Hincl_w.
    elim Hincl_w; clear Hincl_w; intros Hincl_ftrs Hin_ftrs.
    rewrite Hspn_fire_aux.

    (* Then apply IHpgroups with fired_transitions := fired_transitions ++ fired_trs *)
    apply IHpgroups with (fired_transitions := fired_transitions ++ fired_trs).

    (* 4 subgoals, 3 trivials, 1 difficult. *)
    + apply (is_dec_list_cons_cons His_dec).
    + rewrite concat_cons in Hnodup_app.
      specialize (spn_fire_aux_nodup_fired spn s (marking s) [] a fired_trs
                                           Hwell_def_spn Hwell_def_state Hnodup_a
                                           Hspn_fire_aux) as Hnodup_incl_w.
      inversion_clear Hnodup_incl_w as (Hnodup_ftrs & Hincl_ftrs_a).
      rewrite <- app_assoc.
      apply (nodup_app_incl fired_transitions a (concat pgroups) fired_trs
                            Hnodup_app Hnodup_ftrs Hincl_ftrs_a).
    + intros x Hin_x_fsp.
      rewrite <- app_assoc.
      specialize (Hincl_sf x Hin_x_fsp).
      apply in_app_or in Hincl_sf.
      inversion_clear Hincl_sf as [Hin_x_f | Hin_x_concat].
      -- apply in_or_app; left; assumption.
      -- rewrite concat_cons in Hin_x_concat.
         apply in_app_or in Hin_x_concat; inversion_clear Hin_x_concat as [Hin_x_a | Hin_x_conc].
         {
           specialize (Hin_ftrs x (conj Hin_x_a Hin_x_fsp));
             apply in_or_app; right; apply in_or_app; left; assumption.
         }
         { do 2 (apply in_or_app; right); assumption. }           
    + intros x Hin_x_app;
        apply in_app_or in Hin_x_app;
        inversion_clear Hin_x_app as [Hin_x_fired | Hin_x_ftrs];
        [ apply (Hincl_f x Hin_x_fired) | apply (Hincl_ftrs x Hin_x_ftrs) ].
Qed.        

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
  explode_well_defined_spn_state Hwell_def_s'.
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

