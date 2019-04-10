(* Import Spn's types, program and specification. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Spn.SpnAnimator.
Require Import Hilecop.Spn.SpnSemantics.

(* Import core lemmas necessary for Spn's correctness proof. *)

Require Import Hilecop.Spn.SpnCoreLemmas.

(* Import useful tactics and general-purpose lemmas. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Spn.SpnTactics.

Require Import Omega.
Require Import Classical_Prop.

(*!===========================================!*)
(*!=== LEMMAS ON spn_fire and spn_map_fire ===!*)
(*!===========================================!*)

(** ** Lemmas on spn_fire and spn_map_fire. *)

(** *** Proof spn_map_fire returns a well-defined SpnState. *)

Section SpnMapFireWellDefinedState.

  (** Under some hypotheses, all fired transitions returned by spn_fire_aux
      are included in [spn.(transs)]. *)

  Lemma spn_fire_aux_incl_fired_transs :
    forall (spn : Spn)
           (s : SpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg : list Trans)
           (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      incl (fired ++ pg) spn.(transs) ->
      spn_fire_aux spn s residual_marking fired pg = Some final_fired ->
      incl final_fired spn.(transs).
  Proof.
    intros spn s residual_marking fired pg;
      functional induction (spn_fire_aux spn s residual_marking fired pg)
                 using spn_fire_aux_ind;
      intros final_fired Hwell_def_spn Hwell_def_state Hincl_f_pg Hfun.
    (* BASE CASE *)
    - injection Hfun;
        intro Heq_fired;
        rewrite <- Heq_fired;
        rewrite <- app_nil_end in Hincl_f_pg; assumption.
    (* GENERAL CASE, the strategy is to apply the induction hypothesis. *)
    - rewrite <- app_assoc in IHo.
      apply (IHo final_fired Hwell_def_spn Hwell_def_state Hincl_f_pg Hfun).
    (* CASE update_residual_marking = None. *)
    - inversion Hfun.
    (* CASE is_sensitized = Some false, the strategy is to apply IH. *)
    (* First, builds incl (fired ++ tail) (transs spn) *)
    - apply incl_app_inv in Hincl_f_pg; elim Hincl_f_pg; intros Hincl_f Hincl_pg.
      apply incl_cons_inv in Hincl_pg.
      specialize (incl_app Hincl_f Hincl_pg) as Hincl_f_tail.
      (* Applies IHo *)
      apply (IHo final_fired Hwell_def_spn Hwell_def_state Hincl_f_tail Hfun).
    (* CASE is_sensitized returns None. *)
    - inversion Hfun.
    (* CASE spn_is_firable returns Some false. *)
    (* First, builds incl (fired ++ tail) (transs spn) *)
    - apply incl_app_inv in Hincl_f_pg; elim Hincl_f_pg; intros Hincl_f Hincl_pg.
      apply incl_cons_inv in Hincl_pg.
      specialize (incl_app Hincl_f Hincl_pg) as Hincl_f_tail.
      (* Applies IHo *)
      apply (IHo final_fired Hwell_def_spn Hwell_def_state Hincl_f_tail Hfun).
    (* CASE spn_is_firable returns None. *)
    - inversion Hfun.
    (* CASE get_neighbours returns None. *)
    - inversion Hfun.
  Qed.  
  
  (** Under some hypotheses, all fired transitions returned by spn_fire
      are included in [spn.(transs)]. *)
  
  Lemma spn_fire_incl_fired_transs :
    forall (spn : Spn)
           (s : SpnState)
           (pgroup : list Trans)
           (fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      In pgroup spn.(priority_groups) ->
      spn_fire spn s pgroup = Some fired ->
      incl fired spn.(transs).
  Proof.
    intros spn s pgroup fired Hwell_def_spn Hwell_def_state Hin_spn_pgs Hfun.
    unfold spn_fire in Hfun.
    (* Builds incl ([] ++ pgroup) (transs spn)) *)
    explode_well_defined_spn.
    unfold NoUnknownInPriorityGroups in *.
    assert (Hincl_pg_transs : incl pgroup (transs spn))
      by (intros t Hin_pgroup;
          specialize (in_concat t pgroup (priority_groups spn) Hin_pgroup Hin_spn_pgs)
            as Hin_concat_pgs;
          rewrite Hno_unk_pgroups; assumption).
    rewrite <- app_nil_l with (l := pgroup) in Hincl_pg_transs.
    (* Apply spn_fire_aux_incl_fired_transs *)
    apply (spn_fire_aux_incl_fired_transs
             spn s (marking s) [] pgroup fired
             Hwell_def_spn Hwell_def_state Hincl_pg_transs Hfun).
  Qed.
  
  (** Under some hypotheses, all fired transitions returned by 
      [spn_map_fire_aux spn s fired pgroups] are included
      in the list of transitions [spn.(transs)]. *)
  
  Lemma spn_map_fire_aux_incl_fired_transs :
    forall (spn : Spn)
           (s : SpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      incl pgroups spn.(priority_groups) ->
      incl fired spn.(transs) ->
      spn_map_fire_aux spn s fired pgroups = Some final_fired ->
      incl final_fired spn.(transs).
  Proof.
    intros spn s fired pgroups;
      functional induction (spn_map_fire_aux spn s fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hwell_def_spn Hwell_def_state Hincl_pgs Hincl_fired Hfun.
    (* BASE CASE *)
    - injection Hfun; intro Heq_fired; rewrite <- Heq_fired; assumption.
    (* GENERAL CASE, applying induction hypothesis. *)
    - specialize (incl_cons_inv pgroup pgroups_tail (priority_groups spn) Hincl_pgs) as Hincl_pgs'.
      (* Builds incl (fired_transitions ++ fired_trs) (transs spn). 
         First, we need (incl fired_trs (transs spn)), then apply incl_app. *)
      assert (Hin_pgs_tail : In pgroup (pgroup :: pgroups_tail)) by apply in_eq.
      specialize (Hincl_pgs pgroup Hin_pgs_tail) as Hin_spn_pgs.
      specialize (spn_fire_incl_fired_transs
                    spn s pgroup fired_trs Hwell_def_spn
                    Hwell_def_state Hin_spn_pgs e0) as Hincl_fired'.
      specialize (incl_app Hincl_fired Hincl_fired') as Hincl_app.
      apply (IHo final_fired Hwell_def_spn Hwell_def_state Hincl_pgs' Hincl_app Hfun).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (* Under some hypotheses, the list of fired transitions returned by 
     [spn_fire_aux spn s pgroup] contains no duplicate and is included in [pgroup]. *)

  Lemma spn_fire_aux_nodup_fired :
    forall (spn : Spn)
           (s : SpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg : list Trans)
           (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      NoDup (fired ++ pg) ->
      spn_fire_aux spn s residual_marking fired pg = Some final_fired ->
      NoDup final_fired /\ incl final_fired (fired ++ pg). 
  Proof.
    intros spn s residual_marking fired pg final_fired;
      functional induction (spn_fire_aux spn s residual_marking fired pg)
                 using spn_fire_aux_ind;
      intros Hwell_def_spn Hwell_def_state Hnodup_app Hfun.
    (* BASE CASE, pg = [] *)
    - rewrite <- app_nil_end in Hnodup_app.
      assert (Hincl_refl : incl final_fired final_fired) by apply incl_refl.
      rewrite <- app_nil_end.
      injection Hfun; intros Heq; rewrite Heq in *.
      apply (conj Hnodup_app Hincl_refl).
    (* GENERAL CASE *)
    - rewrite <- app_assoc in IHo.
      apply (IHo Hwell_def_spn Hwell_def_state Hnodup_app Hfun).
    (* ERROR CASE, update_residual_marking returns None *)
    - inversion Hfun.
    (* CASE is_sensitized = Some false *)
    - apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.
      specialize (IHo Hwell_def_spn Hwell_def_state Hnodup_app Hfun) as Hw.
      elim Hw; intros Hnodup_ff Hincl_ftail.
      split.
      + assumption.
      + intros a Hin_ff. specialize (Hincl_ftail a Hin_ff) as Hin_ftail.
        apply in_or_app.
        apply in_app_or in Hin_ftail; elim Hin_ftail; intro Hin.
        -- auto.
        -- apply in_cons with (a := t) in Hin; auto.
    (* ERROR CASE, is_sensitized = None *)
    - inversion Hfun.
    (* CASE spn_is_firable = Some false *)
    - apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.
      specialize (IHo Hwell_def_spn Hwell_def_state Hnodup_app Hfun) as Hw.
      elim Hw; intros Hnodup_ff Hincl_ftail.
      split.
      + assumption.
      + intros a Hin_ff. specialize (Hincl_ftail a Hin_ff) as Hin_ftail.
        apply in_or_app.
        apply in_app_or in Hin_ftail; elim Hin_ftail; intro Hin.
        -- auto.
        -- apply in_cons with (a := t) in Hin; auto.
    (* ERROR CASE *)
    - inversion Hfun.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.
  
  (* Under some hypotheses, the list of fired transitions returned by 
     [spn_fire spn s pgroup] contains no duplicate and is included in [pgroup]. *)
  
  Lemma spn_fire_nodup_fired :
    forall (spn : Spn)
           (s : SpnState)
           (pgroup : list Trans)
           (fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      NoDup pgroup ->
      spn_fire spn s pgroup = Some fired ->
      NoDup fired /\ incl fired pgroup.
  Proof.
    intros spn s pgroup fired Hwell_def_spn Hwell_def_state Hnodup_pg Hfun.
    unfold spn_fire in Hfun.
    rewrite <- app_nil_l in Hnodup_pg.
    apply (spn_fire_aux_nodup_fired spn s (marking s) [] pgroup fired
                                    Hwell_def_spn Hwell_def_state Hnodup_pg Hfun).
  Qed.
  
  (** Under some hypotheses, the list of fired transitions returned by 
      [spn_map_fire_aux spn s fired pgroups] contains no duplicate. *)
  
  Lemma spn_map_fire_aux_nodup_fired :
    forall (spn : Spn)
           (s : SpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      NoDup (fired ++ (concat pgroups)) ->
      spn_map_fire_aux spn s fired pgroups = Some final_fired ->
      NoDup final_fired.
  Proof.
    intros spn s fired pgroups;
      functional induction (spn_map_fire_aux spn s fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hwell_def_spn Hwell_def_state Hnodup_fired_pgs Hfun.
    (* BASE CASE, pgroups = []. *)
    - simpl in Hnodup_fired_pgs;
        rewrite <- app_nil_end with (l := fired_transitions) in Hnodup_fired_pgs.
      injection Hfun; intros Heq_fired; rewrite <- Heq_fired; assumption.
    (* GENERAL CASE *)
    (* Builds (NoDup pgroup) to apply spn_fire_nodup_fired. *)
    - rewrite concat_cons in Hnodup_fired_pgs.
      specialize (nodup_app fired_transitions (pgroup ++ concat pgroups_tail) Hnodup_fired_pgs)
        as Hnodup_fpgs_wedge.
      elim Hnodup_fpgs_wedge; intros Hnodup_fired Hnodup_pg.
      apply nodup_app in Hnodup_pg; apply proj1 in Hnodup_pg. 
      specialize (spn_fire_nodup_fired spn s pgroup fired_trs Hwell_def_spn Hwell_def_state
                                       Hnodup_pg e0) as Hnodup_f_w_incl.
      (* Applies nodup_app_incl to get 
         NoDup ((fired_transitions ++ fired_trs) ++ concat pgroups_tail) *)
      elim Hnodup_f_w_incl; intros Hnodup_ftrs Hincl_fpg.
      specialize (nodup_app_incl fired_transitions pgroup (concat pgroups_tail) fired_trs
                                 Hnodup_fired_pgs Hnodup_ftrs Hincl_fpg)
        as Hnodup_ff_concat.
      rewrite app_assoc in Hnodup_ff_concat.
      (* Applies IHo *)
      apply (IHo final_fired Hwell_def_spn Hwell_def_state Hnodup_ff_concat Hfun).
    (* CASE spn_fire returns None. *)
    - inversion Hfun.
  Qed.

  (** ∀ spn, s, such that IsWelldefinedspn spn ∧ IsWelldefinedspnstate spn s,
      spn_map_fire spn s = Some s' ⇒ IsWelldefinedspnstate spn s' *)
  
  Lemma spn_map_fire_well_defined_state :
    forall (spn : Spn) (s s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      spn_map_fire spn s = Some s' ->
      IsWellDefinedSpnState spn s'.
  Proof.
    intros spn s;
      functional induction (spn_map_fire spn s) using spn_map_fire_ind;
      intros s' Hwell_def_spn Hwell_def_s Hfun.
    (* GENERAL CASE *)
    - unfold IsWellDefinedSpnState; split.
      (* Proves MarkingHaveSameStruct (initial_marking spn) (marking s'). 
         Easy because marking is not updated between s and s'. *)
      + explode_well_defined_spn_state Hwell_def_s.
        injection Hfun; intro Heq_s'; rewrite <- Heq_s'; simpl; assumption.
      + split;
          assert (Hincl_pgs : incl spn.(priority_groups) spn.(priority_groups))
          by (apply incl_refl);
          assert (Hincl_nil : incl [] spn.(transs)) by (intros a Hin_nil; inversion Hin_nil);
          injection Hfun; intro Heq_s'; rewrite <- Heq_s'; simpl.
        (* Proves (incl s'.(fired) spn.(transs)) *)
        -- apply (spn_map_fire_aux_incl_fired_transs
                    spn s [] (priority_groups spn) fired Hwell_def_spn Hwell_def_s
                    Hincl_pgs Hincl_nil e).
        (* Proves (NoDup s'.(fired)) *)
        -- explode_well_defined_spn.
           unfold NoIntersectInPriorityGroups in *.
           rewrite <- app_nil_l in Hno_inter. 
           apply (spn_map_fire_aux_nodup_fired
                    spn s [] (priority_groups spn) fired Hwell_def_spn Hwell_def_s
                    Hno_inter e).
    (* CASE OF ERROR *)
    - inversion Hfun.
  Qed.
  
End SpnMapFireWellDefinedState.

(** *** First part of correctness proof *)

(** The goal in this part is to prove: 

    spn_map_fire = Some s' ⇒ ∀ t ∉ firable(s') ⇒ t ∉ Fired'  

    All un-firable transitions are not fired. *)

Section SpnNotFirableNotFired.

  (** ∀ t ∈ fired, 
      spn_fire_aux spn state residual_marking fired group = Some final_fired ⇒ 
      t ∈ final_fired *)
  
  Lemma spn_fire_aux_in_fired :
    forall (spn : Spn)
           (state : SpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pgroup : list Trans)
           (final_fired : list Trans)
           (t : Trans),
      In t fired ->
      spn_fire_aux spn state residual_marking fired pgroup = Some final_fired ->
      In t final_fired.
  Proof.
    intros spn state residual_marking fired pgroup;
      functional induction (spn_fire_aux spn state residual_marking fired pgroup)
                 using spn_fire_aux_ind;
      intros final_fired t' Hin_t_fired Hfun.
    (* BASE CASE *)
    - injection Hfun; intro Heq; rewrite <- Heq; assumption.
    (* GENERAL CASE *)
    - apply or_introl with (B := In t' [t]) in Hin_t_fired.
      apply in_or_app in Hin_t_fired.
      apply (IHo final_fired t' Hin_t_fired Hfun).
    (* ERROR CASE, update_residual_marking = None. *)
    - inversion Hfun.
    (* CASE is_sensitized = Some false. *)
    - apply (IHo final_fired t' Hin_t_fired Hfun).
    (* ERROR CASE, is_sensitized = None. *)
    - inversion Hfun.
    (* CASE spn_is_firable = Some false. *)
    - apply (IHo final_fired t' Hin_t_fired Hfun).
    (* ERROR CASE, spn_is_firable = None. *)
    - inversion Hfun.
    (* ERROR CASE, get_neighbours = None. *)
    - inversion Hfun.
  Qed.
  
  (** ∀ t ∉ pgroup, t ∉ fired, 
      spn_fire_aux spn state residual_marking fired group = Some final_fired ⇒ 
      t ∉ final_fired *)
  
  Lemma spn_fire_aux_not_in_not_fired :
    forall (spn : Spn)
           (state : SpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pgroup : list Trans)
           (final_fired : list Trans)
           (t : Trans),
      ~In t fired ->
      ~In t pgroup ->
      spn_fire_aux spn state residual_marking fired pgroup = Some final_fired ->
      ~In t final_fired.
  Proof.
    intros spn state residual_marking fired pgroup;
      functional induction (spn_fire_aux spn state residual_marking fired pgroup)
                 using spn_fire_aux_ind;
      intros final_fired t' Hnot_in_fired Hnot_in_pg Hfun.
    (* Base case, pgroup = []. *)
    - injection Hfun; intro Heq; rewrite <- Heq; assumption.
    (* General case, all went well. *)
    - apply not_in_cons in Hnot_in_pg.
      elim Hnot_in_pg; intros Hneq_t Hnot_in_tail.
      assert (Hnot_in_tt: ~In t' [t])
        by (apply (diff_not_in t' t Hneq_t)).
      assert (Hnot_in_app : ~In t' (fired ++ [t]))
        by (apply (not_in_app t' fired [t] (conj Hnot_in_fired Hnot_in_tt))).
      apply (IHo final_fired t' Hnot_in_app Hnot_in_tail Hfun).
    - inversion Hfun.
    (* Case is_sensitized = Some false, apply induction hypothesis. *)
    - apply not_in_cons in Hnot_in_pg; elim Hnot_in_pg; intros Hdiff_tt Hnot_in_tail.
      apply (IHo final_fired t' Hnot_in_fired Hnot_in_tail Hfun).
    - inversion Hfun.
    (* Case spn_is_firable = Some false, apply induction hypothesis. *)
    - apply not_in_cons in Hnot_in_pg; elim Hnot_in_pg; intros Hdiff_tt Hnot_in_tail.
      apply (IHo final_fired t' Hnot_in_fired Hnot_in_tail Hfun).
    - inversion Hfun.
    - inversion Hfun.
  Qed.

  (** ∀ t ∈ pgroup, t ∉ fired, t ∉ firable(state),
      spn_fire_aux spn state residual_marking fired group = Some final_fired ⇒ 
      t ∉ final_fired *)
  
  Theorem spn_fire_aux_not_firable_not_fired :
    forall (spn : Spn)
           (state : SpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg : list Trans)
           (pgroup : list Trans)
           (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn state ->
      In pgroup spn.(priority_groups) ->
      NoDup pg ->
      incl pg pgroup ->
      spn_fire_aux spn state residual_marking fired pg = Some final_fired ->
      (forall t : Trans,
          In t pg ->
          ~In t fired ->
          ~SpnIsFirable spn state t ->
          ~In t final_fired).
  Proof.
    intros spn state residual_marking fired pg;
      functional induction (spn_fire_aux spn state residual_marking fired pg)
                 using spn_fire_aux_ind;
      intros pgroup final_fired Hwell_def_spn Hwell_def_state Hin_pgroups
             Hnodup_pg Hincl_pg Hfun t' Hin_pg Hnot_in_fired Hnot_firable.
    (* Base case, pg = []. *)
    - inversion Hin_pg.
    (* Case spn_is_firable = Some true, impossible regarding
       the hypotheses. *)
    - apply in_inv in Hin_pg; elim Hin_pg.
      (* Case t' = t. We have to show ~SpnIsFirable -> spn_is_firable = Some false,
         then show a contradiction. *)
      + intro Heq_t.
        elimtype False; apply Hnot_firable.
        (* Builds In (t, neighbours_of_t) spn.(lneighbours), 
           necessary to apply spn_is_firable_correct. *)
        generalize (get_neighbours_correct spn.(lneighbours) t neighbours_of_t e0)
          as Hin_lneigh; intro.
        (* Generalizes spn_is_firable_correct. *)
        generalize (spn_is_firable_correct
                      spn state neighbours_of_t t Hwell_def_spn Hwell_def_state
                      Hin_lneigh e1) as Hfirable; intro.
        rewrite <- Heq_t; assumption.
      (* Induction case. *)
      + intro Hin_tail.
        apply IHo with (pgroup := pgroup).
        -- assumption.
        -- assumption.
        -- assumption.
        -- apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg; auto.
        -- unfold incl; intros t'' Hin_tail'; apply in_cons with (a := t) in Hin_tail'.
           apply (Hincl_pg t'' Hin_tail').
        -- assumption.
        -- assumption.
        -- intro Hin_fired_app; apply in_app_or in Hin_fired_app; elim Hin_fired_app.
           { intro Hin_fired; apply (Hnot_in_fired Hin_fired). }
           { intro Hin_tt; apply in_inv in Hin_tt; elim Hin_tt.
             ++ intro Heq_tt.
                apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg.
                intros Hnot_in_tail Hnodup_tail.
                rewrite Heq_tt in Hnot_in_tail; apply (Hnot_in_tail Hin_tail).
             ++ auto.
           }
        -- assumption.
    (* Case update_residual_marking returns None. *)
    - inversion Hfun.
    (* Case is_sensitized returns Some false. *)
    - apply IHo with (pgroup := pgroup).
      + assumption.
      + assumption.
      + assumption.
      + apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg; auto.
      + unfold incl; intros t'' Hin_tail'; apply in_cons with (a := t) in Hin_tail'.
        apply (Hincl_pg t'' Hin_tail').
      + assumption.
      + apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg.
        intros Hnot_in_tail Hnodup_tail.
        apply in_inv in Hin_pg; elim Hin_pg.
        -- intro Heq_t.
           elimtype False; apply Hnot_firable.
           (* Builds In (t, neighbours_of_t) spn.(lneighbours), 
              necessary to apply spn_is_firable_correct. *)
           generalize (get_neighbours_correct spn.(lneighbours) t neighbours_of_t e0)
             as Hin_lneigh; intro.
           (* Generalizes spn_is_firable_correct. *)
           generalize (spn_is_firable_correct
                         spn state neighbours_of_t t Hwell_def_spn Hwell_def_state
                         Hin_lneigh e1) as Hfirable; intro.
           rewrite <- Heq_t; assumption.
        -- auto.
      + assumption.
      + assumption.
    (* Case is_sensitized returns None. *)
    - inversion Hfun.
    (* Case spn_is_firable returns Some false. *)
    - apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg; intros Hnot_in_tail Hnodup_tail.
      apply in_inv in Hin_pg; elim Hin_pg.
      (* When t = t', then t ∉ fired and t ∉ tail ⇒ t ∉ final_fired 
         thanks to lemma spn_fire_aux_not_in_not_fired. *)
      + intro Heq_tt. rewrite Heq_tt in Hnot_in_tail.
        apply (spn_fire_aux_not_in_not_fired
                 spn state residual_marking fired tail final_fired t'
                 Hnot_in_fired Hnot_in_tail Hfun).
      + intro Hin_tail; apply IHo with (pgroup := pgroup).
        -- assumption.
        -- assumption.
        -- assumption.
        -- apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg; auto.
        -- unfold incl; intros t'' Hin_tail'; apply in_cons with (a := t) in Hin_tail'.
           apply (Hincl_pg t'' Hin_tail').
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
    (* Case spn_is_firable = None *)
    - inversion Hfun.
    (* Case get_neighbours = None *)
    - inversion Hfun.
  Qed.

  (** ∀ pgroup ∈ spn.(priority_groups),
      spn_fire spn state pgroup = Some fired ⇒ 
      ∀ t ∈ pgroup, t ∉ firable(state) ⇒ t ∉ fired. *)
  
  Theorem spn_fire_not_firable_not_fired :
    forall (spn : Spn)
           (state : SpnState)
           (pgroup : list Trans)
           (fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn state ->
      In pgroup spn.(priority_groups) ->
      spn_fire spn state pgroup = Some fired ->
      (forall t : Trans,
          In t pgroup ->
          ~SpnIsFirable spn state t ->
          ~In t fired).
  Proof.
    unfold spn_fire.
    intros spn state pgroup fired Hwell_def_spn Hwell_def_state
           Hin_pgroups Hfun t Hin_pgroup Hnot_firable.
    (* Builds (incl pgroup pgroup). *)
    assert (Hincl_pgroup : incl pgroup pgroup) by (apply incl_refl).
    (* Builds NoDup pgroup. *)
    unfold IsWellDefinedSpn in Hwell_def_spn;
      decompose [and] Hwell_def_spn; intros; rename_well_defined_spn.
    unfold NoDupTranss in *.
    unfold NoUnknownInPriorityGroups in *.
    rewrite Hno_unk_pgroups in Hnodup_transs.
    generalize (nodup_concat_gen spn.(priority_groups) Hnodup_transs pgroup Hin_pgroups)
      as Hnodup_pgroup; intro.              
    (* Applies spn_fire_aux_not_firable_not_fired. *)
    generalize (spn_fire_aux_not_firable_not_fired
                  spn state (marking state)
                  [] pgroup pgroup fired Hwell_def_spn
                  Hwell_def_state Hin_pgroups Hnodup_pgroup Hincl_pgroup Hfun) as Hspec; intro.
    assert (Hnot_in : ~In t []) by (apply in_nil).
    apply (Hspec t Hin_pgroup Hnot_in Hnot_firable). 
  Qed.

  (** spn_map_fire_aux spn state fired pgroups = Some final_fired ⇒ 
      ∀ t ∉ fired ∧ t ∉ (concat pgroups) ⇒ t ∉ final_fired *)
  
  Theorem spn_map_fire_aux_not_in_not_fired :
    forall (spn : Spn)
           (state : SpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      spn_map_fire_aux spn state fired pgroups = Some final_fired ->
      forall t : Trans, ~In t fired -> ~In t (concat pgroups) -> ~In t final_fired.
  Proof.
    intros spn state fired pgroups;
      functional induction (spn_map_fire_aux spn state fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hfun t Hnot_in_fired Hnot_in_concat.
    (* Base case, pgroups = [] *)
    - injection Hfun; intro Heq; rewrite Heq in *; assumption.
    (* General case *)
    - unfold spn_fire in e0.
      (* Builds (~In t []) to apply spn_fire_aux_not_in_not_fired. *)
      assert (Hnot_in_nil : ~In t []) by apply in_nil.
      (* Builds (~In t pgroup) to apply spn_fire_aux_not_in_not_fired. *)
      simpl in Hnot_in_concat.
      generalize (not_app_in t pgroup (concat pgroups_tail) Hnot_in_concat)
        as Hnot_in_wedge; intro.
      elim Hnot_in_wedge; intros Hnot_in_pg Hnot_in_concat'.
      (* Applies spn_fire_aux_not_in_not_fired *)
      generalize (spn_fire_aux_not_in_not_fired
                    spn state (marking state) [] pgroup fired_trs t
                    Hnot_in_nil Hnot_in_pg e0) as Hnot_in_ff; intro.
      (* Builds ~In t (fired_transitions ++ fired_trs) to apply IHo. *)
      generalize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_ff))
        as Hnot_in_all_ff; intro.
      (* Applies induction hypothesis. *)
      apply (IHo final_fired Hfun t Hnot_in_all_ff Hnot_in_concat').
    (* Case spn_fire returns None. *)
    - inversion Hfun.
  Qed.

  (** spn_map_fire_aux spn state fired pgroups = Some final_fired ⇒ 
      ∀ t ∈ fired ⇒ t ∈ final_fired *)
  
  Theorem spn_map_fire_aux_in_fired :
    forall (spn : Spn)
           (state : SpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      spn_map_fire_aux spn state fired pgroups = Some final_fired ->
      forall t : Trans, In t fired -> In t final_fired.
  Proof.
    intros spn state fired pgroups;
      functional induction (spn_map_fire_aux spn state fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hfun t Hin_t_fired.
    (* BASE CASE *)
    - injection Hfun; intro Heq; rewrite Heq in *; assumption.
    (* GENERAL CASE *)
    - apply or_introl with (B := In t fired_trs) in Hin_t_fired.
      apply in_or_app in Hin_t_fired.
      apply (IHo final_fired Hfun t Hin_t_fired).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.
  
  (** spn_map_fire_aux spn s fired pgroups = Some final_fired ⇒ 
      ∀ pgroup ∈ pgroups, ∀ t ∈ pgroup, 
      t ∉ fired ⇒ t ∉ firable(s) ⇒ t ∉ final_fired 
      
      N.B. firable(s) ≡ firable(s'), because s.(marking) = s'.(marking). *)
  
  Theorem spn_map_fire_aux_not_firable_not_fired :
    forall (spn : Spn)
           (state : SpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn state ->
      NoDup (concat pgroups) ->
      incl pgroups spn.(priority_groups) ->
      spn_map_fire_aux spn state fired pgroups = Some final_fired ->
      (forall (pgroup : list Trans) (t : Trans),
          In pgroup pgroups ->
          In t pgroup ->
          ~In t fired ->
          ~SpnIsFirable spn state t ->
          ~In t final_fired).
  Proof.
    intros spn state fired pgroups;
      functional induction (spn_map_fire_aux spn state fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hwell_def_spn Hwell_def_state Hnodup_concat Hincl_pgs Hfun pgroup' t
             Hin_pgs Hin_pg Hnot_in_fired Hnot_firable.
    (* BASE CASE, pgroups = []. *)
    - inversion Hin_pgs.
    (* GENERAL CASE *)
    - apply in_inv in Hin_pgs; elim Hin_pgs.
      (* CASE pgroup = pgroup' *)
      + intro Heq_pg.
        (* Builds ~In t (concat pgroups_tail) to apply 
           spn_map_fire_aux_not_in_not_fired *)
        rewrite concat_cons in Hnodup_concat.
        rewrite Heq_pg in Hnodup_concat.
        generalize (nodup_app_not_in
                      pgroup' (concat pgroups_tail) Hnodup_concat
                      t Hin_pg) as Hnot_in_concat; intro.
        (* Builds In pgroup spn.(priority_groups) to apply 
           spn_fire_not_firable_not_fired *)
        assert (Hin_pgs' : In pgroup (pgroup :: pgroups_tail)) by apply in_eq.
        generalize (Hincl_pgs pgroup Hin_pgs') as Hin_spn_pgs; intro.
        (* Builds (~In t fired_trs) by applying spn_fire_not_firable_not_fired. *)
        rewrite <- Heq_pg in Hin_pg.
        generalize (spn_fire_not_firable_not_fired
                      spn state pgroup fired_trs Hwell_def_spn Hwell_def_state
                      Hin_spn_pgs e0 t Hin_pg Hnot_firable) as Hnot_in_fired'; intro.
        (* Builds (~In t (fired_transitions ++ fired_trs)) *)
        generalize (not_in_app t fired_transitions fired_trs
                               (conj Hnot_in_fired Hnot_in_fired')) as Hnot_in_fired_app; intro.
        (* Applies spn_map_fire_aux_not_in_not_fired *)
        apply (spn_map_fire_aux_not_in_not_fired
                 spn state (fired_transitions ++ fired_trs) pgroups_tail final_fired Hfun
                 t Hnot_in_fired_app Hnot_in_concat).
      (* CASE In pgroup' pgroups_tail, then apply IHo. *)
      + intro Hin_pgs_tail.
        (* Builds NoDup (concat pgroups_tail). *)
        rewrite concat_cons in Hnodup_concat.
        generalize (nodup_app pgroup (concat pgroups_tail) Hnodup_concat)
          as Hnodup_concat_wedge; intro.
        elim Hnodup_concat_wedge; intros Hnodup_pg Hnodup_concat_tail.
        (* Builds (incl pgroups_tail (priority_groups spn)). *)
        generalize (incl_cons_inv
                      pgroup pgroups_tail
                      spn.(priority_groups) Hincl_pgs) as Hincl_pgs'; intro.
        (* Builds ~In t (fired_transitions ++ fired_trs). 

           First, we need (~In t pgroup) to apply spn_fire_aux_not_in_not_fired. *)
        specialize (NoDup_app_comm pgroup (concat pgroups_tail) Hnodup_concat)
          as Hnodup_concat_inv.
        specialize (nodup_app_not_in (concat pgroups_tail) pgroup Hnodup_concat_inv)
          as Hfall_not_in_pg.
        specialize (in_concat t pgroup' pgroups_tail Hin_pg Hin_pgs_tail) as Hin_concat.
        specialize (Hfall_not_in_pg t Hin_concat) as Hnot_in_pg.
        (* Second, we need to build (~In t fired_trs) by 
           applying spn_fire_aux_not_in_not_fired. *)
        unfold spn_fire in e0.
        assert (Hnot_in_nil : ~In t []) by apply in_nil.
        specialize (spn_fire_aux_not_in_not_fired
                      spn state (marking state) [] pgroup fired_trs t
                      Hnot_in_nil Hnot_in_pg e0) as Hnot_in_fired'.
        (* Finally, builds (~In t (fired_transitions ++ fired_trs)) *)
        specialize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_fired'))
          as Hnot_in_fired_app.
        (* Applies IHo. *)
        apply (IHo final_fired Hwell_def_spn Hwell_def_state
                   Hnodup_concat_tail Hincl_pgs' Hfun pgroup' t Hin_pgs_tail
                   Hin_pg  Hnot_in_fired_app Hnot_firable).
    (* CASE spn_fire returns None. *)
    - inversion Hfun.
  Qed.

  (** spn_map_fire spn s = Some s' ⇒  
      ∀ pgroup ∈ spn.(priority_groups), t ∈ pgroup,
      t ∉ firable(s') ⇒ t ∉ s'.(fired) *)

  Theorem spn_map_fire_not_firable_not_fired :
    forall (spn : Spn) (s s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      spn_map_fire spn s = Some s' ->
      forall (pgroup : list Trans) (t : Trans),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        ~SpnIsFirable spn s' t ->
        ~In t s'.(fired).
  Proof.
    intros spn s s' Hwell_def_spn Hwell_def_s Hfun.
    (* Builds IsWellDefined spn s', needed to apply spn_map_fire_aux_not_firable_not_fired *)
    specialize (spn_map_fire_well_defined_state spn s s' Hwell_def_spn Hwell_def_s Hfun)
      as Hwell_def_s'.
    functional induction (spn_map_fire spn s) using spn_map_fire_ind;
      intros pgroup' t Hin_spn_pgs Hin_pg Hnot_firable.
    (* GENERAL CASE: the strategy is to apply spn_map_fire_aux_not_firable_not_fired. 
                     First, we need to build a few hypotheses. *)
    - explode_well_defined_spn.
      (* Builds NoDup (concat spn.(priority_groups)). *)
      unfold NoIntersectInPriorityGroups in Hno_inter.
      (* Builds (incl spn.(pgs) spn.(pgs)) *)
      assert (Hincl_spn_pgs : incl spn.(priority_groups) spn.(priority_groups))
        by apply incl_refl.
      (* Builds ~In t [] *)
      assert (Hnot_in_nil : ~In t []) by apply in_nil.
      (* Builds (~SpnIsFirable spn s t) *)
      assert (Heq_marking : s.(marking) = s'.(marking))
        by (injection Hfun; intro Heq; rewrite <- Heq; reflexivity). 
      specialize (state_same_marking_firable_iff
                    spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s' Heq_marking t)
        as Hnot_firable_iff.
      rewrite <- Hnot_firable_iff in Hnot_firable.
      (* Rewrites the goal. *)
      injection Hfun; intro Heq_s'; rewrite <- Heq_s'; simpl.
      (* Applies spn_map_fire_aux_not_firable_not_fired. *)
      apply (spn_map_fire_aux_not_firable_not_fired
               spn s [] (priority_groups spn) fired Hwell_def_spn Hwell_def_s
               Hno_inter Hincl_spn_pgs e pgroup' t Hin_spn_pgs Hin_pg Hnot_in_nil Hnot_firable).
    (* ERROR CASE, spn_map_fire_aux returns None. *)
    - inversion Hfun.
  Qed.
  
End SpnNotFirableNotFired.

(** *** Second part of correctness proof *)

(** The goal in this part is to prove: 

    spn_map_fire = Some s' ⇒ 
    ∀ t ∈ firable(s'), t ∈ sens(M - ∑ pre(t'), ∀ t'∈ Pr(t)) ⇒ t ∈ Fired' *)

Section SpnSensitizedByResidual.

  (** pre_sum spn p l + pre_sum spn p [t] = pres_um spn p (l ++ [t]) 

      Needed to prove GENERAL CASE in spn_fire_aux_sens_by_residual. *)
  
  Lemma pre_sum_app_add :
    forall (spn : Spn) (p : Place) (l : list Trans) (t : Trans),
      pre_sum spn p l + pre_sum spn p [t] = pre_sum spn p (l ++ [t]).
  Proof.
    intros spn p l; functional induction (pre_sum spn p l) using pre_sum_ind; intro t'.
    - simpl; reflexivity.
    - simpl.
      rewrite <- (IHn t').
      simpl.
      rewrite plus_assoc_reverse.
      reflexivity.
  Qed.

  (** If occ ∈ l, then repl ∈ l' *)

  Lemma replace_occ_if_in {A : Type} :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (occ : A)
           (repl : A)
           (l : list A)
           (l' : list A),
      replace_occ eq_dec occ repl l = l' ->
      In occ l ->
      In repl l'.
  Proof.
    intros eq_dec occ repl l;
      functional induction (replace_occ eq_dec occ repl l) using replace_occ_ind;
      intros l' Hfun Hin_l.
    (* BASE CASE *)
    - inversion Hin_l.
    (* CASE occ = hd l *)
    - rewrite <- Hfun; apply in_eq.
    (* CASE occ <> hd l *)
    - inversion Hin_l.
      + contradiction.
      + induction l'.
        -- inversion Hfun.
        -- injection Hfun as Heq_xa Heq_fun.
           apply in_cons.
           apply (IHl0 l' Heq_fun H).
  Qed.

  Lemma replace_occ_if_not_in {A : Type} :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (occ : A)
           (repl : A)
           (l : list A)
           (l' : list A),
      replace_occ eq_dec occ repl l = l' ->
      In repl l' ->
      ~In repl l ->
      In occ l.
  Proof.
    intros eq_dec occ repl l;
      functional induction (replace_occ eq_dec occ repl l) using replace_occ_ind;
      intros l' Hfun Hin_l' Hnot_in_l.
    (* BASE CASE *)
    - rewrite <- Hfun in Hin_l'; inversion  Hin_l'.
    (* CASE occ = hd l *)
    - apply in_eq.
    (* CASE occ <> hd l *)
    - induction l'.
      + inversion Hin_l'.
      + inversion Hin_l' as [Heq_repla | Hin_repl_l'].
        -- injection Hfun as Heq_xa Heq_fun.
           apply not_in_cons in Hnot_in_l; apply proj1 in Hnot_in_l.
           rewrite Heq_xa in Hnot_in_l; symmetry in Heq_repla; contradiction.
        -- injection Hfun as Heq_xa Heq_fun.
           apply not_in_cons in Hnot_in_l; apply proj2 in Hnot_in_l.
           apply in_cons.
           apply (IHl0 l' Heq_fun Hin_repl_l' Hnot_in_l).
  Qed.

  (* Lemma : Proves that replace_occ preserves structure
   *         of a marking m passed as argument when 
   *         (fst occ) = (fst repl).
   *)
  Lemma replace_occ_same_struct :
    forall (m : list (Place * nat))
           (p : Place)
           (n n' : nat),
      MarkingHaveSameStruct (replace_occ prodnat_eq_dec (p, n) (p, n') m) m.
  Proof.
    do 4 intro.
    unfold MarkingHaveSameStruct.
    functional induction (replace_occ prodnat_eq_dec (p, n) (p, n') m)
               using replace_occ_ind;
      intros.
    (* Base case. *)
    - auto.
    (* Case (p,n) is hd of list. *)
    - intros.
      rewrite fst_split_cons_app.
      symmetry.
      rewrite fst_split_cons_app.
      rewrite IHl.
      simpl.
      auto.
    (* Case (p, n) not hd of list. *)
    - rewrite fst_split_cons_app.
      symmetry.
      rewrite fst_split_cons_app.
      rewrite IHl.
      auto.
  Qed.

  Lemma replace_occ_in_if_diff {A : Type} :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (occ : A)
           (repl : A)
           (l : list A)
           (l' : list A),
      replace_occ eq_dec occ repl l = l' ->
      forall a : A, a <> occ -> a <> repl -> In a l <-> In a l'.
  Proof.
    intros eq_dec occ repl l;
      functional induction (replace_occ eq_dec occ repl l)
                 using replace_occ_ind;
      intros l' Hfun a Hdiff_occ Hdiff_repl.
    (* BASE CASE *)
    - rewrite <- Hfun; reflexivity.
    (* CASE occ = hd l *)
    - split.
      + intro Hin_a_l.
        inversion Hin_a_l as [Heq_aocc | Hin_a_tl].
        -- symmetry in Heq_aocc; contradiction.
        -- induction l'.
           ++ inversion Hfun.
           ++ injection Hfun as Heq_repla Heq_fun.
              apply in_cons.
              specialize (IHl0 l' Heq_fun a Hdiff_occ) as Hequiv.
              rewrite <- Hequiv; assumption.
      + intro Hin_a_l'; induction l'.
        -- inversion Hfun.
        -- injection Hfun as Heq_repla Heq_fun.
           apply in_cons.
           inversion Hin_a_l' as [Heq_aa0 | Hin_a_l''].
           ++ rewrite Heq_aa0 in Heq_repla; symmetry in Heq_repla; contradiction. 
           ++ specialize (IHl0 l' Heq_fun a Hdiff_occ Hdiff_repl) as Hequiv;
                rewrite Hequiv; assumption.
    (* CASE occ <> hd l *)
    - induction l'.
      + inversion Hfun.
      + injection Hfun as Heq_xa0 Heq_fun.
        specialize (IHl0 l' Heq_fun a Hdiff_occ Hdiff_repl) as Hequiv.
        split.
        -- intro Hin_a_l.
           inversion Hin_a_l as [Heq_ax | Hin_a_tl].
           ++ rewrite <- Heq_ax; rewrite Heq_xa0; apply in_eq.
           ++ apply in_cons; rewrite <- Hequiv; assumption.
        -- intro Hin_a_l'.
           inversion Hin_a_l' as [Heq_aa0 | Hin_a_tll'].
           ++ rewrite Heq_xa0; rewrite Heq_aa0; apply in_eq.
           ++ apply in_cons; rewrite Hequiv; assumption.
  Qed.
  
  (** Correctness proof for [modify_m]. 
      
      Needed in update_residual_marking_aux_correct. *)
  
  Lemma modify_m_correct :
    forall (marking : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat)
           (final_marking : list (Place * nat)),
      NoDup (fst (split marking)) ->
      modify_m marking p op nboftokens = Some final_marking ->
      forall n : nat, In (p, n) marking -> In (p, op n nboftokens) final_marking.
  Proof.
    intros marking p op nboftokens;
      functional induction (modify_m marking p op nboftokens) using modify_m_ind;
      intros final_marking Hnodup Hfun n' Hin_n'_m.
    (* GENERAL CASE *)
    - injection Hfun as Hfun.
      apply get_m_correct in e.
      specialize (replace_occ_if_in
                    prodnat_eq_dec (p, n) (p, op n nboftokens) marking
                    final_marking Hfun e) as Hin_final.
      assert (Heq_p : fst (p, n) = fst (p, n')) by (simpl; reflexivity).
      specialize (nodup_same_pair marking Hnodup (p, n) (p, n') e Hin_n'_m Heq_p) as Heq_pp.
      injection Heq_pp as Heq_nn'.
      rewrite <- Heq_nn'; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma modify_m_in_if_diff :
    forall (marking : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat)
           (final_marking : list (Place * nat)),
      modify_m marking p op nboftokens = Some final_marking ->
      forall (p' : Place) (n : nat), p <> p' -> In (p', n) marking <-> In (p', n) final_marking.
  Proof.
    intros marking p op nboftokens;
      functional induction (modify_m marking p op nboftokens) using modify_m_ind;
      intros final_marking Hfun p'' n' Hdiff_pp.
    (* GENERAL CASE *)
    - injection Hfun as Hfun.
      apply not_eq_sym in Hdiff_pp.
      specialize (fst_diff_pair_diff p'' p Hdiff_pp n' n) as Hdiff_nn0.
      specialize (fst_diff_pair_diff p'' p Hdiff_pp n' (op n nboftokens)) as Hdiff_nnb.
      specialize (replace_occ_in_if_diff
                    prodnat_eq_dec (p, n) (p, op n nboftokens) marking final_marking
                    Hfun (p'', n') Hdiff_nn0 Hdiff_nnb) as Hequiv.
      assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Proves that modify_m preserves the structure of the marking m
      passed as argument. *)
  
  Lemma modify_m_same_struct :
    forall (m m' : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat),
      modify_m m p op nboftokens = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    do 5 intro.
    functional induction (modify_m m p op nboftokens)
               using modify_m_ind;
      intros.
    - injection H; intros.
      rewrite <- H0.
      unfold MarkingHaveSameStruct; symmetry.
      apply replace_occ_same_struct.
    - inversion H.
  Qed.

  (** Proves that update_residual_marking_aux preserves marking structure. *)
  Lemma update_residual_marking_aux_same_struct :
    forall (spn : Spn)
           (residual_marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (final_marking : list (Place * nat)),
      update_residual_marking_aux spn residual_marking t pre_places = Some final_marking ->
      MarkingHaveSameStruct residual_marking final_marking.
    intros spn residual_marking t pre_places;
      functional induction (update_residual_marking_aux spn residual_marking t pre_places)
                 using update_residual_marking_aux_ind;
      intros final_marking Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply modify_m_same_struct in e0.
      apply IHo in Hfun.
      unfold MarkingHaveSameStruct in e0;
        unfold MarkingHaveSameStruct in Hfun;
        rewrite <- e0 in Hfun; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Needed to prove update_marking_aux_correct. *)
  
  Lemma update_residual_marking_aux_not_in_pre_places :
    forall (spn : Spn)
           (residual_marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (final_marking : list (Place * nat)),
      update_residual_marking_aux spn residual_marking t pre_places = Some final_marking ->
      forall (p : Place),
        ~In p pre_places ->
        forall (n : nat), In (p, n) residual_marking <-> In (p, n) final_marking.
  Proof.
    intros spn residual_marking t pre_places;
      functional induction (update_residual_marking_aux spn residual_marking t pre_places)
                 using update_residual_marking_aux_ind;
      intros final_marking Hfun p' Hnot_in_pre n.
    (* BASE CASE *)
    - injection Hfun as Hfun.
      rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply not_in_cons in Hnot_in_pre.
      elim Hnot_in_pre; intros Hdiff_pp' Hnot_in_tl.
      apply not_eq_sym in Hdiff_pp'.
      specialize (modify_m_in_if_diff
                    residual_marking p Nat.sub (pre spn t p) residual_marking'
                    e0 p' n Hdiff_pp') as Hequiv.
      rewrite Hequiv.
      apply (IHo final_marking Hfun p' Hnot_in_tl n).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.
  
  (** Correctness proof for [update_residual_marking_aux].
      Express the structure of the returned [residual_marking'] regarding the structure
      of [residual_marking]. 

      Needed to prove update_residual_marking_correct. *)
  
  Lemma update_residual_marking_aux_correct :
    forall (spn : Spn)
           (residual_marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (neigh_of_t : Neighbours)
           (final_marking : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split residual_marking)) ->
      In (t , neigh_of_t) (lneighbours spn) ->
      NoDup pre_places ->
      incl pre_places (pre_pl neigh_of_t) ->
      update_residual_marking_aux spn residual_marking t pre_places = Some final_marking ->
      forall (p : Place) (n : nat),
        In p pre_places ->
        In (p, n) residual_marking ->
        In (p, n - (pre spn t p)) final_marking.
  Proof.
    intros spn residual_marking t pre_places;
      functional induction (update_residual_marking_aux spn residual_marking t pre_places)
                 using update_residual_marking_aux_ind;
      intros neigh_of_t final_marking Hwell_def_spn Hnodup_m
             Hin_lneigh Hnodup_pre_pl Hincl_pre_pl Hfun p' n Hin_pre_pl Hin_resid.
    (* BASE CASE, pre_places = []. *)
    - inversion Hin_pre_pl.
    (* GENERAL CASE *)
    - inversion Hin_pre_pl as [Heq_pp' | Hin_p'_tail].
      (* First subcase, p = p'. *)
      + rewrite <- Heq_pp' in Hin_pre_pl.
        rewrite <- Heq_pp' in Hin_resid.
        specialize (modify_m_correct
                      residual_marking p Nat.sub (pre spn t p) residual_marking'
                      Hnodup_m e0 n Hin_resid) as Hin_resid'.
        apply NoDup_cons_iff in Hnodup_pre_pl.
        elim Hnodup_pre_pl; intros Hnot_in_tl Hnodup_tl.
        rewrite Heq_pp' in Hnot_in_tl.
        specialize (update_residual_marking_aux_not_in_pre_places
                      spn residual_marking' t tail final_marking
                      Hfun p' Hnot_in_tl (n - pre spn t p)) as Hin_equiv'.
        rewrite Heq_pp' in Hin_resid'.
        rewrite Heq_pp' in Hin_equiv'.
        rewrite Hin_equiv' in Hin_resid'; assumption.
      (* Second subcase, In p' tail, then apply induction hypothesis. *)
      (* But we need to show NoDup (fst (split residual')) first. *)
      + specialize (modify_m_same_struct
                      residual_marking residual_marking' p Nat.sub  (pre spn t p) e0)
          as Hsame_struct.
        unfold MarkingHaveSameStruct in Hsame_struct.
        rewrite Hsame_struct in Hnodup_m.
        (* Builds the other hypotheses, needed to specialize IHo. *)
        apply NoDup_cons_iff in Hnodup_pre_pl;
          elim Hnodup_pre_pl;
          intros Hnot_in_tl Hnodup_tl.
        apply incl_cons_inv in Hincl_pre_pl.        
        (* Then specializes the induction hypothesis. *)
        specialize (IHo neigh_of_t final_marking Hwell_def_spn Hnodup_m
                        Hin_lneigh Hnodup_tl Hincl_pre_pl Hfun
                        p' n Hin_p'_tail) as Himpl.
        specialize (not_in_in_diff p p' tail (conj Hnot_in_tl Hin_p'_tail))
          as Hdiff_pp.
        specialize (modify_m_in_if_diff
                      residual_marking p Nat.sub (pre spn t p)
                      residual_marking' e0 p' n Hdiff_pp) as Hequiv'.
        rewrite <- Hequiv' in Himpl.
        apply (Himpl Hin_resid).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Correctness proof for [update_residual_marking]. 

      Needed to prove GENERAL CASE in spn_fire_aux_sens_by_residual. *)
  Lemma update_residual_marking_correct :
    forall (spn : Spn)
           (residual_marking : list (Place * nat))
           (t : Trans)
           (neigh_of_t : Neighbours)
           (final_marking : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split residual_marking)) ->
      In (t , neigh_of_t) (lneighbours spn) ->
      update_residual_marking spn residual_marking neigh_of_t t = Some final_marking ->
      forall (p : Place) (n : nat),
        In (p, n) residual_marking -> In (p, n - (pre spn t p)) final_marking.
  Proof.
    intros spn residual_marking t neigh_of_t final_marking
           Hwell_def_spn Hnodup_resm Hin_lneigh Hfun p n Hin_resm.
    unfold update_residual_marking in Hfun.
    (* Two cases, either p ∈ (pre_pl neigh_of_t), or
       p ∉ (pre_pl neigh_of_t). *)
    assert (Hvee_in_pre_pl := classic (In p (pre_pl neigh_of_t))).
    inversion Hvee_in_pre_pl as [Hin_p_pre | Hnotin_p_pre]; clear Hvee_in_pre_pl.
    (* First case, p ∈ pre_pl, then applies update_residual_marking_aux_correct. *)
    - explode_well_defined_spn.
      (* Builds NoDup pre_pl. *)
      assert (Hin_flat : In p (flatten_neighbours neigh_of_t))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).      
      unfold NoDupInNeighbours in Hnodup_neigh.
      specialize (Hnodup_neigh t neigh_of_t Hin_lneigh) as Hnodup_flat.
      unfold flatten_neighbours in Hnodup_flat;
        apply nodup_app in Hnodup_flat; apply proj1 in Hnodup_flat.
      (* Then, applies update_residual_marking_aux_correct. *)
      apply (update_residual_marking_aux_correct
               spn residual_marking t (pre_pl neigh_of_t) neigh_of_t final_marking
               Hwell_def_spn Hnodup_resm Hin_lneigh Hnodup_flat
               (incl_refl (pre_pl neigh_of_t)) Hfun p n Hin_p_pre Hin_resm).
    (* Second case, p ∉ pre_pl, then applies 
       update_residual_marking_aux_not_in_pre_places. *)
    - explode_well_defined_spn.
      unfold AreWellDefinedPreEdges in Hwell_def_pre.
      specialize (Hwell_def_pre t neigh_of_t p Hin_lneigh) as Hw_pre_edges.
      apply proj2 in Hw_pre_edges; specialize (Hw_pre_edges Hnotin_p_pre).
      rewrite Hw_pre_edges; rewrite Nat.sub_0_r.
      specialize (update_residual_marking_aux_not_in_pre_places
                    spn residual_marking t (pre_pl neigh_of_t) final_marking
                    Hfun p Hnotin_p_pre n) as Hequiv.
      rewrite <- Hequiv; assumption.
  Qed.
  
  (** If :
      - spn_fire_aux spn s residual fired pg = Some final_fired
      - There are no duplicate in [(fired ++ pg)]
      - [t] ∈ [final_fired]
      Then : [t] ∈ [fired] ∨ [pg]. 
      
      Needed to prove CASE is_sensitized = Some false in 
      spn_fire_aux_sens_by_residual. *)
  
  Theorem spn_fire_aux_final_fired_vee :
    forall (spn : Spn)
           (s : SpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg : list Trans)
           (final_fired : list Trans)
           (t : Trans),
      NoDup (fired ++ pg) ->
      In t final_fired ->
      spn_fire_aux spn s residual_marking fired pg = Some final_fired ->
      In t fired \/ In t pg.
  Proof.
    intros spn s residual_marking fired pg;
      functional induction (spn_fire_aux spn s residual_marking fired pg)
                 using spn_fire_aux_ind;
      intros final_fired t' Hnodup_app Hin_t_ff Hfun.
    (* BASE CASE, pg = []. *)
    - injection Hfun as Heq_fired; left; rewrite Heq_fired; assumption.
    (* GENERAL CASE *)
    - rewrite <- app_assoc in IHo.
      specialize (IHo final_fired t' Hnodup_app Hin_t_ff Hfun) as H_ff_vee'.
      elim H_ff_vee'.
      + intro Hin_t_fired_app.
        apply in_app_or in Hin_t_fired_app.
        elim Hin_t_fired_app.
        -- auto.
        -- intro Hin_tt; simpl in Hin_tt.
           elim Hin_tt; [ intro Heq_tt; rewrite <- Heq_tt; right; apply in_eq |
                          intro Hfalse; inversion Hfalse].
      + intro Hin_t_tail; apply in_cons with (a := t) in Hin_t_tail; right; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
    (* CASE is_sensitized = Some false *)
    - apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.
      specialize (IHo final_fired t' Hnodup_app Hin_t_ff Hfun) as Hin_vee.
      elim Hin_vee.
      + intro Hin_t_fired; left; assumption.
      + intro Hin_t_tail; right; apply in_cons with (a := t) in Hin_t_tail; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
    (* CASE spn_is_firable = Some false *)
    - apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.
      specialize (IHo final_fired t' Hnodup_app Hin_t_ff Hfun) as Hin_vee.
      elim Hin_vee.
      + intro Hin_t_fired; left; assumption.
      + intro Hin_t_tail; right; apply in_cons with (a := t) in Hin_t_tail; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma spn_fire_aux_sens_by_residual :
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
      (* Function ⇒ Specification *)
      spn_fire_aux spn s residual_marking fired pg = Some final_fired ->
      forall (t : Trans)
             (res_marking : list (Place * nat)),
        (* Hypotheses on t. *)
        In t pg ->
        SpnIsFirable spn s t ->
        IsSensitized spn res_marking t ->
        (* Hypotheses on fired *)
        (forall t'' : Trans, In t'' fired -> HasHigherPriority spn t'' t pgroup /\
                                             In t'' final_fired) ->
        (* Hypotheses on res_marking. *)
        MarkingHaveSameStruct spn.(initial_marking) res_marking ->
        (forall (pr : list Trans),
            NoDup pr ->
            (forall t' : Trans,
                HasHigherPriority spn t' t pgroup /\ In t' final_fired <->
                In t' pr) ->
            (forall (p : Place) (n : nat),
                In (p, n) (marking s) -> In (p, n - (pre_sum spn p pr)) res_marking)) ->
        In t final_fired.
  Proof.
    intros spn s residual_marking fired pg;
      functional induction (spn_fire_aux spn s residual_marking fired pg)
                 using spn_fire_aux_ind;
      intros pgroup final_fired Hwell_def_spn Hwell_def_s
             Hin_spn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct Hfun
             t' res_marking Hin_t_pg Hfirable_t Hsens_t Hhigh_in_fired Hsame_struct' Hres_m.
    (* BASE CASE, pg = []. *)
    - inversion Hin_t_pg.
    (* GENERAL CASE, with two subcases. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].
      (* First subcase, t = t' then t' ∈ (fired ++ [t]) ⇒ t' ∈ final_fired. *)
      + assert (Hin_t_fired : In t (fired ++ [t])) by (apply in_or_app; right; apply in_eq).
        rewrite <- Heq_tt'.
        apply (spn_fire_aux_in_fired spn s residual_marking' (fired ++ [t]) tail final_fired t
                                     Hin_t_fired Hfun).
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
        assert(Hhigh_in_fired' :
                 forall t'' : Trans, In t'' (fired ++ [t]) ->
                                     HasHigherPriority spn t'' t' pgroup /\ In t'' final_fired).
        {
          intros t'' Hin_fired_app;
            apply in_app_or in Hin_fired_app;
            inversion Hin_fired_app as [Hin_fired | Heq_tst]; clear Hin_fired_app.
          - apply (Hhigh_in_fired t'' Hin_fired).
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
                   Hnodup_pg Hresid'_m Hsame_struct Hfun t' res_marking Hin_t'_tail
                   Hfirable_t Hsens_t Hhigh_in_fired' Hsame_struct' Hres_m).
    (* ERROR CASE, update_residual_marking = None. *)
    - inversion Hfun.
    (* CASE, is_sensitized = Some false. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].
      (* First subcase, t = t'. *)
      (* What we want to show is a contradiction between is_sensitized = Some false 
         and IsSensitized spn t' res_marking. *)
      (* Then, we need to show that we have IsSensitized spn t' residual_marking.
         We can deduce it from Hsens_t. *)
      (* Hpr_is_fired is needed to specialize Hres_m. *)
      + assert (Hpr_is_fired :
                  forall t'' : Trans, 
                    HasHigherPriority spn t'' t' pgroup /\ In t'' final_fired -> In t'' fired). 
        {
          intros t'' Hw; elim Hw; intros Hhas_high Hin_ts_ff; clear Hw.
          specialize (NoDup_remove fired tail t Hnodup_pg) as Hnodup_app;
            apply proj1 in Hnodup_app.
          specialize (spn_fire_aux_final_fired_vee
                        spn s residual_marking fired tail final_fired t''
                        Hnodup_app Hin_ts_ff Hfun) as Hin_ts_vee.
          elim Hin_ts_vee.
          - auto.
          (* If t'' ∈ tail, then ~IsPredInNoDupList t'' t' (t' :: tail) ⇒ 
             ~IsPredInNoDupList t'' t' pgroup, then contradiction. *)
          - intro Hin_ts_tail.
            unfold HasHigherPriority in Hhas_high.
            (* Builds ~IsPredInNoDuplist t'' t' (t' :: tail) *)
            assert (Hnot_is_pred : ~IsPredInNoDupList t'' t' (t' :: tail)) by
                apply not_is_pred_in_list_if_hd.
            rewrite Heq_tt' in Hdec_list.
            specialize (not_is_pred_in_dec_list Hdec_list Hin_ts_tail) as Hnot_is_pred_in_pg.
            decompose [and] Hhas_high; contradiction.
        }
        (* Now we have Hpr_is_fired, we can specialize Hres_m. *)
        assert (Hpr_iff :
                  forall t'' : Trans,
                    HasHigherPriority spn t'' t' pgroup /\ In t'' final_fired <-> In t'' fired)
          by (intros t'0; split; [apply (Hpr_is_fired t'0) | apply (Hhigh_in_fired t'0)]).
        specialize (nodup_app fired (t :: tail) Hnodup_pg) as Hnodup_fired.
        apply proj1 in Hnodup_fired.
        specialize (Hres_m fired Hnodup_fired Hpr_iff).
        (* Now we can show the equivalence between residual_marking and res_marking. *)
        assert (Hequiv_m : forall (p : Place) (n : nat), In (p, n) res_marking <->
                                                         In (p, n) residual_marking).
        {
          intros p n.
          split.
          - intro Hin_res_m.
            (* Builds (fs (marking s)) = (fs res_marking) *)            
            explode_well_defined_spn_state Hwell_def_s.
            unfold MarkingHaveSameStruct in *.
            assert (Hsame_resm_sm : fst (split res_marking) = fst (split (marking s)))
              by (rewrite <- Hsame_marking_state_spn; rewrite <- Hsame_struct'; reflexivity).
            (* Builds In (p, x) (marking s) from In (p, n) res_marking. *)
            specialize (in_fst_split p n res_marking Hin_res_m) as Hin_fs_resm.
            rewrite Hsame_resm_sm in Hin_fs_resm.
            specialize (in_fst_split_in_pair p (marking s) Hin_fs_resm) as Hex_ms.
            elim Hex_ms; intros x Hin_x_ms.
            (* Applies Hresid_m and Hres_m. *)
            specialize (Hresid_m p x Hin_x_ms) as Hin_resid_m'.
            specialize (Hres_m p x Hin_x_ms) as Hin_res_m'.
            (* Builds NoDup (fs res_marking) to apply nodup_same_pair. *)
            explode_well_defined_spn.
            unfold NoUnmarkedPlace in Hunm_place; unfold NoDupPlaces in Hnodup_places.
            rewrite Hunm_place in Hnodup_places;
              rewrite Hsame_marking_state_spn in Hnodup_places;
              rewrite <- Hsame_resm_sm in Hnodup_places.
            (* Builds fs (p, n) = fs (p, x - pre_sum spn p fired) *)
            assert (Heq_fs : fst (p, n) = fst (p, x - pre_sum spn p fired))
              by (simpl; reflexivity).                    
            (* Applies nodup_same_pair to get n = x - pre_sum spn p fired. *)
            specialize (nodup_same_pair
                          res_marking Hnodup_places (p, n) (p, x - pre_sum spn p fired)
                          Hin_res_m Hin_res_m' Heq_fs) as Heq_nx.
            injection Heq_nx as Heq_nx.
            rewrite Heq_nx.
            assumption.
          - intro Hin_resid_m.
            (* Builds (fs (marking s)) = (fs res_marking) *)
            explode_well_defined_spn_state Hwell_def_s.
            unfold MarkingHaveSameStruct in *.
            assert (Hsame_residm_sm : fst (split residual_marking) = fst (split (marking s)))
              by (rewrite <- Hsame_marking_state_spn; rewrite <- Hsame_struct; reflexivity).
            (* Builds In (p, x) (marking s) from In (p, n) residual_marking. *)
            specialize (in_fst_split p n residual_marking Hin_resid_m) as Hin_fs_residm.
            rewrite Hsame_residm_sm in Hin_fs_residm.
            specialize (in_fst_split_in_pair p (marking s) Hin_fs_residm) as Hex_ms.
            elim Hex_ms; intros x Hin_x_ms.
            (* Applies Hresid_m and Hres_m. *)
            specialize (Hresid_m p x Hin_x_ms) as Hin_resid_m'.
            specialize (Hres_m p x Hin_x_ms) as Hin_res_m'.
            (* Builds NoDup (fs residual_marking) to apply nodup_same_pair. *)
            explode_well_defined_spn.
            unfold NoUnmarkedPlace in Hunm_place; unfold NoDupPlaces in Hnodup_places.
            rewrite Hunm_place in Hnodup_places;
              rewrite Hsame_marking_state_spn in Hnodup_places;
              rewrite <- Hsame_residm_sm in Hnodup_places.
            (* Builds fs (p, n) = fs (p, x - pre_sum spn p fired) *)
            assert (Heq_fs : fst (p, n) = fst (p, x - pre_sum spn p fired))
              by (simpl; reflexivity).                    
            (* Applies nodup_same_pair to get n = x - pre_sum spn p fired. *)
            specialize (nodup_same_pair
                          residual_marking Hnodup_places (p, n) (p, x - pre_sum spn p fired)
                          Hin_resid_m Hin_resid_m' Heq_fs) as Heq_nx.
            injection Heq_nx as Heq_nx.
            rewrite Heq_nx.
            assumption.
        }
        (* Then, we deduce IsSensitized spn residual_marking t' from Hequiv_m. *)
        assert (Hsens_t_in_residual_m : IsSensitized spn residual_marking t').
        {
          unfold IsSensitized.
          split. assumption.
          split. assumption.
          split. apply get_neighbours_correct in e0.
          apply in_fst_split in e0.
          explode_well_defined_spn.
          unfold NoUnknownTransInLNeighbours in *.
          rewrite <- Hunk_tr_neigh in e0.
          rewrite <- Heq_tt'; assumption.
          intros p n Hin_resid_m.
          rewrite <- Hequiv_m in Hin_resid_m.
          unfold IsSensitized in Hsens_t.
          decompose [and] Hsens_t.
          apply (H3 p n Hin_resid_m).
        }
        (* Then we apply is_sensitized_complete to show the contradiction with e3. *)
        apply get_neighbours_correct in e0.
        rewrite Heq_tt' in e0.
        specialize (is_sensitized_complete
                      spn residual_marking t' neighbours_of_t
                      Hwell_def_spn Hsame_struct e0 Hsens_t_in_residual_m) as Hsens_t_false.
        rewrite Heq_tt' in e3.
        rewrite Hsens_t_false in e3; inversion e3.
      (* Second subcase, In t' tail then apply the induction hypothesis. *)
      + apply is_dec_list_cons_cons in Hdec_list. 
        apply NoDup_remove in Hnodup_pg; apply proj1 in Hnodup_pg.
        apply (IHo pgroup final_fired Hwell_def_spn Hwell_def_s 
                   Hin_spn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct
                   Hfun t' res_marking
                   Hin_t'_tail Hfirable_t Hsens_t Hhigh_in_fired Hsame_struct' Hres_m).
    (* ERROR CASE, is_sensitized = None. *)
    - inversion Hfun.
    (* CASE, spn_is_firable = Some false. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].
      (* First subcase t = t', show a contradiction between e1 and Hfirable_t. *)
      + rewrite <- Heq_tt' in Hfirable_t.
        apply get_neighbours_correct in e0.
        apply (spn_is_firable_complete
                 spn s neighbours_of_t t Hwell_def_spn Hwell_def_s e0) in Hfirable_t.
        rewrite Hfirable_t in e1; inversion e1.
      (* Second subcase, In t' tail, then apply induction hypothesis. *)
      + apply is_dec_list_cons_cons in Hdec_list. 
        apply NoDup_remove in Hnodup_pg; apply proj1 in Hnodup_pg.
        apply (IHo pgroup final_fired Hwell_def_spn Hwell_def_s 
                   Hin_spn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct
                   Hfun t' res_marking
                   Hin_t'_tail Hfirable_t Hsens_t Hhigh_in_fired Hsame_struct' Hres_m).
    (* ERROR CASE, spn_is_firable = None. *)
    - inversion Hfun.
    (* ERROR CASE, get_neighbours = None. *)
    - inversion Hfun.
  Qed.

  Lemma pr_is_unique :
    forall (spn : Spn)
           (s : SpnState)
           (residual_marking : list (Place * nat))
           (pgroup : list Trans)
           (fired : list Trans)
           (fired' : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans)
           (t : Trans)
           (pr : list Trans),
      NoDup (fired' ++ pgroup ++ concat pgroups) ->
      spn_fire_aux spn s residual_marking [] pgroup = Some fired ->
      spn_map_fire_aux spn s (fired' ++ fired) pgroups = Some final_fired ->
      (forall t' : Trans, HasHigherPriority spn t' t pgroup /\ In t' fired <-> In t' pr) ->
      (forall t' : Trans, HasHigherPriority spn t' t pgroup /\ In t' final_fired <-> In t' pr).
  Proof.
    intros spn s residual_marking pgroup fired fired' pgroups final_fired t pr
           Hnodup_app Hfun_fire Hfun_map_fire Hin_pr t'.
    split.
    (* CASE, in context t' ≻ t ∧ t' ∈ final_fired *)
    - intro Hpr_wedge.
      (* Two subcases, either t' ∈ fired ∨ t' ∉ fired *)
      specialize (classic (In t' fired)) as Hin_fired_vee.
      inversion_clear Hin_fired_vee as [Hin_t'_fired | Hnot_in_t'_fired].
      (* First subcase, t' ∈ fired *)
      + elim Hpr_wedge; intros Hhas_high Hin_t'_ff.
        specialize (conj Hhas_high Hin_t'_fired) as Hpr_wedge'.
        rewrite Hin_pr in Hpr_wedge'.
        assumption.
      (* Second subcase, 
            t' ∈ pgroup ⇒ 
            t' ∉ fired' ∧ t' ∉ concat pgroups ∧ t' ∉ fired ⇒
            t' ∉ final_fired, contradicts Hpr_wedge. *)
      (* Builds In t' pgroup *)
      + elim Hpr_wedge; intros Hhas_high Hin_ff.
        unfold HasHigherPriority in Hhas_high; decompose [and] Hhas_high.
        clear H H1 H2 H4; rename H0 into Hin_t'_pg.
        (* Builds ~In t' fired /\ ~In t' concat pgroups *)
        apply NoDup_app_comm in Hnodup_app.
        rewrite <- app_assoc in Hnodup_app.
        specialize (nodup_app_not_in pgroup ((concat pgroups) ++ fired') Hnodup_app t' Hin_t'_pg)
          as Hnot_in_t'_app.
        apply not_app_in  in Hnot_in_t'_app.
        elim Hnot_in_t'_app; intros Hnot_in_concat Hnot_t'_in_fired.
        (* Builds ~In t' (fired' ++ fired) *)
        specialize (not_in_app t' fired' fired (conj Hnot_t'_in_fired Hnot_in_t'_fired))
          as Hnot_in_app.
        specialize (spn_map_fire_aux_not_in_not_fired
                      spn s (fired' ++ fired) pgroups final_fired Hfun_map_fire
                      t' Hnot_in_app Hnot_in_concat) as Hnot_in_ff.
        contradiction.
    (* CASE, in context t' ∈ pr *)
    - intro Hin_t'_pr.
      split.
      + rewrite <- Hin_pr in Hin_t'_pr.
        elim Hin_t'_pr; auto.
      (* t' ∈ fired ⇒ t' ∈ final_fired. *)
      + rewrite <- Hin_pr in Hin_t'_pr.
        elim Hin_t'_pr; intros Hhash_high Hin_t'_fired.
        (* Builds In t' (fired' ++ fired) to apply spn_map_fire_aux_in_fired. *)
        specialize (or_intror (In t' fired') Hin_t'_fired) as Hin_t'_vee.
        specialize (in_or_app fired' fired t' Hin_t'_vee) as Hin_t'_app.
        (* Applies spn_map_fire_aux_in_fired. *)
        apply (spn_map_fire_aux_in_fired
                 spn s (fired' ++ fired) pgroups final_fired
                 Hfun_map_fire t' Hin_t'_app).
  Qed.
  
  Theorem spn_map_fire_aux_sens_by_residual :
    forall (spn : Spn)
           (s : SpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      incl pgroups (priority_groups spn) ->
      NoDup (fired ++ concat pgroups) ->
      spn_map_fire_aux spn s fired pgroups = Some final_fired ->
      forall (pgroup : list Trans)
             (t : Trans)
             (residual_marking : list (Place * nat)),
        In pgroup pgroups ->
        In t pgroup ->
        ~In t fired ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s t ->
        (forall (pr : list Trans),
            NoDup pr ->
            (forall t' : Trans,
                HasHigherPriority spn t' t pgroup /\ In t' final_fired <-> In t' pr) ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s.(marking) ->
                In (p, n - pre_sum spn p pr) residual_marking)) ->
        IsSensitized spn residual_marking t ->
        In t final_fired.
  Proof.
    intros spn s fired pgroups;
      functional induction (spn_map_fire_aux spn s fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hwell_def_spn Hwell_def_s Hincl_pgs Hnodup_concat_pgs
             Hfun pgroup' t residual_marking Hin_pgs Hin_t_pg Hnot_in_fired
             Hmark_struct Hfirable_t Hres_mark Hsens_t.
    (* BASE CASE *)
    - inversion Hin_pgs.
    (* GENERAL CASE, two subcases. *)
    - inversion Hin_pgs as [Heq_pg | Hin_pgtail].
      (* First subcase, pgroup = pgroup'. *)
      + unfold spn_fire in *.
        rewrite Heq_pg in *.
        (* Builds pgroup' ∈ (priority_groups spn). *)
        specialize (Hincl_pgs pgroup' Hin_pgs) as Hin_spn_pgs.
        (* Builds NoDup pgroup'. *)
        explode_well_defined_spn.
        unfold NoIntersectInPriorityGroups in *.
        specialize (nodup_concat_gen (priority_groups spn)
                                     Hno_inter pgroup' Hin_spn_pgs) as Hnodup_pg.
        (* Builds an hypothesis close to Hres_mark, except final_fired is replaced by fired_trs. 
           Necessary to apply spn_fire_aux_sens_by_residual. *)
        assert (Hres_mark' :
                  forall (pr : list Trans),
                    NoDup pr ->
                    (forall t' : Trans,
                        HasHigherPriority spn t' t pgroup' /\ In t' fired_trs <-> In t' pr) ->
                    forall (p : Place) (n : nat),
                      In (p, n) (marking s) ->
                      In (p, n - pre_sum spn p pr) residual_marking).
        {
          intros pr Hnodup_pr Hin_pr p n Hin_m_s.
          (* Builds hypotheses necessary to apply pr_is_unique. *)
          rewrite concat_cons in Hnodup_concat_pgs.
          (* Applies pr_is_unique. *)
          specialize (pr_is_unique
                        spn s (marking s) pgroup' fired_trs fired_transitions
                        pgroups_tail final_fired t pr Hnodup_concat_pgs e0 Hfun Hin_pr) as Hin_pr'.
          apply (Hres_mark pr Hnodup_pr Hin_pr' p n Hin_m_s).
        }
        (* Builds ∀ (p, n) ∈ (marking s) ⇒ (p, n - pre_sum spn p []) ∈ residual *)
        assert (Hresid_m :
                  forall (p : Place) (n : nat),
                    In (p, n) (marking s) -> In (p, n - pre_sum spn p []) (marking s))
          by (simpl; intros; rewrite Nat.sub_0_r; assumption).
        (* Builds MarkingHaveSamestruct (initial_marking spn) (marking s) *)
        explode_well_defined_spn_state Hwell_def_s.
        (* Builds ∀ t' ∈ [] ⇒ t' ≻ t ∧ t' ∈ ff. *)
        assert (Hhigh_in_fired :
                  forall t' : Trans, In t' [] ->
                                     HasHigherPriority spn t' t pgroup' /\ In t' fired_trs)
          by (intros t' Hin_nil; inversion Hin_nil).
        (* Builds In t fired_trs. *)
        specialize (spn_fire_aux_sens_by_residual
                      spn s (marking s) [] pgroup' pgroup' fired_trs
                      Hwell_def_spn Hwell_def_state Hin_spn_pgs (IsDecListCons_refl pgroup')
                      Hnodup_pg Hresid_m Hsame_marking_state_spn e0
                      t residual_marking Hin_t_pg Hfirable_t Hsens_t Hhigh_in_fired
                      Hmark_struct Hres_mark') as Hin_t_fired.
        (* Then if t ∈ fired_trs ⇒ t ∈ (fired_transitions ++ fired_trs) ⇒ t ∈ final_fired *)
        assert (Hin_fired_app : In t (fired_transitions ++ fired_trs))
          by (apply in_or_app; right; assumption).
        apply (spn_map_fire_aux_in_fired
                 spn s (fired_transitions ++ fired_trs) pgroups_tail
                 final_fired Hfun t Hin_fired_app).
      (* Second subcase, pgroup' ∈ pgroups_tail, then apply the induction hypothesis *)
      (* Builds incl pgroups_tail (priority_groups spn) *)
      + apply incl_cons_inv in Hincl_pgs. 
        (* Builds ~In t fired_trs to build ~In t (fired_transitions ++ fired_trs). *)
        (* But first, builds ~In t pgroup, because ~In t pgroup ⇒ ~In t fired_trs *)
        assert (Hnodup_concat_pgs_copy := Hnodup_concat_pgs).
        rewrite concat_cons in Hnodup_concat_pgs.
        apply NoDup_app_comm in Hnodup_concat_pgs.
        apply nodup_app in Hnodup_concat_pgs.
        elim Hnodup_concat_pgs; intros Hnodup_app Hnodup_fired.
        apply NoDup_app_comm in Hnodup_app.
        specialize (nodup_app_not_in (concat pgroups_tail) pgroup Hnodup_app)
          as Hnot_in_pgroup.
        specialize (in_concat t pgroup' pgroups_tail Hin_t_pg Hin_pgtail) as Hin_t_concat.
        specialize (Hnot_in_pgroup t Hin_t_concat) as Hnot_in_pgroup.
        unfold spn_fire in e0.
        assert (Hnot_in_nil : ~In t []) by apply in_nil.
        specialize (spn_fire_aux_not_in_not_fired
                      spn s (marking s) [] pgroup fired_trs t
                      Hnot_in_nil Hnot_in_pgroup e0) as Hnot_in_fired'.
        specialize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_fired'))
          as Hnot_in_app.
        (* Builds NoDup ((fired_transitions ++ fired_trs) ++ concat pgroups_tail). *)
        rewrite concat_cons in Hnodup_concat_pgs_copy.
        
        (* First, we need NoDup fired_trs /\ incl fired_trs ([] ++ pgroup) *)
        apply nodup_app in Hnodup_app; elim Hnodup_app; intros Hnodup_concat_pgs' Hnodup_pg.
        rewrite <- app_nil_l in Hnodup_pg.
        specialize (spn_fire_aux_nodup_fired spn s (marking s) [] pgroup fired_trs
                                             Hwell_def_spn Hwell_def_s Hnodup_pg e0)
          as Hnodup_incl.
        elim Hnodup_incl; intros Hnodup_fired_trs Hincl_fired.
        rewrite app_nil_l in Hincl_fired.
        specialize (nodup_app_incl
                      fired_transitions pgroup (concat pgroups_tail) fired_trs
                      Hnodup_concat_pgs_copy Hnodup_fired_trs Hincl_fired) as Hnodup_app'.
        rewrite app_assoc in Hnodup_app'.
        (* Finally applies the induction hypothesis. *)
        apply (IHo final_fired Hwell_def_spn Hwell_def_s
                   Hincl_pgs Hnodup_app' Hfun pgroup' t residual_marking
                   Hin_pgtail Hin_t_pg Hnot_in_app Hmark_struct Hfirable_t Hres_mark Hsens_t).
    (* ERROR CASE. *)
    - inversion Hfun.
  Qed.
  
  Theorem spn_map_fire_sens_by_residual :
    forall (spn : Spn)
           (s s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      spn_map_fire spn s = Some s' ->
      forall (pgroup : list Trans)
             (t : Trans)
             (residual_marking : list (Place * nat)),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s' t ->
        (forall (pr : list Trans),
            NoDup pr ->
            (forall t' : Trans,
                HasHigherPriority spn t' t pgroup /\ In t' s'.(fired) <-> In t' pr) ->
            (forall (p : Place) (n : nat),
                In (p, n) s'.(marking) -> In (p, n - pre_sum spn p pr) residual_marking)) ->
        IsSensitized spn residual_marking t ->
        In t s'.(fired).
  Proof.
    intros spn s s' Hwell_def_spn Hwell_def_s Hfun;
      (* Builds IsWelldefinedspnstate s' before functional induction. *)
      specialize (spn_map_fire_well_defined_state
                    spn s s' Hwell_def_spn Hwell_def_s Hfun) as Hwell_def_s';
      functional induction (spn_map_fire spn s) using spn_map_fire_ind;
      intros pgroup t residual_marking Hin_spn_pgs Hin_t_pg Hmark_struct Hfirable_t.
    (* Need to rewrite (SPN.fired s') with fired, (marking s') with (marking s) and
       SpnIsFirable spn s' t with SpnIsFirable spn s t. *)
    - injection Hfun; intro Heq_s'.
      assert (Heq_marking : (marking s) = (marking s')) by (rewrite <- Heq_s'; simpl; auto).
      specialize (state_same_marking_firable_iff
                    spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s' Heq_marking)
        as Heq_firable.
      rewrite <- Heq_s'; simpl.
      rewrite <- Heq_firable in Hfirable_t.
      (* Need of few hypotheses. *)
      assert (Hwell_def_spn' := Hwell_def_spn).
      unfold IsWellDefinedSpn in Hwell_def_spn.
      do 3 (apply proj2 in Hwell_def_spn); apply proj1 in Hwell_def_spn.
      rename Hwell_def_spn into Hnodup_concat.
      rename Hwell_def_spn' into Hwell_def_spn.
      unfold NoIntersectInPriorityGroups in *.
      assert (Hnot_in_nil : ~In t []) by apply in_nil.      
      (* Applies spn_map_fire_aux_sens_by_residual *)
      apply (spn_map_fire_aux_sens_by_residual 
               spn s [] (priority_groups spn) fired Hwell_def_spn Hwell_def_s
               (incl_refl (priority_groups spn)) Hnodup_concat e pgroup t
               residual_marking Hin_spn_pgs Hin_t_pg Hnot_in_nil Hmark_struct Hfirable_t).
    (* ERROR CASE *)
    - inversion Hfun.    
  Qed.
  
End SpnSensitizedByResidual.

(** *** Third part of correctness proof *)

(** The goal in this part is to prove: 

    spn_map_fire = Some s' ⇒ 
    ∀ t ∈ firable(s'), t ∉ sens(M - ∑ pre(t'), ∀ t'∈ Pr(t)) ⇒ t ∉ Fired' *)

Section SpnNotSensitizedByResidual.

  Lemma spn_fire_aux_not_sens_by_residual :
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
      (* Function ⇒ Specification *)
      spn_fire_aux spn s residual_marking fired pg = Some final_fired ->
      forall (t : Trans)
             (res_marking : list (Place * nat)),
        (* Hypotheses on t. *)
        In t pg ->
        SpnIsFirable spn s t ->
        ~IsSensitized spn res_marking t ->
        (* Hypotheses on fired *)
        (forall t'' : Trans, In t'' fired -> HasHigherPriority spn t'' t pgroup /\
                                             In t'' final_fired) ->
        (* Hypotheses on res_marking. *)
        MarkingHaveSameStruct spn.(initial_marking) res_marking ->
        (forall (pr : list Trans),
            NoDup pr ->
            (forall t' : Trans,
                HasHigherPriority spn t' t pgroup /\ In t' final_fired <->
                In t' pr) ->
            (forall (p : Place) (n : nat),
                In (p, n) (marking s) -> In (p, n - (pre_sum spn p pr)) res_marking)) ->
        ~In t final_fired.
  Proof.
    intros spn s residual_marking fired pg;
      functional induction (spn_fire_aux spn s residual_marking fired pg)
                 using spn_fire_aux_ind;
      intros pgroup final_fired Hwell_def_spn Hwell_def_s
             Hin_spn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct Hfun
             t' res_marking Hin_t_pg Hfirable_t Hnotsens_t Hhigh_in_fired Hsame_struct' Hres_m.
    (* BASE CASE, pg = []. *)
    - inversion Hin_t_pg.
    (* GENERAL CASE, with two subcases. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].
      (* First subcase, t = t' *)
      (* We need to prove that residual_marking and res_marking are the same, 
         therefore, there is a contradiction between e3 and Hnotsens_t. *)
      + (* Hpr_is_fired is needed to specialize Hres_m. *)
        assert (Hpr_is_fired :
                  forall t'' : Trans, 
                    HasHigherPriority spn t'' t' pgroup /\ In t'' final_fired ->
                    In t'' fired). 
        {
          intros t'' Hw; elim Hw; intros Hhas_high Hin_ts_ff; clear Hw.
          specialize (spn_fire_aux_final_fired_vee
                        spn s residual_marking' (fired ++ [t]) tail final_fired t'')
            as Hff_vee.
          rewrite <- app_assoc in Hff_vee.
          specialize (Hff_vee Hnodup_pg Hin_ts_ff Hfun) as Hin_ts_vee; clear Hff_vee.
          inversion_clear Hin_ts_vee as [Hin_fired | Hin_ts_tail].
          - apply in_app_or in Hin_fired.
            inversion_clear Hin_fired as [Hin_fired_strict | Hin_tst].
            + assumption.
            + inversion Hin_tst as [Heq_tst | Hin_nil].
              (* Contradiction with the definition of t'' ≻ t' *)
              -- unfold HasHigherPriority in Hhas_high.
                 do 4 (apply proj2 in Hhas_high).
                 unfold IsPredInNoDupList in Hhas_high.
                 apply proj1 in Hhas_high.
                 symmetry in Heq_tst; rewrite Heq_tt' in Heq_tst.
                 contradiction.
              -- inversion Hin_nil.
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
        (* Now we have Hpr_is_fired, we can specialize Hres_m. *)
        assert (Hpr_iff :
                  forall t'' : Trans,
                    HasHigherPriority spn t'' t' pgroup /\ In t'' final_fired <-> In t'' fired)
          by (intros t'0; split; [apply (Hpr_is_fired t'0) | apply (Hhigh_in_fired t'0)]).
        specialize (nodup_app fired (t :: tail) Hnodup_pg) as Hnodup_fired.
        apply proj1 in Hnodup_fired.
        specialize (Hres_m fired Hnodup_fired Hpr_iff).
        (* Now we can show the equivalence between residual_marking and res_marking. *)
        assert (Hequiv_m : forall (p : Place) (n : nat), In (p, n) res_marking <->
                                                         In (p, n) residual_marking).
        {
          intros p n.
          split.
          - intro Hin_res_m.
            (* Builds (fs (marking s)) = (fs res_marking) *)
            explode_well_defined_spn_state Hwell_def_s.
            unfold MarkingHaveSameStruct in *.
            assert (Hsame_resm_sm : fst (split res_marking) = fst (split (marking s)))
              by (rewrite <- Hsame_marking_state_spn; rewrite <- Hsame_struct'; reflexivity).
            (* Builds In (p, x) (marking s) from In (p, n) res_marking. *)
            specialize (in_fst_split p n res_marking Hin_res_m) as Hin_fs_resm.
            rewrite Hsame_resm_sm in Hin_fs_resm.
            specialize (in_fst_split_in_pair p (marking s) Hin_fs_resm) as Hex_ms.
            elim Hex_ms; intros x Hin_x_ms.
            (* Applies Hresid_m and Hres_m. *)
            specialize (Hresid_m p x Hin_x_ms) as Hin_resid_m'.
            specialize (Hres_m p x Hin_x_ms) as Hin_res_m'.
            (* Builds NoDup (fs res_marking) to apply nodup_same_pair. *)
            explode_well_defined_spn.
            unfold NoUnmarkedPlace in Hunm_place; unfold NoDupPlaces in Hnodup_places.
            rewrite Hunm_place in Hnodup_places;
              rewrite Hsame_marking_state_spn in Hnodup_places;
              rewrite <- Hsame_resm_sm in Hnodup_places.
            (* Builds fs (p, n) = fs (p, x - pre_sum spn p fired) *)
            assert (Heq_fs : fst (p, n) = fst (p, x - pre_sum spn p fired))
              by (simpl; reflexivity).                    
            (* Applies nodup_same_pair to get n = x - pre_sum spn p fired. *)
            specialize (nodup_same_pair
                          res_marking Hnodup_places (p, n) (p, x - pre_sum spn p fired)
                          Hin_res_m Hin_res_m' Heq_fs) as Heq_nx.
            injection Heq_nx as Heq_nx.
            rewrite Heq_nx.
            assumption.
          - intro Hin_resid_m.
            (* Builds (fs (marking s)) = (fs res_marking) *)
            explode_well_defined_spn_state Hwell_def_s.
            unfold MarkingHaveSameStruct in *.
            assert (Hsame_residm_sm : fst (split residual_marking) = fst (split (marking s)))
              by (rewrite <- Hsame_marking_state_spn; rewrite <- Hsame_struct; reflexivity).
            (* Builds In (p, x) (marking s) from In (p, n) residual_marking. *)
            specialize (in_fst_split p n residual_marking Hin_resid_m) as Hin_fs_residm.
            rewrite Hsame_residm_sm in Hin_fs_residm.
            specialize (in_fst_split_in_pair p (marking s) Hin_fs_residm) as Hex_ms.
            elim Hex_ms; intros x Hin_x_ms.
            (* Applies Hresid_m and Hres_m. *)
            specialize (Hresid_m p x Hin_x_ms) as Hin_resid_m'.
            specialize (Hres_m p x Hin_x_ms) as Hin_res_m'.
            (* Builds NoDup (fs residual_marking) to apply nodup_same_pair. *)
            explode_well_defined_spn.
            unfold NoUnmarkedPlace in Hunm_place; unfold NoDupPlaces in Hnodup_places.
            rewrite Hunm_place in Hnodup_places;
              rewrite Hsame_marking_state_spn in Hnodup_places;
              rewrite <- Hsame_residm_sm in Hnodup_places.
            (* Builds fs (p, n) = fs (p, x - pre_sum spn p fired) *)
            assert (Heq_fs : fst (p, n) = fst (p, x - pre_sum spn p fired))
              by (simpl; reflexivity).                    
            (* Applies nodup_same_pair to get n = x - pre_sum spn p fired. *)
            specialize (nodup_same_pair
                          residual_marking Hnodup_places (p, n) (p, x - pre_sum spn p fired)
                          Hin_resid_m Hin_resid_m' Heq_fs) as Heq_nx.
            injection Heq_nx as Heq_nx.
            rewrite Heq_nx.
            assumption.
        }
        (* Useful to introduce IsSensitized spn res_marking t. *)
        apply get_neighbours_correct in e0.
        apply (is_sensitized_correct
                 spn residual_marking t neighbours_of_t Hwell_def_spn
                 Hsame_struct e0) in e3.
        assert (Hsens_t_in_res_m : IsSensitized spn res_marking t).
        {
          unfold IsSensitized.
          split. assumption.
          split. assumption.
          split. apply in_fst_split in e0.
          explode_well_defined_spn.
          unfold NoUnknownTransInLNeighbours in *.
          rewrite <- Hunk_tr_neigh in e0.
          assumption.
          intros p n Hin_resid_m.
          rewrite Hequiv_m in Hin_resid_m.
          unfold IsSensitized in e3.
          do 3 (apply proj2 in e3).
          apply (e3 p n Hin_resid_m).
        }
        rewrite Heq_tt' in Hsens_t_in_res_m.
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
        assert(Hhigh_in_fired' :
                 forall t'' : Trans, In t'' (fired ++ [t]) ->
                                     HasHigherPriority spn t'' t' pgroup /\ In t'' final_fired).
        {
          intros t'' Hin_fired_app;
            apply in_app_or in Hin_fired_app;
            inversion Hin_fired_app as [Hin_fired | Heq_tst]; clear Hin_fired_app.
          - apply (Hhigh_in_fired t'' Hin_fired).
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
                   Hnodup_pg Hresid'_m Hsame_struct Hfun t' res_marking Hin_t'_tail
                   Hfirable_t Hnotsens_t Hhigh_in_fired' Hsame_struct' Hres_m).
    (* ERROR CASE, update_residual_marking = None. *)
    - inversion Hfun.
    (* CASE is_sensitized = Some false. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_tail].
      (* Subcase 1, t = t', apply spn_fire_aux_not_in_not_fired. *)
      + apply NoDup_remove_2 in Hnodup_pg.
        apply not_app_in in Hnodup_pg.
        inversion_clear Hnodup_pg as (Hnot_in_fired & Hnot_in_tl).
        rewrite <- Heq_tt'.
        apply (spn_fire_aux_not_in_not_fired
                 spn s residual_marking fired tail final_fired t
                 Hnot_in_fired Hnot_in_tl Hfun).
      (* Subcase 2, t ∈ tail, then aplpy induction hypothesis. *)
      + apply is_dec_list_cons_cons in Hdec_list. 
        apply NoDup_remove in Hnodup_pg; apply proj1 in Hnodup_pg.
        apply (IHo pgroup final_fired Hwell_def_spn Hwell_def_s 
                   Hin_spn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct
                   Hfun t' res_marking
                   Hin_tail Hfirable_t Hnotsens_t Hhigh_in_fired Hsame_struct' Hres_m).
    (* ERROR CASE, is_sensitized = None. *)
    - inversion Hfun.
    (* CASE, spn_is_firable = Some false. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].
      (* First subcase t = t', show a contradiction between e1 and Hfirable_t. *)
      + rewrite <- Heq_tt' in Hfirable_t.
        apply get_neighbours_correct in e0.
        apply (spn_is_firable_complete
                 spn s neighbours_of_t t Hwell_def_spn Hwell_def_s e0) in Hfirable_t.
        rewrite Hfirable_t in e1; inversion e1.
      (* Second subcase, In t' tail, then apply induction hypothesis. *)
      + apply is_dec_list_cons_cons in Hdec_list. 
        apply NoDup_remove in Hnodup_pg; apply proj1 in Hnodup_pg.
        apply (IHo pgroup final_fired Hwell_def_spn Hwell_def_s 
                   Hin_spn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct
                   Hfun t' res_marking
                   Hin_t'_tail Hfirable_t Hnotsens_t Hhigh_in_fired Hsame_struct' Hres_m).
    (* ERROR CASE, spn_is_firable = None. *)
    - inversion Hfun.
    (* ERROR CASE, get_neighbours = None. *)
    - inversion Hfun.
  Qed.
  
  Lemma spn_map_fire_aux_not_sens_by_residual :
    forall (spn : Spn)
           (s : SpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      incl pgroups (priority_groups spn) ->
      NoDup (fired ++ concat pgroups) ->
      spn_map_fire_aux spn s fired pgroups = Some final_fired ->
      forall (pgroup : list Trans)
             (t : Trans)
             (residual_marking : list (Place * nat)),
        In pgroup pgroups ->
        In t pgroup ->
        ~In t fired ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s t ->
        (forall (pr : list Trans),
            NoDup pr ->
            (forall t' : Trans,
                HasHigherPriority spn t' t pgroup /\ In t' final_fired <-> In t' pr) ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s.(marking) ->
                In (p, n - pre_sum spn p pr) residual_marking)) ->
        ~IsSensitized spn residual_marking t ->
        ~In t final_fired.
  Proof.
    intros spn s fired pgroups;
      functional induction (spn_map_fire_aux spn s fired pgroups)
                 using spn_map_fire_aux_ind;
      intros final_fired Hwell_def_spn Hwell_def_s Hincl_pgs Hnodup_concat_pgs
             Hfun pgroup' t residual_marking Hin_pgs Hin_t_pg Hnot_in_fired
             Hmark_struct Hfirable_t Hres_mark Hnotsens_t.
    (* BASE CASE *)
    - inversion Hin_pgs.
    (* GENERAL CASE, two subcases. *)
    - inversion Hin_pgs as [Heq_pg | Hin_pgtail].
      (* First case, pgroup = pgroup'. *)
      (* t ∉ fired_transitions ∧ t ∉ fired_trs ∧ t ∉ (concat pgroups_tail) ⇒ 
         t ∉ final_fired. *)
      + (* Builds t ∉ fired_trs from e0 (spn_fire). *)
        unfold spn_fire in *.
        rewrite Heq_pg in *.
        (* Builds pgroup' ∈ (priority_groups spn). *)
        specialize (Hincl_pgs pgroup' Hin_pgs) as Hin_spn_pgs.
        (* Builds NoDup pgroup'. *)
        explode_well_defined_spn.
        unfold NoIntersectInPriorityGroups in *.
        specialize (nodup_concat_gen (priority_groups spn)
                                     Hno_inter pgroup' Hin_spn_pgs) as Hnodup_pg.
        (* Builds an hypothesis close to Hres_mark, except final_fired is replaced by fired_trs. 
           Necessary to apply spn_fire_aux_sens_by_residual. *)
        assert (Hres_mark' :
                  forall (pr : list Trans),
                    NoDup pr ->
                    (forall t' : Trans,
                        HasHigherPriority spn t' t pgroup' /\ In t' fired_trs <-> In t' pr) ->
                    forall (p : Place) (n : nat),
                      In (p, n) (marking s) ->
                      In (p, n - pre_sum spn p pr) residual_marking).
        {
          intros pr Hnodup_pr Hin_pr p n Hin_m_s.
          (* Builds hypotheses necessary to apply pr_is_unique. *)
          rewrite concat_cons in Hnodup_concat_pgs.
          (* Applies pr_is_unique. *)
          specialize (pr_is_unique
                        spn s (marking s) pgroup' fired_trs fired_transitions
                        pgroups_tail final_fired t pr Hnodup_concat_pgs e0 Hfun Hin_pr) as Hin_pr'.
          apply (Hres_mark pr Hnodup_pr Hin_pr' p n Hin_m_s).
        }
        (* Builds ∀ (p, n) ∈ (marking s) ⇒ (p, n - pre_sum spn p []) ∈ residual *)
        assert (Hresid_m :
                  forall (p : Place) (n : nat),
                    In (p, n) (marking s) -> In (p, n - pre_sum spn p []) (marking s))
          by (simpl; intros; rewrite Nat.sub_0_r; assumption).
        (* Builds MarkingHaveSamestruct (initial_marking spn) (marking s) *)
        explode_well_defined_spn_state Hwell_def_s.
        (* Builds ∀ t' ∈ [] ⇒ t' ≻ t ∧ t' ∈ ff. *)
        assert (Hhigh_in_fired :
                  forall t' : Trans, In t' [] ->
                                     HasHigherPriority spn t' t pgroup' /\ In t' fired_trs)
          by (intros t' Hin_nil; inversion Hin_nil).
        (* Builds ~In t fired_trs. *)
        specialize (spn_fire_aux_not_sens_by_residual
                      spn s (marking s) [] pgroup' pgroup' fired_trs
                      Hwell_def_spn Hwell_def_state Hin_spn_pgs (IsDecListCons_refl pgroup')
                      Hnodup_pg Hresid_m Hsame_marking_state_spn e0
                      t residual_marking Hin_t_pg Hfirable_t Hnotsens_t Hhigh_in_fired
                      Hmark_struct Hres_mark') as Hnot_in_fired'.
        (* Then we need, ~In t (concat pgroups_tail) *)
        specialize (nodup_app fired_transitions (concat (pgroup' :: pgroups_tail))
                              Hnodup_concat_pgs) as Hnodup_concat.
        apply proj2 in Hnodup_concat.
        rewrite concat_cons in Hnodup_concat.
        specialize (nodup_app_not_in pgroup' (concat pgroups_tail)
                                     Hnodup_concat t Hin_t_pg) as Hnot_in_concat.
        (* Then if t ∉ fired_trs ⇒ t ∉ (fired_transitions ++ fired_trs) ∧
                   t ∉ concat pgroups_tail ⇒ t ∈ final_fired *)
        specialize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_fired'))
          as Hnotin_fired_app.
        apply (spn_map_fire_aux_not_in_not_fired
                 spn s (fired_transitions ++ fired_trs) pgroups_tail
                 final_fired Hfun t Hnotin_fired_app Hnot_in_concat).
      (* Second subcase, pgroup' ∈ pgroups_tail, then apply the induction hypothesis *)
      (* Builds incl pgroups_tail (priority_groups spn) *)
      + apply incl_cons_inv in Hincl_pgs. 
        (* Builds ~In t fired_trs to build ~In t (fired_transitions ++ fired_trs). *)
        (* But first, builds ~In t pgroup, because ~In t pgroup ⇒ ~In t fired_trs *)
        assert (Hnodup_concat_pgs_copy := Hnodup_concat_pgs).
        rewrite concat_cons in Hnodup_concat_pgs.
        apply NoDup_app_comm in Hnodup_concat_pgs.
        apply nodup_app in Hnodup_concat_pgs.
        elim Hnodup_concat_pgs; intros Hnodup_app Hnodup_fired.
        apply NoDup_app_comm in Hnodup_app.
        specialize (nodup_app_not_in (concat pgroups_tail) pgroup Hnodup_app)
          as Hnot_in_pgroup.
        specialize (in_concat t pgroup' pgroups_tail Hin_t_pg Hin_pgtail) as Hin_t_concat.
        specialize (Hnot_in_pgroup t Hin_t_concat) as Hnot_in_pgroup.
        unfold spn_fire in e0.
        assert (Hnot_in_nil : ~In t []) by apply in_nil.
        specialize (spn_fire_aux_not_in_not_fired
                      spn s (marking s) [] pgroup fired_trs t
                      Hnot_in_nil Hnot_in_pgroup e0) as Hnot_in_fired'.
        specialize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_fired'))
          as Hnot_in_app.
        (* Builds NoDup ((fired_transitions ++ fired_trs) ++ concat pgroups_tail). *)
        rewrite concat_cons in Hnodup_concat_pgs_copy.
        
        (* First, we need NoDup fired_trs /\ incl fired_trs ([] ++ pgroup) *)
        apply nodup_app in Hnodup_app; elim Hnodup_app; intros Hnodup_concat_pgs' Hnodup_pg.
        rewrite <- app_nil_l in Hnodup_pg.
        specialize (spn_fire_aux_nodup_fired spn s (marking s) [] pgroup fired_trs
                                             Hwell_def_spn Hwell_def_s Hnodup_pg e0)
          as Hnodup_incl.
        elim Hnodup_incl; intros Hnodup_fired_trs Hincl_fired.
        rewrite app_nil_l in Hincl_fired.
        specialize (nodup_app_incl
                      fired_transitions pgroup (concat pgroups_tail) fired_trs
                      Hnodup_concat_pgs_copy Hnodup_fired_trs Hincl_fired) as Hnodup_app'.
        rewrite app_assoc in Hnodup_app'.
        (* Finally applies the induction hypothesis. *)
        apply (IHo final_fired Hwell_def_spn Hwell_def_s
                   Hincl_pgs Hnodup_app' Hfun pgroup' t residual_marking
                   Hin_pgtail Hin_t_pg Hnot_in_app Hmark_struct Hfirable_t Hres_mark Hnotsens_t).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.
  
  Theorem spn_map_fire_not_sens_by_residual :
    forall (spn : Spn)
           (s s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      spn_map_fire spn s = Some s' ->
      forall (pgroup : list Trans)
             (t : Trans)
             (residual_marking : list (Place * nat)),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s' t ->
        (forall (pr : list Trans),
            NoDup pr ->
            (forall t' : Trans,
                HasHigherPriority spn t' t pgroup /\ In t' s'.(fired) <-> In t' pr) ->
            (forall (p : Place) (n : nat),
                In (p, n) s'.(marking) -> In (p, n - pre_sum spn p pr) residual_marking)) ->
        ~IsSensitized spn residual_marking t ->
        ~In t s'.(fired).
  Proof.
    intros spn s s' Hwell_def_spn Hwell_def_s Hfun;
      (* Builds IsWelldefinedspnstate s' before functional induction. *)
      specialize (spn_map_fire_well_defined_state
                    spn s s' Hwell_def_spn Hwell_def_s Hfun) as Hwell_def_s';
      functional induction (spn_map_fire spn s) using spn_map_fire_ind;
      intros pgroup t residual_marking Hin_spn_pgs Hin_t_pg Hmark_struct Hfirable_t.
    (* Need to rewrite (SPN.fired s') with fired, (marking s') with (marking s) and
       SpnIsFirable spn s' t with SpnIsFirable spn s t. *)
    - injection Hfun; intro Heq_s'.
      assert (Heq_marking : (marking s) = (marking s')) by (rewrite <- Heq_s'; simpl; auto).
      specialize (state_same_marking_firable_iff
                    spn s s' Hwell_def_spn Hwell_def_s Hwell_def_s' Heq_marking)
        as Heq_firable.
      rewrite <- Heq_s'; simpl.
      rewrite <- Heq_firable in Hfirable_t.
      (* Need of few hypotheses. *)
      assert (Hwell_def_spn' := Hwell_def_spn).
      unfold IsWellDefinedSpn in Hwell_def_spn.
      do 3 (apply proj2 in Hwell_def_spn); apply proj1 in Hwell_def_spn.
      rename Hwell_def_spn into Hnodup_concat.
      rename Hwell_def_spn' into Hwell_def_spn.
      assert (Hnot_in_nil : ~In t []) by apply in_nil.
      (* Applies spn_map_fire_aux_sens_by_residual *)
      apply (spn_map_fire_aux_not_sens_by_residual 
               spn s [] (priority_groups spn) fired Hwell_def_spn Hwell_def_s
               (incl_refl (priority_groups spn)) Hnodup_concat e pgroup t
               residual_marking Hin_spn_pgs Hin_t_pg Hnot_in_nil Hmark_struct Hfirable_t).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.
  
End SpnNotSensitizedByResidual.