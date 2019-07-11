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

  (** ∀ t ∈ fired, 
      sitpn_fire_aux sitpn state residual_marking fired group = Some final_fired ⇒ 
      t ∈ final_fired *)
  
  Lemma sitpn_fire_aux_in_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pgroup : list Trans)
           (final_fired : list Trans)
           (t : Trans),
      In t fired ->
      sitpn_fire_aux sitpn state residual_marking fired pgroup = Some final_fired ->
      In t final_fired.
  Proof.
    intros sitpn state residual_marking fired pgroup;
      functional induction (sitpn_fire_aux sitpn state residual_marking fired pgroup)
                 using sitpn_fire_aux_ind;
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

    (* CASE sitpn_is_firable = Some false. *)
    - apply (IHo final_fired t' Hin_t_fired Hfun).

    (* ERROR CASE, sitpn_is_firable = None. *)
    - inversion Hfun.
  Qed.
  
  (** ∀ t ∉ pgroup, t ∉ fired, 
      sitpn_fire_aux sitpn state residual_marking fired group = Some final_fired ⇒ 
      t ∉ final_fired *)
  
  Lemma sitpn_fire_aux_not_in_not_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pgroup : list Trans)
           (final_fired : list Trans)
           (t : Trans),
      ~In t fired ->
      ~In t pgroup ->
      sitpn_fire_aux sitpn state residual_marking fired pgroup = Some final_fired ->
      ~In t final_fired.
  Proof.
    intros sitpn state residual_marking fired pgroup;
      functional induction (sitpn_fire_aux sitpn state residual_marking fired pgroup)
                 using sitpn_fire_aux_ind;
      intros final_fired t' Hnot_in_fired Hnot_in_pg Hfun.

    (* BASE CASE, pgroup = []. *)
    - injection Hfun; intro Heq; rewrite <- Heq; assumption.

    (* GENERAL CASE, all went well. *)
    - apply not_in_cons in Hnot_in_pg.
      elim Hnot_in_pg; intros Hneq_t Hnot_in_tail.
      assert (Hnot_in_tt: ~In t' [t])
        by (apply (diff_not_in t' t Hneq_t)).
      assert (Hnot_in_app : ~In t' (fired ++ [t]))
        by (apply (not_in_app t' fired [t] (conj Hnot_in_fired Hnot_in_tt))).
      apply (IHo final_fired t' Hnot_in_app Hnot_in_tail Hfun).
    - inversion Hfun.

    (* CASE is_sensitized = Some false, apply induction hypothesis. *)
    - apply not_in_cons in Hnot_in_pg; elim Hnot_in_pg; intros Hdiff_tt Hnot_in_tail.
      apply (IHo final_fired t' Hnot_in_fired Hnot_in_tail Hfun).
    - inversion Hfun.

    (* CASE sitpn_is_firable = Some false, apply induction hypothesis. *)
    - apply not_in_cons in Hnot_in_pg; elim Hnot_in_pg; intros Hdiff_tt Hnot_in_tail.
      apply (IHo final_fired t' Hnot_in_fired Hnot_in_tail Hfun).
    - inversion Hfun.
  Qed.

  (** ∀ t ∈ pgroup, t ∉ fired, t ∉ firable(state),
      sitpn_fire_aux sitpn state residual_marking fired group = Some final_fired ⇒ 
      t ∉ final_fired *)
  
  Theorem sitpn_fire_aux_not_firable_not_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg : list Trans)
           (pgroup : list Trans)
           (final_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn state ->
      In pgroup sitpn.(priority_groups) ->
      IsDecListCons pg pgroup ->
      sitpn_fire_aux sitpn state residual_marking fired pg = Some final_fired ->
      forall t : Trans,
        In t pg ->
        ~In t fired ->
        ~SitpnIsFirable sitpn state t ->
        ~In t final_fired.
  Proof.
    intros sitpn state residual_marking fired pg;
      functional induction (sitpn_fire_aux sitpn state residual_marking fired pg)
                 using sitpn_fire_aux_ind;
      intros pgroup final_fired Hwell_def_sitpn Hwell_def_state Hin_pgroups
             His_dec Hfun t' Hin_pg Hnot_in_fired Hnot_firable.
    
    (* Base case, pg = []. *)
    - inversion Hin_pg.
      
    (* CASE sitpn_is_firable t' = Some true *)
    - inversion_clear Hin_pg as [Heq_t | Hin_tail].
      
      (* Case t' = t.
         
         We have to show ~SitpnIsFirable -> sitpn_is_firable = Some
         false, then contradiction. *)
      + elimtype False; apply Hnot_firable.
                
        (* Specializes sitpn_is_firable_correct. *)
        generalize (sitpn_is_firable_correct
                      sitpn state neighbours_of_t t Hwell_def_sitpn Hwell_def_state
                      Hin_lneigh e1) as Hfirable; intro.
        
        
      (* INDUCTION CASE. *)
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
           (* Builds In (t, neighbours_of_t) sitpn.(lneighbours), 
              necessary to apply sitpn_is_firable_correct. *)
           generalize (get_neighbours_correct sitpn.(lneighbours) t neighbours_of_t e0)
             as Hin_lneigh; intro.
           (* Generalizes sitpn_is_firable_correct. *)
           generalize (sitpn_is_firable_correct
                         sitpn state neighbours_of_t t Hwell_def_sitpn Hwell_def_state
                         Hin_lneigh e1) as Hfirable; intro.
           rewrite <- Heq_t; assumption.
        -- auto.
      + assumption.
      + assumption.
        
    (* ERROR CASE is_sensitized returns None. *)
    - inversion Hfun.
      
    (* CASE sitpn_is_firable returns Some false. *)
    - apply NoDup_cons_iff in Hnodup_pg; elim Hnodup_pg; intros Hnot_in_tail Hnodup_tail.
      apply in_inv in Hin_pg; elim Hin_pg.
      (* When t = t', then t ∉ fired and t ∉ tail ⇒ t ∉ final_fired 
         thanks to lemma sitpn_fire_aux_not_in_not_fired. *)
      + intro Heq_tt. rewrite Heq_tt in Hnot_in_tail.
        apply (sitpn_fire_aux_not_in_not_fired
                 sitpn state residual_marking fired tail final_fired t'
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
           
    (* ERROR CASE sitpn_is_firable = None *)
    - inversion Hfun.
      
    (* ERROR CASE get_neighbours = None *)
    - inversion Hfun.
  Qed.

  (** ∀ pgroup ∈ sitpn.(priority_groups),
      sitpn_fire sitpn state pgroup = Some fired ⇒ 
      ∀ t ∈ pgroup, t ∉ firable(state) ⇒ t ∉ fired. *)
  
  Theorem sitpn_fire_not_firable_not_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (pgroup : list Trans)
           (fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn state ->
      In pgroup sitpn.(priority_groups) ->
      sitpn_fire sitpn state pgroup = Some fired ->
      (forall t : Trans,
          In t pgroup ->
          ~SitpnIsFirable sitpn state t ->
          ~In t fired).
  Proof.
    unfold sitpn_fire.
    intros sitpn state pgroup fired Hwell_def_sitpn Hwell_def_state
           Hin_pgroups Hfun t Hin_pgroup Hnot_firable.

    (* Builds (incl pgroup pgroup). *)
    assert (Hincl_pgroup : incl pgroup pgroup) by (apply incl_refl).

    (* Builds NoDup pgroup. *)
    unfold IsWellDefinedSitpn in Hwell_def_sitpn;
      decompose [and] Hwell_def_sitpn; intros; rename_well_defined_sitpn.
    unfold NoDupTranss in *.
    unfold NoUnknownInPriorityGroups in *.
    rewrite Hno_unk_pgroups in Hnodup_transs.
    generalize (nodup_concat_gen sitpn.(priority_groups) Hnodup_transs pgroup Hin_pgroups)
      as Hnodup_pgroup; intro.              

    (* Applies sitpn_fire_aux_not_firable_not_fired. *)
    generalize (sitpn_fire_aux_not_firable_not_fired
                  sitpn state (marking state)
                  [] pgroup pgroup fired Hwell_def_sitpn
                  Hwell_def_state Hin_pgroups Hnodup_pgroup Hincl_pgroup Hfun) as Hspec; intro.
    assert (Hnot_in : ~In t []) by (apply in_nil).
    apply (Hspec t Hin_pgroup Hnot_in Hnot_firable). 
  Qed.

  (** sitpn_map_fire_aux sitpn state fired pgroups = Some final_fired ⇒ 
      ∀ t ∉ fired ∧ t ∉ (concat pgroups) ⇒ t ∉ final_fired *)
  
  Theorem sitpn_map_fire_aux_not_in_not_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      sitpn_map_fire_aux sitpn state fired pgroups = Some final_fired ->
      forall t : Trans, ~In t fired -> ~In t (concat pgroups) -> ~In t final_fired.
  Proof.
    intros sitpn state fired pgroups;
      functional induction (sitpn_map_fire_aux sitpn state fired pgroups)
                 using sitpn_map_fire_aux_ind;
      intros final_fired Hfun t Hnot_in_fired Hnot_in_concat.
    (* Base case, pgroups = [] *)
    - injection Hfun; intro Heq; rewrite Heq in *; assumption.
    (* General case *)
    - unfold sitpn_fire in e0.
      (* Builds (~In t []) to apply sitpn_fire_aux_not_in_not_fired. *)
      assert (Hnot_in_nil : ~In t []) by apply in_nil.
      (* Builds (~In t pgroup) to apply sitpn_fire_aux_not_in_not_fired. *)
      simpl in Hnot_in_concat.
      generalize (not_app_in t pgroup (concat pgroups_tail) Hnot_in_concat)
        as Hnot_in_wedge; intro.
      elim Hnot_in_wedge; intros Hnot_in_pg Hnot_in_concat'.
      (* Applies sitpn_fire_aux_not_in_not_fired *)
      generalize (sitpn_fire_aux_not_in_not_fired
                    sitpn state (marking state) [] pgroup fired_trs t
                    Hnot_in_nil Hnot_in_pg e0) as Hnot_in_ff; intro.
      (* Builds ~In t (fired_transitions ++ fired_trs) to apply IHo. *)
      generalize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_ff))
        as Hnot_in_all_ff; intro.
      (* Applies induction hypothesis. *)
      apply (IHo final_fired Hfun t Hnot_in_all_ff Hnot_in_concat').
    (* Case sitpn_fire returns None. *)
    - inversion Hfun.
  Qed.

  (** sitpn_map_fire_aux sitpn state fired pgroups = Some final_fired ⇒ 
      ∀ t ∈ fired ⇒ t ∈ final_fired *)
  
  Theorem sitpn_map_fire_aux_in_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      sitpn_map_fire_aux sitpn state fired pgroups = Some final_fired ->
      forall t : Trans, In t fired -> In t final_fired.
  Proof.
    intros sitpn state fired pgroups;
      functional induction (sitpn_map_fire_aux sitpn state fired pgroups)
                 using sitpn_map_fire_aux_ind;
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
  
  (** sitpn_map_fire_aux sitpn s fired pgroups = Some final_fired ⇒ 
      ∀ pgroup ∈ pgroups, ∀ t ∈ pgroup, 
      t ∉ fired ⇒ t ∉ firable(s) ⇒ t ∉ final_fired 
      
      N.B. firable(s) ≡ firable(s'), because 
      s.(marking) = s'.(marking) ∧ 
      s.(ditvals) = s'.(ditvals) ∧ 
      s.(condv) = s'.(condv) *)
  
  Theorem sitpn_map_fire_aux_not_firable_not_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn state ->
      IsDecListCons pgroups (priority_groups sitpn) ->
      sitpn_map_fire_aux sitpn state fired pgroups = Some final_fired ->
      (forall (pgroup : list Trans)
              (t : Trans),
          In pgroup pgroups ->
          In t pgroup ->
          ~In t fired ->
          ~SitpnIsFirable sitpn state t ->
          ~In t final_fired).
  Proof.
    intros sitpn state fired pgroups;
      functional induction (sitpn_map_fire_aux sitpn state fired pgroups)
                 using sitpn_map_fire_aux_ind;
      intros final_fired Hwell_def_sitpn Hwell_def_s His_dec
             Hfun pgroup' t Hin_pgs Hin_pg Hnot_in_fired Hnot_firable.

    (* BASE CASE, pgroups = []. *)
    - inversion Hin_pgs.

    (* GENERAL CASE *)
    - apply in_inv in Hin_pgs; elim Hin_pgs.

      (* CASE pgroup = pgroup' *)
      + intro Heq_pg.

        (* Builds ~In t (concat pgroups_tail) to apply 
           sitpn_map_fire_aux_not_in_not_fired *)
        rewrite concat_cons in Hnodup_concat.
        rewrite Heq_pg in Hnodup_concat.
        generalize (nodup_app_not_in
                      pgroup' (concat pgroups_tail) Hnodup_concat
                      t Hin_pg) as Hnot_in_concat; intro.
        
        (* Builds In pgroup sitpn.(priority_groups) to apply 
           sitpn_fire_not_firable_not_fired *)
        assert (Hin_pgs' : In pgroup (pgroup :: pgroups_tail)) by apply in_eq.
        generalize (Hincl_pgs pgroup Hin_pgs') as Hin_sitpn_pgs; intro.
        
        (* Builds (~In t fired_trs) by applying sitpn_fire_not_firable_not_fired. *)
        rewrite <- Heq_pg in Hin_pg.
        generalize (sitpn_fire_not_firable_not_fired
                      sitpn state pgroup fired_trs Hwell_def_sitpn Hwell_def_state
                      Hin_sitpn_pgs e0 t Hin_pg Hnot_firable) as Hnot_in_fired'; intro.
        
        (* Builds (~In t (fired_transitions ++ fired_trs)) *)
        generalize (not_in_app t fired_transitions fired_trs
                               (conj Hnot_in_fired Hnot_in_fired')) as Hnot_in_fired_app; intro.
        
        (* Applies sitpn_map_fire_aux_not_in_not_fired *)
        apply (sitpn_map_fire_aux_not_in_not_fired
                 sitpn state (fired_transitions ++ fired_trs) pgroups_tail final_fired Hfun
                 t Hnot_in_fired_app Hnot_in_concat).
        
      (* CASE In pgroup' pgroups_tail, then apply IHo. *)
      + intro Hin_pgs_tail.

        (* Builds NoDup (concat pgroups_tail). *)
        rewrite concat_cons in Hnodup_concat.
        generalize (nodup_app pgroup (concat pgroups_tail) Hnodup_concat)
          as Hnodup_concat_wedge; intro.
        elim Hnodup_concat_wedge; intros Hnodup_pg Hnodup_concat_tail.
        
        (* Builds (incl pgroups_tail (priority_groups sitpn)). *)
        generalize (incl_cons_inv
                      pgroup pgroups_tail
                      sitpn.(priority_groups) Hincl_pgs) as Hincl_pgs'; intro.
        
        (* Builds ~In t (fired_transitions ++ fired_trs). 

           First, we need (~In t pgroup) to apply sitpn_fire_aux_not_in_not_fired. *)
        specialize (NoDup_app_comm pgroup (concat pgroups_tail) Hnodup_concat)
          as Hnodup_concat_inv.
        specialize (nodup_app_not_in (concat pgroups_tail) pgroup Hnodup_concat_inv)
          as Hfall_not_in_pg.
        specialize (in_concat t pgroup' pgroups_tail Hin_pg Hin_pgs_tail) as Hin_concat.
        specialize (Hfall_not_in_pg t Hin_concat) as Hnot_in_pg.
        
        (* Second, we need to build (~In t fired_trs) by 
           applying sitpn_fire_aux_not_in_not_fired. *)
        unfold sitpn_fire in e0.
        assert (Hnot_in_nil : ~In t []) by apply in_nil.
        specialize (sitpn_fire_aux_not_in_not_fired
                      sitpn state (marking state) [] pgroup fired_trs t
                      Hnot_in_nil Hnot_in_pg e0) as Hnot_in_fired'.
        
        (* Finally, builds (~In t (fired_transitions ++ fired_trs)) *)
        specialize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_fired'))
          as Hnot_in_fired_app.
        
        (* Applies IHo. *)
        apply (IHo final_fired Hwell_def_sitpn Hwell_def_state
                   Hnodup_concat_tail Hincl_pgs' Hfun pgroup' t Hin_pgs_tail
                   Hin_pg  Hnot_in_fired_app Hnot_firable).
        
    (* CASE sitpn_fire returns None. *)
    - inversion Hfun.
  Qed.
  
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
    intros sitpn s to_be_fired Hfun.
    unfold sitpn_map_fire in Hfun.
    
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

