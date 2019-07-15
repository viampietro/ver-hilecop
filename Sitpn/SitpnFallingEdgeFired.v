(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import misc. lemmas and tactics. *)

Require Import Hilecop.Sitpn.SitpnCoreLemmas.
Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Sitpn.SitpnTactics.
Require Import Hilecop.Utils.HilecopTactics.

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
      intros pgroup final_fired Hwell_def_sitpn Hwell_def_s Hin_pgroups
             His_dec Hfun t' Hin_pg Hnot_in_fired Hnot_firable.
    
    (* Base case, pg = []. *)
    - inversion Hin_pg.
      
    (* CASE sitpn_is_firable t' = Some true *)
    - inversion_clear Hin_pg as [Heq_t | Hin_tail].
      
      (* Case t' = t.
         
         We have to show ~SitpnIsFirable -> sitpn_is_firable = Some
         false, then contradiction. *)
      + (* Builds premises for sitpn_is_firable_correct. *)
        deduce_in_transs.
        
        (* Specializes sitpn_is_firable_correct, then contradiction. *)
        specialize (sitpn_is_firable_correct
                      t Hwell_def_sitpn Hwell_def_s Hin_t_transs e0) as Hfirable.
        rewrite Heq_t in Hfirable; contradiction.
        
      (* Case t' ∈ tail, then apply IH. *)
      + (* Builds premises for IH. *)

        (* Premise t' ∉ (fired ++ [t]) *)
        assert (Hnot_in_fired_app : ~In t' (fired ++ [t])).
        {
          deduce_nodup_in_dec_pgroup.
          deduce_nodup_hd_not_in.
          specialize (not_in_in_diff t t' tail (conj Hnot_in_tl Hin_tail)) as Hneq_tt'.
          assert (Hnot_in_tlist : ~In t' [t]) by (apply not_in_cons; auto).
          apply (not_in_app t' fired [t] (conj Hnot_in_fired Hnot_in_tlist)).            
        }

        (* Premise IsDecListCons tail pgroup *)
        apply is_dec_list_cons_cons in His_dec.

        (* Applies IH with premises. *)
        apply (IHo pgroup final_fired Hwell_def_sitpn Hwell_def_s Hin_pgroups
                   His_dec Hfun t' Hin_tail Hnot_in_fired_app Hnot_firable).
           
    (* Case update_residual_marking returns None. *)
    - inversion Hfun.
      
    (* Case is_sensitized returns Some false. *)
    - inversion_clear Hin_pg as [Heq_tt' | Hin_t'_tail].

      (* Case t = t' *)
      +
        (* Premise to apply sitpn_fire_aux_not_in_not_fired *)
        deduce_nodup_in_dec_pgroup;
          rewrite NoDup_cons_iff in Hnodup_ttail;
          apply proj1 in Hnodup_ttail as Hnot_in_tail;
          rewrite Heq_tt' in Hnot_in_tail.

        (* Applies sitpn_fire_aux_not_in_not_fired. *)
        apply (sitpn_fire_aux_not_in_not_fired
                 sitpn state residual_marking fired tail final_fired t'
                 Hnot_in_fired Hnot_in_tail Hfun).

      (* Case t' ∈ tail, then apply IH. *)
      + (* Builds premises for IH. *)

        (* Premise t' ∉ (fired ++ [t]) *)
        assert (Hnot_in_fired_app : ~In t' (fired ++ [t])).
        {
          deduce_nodup_in_dec_pgroup.
          deduce_nodup_hd_not_in.
          specialize (not_in_in_diff t t' tail (conj Hnot_in_tl Hin_t'_tail)) as Hneq_tt'.
          assert (Hnot_in_tlist : ~In t' [t]) by (apply not_in_cons; auto).
          apply (not_in_app t' fired [t] (conj Hnot_in_fired Hnot_in_tlist)).            
        }

        (* Premise IsDecListCons tail pgroup *)
        apply is_dec_list_cons_cons in His_dec.

        (* Applies IH with premises. *)
        apply (IHo pgroup final_fired Hwell_def_sitpn Hwell_def_s Hin_pgroups
                   His_dec Hfun t' Hin_t'_tail Hnot_in_fired Hnot_firable).
        
    (* ERROR CASE is_sensitized returns None. *)
    - inversion Hfun.
      
    (* CASE sitpn_is_firable returns Some false. *)
    - inversion_clear Hin_pg as [Heq_tt' | Hin_t'_tail].

      (* Case t = t' *)
      +
        (* Premise to apply sitpn_fire_aux_not_in_not_fired *)
        deduce_nodup_in_dec_pgroup;
          rewrite NoDup_cons_iff in Hnodup_ttail;
          apply proj1 in Hnodup_ttail as Hnot_in_tail;
          rewrite Heq_tt' in Hnot_in_tail.

        (* Applies sitpn_fire_aux_not_in_not_fired. *)
        apply (sitpn_fire_aux_not_in_not_fired
                 sitpn state residual_marking fired tail final_fired t'
                 Hnot_in_fired Hnot_in_tail Hfun).

      (* Case t' ∈ tail, then apply IH. *)
      + (* Builds premises for IH. *)

        (* Premise t' ∉ (fired ++ [t]) *)
        assert (Hnot_in_fired_app : ~In t' (fired ++ [t])).
        {
          deduce_nodup_in_dec_pgroup.
          deduce_nodup_hd_not_in.
          specialize (not_in_in_diff t t' tail (conj Hnot_in_tl Hin_t'_tail)) as Hneq_tt'.
          assert (Hnot_in_tlist : ~In t' [t]) by (apply not_in_cons; auto).
          apply (not_in_app t' fired [t] (conj Hnot_in_fired Hnot_in_tlist)).            
        }

        (* Premise IsDecListCons tail pgroup *)
        apply is_dec_list_cons_cons in His_dec.

        (* Applies IH with premises. *)
        apply (IHo pgroup final_fired Hwell_def_sitpn Hwell_def_s Hin_pgroups
                   His_dec Hfun t' Hin_t'_tail Hnot_in_fired Hnot_firable).
           
    (* ERROR CASE sitpn_is_firable = None *)
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
    
    (* Applies sitpn_fire_aux_not_firable_not_fired. *)
    apply (sitpn_fire_aux_not_firable_not_fired
             sitpn state (marking state) [] pgroup pgroup fired
             Hwell_def_sitpn Hwell_def_state Hin_pgroups (IsDecListCons_refl pgroup) Hfun
             t Hin_pgroup (@in_nil Trans t) Hnot_firable).
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

    (* INDUCTION CASE *)

    (* CASE sitpn_fire = Some fired_trs. *)
    - inversion_clear Hin_pgs as [Heq_pg | Hin_pgs_tail].

      (* CASE pgroup = pgroup'. 
         
         - If t ∉ firable then t ∉ fired_trs (sitpn_fire_not_firable_not_in).
         - If t ∉ fired_trs ∧ t ∉ fired_transitions ∧ t ∉ (concat pgroups_tail)
           then t ∉ final_fired (sitpn_map_fire_aux_not_in_not_fired)
       *)
      + (* First specializes, sitpn_fire_not_firable_not_fired to get 
           ~In t fired_trs. *)
        specialize (is_dec_list_cons_incl His_dec) as Hincl_pg_pgs.
        specialize (in_eq pgroup pgroups_tail) as Hin_pgs_tl.
        apply_incl Hin_sitpn_pgs.
        rewrite <- Heq_pg in Hin_pg.
        specialize (sitpn_fire_not_firable_not_fired
                      sitpn state pgroup fired_trs Hwell_def_sitpn Hwell_def_s
                      Hin_sitpn_pgs e0 t Hin_pg Hnot_firable) as Hnot_in_ftrs.

        (* Second, builds (~In t (fired_transitions ++ fired_trs)) 
           from ~In t fired_transitions and ~In t fired_trs. *)
        specialize (not_in_app t fired_transitions fired_trs
                               (conj Hnot_in_fired Hnot_in_ftrs))
          as Hnot_in_fired_app.
        
        (* Builds ~In t (concat pgroups_tail) to apply 
           sitpn_map_fire_aux_not_in_not_fired *)
        explode_well_defined_sitpn.
        unfold NoIntersectInPriorityGroups in Hno_inter.
        specialize (is_dec_list_cons_concat His_dec) as His_dec_concat.
        specialize (nodup_is_dec_list_cons Hno_inter His_dec_concat)
          as Hnodup_concat_pgs_cons.
        rewrite concat_cons in Hnodup_concat_pgs_cons.
        specialize (nodup_app_not_in pgroup (concat pgroups_tail) Hnodup_concat_pgs_cons t Hin_pg)
          as Hnot_in_concat.        
        
        (* Applies sitpn_map_fire_aux_not_in_not_fired *)
        apply (sitpn_map_fire_aux_not_in_not_fired
                 sitpn state (fired_transitions ++ fired_trs) pgroups_tail final_fired Hfun
                 t Hnot_in_fired_app Hnot_in_concat).
        
      (* CASE In pgroup' pgroups_tail, then apply IHo. *)
      + 
        (* Builds ~In t (fired_transitions ++ fired_trs). 

           First, we need (~In t pgroup) to apply sitpn_fire_aux_not_in_not_fired. *)

        assert (Hnot_in_t_pg : ~In t pgroup).
        {
          explode_well_defined_sitpn.
          unfold NoIntersectInPriorityGroups in Hno_inter.
          specialize (is_dec_list_cons_concat His_dec) as His_dec_concat.
          specialize (nodup_is_dec_list_cons Hno_inter His_dec_concat)
            as Hnodup_concat_pgs_cons.
          rewrite concat_cons in Hnodup_concat_pgs_cons.
          specialize (NoDup_app_comm pgroup (concat pgroups_tail) Hnodup_concat_pgs_cons)
            as Hnodup_concat_inv.
          specialize (nodup_app_not_in (concat pgroups_tail) pgroup Hnodup_concat_inv)
            as Hfall_not_in_pg.
          specialize (in_concat t pgroup' pgroups_tail Hin_pg Hin_pgs_tail) as Hin_concat.
          specialize (Hfall_not_in_pg t Hin_concat) as Hnot_in_pg.
          assumption.
        }
        
        (* Second, we apply sitpn_fire_aux_not_in_not_fired
           to obtain ~In t fired_trs. *)
        unfold sitpn_fire in e0.
        specialize (sitpn_fire_aux_not_in_not_fired
                      sitpn state (marking state) [] pgroup fired_trs t
                      (@in_nil Trans t) Hnot_in_t_pg e0) as Hnot_in_fired'.
        
        (* Finally, builds (~In t (fired_transitions ++ fired_trs)) *)
        specialize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_fired'))
          as Hnot_in_fired_app.
        
        (* Applies IHo. *)
        apply (IHo final_fired Hwell_def_sitpn Hwell_def_s
                   (is_dec_list_cons_cons His_dec) Hfun pgroup' t Hin_pgs_tail
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
    intros sitpn s to_be_fired Hwell_def_sitpn Hwell_def_s Hfun
           pgroup t Hin_pg_pgs Hin_t_pg Hnot_firable;
      unfold sitpn_map_fire in Hfun.

    (* Applies sitpn_map_fire_aux_not_firable_not_fired. *)
    apply (sitpn_map_fire_aux_not_firable_not_fired
             sitpn s [] (priority_groups sitpn) to_be_fired
             Hwell_def_sitpn Hwell_def_s (IsDecListCons_refl (priority_groups sitpn))
             Hfun pgroup t Hin_pg_pgs Hin_t_pg (@in_nil Trans t) Hnot_firable).    
  Qed.
           
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

