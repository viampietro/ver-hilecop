(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import Sitpn tactics, and misc. lemmas. *)

Require Import Hilecop.Sitpn.SitpnTactics.
Require Import Hilecop.Utils.HilecopLemmas.


(** * Falling Edge Lemmas about Time-Related Semantics Rules. *)

(** ** Lemmas about structure preservation of dynamic time intervals. *)

Section SitpnFallingEdgeSameStructDItvals.

  (** [update_time_intervals] preserves the structure of
      [new_d_itvals ++ d_itvals] in the returned [d_itvals']. *)
  
  Lemma update_time_intervals_same_struct_ditvals :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      update_time_intervals sitpn s d_itvals new_d_itvals = Some d_itvals' ->
      (fst (split (new_d_itvals ++ d_itvals))) = (fst (split d_itvals')).
  Proof.
    intros sitpn s d_itvals new_d_itvals;
      functional induction (update_time_intervals sitpn s d_itvals new_d_itvals)
                 using update_time_intervals_ind;
      intros d_itvals' Hfun;
      
      (* BASE CASE. *)
      ((injection Hfun as Heq_itvals; simpl; rewrite Heq_itvals; rewrite app_nil_r; reflexivity)
         
       (* GENERAL CASE *)
       || (specialize (IHo d_itvals' Hfun) as Heq_ditvals;
           rewrite fst_split_app in Heq_ditvals;
           rewrite fst_split_app in Heq_ditvals;
           simpl in Heq_ditvals;
           rewrite fst_split_app;
           rewrite fst_split_cons_app;
           simpl;
           rewrite <- app_assoc in Heq_ditvals;
           assumption)

       (* ERROR CASE *)
       || inversion Hfun).
  Qed.
  
  (** [sitpn_falling_edge] preserves the structure of the
      [d_intervals] in the returned state. *)
  
  Lemma sitpn_falling_edge_same_struct_ditvals :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (fst (split (d_intervals s))) = (fst (split (d_intervals s'))).
  Proof.
    intros sitpn s s' time_value env Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind.

    (* GENERAL CASE, all went well. *)
    - simpl in Hfun; injection Hfun as Heq_s'; rewrite <- Heq_s'.
      simpl.
      specialize (update_time_intervals_same_struct_ditvals
                    sitpn s (d_intervals s) [] d_intervals' e)
        as Hsame_struct_ditvals.
      assumption.

    (* ERROR CASE. *)
    - inversion Hfun.

    (* ERROR CASE. *)
    - inversion Hfun.

  Qed.
      
End SitpnFallingEdgeSameStructDItvals.

(** ** Lemmas about structure preservation of reset orders. *)

Section SitpnFallingEdgeResetEq.

  (** [sitpn_falling_edge] preserves the structure of the
      [d_intervals] in the returned state. *)
  
  Lemma sitpn_falling_edge_same_reset :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (reset s) = (reset s').
  Proof.
    intros sitpn s s' time_value env Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind;

      (* GENERAL CASE, all went well. *)
      ((simpl in Hfun;
        injection Hfun as Heq_s';
        rewrite <- Heq_s'; simpl; reflexivity)
       (* ERROR CASE. *)
       || inversion Hfun).
  Qed.
      
End SitpnFallingEdgeResetEq.

(** ** Reset dynamic time intervals on falling edge. *)

Section SitpnFallingEdgeResetDItvals.

  (** A couple [(t, ditval)] in [new_d_itvals] is in the list
      [ditvals'] returned by [update_time_intervals sitpn s d_itvals new_d_itvals]. *)

  Lemma update_time_intervals_in_newditvals :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (d_itvals' : list (Trans * DynamicTimeInterval))
           (t : Trans)
           (d : DynamicTimeInterval),
      In (t, d) new_d_itvals ->
      update_time_intervals sitpn s d_itvals new_d_itvals = Some d_itvals' ->
      In (t, d) d_itvals'.
  Proof.
    intros sitpn s d_itvals new_d_itvals;
      functional induction (update_time_intervals sitpn s d_itvals new_d_itvals)
                 using update_time_intervals_ind;
      intros d_itvals' t' d Hin_td_newditvals Hfun;

      (* BASE CASE. *)
      (injection Hfun as Heq; rewrite <- Heq; assumption)
      
      
      (* OTHERS CASES *)
      || (apply or_introl
            with (B := (In (t', d) [(t, active (dec_itval stc_itval))]))
           in Hin_td_newditvals;
          apply in_or_app in Hin_td_newditvals;
          apply (IHo d_itvals' t' d Hin_td_newditvals Hfun))

      || (apply or_introl
            with (B := (In (t', d) [(t, active (dec_itval itval))]))
           in Hin_td_newditvals;
          apply in_or_app in Hin_td_newditvals;
          apply (IHo d_itvals' t' d Hin_td_newditvals Hfun))

      || (apply or_introl
            with (B := (In (t', d) [(t, blocked)]))
           in Hin_td_newditvals;
          apply in_or_app in Hin_td_newditvals;
          apply (IHo d_itvals' t' d Hin_td_newditvals Hfun))

      (* ERROR CASES *)
      || (inversion Hfun).
  Qed.
      
  Lemma update_time_intervals_reset_ditvals :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      IsWellDefinedSitpnState sitpn s ->
      update_time_intervals sitpn s d_itvals new_d_itvals = Some d_itvals' ->
      (forall (t : Trans)
              (itval : TimeInterval),
          In t (fst (split d_itvals)) ->
          (~IsSensitized sitpn s.(marking) t \/
           (IsSensitized sitpn s.(marking) t /\ (In (t, true) s.(reset) \/ In t s.(fired)))) ->
          Some itval = (s_intervals sitpn t) ->
          In (t, active (dec_itval itval)) d_itvals').
  Proof.
    intros sitpn s d_itvals new_d_itvals;
      functional induction (update_time_intervals sitpn s d_itvals new_d_itvals)
                 using update_time_intervals_ind;
      intros d_itvals' Hwell_def_s Hfun t' sitval Hin_fs_ditvals Hnotsens_or_sens Hsome_itval.

    (* BASE CASE *)
    - inversion Hin_fs_ditvals.

    (* CASE (is_sens t M = Some true) ∧ (in_list t fired) *)
    - specialize (in_fst_split_in_pair t' ((t, dyn_itval) :: tl) Hin_fs_ditvals) as Hex_in_ditvals.
      inversion_clear Hex_in_ditvals as (d & Hin_ditvals).

      (* Two cases, (t', d) = (t, dyn_itval) ∨ (t', d) ∈ tl *)
      + inversion_clear Hin_ditvals as [Heq_tt'_dditval | Hin_tl].

        (* Case (t, dyn_itval) = (t', d) *)
        -- injection Heq_tt'_dditval as Heq_tt' Heq_dditval.

           (* Builds (t, active (dec_itval stc_itval)) ∈ 
              (new_d_itvals ++ [(t, active (dec_itval stc_itval))]),
              necessary to specialize update_time_intervals_in_newditvals. *)
           assert (Hin_newditvals_app :
                     In (t, active (dec_itval stc_itval))
                        (new_d_itvals ++ [(t, active (dec_itval stc_itval))]))
                  by (apply in_or_app; right; apply in_eq).
           
           (* Specializes update_time_intervals_in_newditvals. *)
           specialize (update_time_intervals_in_newditvals
                         sitpn s tl (new_d_itvals ++ [(t, active (dec_itval stc_itval))])
                         d_itvals' t (active (dec_itval stc_itval)) Hin_newditvals_app Hfun)
             as Hin_ditvals'.

           (* Rewrites sitval \w stc_itval and t \w t'. *)
           rewrite Heq_tt' in e1.
           assert (Heq_some_sitval : Some sitval = Some stc_itval)
             by (transitivity (s_intervals sitpn t'); [assumption | assumption]).
           injection Heq_some_sitval as Heq_sitval.
           rewrite Heq_tt' in Hin_ditvals'.
           rewrite Heq_sitval.
           assumption.

        (* Case (t', d) ∈ tl, apply IH. *)
        -- specialize (in_fst_split t' d tl Hin_tl) as Hin_fs_tl.
           apply (IHo d_itvals' Hwell_def_s Hfun t' sitval Hin_fs_tl Hnotsens_or_sens Hsome_itval). 

    (* CASE (is_sens t M = Some true) 
            ∧ (in_list t fired) = Some false
            ∧ get_value t reset = Some true *)
    - specialize (in_fst_split_in_pair t' ((t, dyn_itval) :: tl) Hin_fs_ditvals) as Hex_in_ditvals.
      inversion_clear Hex_in_ditvals as (d & Hin_ditvals).

      (* Two cases, (t', d) = (t, dyn_itval) ∨ (t', d) ∈ tl *)
      + inversion_clear Hin_ditvals as [Heq_tt'_dditval | Hin_tl].

        (* Case (t, dyn_itval) = (t', d) *)
        -- injection Heq_tt'_dditval as Heq_tt' Heq_dditval.

           (* Builds (t, active (dec_itval stc_itval)) ∈ 
              (new_d_itvals ++ [(t, active (dec_itval stc_itval))]),
              necessary to specialize update_time_intervals_in_newditvals. *)
           assert (Hin_newditvals_app :
                     In (t, active (dec_itval stc_itval))
                        (new_d_itvals ++ [(t, active (dec_itval stc_itval))]))
             by (apply in_or_app; right; apply in_eq).
           
           (* Specializes update_time_intervals_in_newditvals. *)
           specialize (update_time_intervals_in_newditvals
                         sitpn s tl (new_d_itvals ++ [(t, active (dec_itval stc_itval))])
                         d_itvals' t (active (dec_itval stc_itval)) Hin_newditvals_app Hfun)
             as Hin_ditvals'.

           (* Rewrites sitval \w stc_itval and t \w t'. *)
           rewrite Heq_tt' in e1.
           assert (Heq_some_sitval : Some sitval = Some stc_itval)
             by (transitivity (s_intervals sitpn t'); [assumption | assumption]).
           injection Heq_some_sitval as Heq_sitval.
           rewrite Heq_tt' in Hin_ditvals'.
           rewrite Heq_sitval.
           assumption.

        (* Case (t', d) ∈ tl, apply IH. *)
        -- specialize (in_fst_split t' d tl Hin_tl) as Hin_fs_tl.
           apply (IHo d_itvals' Hwell_def_s Hfun t' sitval Hin_fs_tl Hnotsens_or_sens Hsome_itval).

    (* CASE is_sens t M = Some true
            ∧  in_list t fired = Some false  
            ∧  get_value t reset = Some false
            ∧  dyn_itval = active itval. *)
    - specialize (in_fst_split_in_pair t' ((t, active itval) :: tl) Hin_fs_ditvals) as Hex_in_ditvals.
      inversion_clear Hex_in_ditvals as (d & Hin_ditvals).

      (* Two cases, (t', d) = (t, dyn_itval) ∨ (t', d) ∈ tl *)
      + inversion_clear Hin_ditvals as [Heq_tt'_dditval | Hin_tl].
        
        (* Case (t, active itval) = (t', d) *)
        -- injection Heq_tt'_dditval as Heq_tt' Heq_dditval.

           (* 2 subcases: 
              - t' ∉ sens(M) 
              - t' ∈ sens(M) ∧ (reset(t') ∨ t' ∈ fired *)
           inversion_clear Hnotsens_or_sens as [Hnot_sens_t' | Hsens_t'_w].

           (* Subcase t' ∉ sens(M) *)
           ++ 
           
  (** All transitions that are not sensitized by the marking at state
      [s], or that are sensitized and either received a reset order or
      were fired at the last cycle, have their dynamic time intervals
      reset. *)

  Lemma sitpn_falling_edge_reset_ditvals :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      IsWellDefinedSitpnState sitpn s ->
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (forall (t : Trans)
              (itval : TimeInterval),
          In t (fst (split s.(d_intervals))) ->
          (~IsSensitized sitpn s.(marking) t \/
           (IsSensitized sitpn s.(marking) t /\ (In (t, true) s.(reset) \/ In t s.(fired)))) ->
          Some itval = (s_intervals sitpn t) ->
          In (t, active (dec_itval itval)) s'.(d_intervals)).
  Proof.
    intros sitpn s time_value env;
      functional induction (sitpn_falling_edge sitpn s time_value env)
                 using sitpn_falling_edge_ind;
      intros s' Hfun.

    (* GENERAL CASE. *)
    - simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl.
  Admitted.
    
End SitpnFallingEdgeResetDItvals.

