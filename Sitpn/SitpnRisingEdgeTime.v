(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import lemmas about well-definition. *)

Require Import Hilecop.Sitpn.SitpnWellDefMarking.

(* Import misc. lemmas and tactics. *)

Require Import Hilecop.Sitpn.SitpnTactics.

(** * Lemmas about reset orders on rising edge.  *)

Section SitpnRisingEdgeDecideReset.

  Lemma get_blocked_and_reset_decide_reset :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (transient_marking : list (Place * nat))
           (reset_orders : list (Trans * bool))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (reset_orders' : list (Trans * bool))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      get_blocked_itvals_and_reset_orders
        sitpn s d_itvals transient_marking reset_orders new_d_itvals = Some (reset_orders', d_itvals') ->
      forall t : Trans,
        In t (fst (split d_itvals)) ->
        ~IsSensitized sitpn transient_marking t ->
        In (t, true) reset_orders'.
  Admitted.
  
  (** All transitions disabled by the transient marking
      receive a reset order at state [s'], where
      [s'] is the state returned by [sitpn_rising_edge]. *)
  
  Lemma sitpn_rising_edge_decide_reset :
    forall (sitpn : Sitpn)
           (s s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_rising_edge sitpn s = Some s' ->
      forall (t : Trans)
             (transient_marking : list (Place * nat)),
        places sitpn = fst (split transient_marking) ->
        (forall (p : Place) (n : nat),
            In (p, n) s.(marking) ->
            In (p, n - pre_sum sitpn p s.(fired)) transient_marking) ->
        In t sitpn.(transs) ->
        s_intervals sitpn t <> None ->
        ~IsSensitized sitpn transient_marking t ->
        In (t, true) s'.(reset).
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s) using sitpn_rising_edge_ind;
      intros s' Hwell_def_sitpn Hwell_def_s Hfun t transient_marking' Heq_places_tm'
             Hdef_tm' Hin_t_transs Hhas_itval_t Hnot_sens_by_tm'.

    (* GENERAL CASE *)
    - injection Hfun as Hfun; rewrite <- Hfun; simpl.
      specialize (get_blocked_and_reset_decide_reset
                    sitpn s (d_intervals s) transient_marking [] [] reset' d_intervals' e0)
        as Hin_ttrue_reset'.

      (* Deduces that t ∈ (fs (d_intervals s)) to specialize
         Hin_ttrue_reset' *)
      assert (Hin_t_ditvals := conj Hin_t_transs Hhas_itval_t).
      explode_well_defined_sitpn_state Hwell_def_s.
      rewrite (Hwf_state_ditvals t) in Hin_t_ditvals.
      clear_well_defined_sitpn_state.

      specialize (Hin_ttrue_reset' t Hin_t_ditvals).

      (* Now, we need to show that for all transition t, if t is
         sensitized by transient_marking then t is sensitized by
         transient_marking' *)
      assert (Hsens_iff : IsSensitized sitpn transient_marking t <->
                          IsSensitized sitpn transient_marking' t).
      {

        (* We need to know that transient_marking has the same structure
           as (places sitpn). *)
        specialize (map_update_marking_pre_same_marking
                      sitpn (marking s) (fired s) transient_marking e)
          as Heq_places_tm.

        (* Proves both sense of implication. *)
        split.

        (* sens by tm -> sens by tm' *)
        - unfold IsSensitized.
      
End SitpnRisingEdgeDecideReset.
