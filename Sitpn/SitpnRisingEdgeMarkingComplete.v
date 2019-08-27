(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.
Require Import Hilecop.Sitpn.SitpnTactics.
Require Import Hilecop.Sitpn.SitpnCoreLemmas.

(* Import misc. lemmas, tactics and definitions. *)

Require Import Hilecop.Utils.HilecopDefinitions.
Require Import Hilecop.Utils.HilecopLemmas.

(* Import lemmas about marking. *)

Require Import Hilecop.Sitpn.SitpnWellDefMarking.
Require Import Hilecop.Sitpn.SitpnRisingEdgeMarking.

(** * Completeness for [map_update_marking_pre]. *)

Section MapUpdateMarkingPreComplete.

  (** Completeness lemma for [modify_m]. *)

  Lemma modify_m_complete :
    forall (marking : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat),
      In p (fs marking) ->
      NoDup (fs marking) ->
      exists m' : list (Place * nat),
        modify_m marking p op nboftokens = Some m'
        /\ forall (n : nat), In (p, n) marking -> In (p, op n nboftokens) m'.
  Proof.
    induction marking.

    (* BASE CASE, marking = [] *)
    - intros p op nboftokens Hin; simpl in Hin; inversion Hin.

    (* INDUCTION CASE *)
    - destruct a; simpl; intros pl op nboftkens Hin_p_fsm Hnodup_fsm.

      (* Two case, for p =? pl *)
      case_eq (p =? pl); intros Heq_ppl.

      (* Case (p =? pl) = true *)
      + exists ((pl, op n nboftkens) :: marking).
        repeat split.
        intros nb Hv; inversion_clear Hv as [Heq_pn | Hin_m].
        
        (* Case (p, n) = (pl, nb) *)
        -- injection Heq_pn as Heq_p Heq_n; rewrite Heq_n; apply in_eq.

        (* Case (pl, nb) ∈ marking, contradiction with NoDup (fs ((p, n) :: marking)) 
           knowing that p = pl. *)
        -- apply beq_nat_true in Heq_ppl.
           rewrite Heq_ppl in Hnodup_fsm.
           unfold fs in Hnodup_fsm; rewrite fst_split_cons_app in Hnodup_fsm.
           simpl in Hnodup_fsm.
           rewrite NoDup_cons_iff in Hnodup_fsm.
           apply proj1 in Hnodup_fsm.
           apply in_fst_split in Hin_m.
           contradiction.

      (* Case (p =? pl) = false *)
      +
        (* Specializes IHmarking. *)

        assert (Hin_p_fsm' : In pl (fs marking)).
        {
          unfold fs in Hin_p_fsm; rewrite fst_split_cons_app in Hin_p_fsm.
          simpl in Hin_p_fsm.
          apply beq_nat_false in Heq_ppl.
          inversion_clear Hin_p_fsm as [Heq_ppl' | Hin_pl_fsm];
            [ contradiction | assumption ].
        }

        assert (Hnodup_fsm' : NoDup (fs marking)).
        {
          unfold fs in Hnodup_fsm; rewrite fst_split_cons_app in Hnodup_fsm.
          simpl in Hnodup_fsm.
          rewrite NoDup_cons_iff in Hnodup_fsm.
          apply proj2 in Hnodup_fsm.
          assumption.
        }

        specialize (IHmarking pl op nboftkens Hin_p_fsm' Hnodup_fsm')
          as Hex_modif_m.
        inversion_clear Hex_modif_m as (m' & Hw_modif_m).
        inversion_clear Hw_modif_m as (Hmodif_m & Hdef_m').

        (* Rewrites the goal with the newly-built hypothesis. *)
        rewrite Hmodif_m.

        (* Instantiates the new marking, then completes the goal. *)
        exists ((p, n) :: m').
        repeat split.
        intros nb Hw.
        inversion_clear Hw as [Heq_pn | Hin_m].
        -- injection Heq_pn as Heq_p Heq_n.
           apply beq_nat_false in Heq_ppl; contradiction.
        -- apply in_cons; apply (Hdef_m' nb Hin_m).           
  Qed.
  
  (** Completeness lemma for [update_marking_pre_aux]. *)

  Lemma update_marking_pre_aux_complete :
    forall (pre_places : list Place)
           (sitpn : Sitpn)
           (t : Trans)
           (marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      Permutation (places sitpn) (fs marking) ->
      IsDecListCons pre_places (pre_pl (lneighbours sitpn t)) ->
      NoDup pre_places ->
      exists m' : list (Place * nat),
        update_marking_pre_aux sitpn marking t pre_places = Some m'
        /\ (forall (p : Place) (n : nat), In p pre_places -> In (p, n) marking -> In (p, n - pre sitpn t p) m')
        /\ (fs marking) = (fs m').
  Proof.
    intros pre_places sitpn t;
      induction pre_places;
      intros marking Hwell_def_sitpn Hin_t_transs
             Hperm_pls His_dec Hnodup_prepl;
      simpl.

    (* BASE CASE, pre_places = [] *)
    
    - exists marking; repeat split.
      intros p n Hfalse; inversion Hfalse.

    (* INDUCTION CASE *)
    -
      (* Specializes modify_m_complete, then rewrites the goal. *)

      assert (Hin_a_fsm : In a (fs marking)).
      {
        assert (Hin_a_fn : In a (flatten_neighbours (lneighbours sitpn t))).
        {
          unfold flatten_neighbours.
          apply in_or_app; left.
          deduce_in_from_is_dec_list_cons His_dec as Hin_a_prepl.
          assumption.
        }

        specialize (in_transs_incl_flatten t Hwell_def_sitpn Hin_t_transs)
          as Hincl_fn_fl.
        specialize (Hincl_fn_fl a Hin_a_fn).
        explode_well_defined_sitpn.
        unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
        specialize (Hunk_pl_neigh a Hincl_fn_fl).
        rewrite Hperm_pls in Hunk_pl_neigh; assumption.
      }

      assert (Hnodup_fsm : NoDup (fs marking)).
      {
        explode_well_defined_sitpn.
        unfold NoDupPlaces in Hnodup_places.
        rewrite Hperm_pls in Hnodup_places.
        assumption.
      }
      
      specialize (modify_m_complete marking a Nat.sub (pre sitpn t a) Hin_a_fsm Hnodup_fsm)
        as Hex_modif_m.

      (* Explodes the newly-built hypotheses, then rewrites the goal. *)
      inversion_clear Hex_modif_m as (m' & Hmodif_m_w).
      inversion_clear Hmodif_m_w as (Hmodif_m & Hdef_m').
      rewrite Hmodif_m.

      (* Then specializes IHpre_places. *)
      
      assert (Hperm_pls_m' : Permutation (places sitpn) (fs m')).
      {
        specialize (modify_m_same_struct marking a Nat.sub (pre sitpn t a) m' Hmodif_m)
          as Heq_fsm_fsm'.
        unfold fs; rewrite <- Heq_fsm_fsm'; assumption.
      }

      assert (Hnodup_prepl' : NoDup pre_places).
      {
        rewrite NoDup_cons_iff in Hnodup_prepl;
          apply proj2 in Hnodup_prepl;
          assumption.
      }
      
      specialize (@IHpre_places m' Hwell_def_sitpn Hin_t_transs Hperm_pls_m'
                                (is_dec_list_cons_cons His_dec) Hnodup_prepl')
        as Hex_up_mark_pre.

      (* Explodes the newly-built hypothesis. *)
      inversion_clear Hex_up_mark_pre as (final_marking & Hup_mark_pre_w).
      inversion_clear Hup_mark_pre_w as (Hup_mark_pre & Hw).
      inversion_clear Hw as (Hdef_fm & Heq_fsm'_fsfm).

      (* Instantiates final_marking, then solves each branch of the goal. *)
      exists final_marking.
      repeat split.

      (* Trivial case. *)
      + assumption.

      (* Case definition of final_marking. *)
      + intros p n Hin_prepl_v Hin_pn_m.

        (* Two case: a = p \/ In p pre_places. *)
        inversion_clear Hin_prepl_v as [Heq_ap | Hin_p_prepl].

        (* Case a = p *)
        -- rewrite <- Heq_ap in Hin_pn_m.
           specialize (Hdef_m' n Hin_pn_m) as Hin_ansub_m'.

           (* Specializes update_marking_pre_aux_not_in_pre_places 
              to deduce In (a, n - pre) final_marking. *)

           assert (Heq_fsm_fsm' : (fs marking) = (fs m')).
           {
             apply (modify_m_same_struct marking a Nat.sub (pre sitpn t a) m' Hmodif_m).
           }
           
           assert (Hnot_in_a_prepl : ~In a pre_places).
           {
             apply NoDup_cons_iff, proj1 in Hnodup_prepl; assumption.
           }
                  
           rewrite (update_marking_pre_aux_not_in_pre_places
                      sitpn m' t pre_places final_marking Hup_mark_pre
                      a Hnot_in_a_prepl (n - pre sitpn t a)) in Hin_ansub_m'.
           rewrite Heq_ap in Hin_ansub_m'.
           assumption.

        (* Case In p pre_places *)
        --
          (* Rewrites In (p, n) marking with modify_m_in_if_diff to
             get In (p, n) m'. *)

          assert (Hneq_ap : a <> p).
          {
            apply NoDup_cons_iff, proj1 in Hnodup_prepl.
            apply (not_in_in_diff a p pre_places (conj Hnodup_prepl Hin_p_prepl)).
          }
          
          rewrite (modify_m_in_if_diff marking a Nat.sub (pre sitpn t a) m'
                                       Hmodif_m p n Hneq_ap)
            in Hin_pn_m.

          (* Completes the goal by applying Hdef_fm. *)
          apply (Hdef_fm p n Hin_p_prepl Hin_pn_m).

      (* Case fs marking = fs final_marking *)
      +
        assert (Heq_fsm_fsm' : (fs marking) = (fs m')).
        {
          apply (modify_m_same_struct marking a Nat.sub (pre sitpn t a) m' Hmodif_m).
        }

        transitivity (fs m'); [assumption | assumption].
  Qed.
  
  (** Completeness lemma for [map_update_marking_pre]. *)

  Lemma map_update_marking_pre_complete :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (fired : list Trans)
           (marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env rising_edge ->
      Permutation (places sitpn) (fs marking) ->
      incl fired (Sitpn.fired s) ->
      NoDup fired ->
      exists transient_marking : list (Place * nat),
        map_update_marking_pre sitpn marking fired = Some transient_marking
        /\ forall (p : Place) (n : nat), In (p, n) marking ->
                                         In (p, n - pre_sum sitpn p fired) transient_marking.
  Proof.
    intros sitpn s s' time_value env;
      induction fired;
      intros marking Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
             Hperm_m Hincl_fired Hnodup_fired.

    (* BASE CASE, fired = [] *)
    - simpl; exists marking; split;
        [ reflexivity | intros p n Hin; rewrite <- minus_n_O; assumption ].

    (* INDUCTION CASE, a :: fired *)
    - simpl.
      unfold update_marking_pre.

      (* Specializes update_marking_pre_aux_complete *)

      assert (Hin_a_transs : In a (transs sitpn)).
      {
        admit.
      }

      assert (Hnodup_prepl : NoDup (pre_pl (lneighbours sitpn a))).
      {
        admit.
      }

      specialize (update_marking_pre_aux_complete
                    (pre_pl (lneighbours sitpn a)) sitpn a marking
                    Hwell_def_sitpn Hin_a_transs Hperm_m
                    (IsDecListCons_refl (pre_pl (lneighbours sitpn a)))
                    Hnodup_prepl)
        as Hex_up_mark_pre.
      
  Admitted.
  
End MapUpdateMarkingPreComplete.
