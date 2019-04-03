(* Import Spn's types, program and specification. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Spn.SpnAnimator.
Require Import Hilecop.Spn.SpnSemantics.

(* Import useful tactics and general-purpose lemmas. *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Spn.SpnTactics.

(* Import core lemmas necessary for Spn's correctness proof. *)

Require Import Hilecop.Spn.SpnCoreLemmas.

(* Import lemmas about spn_map_fire. *)

Require Import Hilecop.Spn.SpnMapFireCorrect.

(* Misc. imports. *)

Require Import Omega.
Require Import Classical_Prop.

(** *** Last part of correctness proof (raising_edge) *)

(** The goal in this part is to prove: 
    spn_cycle spn s = (s', s'') ⇒ SpnSemantics spn s' s'' raising_edge. 
    
    Multiple subproofs :
    
    1. spn_update_marking spn s' = s'' ⇒ IsWelldefinedspnstate s''.
    2. M' = M - ∑ pre(t) + ∑ post(t), forall t ∈ fired s'.
 *)

(** First subproof: spn_update_marking spn s' = s'' ⇒ IsWelldefinedspnstate s''. *)

Section SpnUpdateMarkingWellDefinedState.

  Lemma update_marking_pre_aux_same_marking :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (m' : list (Place * nat)),
      update_marking_pre_aux spn m t pre_places = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros spn m t pre_places;
      functional induction (update_marking_pre_aux spn m t pre_places)
                 using update_marking_pre_aux_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply modify_m_same_struct in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma update_marking_pre_same_marking :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (m' : list (Place * nat)),
      update_marking_pre spn m t = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros spn m t;
      functional induction (update_marking_pre spn m t) using update_marking_pre_ind;
      intros m' Hfun.
    (* GENERAL CASE *)
    - apply update_marking_pre_aux_same_marking in Hfun; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma map_update_marking_pre_same_marking :
    forall (spn : Spn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      map_update_marking_pre spn m fired = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros spn m fired;
      functional induction (map_update_marking_pre spn m fired) using map_update_marking_pre_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply update_marking_pre_same_marking in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma update_marking_post_aux_same_marking :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (post_places : list Place)
           (m' : list (Place * nat)),
      update_marking_post_aux spn m t post_places = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros spn m t post_places;
      functional induction (update_marking_post_aux spn m t post_places)
                 using update_marking_post_aux_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply modify_m_same_struct in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma update_marking_post_same_marking :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (m' : list (Place * nat)),
      update_marking_post spn m t = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros spn m t;
      functional induction (update_marking_post spn m t) using update_marking_post_ind;
      intros m' Hfun.
    (* GENERAL CASE *)
    - apply update_marking_post_aux_same_marking in Hfun; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma map_update_marking_post_same_marking :
    forall (spn : Spn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      map_update_marking_post spn m fired = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros spn m fired;
      functional induction (map_update_marking_post spn m fired) using map_update_marking_post_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply update_marking_post_same_marking in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma spn_update_marking_well_defined :
    forall (spn : Spn) (s : SpnState) (s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      spn_update_marking spn s = Some s' ->
      IsWellDefinedSpnState spn s'.
  Proof.
    intros spn s;
      functional induction (spn_update_marking  spn s) using spn_update_marking_ind;
      intros s' Hwell_def_spn Hwell_def_s Hfun.
    (* GENERAL CASE *)
    - unfold IsWellDefinedSpnState.
      split.
      (* Proves that marking s' structure = initial. *)
      + (* First we need Markinghavesamestruct (marking s) m'
         from map_update_marking_pre_same_marking. *)
        apply map_update_marking_pre_same_marking in e.
        (* Then, we need Markinghavesamestruct m' m'' 
       from map_update_marking_post_same_marking. *)
        apply map_update_marking_post_same_marking in e0.
        (* Then, the goal is deduced. *)
        injection Hfun as Heq_ss; rewrite <- Heq_ss; simpl.
        explode_well_defined_spn_state.
        unfold MarkingHaveSameStruct in *.
        rewrite Hsame_marking_state_spn.
        transitivity (fst (split m')); [assumption | assumption].
      + unfold IsWellDefinedSpnState in Hwell_def_s.
        apply proj2 in Hwell_def_s.
        injection Hfun as Heq_ss; rewrite <- Heq_ss; simpl; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

End SpnUpdateMarkingWellDefinedState.

(** Second subproof: M' = M - ∑ pre(t) + ∑ post(t), forall t ∈ fired s'. *)

Section SpnUpdateMarkingPrePost.

  (** Needed to prove update_marking_pre_aux_correct. *)

  Lemma update_marking_pre_aux_not_in_pre_places :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (m' : list (Place * nat)),
      update_marking_pre_aux spn m t pre_places = Some m' ->
      forall (p : Place),
        ~In p pre_places ->
        forall (n : nat), In (p, n) m <-> In (p, n) m'.
  Proof.
    intros spn m t pre_places;
      functional induction (update_marking_pre_aux spn m t pre_places)
                 using update_marking_pre_aux_ind;
      intros fm Hfun p' Hnot_in_pre n.
    (* BASE CASE *)
    - injection Hfun as Hfun.
      rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply not_in_cons in Hnot_in_pre.
      elim Hnot_in_pre; intros Hdiff_pp' Hnot_in_tl.
      apply not_eq_sym in Hdiff_pp'.
      specialize (modify_m_in_if_diff
                    marking p Nat.sub (pre spn t p) m'
                    e0 p' n Hdiff_pp') as Hequiv.
      rewrite Hequiv.
      apply (IHo fm Hfun p' Hnot_in_tl n).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Correctness proof for [update_marking_pre_aux].
    Express the structure of the returned [m'] regarding the structure
    of [m]. 

    Needed to prove update_marking_pre_correct. *)

  Lemma update_marking_pre_aux_correct :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (neigh_of_t : Neighbours)
           (m' : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split m)) ->
      In (t , neigh_of_t) (lneighbours spn) ->
      NoDup pre_places ->
      incl pre_places (pre_pl neigh_of_t) ->
      update_marking_pre_aux spn m t pre_places = Some m' ->
      forall (p : Place) (n : nat),
        In p pre_places ->
        In (p, n) m ->
        In (p, n - (pre spn t p)) m'.
  Proof.
    intros spn m t pre_places;
      functional induction (update_marking_pre_aux spn m t pre_places)
                 using update_marking_pre_aux_ind;
      intros neigh_of_t fm Hwell_def_spn Hnodup_m
             Hin_lneigh Hnodup_pre_pl Hincl_pre_pl Hfun p' n Hin_pre_pl Hin_resid.
    (* BASE CASE, pre_places = []. *)
    - inversion Hin_pre_pl.
    (* GENERAL CASE *)
    - inversion Hin_pre_pl as [Heq_pp' | Hin_p'_tail].
      (* First subcase, p = p'. *)
      + rewrite <- Heq_pp' in Hin_pre_pl.
        rewrite <- Heq_pp' in Hin_resid.
        specialize (modify_m_correct
                      marking p Nat.sub (pre spn t p) m'
                      Hnodup_m e0 n Hin_resid) as Hin_resid'.
        apply NoDup_cons_iff in Hnodup_pre_pl.
        elim Hnodup_pre_pl; intros Hnot_in_tl Hnodup_tl.
        rewrite Heq_pp' in Hnot_in_tl.
        specialize (update_marking_pre_aux_not_in_pre_places
                      spn m' t tail fm
                      Hfun p' Hnot_in_tl (n - pre spn t p)) as Hin_equiv'.
        rewrite Heq_pp' in Hin_resid'.
        rewrite Heq_pp' in Hin_equiv'.
        rewrite Hin_equiv' in Hin_resid'; assumption.
      (* Second subcase, In p' tail, then apply induction hypothesis. *)
      (* But we need to show NoDup (fst (split residual')) first. *)
      + specialize (modify_m_same_struct
                      marking m' p Nat.sub  (pre spn t p) e0)
          as Hsame_struct.
        unfold MarkingHaveSameStruct in Hsame_struct.
        rewrite Hsame_struct in Hnodup_m.
        (* Builds the other hypotheses, needed to specialize IHo. *)
        apply NoDup_cons_iff in Hnodup_pre_pl;
          elim Hnodup_pre_pl;
          intros Hnot_in_tl Hnodup_tl.
        apply incl_cons_inv in Hincl_pre_pl.        
        (* Then specializes the induction hypothesis. *)
        specialize (IHo neigh_of_t fm Hwell_def_spn Hnodup_m
                        Hin_lneigh Hnodup_tl Hincl_pre_pl Hfun
                        p' n Hin_p'_tail) as Himpl.
        specialize (not_in_in_diff p p' tail (conj Hnot_in_tl Hin_p'_tail))
          as Hdiff_pp.
        specialize (modify_m_in_if_diff
                      marking p Nat.sub (pre spn t p)
                      m' e0 p' n Hdiff_pp) as Hequiv'.
        rewrite <- Hequiv' in Himpl.
        apply (Himpl Hin_resid).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Correctness proof for [update_marking_pre]. 

      Needed to prove GENERAL CASE in spn_fire_aux_sens_by_residual. *)
  Lemma update_marking_pre_correct :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (final_marking : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split marking)) ->
      update_marking_pre spn marking t = Some final_marking ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> In (p, n - (pre spn t p)) final_marking.
  Proof.
    intros spn marking t;
      functional induction (update_marking_pre spn marking t)
                 using update_marking_pre_ind;
      intros final_marking Hwell_def_spn Hnodup_resm Hfun p n Hin_resm.
    (* GENERAL CASE *)
    - (* Two cases, either p ∈ (pre_pl neigh_of_t), or
       p ∉ (pre_pl neigh_of_t). *)
      assert (Hvee_in_pre_pl := classic (In p (pre_pl neighbours_of_t))).
      inversion_clear Hvee_in_pre_pl as [Hin_p_pre | Hnotin_p_pre];
        specialize (get_neighbours_correct (lneighbours spn) t neighbours_of_t e) as Hin_lneigh.
      (* First case, p ∈ pre_pl, then applies update_marking_pre_aux_correct. *)
      + explode_well_defined_spn.
        (* Builds NoDup pre_pl. *)
        assert (Hin_flat : In p (flatten_neighbours neighbours_of_t))
          by (unfold flatten_neighbours; apply in_or_app; left; assumption).      
        unfold NoDupInNeighbours in Hnodup_neigh.
        specialize (Hnodup_neigh t neighbours_of_t Hin_lneigh) as Hnodup_flat.
        unfold flatten_neighbours in Hnodup_flat;
          apply nodup_app in Hnodup_flat; apply proj1 in Hnodup_flat.
        (* Then, applies update_marking_pre_aux_correct. *)
        apply (update_marking_pre_aux_correct
                 spn marking t (pre_pl neighbours_of_t) neighbours_of_t final_marking
                 Hwell_def_spn Hnodup_resm Hin_lneigh Hnodup_flat
                 (incl_refl (pre_pl neighbours_of_t)) Hfun p n Hin_p_pre Hin_resm).
      (* Second case, p ∉ pre_pl, then applies 
       update_marking_pre_aux_not_in_pre_places. *)
      + explode_well_defined_spn.
        unfold AreWellDefinedPreEdges in Hwell_def_pre.
        specialize (Hwell_def_pre t neighbours_of_t p Hin_lneigh) as Hw_pre_edges.
        apply proj2 in Hw_pre_edges; specialize (Hw_pre_edges Hnotin_p_pre).
        rewrite Hw_pre_edges; rewrite Nat.sub_0_r.
        specialize (update_marking_pre_aux_not_in_pre_places
                      spn marking t (pre_pl neighbours_of_t) final_marking
                      Hfun p Hnotin_p_pre n) as Hequiv.
        rewrite <- Hequiv; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma map_update_marking_pre_sub_pre :
    forall (spn : Spn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split m)) ->
      map_update_marking_pre spn m fired = Some m' ->
      forall (p : Place) (n : nat),
        In (p, n) m -> In (p, n - pre_sum spn p fired) m'.
  Proof.
    intros spn m fired;
      functional induction (map_update_marking_pre spn m fired) using map_update_marking_pre_ind;
      intros fm Hwell_def_spn Hnodup_m Hfun p n Hin_m.
    (* BASE CASE *)
    - injection Hfun as Heq_marking; rewrite <- Heq_marking.
      simpl; rewrite Nat.sub_0_r; assumption.
    (* GENERAL CASE *)
    - simpl. 
      rewrite Nat.sub_add_distr.
      specialize (update_marking_pre_correct
                    spn marking t m' Hwell_def_spn Hnodup_m e0 p n Hin_m) as Hin_m'.
      apply update_marking_pre_same_marking in e0;
        unfold MarkingHaveSameStruct in e0;
        rewrite e0 in Hnodup_m.
      apply (IHo fm Hwell_def_spn Hnodup_m Hfun p (n - pre spn t p) Hin_m').
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Needed to prove update_marking_post_aux_correct. *)

  Lemma update_marking_post_aux_not_in_post_places :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (post_places : list Place)
           (m' : list (Place * nat)),
      update_marking_post_aux spn m t post_places = Some m' ->
      forall (p : Place),
        ~In p post_places ->
        forall (n : nat), In (p, n) m <-> In (p, n) m'.
  Proof.
    intros spn m t post_places;
      functional induction (update_marking_post_aux spn m t post_places)
                 using update_marking_post_aux_ind;
      intros fm Hfun p' Hnot_in_post n.
    (* BASE CASE *)
    - injection Hfun as Hfun.
      rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply not_in_cons in Hnot_in_post.
      elim Hnot_in_post; intros Hdiff_pp' Hnot_in_tl.
      apply not_eq_sym in Hdiff_pp'.
      specialize (modify_m_in_if_diff
                    marking p Nat.add (post spn t p) m'
                    e0 p' n Hdiff_pp') as Hequiv.
      rewrite Hequiv.
      apply (IHo fm Hfun p' Hnot_in_tl n).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Correctness proof for [update_marking_post_aux].
    Express the structure of the returned [m'] regarding the structure
    of [m]. 

    Needed to prove update_marking_post_correct. *)

  Lemma update_marking_post_aux_correct :
    forall (spn : Spn)
           (m : list (Place * nat))
           (t : Trans)
           (post_places : list Place)
           (neigh_of_t : Neighbours)
           (m' : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split m)) ->
      In (t , neigh_of_t) (lneighbours spn) ->
      NoDup post_places ->
      incl post_places (post_pl neigh_of_t) ->
      update_marking_post_aux spn m t post_places = Some m' ->
      forall (p : Place) (n : nat),
        In p post_places ->
        In (p, n) m ->
        In (p, n + (post spn t p)) m'.
  Proof.
    intros spn m t post_places;
      functional induction (update_marking_post_aux spn m t post_places)
                 using update_marking_post_aux_ind;
      intros neigh_of_t fm Hwell_def_spn Hnodup_m
             Hin_lneigh Hnodup_post_pl Hincl_post_pl Hfun p' n Hin_post_pl Hin_resid.
    (* BASE CASE, post_places = []. *)
    - inversion Hin_post_pl.
    (* GENERAL CASE *)
    - inversion Hin_post_pl as [Heq_pp' | Hin_p'_tail].
      (* First subcase, p = p'. *)
      + rewrite <- Heq_pp' in Hin_post_pl.
        rewrite <- Heq_pp' in Hin_resid.
        specialize (modify_m_correct
                      marking p Nat.add (post spn t p) m'
                      Hnodup_m e0 n Hin_resid) as Hin_resid'.
        apply NoDup_cons_iff in Hnodup_post_pl.
        elim Hnodup_post_pl; intros Hnot_in_tl Hnodup_tl.
        rewrite Heq_pp' in Hnot_in_tl.
        specialize (update_marking_post_aux_not_in_post_places
                      spn m' t tail fm
                      Hfun p' Hnot_in_tl (n + post spn t p)) as Hin_equiv'.
        rewrite Heq_pp' in Hin_resid'.
        rewrite Heq_pp' in Hin_equiv'.
        rewrite Hin_equiv' in Hin_resid'; assumption.
      (* Second subcase, In p' tail, then apply induction hypothesis. *)
      (* But we need to show NoDup (fst (split residual')) first. *)
      + specialize (modify_m_same_struct
                      marking m' p Nat.add (post spn t p) e0)
          as Hsame_struct.
        unfold MarkingHaveSameStruct in Hsame_struct.
        rewrite Hsame_struct in Hnodup_m.
        (* Builds the other hypotheses, needed to specialize IHo. *)
        apply NoDup_cons_iff in Hnodup_post_pl;
          elim Hnodup_post_pl;
          intros Hnot_in_tl Hnodup_tl.
        apply incl_cons_inv in Hincl_post_pl.        
        (* Then specializes the induction hypothesis. *)
        specialize (IHo neigh_of_t fm Hwell_def_spn Hnodup_m
                        Hin_lneigh Hnodup_tl Hincl_post_pl Hfun
                        p' n Hin_p'_tail) as Himpl.
        specialize (not_in_in_diff p p' tail (conj Hnot_in_tl Hin_p'_tail))
          as Hdiff_pp.
        specialize (modify_m_in_if_diff
                      marking p Nat.add (post spn t p)
                      m' e0 p' n Hdiff_pp) as Hequiv'.
        rewrite <- Hequiv' in Himpl.
        apply (Himpl Hin_resid).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Correctness proof for [update_marking_post]. 

      Needed to prove GENERAL CASE in spn_fire_aux_sens_by_residual. *)
  Lemma update_marking_post_correct :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (final_marking : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split marking)) ->
      update_marking_post spn marking t = Some final_marking ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> In (p, n + (post spn t p)) final_marking.
  Proof.
    intros spn marking t;
      functional induction (update_marking_post spn marking t)
                 using update_marking_post_ind;
      intros final_marking Hwell_def_spn Hnodup_resm Hfun p n Hin_resm.
    (* GENERAL CASE *)
    - (* Two cases, either p ∈ (post_pl neigh_of_t), or
       p ∉ (post_pl neigh_of_t). *)
      assert (Hvee_in_post_pl := classic (In p (post_pl neighbours_of_t))).
      inversion_clear Hvee_in_post_pl as [Hin_p_post | Hnotin_p_post];
        specialize (get_neighbours_correct (lneighbours spn) t neighbours_of_t e) as Hin_lneigh.
      (* First case, p ∈ post_pl, then applies update_marking_post_aux_correct. *)
      + explode_well_defined_spn.
        (* Builds NoDup post_pl. *)
        assert (Hin_flat : In p (flatten_neighbours neighbours_of_t))
          by (unfold flatten_neighbours; do 3 (apply in_or_app; right); assumption).
        unfold NoDupInNeighbours in Hnodup_neigh.
        specialize (Hnodup_neigh t neighbours_of_t Hin_lneigh) as Hnodup_flat.
        unfold flatten_neighbours in Hnodup_flat;
          do 3 (apply nodup_app in Hnodup_flat; apply proj2 in Hnodup_flat).
        (* Then, applies update_marking_post_aux_correct. *)
        apply (update_marking_post_aux_correct
                 spn marking t (post_pl neighbours_of_t) neighbours_of_t final_marking
                 Hwell_def_spn Hnodup_resm Hin_lneigh Hnodup_flat
                 (incl_refl (post_pl neighbours_of_t)) Hfun p n Hin_p_post Hin_resm).
      (* Second case, p ∉ post_pl, then applies 
       update_marking_post_aux_not_in_post_places. *)
      + explode_well_defined_spn.
        unfold AreWellDefinedPostEdges in Hwell_def_post.
        specialize (Hwell_def_post t neighbours_of_t p Hin_lneigh) as Hw_post_edges.
        apply proj2 in Hw_post_edges; specialize (Hw_post_edges Hnotin_p_post).
        rewrite Hw_post_edges; rewrite Nat.add_0_r.
        specialize (update_marking_post_aux_not_in_post_places
                      spn marking t (post_pl neighbours_of_t) final_marking
                      Hfun p Hnotin_p_post n) as Hequiv.
        rewrite <- Hequiv; assumption.
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma map_update_marking_post_add_post :
    forall (spn : Spn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      IsWellDefinedSpn spn ->
      NoDup (fst (split m)) ->
      map_update_marking_post spn m fired = Some m' ->
      forall (p : Place) (n : nat),
        In (p, n) m -> In (p, n + post_sum spn p fired) m'.
  Proof.
    intros spn m fired;
      functional induction (map_update_marking_post spn m fired) using map_update_marking_post_ind;
      intros fm Hwell_def_spn Hnodup_m Hfun p n Hin_m.
    (* BASE CASE *)
    - injection Hfun as Heq_marking; rewrite <- Heq_marking.
      simpl; rewrite Nat.add_0_r; assumption.
    (* GENERAL CASE *)
    - simpl.
      rewrite Nat.add_assoc.
      specialize (update_marking_post_correct
                    spn marking t m' Hwell_def_spn Hnodup_m e0 p n Hin_m) as Hin_m'.
      apply update_marking_post_same_marking in e0;
        unfold MarkingHaveSameStruct in e0;
        rewrite e0 in Hnodup_m.
      apply (IHo fm Hwell_def_spn Hnodup_m Hfun p (n + post spn t p) Hin_m').
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma spn_update_marking_sub_pre_add_post :
    forall (spn : Spn)
           (s : SpnState)
           (s' : SpnState),
      IsWellDefinedSpn spn ->
      IsWellDefinedSpnState spn s ->
      spn_update_marking spn s = Some s' ->
      (forall (p : Place)
              (n : nat),
          In (p, n) s.(marking) ->
          In (p, n - (pre_sum spn p s.(fired)) + (post_sum spn p s.(fired))) s'.(marking)).
  Proof.
    intros spn s;
      functional induction (spn_update_marking spn s) using spn_update_marking_ind;
      intros s' Hwell_def_spn Hwell_def_s Hfun p n Hin_ms.
    (* GENERAL CASE *)
    - (* We need ∀ (p, n) ∈ (marking s) ⇒ (p, n - presum) ∈ m'. 
       map_update_marking_pre_sub_pre gives it. *)

      (* Builds NoDup (fst (split (marking s)) 
         to apply map_update_marking_pre_sub_pre *)
      explode_well_defined_spn; explode_well_defined_spn_state.
      unfold NoUnmarkedPlace in *.
      unfold NoDupPlaces in *.
      assert (Hnodup_ms := Hnodup_places).
      rewrite Hunm_place in Hnodup_ms.
      rewrite Hsame_marking_state_spn in Hnodup_ms.
      
      (* Specializes map_update_marking_pre_sub_pre. *)
      specialize (map_update_marking_pre_sub_pre
                    spn (marking s) (fired s) m'
                    Hwell_def_spn Hnodup_ms e p n Hin_ms)
        as Hin_mp.

      (* Builds NoDup (fst (split m') to specialize 
         map_update_marking_post_add_post *)
      specialize (map_update_marking_pre_same_marking
                    spn (marking s) (fired s) m' e)
        as Hsame_struct_mm'.
      rewrite Hsame_struct_mm' in Hnodup_ms.

      (* Specializes map_update_marking_post_add_post. *)
      specialize (map_update_marking_post_add_post
                    spn m' (fired s) m''
                    Hwell_def_spn Hnodup_ms e0 p
                    (n - pre_sum spn p (fired s)) Hin_mp)
        as Hin_msec.
      (* Rewrite (marking s') then assumption. *)
      injection Hfun as Hfun.
      rewrite <- Hfun; simpl; assumption.
      
    (* ERROR CASE *)
    - inversion Hfun.

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

End SpnUpdateMarkingPrePost.
