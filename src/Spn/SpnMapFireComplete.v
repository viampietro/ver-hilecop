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
    (* ∀ t ∈ firable(s'), (∀ t', t' ≻ t ⇒ t' ∉ firable(s')) ⇒ t ∈ Fired' 
       If all transitions with a higher firing priority than t are not firable,
       then t is fired. *)
    (forall (pgroup : list Trans) (t : Trans),
        In pgroup pgroups ->
        In t pgroup ->
        SpnIsFirable spn s t ->
        (forall (t' : Trans),
            In t' pgroup ->
            HasHigherPriority spn t' t pgroup ->
            ~SpnIsFirable spn s t') ->
        In t final_fired) ->
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
           Hnot_fira_succ Hsens_by_res Hnot_sens_by_res
           Hwell_def_spn Hwell_def_s Hincl_pgs Hnodup_f_pgs Hnodup_ff
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
    (* Subcase: all higher priority not firable ⇒ fired. *)
    + intros pgroup' t Hin_pgs_tl Hin_t_pg Hfira Hhas_high.
      apply in_cons with (a := pgroup) in Hin_pgs_tl.
      apply (Hnot_fira_succ pgroup' t Hin_pgs_tl Hin_t_pg Hfira Hhas_high).
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
    (*  *)
    + 
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