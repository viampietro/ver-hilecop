Require Export Hilecop.SITPN.
Require Export Hilecop.STPNAnimator.

(*** ========================== ***)
(*** FIRING ALGORITHM for SITPN ***)
(*** ========================== ***)

(** * Firing algorithm for SITPN *)

Section FireSitpn.

  (** Returns true if transition t is firable according
      to "SITPN standards", meaning that t is sensitized,
      its time counter value is in the firable interval, and
      its condition value equals true.
    
      Raises an error (None value) if [stpn_is_firable] or 
      [get_condition] returns None. *)
  
  Definition sitpn_is_firable
             (t : trans_type)
             (neighbours_t : neighbours_type)
             (pre test inhib: weight_type)
             (steadym decreasingm : marking_type)
             (chronos : list (trans_type * option chrono_type))
             (lconditions : list (trans_type * option condition_type))
             (time_value : nat) :
    option bool :=
    match stpn_is_firable t neighbours_t pre test inhib steadym decreasingm chronos with
    (* If t is firable according to "STPN standards", then checks its associated conditions. *)
    | Some b =>
      (* Checks if the condition associated to t is true (if exists). *)
      match get_condition lconditions t with
      | Some opt_cond =>
        Some (b && check_condition opt_cond time_value)
      (* Error case, get_condition failed!!! *)
      | None => None
      end
    (* Error case, stpn_is_firable failed!!! *)
    | None => None
    end.

  Functional Scheme sitpn_is_firable_ind := Induction for sitpn_is_firable Sort Prop.
  
  (** Formal specification : sitpn_is_firable *)
  
  Inductive SitpnIsFirable
            (t : trans_type)
            (neighbours_t : neighbours_type)
            (pre test inhib: weight_type)
            (steadym decreasingm : marking_type)
            (chronos : list (trans_type * option chrono_type))
            (lconditions : list (trans_type * option condition_type))
            (time_value : nat) :
    option bool -> Prop :=
  | SitpnIsFirable_stpn_firable_err :
      StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos None ->
      SitpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value None
  | SitpnIsFirable_get_condition_err :
      forall (b : bool),
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some b) ->
        GetCondition lconditions t None ->
        SitpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value None
  | SitpnIsFirable_cons_true :
      forall (opt_cond : option condition_type),
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some true) ->
        GetCondition lconditions t (Some opt_cond) ->
        CheckCondition opt_cond time_value ->
        SitpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value (Some true)
  | SitpnIsFirable_cons_false :
      forall (opt_cond : option condition_type),
        GetCondition lconditions t (Some opt_cond) ->
        (StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some false) \/
         StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some true) /\
         ~CheckCondition opt_cond time_value) ->
        SitpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value (Some false).
  
  (** Correctness proof : sitpn_is_firable *)

  Theorem sitpn_is_firable_correct :
    forall (t : trans_type)
      (neighbours_t : neighbours_type)
      (pre test inhib: weight_type)
      (steadym decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (optionb : option bool),
      sitpn_is_firable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value = optionb ->
      SitpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value optionb.
  Proof.
    intros t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value.
    functional induction (sitpn_is_firable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value)
               using sitpn_is_firable_ind; intros.
    (* General case, all went well. *)
    - dependent induction optionb.
      dependent induction a.
      + apply SitpnIsFirable_cons_true with (opt_cond); injection H; intros;
          apply andb_prop in H0; elim H0; intros.
        -- rewrite H1 in e.
           apply stpn_is_firable_correct.
           assumption.
        -- apply get_condition_correct; assumption.
        -- apply check_condition_correct; assumption.
      + apply SitpnIsFirable_cons_false with (opt_cond := opt_cond);
          injection H; intros; apply andb_false_iff in H0; elim H0; intros.
        -- apply get_condition_correct; assumption.
        -- apply get_condition_correct; assumption.
        -- rewrite H1 in e; left; apply stpn_is_firable_correct; auto.
        -- dependent induction b.
           ++ right; split; [ apply stpn_is_firable_correct in e; auto
                            | intro; apply check_condition_complete in H2; rewrite H1 in H2; inversion H2; auto ].
           ++ left; apply stpn_is_firable_correct; auto.
      + inversion H.
    (* Error case, get_condition returns None. *)
    - rewrite <- H; apply SitpnIsFirable_get_condition_err with (b := b).
      + apply stpn_is_firable_correct; assumption.
      + apply get_condition_correct; assumption.
    (* Error case, stpn_is_firable returns None. *)
    - rewrite <- H; apply SitpnIsFirable_stpn_firable_err.
      apply stpn_is_firable_correct; assumption.
  Qed.

  (** Completeness proof : sitpn_is_firable *)

  Theorem sitpn_is_firable_compl :
    forall (t : trans_type)
      (neighbours_t : neighbours_type)
      (pre test inhib: weight_type)
      (steadym decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (optionb : option bool),
      SitpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value optionb ->
      sitpn_is_firable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value = optionb.
  Proof.  
    intros t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value optionb H.
    elim H; intros.
    (* Case SitpnIsFirable_stpn_firable_err *)
    - apply stpn_is_firable_compl in H0.
      unfold sitpn_is_firable; rewrite H0; auto.
    (* Case SitpnIsFirable_get_condition_err *)
    - apply stpn_is_firable_compl in H0.
      apply get_condition_compl in H1.
      unfold sitpn_is_firable; rewrite H0; rewrite H1; auto.
    (* Case SitpnIsFirable_cons_true *)
    - apply stpn_is_firable_compl in H0.
      apply get_condition_compl in H1.
      apply check_condition_complete in H2.
      unfold sitpn_is_firable; rewrite H0; rewrite H1; rewrite H2; auto.      
    (* Case SitpnIsFirable_cons_false *)
    - elim H1; intros.
      + apply stpn_is_firable_compl in H2.
        apply get_condition_compl in H0.
        unfold sitpn_is_firable; rewrite H2; rewrite H0.
        match goal with
        | [ |- Some (?a && ?c) = Some ?b ] => generalize (andb_false_l c); intro
        end.
        rewrite H3; reflexivity.
      + assert (H' := (conj (check_condition_complete opt_cond time_value)
                            (check_condition_correct opt_cond time_value))).
        elim H2; intros.
        apply iff_to_and in H'; apply not_iff_compat in H'; apply H' in H4.
        apply not_true_is_false in H4.
        apply stpn_is_firable_compl in H3.
        apply get_condition_compl in H0.
        unfold sitpn_is_firable; rewrite H3; rewrite H0; rewrite H4; auto.
  Qed.

  (** Proves that [sitpn_is_firable] returns no error if :

      - the places in [(pre_pl neighbours_t)], [(inhib_pl neighbours_t)] 
        and [(test_pl neighbours_t)] are referenced in markings [steadym]
        and [decreasingm].
      - [t] is referenced in chronos. 
      - [t] is referenced in lconditions *)
  
  Lemma sitpn_is_firable_no_error :
    forall (t : trans_type)
      (neighbours_t : neighbours_type)
      (pre test inhib : weight_type)
      (steadym decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat),
      In t (fst (split lconditions)) ->
      In t (fst (split chronos)) ->
      incl (pre_pl neighbours_t) (fst (split decreasingm)) ->
      incl (test_pl neighbours_t) (fst (split steadym)) ->
      incl (inhib_pl neighbours_t) (fst (split steadym)) ->
      exists v : bool,
        sitpn_is_firable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value = Some v.
  Proof.
    intros t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value.
    functional induction (sitpn_is_firable t neighbours_t pre test inhib steadym decreasingm
                                           chronos lconditions time_value)
               using sitpn_is_firable_ind; intros.
    (* General case, all went well. *)
    - exists (b && check_condition opt_cond time_value); auto.
    (* Case get_chrono = None, impossible regarding the hypotheses. *)
    - generalize (get_condition_no_error lconditions t H); intros.
      elim H4; intros; rewrite H5 in e0; inversion e0.
    (* Case stpn_is_firable = None, impossible regarding the hypotheses. *)
    - generalize (stpn_is_firable_no_error t neighbours_t pre test inhib steadym decreasingm chronos
                                           H0 H1 H2 H3); intros.
      elim H4; intros; rewrite H5 in e; inversion e.
  Qed.

  
  (** -------------------------------------------------------------------------- *)
  (** -------------------------------------------------------------------------- *)
  
  (** Given 1 priority group of transitions (a list [pgroup]), 
      returns a list of transitions [fired_pre_group] and a marking [decreasingm].
   
      Returns a couple (list of transitions, marking)
      For each sensitized transition of the list,
      the marking of the pre-condition places are updated (the 
      transition is fired). [decreasingm] is then the resulting marking. *)
  
  Fixpoint sitpn_fire_pre_aux
           (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)  
           (steadym : marking_type)
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (lconditions : list (trans_type * option condition_type))
           (time_value : nat)
           (fired_pre_group pgroup : list trans_type) {struct pgroup} :
    option ((list trans_type) * marking_type) :=
    match pgroup with
    | t :: tail =>
      match get_neighbours lneighbours t with
      (* t is referenced in lneighbours. *)
      | Some neighbours_t =>
        match sitpn_is_firable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value with
        (* If t is firable, then updates marking for pre places of t. *)
        | Some true =>
          match update_marking_pre t pre decreasingm (pre_pl neighbours_t) with
          (* Adds t at the end of fired_pre_group, and continues with new marking. *)
          | Some marking' =>
            sitpn_fire_pre_aux lneighbours pre test inhib steadym marking' chronos lconditions time_value
                               (fired_pre_group ++ [t]) tail
          (* Error, something went wrong with update_marking_pre!!! *)
          | None => None
          end
        (* Else t is not firable, then continues without adding it to fired_pre_group. *)
        | Some false =>
          sitpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                             fired_pre_group tail
        (* Error, something went wrong with sitpn_is_firable!!! *)
        | None => None
        end
      (* Error, t is not referenced in lneighbours!!! *)
      | None => None
      end
    | [] => Some (fired_pre_group, decreasingm)
    end.

  Functional Scheme sitpn_fire_pre_aux_ind := Induction for sitpn_fire_pre_aux Sort Prop.
  
  (** Formal specification : sitpn_fire_pre_aux *)

  Inductive SitpnFirePreAux
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type) 
            (steadym : marking_type) 
            (decreasingm : marking_type)
            (chronos : list (trans_type * option chrono_type))
            (lconditions : list (trans_type * option condition_type))
            (time_value : nat)
            (fired_pre_group : list trans_type) :
    list trans_type -> option (list trans_type * marking_type) -> Prop :=
  | SitpnFirePreAux_nil :
      SitpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group []
                      (Some (fired_pre_group, decreasingm))
  (* Case get_neighbours returns an error. *)
  | SitpnFirePreAux_neighbours_err :
      forall (t : trans_type) (pgroup : list trans_type),
        GetNeighbours lneighbours t None ->
        SitpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group (t :: pgroup) None
  (* Case sitpn_is_firable returns an error. *)
  | SitpnFirePreAux_firable_err :
      forall (t : trans_type) (pgroup : list trans_type) (neighbours_t : neighbours_type),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        SitpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value None ->
        SitpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group (t :: pgroup) None
  (* Case sitpn_is_firable returns false. *)
  | SitpnFirePreAux_firable_false :
      forall (t : trans_type)
             (pgroup : list trans_type)
             (neighbours_t : neighbours_type)
             (option_final_couple : option (list trans_type * marking_type)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        SitpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value (Some false) ->
        SitpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group pgroup
                        option_final_couple ->
        SitpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group (t :: pgroup)
                        option_final_couple
  (* Case update_marking_pre returns an error. *)
  | SitpnFirePreAux_update_err :
      forall (t : trans_type)
             (neighbours_t : neighbours_type)
             (pgroup : list trans_type),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        SitpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value (Some true) ->
        UpdateMarkingPre t pre decreasingm (pre_pl neighbours_t) None ->
        SitpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group (t :: pgroup) None
  (* General case, all went well. *)
  | SitpnFirePreAux_cons :
      forall (t : trans_type)
             (neighbours_t : neighbours_type)
             (pgroup : list trans_type)
             (modifiedm : marking_type)
             (option_final_couple : option (list trans_type * marking_type)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        SitpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos lconditions time_value (Some true) ->
        UpdateMarkingPre t pre decreasingm (pre_pl neighbours_t) (Some modifiedm) ->
        SitpnFirePreAux lneighbours pre test inhib steadym modifiedm chronos lconditions time_value (fired_pre_group ++ [t]) pgroup
                        option_final_couple ->
        SitpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group (t :: pgroup)
                        option_final_couple.

  (** Correctness proof : sitpn_fire_pre_aux *)

  Theorem sitpn_fire_pre_aux_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (lconditions : list (trans_type * option condition_type))
           (time_value : nat)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      sitpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                         fired_pre_group pgroup = option_final_couple ->
      SitpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                      fired_pre_group pgroup option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group pgroup.
    functional induction (sitpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                                             fired_pre_group pgroup)
               using sitpn_fire_pre_aux_ind; intros.
    (* Case pgroup = [] *)
    - rewrite <- H; apply SitpnFirePreAux_nil.
    (* General case, all went well. *)
    - apply SitpnFirePreAux_cons with (modifiedm := marking')
                                      (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply sitpn_is_firable_correct; auto.
      + apply update_marking_pre_correct; auto.
      + apply IHo; auto.
    (* Case update_marking_pre error. *)
    - rewrite <- H; apply SitpnFirePreAux_update_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply sitpn_is_firable_correct; auto.
      + apply update_marking_pre_correct; auto.
    (* Case sitpn_is_firable returns false. *)
    - apply SitpnFirePreAux_firable_false with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply sitpn_is_firable_correct; auto.
      + apply IHo; auto.
    (* Case sitpn_is_firable returns an error. *)
    - rewrite <- H; apply SitpnFirePreAux_firable_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply sitpn_is_firable_correct; auto.
    (* Case get_neighbours returns an error. *)
    - rewrite <- H; apply SitpnFirePreAux_neighbours_err.
      apply get_neighbours_correct; auto.
  Qed.

  (** Completeness proof : sitpn_fire_pre_aux *)

  Theorem sitpn_fire_pre_aux_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type) 
      (steadym : marking_type) 
      (decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (fired_pre_group : list trans_type)
      (pgroup : list trans_type)
      (option_final_couple : option (list trans_type * marking_type)),
      SitpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                      fired_pre_group pgroup option_final_couple ->
      sitpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                         fired_pre_group pgroup = option_final_couple.
  Proof.
    intros; elim H; intros.
    (* Case SitpnFirePreAux_nil *)
    - simpl; auto.
    (* Case SitpnFirePreAux_neighbours_err *)
    - simpl; apply get_neighbours_compl in H0; rewrite H0; auto.
    (* Case SitpnFirePreAux_firable_err *)
    - simpl;
        apply get_neighbours_compl in H0; rewrite H0;
          apply sitpn_is_firable_compl in H1; rewrite H1; auto.
    (* Case SitpnFirePreAux_firable_false *)
    - simpl;
        apply get_neighbours_compl in H0; rewrite H0;
          apply sitpn_is_firable_compl in H1; rewrite H1; rewrite H3; auto.
    (* Case SitpnFirePreAux_update_err *)
    - simpl;
        apply get_neighbours_compl in H0; rewrite H0;
          apply sitpn_is_firable_compl in H1; rewrite H1; auto;
            apply update_marking_pre_compl in H2; rewrite H2; auto.
    (* Case SitpnFirePreAux_cons *)
    - simpl;
        apply get_neighbours_compl in H0; rewrite H0;
          apply sitpn_is_firable_compl in H1; rewrite H1; auto;
            apply update_marking_pre_compl in H2; rewrite H2; auto.
  Qed.

  (** Proves that [sitpn_fire_pre_aux] preserves
      the structure of the marking [decreasingm]
      passed as argument.
      
      [sitpn_fire_pre_aux] returns a marking [decreasedm]
      which has the same structure as [decreasingm]. *)
  
  Lemma sitpn_fire_pre_aux_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type) 
      (steadym : marking_type) 
      (decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (fired_pre_group : list trans_type)
      (pgroup : list trans_type)
      (pre_fired_transitions : list trans_type)
      (decreasedm : marking_type),
      sitpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group pgroup =
      Some (pre_fired_transitions, decreasedm) ->
      MarkingHaveSameStruct decreasingm decreasedm.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group pgroup.
    functional induction (sitpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                                             chronos lconditions time_value fired_pre_group pgroup)
               using sitpn_fire_pre_aux_ind;
      intros.
    - injection H; intros.
      rewrite H0.
      unfold MarkingHaveSameStruct; auto.
    - apply IHo in H.
      apply update_marking_pre_same_struct in e3.
      unfold MarkingHaveSameStruct.
      unfold MarkingHaveSameStruct in e3.
      unfold MarkingHaveSameStruct in H.
      rewrite <- H; rewrite e3; auto.
    - inversion H.
    - apply IHo in H; auto.
    - inversion H.
    - inversion H.
  Qed.

  (** If all transitions in [pgroup] are in [lneighbours] then 
      all transitions in [final_fired_pre_group] (returned by [sitpn_fire_pre_aux])
      are in [lneighbours]. *)
  
  Lemma sitpn_fire_pre_aux_final_fired_in_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type) 
      (steadym : marking_type) 
      (decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (fired_pre_group : list trans_type)
      (pgroup : list trans_type)
      (final_fired_pre_group : list trans_type)
      (finalm : marking_type),
      incl pgroup (fst (split lneighbours)) ->
      incl fired_pre_group (fst (split lneighbours)) ->
      sitpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group pgroup =
      Some (final_fired_pre_group, finalm) ->
      incl final_fired_pre_group (fst (split lneighbours)).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group pgroup.
    functional induction (sitpn_fire_pre_aux
                            lneighbours pre test inhib steadym decreasingm
                            chronos lconditions time_value fired_pre_group pgroup)
               using sitpn_fire_pre_aux_ind;
      intros.
    (* Base case, pgroup = []. *)
    - injection H1; intros.
      rewrite <- H4 in H2.
      apply H0 in H2.
      auto.
    (* Case everything went well. *)
    - apply IHo with (final_fired_pre_group := final_fired_pre_group)
                     (finalm := finalm).
      + intros.
        apply (in_cons t) in H3.
        apply H in H3; auto.
      + intros.
        apply in_app_or in H3.
        elim H3; intros.
        -- apply H0 in H4; auto.
        -- apply in_inv in H4.
           elim H4; intros.
           { cut (In a0 (t :: tail)); intros;
               [apply H in H6; auto | rewrite H5; apply in_eq].
           }
           { elim H5. }
      + auto.
      + auto.
    (* Case update_marking_pre returns an error,
     * then contradiction.
     *)
    - inversion H1.
    (* Case sitpn_is_firable = false. *)
    - apply IHo with (final_fired_pre_group := final_fired_pre_group)
                     (finalm := finalm).
      + intros.
        apply (in_cons t) in H3.
        apply H in H3; auto.
      + intros.
        apply H0 in H3.
        auto.
      + auto.
      + auto.
    (* Case sitpn_is_firable returns an error,
     * then contradiction.
     *)
    - inversion H1.
    (* Case get_neighbours returns an error,
     * then contradiction.
     *)
    - inversion H1.
  Qed.
  
  (** If all transitions in [pgroup] are ref in [chronos] then 
      all transitions in [final_fired_pre_group] (returned by [sitpn_fire_pre_aux])
      are ref in [chronos]. *)
  
  Lemma sitpn_fire_pre_aux_final_fired_in_chronos :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type) 
      (steadym : marking_type) 
      (decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (fired_pre_group : list trans_type)
      (pgroup : list trans_type)
      (final_fired_pre_group : list trans_type)
      (finalm : marking_type),
      incl pgroup (fst (split chronos)) ->
      incl fired_pre_group (fst (split chronos)) ->
      sitpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                         fired_pre_group pgroup =
      Some (final_fired_pre_group, finalm) ->
      incl final_fired_pre_group (fst (split chronos)).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group pgroup.
    functional induction (sitpn_fire_pre_aux
                            lneighbours pre test inhib steadym decreasingm
                            chronos lconditions time_value fired_pre_group pgroup)
               using sitpn_fire_pre_aux_ind;
      intros.
    (* Base case, pgroup = []. *)
    - injection H1; intros.
      rewrite <- H4 in H2.
      apply H0 in H2.
      auto.
    (* Case everything went well. *)
    - apply IHo with (final_fired_pre_group := final_fired_pre_group)
                     (finalm := finalm).
      + intros.
        apply (in_cons t) in H3.
        apply H in H3; auto.
      + intros.
        apply in_app_or in H3.
        elim H3; intros.
        -- apply H0 in H4; auto.
        -- apply in_inv in H4.
           elim H4; intros.
           { cut (In a0 (t :: tail)); intros;
               [apply H in H6; auto | rewrite H5; apply in_eq].
           }
           { elim H5. }
      + auto.
      + auto.
    (* Case update_marking_pre returns an error,
     * then contradiction.
     *)
    - inversion H1.
    (* Case sitpn_is_firable = false. *)
    - apply IHo with (final_fired_pre_group := final_fired_pre_group)
                     (finalm := finalm).
      + intros.
        apply (in_cons t) in H3.
        apply H in H3; auto.
      + intros.
        apply H0 in H3.
        auto.
      + auto.
      + auto.
    (* Case sitpn_is_firable returns an error,
     * then contradiction.
     *)
    - inversion H1.
    (* Case get_neighbours returns an error,
     * then contradiction.
     *)
    - inversion H1.
  Qed.
  
  (** [sitpn_fire_pre_aux] returns no error if : 
      
      - all transitions in [pgroup] are referenced in [chronos]   
      - all transitions in [pgroup] are referenced in [lconditions]
      - all transitions in [pgroup] are referenced in [lneighbours]
      - all neighbour places referenced in [lneighbours] are
        referenced in the markings [steadym] and [decreasingm]. *)
  
  Lemma sitpn_fire_pre_aux_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type) 
      (steadym : marking_type) 
      (decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (fired_pre_group : list trans_type)
      (pgroup : list trans_type),
      incl pgroup (fst (split lconditions)) ->
      incl pgroup (fst (split chronos)) ->
      incl pgroup (fst (split lneighbours)) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split decreasingm)) /\
           incl neighbours.(inhib_pl) (fst (split steadym)) /\
           incl neighbours.(test_pl) (fst (split steadym)))) ->
      exists v : (list trans_type * marking_type),
        sitpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group pgroup = Some v.
  Proof.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions time_value fired_pre_group pgroup.
    functional induction (sitpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos
                                             lconditions time_value fired_pre_group pgroup)
               using sitpn_fire_pre_aux_ind;
      intros.
    (* Base case, pgroup = []. *)
    - exists (fired_pre_group, decreasingm); auto.
    (* Case sitpn_is_firable = true. *)
    - apply IHo.
      + intros.
        apply (in_cons t) in H3.
        apply (H a) in H3; auto.
      + intros.
        apply (in_cons t) in H3.
        apply (H0 a) in H3; auto.
      + intros.
        apply (in_cons t) in H3.
        apply (H1 a) in H3; auto.
      + intros.
        apply (H2 t0 neighbours) in H3.
        apply update_marking_pre_same_struct in e3.
        unfold MarkingHaveSameStruct in e3.
        rewrite <- e3; auto.
    (* Case update_marking_pre = None,
     * impossible regarding hypothesis.
     *)
    - assert (H' := in_eq t tail).
      apply get_neighbours_in in e0.
      generalize ((H2 t neighbours_t) e0).
      intros.
      elim H3; intros.
      apply (update_marking_pre_no_error t pre (pre_pl neighbours_t) decreasingm) in H4.
      elim H4; intros.
      rewrite H6 in e3; inversion e3.
    (* Case sitpn_is_firable = false. *)
    - apply IHo; intros.
      + apply (H a (in_cons t a tail H3)).
      + apply (H0 a (in_cons t a tail H3)).
      + apply (H1 a (in_cons t a tail H3)).
      + apply (H2 t0 neighbours H3).
    (* Case sitpn_is_firable = None, 
     * impossible regarding the hypotheses. 
     *)
    - assert (H' := in_eq t tail).
      apply get_neighbours_in in e0.
      generalize (H t H'); intros.
      generalize (H0 t H'); intros.
      generalize (H1 t H'); intros.
      generalize ((H2 t neighbours_t) e0); intros.
      elim H6; intros; clear H6.
      elim H8; intros; clear H8.
      (* Applies sitpn_is_firable_no_error to create a contradiction. *)
      generalize (sitpn_is_firable_no_error
                    t neighbours_t pre test inhib
                    steadym decreasingm chronos lconditions time_value
                    H3 H4 H7 H9 H6); intro.
      elim H8; intros.
      rewrite H10 in e1.
      inversion e1.
    (* Case get_neighbours = None, 
     * impossible regarding the hypotheses.
     *)
    - assert (H' := in_eq t tail).
      apply H1 in H'.
      apply get_neighbours_no_error in H'.
      elim H'; intros.
      rewrite H3 in e0; inversion e0.
  Qed.
  
  (** ----------------------------------------------------------------------- *)
  (** ----------------------------------------------------------------------- *)
  
  (** Wrapper function around sitpn_fire_pre_aux. *)
  
  Definition sitpn_fire_pre
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib : weight_type) 
             (steadym : marking_type) 
             (decreasingm : marking_type)
             (chronos : list (trans_type * option chrono_type))
             (lconditions  : list (trans_type * option condition_type))
             (time_value : nat)
             (pgroup : list trans_type) :
    option (list trans_type * marking_type) :=
    sitpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value [] pgroup.

  Functional Scheme sitpn_fire_pre_ind := Induction for sitpn_fire_pre Sort Prop.

  (** Formal specification : sitpn_fire_pre *)

  Inductive SitpnFirePre
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type) 
            (steadym : marking_type) 
            (decreasingm : marking_type)
            (chronos : list (trans_type * option chrono_type))
            (lconditions  : list (trans_type * option condition_type))
            (time_value : nat)
            (pgroup : list trans_type) : option (list trans_type * marking_type) -> Prop :=
  | SitpnFirePre_cons :
      forall (option_final_couple : option (list trans_type * marking_type)),
        SitpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                        [] pgroup option_final_couple ->
        SitpnFirePre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                     pgroup option_final_couple.

  (** Correctness proof : sitpn_fire_pre *)

  Theorem sitpn_fire_pre_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (lconditions : list (trans_type * option condition_type))
           (time_value : nat)
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      sitpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                     pgroup = option_final_couple ->
      SitpnFirePre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                   pgroup option_final_couple.
  Proof.
    intros; unfold sitpn_fire_pre in H.
    apply SitpnFirePre_cons; apply sitpn_fire_pre_aux_correct in H; auto.
  Qed.

  (** Completeness proof : sitpn_fire_pre *)

  Theorem sitpn_fire_pre_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type) 
      (steadym decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (pgroup : list trans_type)
      (option_final_couple : option (list trans_type * marking_type)),
      SitpnFirePre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                   pgroup option_final_couple ->
      sitpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                     pgroup = option_final_couple.
  Proof.
    intros; elim H; intros.
    unfold sitpn_fire_pre; apply sitpn_fire_pre_aux_compl in H0; auto. 
  Qed.

  (** Proves that [sitpn_fire_pre] preserves
      the structure of the marking [decreasingm]
      passed as argument.
   
      [sitpn_fire_pre] returns a marking [decreasedm]
      which has the same structure as [decreasingm]. *)
  
  Lemma sitpn_fire_pre_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type) 
      (steadym : marking_type) 
      (decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (pgroup : list trans_type)
      (pre_fired_transitions : list trans_type)
      (decreasedm : marking_type),
      sitpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value pgroup =
      Some (pre_fired_transitions, decreasedm) ->
      MarkingHaveSameStruct decreasingm decreasedm.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions time_value pgroup; intros.
    unfold sitpn_fire_pre in H.
    apply sitpn_fire_pre_aux_same_struct in H; auto.
  Qed.

  (** If all transitions in [pgroup] are in [lneighbours] then 
      all transitions in [final_fired_pre_group] (returned by [sitpn_fire_pre])
      are in [lneighbours]. *)
  
  Lemma sitpn_fire_pre_final_fired_in_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type) 
      (steadym : marking_type) 
      (decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (pgroup : list trans_type)
      (final_fired_pre_group : list trans_type)
      (finalm : marking_type),
      incl pgroup (fst (split lneighbours)) ->
      sitpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value pgroup =
      Some (final_fired_pre_group, finalm) ->
      incl final_fired_pre_group (fst (split lneighbours)).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions time_value pgroup.
    functional induction (sitpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value pgroup)
               using sitpn_fire_pre_ind;
      intros.
    (* This hypothesis is needed to apply spn_fire_pre_aux_final_fired_in_lneighbours. 
     * Corresponds to the hypothesis "incl pre_fired_group (fst (split lneighbours))"
     * but in that case, pre_fired_group = [].
     *)
    cut (incl [] (fst (split lneighbours))); intros.
    - generalize (sitpn_fire_pre_aux_final_fired_in_lneighbours
                    lneighbours pre test inhib
                    steadym decreasingm chronos lconditions
                    time_value
                    [] pgroup
                    final_fired_pre_group finalm
                    H H2 H0).
      intros.
      apply H3 in H1.
      auto.
    - unfold incl; intros; elim H2.
  Qed.

  (** If all transitions in [pgroup] are ref in [chronos] then 
      all transitions in [final_fired_pre_group] (returned by [sitpn_fire_pre])
      are ref in [chronos]. *)
  
  Lemma sitpn_fire_pre_final_fired_in_chronos :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type) 
      (steadym : marking_type) 
      (decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (pgroup : list trans_type)
      (final_fired_pre_group : list trans_type)
      (finalm : marking_type),
      incl pgroup (fst (split chronos)) ->
      sitpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value pgroup =
      Some (final_fired_pre_group, finalm) ->
      incl final_fired_pre_group (fst (split chronos)).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions time_value pgroup.
    functional induction (sitpn_fire_pre lneighbours pre test inhib
                                        steadym decreasingm chronos lconditions time_value pgroup)
               using sitpn_fire_pre_ind; intros.
    (* This hypothesis is needed to apply sitpn_fire_pre_aux_final_fired_in_chronos. 
     * Corresponds to the hypothesis "incl pre_fired_group (fst (split chronos))"
     * but in that case, pre_fired_group = [].
     *)
    cut (incl [] (fst (split chronos))); intros.
    - generalize (sitpn_fire_pre_aux_final_fired_in_chronos
                    lneighbours pre test inhib
                    steadym decreasingm chronos
                    lconditions time_value
                    [] pgroup
                    final_fired_pre_group finalm
                    H H2 H0).
      intros.
      apply H3 in H1.
      auto.
    - unfold incl; intros; elim H2.
  Qed.
  
  (** [sitpn_fire_pre] returns no error if : 
      
      - all transitions in [pgroup] are referenced in [lconditions]
      - all transitions in [pgroup] are referenced in [chronos]
      - all transitions in [pgroup] are referenced in [lneighbours]
      - all neighbour places referenced in [lneighbours] are
        referenced in the markings [steadym] and [decreasingm]. *)
  
  Lemma sitpn_fire_pre_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type) 
      (steadym : marking_type) 
      (decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (pgroup : list trans_type),
      incl pgroup (fst (split lconditions)) ->
      incl pgroup (fst (split chronos)) ->
      incl pgroup (fst (split lneighbours)) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split decreasingm)) /\
           incl neighbours.(inhib_pl) (fst (split steadym)) /\
           incl neighbours.(test_pl) (fst (split steadym)))) ->
      exists v : (list trans_type * marking_type),
        sitpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value pgroup = Some v.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos pgroup; intros.
    unfold spn_fire_pre.
    apply sitpn_fire_pre_aux_no_error; [auto | auto | auto | auto].
  Qed.
  
  (** ----------------------------------------------------------------------- *)
  (** ----------------------------------------------------------------------- *)
  
  (** Returns the list of pre-fired transitions and a marking.
   
      Applies [sitpn_fire_pre] over all priority group of transitions. 
      Begins with initial marking; ends with half-fired marking.  *)
  
  Fixpoint sitpn_map_fire_pre_aux
           (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (lconditions : list (trans_type * option condition_type))
           (time_value : nat)
           (pre_fired_transitions : list trans_type)
           (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) :=
    match priority_groups with
    (* Loops over all priority group of transitions (prgroup) and
     * calls sitpn_fire_pre. *)
    | pgroup :: pgroups_tail =>
      match sitpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value pgroup with
      (* If sitpn_fire_pre succeeds, then adds the fired transitions
       * in pre_fired_transitions list. *)
      | Some (pre_fired_trs, decreasedm) =>
        sitpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasedm chronos lconditions time_value
                               (pre_fired_transitions ++ pre_fired_trs) pgroups_tail
      (* Error, sitpn_fire_pre failed!!! *)
      | None => None
      end
    | [] => Some (pre_fired_transitions, decreasingm)
    end.

  Functional Scheme sitpn_map_fire_pre_aux_ind := Induction for sitpn_map_fire_pre_aux Sort Prop.
  
  (** Formal specification : sitpn_map_fire_pre_aux *)
  
  Inductive SitpnMapFirePreAux
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type)
            (steadym decreasingm : marking_type)
            (chronos : list (trans_type * option chrono_type))
            (lconditions : list (trans_type * option condition_type))
            (time_value : nat)
            (pre_fired_transitions : list trans_type) :
    list (list trans_type) -> option (list trans_type * marking_type) -> Prop :=
  | SitpnMapFirePreAux_nil :
      SitpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                         pre_fired_transitions []
                         (Some (pre_fired_transitions, decreasingm))
  | SitpnMapFirePreAux_cons :
      forall (pgroup pre_fired_trs : list trans_type)
             (decreasedm : marking_type)
             (priority_groups : list (list trans_type))
             (option_final_couple : option (list trans_type * marking_type)),
        SitpnFirePre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value pgroup
                     (Some (pre_fired_trs, decreasedm)) ->
        SitpnMapFirePreAux lneighbours pre test inhib steadym decreasedm chronos lconditions time_value
                           (pre_fired_transitions ++ pre_fired_trs)
                           priority_groups
                           option_final_couple ->
        SitpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                           pre_fired_transitions
                           (pgroup :: priority_groups)
                           option_final_couple
  | SitpnMapFirePreAux_err :
      forall (pgroup : list trans_type)
             (priority_groups : list (list trans_type)),
        SitpnFirePre lneighbours pre test inhib steadym decreasingm chronos lconditions time_value pgroup None ->
        SitpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                           pre_fired_transitions
                           (pgroup :: priority_groups) None.

  (** Correctness proof : sitpn_map_fire_pre_aux *)
  
  Theorem sitpn_map_fire_pre_aux_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (lconditions : list (trans_type * option condition_type))
           (time_value : nat)
           (priority_groups : list (list trans_type))
           (pre_fired_transitions : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      sitpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                             pre_fired_transitions priority_groups = option_final_couple ->
      SitpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                         pre_fired_transitions priority_groups option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
           priority_groups
           pre_fired_transitions.
    functional induction (sitpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                                                 chronos
                                                 lconditions
                                                 time_value
                                                 pre_fired_transitions
                                                 priority_groups)
               using sitpn_map_fire_pre_aux_ind; intros.
    (* Case priority_groups = [] *)
    - rewrite <- H; apply SitpnMapFirePreAux_nil.
    (* General case *)
    - apply SitpnMapFirePreAux_cons with (pre_fired_trs := pre_fired_trs)
                                         (decreasedm := decreasedm).
      + apply sitpn_fire_pre_correct; auto.
      + apply IHo; rewrite H; auto.
    (* Case of error *)
    - rewrite <- H; apply SitpnMapFirePreAux_err.
      apply sitpn_fire_pre_correct; auto.
  Qed.

  (** Completeness proof : sitpn_map_fire_pre_aux *)
  
  Theorem sitpn_map_fire_pre_aux_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type)
      (steadym decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (priority_groups : list (list trans_type))
      (pre_fired_transitions : list trans_type)
      (option_final_couple : option (list trans_type * marking_type)),
      SitpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                         pre_fired_transitions priority_groups option_final_couple ->
      sitpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions time_value
                             pre_fired_transitions priority_groups = option_final_couple.
  Proof.
    intros; elim H; intros.
    (* Case SitpnMapFirePreAux_nil *)
    - simpl; auto.
    (* Case SitpnMapFirePreAux_cons *)
    - simpl; apply sitpn_fire_pre_compl in H0; rewrite H0; rewrite H2; auto.
    (* Case SitpnMapFirePreAux_err *)
    - simpl; apply sitpn_fire_pre_compl in H0; rewrite H0; auto.
  Qed.

  (** Proves that [sitpn_map_fire_pre_aux] preserves
      the structure of the marking [decreasingm]
      passed as argument. *)
  
  Lemma sitpn_map_fire_pre_aux_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type)
      (steadym decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (pre_fired_transitions : list trans_type)
      (priority_groups : list (list trans_type))
      (final_pre_fired : list trans_type)
      (intermediatem : marking_type),
      sitpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos
                             lconditions time_value
                             pre_fired_transitions priority_groups =
      Some (final_pre_fired, intermediatem) ->
      MarkingHaveSameStruct decreasingm intermediatem.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions
           time_value pre_fired_transitions priority_groups.
    functional induction (sitpn_map_fire_pre_aux
                            lneighbours pre test inhib steadym decreasingm
                            chronos lconditions time_value pre_fired_transitions priority_groups)
               using sitpn_map_fire_pre_aux_ind;
      intros.
    - injection H; intros.
      rewrite H0.
      unfold MarkingHaveSameStruct; auto.
    - apply IHo in H.
      apply sitpn_fire_pre_same_struct in e0.
      unfold MarkingHaveSameStruct.
      unfold MarkingHaveSameStruct in e0.
      unfold MarkingHaveSameStruct in H.
      rewrite <- H; rewrite e0; auto.
    - inversion H.
  Qed.

  (** If all transitions in [priority_groups] are in [lneighbours]
      then all transitions in [final_pre_fired] (returned by [sitpn_map_fire_pre_aux]) 
      are in [lneighbours]. *)
  
  Lemma sitpn_map_fire_pre_aux_final_fired_in_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type)
      (steadym decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (pre_fired_transitions : list trans_type)
      (priority_groups : list (list trans_type))
      (final_pre_fired : list trans_type)
      (intermediatem : marking_type),
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      incl pre_fired_transitions (fst (split lneighbours)) ->
      sitpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos
                             lconditions time_value pre_fired_transitions priority_groups =
      Some (final_pre_fired, intermediatem) ->
      incl final_pre_fired (fst (split lneighbours)).
  Proof.
    unfold PriorityGroupsAreRefInLneighbours.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions
           time_value pre_fired_transitions priority_groups.
    functional induction (sitpn_map_fire_pre_aux lneighbours pre test inhib
                                                 steadym decreasingm
                                                 chronos
                                                 lconditions
                                                 time_value
                                                 pre_fired_transitions
                                                 priority_groups)
               using sitpn_map_fire_pre_aux_ind;
      intros.
    (* Base case, priority_groups = []. *)
    - injection H1; intros.
      rewrite <- H4 in H2; apply H0 in H2; auto.
    (* Case sitpn_fire_pre returns Some value. *)
    - apply IHo with (final_pre_fired := final_pre_fired)
                     (intermediatem := intermediatem).
      + intros.
        apply (in_cons pgroup) in H3.
        generalize (H pgroup0 H3); intros.
        apply H5 in H4; auto.
      + intros.
        generalize (H pgroup); intros.
        apply in_eq_impl in H4.
        (*  
         * We need to use the lemma saying
         * that all transitions in pre_fired_trs are
         * referenced in lneighbours.
         *)
        generalize (sitpn_fire_pre_final_fired_in_lneighbours
                      lneighbours pre test inhib
                      steadym decreasingm
                      chronos
                      lconditions
                      time_value
                      pgroup
                      pre_fired_trs
                      decreasedm H4 e0).
        intros.
        apply in_app_or in H3; elim H3; intros;
          [apply H0 in H6; auto | apply H5 in H6; auto].
      + auto.
      + auto.
    (* Case sitpn_fire_pre returns an error,
     * then contradiction.
     *)
    - inversion H1.
  Qed.

  (** If all transitions in [priority_groups] are ref in [chronos]
      then all transitions in [final_pre_fired] (returned by [sitpn_map_fire_pre_aux]) 
      are ref in [chronos]. *)
  
  Lemma sitpn_map_fire_pre_aux_final_fired_in_chronos :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type)
      (steadym decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (pre_fired_transitions : list trans_type)
      (priority_groups : list (list trans_type))
      (final_pre_fired : list trans_type)
      (intermediatem : marking_type),
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      incl pre_fired_transitions (fst (split chronos)) ->
      sitpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions
                             time_value pre_fired_transitions priority_groups =
      Some (final_pre_fired, intermediatem) ->
      incl final_pre_fired (fst (split chronos)).
  Proof.
    unfold PriorityGroupsAreRefInChronos.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions
           time_value pre_fired_transitions priority_groups.
    functional induction (sitpn_map_fire_pre_aux lneighbours pre test inhib
                                                steadym decreasingm
                                                chronos
                                                lconditions
                                                time_value
                                                pre_fired_transitions
                                                priority_groups)
               using sitpn_map_fire_pre_aux_ind;
      intros.
    (* Base case, priority_groups = []. *)
    - injection H1; intros.
      rewrite <- H4 in H2; apply H0 in H2; auto.
    (* Case sitpn_fire_pre returns Some value. *)
    - apply IHo with (final_pre_fired := final_pre_fired)
                     (intermediatem := intermediatem).
      + intros.
        apply (in_cons pgroup) in H3.
        generalize (H pgroup0 H3); intros.
        apply H5 in H4; auto.
      + intros.
        generalize (H pgroup); intros.
        apply in_eq_impl in H4.
        (*  
         * We need to use the lemma saying
         * that all transitions in pre_fired_trs are
         * referenced in chronos.
         *)
        generalize (sitpn_fire_pre_final_fired_in_chronos
                      lneighbours pre test inhib
                      steadym decreasingm
                      chronos
                      lconditions
                      time_value
                      pgroup
                      pre_fired_trs
                      decreasedm H4 e0).
        intros.
        apply in_app_or in H3; elim H3; intros;
          [apply H0 in H6; auto | apply H5 in H6; auto].
      + auto.
      + auto.
    (* Case sitpn_fire_pre returns an error,
     * then contradiction.
     *)
    - inversion H1.
  Qed.
  
  (** Proves that [sitpn_map_fire_pre_aux] returns no error if :  
      
      - for all pgroups of transitions in [lconditions],
        transitions are referenced in [chronos]
      - for all pgroups of transitions in [priority_groups],
        transitions are referenced in [chronos]
      - for all pgroups of transitions in [priority_groups],
        transitions are referenced in [lneighbours]
      - neighbours places (of these transitions) are referenced 
        in markings [steadym] and [decreasingm]. *)
  
  Lemma sitpn_map_fire_pre_aux_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type)
      (steadym decreasingm : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (priority_groups : list (list trans_type))
      (pre_fired_transitions : list trans_type),
      PriorityGroupsAreRefInLconditions priority_groups lconditions ->
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split decreasingm)) /\
           incl neighbours.(inhib_pl) (fst (split steadym)) /\
           incl neighbours.(test_pl) (fst (split steadym)))) ->
      exists v : (list trans_type * marking_type),
        sitpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos lconditions
                               time_value pre_fired_transitions priority_groups = Some v.
  Proof.
    unfold PriorityGroupsAreRefInLconditions.
    unfold PriorityGroupsAreRefInChronos.
    unfold PriorityGroupsAreRefInLneighbours.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos lconditions 
           time_value priority_groups pre_fired_transitions.
    functional induction (sitpn_map_fire_pre_aux
                            lneighbours pre test inhib steadym decreasingm chronos lconditions
                            time_value pre_fired_transitions priority_groups)
               using sitpn_map_fire_pre_aux_ind;
      intros.
    (* Base case, priority_groups = []. *)
    - exists (pre_fired_transitions, decreasingm); auto.
    (* Case sitpn_fire_pre = Some v *)
    - apply IHo.
      + intros.
        apply (in_cons pgroup) in H3.
        generalize (H pgroup0 H3); intro; auto.
      + intros.
        apply (in_cons pgroup) in H3.
        generalize (H0 pgroup0 H3); intro; auto.
      + intros.
        apply (in_cons pgroup) in H3.
        generalize (H1 pgroup0 H3); intro; auto.
      + apply sitpn_fire_pre_same_struct in e0.
        unfold MarkingHaveSameStruct in e0.
        rewrite <- e0.
        auto.
    (* Case sitpn_fire_pre = None, impossible regarding the hypotheses. *)
    - assert (H' := in_eq pgroup pgroups_tail).      
      generalize (H pgroup H'); intro.
      generalize (H0 pgroup H'); intro.
      generalize (H1 pgroup H'); intro.
      generalize (sitpn_fire_pre_no_error lneighbours pre test inhib
                                          steadym decreasingm
                                          chronos lconditions time_value pgroup
                                          H3 H4 H5 H2).
      intro; elim H6; intros; rewrite H7 in e0; inversion e0.
  Qed.
  
  (** ------------------------------------------------------------------------ *)
  (** ------------------------------------------------------------------------ *)
  
  (** Wrapper around [sitpn_map_fire_pre_aux] function. 

      Updates the marking [m] by consuming the tokens in pre-condition places. *)
  
  Definition sitpn_map_fire_pre
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib : weight_type)
             (m : marking_type)
             (chronos : list (trans_type * option chrono_type))
             (lconditions : list (trans_type * option condition_type))
             (time_value : nat)
             (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) :=
    sitpn_map_fire_pre_aux lneighbours pre test inhib m m chronos lconditions time_value [] priority_groups.

  Functional Scheme sitpn_map_fire_pre_ind := Induction for sitpn_map_fire_pre Sort Prop.
  
  (** Formal specification : sitpn_map_fire_pre *)
  
  Inductive SitpnMapFirePre
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type)
            (m : marking_type)
            (chronos : list (trans_type * option chrono_type))
            (lconditions : list (trans_type * option condition_type))
            (time_value : nat)
            (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) -> Prop :=
  | SitpnMapFirePre_cons :
      forall (option_final_couple : option (list trans_type * marking_type)),
        SitpnMapFirePreAux lneighbours pre test inhib m m chronos lconditions time_value [] priority_groups
                           option_final_couple ->
        SitpnMapFirePre lneighbours pre test inhib m chronos lconditions time_value priority_groups option_final_couple.

  (** Correctness proof : sitpn_map_fire_pre *)
  
  Theorem sitpn_map_fire_pre_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (lconditions : list (trans_type * option condition_type))
           (time_value : nat)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      sitpn_map_fire_pre lneighbours pre test inhib m chronos lconditions time_value priority_groups = option_final_couple ->
      SitpnMapFirePre lneighbours pre test inhib m chronos lconditions time_value priority_groups option_final_couple.  
  Proof.
    intros lneighbours pre test inhib m chronos lconditions time_value priority_groups option_final_couple H.
    apply SitpnMapFirePre_cons.
    apply sitpn_map_fire_pre_aux_correct.
    auto.
  Qed.

  (** Completeness proof : sitpn_map_fire_pre *)
  
  Theorem sitpn_map_fire_pre_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type)
      (m : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (priority_groups : list (list trans_type))
      (option_final_couple : option (list trans_type * marking_type)),
      SitpnMapFirePre lneighbours pre test inhib m chronos lconditions time_value priority_groups
                      option_final_couple ->
      sitpn_map_fire_pre lneighbours pre test inhib m chronos lconditions time_value priority_groups = option_final_couple.
  Proof.
    intros; elim H; intros.
    unfold sitpn_map_fire_pre.
    apply sitpn_map_fire_pre_aux_compl; auto.
  Qed.

  (** If all transitions in [priority_groups] are in [lneighbours]
      then all transitions in [final_pre_fired] (returned by [sitpn_map_fire_pre]) 
      are in [lneighbours]. *)
  
  Lemma sitpn_map_fire_pre_final_fired_in_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type)
      (m : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (priority_groups : list (list trans_type))
      (final_pre_fired : list trans_type)
      (intermediatem : marking_type),
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      sitpn_map_fire_pre lneighbours pre test inhib m chronos lconditions time_value priority_groups =
      Some (final_pre_fired, intermediatem) ->
      incl final_pre_fired (fst (split lneighbours)).
  Proof.
    unfold PriorityGroupsAreRefInLneighbours.
    unfold incl.
    intros lneighbours pre test inhib m chronos lconditions time_value priority_groups.
    functional induction (sitpn_map_fire_pre lneighbours pre test inhib m chronos lconditions time_value priority_groups)
               using sitpn_map_fire_pre_ind; intros.
    cut (forall t : trans_type, In t [] -> In t (fst (split lneighbours))); intros.
    - generalize (sitpn_map_fire_pre_aux_final_fired_in_lneighbours
                    lneighbours pre test inhib m m chronos lconditions time_value [] priority_groups
                    final_pre_fired intermediatem
                    H H2 H0).
      intros.
      apply H3 in H1; auto.
    - elim H2.
  Qed.

  (** If all transitions in [priority_groups] are ref in [chronos]
      then all transitions in [final_pre_fired] (returned by [sitpn_map_fire_pre]) 
      are ref in [chronos]. *)
  
  Lemma sitpn_map_fire_pre_final_fired_in_chronos :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type)
      (m : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (priority_groups : list (list trans_type))
      (final_pre_fired : list trans_type)
      (intermediatem : marking_type),
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      sitpn_map_fire_pre lneighbours pre test inhib m chronos lconditions time_value priority_groups =
      Some (final_pre_fired, intermediatem) ->
      incl final_pre_fired (fst (split chronos)).
  Proof.
    unfold PriorityGroupsAreRefInChronos.
    unfold incl.
    intros lneighbours pre test inhib m chronos lconditions time_value priority_groups.
    functional induction (sitpn_map_fire_pre lneighbours pre test inhib m chronos lconditions time_value priority_groups)
               using sitpn_map_fire_pre_ind; intros.
    cut (forall t : trans_type, In t [] -> In t (fst (split chronos))); intros.
    - generalize (sitpn_map_fire_pre_aux_final_fired_in_chronos
                    lneighbours pre test inhib m m chronos lconditions time_value [] priority_groups
                    final_pre_fired intermediatem
                    H H2 H0).
      intros.
      apply H3 in H1; auto.
    - elim H2.
  Qed.
  
  (** [sitpn_map_fire_pre] returns no error if for all [pgroup] of transitions in [priority_groups] :
      
      - transitions are referenced in [chronos]
      - transitions are referenced in [lneighbours]
      - neighbours places (of these transitions) are referenced 
        in markings [steadym] and [decreasingm]. *)
  
  Lemma sitpn_map_fire_pre_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type)
      (m : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (priority_groups : list (list trans_type)),
      PriorityGroupsAreRefInLconditions priority_groups lconditions ->
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      exists v : (list trans_type * marking_type),
        sitpn_map_fire_pre lneighbours pre test inhib m chronos lconditions time_value priority_groups = Some v.
  Proof.
    intros lneighbours pre test inhib m chronos lconditions time_value priority_groups.
    unfold sitpn_map_fire_pre; intros.
    apply sitpn_map_fire_pre_aux_no_error; [ auto | auto | auto | auto ].
  Qed.
  
  (** Proves that [sitpn_map_fire_pre] preserves the structure of the marking [m]
      passed in parameter. *)
  
  Lemma sitpn_map_fire_pre_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib : weight_type)
      (m : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (priority_groups : list (list trans_type))
      (final_pre_fired : list trans_type)
      (intermediatem : marking_type),
      sitpn_map_fire_pre lneighbours pre test inhib m chronos lconditions time_value priority_groups =
      Some (final_pre_fired, intermediatem) ->
      MarkingHaveSameStruct m intermediatem.
  Proof.
    intros lneighbours pre test inhib m chronos lconditions time_value priority_groups.
    functional induction (sitpn_map_fire_pre lneighbours pre test inhib m chronos lconditions time_value priority_groups)
               using sitpn_map_fire_pre_ind; intros.
    apply sitpn_map_fire_pre_aux_same_struct in H; auto.
  Qed.

  (** ------------------------------------------------------------------------------- *)
  (** ------------------------------------------------------------------------------- *)
  
  (** Returns a tuplet (fired transitions (at this cycle), final marking, final chronos).
               
      Raises an error (None value) if [sitpn_map_fire_pre], [reset_all_chronos],
      [list_disabled], or [fire_post] return None.            
   
      This function has the same structure has [stpn_fire], except
      that [sitpn_fire] adds some instructions to reset chronos
      between the pre-firing and the post-firing phases. *)
  
  Definition sitpn_fire  
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib post : weight_type)
             (m : marking_type)
             (chronos : list (trans_type * option chrono_type))
             (lconditions : list (trans_type * option condition_type))
             (time_value : nat)
             (transs : list trans_type)
             (priority_groups : list (list trans_type)) :
    option ((list trans_type) * marking_type * (list (trans_type * option chrono_type))) :=
    (* Pre-fires the transitions in priority_groups. *)
    match sitpn_map_fire_pre lneighbours pre test inhib m chronos lconditions time_value priority_groups with
    | Some (pre_fired_transitions, intermediatem) =>
      (* Resets chronos for all pre-fired transitions. *)
      match reset_all_chronos chronos pre_fired_transitions with
      | Some updated_chronos =>
        (* Lists transitions disabled by the pre-firing, and resets their chronos. *)
        match list_disabled lneighbours pre test inhib m transs with
        | Some disabled_transs =>
          match reset_all_chronos updated_chronos disabled_transs with
          | Some final_chronos =>
            (* Post-fires the pre-fired transitions, then returns the final tuplet. *)
            match fire_post lneighbours post intermediatem pre_fired_transitions with
            | Some finalm => Some (pre_fired_transitions, finalm, final_chronos)
            (* Error, fire_post failed!!! *)
            | None => None
            end
          (* Error, reset_all_chronos failed!!! *)
          | None => None
          end
        (* Error, list_disabled failed!!! *)
        | None => None
        end
      (* Error, reset_all_chronos failed!!! *)
      | None => None
      end
    (* Error, sitpn_map_fire_pre failed!!! *)
    | None => None
    end.

  Functional Scheme sitpn_fire_ind := Induction for sitpn_fire Sort Prop.
  
  (** Formal specification : sitpn_fire *)

  Inductive SitpnFire
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib post : weight_type)
            (m : marking_type)
            (chronos : list (trans_type * option chrono_type))
            (lconditions : list (trans_type * option condition_type))
            (time_value : nat)
            (transs : list trans_type)
            (priority_groups : list (list trans_type)) :
    option ((list trans_type) * marking_type * (list (trans_type * option chrono_type))) ->
    Prop :=
  | SitpnFire_fire_pre_err :
      SitpnMapFirePre lneighbours pre test inhib m chronos lconditions time_value priority_groups None ->
      SitpnFire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups None
  | SitpnFire_reset_chronos_err1 :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type),
        SitpnMapFirePre lneighbours pre test inhib m chronos lconditions time_value priority_groups
                        (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions None ->
        SitpnFire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups None
  | SitpnFire_list_disabled_err :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type)
             (updated_chronos : list (trans_type * option chrono_type)),
        SitpnMapFirePre lneighbours pre test inhib m chronos lconditions time_value priority_groups
                        (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions (Some updated_chronos) ->
        ListDisabled lneighbours pre test inhib m transs None -> 
        SitpnFire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups None
  | SitpnFire_reset_chronos_err2 :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type)
             (updated_chronos : list (trans_type * option chrono_type))
             (disabled_transs : list trans_type),
        SitpnMapFirePre lneighbours pre test inhib m chronos lconditions time_value priority_groups
                        (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions (Some updated_chronos) ->
        ListDisabled lneighbours pre test inhib m transs (Some disabled_transs) -> 
        ResetAllChronos updated_chronos disabled_transs None ->
        SitpnFire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups None
  | SitpnFire_fire_post_err :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type)
             (updated_chronos : list (trans_type * option chrono_type))
             (disabled_transs : list trans_type)
             (final_chronos : list (trans_type * option chrono_type)),
        SitpnMapFirePre lneighbours pre test inhib m chronos lconditions time_value priority_groups
                        (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions (Some updated_chronos) ->
        ListDisabled lneighbours pre test inhib m transs (Some disabled_transs) -> 
        ResetAllChronos updated_chronos disabled_transs (Some final_chronos) ->
        FirePost lneighbours post intermediatem pre_fired_transitions None ->
        SitpnFire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups None
  | SitpnFire_cons :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type)
             (updated_chronos : list (trans_type * option chrono_type))
             (disabled_transs : list trans_type)
             (final_chronos : list (trans_type * option chrono_type))
             (finalm : marking_type),
        SitpnMapFirePre lneighbours pre test inhib m chronos lconditions time_value priority_groups
                        (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions (Some updated_chronos) ->
        ListDisabled lneighbours pre test inhib m transs (Some disabled_transs) -> 
        ResetAllChronos updated_chronos disabled_transs (Some final_chronos) ->
        FirePost lneighbours post intermediatem pre_fired_transitions (Some finalm) ->
        SitpnFire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups
                  (Some (pre_fired_transitions, finalm, final_chronos)).

  (** Correctness proof : sitpn_fire *)

  Theorem sitpn_fire_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib post : weight_type)
      (m : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (transs : list trans_type)
      (priority_groups : list (list trans_type))
      (opt_final_tuplet : option ((list trans_type) *
                                  marking_type *
                                  (list (trans_type * option chrono_type)))),
      sitpn_fire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups = opt_final_tuplet ->
      SitpnFire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups opt_final_tuplet.
  Proof.
    intros lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups.
    functional induction (sitpn_fire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups)
               using sitpn_fire_ind; intros.
    (* General case, all went well. *)
    - rewrite <- H; apply SitpnFire_cons with (intermediatem := intermediatem)
                                             (updated_chronos := updated_chronos)
                                             (disabled_transs := disabled_transs).
      + apply sitpn_map_fire_pre_correct in e; auto.
      + apply reset_all_chronos_correct in e1; auto.
      + apply list_disabled_correct in e2; auto.
      + apply reset_all_chronos_correct in e3; auto.
      + apply fire_post_correct in e4; auto.
    (* Error case, fire_post returns None. *)
    - rewrite <- H; apply SitpnFire_fire_post_err with (pre_fired_transitions := pre_fired_transitions)
                                                       (intermediatem := intermediatem)
                                                       (updated_chronos := updated_chronos)
                                                       (disabled_transs := disabled_transs)
                                                       (final_chronos := final_chronos).
      + apply sitpn_map_fire_pre_correct in e; auto.
      + apply reset_all_chronos_correct in e1; auto.
      + apply list_disabled_correct in e2; auto.
      + apply reset_all_chronos_correct in e3; auto.
      + apply fire_post_correct in e4; auto.
    (* Error case, 2nd reset_all_chronos returns None. *)
    - rewrite <- H; apply SitpnFire_reset_chronos_err2 with (pre_fired_transitions := pre_fired_transitions)
                                                            (intermediatem := intermediatem)
                                                            (updated_chronos := updated_chronos)
                                                            (disabled_transs := disabled_transs).
      + apply sitpn_map_fire_pre_correct in e; auto.
      + apply reset_all_chronos_correct in e1; auto.
      + apply list_disabled_correct in e2; auto.
      + apply reset_all_chronos_correct in e3; auto.
    (* Error case, list_disabled returns None. *)
    - rewrite <- H; apply SitpnFire_list_disabled_err with (pre_fired_transitions := pre_fired_transitions)
                                                          (intermediatem := intermediatem)
                                                          (updated_chronos := updated_chronos).
      + apply sitpn_map_fire_pre_correct in e; auto.
      + apply reset_all_chronos_correct in e1; auto.
      + apply list_disabled_correct in e2; auto.
    (* Error case, 1st reset_all_chronos returns None. *)
    - rewrite <- H; apply SitpnFire_reset_chronos_err1 with (pre_fired_transitions := pre_fired_transitions)
                                                           (intermediatem := intermediatem).
      + apply sitpn_map_fire_pre_correct in e; auto.
      + apply reset_all_chronos_correct in e1; auto.
    (* Error case, sitpn_map_fire_pre returns None. *)
    - rewrite <- H; apply SitpnFire_fire_pre_err.
      + apply sitpn_map_fire_pre_correct in e; auto.
  Qed.

  (** Completeness proof : sitpn_fire *)

  Theorem sitpn_fire_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib post : weight_type)
      (m : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (transs : list trans_type)
      (priority_groups : list (list trans_type))
      (opt_final_tuplet : option ((list trans_type) *
                                  marking_type *
                                  (list (trans_type * option chrono_type)))),
      SitpnFire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups opt_final_tuplet ->
      sitpn_fire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups = opt_final_tuplet.
  Proof.
    intros lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups opt_final_tuplet H.
    elim H; intros.
    (* Case SitpnFire_fire_pre_err *)
    - unfold sitpn_fire.
      apply sitpn_map_fire_pre_compl in H0; rewrite H0; auto.
    (* Case SitpnFire_reset_chronos_err1 *)
    - unfold sitpn_fire.
      apply sitpn_map_fire_pre_compl in H0; rewrite H0.
      apply reset_all_chronos_complete in H1; rewrite H1; auto.
    (* Case SitpnFire_list_disabled_err *)
    - unfold sitpn_fire.
      apply sitpn_map_fire_pre_compl in H0; rewrite H0.
      apply reset_all_chronos_complete in H1; rewrite H1.
      apply list_disabled_complete in H2; rewrite H2; auto.
    (* Case SitpnFire_reset_chronos_err2 *)
    - unfold sitpn_fire.
      apply sitpn_map_fire_pre_compl in H0; rewrite H0.
      apply reset_all_chronos_complete in H1; rewrite H1.
      apply list_disabled_complete in H2; rewrite H2.
      apply reset_all_chronos_complete in H3; rewrite H3; auto.
    (* Case SitpnFire_reset_chronos_err2 *)
    - unfold sitpn_fire.
      apply sitpn_map_fire_pre_compl in H0; rewrite H0.
      apply reset_all_chronos_complete in H1; rewrite H1.
      apply list_disabled_complete in H2; rewrite H2.
      apply reset_all_chronos_complete in H3; rewrite H3.
      apply fire_post_compl in H4; rewrite H4; auto.
    (* Case SitpnFire_cons *)
    - unfold sitpn_fire.
      apply sitpn_map_fire_pre_compl in H0; rewrite H0.
      apply reset_all_chronos_complete in H1; rewrite H1.
      apply list_disabled_complete in H2; rewrite H2.
      apply reset_all_chronos_complete in H3; rewrite H3.
      apply fire_post_compl in H4; rewrite H4; auto.      
  Qed.

  (** Proves that [sitpn_fire] preserves the structure of the marking [m]
      passed as argument. *)
  
  Lemma sitpn_fire_same_struct_marking :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib post : weight_type)
      (m : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (transs : list trans_type)
      (priority_groups : list (list trans_type))
      (fired_transitions : list (trans_type))
      (newm : marking_type)
      (new_chronos : list (trans_type * option chrono_type)),
      sitpn_fire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups =
      Some (fired_transitions, newm, new_chronos) ->
      MarkingHaveSameStruct m newm.
  Proof.
    intros lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups.
    functional induction (sitpn_fire lneighbours pre test inhib post m chronos lconditions
                                     time_value transs priority_groups)
               using sitpn_fire_ind;
      intros.
    injection H; intros; rewrite <- H1; auto.
    generalize (sitpn_map_fire_pre_same_struct
                  lneighbours pre test inhib m chronos lconditions time_value priority_groups
                  pre_fired_transitions intermediatem e); intro.
    - generalize (fire_post_same_struct
                    lneighbours post intermediatem
                    pre_fired_transitions finalm e4); intro.
      unfold MarkingHaveSameStruct in H3; unfold MarkingHaveSameStruct in H4.
      unfold MarkingHaveSameStruct.
      transitivity (fst (split intermediatem)); [auto | auto].
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
  Qed.

  (** Proves that sitpn_fire preserves the structure of the [chronos] list. *)
  
  Lemma sitpn_fire_same_struct_chronos :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib post : weight_type)
      (m : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (transs : list trans_type)
      (priority_groups : list (list trans_type))
      (fired_transitions : list (trans_type))
      (newm : marking_type)
      (new_chronos : list (trans_type * option chrono_type)),
      sitpn_fire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups =
      Some (fired_transitions, newm, new_chronos) ->
      ChronosHaveSameStruct chronos new_chronos.
  Proof.
    intros lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups.
    functional induction (sitpn_fire lneighbours pre test inhib post m chronos
                                     lconditions time_value transs priority_groups)
               using sitpn_fire_ind; intros.
    - injection H; intros; rewrite <- H0; auto.
      generalize (reset_all_chronos_same_struct
                    chronos pre_fired_transitions updated_chronos e1); intro.
      generalize (reset_all_chronos_same_struct
                    updated_chronos disabled_transs final_chronos e3); intro.
      unfold ChronosHaveSameStruct in H3; unfold ChronosHaveSameStruct in H4.
      unfold ChronosHaveSameStruct.
      transitivity (fst (split updated_chronos)); [auto | auto].
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
  Qed.
  
  (** If all chrono in [chronos] are well-formed, then [sitpn_fire] 
      returns a list [new_chronos] of well-formed chronos. *)
  
  Lemma sitpn_fire_well_formed_chronos :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib post : weight_type)
      (m : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (transs : list trans_type)
      (priority_groups : list (list trans_type))
      (fired_transitions : list (trans_type))
      (newm : marking_type)
      (new_chronos : list (trans_type * option chrono_type)),
      (forall chrono : chrono_type,
          In (Some chrono) (snd (split chronos)) -> IsWellFormedChrono chrono) ->
      sitpn_fire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups =
      Some (fired_transitions, newm, new_chronos) ->
      (forall chrono' : chrono_type,
          In (Some chrono') (snd (split new_chronos)) -> IsWellFormedChrono chrono').
  Proof.
    intros lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups.
    functional induction (sitpn_fire lneighbours pre test inhib post m chronos lconditions
                                     time_value transs priority_groups)
               using sitpn_fire_ind; intros.
    (* GENERAL CASE (all went well) *)
    (* We need to prove that reset_all_chronos return well-formed chronos. *)
    - generalize (reset_all_chronos_well_formed_chronos chronos pre_fired_transitions updated_chronos H e1); intro.
      generalize (reset_all_chronos_well_formed_chronos updated_chronos disabled_transs final_chronos H2 e3); intro.
      injection H0; intros.
      rewrite <- H4 in H1; apply (H3 chrono' H1).
    (* CASE fire_post returns None, impossible. *)
    - inversion H0.
    (* CASE reset_all_chronos returns None, impossible. *)
    - inversion H0.
    (* CASE list_disabled returns None, impossible. *)
    - inversion H0.
    (* CASE reset_all_chronos returns None, impossible. *)
    - inversion H0.
    (* CASE sitpn_map_fire_pre returns None, impossible. *)
    - inversion H0.      
  Qed.

  (** Proves that [sitpn_fire] returns no error if :
      
      - All transitions in [transs] are ref in [lconditions], [chronos] and [lneighbours].
      - All pgroups in [priority_groups] are ref in [lconditions], [chronos] and [lneighbours].
      - All places in [lneighbours] are ref in [m]. 
   
      Of course, all these hypotheses will finally be comprised 
      in the predicate [IsWellStructuredSitpn]. *)
  
  Lemma sitpn_fire_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
      (pre test inhib post : weight_type)
      (m : marking_type)
      (chronos : list (trans_type * option chrono_type))
      (lconditions : list (trans_type * option condition_type))
      (time_value : nat)
      (transs : list trans_type)
      (priority_groups : list (list trans_type)),
      incl transs (fst (split lconditions)) ->
      incl transs (fst (split chronos)) ->
      incl transs (fst (split lneighbours)) ->
      PriorityGroupsAreRefInLconditions priority_groups lconditions ->
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          incl neighbours.(post_pl) (fst (split m))) ->
      exists v : (list trans_type * marking_type * list (trans_type * option chrono_type)),
        sitpn_fire lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups = Some v.
  Proof.
    unfold incl.
    unfold PriorityGroupsAreRefInLconditions.
    unfold PriorityGroupsAreRefInChronos.
    unfold PriorityGroupsAreRefInLneighbours.
    intros lneighbours pre test inhib post m chronos lconditions time_value transs priority_groups.
    functional induction (sitpn_fire lneighbours pre test inhib post m
                                     chronos lconditions time_value transs priority_groups)
               using sitpn_fire_ind;
      intros.
    (* GENERAL CASE, all functions returned Some value. *)
    - exists (pre_fired_transitions, finalm, final_chronos); auto.
    (* CASE fire_post returns None, 
     * impossible according to the hypotheses.
     *)
    (* First we need the hypothesis saying that
     * all transitions in the list pre_fired_transitions
     * are referenced in lneighbours.
     *)
    - generalize (sitpn_map_fire_pre_final_fired_in_lneighbours
                    lneighbours
                    pre test inhib m chronos
                    lconditions time_value
                    priority_groups
                    pre_fired_transitions intermediatem
                    H4 e); intros.
      (* Then we need transform our hypotheses,  
       * using the fact that first marking and intermediate markings
       * have the same structure.
       *)
      apply sitpn_map_fire_pre_same_struct in e.
      unfold MarkingHaveSameStruct in e.
      rewrite e in H6.
      generalize (fire_post_no_error lneighbours post intermediatem pre_fired_transitions H7 H6).
      intros.
      elim H8; intros.
      rewrite H9 in e4.
      inversion e4.
    (* CASE 2nd call to reset_all_chronos returns None,
     * impossible according to the hypotheses.
     *)
    (*  
     * To deduce (incl disabled_transs (fst (split updated_chronos)))
     * and apply reset_all_chronos_no_error, we need to ensure :
     *
     * - (incl disabled_transs transs), then use incl_tran
     *   to deduce (incl disabled (fst (split chronos))).
     * - ChronosHaveSameStruct chronos updated_chronos,
     *   then rewrite (fst (split chronos) in (fst (split updated_chronos).
     *)
    - generalize (list_disabled_incl_transs
                    lneighbours pre test inhib m transs disabled_transs e2); intros.
      generalize (incl_tran H7 H0); intros.
      generalize (reset_all_chronos_same_struct
                    chronos pre_fired_transitions updated_chronos e1); intros.
      unfold ChronosHaveSameStruct in H9.
      rewrite H9 in H8.
      generalize (reset_all_chronos_no_error
                    updated_chronos disabled_transs H8); intros.
      elim H10; intros; rewrite H11 in e3; inversion e3.
    (* CASE list_disabled returns None,
     * impossible according to the hypotheses.
     *)
    - generalize (list_disabled_no_error
                    lneighbours pre test inhib m transs
                    H1 H5); intros.
      elim H7; intros; rewrite H8 in e2; inversion e2.
    (* CASE 1st reset_all_chronos returns None,
     * impossible according to the hypotheses.
     *)
    (* We need (incl pre_fired_transitions chronos) 
     * in order to apply reset_all_chronos_no_error.
     *)
    - generalize (sitpn_map_fire_pre_final_fired_in_chronos
                    lneighbours pre test inhib m chronos
                    lconditions
                    time_value
                    priority_groups
                    pre_fired_transitions intermediatem
                    H3 e); intros.
      generalize (reset_all_chronos_no_error
                    chronos pre_fired_transitions H7); intros.
      elim H8; intros; rewrite H9 in e1; inversion e1.
    (* CASE sitpn_map_fire_pre returns None,
     * impossible according to the hypotheses.
     *)
    - generalize (sitpn_map_fire_pre_no_error
                    lneighbours pre test inhib m chronos
                    lconditions time_value priority_groups
                    H2 H3 H4 H5); intros.
      elim H7; intros; rewrite H8 in e; inversion e.
  Qed.
  
End FireSitpn.

(*=========================================================*)
(*================= SITPN CYCLE EVOLUTION =================*)
(*=========================================================*)

Section AnimateSitpn.
  
  (** Returns the resulting Petri net after the firing of all the sensitized
      transitions - with right chrono and cond value - in sitpn.
      
      Also returns the list of fired transitions. 
      
      [time_value] represents the number of the current cycle of evolution. *)
  
  Definition sitpn_cycle (sitpn : SITPN) (time_value : nat) : option ((list trans_type) * SITPN)  :=
    match sitpn with
    | mk_SITPN
        lconditions
        (mk_STPN
           chronos
           (mk_SPN places transs pre post test inhib marking priority_groups lneighbours)) =>
      (* Lists all sensitized transitions. *)
      match list_sensitized lneighbours pre test inhib marking transs with
      | Some sensitized_transs =>           
        (* Increments all chronos for the sensitized transitions. *)
        match increment_all_chronos chronos sensitized_transs with
        | Some updated_chronos =>
          match sitpn_fire lneighbours pre test inhib post marking updated_chronos lconditions time_value transs priority_groups with
          | Some (fired_transitions, nextm, next_chronos) =>
            Some (fired_transitions,
                  (mk_SITPN
                     lconditions
                     (mk_STPN
                        next_chronos
                        (mk_SPN places transs pre post test inhib nextm priority_groups lneighbours))))
          (* Error, sitpn_fire failed!!! *)
          | None => None
          end
        (* Error, increment_all_chronos failed!!! *)
        | None => None
        end
      (* Error, list_sensitized failed. *)
      | None => None
      end
    end.

  Functional Scheme sitpn_cycle_ind := Induction for sitpn_cycle Sort Prop.
  
  (** Formal specification : sitpn_cycle *)
  
  Inductive SitpnCycle :
    SITPN -> nat -> option ((list trans_type) * SITPN) -> Prop :=
  | SitpnCycle_list_sensitized_err :
      forall (lconditions : list (trans_type * option condition_type))
        (chronos : list (trans_type * option chrono_type))
        (places : list place_type)
        (transs : list trans_type)
        (pre post test inhib : weight_type)
        (marking : marking_type)
        (priority_groups : list (list trans_type))
        (lneighbours : list (trans_type * neighbours_type))
        (time_value : nat),
        ListSensitized lneighbours pre test inhib marking transs None ->
        SitpnCycle
          (mk_SITPN
             lconditions
             (mk_STPN chronos (mk_SPN places transs pre post test inhib marking priority_groups lneighbours)))
          time_value
          None
  | SitpnCycle_increment_chronos_err :
      forall (lconditions : list (trans_type * option condition_type))
             (chronos : list (trans_type * option chrono_type))
             (places : list place_type)
             (transs : list trans_type)
             (pre post test inhib : weight_type)
             (marking : marking_type)
             (priority_groups : list (list trans_type))
             (lneighbours : list (trans_type * neighbours_type))
             (sensitized_transs : list trans_type)
             (time_value : nat),
        ListSensitized lneighbours pre test inhib marking transs (Some sensitized_transs) ->
        IncrementAllChronos chronos sensitized_transs None ->
        SitpnCycle
          (mk_SITPN
             lconditions
             (mk_STPN chronos (mk_SPN places transs pre post test inhib marking priority_groups lneighbours)))
          time_value
          None
  | SitpnCycle_fire_err :
      forall (lconditions : list (trans_type * option condition_type))
             (chronos : list (trans_type * option chrono_type))
             (places : list place_type)
             (transs : list trans_type)
             (pre post test inhib : weight_type)
             (marking : marking_type)
             (priority_groups : list (list trans_type))
             (lneighbours : list (trans_type * neighbours_type))
             (sensitized_transs : list trans_type)
             (updated_chronos : list (trans_type * option chrono_type))
             (time_value : nat),
        ListSensitized lneighbours pre test inhib marking transs (Some sensitized_transs) ->
        IncrementAllChronos chronos sensitized_transs (Some updated_chronos) ->
        SitpnFire lneighbours pre test inhib post marking updated_chronos lconditions time_value transs priority_groups None -> 
        SitpnCycle
          (mk_SITPN
             lconditions
             (mk_STPN chronos (mk_SPN places transs pre post test inhib marking priority_groups lneighbours)))
          time_value
          None
  | SitpnCycle_cons :
      forall (lconditions : list (trans_type * option condition_type))
             (chronos : list (trans_type * option chrono_type))
             (places : list place_type)
             (transs : list trans_type)
             (pre post test inhib : weight_type)
             (marking : marking_type)
             (priority_groups : list (list trans_type))
             (lneighbours : list (trans_type * neighbours_type))
             (sensitized_transs : list trans_type)
             (updated_chronos : list (trans_type * option chrono_type))
             (fired_transitions : list trans_type)
             (nextm : marking_type)
             (next_chronos : list (trans_type * option chrono_type))
             (time_value : nat),
        ListSensitized lneighbours pre test inhib marking transs (Some sensitized_transs) ->
        IncrementAllChronos chronos sensitized_transs (Some updated_chronos) ->
        SitpnFire lneighbours pre test inhib post marking updated_chronos lconditions time_value transs priority_groups
                  (Some (fired_transitions, nextm, next_chronos)) -> 
        SitpnCycle
          (mk_SITPN
             lconditions
             (mk_STPN chronos (mk_SPN places transs pre post test inhib marking priority_groups lneighbours)))
          time_value
          (Some (fired_transitions,
                 (mk_SITPN
                    lconditions
                    (mk_STPN next_chronos (mk_SPN places transs pre post test inhib nextm priority_groups lneighbours))))).

  (** Correctness proof : sitpn_cycle *)

  Theorem sitpn_cycle_correct :
    forall (sitpn : SITPN)
      (time_value : nat)
      (opt_final_couple : option ((list trans_type) * SITPN)),
      sitpn_cycle sitpn time_value = opt_final_couple ->
      SitpnCycle sitpn time_value opt_final_couple.
  Proof.
    intros sitpn time_value.
    functional induction (sitpn_cycle sitpn time_value) using sitpn_cycle_ind; intros.
    (* General case, all went well. *)
    - rewrite <- H; apply SitpnCycle_cons with (chronos := chronos)
                                              (marking := marking)
                                              (sensitized_transs := sensitized_transs)
                                              (updated_chronos := updated_chronos).
      + apply list_sensitized_correct; auto.
      + apply increment_all_chronos_correct; auto.
      + apply sitpn_fire_correct; auto.
    (* Error case, sitpn_fire returns None. *)
    - rewrite <- H; apply SitpnCycle_fire_err with (places := places)
                                                  (transs := transs)
                                                  (pre := pre)
                                                  (post := post)
                                                  (test := test)
                                                  (inhib := inhib)
                                                  (priority_groups := priority_groups)
                                                  (lneighbours := lneighbours)
                                                  (chronos := chronos)
                                                  (marking := marking)
                                                  (sensitized_transs := sensitized_transs)
                                                  (updated_chronos := updated_chronos).
      + apply list_sensitized_correct; auto.
      + apply increment_all_chronos_correct; auto.
      + apply sitpn_fire_correct; auto.
    (* Error case, increment_all_chronos returns None. *)
    - rewrite <- H; apply SitpnCycle_increment_chronos_err with (places := places)
                                                               (transs := transs)
                                                               (pre := pre)
                                                               (post := post)
                                                               (test := test)
                                                               (inhib := inhib)
                                                               (priority_groups := priority_groups)
                                                               (lneighbours := lneighbours)
                                                               (chronos := chronos)
                                                               (marking := marking)
                                                               (sensitized_transs := sensitized_transs).
      + apply list_sensitized_correct; auto.
      + apply increment_all_chronos_correct; auto.
    (* Error case, list_sensitized returns None. *)
    - rewrite <- H; apply SitpnCycle_list_sensitized_err with (places := places)
                                                             (transs := transs)
                                                             (pre := pre)
                                                             (post := post)
                                                             (test := test)
                                                             (inhib := inhib)
                                                             (priority_groups := priority_groups)
                                                             (lneighbours := lneighbours)
                                                             (chronos := chronos)
                                                             (marking := marking).
      + apply list_sensitized_correct; auto.
  Qed.

  (** Completeness proof : sitpn_cycle *)
  
  Theorem sitpn_cycle_compl :
    forall (sitpn : SITPN)
      (time_value : nat)
      (opt_final_couple : option ((list trans_type) * SITPN)),
      SitpnCycle sitpn time_value opt_final_couple ->
      sitpn_cycle sitpn time_value = opt_final_couple.
  Proof.
    intros; elim H; intros; unfold sitpn_cycle.
    (* Case SitpnCycle_list_sensitized_err *)
    - apply list_sensitized_complete in H0; rewrite H0; auto.
    (* Case SitpnCycle_increment_chronos_err *)
    - apply list_sensitized_complete in H0; rewrite H0;
        apply increment_all_chronos_complete in H1; rewrite H1; auto.
    (* Case SitpnCycle_fire_err *)
    - apply list_sensitized_complete in H0; rewrite H0;
        apply increment_all_chronos_complete in H1; rewrite H1;
          apply sitpn_fire_compl in H2; rewrite H2; auto.
    (* Case SitpnCycle_cons *)
    - apply list_sensitized_complete in H0; rewrite H0;
        apply increment_all_chronos_complete in H1; rewrite H1;
          apply sitpn_fire_compl in H2; rewrite H2; auto.
  Qed.

  (** For all [SITPN] with properties [NoUnknownInPriorityGroups]
      and [NoUnknownTransInLconditions] then transitions
      in [SITPN.(priority_groups)] are referenced in [SITPN.(lconditions)].
          
      Useful to apply [sitpn_fire_no_error] while proving [sitpn_cycle_no_error]. *)
  
  Lemma priority_groups_in_lconditions :
    forall (sitpn : SITPN),
      NoUnknownInPriorityGroups sitpn ->
      NoUnknownTransInLconditions sitpn ->
      PriorityGroupsAreRefInLconditions sitpn.(priority_groups) sitpn.(lconditions).
  Proof.
    unfold NoUnknownInPriorityGroups.
    unfold NoUnknownTransInLconditions.
    unfold PriorityGroupsAreRefInLconditions.
    intros.
    generalize (in_concat t pgroup (priority_groups sitpn) H2 H1); intro.
    rewrite <- H in H3.
    rewrite H0 in H3.
    assumption.
  Qed.

  (** For all [SITPN] verifying the predicate [IsWellStructuredSitpn],
      [sitpn_cycle] returns no error (always returns Some value). *)
  
  Theorem sitpn_cycle_no_error :
    forall (sitpn : SITPN)
      (time_value : nat),
    IsWellStructuredSitpn sitpn ->
    exists v : ((list trans_type) * SITPN),
      sitpn_cycle sitpn time_value = Some v.
  Proof.
    do 2 intro;
    functional induction (sitpn_cycle sitpn time_value) using sitpn_cycle_ind;
    set (sitpn := {| lconditions := lconditions;
                     stpn := {| chronos := chronos;
                                spn := {| places := places;
                                          transs := transs;
                                          pre := pre;
                                          post := post;
                                          test := test;
                                          inhib := inhib;
                                          marking := marking;
                                          priority_groups := priority_groups;
                                          lneighbours := lneighbours |} |} |});
    intros;
    unfold IsWellStructuredSitpn in H; unfold IsWellStructuredStpn in H; unfold IsWellStructuredSpn in H;
    decompose [and] H; clear H.
    (* Case all went well, spn_fire returns Some value. *)
    - exists ((fired_transitions,
          {| lconditions := lconditions;
             stpn := {| chronos := next_chronos;
                        spn := {| places := places;
                                  transs := transs;
                                  pre := pre;
                                  post := post;
                                  test := test;
                                  inhib := inhib;
                                  marking := nextm;
                                  priority_groups := priority_groups;
                                  lneighbours := lneighbours |} |} |})).
      reflexivity.            
    (* CASE sitpn_fire returns None, impossible
     * regarding the hypotheses.
     *)
    - unfold NoUnknownTransInLconditions in H0.
      unfold NoUnknownTransInChronos in H1.
      unfold NoUnknownTransInLNeighbours in H10.
      (* Deduces the hypotheses needed to apply sitpn_fire_no_error 
       * from the properties embedded in IsWellStructuredSitpn.
       *)
      assert (Hlcond : incl (SPN.transs sitpn) (fst (split (SITPN.lconditions sitpn))))
        by (rewrite H0; unfold incl; intros ; auto).
      assert (Hchro : incl (SPN.transs sitpn) (fst (split (STPN.chronos sitpn))))
        by (rewrite H1; unfold incl; intros ; auto).
      assert (Hlnei : incl (SPN.transs sitpn) (fst (split (SPN.lneighbours sitpn))))
        by (rewrite H10; unfold incl; intros ; auto).
      generalize (priority_groups_in_lconditions sitpn H5 H0); intro.
      generalize (priority_groups_in_chronos sitpn H5 H1); intro.
      generalize (priority_groups_in_lneighbours sitpn H5 H10); intro.
      generalize (pre_places_in_marking sitpn H13 H9); intro.
      generalize (post_places_in_marking sitpn H13 H9); intro.
      (* Then, ensures that chronos and updated_chronos have same structure. *)
      generalize (increment_all_chronos_same_struct
                    chronos sensitized_transs updated_chronos e3); intros.
      (* Rewrites chronos with updated_chronos in some hypotheses.  *)
      unfold ChronosHaveSameStruct in H17.
      simpl in Hchro; rewrite H17 in Hchro.
      simpl in H12; unfold PriorityGroupsAreRefInChronos in H12; rewrite H17 in H12.
      (* Finally, applies lemma sitpn_fire_no_error. *)
      generalize (sitpn_fire_no_error
                    lneighbours pre test inhib post marking updated_chronos
                    lconditions time_value transs priority_groups
                    Hlcond Hchro Hlnei H H12 H14 H15 H16).
      intro; elim H18; intros.
      rewrite H19 in e4.
      inversion e4.
    (* CASE increment_all_chronos returns None, impossible
     * regarding the hypotheses. 
     *)
    - unfold NoUnknownTransInChronos in H1.
      generalize (list_sensitized_incl_transs
                    lneighbours pre test inhib marking transs sensitized_transs e2); intro.
      assert (H' : incl (SPN.transs sitpn) (fst (split (STPN.chronos sitpn))))
        by (rewrite H1; unfold incl; intros ; auto).
      generalize (incl_tran H H'); intro.
      generalize (increment_all_chronos_no_error
                    chronos sensitized_transs H12); intro.
      elim H14; intros.
      rewrite H15 in e3; inversion e3.
    (* CASE list_sensitized returns None, impossible
     * regarding the hypotheses. 
     *)
    - unfold NoUnknownTransInLNeighbours in H10.
      assert (H' : incl (SPN.transs sitpn) (fst (split (SPN.lneighbours sitpn))))
        by (rewrite H10; unfold incl; intros ; auto).
      generalize (pre_places_in_marking sitpn H13 H9); intro.
      unfold incl in H.
      generalize (list_sensitized_no_error
                    lneighbours pre test inhib marking transs
                    H' H); intro.
      elim H12; intros; rewrite H14 in e2; inversion e2.
  Qed.
  
  (** For all [sitpn] verifying the property [IsWellStructuredSitpn],
      [sitpn_cycle] returns a new SITPN [next_sitpn] verifying the relation
      [IsWellStructuredSitpn]. *)
  
  Theorem sitpn_cycle_well_structured :
    forall (sitpn : SITPN)
      (time_value : nat)
      (fired_transitions : list trans_type)
      (next_sitpn : SITPN),
      IsWellStructuredSitpn sitpn ->
      sitpn_cycle sitpn time_value = Some (fired_transitions, next_sitpn) ->
      IsWellStructuredSitpn next_sitpn.
  Proof.
    do 2 intro.
    functional induction (sitpn_cycle sitpn time_value) using sitpn_cycle_ind; intros.
    (* GENERAL CASE. *)
    - unfold IsWellStructuredSitpn;
        unfold IsWellStructuredStpn;
        unfold IsWellStructuredSpn.
      unfold IsWellStructuredSitpn in H;
        unfold IsWellStructuredStpn in H;
        unfold IsWellStructuredSpn in H.
      injection H0; clear H0; intros.
      unfold NoUnmarkedPlace in H.
      unfold NoUnknownTransInChronos in H.
      (*  
       * We need to ensure that sitpn_fire preserves the structure
       * of marking and chronos, and preserves the fact that chronos
       * are well-formed.
       *)
      
      (* sitpn_fire returns well-formed chronos. *)
      (* Hypothesis H4 in needed to apply sitpn_fire_well_formed_chronos. *)
      elim H; intros; elim H3; intros; unfold AreWellFormedChronos in H4; simpl in H4.
      generalize (increment_all_chronos_well_formed_chronos
                    chronos sensitized_transs updated_chronos H4 e3); intro.
      generalize (sitpn_fire_well_formed_chronos
                    lneighbours pre test inhib post
                    marking updated_chronos lconditions time_value transs priority_groups
                    fired_transitions nextm next_chronos H6 e4); intro.
      (* sitpn_fire preserves marking structure. *)
      generalize (sitpn_fire_same_struct_marking
                    lneighbours pre test inhib post
                    marking updated_chronos lconditions time_value transs priority_groups
                    fired_transitions nextm next_chronos e4); intro.
      (* increment_all_chronos and sitpn_fire preserves chronos structure *)
      generalize (increment_all_chronos_same_struct
                    chronos sensitized_transs updated_chronos e3); intro.
      generalize (sitpn_fire_same_struct_chronos
                    lneighbours pre test inhib post
                    marking updated_chronos lconditions time_value
                    transs priority_groups
                    fired_transitions nextm next_chronos e4); intro.      
      (*  
       * Then, we need to rewrite chronos with updated_chronos, and
       * marking with nextm.
       *)
      unfold MarkingHaveSameStruct in H8;
        unfold ChronosHaveSameStruct in H9;
        unfold ChronosHaveSameStruct in H10.
      simpl in H.
      rewrite H8 in H.
      rewrite H9 in H.
      rewrite H10 in H.
      unfold NoUnknownTransInChronos;
        unfold NoUnmarkedPlace;
        unfold AreWellFormedChronos.
      (* Conjunction of H7 and H14 to obtain a hypothesis close to the goal. *)
      elim H; intros.
      elim H12; intros.
      generalize (conj H11 (conj H7 H14)); intro.
      (* Rewrite and symplify goal to match last hypothesis. *)
      rewrite <- H0; simpl; auto.
    (* CASE sitpn_fire returns None. *)
    - inversion H0.
    (* CASE increment_all_chronos returns None. *)
    - inversion H0.
    (* CASE list_sensitized returns None. *)
    - inversion H0.
  Qed.
  
  (** ------------------------------------------------------------------- *)
  (** ------------------------------------------------------------------- *)
  
  (*! ======================================== !*)
  (*! ====== ANIMATING DURING N CYCLES ======= !*)
  (*! ======================================== !*)  
  
  (** Returns the list of (fired_transitions(i), SITPN(i))
      for each cycle i, from 0 to n, representing the evolution
      of the Petri net [sitpn]. *)
  
  Fixpoint sitpn_animate_aux 
           (sitpn : SITPN)
           (n : nat)
           (sitpn_evolution : list (list trans_type * SITPN)) :
    option (list (list trans_type * SITPN)) :=
    match n with
    (* Base case, returns the list storing the evolution. *)
    | O => Some sitpn_evolution
    | S n' =>
      match (sitpn_cycle sitpn n) with
      (* Adds a new evolution step at the end of the list. *)
      | Some (fired_trans_at_n, sitpn_at_n) =>
        sitpn_animate_aux sitpn_at_n n' (sitpn_evolution ++ [(fired_trans_at_n, sitpn_at_n)])
      (* Error, sitpn_cycle failed!!! *)
      | None => None
      end
    end.

  Functional Scheme sitpn_animate_aux_ind := Induction for sitpn_animate_aux Sort Prop.
  
  (** Formal specification : sitpn_animate_aux *)

  Inductive SitpnAnimateAux (sitpn : SITPN) :
    nat ->
    list (list trans_type * SITPN) ->
    option (list (list trans_type * SITPN)) ->
    Prop :=
  | SitpnAnimateAux_0 :
      forall (sitpn_evolution : list (list trans_type * SITPN)),
        SitpnAnimateAux sitpn 0 sitpn_evolution (Some sitpn_evolution) 
  | SitpnAnimateAux_cons :
      forall (n : nat)
             (fired_trans_at_n : list trans_type)
             (sitpn_at_n : SITPN)
             (sitpn_evolution : list (list trans_type * SITPN))
             (opt_evolution : option (list (list trans_type * SITPN))),
        SitpnCycle sitpn (S n) (Some (fired_trans_at_n, sitpn_at_n)) ->
        SitpnAnimateAux sitpn_at_n
                     n
                     (sitpn_evolution ++ [(fired_trans_at_n, sitpn_at_n)])
                     opt_evolution ->
        SitpnAnimateAux sitpn (S n) sitpn_evolution opt_evolution
  | SitpnAnimateAux_err :
      forall (n : nat)
             (sitpn_evolution : list (list trans_type * SITPN)),
        SitpnCycle sitpn (S n) None ->
        SitpnAnimateAux sitpn (S n) sitpn_evolution None.

  (** Correctness proof : sitpn_animate_aux *)
  
  Theorem sitpn_animate_aux_correct :
    forall (sitpn :SITPN)
           (n : nat)
           (sitpn_evolution : list (list trans_type * SITPN))
           (opt_evolution : option (list (list trans_type * SITPN))),
      sitpn_animate_aux sitpn n sitpn_evolution = opt_evolution ->
      SitpnAnimateAux sitpn n sitpn_evolution opt_evolution.
  Proof.                                                                                
    intros sitpn n sitpn_evolution.
    functional induction (sitpn_animate_aux sitpn n sitpn_evolution) using sitpn_animate_aux_ind; intros.
    (* Case n = 0 *)
    - rewrite <- H; apply SitpnAnimateAux_0.
    (* General case *)
    - intros; rewrite <- H.
      apply SitpnAnimateAux_cons with (fired_trans_at_n := fired_trans_at_n)
                                      (sitpn_at_n := sitpn_at_n).
      + apply sitpn_cycle_correct in e0; auto.
      + apply IHo; auto.
    (* Error case, sitpn_cycle returns None. *)
    - rewrite <- H; apply SitpnAnimateAux_err.
      apply sitpn_cycle_correct in e0; auto.
  Qed.

  (** Completeness proof : sitpn_animate_aux *)
  Theorem sitpn_animate_aux_compl :
    forall (sitpn : SITPN)
           (n : nat)
           (sitpn_evolution : list (list trans_type * SITPN))
           (opt_evolution : option (list (list trans_type * SITPN))),
      SitpnAnimateAux sitpn n sitpn_evolution opt_evolution ->
      sitpn_animate_aux sitpn n sitpn_evolution = opt_evolution.
  Proof.
    intros; elim H; intros.
    (* Case SitpnAnimateAux_0 *)
    - simpl; auto.
    (* Case SitpnAnimateAux_cons *)
    - simpl. apply sitpn_cycle_compl in H0; rewrite H0.
      rewrite H2; auto.
    (* Case SitpnAnimateAux_err *)
    - apply sitpn_cycle_compl in H0.
      simpl.
      rewrite H0; auto.
  Qed.

  (** For all [SITPN] verifying the property [IsWellStructuredSitpn], and for all number [n] 
      of evolution cycles, [sitpn_animate_aux] returns no error. *)
  
  Theorem sitpn_animate_aux_no_error :
    forall (sitpn : SITPN)
      (n : nat)
      (sitpn_evolution : list (list trans_type * SITPN)),
      IsWellStructuredSitpn sitpn ->
      exists (v : list (list trans_type * SITPN)),
        sitpn_animate_aux sitpn n sitpn_evolution = Some v.
  Proof.
    do 3 intro.
    functional induction (sitpn_animate_aux sitpn n sitpn_evolution)
               using sitpn_animate_aux_ind;
      intros.
    (* Base case, n = 0. *)
    - exists sitpn_evolution; auto.
    (* General case. *)
    - apply IHo.
      apply (sitpn_cycle_well_structured sitpn (S n') fired_trans_at_n sitpn_at_n H e0).
    (* Error case, impossible regarding the hypotheses. *)
    - generalize (sitpn_cycle_no_error sitpn (S n') H); intro.
      elim H0; intros.
      rewrite H1 in e0; inversion e0.
  Qed.

  (** For all well-structured [SITPN] passed to [sitpn_animate_aux], 
      and for all list [sitpn_evolution] of well-structured [SITPN], 
      the resulting evolution list is only composed of well-structured [SITPN]. *)
  
  Theorem sitpn_animate_aux_well_structured :
    forall (sitpn : SITPN)
      (n : nat)
      (sitpn_evolution final_sitpn_evolution : list (list trans_type * SITPN)),
      IsWellStructuredSitpn sitpn ->
      (forall sitpn' : SITPN, In sitpn' (snd (split sitpn_evolution)) -> IsWellStructuredSitpn sitpn') ->
      sitpn_animate_aux sitpn n sitpn_evolution = Some final_sitpn_evolution ->
      forall (sitpn'' : SITPN), In sitpn'' (snd (split final_sitpn_evolution)) -> IsWellStructuredSitpn sitpn''.
  Proof.
    do 3 intro.
    functional induction (sitpn_animate_aux sitpn n sitpn_evolution) using sitpn_animate_aux_ind; intros.
    - injection H1; intros.
      rewrite <- H3 in H2.
      apply (H0 sitpn'' H2).
    - apply IHo with (final_sitpn_evolution := final_sitpn_evolution).
      + generalize (sitpn_cycle_well_structured sitpn (S n') fired_trans_at_n sitpn_at_n H e0); intro; auto.
      + intros.
        rewrite snd_split_app in H3.
        apply in_app_or in H3.
        elim H3; intros.
        -- apply (H0 sitpn' H4).
        -- simpl in H4; elim H4; intros;
             [generalize (sitpn_cycle_well_structured sitpn (S n') fired_trans_at_n sitpn_at_n H e0); intro;
              rewrite H5 in H6; assumption
             | elim H5].           
      + auto.
      + auto.
    - inversion H1.
  Qed.

  (** For all well-structured [SITPN] passed to [sitpn_animate_aux], and for all [n], number 
      of evolution cycles, the length of the resulting [final_sitpn_evolution] list
      is equal to the number of evolution cycles plus the length of the [sitpn_evolution] 
      list passed in argument. *)
  
  Theorem sitpn_animate_aux_preserves_cycles :
    forall (sitpn : SITPN)
      (n : nat)
      (sitpn_evolution final_sitpn_evolution : list (list trans_type * SITPN)),
      IsWellStructuredSitpn sitpn ->
      sitpn_animate_aux sitpn n sitpn_evolution = Some final_sitpn_evolution ->
      n + length sitpn_evolution = length final_sitpn_evolution.
  Proof.
    do 3 intro.
    functional induction (sitpn_animate_aux sitpn n sitpn_evolution) using sitpn_animate_aux_ind; intros.
    - injection H0; intros; rewrite H1; simpl; auto.
    - generalize (sitpn_cycle_well_structured sitpn (S n') fired_trans_at_n sitpn_at_n H e0); intro.
      generalize (IHo final_sitpn_evolution H1 H0); intro.
      rewrite <- H2.
      rewrite app_length.
      simpl.
      rewrite Nat.add_1_r.
      auto.
    - inversion H0.
  Qed.
  
  (** ------------------------------------------------------------------------------- *)
  (** ------------------------------------------------------------------------------- *)
  
  (** Wrapper function around [sitpn_animate_aux]. 
      
      Here, the [sitpn_evolution] list is initialized to [nil]. *)
  
  Definition sitpn_animate (sitpn : SITPN) (n : nat) :
    option (list (list trans_type * SITPN)) := sitpn_animate_aux sitpn n [].

  (** Formal specification : sitpn_animate *)
  
  Inductive SitpnAnimate (sitpn : SITPN) (n : nat) : option (list (list trans_type * SITPN)) -> Prop :=
  | SitpnAnimate_cons :
      forall (opt_sitpn_evolution : option (list (list trans_type * SITPN))),
        SitpnAnimateAux sitpn n [] opt_sitpn_evolution ->
        SitpnAnimate sitpn n opt_sitpn_evolution.

  (** Correctness proof : sitpn_animate *)
  
  Theorem sitpn_animate_correct :
    forall (sitpn : SITPN) (n : nat) (opt_sitpn_evolution : option (list (list trans_type * SITPN))),
      sitpn_animate sitpn n = opt_sitpn_evolution ->
      SitpnAnimate sitpn n opt_sitpn_evolution.
  Proof.
    unfold sitpn_animate.
    intros.
    apply SitpnAnimate_cons; apply sitpn_animate_aux_correct in H; auto.
  Qed.

  (** Completeness proof : sitpn_animate *)
  
  Theorem sitpn_animate_compl :
    forall (sitpn : SITPN) (n : nat) (opt_sitpn_evolution : option (list (list trans_type * SITPN))),
      SitpnAnimate sitpn n opt_sitpn_evolution ->
      sitpn_animate sitpn n = opt_sitpn_evolution.
  Proof.
    unfold sitpn_animate.
    intros.
    elim H; apply sitpn_animate_aux_compl; auto.
  Qed.
  
  (** For all [SITPN] verifying the property [IsWellStructuredSitpn],
      and for all number [n] of evolution cycles, [sitpn_animate] returns no error. *)
  
  Theorem sitpn_animate_no_error :
    forall (sitpn : SITPN) (n : nat),
      IsWellStructuredSitpn sitpn ->
      exists (v : list ((list trans_type) * SITPN)), sitpn_animate sitpn n = Some v.
  Proof.
    unfold sitpn_animate.
    intros.
    generalize (sitpn_animate_aux_no_error sitpn n [] H); intro.
    elim H0; intros.
    rewrite H1.
    exists x; auto.
  Qed.

  (** For all well-structured [SITPN] passed to [sitpn_animate], 
      the resulting evolution list is only composed of well-structured [SITPN]. *)
  
  Theorem sitpn_animate_well_structured :
    forall (sitpn : SITPN)
      (n : nat)
      (sitpn_evolution : list (list trans_type * SITPN)),
      IsWellStructuredSitpn sitpn ->
      sitpn_animate sitpn n = Some sitpn_evolution ->
      forall (sitpn' : SITPN), In sitpn' (snd (split sitpn_evolution)) -> IsWellStructuredSitpn sitpn'.
  Proof.
    unfold sitpn_animate.
    intros.
    (* We need this hypothesis to apply sitpn_animate_aux_well_structured. *)
    assert (H' : forall (sitpn' : SITPN), In sitpn' [] -> IsWellStructuredSitpn sitpn')
      by (intros; elim H2).
    generalize (sitpn_animate_aux_well_structured sitpn n [] sitpn_evolution H H' H0); intros.
    apply H2; assumption.
  Qed.

  (** For all well-structured [SITPN] passed to [sitpn_animate], and for all number [n]  
      of evolution cycles, the length of the resulting [final_sitpn_evolution] list
      is equal to the number of evolution cycles. *)
  
  Theorem sitpn_animate_preserves_cycles :
    forall (sitpn : SITPN)
      (n : nat)
      (sitpn_evolution : list (list trans_type * SITPN)),
      IsWellStructuredSitpn sitpn ->
      sitpn_animate sitpn n = Some sitpn_evolution ->
      n = length sitpn_evolution.
  Proof.
    unfold sitpn_animate; intros.
    generalize (sitpn_animate_aux_preserves_cycles sitpn n [] sitpn_evolution H H0); intros.
    rewrite Nat.add_0_r in H1.
    assumption.
  Qed.
  
End AnimateSitpn.
