Require Export Hilecop.SITPN.
Require Export Hilecop.STPNAnimator.

(** * Firing algorithm for SITPN *)

(*=============================================================*)
(*================= FIRING ALGORITHM for SITPN ================*)
(*=============================================================*)

Section FireSitpn.

  (** Returns true if transition t is firable according
      to "SITPN standards", meaning that t is sensitized,
      its time counter value is in the firable interval, and
      its condition value equals true.
    
      Raises an error (None value) if stpn_is_firable or 
      get_condition returns None. *)
  
  Definition sitpn_is_firable
             (t : trans_type)
             (neighbours_t : neighbours_type)
             (pre test inhib: weight_type)
             (steadym decreasingm : marking_type)
             (chronos : list (trans_type * option chrono_type))
             (lconditions : list (trans_type * option condition_type))
             (time_value : nat) : option bool :=
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
  
  (*** Formal specification : sitpn_is_firable ***)
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
  
  (** -------------------------------------------------------------------------- *)
  (** -------------------------------------------------------------------------- *)
  
  (** Given 1 priority group of transitions (a list [pgroup]), 
      returns a list of transitions "fired_pre_group" and a marking [decreasingm].
   
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
  
  (** Formal specification : stpn_fire_pre_aux *)
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

  (*** Correctness proof : sitpn_fire_pre_aux ***)

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
    (* Case stpn_is_firable returns false. *)
    - apply SitpnFirePreAux_firable_false with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply sitpn_is_firable_correct; auto.
      + apply IHo; auto.
    (* Case stpn_is_firable returns an error. *)
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

  (** ----------------------------------------------------------------------- *)
  (** ----------------------------------------------------------------------- *)
  
  (** Returns the list of pre-fired transitions and a marking.
   
      Applies [sitpn_fire_pre] over all priority group of transitions. 
      Begins with initial marking; End with half fired marking.  *)
  
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

  (** ------------------------------------------------------------------------ *)
  (** ------------------------------------------------------------------------ *)
  
  (** Wrapper around sitpn_map_fire_pre_aux function. 
      Updates the marking by consuming the tokens in pre-condition places. *)
  
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

  (*** Completeness proof : sitpn_map_fire_pre ***)
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
  
  (** Returns a tuplet (fired transitions (at this cycle), 
                       final marking, 
                       final chronos).
               
      Raises an error (None value) if sitpn_map_fire_pre, reset_all_chronos,
      list_disabled, or fire_post return None.            
   
      This function has the same structure has stpn_fire, except
      that sitpn_fire adds some instructions to reset chronos
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
  
End FireSitpn.

(*=========================================================*)
(*================= SITPN CYCLE EVOLUTION =================*)
(*=========================================================*)

Section AnimateSitpn.
  
  (** Returns the resulting Petri net after that all the sensitized
      transitions - with right chrono and cond value - in sitpn have been fired.
      
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
  
  (* Formal specification : sitpn_cycle *)
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

  (** ------------------------------------------------------------------- *)
  (** ------------------------------------------------------------------- *)
  
  (*******************************************)
  (******** ANIMATING DURING N CYCLES ********)
  (*******************************************)
  
  (** Returns the list of (transitions_fired(i), SITPN(i))
      for each cycle i, from 0 to n, representing the evolution
      of the Petri net sitpn. *)
  
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

  (*** Completeness proof : sitpn_animate_aux ***)
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

End AnimateSitpn.
