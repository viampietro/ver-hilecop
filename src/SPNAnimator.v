Require Export Hilecop.SPN.

(*! ============================================================ !*)
(*! ================ FIRING ALGORITHM for SPN ================== !*)
(*! ============================================================ !*)

Section FireSpn.

  (** Returns true if a certain transition t is firable according to a marking [steadym]
      (or [decreasingm]) on the neighbour places of t and to some 
      weight functions [pre_arcs_t], [test_arcs_t] and [inhib_arcs_t]. *)
  Definition spn_is_firable
             (t : trans_type)
             (neighbours_t : neighbours_type)
             (pre test inhib : weight_type)
             (steadym decreasingm : marking_type) : option bool :=
    match (check_pre_or_test (pre t) decreasingm (pre_pl neighbours_t) true) with
    | Some check_pre_result =>  
      match (check_pre_or_test (test t) steadym (test_pl neighbours_t) true) with
      | Some check_test_result =>
        match check_inhib (inhib t) steadym (inhib_pl neighbours_t) true with
        | Some check_inhib_result => Some (check_pre_result
                                             && check_test_result
                                             && check_inhib_result)
        (* Case of error!! *)
        | None => None
        end
      (* Case of error!! *)
      | None => None
      end
    (* Case of error!! *)
    | None => None
    end.

  Functional Scheme spn_is_firable_ind := Induction for spn_is_firable Sort Prop.

  (** Formal specification : spn_is_firable *)
  Inductive SpnIsFirable
            (t : trans_type)
            (neighbours_t : neighbours_type)
            (pre test inhib : weight_type)
            (steadym decreasingm : marking_type) : option bool -> Prop :=
  | SpnIsFirable_some :
      forall (check_pre_result check_test_result check_inhib_result : bool),
        CheckPreOrTest (pre t) decreasingm (pre_pl neighbours_t) true (Some check_pre_result) /\
        CheckPreOrTest (test t) steadym (test_pl neighbours_t) true (Some check_test_result) /\
        CheckInhib (inhib t) steadym (inhib_pl neighbours_t) true (Some check_inhib_result) ->
        SpnIsFirable t neighbours_t pre test inhib steadym decreasingm
                     (Some (check_pre_result && check_test_result && check_inhib_result))
  | SpnIsFirable_err :
      CheckPreOrTest (pre t) decreasingm (pre_pl neighbours_t) true None \/
      CheckPreOrTest (test t) steadym (test_pl neighbours_t) true None \/
      CheckInhib (inhib t) steadym (inhib_pl neighbours_t) true None ->
      SpnIsFirable t neighbours_t pre test inhib steadym decreasingm None.

  (** Correctness proof : spn_is_firable *)
  
  Theorem spn_is_firable_correct :
    forall (t : trans_type)
           (neighbours_t : neighbours_type)
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (optionb : option bool),
      spn_is_firable t neighbours_t pre test inhib steadym decreasingm = optionb ->
      SpnIsFirable t neighbours_t pre test inhib steadym decreasingm optionb.
  Proof.
    intros t neighbours_t pre test inhib steadym decreasingm. 
    functional induction (spn_is_firable t neighbours_t pre test inhib steadym decreasingm)
               using spn_is_firable_ind; intros.
    (* Case check_pre, check_test and check_inhib returned some value. *)
    - rewrite <- H; apply SpnIsFirable_some.
      split; [apply check_pre_or_test_correct; auto |
              split; [apply check_pre_or_test_correct; auto |
                      apply check_inhib_correct; auto]].            
    (* Case of error 1. check_inhib returns None. *)
    - rewrite <- H; apply SpnIsFirable_err.
      apply check_inhib_correct in e1; auto.
    (* Case of error 2. check_test returns None.  *)
    - rewrite <- H; apply SpnIsFirable_err.
      apply check_pre_or_test_correct in e0; auto.
    (* Case of error 3. check_pre returns None. *)
    - rewrite <- H; apply SpnIsFirable_err.
      apply check_pre_or_test_correct in e; auto.
  Qed.

  (*** Completeness proof : spn_is_firable ***)
  Theorem spn_is_firable_compl :
    forall (t : trans_type)
           (neighbours_t : neighbours_type)
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (optionb : option bool),
      SpnIsFirable t neighbours_t pre test inhib steadym decreasingm optionb ->
      spn_is_firable t neighbours_t pre test inhib steadym decreasingm = optionb.
  Proof.
    intros t neighbours_t pre test inhib steadym decreasingm optionb H; elim H; intros.
    (* Case SpnIsFirable_some *)
    - unfold spn_is_firable.
      elim H0; clear H0; intros.
      elim H1; clear H1; intros.
      repeat (((apply check_pre_or_test_compl in H0; rewrite H0) ||
               (apply check_pre_or_test_compl in H1; rewrite H1) ||
               (apply check_inhib_compl in H2; rewrite H2));
              auto).
    (* Case SpnIsFirable_err *)
    - unfold spn_is_firable.
      elim H0; clear H0; intros.
      + apply check_pre_or_test_compl in H0; rewrite H0; auto.
      + elim H0; clear H0; intros.
        -- case (check_pre_or_test (pre t) decreasingm (pre_pl neighbours_t) true).
           ++ intro; apply check_pre_or_test_compl in H0; rewrite H0; auto.
           ++ auto.
        -- case (check_pre_or_test (pre t) decreasingm (pre_pl neighbours_t) true).
           +++ case (check_pre_or_test (test t) steadym (test_pl neighbours_t) true);
                 [ apply check_inhib_compl in H0; rewrite H0; auto | intro; auto ].
           +++ auto.
  Qed.

  (* Lemma : Proves that spn_is_firable returns no error if
   *         the places in (pre_pl neighbours_t), (inhib_pl neighbours_t) 
   *         and (test_pl neighbours_t) are referenced in markings steadym
   *         and decreasingm.  
   *
   *)
  Lemma spn_is_firable_no_error :
    forall (t : trans_type)
           (neighbours_t : neighbours_type)
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type),
      incl (pre_pl neighbours_t) (fst (split decreasingm)) ->
      incl (test_pl neighbours_t) (fst (split steadym)) ->
      incl (inhib_pl neighbours_t) (fst (split steadym)) ->
      exists v : bool,
        spn_is_firable t neighbours_t pre test inhib steadym decreasingm = Some v.
  Proof.
    unfold incl.
    intros t neighbours_t pre test inhib steadym decreasingm.
    functional induction (spn_is_firable t neighbours_t pre test inhib steadym decreasingm)
               using spn_is_firable_ind; intros.
    (* Case all went well. *)
    - exists (check_pre_result && check_test_result && check_inhib_result); auto.
    (* Case check_inhib = None, impossible regarding hypothesis. *)
    - apply check_inhib_no_error with (inhib_arcs_t := inhib t)
                                      (check_result := true) in H1.
      elim H1; intros.
      rewrite e1 in H2; inversion H2.
    (* Case check_test = None, impossible regarding hypothesis. *)
    - apply check_pre_or_test_no_error with (pre_or_test_arcs_t := test t)
                                            (check_result := true) in H0.
      elim H0; intros.
      rewrite e0 in H2; inversion H2.
    (* Case check_pre = None, impossible regarding hypothesis. *)
    - apply check_pre_or_test_no_error with (pre_or_test_arcs_t := pre t)
                                            (check_result := true) in H.
      elim H; intros.
      rewrite e in H2; inversion H2.
  Qed.
    
  (* 
   * There are 2 parallel calculus in spn_fire_pre_aux : 
   * 1. pumping tokens to get "decreasingm" (fired pre)
   * 2. returning group of transitions (fired_pre_group)
   *
   * and 2 markings are recorded : 
   * 1. the initial one to check with inhib and test arcs
   * 2. a floating (decreasing) intermediate marking to check classic arcs
   *)
  
  (* Function : Given 1 priority group of transitions (a list pgroup), 
   *            returns 1 list of transitions "fired_pre_group" 
   *            and marking "decreasingm" accordingly ...
   *
   *            Returns a couple (list of transitions, marking)
   *            For each sensitized transition of the list,
   *            the marking of the pre-condition places are updated (the 
   *            transition is fired). "decreasingm" is then the resulting marking.
   *)
  Fixpoint spn_fire_pre_aux
           (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)  
           (steadym : marking_type)
           (decreasingm : marking_type)
           (fired_pre_group pgroup : list trans_type) :
    option (list trans_type * marking_type) :=
    match pgroup with
    | t :: tail =>
      match get_neighbours lneighbours t with
      (* Checks neighbours of t. *)
      | Some neighbours_t =>
        match spn_is_firable t neighbours_t pre test inhib steadym decreasingm with
        (* If t is firable, updates the marking for the pre places neighbours of t. *)
        | Some true =>
          match update_marking_pre t pre decreasingm (pre_pl neighbours_t) with
          (* Recursive call with new marking *)
          | Some marking' =>
            spn_fire_pre_aux lneighbours pre test inhib steadym marking' (fired_pre_group ++ [t]) tail
          (* Something went wrong, error! *)
          | None => None
          end
        (* Else no changes but inductive progress. *)
        | Some false =>
          spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group tail
        (* Something went wrong, error! *)
        | None => None
        end
      (* If transition t have no neighbours, then error! *)
      | None => None
      end
    | []  => Some (fired_pre_group, decreasingm)
    end.

  Functional Scheme spn_fire_pre_aux_ind := Induction for spn_fire_pre_aux Sort Prop. 
  
  (*** Formal specification : spn_fire_pre_aux ***)
  Inductive SpnFirePreAux
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type) 
            (steadym : marking_type) 
            (decreasingm : marking_type)
            (fired_pre_group : list trans_type) :
    list trans_type -> option (list trans_type * marking_type) -> Prop :=
  | SpnFirePreAux_nil :
      SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group []
                    (Some (fired_pre_group, decreasingm))
  (* Case get_neighbours returns an error. *)
  | SpnFirePreAux_neighbours_err :
      forall (t : trans_type) (pgroup : list trans_type),
        GetNeighbours lneighbours t None ->
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group (t :: pgroup) None
  (* Case spn_is_firable returns an error. *)
  | SpnFirePreAux_firable_err :
      forall (t : trans_type) (pgroup : list trans_type) (neighbours_t : neighbours_type),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        SpnIsFirable t neighbours_t pre test inhib steadym decreasingm None ->
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group (t :: pgroup) None
  (* Case spn_is_firable returns false. *)
  | SpnFirePreAux_firable_false :
      forall (t : trans_type)
             (pgroup : list trans_type)
             (neighbours_t : neighbours_type)
             (option_final_couple : option (list trans_type * marking_type)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        SpnIsFirable t neighbours_t pre test inhib steadym decreasingm (Some false) ->
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup
                      option_final_couple ->
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group (t :: pgroup)
                      option_final_couple
  (* Case update_marking_pre returns an error. *)
  | SpnFirePreAux_update_err :
      forall (t : trans_type)
             (neighbours_t : neighbours_type)
             (pgroup : list trans_type),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        SpnIsFirable t neighbours_t pre test inhib steadym decreasingm (Some true) ->
        UpdateMarkingPre t pre decreasingm (pre_pl neighbours_t) None ->
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group (t :: pgroup) None
  (* General case, all went well. *)
  | SpnFirePreAux_cons :
      forall (t : trans_type)
             (neighbours_t : neighbours_type)
             (pgroup : list trans_type)
             (modifiedm : marking_type)
             (option_final_couple : option (list trans_type * marking_type)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        SpnIsFirable t neighbours_t pre test inhib steadym decreasingm (Some true) ->
        UpdateMarkingPre t pre decreasingm (pre_pl neighbours_t) (Some modifiedm) ->
        SpnFirePreAux lneighbours pre test inhib steadym modifiedm (fired_pre_group ++ [t]) pgroup
                      option_final_couple ->
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group (t :: pgroup)
                      option_final_couple.
  
  (*** Correctness proof : spn_fire_pre_aux ***)
  Theorem spn_fire_pre_aux_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup = option_final_couple ->
      SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup option_final_couple.
    functional induction (spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup)
               using spn_fire_pre_aux_ind; intros.
    (* Case pgroup = [] *)
    - rewrite <- H; apply SpnFirePreAux_nil.
    (* General case, all went well. *)
    - apply SpnFirePreAux_cons with (modifiedm := marking')
                                    (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply spn_is_firable_correct; auto.
      + apply update_marking_pre_correct; auto.
      + apply IHo; auto.
    (* Case update_marking_pre error. *)
    - rewrite <- H; apply SpnFirePreAux_update_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply spn_is_firable_correct; auto.
      + apply update_marking_pre_correct; auto.
    (* Case spn_is_firable returns false. *)
    - apply SpnFirePreAux_firable_false with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply spn_is_firable_correct; auto.
      + apply IHo; auto.
    (* Case spn_is_firable returns an error. *)
    - rewrite <- H; apply SpnFirePreAux_firable_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply spn_is_firable_correct; auto.
    (* Case get_neighbours returns an error. *)
    - rewrite <- H; apply SpnFirePreAux_neighbours_err.
      apply get_neighbours_correct; auto.
  Qed.

  (*** Completeness proof : spn_fire_pre_aux ***)
  Theorem spn_fire_pre_aux_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup option_final_couple ->
      spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup = option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm fired_pre_group
           pgroup option_final_couple Hspec.
    induction Hspec.
    (* Case SpnFirePreAux_nil *)
    - simpl; auto.
    (* Case SpnFirePreAux_neighbours_err *)
    - simpl; apply get_neighbours_compl in H; rewrite H; auto.
    (* Case SpnFirePreAux_firable_err *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply spn_is_firable_compl in H0; rewrite H0; auto.
    (* Case SpnFirePreAux_firable_false *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply spn_is_firable_compl in H0; rewrite H0; rewrite IHHspec; auto.
    (* Case SpnFirePreAux_update_err *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply spn_is_firable_compl in H0; rewrite H0; auto.
      apply update_marking_pre_compl in H1; rewrite H1; auto.
    (* Case SpnFirePreAux_cons *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply spn_is_firable_compl in H0; rewrite H0; auto.
      apply update_marking_pre_compl in H1; rewrite H1; auto.
  Qed.

  (* Lemma : spn_fire_pre_aux returns no error if 
   *         all transition t in pgroup are referenced in lneighbours
   *         and if all neighbour places referenced in lneighbours are
   *         referenced in the markings steadym and decreasingm. 
   *)
  Lemma spn_fire_pre_aux_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type),
      incl pgroup (fst (split lneighbours)) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split decreasingm)) /\
           incl neighbours.(inhib_pl) (fst (split steadym)) /\
           incl neighbours.(test_pl) (fst (split steadym)))) ->
      exists v : (list trans_type * marking_type),
        spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup = Some v.
  Proof.
    unfold incl.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm
           fired_pre_group pgroup.
    functional induction (spn_fire_pre_aux lneighbours pre test inhib
                                           steadym decreasingm
                                           fired_pre_group pgroup)
               using spn_fire_pre_aux_ind;
      intros.
    (* Base case, pgroup = []. *)
    - exists (fired_pre_group, decreasingm); auto.
    (* Case spn_is_firable = true. *)
    - apply IHo.
      + intros.
        apply (in_cons t) in H1.
        apply (H a) in H1; auto.
      + intros.
        apply (H0 t0 neighbours) in H1.
        apply update_marking_pre_same_struct in e3.
        unfold MarkingHaveSameStruct in e3.
        rewrite <- e3; auto.
    (* Case update_marking_pre = None,
     * impossible regarding hypothesis.
     *)
    - cut (In t (t :: tail)); intros.
      + apply get_neighbours_in in e0.
        generalize ((H0 t neighbours_t) e0).
        intros.
        elim H2; intros.
        apply (update_marking_pre_no_error t pre (pre_pl neighbours_t) decreasingm) in H3.
        elim H3; intros.
        rewrite H5 in e3; inversion e3.
      + apply in_eq.
    (* Case spn_is_firable = false. *)
    - apply IHo; intros.
      + apply (in_cons t) in H1; apply H in H1; auto.
      + apply H0 in H1; auto.
    (* Case spn_is_firable = None, 
     * impossible regarding the hypotheses. 
     *)
    - cut (In t (t :: tail)); intros.
      + apply get_neighbours_in in e0.
        generalize ((H0 t neighbours_t) e0).
        intros.
        elim H2; intros; clear H2.
        elim H4; intros; clear H4.
        (* Applies spn_is_firable_no_error to create a contradiction. *)
        apply (spn_is_firable_no_error t neighbours_t pre test inhib
                                       steadym decreasingm H3 H5) in H2.
        elim H2; intros.
        rewrite H4 in e1.
        inversion e1.
      + apply in_eq.
    (* Case get_neighbours = None, 
     * impossible regarding the hypotheses.
     *)
    - cut (In t (t :: tail)); intros.
      + apply H in H1.
        apply get_neighbours_no_error in H1.
        elim H1; intros.
        rewrite H2 in e0; inversion e0.
      + apply in_eq.
  Qed.

  (* Lemma : Proves that spn_fire_pre_aux preserves
   *         the structure of the marking decreasingm
   *         passed as argument. 
   *)
  Lemma spn_fire_pre_aux_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (final_fire_pre_group : list trans_type)
           (finalm : marking_type),
      spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup =
      Some (final_fire_pre_group, finalm) ->
      MarkingHaveSameStruct decreasingm finalm.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup.
    functional induction (spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup)
               using spn_fire_pre_aux_ind;
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

  (*  
   * Lemma : If all transitions in pgroup and in fired_pre_group
   *         are in lneighbours then all transitions in final_fired_pre_group
   *         are in lneighbours.
   *)
  Lemma spn_fire_pre_aux_final_fired_in_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (final_fired_pre_group : list trans_type)
           (finalm : marking_type),
      incl pgroup (fst (split lneighbours)) ->
      incl fired_pre_group (fst (split lneighbours)) ->
      spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup =
      Some (final_fired_pre_group, finalm) ->
      incl final_fired_pre_group (fst (split lneighbours)).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup.
    functional induction (spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup)
               using spn_fire_pre_aux_ind;
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
    (* Case spn_is_firable = false. *)
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
    (* Case spn_is_firable returns an error,
     * then contradiction.
     *)
    - inversion H1.
    (* Case get_neighbours returns an error,
     * then contradiction.
     *)
    - inversion H1.
  Qed.

  (*  
   * Lemma : If there are no duplicates in marking decreasingm
   *         then spn_fire_pre_aux returns a marking with no
   *         duplicates.
   *)
  Lemma spn_fire_pre_aux_nodup :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (final_fired_pre_group : list trans_type)
           (finalm : marking_type),
      NoDup (fst (split decreasingm)) ->
      spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup =
      Some (final_fired_pre_group, finalm) ->
      NoDup (fst (split finalm)).
  Proof.
    intros lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup.
    functional induction (spn_fire_pre_aux lneighbours pre test inhib
                                           steadym decreasingm
                                           fired_pre_group pgroup)
               using spn_fire_pre_aux_ind;
    intros.
    (* Base case, pgroup = []. *)
    - injection H0; intros; rewrite <- H1; auto.
    (* Case update_marking_pre returns Some value. *)
    - apply IHo with (final_fired_pre_group := final_fired_pre_group).
      + apply (update_marking_pre_nodup t pre (pre_pl neighbours_t) decreasingm marking' H e3).
      + auto.
    (* Case update_marking_pre returns None. *)
    - inversion H0.
    (* Case spn_is_firable = false *)
    - apply (IHo final_fired_pre_group finalm); [auto | auto].
    (* Case spn_is_firable = None. *)
    - inversion H0.
    (* Case get_neighbours = None. *)
    - inversion H0.
  Qed.
  
  (*****************************************************)
  (*****************************************************)
  
  (*  
   * Function : Wrapper function around spn_fire_pre_aux.
   *)
  Definition spn_fire_pre
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib : weight_type) 
             (steadym : marking_type) 
             (decreasingm : marking_type)
             (pgroup : list trans_type) : option (list trans_type * marking_type) :=
    spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm [] pgroup.

  Functional Scheme spn_fire_pre_ind := Induction for spn_fire_pre Sort Prop.

  (*** Formal specification : spn_fire_pre ***)
  Inductive SpnFirePre
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type) 
            (steadym : marking_type) 
            (decreasingm : marking_type)
            (pgroup : list trans_type) : option (list trans_type * marking_type) -> Prop :=
  | SpnFirePre_cons :
      forall (option_final_couple : option (list trans_type * marking_type)),
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm [] pgroup
                      option_final_couple ->
        SpnFirePre lneighbours pre test inhib steadym decreasingm pgroup
                   option_final_couple.

  (*** Correctness proof : spn_fire_pre ***)
  Theorem spn_fire_pre_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym decreasingm : marking_type) 
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup = option_final_couple ->
      SpnFirePre lneighbours pre test inhib steadym decreasingm pgroup option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pgroup option_final_couple;
      functional induction (spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup)
                 using spn_fire_pre_ind; intros.
    apply SpnFirePre_cons; apply spn_fire_pre_aux_correct in H; auto.
  Qed.

  (*** Completeness proof : spn_fire_pre ***)
  Theorem spn_fire_pre_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym decreasingm : marking_type) 
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      SpnFirePre lneighbours pre test inhib steadym decreasingm pgroup option_final_couple ->
      spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup = option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pgroup option_final_couple Hspec;
      elim Hspec;
      intros.
    unfold spn_fire_pre; apply spn_fire_pre_aux_compl in H; auto. 
  Qed.

  (* Lemma : spn_fire_pre returns no error if 
   *         all transition t in pgroup are referenced in lneighbours
   *         and if all neighbour places referenced in lneighbours are
   *         referenced in the markings steadym and decreasingm. 
   *)
  Lemma spn_fire_pre_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (pgroup : list trans_type),
      incl pgroup (fst (split lneighbours)) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split decreasingm)) /\
           incl neighbours.(inhib_pl) (fst (split steadym)) /\
           incl neighbours.(test_pl) (fst (split steadym)))) ->
      exists v : (list trans_type * marking_type),
        spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup = Some v.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pgroup; intros.
    unfold spn_fire_pre.
    apply spn_fire_pre_aux_no_error; [auto | auto].
  Qed.

  (* Lemma : Proves that spn_fire_pre preserves
   *         the structure of the marking decreasingm
   *         passed as argument. 
   *)
  Lemma spn_fire_pre_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (pgroup : list trans_type)
           (final_fire_pre_group : list trans_type)
           (finalm : marking_type),
      spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup =
      Some (final_fire_pre_group, finalm) ->
      MarkingHaveSameStruct decreasingm finalm.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pgroup; intros.
    unfold spn_fire_pre in H.
    apply spn_fire_pre_aux_same_struct in H; auto.
  Qed.

  (*  
   * Lemma : If all transitions in pgroup are in lneighbours then 
   *         all transitions in final_fired_pre_group are in lneighbours.
   *)
  Lemma spn_fire_pre_final_fired_in_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (pgroup : list trans_type)
           (final_fired_pre_group : list trans_type)
           (finalm : marking_type),
      incl pgroup (fst (split lneighbours)) ->
      spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup =
      Some (final_fired_pre_group, finalm) ->
      incl final_fired_pre_group (fst (split lneighbours)).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm pgroup.
    functional induction (spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup)
               using spn_fire_pre_ind;
    intros.
    cut (forall t : trans_type, In t [] -> In t (fst (split lneighbours))); intros.
    - generalize (spn_fire_pre_aux_final_fired_in_lneighbours
                    lneighbours pre test inhib
                    steadym decreasingm
                    [] pgroup
                    final_fired_pre_group finalm
                    H H2 H0).
      intros.
      apply H3 in H1.
      auto.
    - elim H2.
  Qed.

  (*  
   * Lemma : If there are no duplicates in marking decreasingm
   *         then spn_fire_pre returns a marking with no duplicates.
   *)
  Lemma spn_fire_pre_nodup :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (pgroup : list trans_type)
           (final_fired_pre_group : list trans_type)
           (finalm : marking_type),
      NoDup (fst (split decreasingm)) ->
      spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup =
      Some (final_fired_pre_group, finalm) ->
      NoDup (fst (split finalm)).
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pgroup; intros.
    unfold spn_fire_pre in H0.
    apply (spn_fire_pre_aux_nodup lneighbours pre test inhib steadym decreasingm [] pgroup
                                  final_fired_pre_group finalm H H0).
  Qed.
  
  (***********************************************************************)
  (***********************************************************************)
  
  (*
   * Function : Returns the list of pre-fired transitions.
   *            Apply spn_fire_pre over ALL priority group of transitions. 
   *            Begin with initial marking; End with half fired marking.  
   *            "pre_fired_transitions" is empty at first. 
   *)
  Fixpoint spn_map_fire_pre_aux
           (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (pre_fired_transitions : list trans_type)
           (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) :=
    match priority_groups with
    (* Loops over all priority group of transitions (prgroup) and
     * calls spn_fire_pre. *)
    | pgroup :: pgroups_tail =>
      match spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup with
      (* If spn_fire_pre succeeds, then adds the fired transitions
       * in pre_fired_transitions list. *)
      | Some (pre_fired_trs, decreasedm) =>
        spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasedm
                             (pre_fired_transitions ++ pre_fired_trs) pgroups_tail
      (* Case of error! *)
      | None => None
      end
    | [] => Some (pre_fired_transitions, decreasingm)
    end.

  Functional Scheme spn_map_fire_pre_aux_ind := Induction for spn_map_fire_pre_aux Sort Prop.
  
  (*** Formal specification : spn_map_fire_pre_aux ***)
  Inductive SpnMapFirePreAux
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type)
            (steadym decreasingm : marking_type)
            (pre_fired_transitions : list trans_type) :
    list (list trans_type) -> option (list trans_type * marking_type) -> Prop :=
  | SpnMapFirePreAux_nil :
      SpnMapFirePreAux lneighbours pre test inhib steadym decreasingm pre_fired_transitions []
                       (Some (pre_fired_transitions, decreasingm))
  | SpnMapFirePreAux_cons :
      forall (pgroup pre_fired_trs : list trans_type)
             (decreasedm : marking_type)
             (priority_groups : list (list trans_type))
             (option_final_couple : option (list trans_type * marking_type)),
        SpnFirePre lneighbours pre test inhib steadym decreasingm pgroup
                   (Some (pre_fired_trs, decreasedm)) ->
        SpnMapFirePreAux lneighbours pre test inhib steadym decreasedm (pre_fired_transitions ++ pre_fired_trs)
                         priority_groups
                         option_final_couple ->
        SpnMapFirePreAux lneighbours pre test inhib steadym decreasingm pre_fired_transitions
                         (pgroup :: priority_groups)
                         option_final_couple
  | SpnMapFirePreAux_err :
      forall (pgroup : list trans_type)
             (priority_groups : list (list trans_type)),
        SpnFirePre lneighbours pre test inhib steadym decreasingm pgroup None ->
        SpnMapFirePreAux lneighbours pre test inhib steadym decreasingm pre_fired_transitions
                         (pgroup :: priority_groups) None.

  (*** Correctness proof : spn_map_fire_pre_aux ***)
  Theorem spn_map_fire_pre_aux_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (priority_groups : list (list trans_type))
           (pre_fired_transitions : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                           pre_fired_transitions priority_groups = option_final_couple ->
      SpnMapFirePreAux lneighbours pre test inhib steadym decreasingm
                       pre_fired_transitions priority_groups option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm priority_groups
           pre_fired_transitions option_final_couple;
      functional induction (spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                                                 pre_fired_transitions priority_groups)
                 using spn_map_fire_pre_aux_ind;
      intros.
    (* Case priority_groups = [] *)
    - rewrite <- H; apply SpnMapFirePreAux_nil.
    (* General case *)
    - apply SpnMapFirePreAux_cons with (pre_fired_trs := pre_fired_trs)
                                       (decreasedm := decreasedm).
      + apply spn_fire_pre_correct; auto.
      + apply IHo; rewrite H; auto.
    (* Case of error *)
    - rewrite <- H; apply SpnMapFirePreAux_err.
      apply spn_fire_pre_correct; auto.
  Qed.

  (*** Completeness proof : spn_map_fire_pre_aux ***)
  Theorem spn_map_fire_pre_aux_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (priority_groups : list (list trans_type))
           (pre_fired_transitions : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      SpnMapFirePreAux lneighbours pre test inhib steadym decreasingm
                       pre_fired_transitions priority_groups option_final_couple ->
      spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                           pre_fired_transitions priority_groups = option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm
           priority_groups pre_fired_transitions option_final_couple Hspec;
      elim Hspec;
      intros.
    (* Case SpnMapFirePreAux_nil *)
    - simpl; auto.
    (* Case SpnMapFirePreAux_cons *)
    - simpl; apply spn_fire_pre_compl in H; rewrite H; rewrite H1; auto.
    (* Case SpnMapFirePreAux_err *)
    - simpl; apply spn_fire_pre_compl in H; rewrite H; auto.
  Qed.

  (*
   * Lemma : spn_map_fire_pre_aux returns no error if 
   *         forall pgroup of transitions in priority_groups,
   *         transitions are referenced in lneighbours and
   *         neighbours places (of these transitions) are referenced 
   *         in markings steadym and decreasingm.
   *)
  Lemma spn_map_fire_pre_aux_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (priority_groups : list (list trans_type))
           (pre_fired_transitions : list trans_type),
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split decreasingm)) /\
           incl neighbours.(inhib_pl) (fst (split steadym)) /\
           incl neighbours.(test_pl) (fst (split steadym)))) ->
      exists v : (list trans_type * marking_type),
        spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                             pre_fired_transitions priority_groups = Some v.
  Proof.
    unfold PriorityGroupsAreRefInLneighbours.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm
           priority_groups pre_fired_transitions.
    functional induction (spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                                               pre_fired_transitions priority_groups)
               using spn_map_fire_pre_aux_ind;
      intros.
    (* Base case, priority_groups = []. *)
    - exists (pre_fired_transitions, decreasingm); auto.
    (* Case spn_fire_pre = Some v *)
    - apply IHo.
      + intros.
        apply (in_cons pgroup) in H1.
        generalize (H pgroup0 H1); intro; auto.
      + apply spn_fire_pre_same_struct in e0.
        unfold MarkingHaveSameStruct in e0.
        rewrite <- e0.
        auto.
    (* Case spn_fire_pre = None, impossible regarding the hypotheses. *)
    - cut (In pgroup (pgroup :: pgroups_tail)).
      + intro.
        generalize (H pgroup H1).
        intro.
        generalize (spn_fire_pre_no_error lneighbours pre test inhib steadym decreasingm pgroup H2 H0).
        intro; elim H3; intros; rewrite H4 in e0; inversion e0.
      + apply in_eq. 
  Qed.

  (* Lemma : Proves that spn_map_fire_pre_aux preserves
   *         the structure of the marking decreasingm
   *         passed as argument. 
   *)
  Lemma spn_map_fire_pre_aux_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (pre_fired_transitions : list trans_type)
           (priority_groups : list (list trans_type))
           (final_pre_fired : list trans_type)
           (intermediatem : marking_type),
      spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm pre_fired_transitions priority_groups =
      Some (final_pre_fired, intermediatem) ->
      MarkingHaveSameStruct decreasingm intermediatem.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pre_fired_transitions
           priority_groups.
    functional induction (spn_map_fire_pre_aux lneighbours
                                               pre test inhib
                                               steadym decreasingm
                                               pre_fired_transitions priority_groups)
               using spn_map_fire_pre_aux_ind;
    intros.
    - injection H; intros.
      rewrite H0.
      unfold MarkingHaveSameStruct; auto.
    - apply IHo in H.
      apply spn_fire_pre_same_struct in e0.
      unfold MarkingHaveSameStruct.
      unfold MarkingHaveSameStruct in e0.
      unfold MarkingHaveSameStruct in H.
      rewrite <- H; rewrite e0; auto.
    - inversion H.
  Qed.
  
  (*  
   * Lemma : If all transitions in priority_groups are in lneighbours
   *         and all transitions in pre_fired_transitions are in
   *         lneighbours then all transitions in final_pre_fired 
   *         are in lneighbours.
   *)
  Lemma spn_map_fire_pre_aux_final_fired_in_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (pre_fired_transitions : list trans_type)
           (priority_groups : list (list trans_type))
           (final_pre_fired : list trans_type)
           (intermediatem : marking_type),
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      incl pre_fired_transitions (fst (split lneighbours)) ->
      spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm pre_fired_transitions priority_groups =
      Some (final_pre_fired, intermediatem) ->
      incl final_pre_fired (fst (split lneighbours)).
  Proof.
    unfold PriorityGroupsAreRefInLneighbours.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm pre_fired_transitions priority_groups.
    functional induction (spn_map_fire_pre_aux lneighbours pre test inhib
                                               steadym decreasingm
                                               pre_fired_transitions priority_groups)
               using spn_map_fire_pre_aux_ind;
    intros.
    (* Base case, priority_groups = []. *)
    - injection H1; intros.
      rewrite <- H4 in H2; apply H0 in H2; auto.
    (* Case spn_fire_pre returns Some value. *)
    - apply IHo with (final_pre_fired := final_pre_fired)
                     (intermediatem := intermediatem).
      + intros.
        apply (in_cons pgroup) in H3.
        generalize (H pgroup0 H3); intros.
        apply H5 in H4; auto.
      + intros.
        generalize (H pgroup); intros.
        apply in_eq_impl in H4.
        generalize (spn_fire_pre_final_fired_in_lneighbours
                      lneighbours pre test inhib
                      steadym decreasingm
                      pgroup
                      pre_fired_trs
                      decreasedm H4 e0).
        intros.
        apply in_app_or in H3; elim H3; intros;
          [apply H0 in H6; auto | apply H5 in H6; auto].
      + auto.
      + auto.
    (* Case spn_fire_pre returns an error,
     * then contradiction.
     *)
    - inversion H1.
  Qed.

  (*  
   * Lemma : If there are no duplicates in marking decreasingm
   *         then spn_map_fire_pre_aux returns a marking with no 
   *         duplicates.
   *)
  Lemma spn_map_fire_pre_aux_nodup :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (pre_fired_transitions : list trans_type)
           (priority_groups : list (list trans_type))
           (final_pre_fired : list trans_type)
           (intermediatem : marking_type),
      NoDup (fst (split decreasingm)) ->
      spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                           pre_fired_transitions priority_groups =
      Some (final_pre_fired, intermediatem) ->
      NoDup (fst (split intermediatem)).
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pre_fired_transitions priority_groups.
    functional induction (spn_map_fire_pre_aux lneighbours pre test inhib
                                               steadym decreasingm
                                               pre_fired_transitions priority_groups)
               using spn_map_fire_pre_aux_ind;
    intros.
    (* Base case priority_groups = [] *)
    - injection H0; intros; rewrite <- H1; auto.
    (* Case spn_fire_pre returns Some value. *)
    - apply IHo with (final_pre_fired := final_pre_fired).
      + apply (spn_fire_pre_nodup lneighbours pre test inhib steadym decreasingm pgroup
                                  pre_fired_trs decreasedm H e0).
      + auto.
    (* Case spn_fire_pre returns None. *)
    - inversion H0.
  Qed.  
  
  (***********************************************************************)
  (***********************************************************************)
  
  (*
   * Function : Wrapper around spn_map_fire_pre_aux function. 
   *            Update the marking by consuming
   *            the tokens in pre-condition places.            
   *)
  Definition spn_map_fire_pre
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib : weight_type)
             (m : marking_type)
             (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) :=
    spn_map_fire_pre_aux lneighbours pre test inhib m m [] priority_groups.

  Functional Scheme spn_map_fire_pre_ind := Induction for spn_map_fire_pre Sort Prop.
  
  (*** Formal specification : spn_map_fire_pre ***)
  Inductive SpnMapFirePre
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type)
            (m : marking_type)
            (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) -> Prop :=
  | SpnMapFirePre_cons :
      forall (option_final_couple : option (list trans_type * marking_type)),
        SpnMapFirePreAux lneighbours pre test inhib m m [] priority_groups
                         option_final_couple ->
        SpnMapFirePre lneighbours pre test inhib m priority_groups option_final_couple.

  (*** Correctness proof : spn_map_fire_pre ***)
  Theorem spn_map_fire_pre_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      spn_map_fire_pre lneighbours pre test inhib m priority_groups = option_final_couple ->
      SpnMapFirePre lneighbours pre test inhib m priority_groups option_final_couple.  
  Proof.
    intros lneighbours pre test inhib m priority_groups option_final_couple H.
    apply SpnMapFirePre_cons.
    apply spn_map_fire_pre_aux_correct.
    auto.
  Qed.

  (*** Completeness proof : spn_map_fire_pre ***)
  Theorem spn_map_fire_pre_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      SpnMapFirePre lneighbours pre test inhib m priority_groups
                    option_final_couple ->
      spn_map_fire_pre lneighbours pre test inhib m priority_groups = option_final_couple.
  Proof.
    intros lneighbours pre test inhib m priority_groups option_final_couple H.
    elim H; intros.
    unfold spn_map_fire_pre.
    apply spn_map_fire_pre_aux_compl; auto.
  Qed.

  (*
   * Lemma : spn_map_fire_pre returns no error if 
   *         forall pgroup of transitions in priority_groups,
   *         transitions are referenced in lneighbours and
   *         neighbours places (of these transitions) are referenced 
   *         in markings steadym and decreasingm.
   *)
  Lemma spn_map_fire_pre_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (priority_groups : list (list trans_type)),
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      exists v : (list trans_type * marking_type),
        spn_map_fire_pre lneighbours pre test inhib m priority_groups = Some v.
  Proof.
    intros lneighbours pre test inhib m priority_groups.
    unfold spn_map_fire_pre; intros.
    apply spn_map_fire_pre_aux_no_error; [ auto | auto ].
  Qed.

  (* Lemma : Proves that spn_map_fire_pre preserves
   *         the structure of the marking m
   *         passed as argument. 
   *)
  Lemma spn_map_fire_pre_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (priority_groups : list (list trans_type))
           (final_pre_fired : list trans_type)
           (intermediatem : marking_type),
      spn_map_fire_pre lneighbours pre test inhib m priority_groups =
      Some (final_pre_fired, intermediatem) ->
      MarkingHaveSameStruct m intermediatem.
  Proof.
    intros lneighbours pre test inhib m priority_groups.
    functional induction (spn_map_fire_pre lneighbours pre test inhib m priority_groups)
               using spn_map_fire_pre_ind;
    intros.
    apply spn_map_fire_pre_aux_same_struct in H; auto.
  Qed.
  
  (*  
   * Lemma : If all transitions in priority_groups are in lneighbours
   *         then all transitions in final_pre_fired are in lneighbours.
   *)
  Lemma spn_map_fire_pre_final_fired_in_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (priority_groups : list (list trans_type))
           (final_pre_fired : list trans_type)
           (intermediatem : marking_type),
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      spn_map_fire_pre lneighbours pre test inhib m priority_groups =
      Some (final_pre_fired, intermediatem) ->
      incl final_pre_fired (fst (split lneighbours)).
  Proof.
    unfold PriorityGroupsAreRefInLneighbours.
    unfold incl.
    intros lneighbours pre test inhib m priority_groups.
    functional induction (spn_map_fire_pre lneighbours pre test inhib m priority_groups)
               using spn_map_fire_pre_ind;
    intros.
    cut (forall t : trans_type, In t [] -> In t (fst (split lneighbours))); intros.
    - generalize (spn_map_fire_pre_aux_final_fired_in_lneighbours
                    lneighbours pre test inhib m m [] priority_groups
                    final_pre_fired intermediatem
                    H H2 H0).
      intros.
      apply H3 in H1; auto.
    - elim H2.
  Qed.

  (*  
   * Lemma : If there are no duplicates in marking m
   *         then spn_map_fire_pre returns a marking
   *         with no duplicates.
   *)
  Lemma spn_map_fire_pre_nodup :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (priority_groups : list (list trans_type))
           (final_pre_fired : list trans_type)
           (intermediatem : marking_type),
      NoDup (fst (split m)) ->
      spn_map_fire_pre lneighbours pre test inhib m priority_groups =
      Some (final_pre_fired, intermediatem) ->
      NoDup (fst (split intermediatem)).
  Proof. 
    intros lneighbours pre test inhib m priority_groups.
    functional induction (spn_map_fire_pre lneighbours pre test inhib m priority_groups)
               using spn_map_fire_pre_ind;
    intros.
    apply (spn_map_fire_pre_aux_nodup lneighbours pre test inhib m m [] priority_groups
                                      final_pre_fired intermediatem H H0). 
  Qed.
  
  (***********************************************************************)
  (***********************************************************************)
  
  (* 
   * Function : Returns a marking resulting of the update of the marking 
   *            for all post places related to the transitions contained in 
   *            the pre_fired_transitions list.
   *)
  Fixpoint fire_post
           (lneighbours : list (trans_type * neighbours_type))
           (post : weight_type)
           (increasingm : marking_type)
           (pre_fired_transitions : list trans_type) : option marking_type :=
    match pre_fired_transitions with
    | t :: tail  =>
      match get_neighbours lneighbours t with
      (* Updates the marking
       * for all neighbour post places of t. *)
      | Some neighbours_t =>
        match update_marking_post t post increasingm (post_pl neighbours_t) with
        | Some new_marking => (fire_post lneighbours post new_marking tail)
        (* Something went wrong, case of error. *)
        | None => None
        end
      (* If transition t has no neighbours, then error. *)
      | None => None
      end
    | []  => Some increasingm
    end.

  (*** Formal specification : fire_post ***)
  Inductive FirePost
            (lneighbours : list (trans_type * neighbours_type))
            (post : weight_type) 
            (increasingm : marking_type) :
    list trans_type -> option marking_type -> Prop :=
  (* Case pre_fired_transitions = [] *)
  | FirePost_nil :
      FirePost lneighbours post increasingm [] (Some increasingm)
  (* Case get_neighbours returns an error *)
  | FirePost_neighbours_err :
      forall (t : trans_type) (pre_fired_transitions : list trans_type),
        GetNeighbours lneighbours t None ->
        FirePost lneighbours post increasingm (t :: pre_fired_transitions) None
  (* General case *)
  | FirePost_cons :
      forall (t : trans_type)
             (neighbours_t : neighbours_type)
             (pre_fired_transitions : list trans_type)
             (modifiedm : marking_type)
             (optionm : option marking_type),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        UpdateMarkingPost t post increasingm (post_pl neighbours_t) (Some modifiedm) ->
        FirePost lneighbours post modifiedm pre_fired_transitions optionm ->
        FirePost lneighbours post increasingm (t :: pre_fired_transitions) optionm
  (* Case update_marking_post returns an error. *)
  | FirePost_update_err :
      forall (t : trans_type)
             (neighbours_t : neighbours_type)
             (pre_fired_transitions : list trans_type),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        UpdateMarkingPost t post increasingm (post_pl neighbours_t) None ->
        FirePost lneighbours post increasingm (t :: pre_fired_transitions) None.

  Functional Scheme fire_post_ind := Induction for fire_post Sort Prop.
  
  (*** Correctness proof : fire_post ***)
  Theorem fire_post_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (post : weight_type) 
           (increasingm : marking_type) 
           (pre_fired_transitions : list trans_type)
           (optionm : option marking_type),
      fire_post lneighbours post increasingm pre_fired_transitions = optionm ->
      FirePost lneighbours post increasingm pre_fired_transitions optionm.
  Proof.
    intros lneighbours post increasingm pre_fired_transitions optionm;
      functional induction (fire_post lneighbours post increasingm pre_fired_transitions)
                 using fire_post_ind;
      intros.
    (* Case fired_pre_group = [] *)
    - rewrite <- H; apply FirePost_nil; auto.
    (* General case. *)
    - apply FirePost_cons with (neighbours_t := neighbours_t)
                               (modifiedm := new_marking).
      + apply get_neighbours_correct; auto.
      + apply update_marking_post_correct; auto.
      + apply IHo; rewrite <- H; auto.
    (* Case update_marking_post returns an error. *)
    - rewrite <- H; apply FirePost_update_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply update_marking_post_correct; auto.
    (* Case get_neighbours returns an error. *)
    - rewrite <- H; apply FirePost_neighbours_err.
      apply get_neighbours_correct; auto.
  Qed.

  (*** Completeness proof : fire_post ***)
  Theorem fire_post_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (post : weight_type) 
           (increasingm : marking_type) 
           (pre_fired_transitions : list trans_type)
           (optionm : option marking_type),
      FirePost lneighbours post increasingm pre_fired_transitions optionm ->
      fire_post lneighbours post increasingm pre_fired_transitions = optionm.
  Proof.
    intros lneighbours post increasingm pre_fired_transitions optionm H;
      elim H;
      intros.
    (* Case FirePost_nil *)
    - simpl; auto.
    (* Case FirePost_neighbours_err *)
    - simpl; apply get_neighbours_compl in H0; rewrite H0; auto.
    (* General case *)
    - simpl.
      apply get_neighbours_compl in H0; rewrite H0.
      apply update_marking_post_compl in H1; rewrite H1; auto.
    (* Case FirePost_update_err *)
    - simpl.
      apply get_neighbours_compl in H0; rewrite H0.
      apply update_marking_post_compl in H1; rewrite H1; auto.
  Qed.

  (* Lemma : fire_post returns no error if 
   *         all transition t in pre_fired_transitions are referenced in lneighbours
   *         and if all neighbour places referenced in lneighbours are
   *         referenced in the markings increasingm. 
   *)
  Lemma fire_post_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (post : weight_type) 
           (increasingm : marking_type) 
           (pre_fired_transitions : list trans_type),
      incl pre_fired_transitions (fst (split lneighbours)) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          incl neighbours.(post_pl) (fst (split increasingm))) ->
      exists v : marking_type,
        fire_post lneighbours post increasingm pre_fired_transitions = Some v.
  Proof.
    unfold incl.
    intros lneighbours post increasingm pre_fired_transitions.
    functional induction (fire_post lneighbours post increasingm pre_fired_transitions)
               using fire_post_ind;
      intros.
    (* Base case, pre_fired_transitions = []. *)
    - exists increasingm; auto.
    (* Case update_marking_post = Some m. *)
    - apply IHo.
      + intros.
        apply (in_cons t) in H1.
        apply (H a) in H1; auto.
      + intros.
        generalize (H0 t0 neighbours H1); intro.
        apply (H3 a) in  H2.
        apply update_marking_post_same_struct in e1.
        unfold MarkingHaveSameStruct in e1.
        rewrite <- e1; auto.
    (* Case update_marking_post = None,
     * impossible regarding hypothesis.
     *)
    - cut (In t (t :: tail)); intros.
      + apply get_neighbours_in in e0.
        generalize ((H0 t neighbours_t) e0).
        intros.        
        apply (update_marking_post_no_error t post (post_pl neighbours_t) increasingm) in H2.
        elim H2; intros.
        rewrite H3 in e1; inversion e1.
      + apply in_eq.
    (* Case get_neighbours = None, 
     * impossible regarding the hypotheses.
     *)
    - cut (In t (t :: tail)); intros.
      + apply H in H1.
        apply get_neighbours_no_error in H1.
        elim H1; intros.
        rewrite H2 in e0; inversion e0.
      + apply in_eq.
  Qed.

  (*  
   * Lemma : If there are no duplicates in marking m
   *         then fire_post returns a marking
   *         with no duplicates.
   *)
  Lemma fire_post_nodup :
    forall (lneighbours : list (trans_type * neighbours_type))
           (post : weight_type) 
           (increasingm : marking_type) 
           (pre_fired_transitions : list trans_type)
           (increasedm : marking_type),
      NoDup (fst (split increasingm)) ->
      fire_post lneighbours post increasingm pre_fired_transitions =
      Some increasedm ->
      NoDup (fst (split increasedm)).
  Proof.
    intros lneighbours post increasingm pre_fired_transitions.
    functional induction (fire_post lneighbours post increasingm pre_fired_transitions)
               using fire_post_ind;
    intros.
    (* Base case pre_fired_transitions = [] *)
    - injection H0; intros; rewrite <- H1; auto.
    (* Case update_marking_post returns Some value. *)
    - apply IHo.
      + apply (update_marking_post_nodup t post (post_pl neighbours_t) increasingm
                                         new_marking H e1).
      + auto.
    (* Case update_marking_post returns None. *)
    - inversion H0.
    (* Case get_neighbours = None. *)
    - inversion H0.
  Qed.

  (* Lemma : Proves that fire_post preserves
   *         the structure of the marking increasingm
   *         passed as argument. 
   *)
  Lemma fire_post_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (post : weight_type) 
           (increasingm : marking_type) 
           (pre_fired_transitions : list trans_type)
           (increasedm : marking_type),
      fire_post lneighbours post increasingm pre_fired_transitions =
      Some increasedm ->
      MarkingHaveSameStruct increasingm increasedm.
  Proof.
    intros lneighbours post increasingm pre_fired_transitions.
    functional induction (fire_post lneighbours post increasingm pre_fired_transitions)
               using fire_post_ind;
    intros.
    (* Base case pre_fired_transitions = []. *)
    - injection H; intros.
      rewrite H0.
      unfold MarkingHaveSameStruct; auto.
    (* Case update_marking_post returns Some value. *)
    - apply IHo in H.
      apply update_marking_post_same_struct in e1.
      unfold MarkingHaveSameStruct.
      unfold MarkingHaveSameStruct in e1.
      unfold MarkingHaveSameStruct in H.
      rewrite <- H; rewrite e1; auto.
    (* Case update_marking_post returns None. *)
    - inversion H.
    (* Case get_neighbours returns None. *)
    - inversion H.
  Qed.  
  
  (*************************************************)
  (****************** SPN FIRE *********************)
  (*************************************************)

  (*
   * Function : Returns  "fired transitions" + "final marking",
   *            composing fire_post with spn_map_fire_pre
   *)
  Definition spn_fire
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib post : weight_type)
             (steadym : marking_type)
             (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) :=
    (* Pre-fires the transitions in priority_groups. *)
    match spn_map_fire_pre lneighbours pre test inhib steadym priority_groups with 
    | Some (pre_fired_transitions, intermediatem) =>
      (* Post-fires the pre-fired transitions. *)
      match fire_post lneighbours post intermediatem pre_fired_transitions with
      | Some finalm => Some (pre_fired_transitions, finalm)
      (* If fire_post returned an error, then error. *)
      | None => None
      end
    (* If spn_map_fire_pre returned an error, then error. *)
    | None => None
    end.

  Functional Scheme spn_fire_ind := Induction for spn_fire Sort Prop.
  
  (*** Formal specification : spn_fire ***)
  Inductive SpnFire
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib post : weight_type)
            (steadym : marking_type)
            (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) -> Prop :=
  (* General case *)
  | SpnFire_cons :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem finalm : marking_type),
        SpnMapFirePre lneighbours pre test inhib steadym priority_groups
                      (Some (pre_fired_transitions, intermediatem)) ->
        FirePost lneighbours post intermediatem pre_fired_transitions (Some finalm) ->
        SpnFire lneighbours pre test inhib post steadym priority_groups
                (Some (pre_fired_transitions, finalm))
  (* Case spn_map_fire_pre returns an error. *)
  | SpnFire_map_fire_pre_err :
      SpnMapFirePre lneighbours pre test inhib steadym priority_groups None ->
      SpnFire lneighbours pre test inhib post steadym priority_groups None
  (* Case fire_post returns an error. *)
  | SpnFire_fire_post_err :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type),
        SpnMapFirePre lneighbours pre test inhib steadym priority_groups
                      (Some (pre_fired_transitions, intermediatem)) ->
        FirePost lneighbours post intermediatem pre_fired_transitions None ->
        SpnFire lneighbours pre test inhib post steadym priority_groups None.

  (*** Correctness proof : spn_fire ***)
  Theorem spn_fire_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib post : weight_type)
           (steadym : marking_type)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      spn_fire lneighbours pre test inhib post steadym priority_groups = option_final_couple ->
      SpnFire lneighbours pre test inhib post steadym priority_groups option_final_couple.
  Proof.
    intros lneighbours pre test inhib post steadym priority_groups option_final_couple;
      functional induction (spn_fire lneighbours pre test inhib post steadym priority_groups)
                 using spn_fire_ind;
      intros.
    (* General case *)
    - rewrite <- H; apply SpnFire_cons with (intermediatem := intermediatem).
      + apply spn_map_fire_pre_correct; auto.
      + apply fire_post_correct; auto.
    (* Case fire_post returns an error. *)
    - rewrite <- H; apply SpnFire_fire_post_err
                      with (pre_fired_transitions := pre_fired_transitions)
                           (intermediatem := intermediatem).
      + apply spn_map_fire_pre_correct; auto.
      + apply fire_post_correct; auto.
    (* Case spn_map_fire_pre returns an error. *)
    - rewrite <- H; apply SpnFire_map_fire_pre_err.
      apply spn_map_fire_pre_correct; auto.                             
  Qed.

  (*** Completeness proof : spn_fire ***)
  Theorem spn_fire_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib post : weight_type)
           (steadym : marking_type)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      SpnFire lneighbours pre test inhib post steadym priority_groups option_final_couple ->
      spn_fire lneighbours pre test inhib post steadym priority_groups = option_final_couple.
  Proof.
    intros lneighbours pre test inhib post steadym priority_groups option_final_couple Hspec.
    elim Hspec; intros; unfold spn_fire.
    (* Case SpnFire_cons *)
    + apply spn_map_fire_pre_compl in H; rewrite H.
      apply fire_post_compl in H0; rewrite H0; auto.
    (* Case SpnFire_map_fire_pre_err *)
    + apply spn_map_fire_pre_compl in H; rewrite H; auto.
    (* Case SpnFire_fire_post_err *)
    + apply spn_map_fire_pre_compl in H; rewrite H.
      apply fire_post_compl in H0; rewrite H0; auto.
  Qed.

  (* Lemma : spn_fire always returns some value
   *         
   *)
  Lemma spn_fire_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib post : weight_type)
           (m : marking_type)
           (priority_groups : list (list trans_type)),
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          incl neighbours.(post_pl) (fst (split m))) ->
      exists v : (list trans_type * marking_type),
        spn_fire lneighbours pre test inhib post m priority_groups = Some v.
  Proof.
    unfold PriorityGroupsAreRefInLneighbours.
    unfold incl.
    intros lneighbours pre test inhib post m priority_groups.
    functional induction (spn_fire lneighbours pre test inhib post m priority_groups)
               using spn_fire_ind;
    intros.
    (* General case, spn_map_fire_pre and fire_post 
     * both returned Some value.
     *)
    - exists (pre_fired_transitions, finalm); auto.
    (* Case fire_post returns None, 
     * impossible according to the hypotheses.
     *)
    (* First we need the hypothesis that said that
     * all transitions in the list pre_fired_transitions
     * are referenced in lneighbours.
     *)
    - generalize (spn_map_fire_pre_final_fired_in_lneighbours
                    lneighbours
                    pre test inhib m priority_groups
                    pre_fired_transitions intermediatem
                    H e).
      intros.
      (* Then we need transform our hypotheses,  
       * using the fact that intermediate marking
       * have the same structure as the first marking.
       *)
      apply spn_map_fire_pre_same_struct in e.
      unfold MarkingHaveSameStruct in e.
      rewrite e in H1.
      generalize (fire_post_no_error lneighbours post intermediatem pre_fired_transitions H2 H1).
      intros.
      elim H3; intros.
      rewrite H4 in e1.
      inversion e1.
    (* Case spn_map_fire_pre returns None,
     * impossible according to the hypotheses.
     *)
    - generalize (spn_map_fire_pre_no_error lneighbours pre test inhib m priority_groups
                                            H H0).
      intros.
      elim H2; intros.
      rewrite H3 in e.
      inversion e.
  Qed.

  (* 
   * Lemma : If there are no duplicates in marking m,
   *         then spn_fire returns a marking with no duplicates.
   *)
  Lemma spn_fire_nodup :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib post : weight_type)
           (m : marking_type)
           (priority_groups : list (list trans_type))
           (fired_transitions : list (trans_type))
           (newm : marking_type),
      NoDup (fst (split m)) ->
      spn_fire lneighbours pre test inhib post m priority_groups =
      Some (fired_transitions, newm) ->
      NoDup (fst (split newm)).
  Proof.
    intros lneighbours pre test inhib post m priority_groups.
    functional induction (spn_fire lneighbours pre test inhib post m priority_groups)
               using spn_fire_ind;
    intros.
    (* General case, all went well. *)
    - injection H0; intros; rewrite <- H1; auto.
      generalize (spn_map_fire_pre_nodup lneighbours pre test inhib m priority_groups
                                         pre_fired_transitions intermediatem
                                         H e); intro.
      apply (fire_post_nodup lneighbours post intermediatem pre_fired_transitions
                             finalm H3 e1).
    (* Case fire_post returns None. *)
    - inversion H0.
    (* Case spn_map_fire_pre returns None. *)
    - inversion H0.
  Qed.

  (* Lemma : Proves that spn_fire preserves
   *         the structure of the marking m
   *         passed as argument. 
   *)  
  Lemma spn_fire_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib post : weight_type)
           (m : marking_type)
           (priority_groups : list (list trans_type))
           (fired_transitions : list (trans_type))
           (newm : marking_type),
      spn_fire lneighbours pre test inhib post m priority_groups =
      Some (fired_transitions, newm) ->
      MarkingHaveSameStruct m newm.
  Proof.
    intros lneighbours pre test inhib post m priority_groups.
    functional induction (spn_fire lneighbours pre test inhib post m priority_groups)
               using spn_fire_ind;
    intros.
    - injection H; intros; rewrite <- H0; auto.
      generalize (spn_map_fire_pre_same_struct lneighbours pre test inhib m priority_groups
                                               pre_fired_transitions intermediatem
                                               e); intro.
      generalize (fire_post_same_struct lneighbours post intermediatem pre_fired_transitions
                                        finalm e1); intro.
      unfold MarkingHaveSameStruct in H2; unfold MarkingHaveSameStruct in H3.
      unfold MarkingHaveSameStruct.
      rewrite H2; rewrite H3; auto.
    - inversion H.
    - inversion H.
  Qed.
  
End FireSpn.

(*==========================================================*)
(*================= SPN CYCLE EVOLUTION ====================*)
(*==========================================================*)

Section AnimateSpn.
  
  (*  
   * Function : Returns the resulting Petri net after all the sensitized
   *            transitions in spn have been fired, and returns
   *            the list of transitions fired in this cycle.
   *
   *)
  Definition spn_cycle (spn : SPN) : option (list trans_type * SPN) :=
    match spn with
    | (mk_SPN places transs pre post test inhib m priority_groups lneighbours) =>
      match (spn_fire lneighbours pre test inhib post m priority_groups) with
      | Some (fired_transitions, nextm) =>
        Some (fired_transitions,
              (mk_SPN places transs pre post test inhib nextm priority_groups lneighbours))
      | None => None
      end
    end.

  (*** Formal specification : SpnCycle ***)
  Inductive SpnCycle (spn : SPN) :
    option (list trans_type * SPN) -> Prop :=
  (* General case *)
  | SpnCycle_cons :
      forall (places : list place_type)
             (transs : list trans_type)
             (pre post test inhib : weight_type)
             (m nextm : marking_type)
             (priority_groups : list (list trans_type))
             (lneighbours : list (trans_type * neighbours_type))
             (fired_transitions : list trans_type),
        spn = (mk_SPN places transs pre post test inhib m priority_groups lneighbours) ->
        SpnFire lneighbours pre test inhib post m priority_groups
                (Some (fired_transitions, nextm)) ->
        SpnCycle spn (Some (fired_transitions,
                            (mk_SPN places transs pre post test inhib nextm
                                    priority_groups lneighbours)))
  (* Case spn_fire returns an error. *)
  | SpnCycle_err :
      forall (places : list place_type)
             (transs : list trans_type)
             (pre post test inhib : weight_type)
             (m : marking_type)
             (priority_groups : list (list trans_type))
             (lneighbours : list (trans_type * neighbours_type)),
        spn = (mk_SPN places transs pre post test inhib m priority_groups lneighbours) ->
        SpnFire lneighbours pre test inhib post m priority_groups None ->
        SpnCycle spn None.

  Functional Scheme spn_cycle_ind := Induction for spn_cycle Sort Prop.
  
  (*** Correctness proof : spn_cycle ***)
  Theorem spn_cycle_correct :
    forall (spn : SPN)
           (option_final_couple : option (list trans_type * SPN)),
      spn_cycle spn = option_final_couple -> SpnCycle spn option_final_couple.
  Proof.
    intros; functional induction (spn_cycle spn) using spn_cycle_ind; intros.
    rewrite <- H; apply SpnCycle_cons with (m := m).
    (* Base case *)
    - auto.
    (* General case, all went well. *)
    - apply spn_fire_correct; auto.
    (* Error case. *)
    - rewrite <- H; apply SpnCycle_err with (places := places)
                                            (transs := transs)
                                            (pre := pre)
                                            (post := post)
                                            (test := test)
                                            (inhib := inhib)
                                            (m := m)
                                            (priority_groups := priority_groups)
                                            (lneighbours := lneighbours).
      + auto.
      + apply spn_fire_correct; auto.
  Qed.

  (*** Completeness proof : spn_cycle ***)
  Theorem spn_cycle_compl :
    forall (spn : SPN)
           (option_final_couple : option (list trans_type * SPN)),
      SpnCycle spn option_final_couple -> spn_cycle spn = option_final_couple.
  Proof.
    intros; elim H; intros.
    unfold spn_cycle; rewrite H0.
    apply spn_fire_compl in H1; rewrite H1.
    (* SpnCycle_cons *)
    + auto.
    (* SpnCycle_err *)
    + unfold spn_cycle; rewrite H0.
      apply spn_fire_compl in H1; rewrite H1; auto.
  Qed.

  (*  
   * Lemma : For all spn with properties NoUnknownInPriorityGroups
   *         and NoUnknownTransInLNeighbours then transitions
   *         in spn.(priority_groups) are referenced in spn.(lneighbours).
   *         
   *         Useful to apply spn_fire_no_error while proving spn_cycle_no_error.
   *)
  Lemma priority_groups_in_lneighbours :
    forall (spn : SPN),
      NoUnknownInPriorityGroups spn ->
      NoUnknownTransInLNeighbours spn ->
      PriorityGroupsAreRefInLneighbours spn.(priority_groups) spn.(lneighbours).
  Proof.
    unfold NoUnknownInPriorityGroups.
    unfold NoUnknownTransInLNeighbours.
    unfold PriorityGroupsAreRefInLneighbours.
    intros.
    generalize (in_concat t pgroup (priority_groups spn) H2 H1); intro.
    rewrite <- H in H3.
    rewrite H0 in H3.
    auto.
  Qed.

  Lemma incl_places_flatten_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
           (t : trans_type)
           (neighbours : neighbours_type),
      In (t, neighbours) lneighbours ->
      (forall p : place_type, (In p (pre_pl neighbours) \/
                               In p (test_pl neighbours) \/
                               In p (inhib_pl neighbours) \/
                               In p (post_pl neighbours)) ->
                              In p (flatten_lneighbours lneighbours)).
  Proof.
    intros lneighbours.
    functional induction (flatten_lneighbours lneighbours) using flatten_lneighbours_ind; intros.
    - inversion H.
    - apply in_or_app.
      apply in_inv in H.
      elim H; intros.
      + injection H1; intros.
        rewrite H2.
        left.
        unfold flatten_neighbours.
        decompose [or] H0.
        -- apply in_or_app; left; auto.
        -- apply in_or_app; right; apply in_or_app; left; auto.
        -- do 2 (apply in_or_app; right); apply in_or_app; left; auto.
        -- do 3 (apply in_or_app; right); auto.
      + right.
        apply IHl with (t := t) (neighbours := neighbours); auto.
  Qed.
  
    (*  
   * Lemma : For all spn with properties NoUnmarkedPlace and NoUnknownPlaceInNeighbours
   *         then pre-places referenced in spn.(lneighbours) are referenced in spn.(marking).
   *
   *         Useful to apply spn_fire_no_error while proving spn_cycle_no_error.
   *)
  Lemma pre_places_in_marking :
    forall (spn : SPN),
      NoUnmarkedPlace spn ->
      NoUnknownPlaceInNeighbours spn ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) spn.(lneighbours) ->
          incl neighbours.(pre_pl) (fst (split spn.(marking))) /\
          incl neighbours.(inhib_pl) (fst (split spn.(marking))) /\
          incl neighbours.(test_pl) (fst (split spn.(marking)))).
  Proof.
    unfold incl.
    intros.
    unfold NoUnmarkedPlace in H.
    unfold NoUnknownPlaceInNeighbours in H0.
    unfold incl in H0.
    generalize (incl_places_flatten_lneighbours (lneighbours spn) t neighbours H1); intro.
    split.
    - intros.
      apply or_introl with (B := (In a (test_pl neighbours) \/
                                  In a (inhib_pl neighbours) \/
                                  In a (post_pl neighbours))) in H3. 
      generalize (H2 a H3); intro.
      apply H0 in H4.
      rewrite H in H4; auto.
    - split; intros.
      + apply or_introl with (B := In a (post_pl neighbours)) in H3.
        apply or_intror with (A := In a (test_pl neighbours)) in H3.
        apply or_intror with (A := In a (pre_pl neighbours)) in H3.
        generalize (H2 a H3); intro.
        apply H0 in H4.
        rewrite H in H4; auto.
      + apply or_introl with (B := In a (inhib_pl neighbours) \/ In a (post_pl neighbours)) in H3.
        apply or_intror with (A := In a (pre_pl neighbours)) in H3.
        generalize (H2 a H3); intro.
        apply H0 in H4.
        rewrite H in H4; auto.
  Qed.

  (*  
   * Lemma : forall spn with properties NoUnmarkedPlace and NoUnknownPlaceInNeighbours
   *         then post-places referenced in spn.(lneighbours) are referenced in spn.(marking).
   *
   *         Useful to apply spn_fire_no_error while proving spn_cycle_no_error.
   *)
  Lemma post_places_in_marking :
    forall (spn : SPN),
      NoUnmarkedPlace spn ->
      NoUnknownPlaceInNeighbours spn ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) spn.(lneighbours) ->
          incl neighbours.(post_pl) (fst (split spn.(marking)))).
  Proof.
    unfold incl.
    intros.
    unfold NoUnmarkedPlace in H.
    unfold NoUnknownPlaceInNeighbours in H0.
    unfold incl in H0.
    generalize (incl_places_flatten_lneighbours spn.(lneighbours) t neighbours H1); intro.
    apply or_intror with (A := In a (inhib_pl neighbours)) in H2.
    apply or_intror with (A := In a (test_pl neighbours)) in H2.
    apply or_intror with (A := In a (pre_pl neighbours)) in H2.
    generalize (H3 a H2); intro.
    apply H0 in H4.
    rewrite H in H4; auto.
  Qed.
  
  (*  
   * Theorem : For all spn verifying the property IsWellStructuredSpn,
   *           spn_cycle spn returns no error.
   *)
  Theorem spn_cycle_no_error :
    forall (spn : SPN),
      IsWellStructuredSpn spn ->
      exists value : list trans_type * SPN, spn_cycle spn = Some value.
  Proof.
    unfold IsWellStructuredSpn.
    intro.
    functional induction (spn_cycle spn) using spn_cycle_ind.
    (* Case all went well, spn_fire returns Some value. *)
    - exists ((fired_transitions, {| places := places;
                                     transs := transs;
                                     pre := pre;
                                     post := post;
                                     test := test;
                                     inhib := inhib;
                                     marking := nextm;
                                     priority_groups := priority_groups;
                                     lneighbours := lneighbours |})).
      auto.
    (* Case spn_fire returns None, impossible
     * regarding the hypotheses.
     *)
    - set (spn := {| places := places;
                     transs := transs;
                     pre := pre;
                     post := post;
                     test := test;
                     inhib := inhib;
                     marking := m;
                     priority_groups := priority_groups;
                     lneighbours := lneighbours |}).
      intros.
      decompose [and] H; clear H.
      generalize (priority_groups_in_lneighbours spn H1 H7); intro.
      generalize (pre_places_in_marking spn H10 H6); intro.
      generalize (post_places_in_marking spn H10 H6); intro.
      generalize (spn_fire_no_error
                    lneighbours pre test inhib post m priority_groups H H9 H11).
      intro.
      elim H12; intros.
      rewrite H13 in e0.
      inversion e0.
  Qed.

  (*  
   * Theorem : For all spn verifying the property IsWellStructuredSpn,
   *           (spn_cycle spn) returns a new spn verifying the relation
   *           IsWellStructuredSpn.
   *)
  Theorem spn_cycle_well_structured :
    forall (spn : SPN)
           (fired_transitions : list trans_type)
           (next_spn : SPN),
      IsWellStructuredSpn spn ->
      spn_cycle spn = Some (fired_transitions, next_spn) ->
      IsWellStructuredSpn next_spn.
  Proof.
    intro.
    functional induction (spn_cycle spn) using spn_cycle_ind; intros.
    (* General case. *)
    - unfold IsWellStructuredSpn.
      unfold IsWellStructuredSpn in H.
      injection H0; clear H0; intros.
      unfold NoUnmarkedPlace.
      unfold NoUnmarkedPlace in H.
      apply spn_fire_same_struct in e0.
      unfold MarkingHaveSameStruct in e0.
      rewrite <- H0.
      simpl.
      rewrite <- e0.
      simpl in H.
      auto.
    (* Case spn_fire returns None. *)
    - inversion H0.
  Qed.
  
  (*******************************************)
  (******** ANIMATING DURING N CYCLES ********)
  (*******************************************)

  (** Returns the list of (fired_transitions(i), SPN(i)) for each cycle i, 
      from 0 to n, representing the evolution of the Petri net [spn]. *)
  
  Fixpoint spn_animate_aux
           (spn : SPN)
           (n : nat)
           (spn_evolution : list (list trans_type * SPN)) :
    option (list (list trans_type * SPN)) :=
    match n with
    | O => Some spn_evolution
    | S n' => match (spn_cycle spn) with
              | Some (fired_trans_at_n, spn_at_n) =>
                spn_animate_aux spn_at_n n' (spn_evolution ++ [(fired_trans_at_n, spn_at_n)])
              (* Case of error!! *)
              | None => None
              end
    end.

  Functional Scheme spn_animate_aux_ind := Induction for spn_animate_aux Sort Prop.
  
  (** Formal specification : spn_animate_aux *)
  
  Inductive SpnAnimateAux (spn : SPN) :
    nat ->
    list (list trans_type * SPN) ->
    option (list (list trans_type * SPN)) ->
    Prop :=
  | SpnAnimateAux_0 :
      forall (spn_evolution : list (list trans_type * SPN)),
        SpnAnimateAux spn 0 spn_evolution (Some spn_evolution) 
  | SpnAnimateAux_cons :
      forall (n : nat)
             (fired_trans_at_n : list trans_type)
             (spn_at_n : SPN)
             (spn_evolution : list (list trans_type * SPN))
             (opt_evolution : option (list (list trans_type * SPN))),
        SpnCycle spn (Some (fired_trans_at_n, spn_at_n)) ->
        SpnAnimateAux spn_at_n
                   n
                   (spn_evolution ++ [(fired_trans_at_n, spn_at_n)])
                   opt_evolution ->
        SpnAnimateAux spn
                   (S n)
                   spn_evolution
                   opt_evolution
  | SpnAnimateAux_err :
      forall (n : nat)
             (spn_evolution : list (list trans_type * SPN)),
        SpnCycle spn None ->
        SpnAnimateAux spn (S n) spn_evolution None.
  
  (** Correctness proof : spn_animate_aux *)
  Theorem spn_animate_aux_correct :
    forall (spn :SPN)
           (n : nat)
           (spn_evolution : list (list trans_type * SPN))
           (opt_evolution : option (list (list trans_type * SPN))),
      spn_animate_aux spn n spn_evolution = opt_evolution ->
      SpnAnimateAux spn n spn_evolution opt_evolution.
  Proof.                                                                                
    intros spn n spn_evolution.
    functional induction (spn_animate_aux spn n spn_evolution) using spn_animate_aux_ind;
    intros.
    (* Case n = 0 *)
    - intros; rewrite <- H; apply SpnAnimateAux_0.
    (* General case *)
    - intros; rewrite <- H.
      apply SpnAnimateAux_cons with (fired_trans_at_n := fired_trans_at_n)
                                 (spn_at_n := spn_at_n).
      + apply spn_cycle_correct in e0; auto.
      + apply IHo; auto.
    (* Error case. *)
    - rewrite <- H; apply SpnAnimateAux_err.
      apply spn_cycle_correct in e0; auto.
  Qed.

  (** Completeness proof : spn_animate_aux *)
  Theorem spn_animate_aux_compl :
    forall (spn :SPN)
           (n : nat)
           (spn_evolution : list (list trans_type * SPN))
           (opt_evolution : option (list (list trans_type * SPN))),
      SpnAnimateAux spn n spn_evolution opt_evolution ->
      spn_animate_aux spn n spn_evolution = opt_evolution.
  Proof.
    intros; elim H; intros.
    (* Case SpnAnimateAux_0 *)
    - simpl; auto.
    (* Case SpnAnimateAux_cons *)
    - simpl. apply spn_cycle_compl in H0; rewrite H0.
      rewrite H2; auto.
    (* Case SpnAnimateAux_err *)
    - apply spn_cycle_compl in H0.
      simpl.
      rewrite H0; auto.
  Qed.

  (** For all spn verifying the property IsWellStructuredSpn,
      and for all number n of evolution cycles, spn_animate_aux returns no error. *)
  
  Theorem spn_animate_aux_no_error :
    forall (spn : SPN)
           (n : nat)
           (spn_evolution : list (list trans_type * SPN)),
      IsWellStructuredSpn spn ->
      exists (v : list ((list trans_type) * SPN)),
        spn_animate_aux spn n spn_evolution = Some v.
  Proof.
    do 3 intro.
    functional induction (spn_animate_aux spn n spn_evolution)
               using spn_animate_aux_ind;
    intros.
    (* Base case, n = 0. *)
    - exists spn_evolution; auto.
    (* General case. *)
    - apply IHo.
      apply (spn_cycle_well_structured spn fired_trans_at_n spn_at_n H e0).
    (* Error case, impossible regarding the hypotheses. *)
    - generalize (spn_cycle_no_error spn H); intro.
      elim H0; intros.
      rewrite H1 in e0; inversion e0.
  Qed.

  (** For all well-structured [SPN] passed to [spn_animate_aux], and for all list of well-structured [SPN]
      spn_evolution, the resulting list is only composed of well-structured [SPN]. *)
  
  Theorem spn_animate_aux_well_structured :
    forall (spn : SPN)
           (n : nat)
           (spn_evolution final_spn_evolution : list (list trans_type * SPN)),
      IsWellStructuredSpn spn ->
      (forall spn' : SPN, In spn' (snd (split spn_evolution)) -> IsWellStructuredSpn spn') ->
      spn_animate_aux spn n spn_evolution = Some final_spn_evolution ->
      forall (spn'' : SPN), In spn'' (snd (split final_spn_evolution)) -> IsWellStructuredSpn spn''.
  Proof.
    do 3 intro.
    functional induction (spn_animate_aux spn n spn_evolution) using spn_animate_aux_ind; intros.
    - injection H1; intros.
      rewrite <- H3 in H2.
      apply (H0 spn'' H2).
    - apply IHo with (final_spn_evolution := final_spn_evolution).
      + generalize (spn_cycle_well_structured spn fired_trans_at_n spn_at_n H e0); intro; auto.
      + intros.
        rewrite snd_split_app in H3.
        apply in_app_or in H3.
        elim H3; intros.
        -- apply (H0 spn' H4).
        -- simpl in H4; elim H4; intros;
           [generalize (spn_cycle_well_structured spn fired_trans_at_n spn_at_n H e0); intro;
            rewrite H5 in H6; assumption
           | elim H5].           
      + auto.
      + auto.
    - inversion H1.
  Qed.

  (** For all well-structured [SPN] passed to [spn_animate_aux], and for all [n], number 
      of evolution cycles, the length of the resulting [final_spn_evolution] list
      is equal to the number of evolution cycles plus the length of the [spn_evolution] 
      list passed in argument. *)
  
  Theorem spn_animate_aux_preserves_cycles :
    forall (spn : SPN)
           (n : nat)
           (spn_evolution final_spn_evolution : list (list trans_type * SPN)),
      IsWellStructuredSpn spn ->
      spn_animate_aux spn n spn_evolution = Some final_spn_evolution ->
      n + length spn_evolution = length final_spn_evolution.
  Proof.
    do 3 intro.
    functional induction (spn_animate_aux spn n spn_evolution) using spn_animate_aux_ind; intros.
    - injection H0; intros; rewrite H1; simpl; auto.
    - generalize (spn_cycle_well_structured spn fired_trans_at_n spn_at_n H e0); intro.
      generalize (IHo final_spn_evolution H1 H0); intro.
      rewrite <- H2.
      rewrite app_length.
      simpl.
      rewrite Nat.add_1_r.
      auto.
    - inversion H0.
  Qed.

  (** ------------------------------------------------------------------------------- *)
  (** ------------------------------------------------------------------------------- *)

  (** Wrapper function around spn_animate_aux. Here, spn_evolution is initialized to nil. *)
  
  Definition spn_animate (spn : SPN) (n : nat) :
    option (list (list trans_type * SPN)) := spn_animate_aux spn n [].

  (** Formal specification : spn_animate *)
  
  Inductive SpnAnimate (spn : SPN) (n : nat) : option (list (list trans_type * SPN)) -> Prop :=
  | SpnAnimate_cons :
      forall (opt_spn_evolution : option (list (list trans_type * SPN))),
        SpnAnimateAux spn n [] opt_spn_evolution ->
        SpnAnimate spn n opt_spn_evolution.

  (** Correctness proof : spn_animate *)
  
  Theorem spn_animate_correct :
    forall (spn : SPN) (n : nat) (opt_spn_evolution : option (list (list trans_type * SPN))),
      spn_animate spn n = opt_spn_evolution ->
      SpnAnimate spn n opt_spn_evolution.
  Proof.
    unfold spn_animate.
    intros.
    apply SpnAnimate_cons; apply spn_animate_aux_correct in H; auto.
  Qed.

  (** Completeness proof : spn_animate *)
  
  Theorem spn_animate_compl :
    forall (spn : SPN) (n : nat) (opt_spn_evolution : option (list (list trans_type * SPN))),
      SpnAnimate spn n opt_spn_evolution ->
      spn_animate spn n = opt_spn_evolution.
  Proof.
    unfold spn_animate.
    intros.
    elim H; apply spn_animate_aux_compl; auto.
  Qed.

  (** For all spn verifying the property IsWellStructuredSpn,
      and for all number n of evolution cycles, spn_animate returns no error. *)
  
  Theorem spn_animate_no_error :
    forall (spn : SPN)
           (n : nat),
      IsWellStructuredSpn spn ->
      exists (v : list ((list trans_type) * SPN)),
        spn_animate spn n = Some v.
  Proof.
    unfold spn_animate.
    intros.
    generalize (spn_animate_aux_no_error spn n [] H); intro.
    elim H0; intros.
    rewrite H1.
    exists x; auto.
  Qed.

  (** For all well-structured [SPN] passed to [spn_animate], the resulting evolution 
      list is only composed of well-structured [SPN]. *)
  
  Theorem spn_animate_well_structured :
    forall (spn : SPN)
           (n : nat)
           (spn_evolution : list (list trans_type * SPN)),
      IsWellStructuredSpn spn ->
      spn_animate spn n = Some spn_evolution ->
      forall (spn' : SPN), In spn' (snd (split spn_evolution)) -> IsWellStructuredSpn spn'.
  Proof.
    unfold spn_animate.
    intros.
    (* We need this hypothesis to apply spn_animate_aux_well_structured. *)
    assert (H' : forall (spn' : SPN), In spn' [] -> IsWellStructuredSpn spn')
      by (intros; elim H2).
    generalize (spn_animate_aux_well_structured spn n [] spn_evolution H H' H0); intros.
    apply H2; assumption.
  Qed.

  (** For all well-structured [SPN] passed to [spn_animate], and for all [n], number 
      of evolution cycles, the length of the resulting [final_spn_evolution] list
      is equal to [n]. *)
  
  Theorem spn_animate_preserves_cycles :
    forall (spn : SPN)
           (n : nat)
           (spn_evolution : list (list trans_type * SPN)),
      IsWellStructuredSpn spn ->
      spn_animate spn n = Some spn_evolution ->
      n = length spn_evolution.
  Proof.
    unfold spn_animate; intros.
    generalize (spn_animate_aux_preserves_cycles spn n [] spn_evolution H H0); intros.
    rewrite Nat.add_0_r in H1.
    assumption.
  Qed.
  
End AnimateSpn.
