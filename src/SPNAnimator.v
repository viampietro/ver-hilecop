Require Import Hilecop.SPN.

(*! ============================================================ !*)
(*! ================ FIRING ALGORITHM for Spn ================== !*)
(*! ============================================================ !*)

Section FireSpn.

  (** Returns [Some true] if [t] is sensitized in marking [marking], 
      [Some false] otherwise. 
                 
      Raises an error if [map_check_pre], [map_check_test], [map_check_inhib] or
      [get_neighbours] fail. *)
  
  Definition is_sensitized
             (spn : Spn)
             (marking : list (Place * nat))
             (neighbours_of_t : Neighbours)
             (t : Trans) : option bool :=    
    match map_check_pre spn marking (pre_pl neighbours_of_t) t with
    | Some check_pre_result =>  
      match map_check_test spn marking (test_pl neighbours_of_t) t with
      | Some check_test_result =>
        match map_check_inhib spn marking (inhib_pl neighbours_of_t) t with
        | Some check_inhib_result =>
          Some (check_pre_result && check_test_result && check_inhib_result)
        (* Case of error!! *)
        | None => None
        end
      (* Case of error!! *)
      | None => None
      end
    (* Case of error!! *)
    | None => None
    end.

  Functional Scheme is_sensitized_ind := Induction for is_sensitized Sort Prop.    
  
  (** Returns true if t ∈ sensitized(residual_marking). 
      [state] is not used in [spn_is_firable], but it is here
      to recall that a transitions is firable at a certain state.
   *)
  
  Definition spn_is_firable
             (spn : Spn)
             (state : SpnState)
             (neighbours_of_t : Neighbours)
             (t : Trans) : option bool :=
    is_sensitized spn state.(marking) neighbours_of_t t.
  
  (** Returns a marking M' where 
      M' = [residual_marking] - ∀ p ∈ [pre_places], ∑ pre(p, t)  *)
  
  Fixpoint update_residual_marking_aux
           (spn : Spn)
           (residual_marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place) {struct pre_places} :
    option (list (Place * nat)) :=
    match pre_places with
    | p :: tail =>
      match modify_m residual_marking p Nat.sub (pre spn t p) with
      | Some residual_marking' =>
        update_residual_marking_aux spn residual_marking' t tail
      (* It's an exception, p is not referenced in spn.(marking). *)
      | None => None
      end
    | [] => Some (residual_marking)
    end.

  Functional Scheme update_residual_marking_aux_ind :=
    Induction for update_residual_marking_aux Sort Prop.

  (** Wrapper around update_residual_marking. *)
  
  Definition update_residual_marking
             (spn : Spn)
             (residual_marking : list (Place * nat))
             (neighbours_of_t : Neighbours)
             (t : Trans) : option (list (Place * nat)) :=
    update_residual_marking_aux spn residual_marking t (pre_pl neighbours_of_t).
    
  (** Returns the list of fired transitions in priority group [pgroup]
      at the current state of [spn]. *)
  
  Fixpoint spn_fire_aux
           (spn : Spn)
           (state : SpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pgroup : list Trans):
    option (list Trans) :=
    match pgroup with
    | t :: tail =>
      match get_neighbours spn.(lneighbours) t with
      | Some neighbours_of_t =>
        match spn_is_firable spn state neighbours_of_t t with
        (* If t is firable, then checks if t is sensitized by residual_marking.  *)
        | Some true =>
          (* If t is sensitized by residual_marling, then, 
             updates the residual_marking, and add t to the fired transitions. *)
          match is_sensitized spn residual_marking neighbours_of_t t with
          | Some true =>
            match update_residual_marking spn residual_marking neighbours_of_t t with
            (* Recursive call with updated residual marking *)
            | Some residual_marking' =>
              spn_fire_aux spn state residual_marking' (fired ++ [t]) tail
            (* Something went wrong, error! *)
            | None => None
            end
          (* Else no changes but inductive progress. *)
          | Some false =>
            spn_fire_aux spn state residual_marking fired tail
          (* Something went wrong, error! *)
          | None => None
          end
        (* Else no changes but inductive progress. *)
        | Some false =>
          spn_fire_aux spn state residual_marking fired tail
        (* Something went wrong, error! *)
        | None => None
        end
      (* get_neighbours went wrong, error! *)
      | None => None
      end
    | []  => Some fired
    end.

  Functional Scheme spn_fire_aux_ind := Induction for spn_fire_aux Sort Prop.
  
  (*****************************************************)
  (*****************************************************)
  
  (** Wrapper function around spn_fire_pre_aux. *)
  
  Definition spn_fire
             (spn : Spn)
             (state : SpnState)
             (pgroup : list Trans) :
    option (list Trans) :=
    spn_fire_aux spn state state.(marking) [] pgroup.
  
  (***********************************************************************)
  (***********************************************************************)
  
  (** Returns the list of fired transitions at the current state of [spn].
               
      Applies spn_fire over ALL priority group of transitions. *)
  
  Fixpoint spn_map_fire_aux
           (spn : Spn)
           (state : SpnState)
           (fired_transitions : list Trans)
           (priority_groups : list (list Trans)) :
    option (list Trans) :=
    match priority_groups with
    (* Loops over all priority group of transitions (pgroup) and
     * calls spn_fire. *)
    | pgroup :: pgroups_tail =>
      match spn_fire spn state pgroup with
      (* If spn_fire succeeds, then adds the fired transitions
       * in fired_transitions list. *)
      | Some (fired_trs) =>
        spn_map_fire_aux spn state (fired_transitions ++ fired_trs) pgroups_tail
      (* Case of error! *)
      | None => None
      end
    | [] => Some (fired_transitions)
    end.

  Functional Scheme spn_map_fire_aux_ind := Induction for spn_map_fire_aux Sort Prop.
  
  (***********************************************************************)
  (***********************************************************************)
  
  (** Wrapper around spn_map_fire_aux function. *)
  
  Definition spn_map_fire (spn : Spn) (state : SpnState) :
    option SpnState :=
    match spn_map_fire_aux spn state [] spn.(priority_groups) with
    | Some fired => Some (mk_SpnState fired state.(marking))
    | None => None
    end.

  Functional Scheme spn_map_fire_ind := Induction for spn_map_fire Sort Prop.
  
  (** ∀ spn, s, [spn_map_fire spn s] returns a state [s'] 
      with [s'.(marking)] = [s.(marking)] *)
  
  Lemma spn_map_fire_same_marking :
    forall (spn : Spn) (s s': SpnState),
      spn_map_fire spn s = Some s' ->
      s.(marking) = s'.(marking).
  Proof.
    do 2 intro;
      functional induction (spn_map_fire spn s) using spn_map_fire_ind;
      intros.
    - injection H; intros; rewrite <- H0; simpl; reflexivity.
    - inversion H.
  Qed.
  
  (***********************************************************************)
  (***********************************************************************)
    
End FireSpn.

Section UpdateMarkingSpn.

  (** Function : Removes some tokens from [pre_places], result  
                 of the firing of t. 
                 
                 Returns a new [spn] with an updated marking. *)
  
  Fixpoint update_marking_pre_aux
           (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place) : option (list (Place * nat)) :=
    match pre_places with
    | p :: tail =>
      match modify_m marking p Nat.sub (pre spn t p) with
      | Some m' => update_marking_pre_aux spn m' t tail
      (* It's an exception, p is not referenced in spn.(marking). *)
      | None => None
      end
    | [] => Some marking
    end.

  (** Wrapper around [update_marking_pre_aux]. *)
  
  Definition update_marking_pre
             (spn : Spn)
             (marking : list (Place * nat))
             (t : Trans) : option (list (Place * nat)) :=
    match get_neighbours spn.(lneighbours) t with
    | Some (neighbours_of_t) =>
      update_marking_pre_aux spn marking t (pre_pl neighbours_of_t)
    | None => None
    end.

  (**  Applies [update_marking_pre] on every transition t ∈ fired,
       and returns the resulting [spn] *)
  
  Fixpoint map_update_marking_pre
           (spn : Spn)
           (marking : list (Place * nat))
           (fired : list Trans) {struct fired} :
    option (list (Place * nat)) :=
    match fired with
    | t :: tail =>
      match update_marking_pre spn marking t with
      | Some m' => map_update_marking_pre spn m' tail
      | None => None
      end
    | [] => Some marking
    end.
  
  (** Function : Adds some tokens to the post places of [t], result 
                 of the firing of [t].

                 Returns a new Spn with an updated marking. *)
  
  Fixpoint update_marking_post_aux
           (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (post_places : list Place) : option (list (Place * nat)) :=
    match post_places with
    | p :: tail =>
      match modify_m marking p Nat.add (post spn t p) with
      | Some m' => update_marking_post_aux spn m' t tail
      (* It's a exception, p is not referenced in m. *)
      | None => None
      end
    | [] => Some marking
    end.

  (** Wrapper around update_marking_post_aux. *)
  
  Definition update_marking_post
             (spn : Spn)
             (marking : list (Place * nat))
             (t : Trans) : option (list (Place * nat)) :=
    match get_neighbours spn.(lneighbours) t with
    | Some (neighbours_of_t) =>
      update_marking_post_aux spn marking t (post_pl neighbours_of_t)
    | None => None
    end.

  (**  Applies [update_marking_post] on every transition t ∈ fired,
       and returns the resulting [spn] *)
  
  Fixpoint map_update_marking_post
           (spn : Spn)
           (marking : list (Place * nat))
           (fired : list Trans) {struct fired} :
    option (list (Place * nat)) :=
    match fired with
    | t :: tail =>
      match update_marking_post spn marking t with
      | Some m' => map_update_marking_post spn m' tail
      | None => None
      end
    | [] => Some marking
    end.

  (** Updates the marking of [spn] ∀ t ∈ fired. Returns the resulting [spn].*)
  
  Definition spn_update_marking
             (spn : Spn)
             (state : SpnState) :
    option SpnState :=
    match map_update_marking_pre spn state.(marking) state.(fired) with
    | Some m' =>
      match map_update_marking_post spn m' state.(fired) with
      | Some m'' => Some (mk_SpnState state.(fired) m'')
      | None => None
      end
    | None => None
    end.
  
End UpdateMarkingSpn.

(*==========================================================*)
(*================= Spn CYCLE EVOLUTION ====================*)
(*==========================================================*)

Section AnimateSpn.
  
  (** Executes one evolution cycle for [spn], 
      returns a couple (intermediate state, final state). *)
  
  Definition spn_cycle (spn : Spn) (starting_state : SpnState) :
    option (SpnState * SpnState) :=
    (* Fires/Determines the fired transitions in spn. *)
    match spn_map_fire spn starting_state with
    | Some inter_state =>
      (* Updates the marking in spn. *)
      match spn_update_marking spn inter_state with
      (* Returns the couple (inter_state, final_state). *)
      | Some final_state => Some (inter_state, final_state)
      | None => None
      end
    | None => None
    end.

  Functional Scheme spn_cycle_ind := Induction for spn_cycle Sort Prop.
  
  (*******************************************)
  (******** ANIMATING DURING N CYCLES ********)
  (*******************************************)

  (** Returns the list of (fired_transitions(i), Spn(i)) for each cycle i, 
      from 0 to n, representing the evolution of the Petri net [spn]. *)
  
  Fixpoint spn_animate_aux
           (spn : Spn)
           (starting_state : SpnState)
           (n : nat)
           (states : list (SpnState * SpnState)) :
    option (list (SpnState * SpnState)) :=
    match n with
    (* Adds the initial at the beginning of the states list. *)
    | O => Some states
    | S n' => match spn_cycle spn starting_state with
             | Some (inter_state, final_state) =>
               spn_animate_aux spn final_state n' (states ++ [(inter_state, final_state)])
             (* Case of error!! *)
             | None => None
             end
    end.

  (** ------------------------------------------------------------------------------- *)
  (** ------------------------------------------------------------------------------- *)

  (** Wrapper function around spn_animate_aux. Here, spn_evolution is initialized to nil. *)
  
  Definition spn_animate (spn : Spn) (n : nat) :
    option (list (SpnState * SpnState)) :=
    let spn_initial_state := (mk_SpnState [] spn.(initial_marking)) in 
    spn_animate_aux spn spn_initial_state n [((mk_SpnState [] []), spn_initial_state)].
  
End AnimateSpn.
