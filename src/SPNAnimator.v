Require Export Hilecop.SPN.

(*! ============================================================ !*)
(*! ================ FIRING ALGORITHM for SPN ================== !*)
(*! ============================================================ !*)

Section FireSpn.

  (** Formal specification for is_sensitized *)

  Definition IsSensitized
             (spn : SPN)
             (marking : marking_type)
             (t : trans_type) : Prop :=
    forall (p : place_type)
      (n : nat),
      In p spn.(places) ->
      GetM marking p (Some n) ->
      n >= (pre spn t p) /\ n >= (test spn t p) /\ n < (inhib spn t p).
  
  (** Returns [Some true] if [t] is sensitized in marking [marking], 
      [Some false] otherwise. 
                 
      Raises an error if [map_check_pre], [map_check_test], [map_check_inhib] or
      [get_neighbours] fail. *)
  
  Definition is_sensitized
             (spn : SPN)
             (marking : marking_type)
             (neighbours_of_t : neighbours_type)
             (t : trans_type) : option bool :=    
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

  (** Soundness proof for is_sensitized and IsSensitized. *)

  Theorem is_sensitized_correct :
    forall (spn : SPN)
      (marking : marking_type)
      (neighbours_of_t : neighbours_type)
      (t : trans_type)
      (opt_b : option bool),
      is_sensitized spn marking neighbours_of_t t = opt_b ->
      IsSensitized spn marking neighbours_of_t t opt_b.
  Proof.

  (** Returns true if t ∈ sensitized(spn). *)
  
  Definition spn_is_firable
             (spn : SPN)
             (marking : marking_type)
             (neighbours_of_t : neighbours_type)
             (t : trans_type) : option bool :=
    is_sensitized spn marking neighbours_of_t t.

  (** Returns a marking M' where 
      M' = [residual_marking] - ∀ p ∈ [pre_places], ∑ pre(p, t)  *)
  
  Fixpoint update_residual_marking_aux
           (spn : SPN)
           (residual_marking : marking_type)
           (t : trans_type)
           (pre_places : list place_type) {struct pre_places} :
    option marking_type :=
    match pre_places with
    | p :: tail =>
      match modify_m spn.(marking) p Nat.sub (pre spn t p) with
      | Some residual_marking' =>
        update_residual_marking_aux spn residual_marking' t tail
      (* It's an exception, p is not referenced in spn.(marking). *)
      | None => None
      end
    | [] => Some (residual_marking)
    end.  

  (** Wrapper around update_residual_marking. *)
  
  Definition update_residual_marking
             (spn : SPN)
             (residual_marking : marking_type)
             (neighbours_of_t : neighbours_type)
             (t : trans_type) : option marking_type :=
    update_residual_marking_aux spn residual_marking t (pre_pl neighbours_of_t).
  
  (* 
   * There are 2 parallel calculus in spn_fire_pre_aux : 
   * 1. pumping tokens to get "decreasingm" (fired pre)
   * 2. returning group of transitions (fired_pre_group)
   *
   * and 2 markings are recorded : 
   * 1. the initial one to check with inhib and test arcs
   * 2. a residual marking to check classic arcs
   *)
  
  (** Returns the list of fired transitions in priority group [pgroup]
      at the current state of [spn]. *)
  
  Fixpoint spn_fire_aux
           (spn : SPN)
           (residual_marking : marking_type)
           (fired : list trans_type)
           (pgroup : list trans_type):
    option (list trans_type) :=
    match pgroup with
    | t :: tail =>
      match get_neighbours spn.(lneighbours) t with
      | Some neighbours_of_t =>
        match spn_is_firable spn residual_marking neighbours_of_t t with
        (* If t is firable, updates the residual_marking, and add t to the fired transitions. *)
        | Some true =>
          match update_residual_marking spn residual_marking neighbours_of_t t with
          (* Recursive call with new marking *)
          | Some residual_marking' =>
            spn_fire_aux spn residual_marking' (fired ++ [t]) tail
          (* Something went wrong, error! *)
          | None => None
          end
        (* Else no changes but inductive progress. *)
        | Some false =>
          spn_fire_aux spn residual_marking fired tail
        (* Something went wrong, error! *)
        | None => None
        end
      (* get_neighbours went wrong, error! *)
      | None => None
      end
    | []  => Some fired
    end.
  
  (*****************************************************)
  (*****************************************************)
  
  (** Wrapper function around spn_fire_pre_aux. *)
  
  Definition spn_fire
             (spn : SPN)
             (pgroup : list trans_type) :
    option (list trans_type) :=
    spn_fire_aux spn spn.(marking) [] pgroup.
  
  (***********************************************************************)
  (***********************************************************************)
  
  (** Returns the list of fired transitions at the current state of [spn].
               
      Applies spn_fire over ALL priority group of transitions. *)
  
  Fixpoint spn_map_fire_aux
           (spn : SPN)
           (fired_transitions : list trans_type)
           (priority_groups : list (list trans_type)) :
    option (list trans_type) :=
    match priority_groups with
    (* Loops over all priority group of transitions (pgroup) and
     * calls spn_fire. *)
    | pgroup :: pgroups_tail =>
      match spn_fire spn pgroup with
      (* If spn_fire succeeds, then adds the fired transitions
       * in fired_transitions list. *)
      | Some (fired_trs) =>
        spn_map_fire_aux spn (fired_transitions ++ fired_trs) pgroups_tail
      (* Case of error! *)
      | None => None
      end
    | [] => Some (fired_transitions)
    end.
  
  (***********************************************************************)
  (***********************************************************************)
  
  (** Wrapper around spn_map_fire_aux function. *)
  
  Definition spn_map_fire (spn : SPN) :
    option (list trans_type) :=
    spn_map_fire_aux spn [] spn.(priority_groups).
  
  (***********************************************************************)
  (***********************************************************************)
    
End FireSpn.

Section UpdateMarkingSpn.

  (** Function : Removes some tokens from [pre_places], result  
                 of the firing of t. 
                 
                 Returns a new [spn] with an updated marking. *)
  
  Fixpoint update_marking_pre_aux
           (spn : SPN)
           (marking : marking_type)
           (t : trans_type)
           (pre_places : list place_type) : option marking_type :=
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
             (spn : SPN)
             (marking : marking_type)
             (t : trans_type) : option marking_type :=
    match get_neighbours spn.(lneighbours) t with
    | Some (neighbours_of_t) =>
      update_marking_pre_aux spn marking t (pre_pl neighbours_of_t)
    | None => None
    end.

  (**  Applies [update_marking_pre] on every transition t ∈ fired,
       and returns the resulting [spn] *)
  
  Fixpoint map_update_marking_pre
           (spn : SPN)
           (marking : marking_type)
           (fired : list trans_type) {struct fired} :
    option marking_type :=
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

                 Returns a new SPN with an updated marking. *)
  
  Fixpoint update_marking_post_aux
           (spn : SPN)
           (marking : marking_type)
           (t : trans_type)
           (post_places : list place_type) : option marking_type :=
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
             (spn : SPN)
             (marking : marking_type)
             (t : trans_type) : option marking_type :=
    match get_neighbours spn.(lneighbours) t with
    | Some (neighbours_of_t) =>
      update_marking_post_aux spn marking t (post_pl neighbours_of_t)
    | None => None
    end.

  (**  Applies [update_marking_post] on every transition t ∈ fired,
       and returns the resulting [spn] *)
  
  Fixpoint map_update_marking_post
           (spn : SPN)
           (marking : marking_type)
           (fired : list trans_type) {struct fired} :
    option marking_type :=
    match fired with
    | t :: tail =>
      match update_marking_post spn marking t with
      | Some m' => map_update_marking_post spn m' tail
      | None => None
      end
    | [] => Some marking
    end.

  (** Updates the marking of [spn] ∀ t ∈ fired. Returns the resulting [spn].*)
  
  Definition spn_update_marking (spn : SPN) (fired : list trans_type) :
    option marking_type :=
    match map_update_marking_pre spn spn.(marking) fired with
    | Some m' => map_update_marking_post spn m' fired
    | None => None
    end.
  
End UpdateMarkingSpn.

(*==========================================================*)
(*================= SPN CYCLE EVOLUTION ====================*)
(*==========================================================*)

Section AnimateSpn.
  
  (** Executes one evolution cycle for [spn], 
      returns the transitions fired at this cycle, and the new state of [spn]. *)
  
  Definition spn_cycle (spn : SPN) : option (list trans_type * SPN) :=
    (* Fires/Determines the fired transitions in spn. *)
    match spn_map_fire spn with
    | Some fired_transitions =>
      (* Updates the marking in spn. *)
      match spn_update_marking spn fired_transitions with
      (* Sets m' has the new marking of spn. *)
      | Some m' => Some (fired_transitions, (set_m spn m'))
      | None => None
      end
    | None => None
    end.
  
  (*******************************************)
  (******** ANIMATING DURING N CYCLES ********)
  (*******************************************)

  (** Returns the list of (fired_transitions(i), SPN(i)) for each cycle i, 
      from 0 to n, representing the evolution of the Petri net [spn]. *)
  
  Fixpoint spn_animate_aux
           (spn : SPN)
           (n : nat)
           (states : list (list trans_type * SPN)) :
    option (list (list trans_type * SPN)) :=
    match n with
    | O => Some states
    | S n' => match spn_cycle spn with
             | Some (fired_at_n, spn_at_n) =>
               spn_animate_aux spn_at_n n' (states ++ [(fired_at_n, spn_at_n)])
             (* Case of error!! *)
             | None => None
             end
    end.

  (** ------------------------------------------------------------------------------- *)
  (** ------------------------------------------------------------------------------- *)

  (** Wrapper function around spn_animate_aux. Here, spn_evolution is initialized to nil. *)
  
  Definition spn_animate (spn : SPN) (n : nat) :
    option (list (list trans_type * SPN)) := spn_animate_aux spn n [].
  
End AnimateSpn.
