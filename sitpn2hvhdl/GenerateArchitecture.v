(** * Generation of the architecture body of a H-VHDL design. *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.ListPlus.
Require Import common.ListDep.
Require Import common.StateAndErrorMonad.
Require Import String.
Require Import dp.Sitpn.
Require Import dp.SitpnFacts.
Require Import dp.SitpnTypes.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Petri.
Require Import hvhdl.Place.
Require Import hvhdl.Transition.
Require Import sitpn2hvhdl.Sitpn2HVhdlTypes.

Import ErrMonadNotations.

Set Implicit Arguments.

Section GenArch.

  Variable sitpn : Sitpn.

  (* Proof of decidability for the priority relation of [sitpn] *)

  Variable decpr : forall x y : T sitpn, {x >~ y} + {~x >~ y}.

  (* Alias for the state-and-error monad instantiated with the
     compile-time state.  *)

  Definition CompileTimeState := @Mon (Sitpn2HVhdlState sitpn).
  
  (** ** Generation of place component instances *)

  Section GeneratePCIs.
    
    (** Returns the generic map (abstract syntax) of the place component
        describing place [p]. 
 
      Parameter [max_marking] is the maximal marking of the overall
      Sitpn; this value is computed by the analysis of the net.
     *)

    Definition generate_place_gen_map (p : P sitpn) (pinfo : PlaceInfo sitpn) (max_marking : nat) :
      CompileTimeState genmap :=      
      (* If p has no input, creates one input that will have a weight of zero. *)
      let p_in_arcs_nb := ( if tinputs pinfo then 1 else List.length (tinputs pinfo) ) in
      (* If p has no output, creates one output that will have a weight of zero. *)
      let p_out_arcs_nb := ( if toutputs pinfo then 1 else List.length (toutputs pinfo) ) in

      (* Builds the generic map of p. *)
      Ret [assocg_ Place.input_arcs_number p_in_arcs_nb;
           assocg_ Place.output_arcs_number p_out_arcs_nb;
           assocg_ Place.maximal_marking max_marking].

    (** Returns the list of input arcs weights of place [p]. *)

    Definition get_input_arcs_weights (p : P sitpn) (pinfo : PlaceInfo sitpn) : CompileTimeState (list expr) :=

      (* If p has no inputs, creates one input with a weight of zero. *)
      let p_in_arcs_weights := (if List.length (tinputs pinfo) =? 0 then [e_nat 0] else []) in
      
      (* Adds the weight of the post arc between t and p to the list of
       expressions if an arc exists between t and p. Returns an error
       otherwise.  *)
      let get_in_arc_weight :=
          (fun lofexprs t =>
             match post t p with
             | Some (exist _ w _) => Ret (lofexprs ++ [e_nat w])
             | _ => Err ("get_input_arcs_weights: Transition "
                           ++ $$t ++ " is not an input of place "
                           ++ $$p ++ ".")%string
             end)
      in

      (* Iterates and calls get_in_arc_weight over all input transitions
       of p. *)
      ListMonad.fold_left get_in_arc_weight (tinputs pinfo) p_in_arcs_weights.

    (** Returns the list of output arc weights and types of place [p]. *)
    
    Definition get_output_arcs_weights_and_types (p : P sitpn) (pinfo : PlaceInfo sitpn) :
      CompileTimeState (list expr * list expr) :=

      (* If p has no output, creates one output with a weight of zero
       and type basic. *)
      let p_out_arcs_wandt :=
          ( if (toutputs pinfo) then ([e_nat 0], [e_nat basic]) else ([], []) )
      in
      
      (* Adds the weight and the type of the pre arc between p and t to
       the couple of lists (weights, types) if an arc exists between p
       and t. Returns an error otherwise.  *)
      let get_out_arc_wandt :=
          (fun params t =>
             let '(weights, types) := params in
             match pre p t with
             | Some (a, (exist _ w _) ) => Ret (weights ++ [e_nat w], types ++ [e_nat a])
             | _ => Err ("get_output_arcs_weights_and_types: Transition "
                           ++ $$t ++ " is not an output of place " ++ $$p ++ ".")%string
             end)
      in

      (* Iterates and calls get_in_arc_weight over all input transitions
       of p. *)
      ListMonad.fold_left get_out_arc_wandt (toutputs pinfo) p_out_arcs_wandt.
    
    (** Generates a part of the input map (static part) for the place
      component representing place [p]. *)

    Definition generate_place_input_map (p : P sitpn) (pinfo : PlaceInfo sitpn) :
      CompileTimeState InputMap :=
      (* Retrieves the list of input arc weights. *)
      do in_arcs_weights <- get_input_arcs_weights p pinfo;

      (* Retrieves the list of output arcs weights and types. *)
      do out_arcs_wandt <- get_output_arcs_weights_and_types p pinfo;
      let (out_arcs_weights, out_arcs_types) := out_arcs_wandt in
      
      Ret [(Place.initial_marking, inl (e_nat (M0 p)));
          (Place.input_arcs_weights, inr in_arcs_weights);
          (Place.output_arcs_weights, inr out_arcs_weights);
          (Place.output_arcs_types, inr out_arcs_types)].

    
    
    (** Generates a PCI from place [p]. *)

    Definition generate_pci (p : P sitpn) (max_marking : nat) :
      CompileTimeState (P sitpn * HComponent) :=
      (* Retrieves information about p. *)
      do pinfo <- get_pinfo p;

      (* Retrieves a fresh identifier [id__p] to name the newly
         generated PCI. *)
      do id__p <- get_nextid;
      
      (* Builds the generic map, input and output port maps for PCI
         [id__p]. *)
      do '((g, i), o) <- build_pci p pinfo [(assocg_ Place.maximal_marking max_marking)] [] [];

      (* Adds the new PCI in the compile-time state's behavior. *)
      do _ <- add_cs (cs_comp id__p place_entid g i o);

      (* Adds a binding between place [p] and PCI [id__p] in γ. *)
      do _ <- bind_place p id__p;
      
      (* Returns a place map entry *)
      Ret (p, (gmap, pipmap, [])).
    
    (** Builds a PlaceMap out the list of places of [sitpn], and
        sets it in the architecture of the compile-time state. *)

    Definition generate_pcis (b : P sitpn -> nat) : CompileTimeState unit :=
      do Plist <- get_lofPs;
      do _ <- ListMonad.iter (fun p => generate_pci p (b p)) Plist.
    
  End GeneratePCIs.

  (** ** Mapping between transitions and transition components. *)

  Section GenerateTransMap.
    
    (** Returns the transition type of t. *)

    Definition get_trans_type (t : T sitpn) : TransitionT :=
      match Is t with
      | Some (MkTItval a (ninat b) _)  =>
        if a =? b then temporal_a_a else temporal_a_b
      | Some (MkTItval a i+ _) => temporal_a_inf
      | None => not_temporal
      end.

    (** Returns maximal time counter value associated to t, depending
        the time counter associated to t.  *)

    Definition get_max_time_counter (t : T sitpn) : nat :=
      match Is t with
      (* Maximal time counter is equal to the upper bound value. *)
      | Some (MkTItval a (ninat b) _)  => b
      (* Or to the lower bound, if static time itval is of the form [a,∞] . *)
      | Some (MkTItval a i+ _)  => a
      (* Or to 1 if no itval is associated to t. *)
      | None => 1
      end.
    
    (** Returns the generic map (abstract syntax) of the transition
      component mirror of transition [t]. *)

    Definition generate_trans_gen_map (t : T sitpn) (tinfo : TransInfo sitpn): CompileTimeState genmap :=

      (* Retrieves transition type. *)
      let t_type := get_trans_type t in

      (* Retrieves number of input arcs. *)
      let t_in_arcs_nb := (if pinputs tinfo then 1 else List.length (pinputs tinfo)) in

      (* Retrieves number of conditions. *)
      let t_conds_nb := (if conds tinfo then 1 else List.length (conds tinfo)) in

      (* Retrieves maximal time counter value. *)
      let t_max_time_counter := get_max_time_counter t in

      (* Builds the generic map of t. *)
      Ret [assocg_ Transition.transition_type t_type;
          assocg_ Transition.input_arcs_number t_in_arcs_nb;
          assocg_ Transition.conditions_number t_conds_nb;
          assocg_ Transition.maximal_time_counter t_max_time_counter].

    (** Generates a part of the input map (static part) for the transition
      component representing transition [t]. *)

    Definition generate_trans_input_map (t : T sitpn) (tinfo : TransInfo sitpn) :
      CompileTimeState InputMap :=
      (* If [|conds(t)| = 0], adds [input_conditions, [true]] in [t]'s
       input map entry, to generate [input_conditions(0)⇒true]
       later. *)
      let in_conds_lofexprs := ( if conds tinfo then [e_bool true] else []) in
      let input_conditions := (Transition.input_conditions, inr in_conds_lofexprs) in
      
      match Is t with
      | Some (MkTItval a (ninat b) _) =>
        Ret [(Transition.time_A_value, inl (e_nat a));
            (Transition.time_B_value, inl (e_nat b));
            input_conditions]
          
      | Some (MkTItval a i+ _) =>
        Ret [(Transition.time_A_value, inl (e_nat a));
            (Transition.time_B_value, inl (e_nat 0));
            input_conditions]
          
      | None =>
        Ret [(Transition.time_A_value, inl (e_nat 0));
            (Transition.time_B_value, inl (e_nat 0));
            input_conditions]
      end.

    (** Builds a TransMap entry for transition t. *)

    Definition generate_trans_map_entry (t : T sitpn) :
      CompileTimeState (T sitpn * HComponent) :=
      (* Retrieves information about p. *)
      do tinfo <- get_tinfo t;

      (* Retrieves t's generic map. *)
      do gmap <- generate_trans_gen_map t tinfo;

      (* Retrieves p's static input map part. *)
      do tipmap <- generate_trans_input_map t tinfo;

      (* Builds TransMap entry. *)
      Ret (t, (gmap, tipmap, [])).
    
    (** Returns the TransMap built out the list of transitions of [sitpn]. *)

    Definition generate_trans_map : CompileTimeState unit :=
      do Tlist <- get_lofTs;
      do trmap <- ListMonad.map generate_trans_map_entry Tlist;
      do a <- get_arch;
      set_arch (MkArch sitpn (sigs a) (plmap a) trmap (fmap a) (amap a)).
    
  End GenerateTransMap.

  (** ** Interconnections between place and transition components. *)

  Section GenerateInterconnections.

    Local Open Scope abss_scope.

    Definition get_actual_of_out_port (opid : ident) (comp : HComponent) :
      CompileTimeState (option (option name + list name)) :=
      let '(gmap, ipmap, opmap) := comp in
      Ret (getv Nat.eq_dec opid opmap).

    Definition get_actual_of_in_port (ipid : ident) (comp : HComponent) :
      CompileTimeState (option (expr + list expr)) :=
      let '(gmap, ipmap, opmap) := comp in
      Ret (getv Nat.eq_dec ipid ipmap).

    Definition connect_out_port
               (opid : ident)
               (actual : option name + list name)
               (comp : HComponent) :
      CompileTimeState (HComponent) :=
      let '(gmap, ipmap, opmap) := comp in
      Ret (gmap, ipmap, setv Nat.eq_dec opid actual opmap).
    
    (** (1) Connects the "fired" output port of the component
        representing transition [t] to another composite port via the
        list of expressions [lofexprs].
      
        (2) Adds the newly generated interconnection signal to the list
        of architecture's declarations, if such a signal has been
        created.

        (3) Returns the new architecture, the next available identifier,
        and the new list of expressions. *)
    
    Definition connect_fired_port (lofexprs : list expr) (t : T sitpn) :
      CompileTimeState (list expr) :=
      
      (* Retrieves the component associated to transtion [t] in
         [TransMap trmap].  *)
      do tcomp <- get_tcomp t;
      do opt_fired_actual <- get_actual_of_out_port Transition.fired tcomp;
      
      (* Checks if the "fired" port already belongs to the output port map
         of [tcomp]. *)
      match opt_fired_actual with
      (* Case where fired is connected to an [option name].         
         Error, if fired port is open (i.e, connected to None).
         Otherwise, adds a new expression to [lofexprs]. *)
      | Some (inl optn) =>
        match optn with
        | Some n => Ret (lofexprs ++ [e_name n])
        | _ => Err ("connect_fired_port: the fired port of T component "
                      ++ $$t ++ " is open.")
        end
      (* Error case, in the output port map [topmap], fired is
         connected to a list of expressions, albeit it must be of
         scalar type (boolean).  *)
      | Some (inr _) =>
        Err ("connect_fired_port: the fired port of transition "
               ++ $$t ++ " must be of scalar type.")%string
      (* Case where [fired] is not connected yet. Then, adds a new
         interconnection signal to the [arch]'s internal signal
         declaration list and at the end of the [lofexprs], modifies
         the output port map of component [tcomp], and returns . *)
      | None =>

        do id <- get_nextid;
        do tcomp' <- connect_out_port Transition.fired (inl (Some ($id))) tcomp;
        do _ <- set_tcomp t tcomp';
        do _ <- add_sig_decl (sdecl_ id tind_boolean);
        
        (* Increments nextid to return the next available identifier. *)
        Ret (lofexprs ++ [#id])
      end.

    (** Returns a new architecture where the fired ports of all the
      transitions of the [transs] list have been connected to an
      internal signal; the list of all such signals is returned
      alongside the next available identifier.  *)
    
    Definition connect_fired_ports (transs : list (T sitpn)) :
      CompileTimeState (list expr) :=
      
      (* Local variable storing the list of expressions, that is the
         list of internal signal identifiers connected to the fired port
         of transitions of the transs list.
       
        If the transs list is nil, then the list of expressions
        contains the singleton expression [false].  *)
      let lofexprs := (if transs then [e_bool false] else []) in
      
      (* Calls the connect_fired function over all transitions
         of the transs list. *)
      ListMonad.fold_left connect_fired_port transs lofexprs.

    Definition connect_in_port
               (ipid : ident)
               (actual : expr + list expr)
               (comp : HComponent) :
      CompileTimeState (HComponent) :=
      let '(gmap, ipmap, opmap) := comp in
      Ret (gmap, setv Nat.eq_dec ipid actual ipmap, opmap).
    
    (** Connects the input port map of a component [phcomp],
        representing some place p, to the output port map of the
        components representing the input transitions (resp. output
        transitions) of p. *)

    Definition connect_place_inputs
               (pinfo : PlaceInfo sitpn)
               (pcomp : HComponent) :
      CompileTimeState (HComponent) :=

      (* Lists the signals connected to the [fired] port of the input
         transitions of [p]. *)
      do in_trans_fired <- connect_fired_ports (tinputs pinfo);
      (* Lists the signals connected to the [fired] port of the output
         transitions of [p]. *)
      do out_trans_fired <- connect_fired_ports (toutputs pinfo);
      (* Connects composite port [input_transitions_fired] of [pcomp]
         to the [fired] ports of its input transitions.  *)
      do pcomp' <- connect_in_port Place.input_transitions_fired (inr in_trans_fired) pcomp;
      (* Connects the composite port [output_transitions_fired] of [pcomp]
         to the [fired] ports of its output transitions, and returns [pcomp].  *)      
      connect_in_port Place.output_transitions_fired (inr out_trans_fired) pcomp'.
    
    (** Adds the expression [e] at the end of the list of expressions
        associated with the composite input port [ipid] in the input
        map of component [comp]. Returns the new version of [comp]. *)

    Definition add_cassoc_to_ipmap (ipid : ident) (e : expr) (comp : HComponent) :
      CompileTimeState HComponent :=
      
      let '(gmap, ipmap, opmap) := comp in

      (* Checks if ipid is known in ipmap. *)
      match getv Nat.eq_dec ipid ipmap with
      (* If [ipid] is associated to an expression in [ipmap], then
         [ipid] is not a composite port, then error.  *)
      | Some (inl _) => Err ("add_cassoc_to_pmap : port "
                               ++ $$ipid ++ " is not a composite port.")%string

      (* If [ipid] is a known composite port in [ipmap], then adds [e]
         at the end of the associated list of expressions. *)
      | Some (inr lofexprs) =>
         Ret (gmap, (setv Nat.eq_dec ipid (inr (lofexprs ++ [e])) ipmap), opmap)

      (* If ipid is not known in ipmap, then adds the association
         between ipid and the singleton list [e] in ipmap. *)
      | None =>
        Ret (gmap, (setv Nat.eq_dec ipid (inr [e]) ipmap), opmap)
      end.

    (** Adds the name [n] at the end of the list of names associated
        with the composite output port [opid] in the output map of
        component [comp]. *)
    
    Definition add_cassoc_to_opmap (opid : ident) (n : name) (comp : HComponent) :
      CompileTimeState HComponent :=

      let '(gmap, ipmap, opmap) := comp in
      
      (* Checks if opid is known in opmap. *)
      match getv Nat.eq_dec opid opmap with
      (* If opid is associated to a name in opmap, then
         opid is not a composite port, then error.  *)
      | Some (inl _) => Err ("add_cassoc_to_pmap : "
                               ++ $$opid ++ " is not a composite port.")%string

      (* If [opid] is a known composite port in [opmap], then adds
         [n] at the end of the associated list of names. *)
      | Some (inr lofnames) =>
        Ret (gmap, ipmap, (setv Nat.eq_dec opid (inr (lofnames ++ [n])) opmap))

      (* If [opid] is not known in [opmap], then adds the association
         between [opid] and the singleton list [n] in [opmap]. *)
      | None =>
        Ret (gmap, ipmap, (setv Nat.eq_dec opid (inr [n]) opmap))
      end.
    
    (** Creates an interconnection signal (adds it to [sigs]) and
        connects [xoport] (in the output port map of [compx]) to
        [yiport] (in the input port map of [compy]) through this
        newly created signal.  *)
    
    Definition connect
               (compx compy : HComponent)
               (xopid yipid : ident) :
       CompileTimeState (HComponent * HComponent) :=

      do id <- get_nextid;
      do _ <- add_sig_decl (sdecl_ id tind_boolean);
      do compx' <- add_cassoc_to_opmap xopid ($id) compx;
      do compy' <- add_cassoc_to_ipmap yipid (#id) compy;
      Ret (compx', compy').
      
    (** Connects the output port map of component [pcomp] to the input
        port map of the component associated to transition [t] in the
        architecture [arch] (more precisely, in the [arch]'s
        TransMap). *)

    Definition connect_popmap_to_tipmap
               (pcomp : HComponent)
               (t : T sitpn) :
      CompileTimeState HComponent :=
      do tcomp <- get_tcomp t;
      do ptcomp1 <- connect pcomp tcomp Place.output_arcs_valid Transition.input_arcs_valid;
      let (pcomp1, tcomp1) := ptcomp1 in
      do ptcomp2 <- connect pcomp1 tcomp1 Place.priority_authorizations Transition.priority_authorizations;
      let (pcomp2, tcomp2) := ptcomp2 in
      do ptcomp3 <- connect pcomp2 tcomp2 Place.reinit_transitions_time Transition.reinit_time;
      let (pcomp3, tcomp3) := ptcomp3 in
      do _ <- set_tcomp t tcomp3;
      Ret pcomp3.      

    (** Connects the output port map of component [pcomp] representing
        some place p, to the input port map of the components
        representing the output transitions of p in the architecture
        [arch]. *)
    
    Definition connect_place_outputs
               (pinfo : PlaceInfo sitpn)
               (pcomp : HComponent) :
      CompileTimeState HComponent :=

      (* Wrapper around the connect_popmap_to_tipmap function. *)
      let wconn_pop_to_tip :=
          (fun pcomp t =>
             connect_popmap_to_tipmap pcomp t)
      in
      (* Calls connect_popmap_to_tipmap on every output transitions of
         p. *)
      ListMonad.fold_left wconn_pop_to_tip (toutputs pinfo) pcomp.

    (** Retrieves the component [pcomp] associated to place [p] in the
        architecture of the compile-time state, and connects its input
        and ouput ports to the components representing its input
        (resp. output) transitions.  *)
    
    Definition interconnect_p (p : P sitpn) :
      CompileTimeState unit :=

      do pinfo <- get_pinfo p;
      do pcomp <- get_pcomp p;
      (* Connects the input port map of [pcomp]. *)
      do pcomp1 <- connect_place_inputs pinfo pcomp;
      (* Connects the output port map of [pcomp]. *)
      do pcomp2 <- connect_place_outputs pinfo pcomp1;
      set_pcomp p pcomp2.

    (** Generates the interconnections between place and transition
        components in the architecture of the compile-time state.
      
        For each place in [sitpn], its mirror place component is
        retrieved from [arch]'s PlaceMap, and interconnected to its
        input and output transitions. *)

    Definition generate_interconnections :
      CompileTimeState unit :=
      (* Calls interconnect_p on each place of sitpn. *)
      do Plist <- get_lofPs; ListMonad.iter interconnect_p Plist.
    
  End GenerateInterconnections.

  (** ** Generation of an Architecture structure from an Sitpn. *)

  Section GenerateArchitecture.

    (** Generates an Architecture structure based on the information
        and the structure of [sitpn]. *)

    Definition generate_architecture (b : P sitpn -> nat) :
      CompileTimeState unit :=
      (* Generates the PlaceMap that maps places to intermediary Place
         components. *)
      do _ <- generate_place_map b;
      (* Generates the TransMap that maps transitions to intermediary
         Transition components. *)
      do _ <- generate_trans_map;

      (* Generates the interconnections between Place and Transition
         components in the compile-time state architecture. *)
      generate_interconnections.

  End GenerateArchitecture.

End GenArch.

Arguments generate_place_map {sitpn}.
Arguments generate_trans_map {sitpn}.
Arguments generate_interconnections {sitpn}.
Arguments generate_architecture {sitpn}.

(* Require Import test.sitpn.dp.WellDefinedSitpns. *)
(* Require Import GenerateInfos. *)

(* Local Notation "[ e ]" := (exist _ e _). *)

Eval vm_compute in (RedV ((do _ <- generate_sitpn_infos sitpn_simpl prio_simpl_dec;
                           do _ <- generate_architecture 255;
                           get_arch)
                            (InitS2HState sitpn_simpl 10))).
