(** * Generation of the architecture body of a H-VHDL design. *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import HVhdlTypes.
Require Import ListsPlus.
Require Import ListsDep.
Require Import String.
Require Import dp.Sitpn.
Require Import dp.SitpnFacts.
Require Import SitpnTypes.
Require Import InfosTypes.
Require Import AbstractSyntax.
Require Import Petri.
Require Import Place.
Require Import Transition.
Require Import Sitpn2HVhdlTypes.

Import ErrMonadNotations.

Set Implicit Arguments.

(** ** Mapping between places and place components. *)

Section GeneratePlaceMap.

  Variable sitpn : Sitpn.
  Variable sitpn_info : SitpnInfo sitpn.

  (** Returns the generic map (abstract syntax) of the place component
      describing place [p]. 
 
      Parameter [max_marking] is the maximal marking of the overall
      Sitpn; this value is computed by the analysis of the net.
   *)

  Definition generate_place_gen_map (p : P sitpn) (pinfo : PlaceInfo sitpn) (max_marking : nat) :
    optionE genmap :=
 
    (* Error case: p has no input or output transitions. *)
    if is_empty (tinputs pinfo) && is_empty (toutputs pinfo) then
      Err ("generate_place_gen_map: "
             ++ "Place " ++ $$p
             ++ " is an isolated place.")%string
    else
      (* If p has no input, creates one input that will have a weight of zero. *)
      let p_in_arcs_nb := ( if tinputs pinfo then 1 else List.length (tinputs pinfo) ) in
      (* If p has no output, creates one output that will have a weight of zero. *)
      let p_out_arcs_nb := ( if toutputs pinfo then 1 else List.length (toutputs pinfo) ) in

      (* Builds the generic map of p. *)
      [| [assocg_ Place.input_arcs_number p_in_arcs_nb;
         assocg_ Place.output_arcs_number p_out_arcs_nb;
         assocg_ Place.maximal_marking max_marking] |].

  (** Returns the list of input arcs weights of place [p]. *)

  Definition get_input_arcs_weights (p : P sitpn) (pinfo : PlaceInfo sitpn) : optionE (list expr) :=

    (* If p has no inputs, creates one input with a weight of zero. *)
    let p_in_arcs_weights := (if List.length (tinputs pinfo) =? 0 then [e_nat 0] else []) in
    
    (* Adds the weight of the post arc between t and p to the list of
       expressions if an arc exists between t and p. Returns an error
       otherwise.  *)
    let get_in_arc_weight :=
        (fun lofexprs t =>
           match post t p with
           | Some (exist _ w _) => [| lofexprs ++ [e_nat w] |]
           | _ => Err ("get_input_arcs_weights: Transition "
                         ++ $$t ++ " is not an input of place "
                         ++ $$p ++ ".")%string
           end)
    in

    (* Iterates and calls get_in_arc_weight over all input transitions
       of p. *)
    oefold_left get_in_arc_weight (tinputs pinfo) p_in_arcs_weights.

  (** Returns the list of output arc weights and types of place [p]. *)
  
  Definition get_output_arcs_weights_and_types (p : P sitpn) (pinfo : PlaceInfo sitpn) :
    optionE (list expr * list expr) :=

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
           | Some (a, (exist _ w _) ) => [| (weights ++ [e_nat w], types ++ [e_nat a]) |]
           | _ => Err ("get_output_arcs_weights_and_types: Transition "
                      ++ $$t ++ " is not an output of place " ++ $$p ++ ".")%string
           end)
    in

    (* Iterates and calls get_in_arc_weight over all input transitions
       of p. *)
    oefold_left get_out_arc_wandt (toutputs pinfo) p_out_arcs_wandt.
    
  (** Generates a part of the input map (static part) for the place
      component representing place [p]. *)

  Definition generate_place_input_map (p : P sitpn) (pinfo : PlaceInfo sitpn) :
    optionE InputMap :=
    (* Retrieves the list of input arc weights. *)
    in_arcs_weights <- get_input_arcs_weights p pinfo;

    (* Retrieves the list of output arcs weights and types. *)
    |(out_arcs_weights, out_arcs_types)| <- get_output_arcs_weights_and_types p pinfo;

    [| [(Place.initial_marking, inl (e_nat (M0 p)));
       (Place.input_arcs_weights, inr in_arcs_weights);
       (Place.output_arcs_weights, inr out_arcs_weights);
       (Place.output_arcs_types, inr out_arcs_types)] |].
  
  (** Builds a PlaceMap entry for place p. *)

  Definition generate_place_map_entry (p : P sitpn) (max_marking : nat) :
    optionE (P sitpn * HComponent) :=
    (* Retrieves information about p. *)
    match getv Peqdec p (pinfos sitpn sitpn_info) with
    | Some pinfo =>
      (* Retrieves p's generic map. *)
      gmap <- generate_place_gen_map p pinfo max_marking;
      (* Retrieves p's static input map part. *)
      pipmap <- generate_place_input_map p pinfo;
      (* Returns a place map entry *)
      [| (p, (gmap, pipmap, [])) |]
    (* Error case. *)
    | None => Err ("generate_place_map_entry: Place "
                     ++ $$p ++ " is not referenced in SitpnInfo structure.")%string
    end.
  
  (** Returns the PlaceMap built out the list of places of [sitpn]. *)

  Definition generate_place_map (max_marking : nat) : optionE (PlaceMap sitpn) :=
    topte_map (fun p => generate_place_map_entry p max_marking) (P2List sitpn) nat_to_P.
  
End GeneratePlaceMap.

Arguments generate_place_map {sitpn}.

(** ** Mapping between transitions and transition components. *)

Section GenerateTransMap.

  Variable sitpn : Sitpn.
  Variable sitpn_info : SitpnInfo sitpn.

  (** Returns the transition type of t. *)

  Definition get_trans_type (t : T sitpn) : TransitionT :=
    match Is t with
    | Some (MkSTimeItval <| a, ninat b |> _)  =>
      if a =? b then temporal_a_a else temporal_a_b
    | Some (MkSTimeItval <| a, i+ |> _) => temporal_a_inf
    | None => not_temporal
    end.

  (** Returns maximal time counter value associated to t, depending 
      the time counter associated to t.
   *)

  Definition get_max_time_counter (t : T sitpn) : nat :=
    match Is t with
    (* Maximal time counter is equal to the upper bound value. *)
    | Some (MkSTimeItval <| a, ninat b |> _)  => b
    (* Or to one, if static time itval is of the form [a,∞] or if
       no itval is associated to t. *)
    | _ => 1
    end.
  
  (** Returns the generic map (abstract syntax) of the transition
      component mirror of transition [t]. *)

  Definition generate_trans_gen_map (t : T sitpn) (tinfo : TransInfo sitpn): genmap :=

    (* Retrieves transition type. *)
    let t_type := get_trans_type t in

    (* Retrieves number of input arcs. *)
    let t_in_arcs_nb := (if pinputs tinfo then 1 else List.length (pinputs tinfo)) in

    (* Retrieves number of conditions. *)
    let t_conds_nb := (if conds tinfo then 1 else List.length (conds tinfo)) in

    (* Retrieves maximal time counter value. *)
    let t_max_time_counter := get_max_time_counter t in

    (* Builds the generic map of t. *)
    [assocg_ Transition.transition_type t_type;
    assocg_ Transition.input_arcs_number t_in_arcs_nb;
    assocg_ Transition.conditions_number t_conds_nb;
    assocg_ Transition.maximal_time_counter t_max_time_counter].

  (** Generates a part of the input map (static part) for the transition
      component representing transition [t]. *)

  Definition generate_trans_input_map (t : T sitpn) (tinfo : TransInfo sitpn) : InputMap :=
    (* If [|conds(t)| = 0], adds [input_conditions, [true]] in [t]'s
       input map entry, to generate [input_conditions(0)⇒true]
       later. *)
    let in_conds_lofexprs := ( if conds tinfo then [e_bool true] else []) in
    let input_conditions := (Transition.input_conditions, inr in_conds_lofexprs) in

    
    match Is t with
    | Some (MkSTimeItval <| a, ninat b |> _) =>
      [(Transition.time_A_value, inl (e_nat a));
      (Transition.time_B_value, inl (e_nat b));
      input_conditions]
        
    | Some (MkSTimeItval <| a, i+ |> _) =>
      [(Transition.time_A_value, inl (e_nat a));
      (Transition.time_B_value, inl (e_nat 0));
      input_conditions]
        
    | None =>
      [(Transition.time_A_value, inl (e_nat 0));
      (Transition.time_B_value, inl (e_nat 0));
      input_conditions]
    end.

  (** Builds a TransMap entry for transition t. *)

  Definition generate_trans_map_entry (t : T sitpn) :
    optionE (T sitpn * HComponent) :=
    match getv Teqdec t (tinfos sitpn sitpn_info) with
    | Some tinfo =>
      (* Retrieves t's generic map. *)
      let gmap := generate_trans_gen_map t tinfo in

      (* Retrieves p's static input map part. *)
      let tipmap := generate_trans_input_map t tinfo in

      (* Builds TransMap entry. *)
      [| (t, (gmap, tipmap, [])) |]
    | None => Err ("generate_trans_map_entry: Transition "
                     ++ $$t ++ " is not referenced in SitpnInfo structure.")%string
    end.
  
  (** Returns the TransMap built out the list of transitions of [sitpn]. *)

  Definition generate_trans_map : optionE (TransMap sitpn) :=
    topte_map generate_trans_map_entry (T2List sitpn) nat_to_T.
  
End GenerateTransMap.

Arguments generate_trans_map {sitpn}.

(** ** Interconnections between place and transition components. *)

Section GenerateInterconnections.

  Variable sitpn : Sitpn.
  Variable sitpn_info : SitpnInfo sitpn.

  Local Open Scope abss_scope.
  
  (** (1) Connects the "fired" output port of the component
      representing transition [t] to another composite port via the
      list of expressions [lofexprs].
      
      (2) Adds the newly generated interconnection signal to the list
      of architecture's declarations, if such a signal has been
      created.

      (3) Returns the new architecture, the next available identifier,
      and the new list of expressions. *)
  
  Definition connect_fired_port
             (arch : Architecture sitpn)
             (nextid : ident)
             (lofexprs : list expr)
             (t : T sitpn) :
    optionE (Architecture sitpn * ident * list expr) :=
    (* Destructs the architecture. *)
    let '(adecls, plmap, trmap, fmap, amap) := arch in
    
    (* Retrieves the component associated to transtion t in TransMap
       trmap.  *)
    match getv Teqdec t trmap with
    | Some (tgmap, tipmap, topmap) =>
    (* Checks if the "fired" port already belongs to the input port map
       of the component. *)
      match getv Nat.eq_dec Transition.fired tipmap with
      (* Case where fired is connected to an expression.  Then, adds
         the expression e at the end of lofexprs, and returns the
         triplet (architecture, lofexprs, nextid). *)
      | Some (inl e) => [| (arch, nextid, lofexprs ++ [e]) |]
      (* Error case, in the output port map [topmap], fired is
         connected to a list of expressions, albeit it must be of
         scalar type (boolean).  *)
      | Some (inr _) => Err ("The fired port of transition " ++ $$t ++ " must be of scalar type.")%string
      (* Case where fired is not connected yet. Then, adds a new
         interconnection signal to the arch's declaration list and at
         the end of the lofexprs, modifies the output port map of
         transition t, and returns the resulting triplet. *)
      | None =>
        let adecls' := adecls ++ [adecl_sig nextid tind_boolean] in
        let topmap' := setv Nat.eq_dec Transition.fired (inl ($nextid)) topmap in
        let thcomp := (tgmap, tipmap, topmap') in
        let trmap' := setv Teqdec t thcomp trmap in
        let arch' := (adecls', plmap, trmap', fmap, amap) in
        (* Increments nextid to return the next available identifier. *)
        [| (arch', nextid + 1, lofexprs ++ [#nextid]) |]
      end
    (* Error case. *)
    | None => Err ("connect_fired_port: Transition "
                     ++ $$t ++ " is not referenced in the TransMap.")%string
    end.

  (** Returns a new architecture where the fired ports of all the
      transitions of the [transs] list have been connected to an
      internal signal; the list of all such signals is returned
      alongside the next available identifier.  *)
  
  Definition connect_fired_ports
             (arch : Architecture sitpn)
             (nextid : ident)
             (transs : list (T sitpn)) :
    optionE (Architecture sitpn * ident * list expr) :=
    
    (* Destructs the architecture. *)
    let '(adecls, plmap, trmap) := arch in
        
    (* Local variable storing the list of expressions, that is the
       list of internal signal identifiers connected to the fired port
       of transitions of the transs list.
       
       If the transs list is nil, then the list of expressions
       contains the singleton expression false.  *)
    let lofexprs := (if transs then [e_bool false] else []) in

    (* Wrapper around the connect_fired_port function. *)
    let wconn_fired_port :=
        (fun params t =>
           let '(arch, nextid, lofexprs) := params in
           connect_fired_port arch nextid lofexprs t)
    in
    (* Calls the connect_fired function over all transitions
         of the transs list. *)
    oefold_left wconn_fired_port transs (arch, nextid, lofexprs).

  (** Connects the input port map of a component [phcomp],
      representing some place p, to the output port map of the
      components representing the input transitions (resp. output
      transitions) of p. *)

  Definition connect_place_inputs
             (arch : Architecture sitpn)
             (nextid : ident)
             (pinfo : PlaceInfo sitpn)
             (phcomp : HComponent) :
    optionE (Architecture sitpn * ident * HComponent) :=

    (* Destructs phcomp. *)
    let '(pgmap, pipmap, popmap) := phcomp in
    
    (* Calls connect_transitions_fired on the input transitions of p. *)
    match connect_fired_ports arch nextid (tinputs pinfo) with
    | [| (arch', nextid', in_trans_fired) |] =>
      (* Calls connect_transitions_fired on the output transitions of p. *)
      match connect_fired_ports arch' nextid' (toutputs pinfo) with
      | [| (arch'', nextid'', out_trans_fired) |] =>
        (* Connects ports input_transitions_fired and
           output_transitions_fired to the list of expressions
           in_trans_fired and out_trans_fired.  *)
        let pipmap' := setv Nat.eq_dec Place.input_transitions_fired (inr in_trans_fired) pipmap in
        let pipmap'' := setv Nat.eq_dec Place.output_transitions_fired (inr out_trans_fired) pipmap' in
        
        (* Modifies the phcomp HComponent. *)
        let phcomp' := (pgmap, pipmap'', popmap) in
        [| (arch'', nextid'', phcomp') |]
        
      (* Error case. *)
      | Err msg => Err msg
      end
    (* Error case. *)
    | Err msg => Err msg
    end.

  (** Adds an association between the composite port [cportid] and the
      expression [e] in the input port map [ipmap]. *)

  Definition add_cassoc_to_ipmap (ipmap : InputMap) (cportid : ident) (e : expr) :
    optionE InputMap :=
    
    (* Checks if cportid is known in ipmap. *)
    match getv Nat.eq_dec cportid ipmap with
    (* If cportid is associated to an expression in ipmap, then
         cportid is not a composite port, then error.  *)
    | Some (inl _) => Err ("add_cassoc_to_pmap : cportid is not a composite port.")%string

    (* If cportid is a known composite port in ipmap, then adds
         e at the end of the associated list of expressions. *)
    | Some (inr lofexprs) =>
      [| (setv Nat.eq_dec cportid (inr (lofexprs ++ [e])) ipmap) |]

    (* If cportid is not known in ipmap, then adds the association
         between cportid and the singleton list [e] in ipmap. *)
    | None =>
      [| (setv Nat.eq_dec cportid (inr [e]) ipmap) |]
    end.

  (** Adds an association between the composite port [cportid] and the
      name [n] in the output port map [opmap]. *)

  Definition add_cassoc_to_opmap (opmap : OutputMap) (cportid : ident) (n : name) :
    optionE OutputMap :=
    
    (* Checks if cportid is known in opmap. *)
    match getv Nat.eq_dec cportid opmap with
    (* If cportid is associated to a name in opmap, then
         cportid is not a composite port, then error.  *)
    | Some (inl _) => Err ("add_cassoc_to_pmap : cportid is not a composite port.")%string

    (* If cportid is a known composite port in opmap, then adds
         n at the end of the associated list of names. *)
    | Some (inr lofexprs) =>
      [| (setv Nat.eq_dec cportid (inr (lofexprs ++ [n])) opmap) |]

    (* If cportid is not known in opmap, then adds the association
         between cportid and the singleton list [n] in opmap. *)
    | None =>
      [| (setv Nat.eq_dec cportid (inr [n]) opmap) |]
    end.
  
  (** Creates an interconnection signal (adds it to [adecls]) and
      connects [xoport] (in the output port map of [hcompx]) to
      [yiport] (in the input port map of [hcompy]) through this newly
      created signal.  *)
  
  Definition connect
             (adecls : list adecl)
             (nextid : ident)
             (hcompx hcompy : HComponent)
             (xoport yiport : ident) :
    optionE (list adecl * ident * HComponent * HComponent) :=
    
    (* Adds a new interconnection signal at the end of adecls. *)
    let adecls := adecls ++ [adecl_sig nextid tind_boolean] in

    (* Destructs component x and y. *)
    let '(xgmap, xipmap, xopmap) := hcompx in
    let '(ygmap, yipmap, yopmap) := hcompy in

    (* Connects xoport to the newly declared interconnection signal in
       output port map xopmap. *)
    match add_cassoc_to_opmap xopmap xoport ($nextid) with
    | [| xopmap' |] =>
      (* Connects yiport to the newly declared interconnection signal
         in input port map yipmap. *)
      match add_cassoc_to_ipmap yipmap yiport (#nextid) with
      | [| yipmap' |] =>
        (* Overrides component hcompx and hcompy with their new output
           and input port map.  *)
        let hcompx' := (xgmap, xipmap, xopmap') in
        let hcompy' := (ygmap, yipmap', yopmap) in
        
        (* Returns the resulting 4-uplet. *)
        [| (adecls, nextid + 1, hcompx', hcompy') |]
      | Err msg => Err msg
      end
    | Err msg => Err msg
    end.

  (** Connects the output port map of component [phcomp] to the input
      port map of the component associated to transition [t] in the
      architecture [arch] (more precisely, in the [arch]'s TransMap). *)

  Definition connect_popmap_to_tipmap
             (arch : Architecture sitpn)
             (nextid : ident)
             (phcomp : HComponent)
             (t : T sitpn) :
    optionE (Architecture sitpn * ident * HComponent) :=

    (* Destructs the architecture. *)
    let '(adecls, plmap, trmap, fmap, amap) := arch in
    
    (* Retrieves the component associated to transition t in trmap. *)
    match getv Teqdec t trmap with
    | Some thcomp =>
      (* Connects output_arcs_valid to input_arcs_valid. *)
      s' <- connect adecls nextid phcomp thcomp Place.output_arcs_valid Transition.input_arcs_valid;
      let '(adecls', nextid', phcomp', thcomp') := s' in

      (* Connects priority_authorizations to priority_authorizations. *)
      s'' <- connect adecls' nextid' phcomp' thcomp' Place.priority_authorizations Transition.priority_authorizations;
      let '(adecls'', nextid'', phcomp'', thcomp'') := s'' in

      (* Connects reinit_transitions_time to reinit_time. *)
      s''' <- connect adecls'' nextid'' phcomp'' thcomp'' Place.reinit_transitions_time Transition.reinit_time;
      let '(adecls''', nextid''', phcomp''', thcomp''') := s''' in

      (* Overrides the association of t to thcomp in trmap. *)
      let trmap' := setv Teqdec t thcomp''' trmap in
      
      (* Creates a new architecture, i.e, with new adecls and trmap. *)
      let arch' := (adecls''', plmap, trmap', fmap, amap) in

      (* Returns a triplet with a new archictecture, fresh id, and an HComponent. *)
      [| (arch', nextid''', phcomp) |]
                                                              
    (* Error case. *)
    | None => Err ("connect_popmap_to_tipmap:"
                     ++ "Transition " ++ $$t ++
                     " is not referenced in the architecture's TransMap.")%string
    end.

  (** Connects the output port map of component [phcomp] representing
      some place p, to the input port map of the components
      representing the output transitions of p in the architecture
      [arch]. *)
  
  Definition connect_place_outputs
             (arch : Architecture sitpn)
             (nextid : ident)
             (pinfo : PlaceInfo sitpn)
             (phcomp : HComponent) :
    optionE (Architecture sitpn * ident * HComponent) :=

    (* Wrapper around the connect_popmap_to_tipmap function. *)
    let wconn_pop_to_tip :=
        (fun params t =>
           let '(arch, nextid, phcomp) := params in
           connect_popmap_to_tipmap arch nextid phcomp t)
    in
    (* Calls connect_popmap_to_tipmap on every output transitions of
       p.  *)
    oefold_left wconn_pop_to_tip (toutputs pinfo) (arch, nextid, phcomp).

  (** Retrieves the component representing place [p] in the
      Architecture [arch] and connects its input and ouput ports to
      the components representing its input (resp. output)
      transitions.  

      Informations about which transitions are the input and output
      of place [p] are retrieved thanks to the [sitpn_info] instance. 
   *)
  
  Definition interconnect_p
             (arch : Architecture sitpn)
             (nextid : ident)
             (p : P sitpn) :
    optionE (Architecture sitpn * ident) :=
    
    (* Destructs the architecture. *)
    let '(adecls, plmap, trmap, fmap, amap) := arch in
    
    (* Retrieves information about p. *)
    match getv Peqdec p (pinfos sitpn sitpn_info) with
    | Some pinfo =>
    (* Retrieves the component associated to p in plmap. *)
      match getv Peqdec p plmap with
      | Some phcomp =>
        (* Connects the input port map of phcomp. *)
        s' <- connect_place_inputs arch nextid pinfo phcomp;
        let '(arch', nextid', phcomp') := s' in

        (* Connects the output port map of phcomp. *)
        s'' <- connect_place_outputs arch' nextid' pinfo phcomp';
        let '(arch'', nextid'', phcomp'') := s'' in

        (* Associates p to phcomp'' in the PlaceMap of arch''. *)
        let '(adecls'', plmap'', trmap'', fmap, amap) := arch'' in
        let plmap''' := setv Peqdec p phcomp'' plmap'' in
        
        (* Creates an new architecture, and returns the resulting couple. *)
        let arch''' := (adecls'', plmap''', trmap'', fmap, amap) in

        (* Returns a couple new architecture and fresh id. *)
        [| (arch''', nextid'') |]
     | None =>
        Err ("interconnect_p:"
               ++ "Place " ++ $$p
               ++ " is not referenced in the architecture's PlaceMap structure.")%string
      end
    | None =>
      Err ("interconnect_p:"
             ++ "Place " ++ $$p
             ++ " is not referenced in SitpnInfo structure.")%string
    end.

  (** Generates the interconnections between place and transition
      components of the architecture [arch].
      
      For each place in [sitpn], its mirror place component is
      retrieved from [arch]'s PlaceMap, and interconnected to its
      input and output transitions. *)

  Definition generate_interconnections (arch : Architecture sitpn) (nextid : ident) :
    optionE (Architecture sitpn * ident) :=
    
    (* Wrapper around the interconnect_p function. *)
    let winterconn_p :=
        (fun params p =>
           let '(arch, nextid) := params in
           interconnect_p arch nextid p)
    in
    
    (* Calls interconnect_p on each place of sitpn. *)
    topte_fold_left winterconn_p (P2List sitpn) (arch, nextid) nat_to_P.
  
End GenerateInterconnections.

Arguments generate_interconnections {sitpn}.

(** ** Generation of an Architecture structure from an Sitpn. *)

Section GenerateArchitecture.

  Variable sitpn : Sitpn.
  Variable sitpn_info : SitpnInfo sitpn.
  
  (** Generates an Architecture structure (i.e, a triplet
      archictecture declaration list, Placemap instance, and TransMap
      instance) based on the information and the structure of
      [sitpn]. *)

  Definition generate_architecture (nextid : ident) (max_marking : nat) :
    optionE (Architecture sitpn * ident) :=
    (* Generates the PlaceMap that maps places to intermediary Place
       components. *)
    plmap <- generate_place_map sitpn_info max_marking;
    (* Generates the TransMap that maps transitions to intermediary
       Transition components. *)
    trmap <- generate_trans_map sitpn_info;

    let arch := ([], plmap, trmap, [], []) in
    (* Generates the interconnections between Place and Transition
       components referenced in the PlaceMap plmap and the TransMap
       trmap, and returns the new architecture and the next
       available identifier. *)
    generate_interconnections sitpn_info arch nextid.

End GenerateArchitecture.
