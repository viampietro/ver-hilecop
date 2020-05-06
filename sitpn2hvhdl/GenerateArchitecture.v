(** * Generation of the architecture body of a H-VHDL design. *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import HVhdlTypes.
Require Import ListsPlus.
Require Import ListsDep.
Require Import String.
Require Import sets.Sitpn.
Require Import SitpnTypes.
Require Import InfosTypes.
Require Import AbstractSyntax.
Require Import Petri.
Require Import Place.
Require Import Transition.
Require Import Sitpn2HVhdlTypes.

Set Implicit Arguments.

(** ** Mapping between places and place components. *)

Section GeneratePlaceMap.

  Variable sitpn : Sitpn.
  Variable sitpn_info : @SitpnInfo sitpn.

  (** Returns the generic map (abstract syntax) of the place component
      describing place [p]. 
 
      Parameter [max_marking] is the maximal marking of the overall
      Sitpn; this value is computed by the analysis of the net.
   *)

  Definition generate_place_gen_map (p : P sitpn) (pinfo : PlaceInfo sitpn) (max_marking : nat) :
    optionE genmap :=
 
    (* Error case: p has no input or output transitions. *)
    if (Nat.eqb (List.length (tinputs pinfo)) 0) && (Nat.eqb (List.length (toutputs pinfo)) 0) then
      Err ("Place " ++ $$p ++ " is an isolated place.")%string
    else
      (* If p has no input, creates one input that will have a weight of zero. *)
      let p_in_arcs_nb := (if List.length (tinputs pinfo) =? 0 then 1 else List.length (tinputs pinfo)) in
      (* If p has no output, creates one output that will have a weight of zero. *)
      let p_out_arcs_nb := (if List.length (toutputs pinfo) =? 0 then 1 else List.length (toutputs pinfo)) in

      (* Builds the generic map of p. *)
      Success
        [assocg_ Place.input_arcs_number p_in_arcs_nb;
        assocg_ Place.output_arcs_number p_out_arcs_nb;
        assocg_ Place.maximal_marking max_marking].

  (** Returns the list of input arcs weights of place [p]. *)

  Definition get_input_arcs_weights (p : P sitpn) (pinfo : PlaceInfo sitpn) : option (list expr) :=

    (* If p has no inputs, creates one input with a weight of zero. *)
    let p_in_arcs_weights := (if List.length (tinputs pinfo) =? 0 then [e_nat 0] else []) in
    
    (* Adds the weight of the post arc between t and p to the list of
       expressions if an arc exists between t and p. Returns an error
       otherwise.  *)
    let get_in_arc_weight :=
        (fun lofexprs t =>
           match post t p with Some (exist _ w _) => Some (lofexprs ++ [e_nat w]) | _ => None end) in

    (* Iterates and calls get_in_arc_weight over all input transitions
       of p. *)
    ofold_left get_in_arc_weight (tinputs pinfo) p_in_arcs_weights.

  (** Returns the list of output arc weights and types of place [p]. *)
  
  Definition get_output_arcs_weights_and_types (p : P sitpn) (pinfo : PlaceInfo sitpn) :
    option (list expr * list expr) :=

    (* If p has no output, creates one output with a weight of zero
       and type basic. *)
    let p_out_arcs_wandt :=
        (if List.length (toutputs pinfo) =? 0
         then ([e_nat 0], [e_nat basic])
         else ([], []))
    in
    
    (* Adds the weight and the type of the pre arc between p and t to
       the couple of lists (weights, types) if an arc exists between p
       and t. Returns an error otherwise.  *)
    let get_out_arc_wandt :=
        (fun (wandt : (list expr * list expr)) t =>
           let (weights, types) := wandt in
           match pre p t with
           | Some (a, (exist _ w _)) => Some (weights ++ [e_nat w], types ++ [e_nat a])
           | _ => None
           end)
    in

    (* Iterates and calls get_in_arc_weight over all input transitions
       of p. *)
    ofold_left get_out_arc_wandt (toutputs pinfo) p_out_arcs_wandt.
    
  (** Generates a part of the input map (static part) for the place
      component representing place [p]. *)

  Definition generate_place_input_map (p : P sitpn) (pinfo : PlaceInfo sitpn) :
    optionE InputMap :=
    (* Retrieves the list of input arc weights. *)
    match get_input_arcs_weights p pinfo with
    | Some in_arcs_weights =>
      (* Retrieves the list of output arcs weights and types. *)
      match get_output_arcs_weights_and_types p pinfo with
      | Some (out_arcs_weights, out_arcs_types) =>
        Success
          [(Place.initial_marking, inl (e_nat (M0 p)));
          (Place.input_arcs_weights, inr in_arcs_weights);
          (Place.output_arcs_weights, inr out_arcs_weights);
          (Place.output_arcs_types, inr out_arcs_types)
          ]
      (* Error case. *)
      | None => Err ("Ill-formed PlaceInfo structure for place " ++ $$p ++ ".")%string
      end
    (* Error case. *)
    | None => Err ("Ill-formed PlaceInfo structure for place " ++ $$p ++ ".")%string
    end.

  (** Builds a PlaceMap entry for place p. *)

  Definition generate_place_map_entry (p : P sitpn) (max_marking : nat) :
    optionE (P sitpn * (genmap * InputMap * OutputMap)) :=
    match getv eq_place_dec p (pinfos sitpn sitpn_info) with
    | Some pinfo =>
      (* Retrieves p's generic map. *)
      match generate_place_gen_map p pinfo max_marking with
      | Success gmap =>
        (* Retrieves p's static input map part. *)
        match generate_place_input_map p pinfo with
        | Success pipmap =>
          Success (p, (gmap, pipmap, []))
        (* Error case. *)
        | Err msg => Err msg
        end
      (* Error case. *)
      | Err msg => Err msg
      end
    | None => Err ("Place " ++ $$p ++ " is not referenced in SitpnInfo structure.")%string
    end.
  
  (** Returns the PlaceMap built out the list of places of [sitpn]. *)

  Definition generate_place_map (max_marking : nat) : optionE (PlaceMap sitpn) :=
    topt_map (fun p => generate_place_map_entry p max_marking) (P2List sitpn) nat_to_P.
  
End GeneratePlaceMap.

(** ** Mapping between transitions and transition components. *)

Section GenerateTransMap.

  Variable sitpn : Sitpn.
  Variable sitpn_info : SitpnInfo sitpn.

  (** Returns the transition type of t. *)

  Definition get_trans_type (t : T sitpn) : TransitionT :=
    match Is t with
    | Some (MkSTimeItval <| a, ninat b |> _)  => if a =? b then temporal_a_a else temporal_a_b
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
    let t_in_arcs_nb := (if List.length (pinputs tinfo) =? 0 then 1 else List.length (pinputs tinfo)) in

    (* Retrieves number of conditions. *)
    let t_conds_nb := (if List.length (conds tinfo) =? 0 then 1 else List.length (conds tinfo)) in

    (* Retrieves maximal time counter value. *)
    let t_max_time_counter := get_max_time_counter t in

    (* Builds the generic map of t. *)
    [assocg_ Transition.transition_type t_type;
    assocg_ Transition.input_arcs_number t_in_arcs_nb;
    assocg_ Transition.conditions_number t_conds_nb;
    assocg_ Transition.maximal_time_counter t_max_time_counter].

  (** Generates a part of the input map (static part) for the transition
      component representing transition [t]. *)

  Definition generate_trans_input_map (t : T sitpn) : InputMap :=
    match Is t with
    | Some (MkSTimeItval <| a, ninat b |> _) =>
      [(Transition.time_A_value, inl (e_nat a)); (Transition.time_B_value, inl (e_nat b))]
    | Some (MkSTimeItval <| a, i+ |> _) =>
      [(Transition.time_A_value, inl (e_nat a)); (Transition.time_B_value, inl (e_nat 0))]
    | None =>
      [(Transition.time_A_value, inl (e_nat 0)); (Transition.time_B_value, inl (e_nat 0))]
    end.

  (** Builds a TransMap entry for transition t. *)

  Definition generate_trans_map_entry (t : T sitpn) :
    optionE (T sitpn * (genmap * InputMap * OutputMap)) :=
    match getv eq_trans_dec t (tinfos sitpn sitpn_info) with
    | Some tinfo =>
      (* Retrieves t's generic map. *)
      let gmap := generate_trans_gen_map t tinfo in

      (* Retrieves p's static input map part. *)
      let tipmap := generate_trans_input_map t in

      (* Builds TransMap entry. *)
      Success (t, (gmap, tipmap, []))
    | None => Err ("Transition " ++ $$t ++ " is not referenced in SitpnInfo structure.")%string
    end.
  
  (** Returns the TransMap built out the list of transitions of [sitpn]. *)

  Definition generate_trans_map : optionE (TransMap sitpn) :=
    topt_map (fun t => generate_trans_map_entry t) (T2List sitpn) nat_to_T.
  
End GenerateTransMap.
