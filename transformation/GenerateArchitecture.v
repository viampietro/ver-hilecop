(** * Generation of the architecture body of a H-VHDL design. *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.ListPlus.
Require Import common.ListDep.
Require Import common.StateAndErrorMonad.
Require Import String.

Require Import sitpn.Sitpn.
Require Import sitpn.SitpnTypes.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Petri.
Require Import hvhdl.Place.
Require Import hvhdl.Transition.

Require Import transformation.Sitpn2HVhdlTypes.

Set Implicit Arguments.

Section GenArch.

  Variable sitpn : Sitpn.

  (* Proof of decidability for the priority relation of [sitpn] *)

  Variable decpr : forall x y : T sitpn, {x >~ y} + {~x >~ y}.

  (* Alias for the state-and-error monad instantiated with the
     compile-time state.  *)

  Definition CompileTimeState := @Mon (Sitpn2HVhdlState sitpn).
  
  (** ** Generation of place component instances (PCIs) *)

  Section GeneratePCIs.

    (** Adds content to the generic map [g] and partially builds the
        input port map based on the set of input transitions of place
        [p]. 
        
        Returns the new couple (genmap * inputmap).
     *)
    
    Definition build_pci_from_inputs (p : P sitpn) (pinfo : PlaceInfo sitpn) :
      CompileTimeState inputmap := 
      (* If the set of input transitions of [p] is empty. *)
      if (tinputs pinfo) then
        Ret [(ipa_ (Place.input_arcs_weights $[[0]]) 0);
             (ipa_ (Place.input_transitions_fired $[[0]]) false)]
      else
        let add_iaw_assoc '(i, idx) t :=
          match post t p with
          | Some (exist _ ω _) => Ret (i ++ [ipa_ (Place.input_arcs_weights $[[(e_nat idx)]]) ω], idx + 1) 
          | _ => Err ("build_pci: Transition " ++ $$t ++ " is not an input transition of place " ++ $$p)
          end
        in
        do iidx <- ListMonad.fold_left add_iaw_assoc (tinputs pinfo) ([], 0);
        Ret (fst iidx).

    (** Adds content the input port map [i], and partially builds an
        output port map for a PCI based on the set of output
        transitions of place [p]. *)
    
    Definition build_pci_from_outputs (p : P sitpn) (pinfo : PlaceInfo sitpn) (i : inputmap) :
      CompileTimeState (inputmap * outputmap) :=
      
      (* If the set of output transitions of [p] is empty. *)
      if (tconflict pinfo) ++ (toutputs pinfo) then
        Ret (i ++ [ipa_ (Place.output_arcs_weights $[[0]]) 0;
                     ipa_ (Place.output_arcs_types $[[0]]) basic;
                     ipa_ (Place.output_transitions_fired $[[0]]) false],
              [opa_simpl Place.output_arcs_valid None;
               opa_simpl Place.priority_authorizations None;
               opa_simpl Place.reinit_transitions_time None])
      else
        let add_oawt_assoc '(im, idx) t :=
          match pre p t with
          | Some (a, exist _ ω _) =>
              Ret (im ++ [ipa_ (Place.output_arcs_types $[[(e_nat idx)]]) a;
                          ipa_ (Place.output_arcs_weights $[[(e_nat idx)]]) ω], idx + 1) 
          | _ => Err ("build_pci: Transition " ++ $$t ++ " is not an output transition of place " ++ $$p)
          end
        in
        do iidx <- ListMonad.fold_left add_oawt_assoc ((tconflict pinfo) ++ (toutputs pinfo)) (i, 0);
        Ret (fst iidx, []).

    (** Adds content to the generic map [g] and the output port map
        [o] based on the set of actions associated with place [p]. *)
    
    Definition build_pci_from_acts
               (p : P sitpn) (pinfo : PlaceInfo sitpn) (o : outputmap) :
      CompileTimeState outputmap :=
      (* If the set of actions associated with [p] is empty. *)
      if acts pinfo then
        Ret (o ++ [opa_simpl Place.marked None])
      else
        do id__s <- get_nextid;
        do _ <- add_sig_decl (sdecl_ id__s tind_boolean);
        Ret (o ++ [opa_simpl Place.marked (Some ($id__s))]).
    
    (** Builds a PCI from a place [p] and its associated informations. *)

    Definition build_pci (p : P sitpn) (pinfo : PlaceInfo sitpn) (max_marking : nat) :
      CompileTimeState (genmap * inputmap * outputmap) :=

      (* Builds the generic map *)
      let g := [assocg_ Place.maximal_marking max_marking;
                assocg_ Place.input_arcs_number
                        (if tinputs pinfo then 1 else List.length (tinputs pinfo));
                assocg_ Place.output_arcs_number
                        (if (tconflict pinfo ++ toutputs pinfo)%list then 1
                         else List.length (tconflict pinfo ++ toutputs pinfo)%list)]
      in
       
      (* Adds content to the generic map and the input port map
         depending on the set of input transitions of [p].

         Initializes the generic map with the association [(mm,
       max_marking)].  *)
      
      do i1 <- build_pci_from_inputs p pinfo;
      
      (* Adds content to the generic map, the input port map, and the
         output port map depending on the set of output transitions of
         [p]. *)
      do io2 <- build_pci_from_outputs p pinfo i1;
      
      (* Adds content to the generic map, the input port map, and the
         output port map depending on the set of actions associated
         with [p]. *)
      let '(i2, o2) := io2 in
      do o3 <- build_pci_from_acts p pinfo o2;
      
      (* Returns the triplet generic map, input port map, and output
         port map. *)
      Ret (g, i2, o3).
    
    (** Generates a PCI from place [p]. *)

    Definition generate_pci (p : P sitpn) (max_marking : nat) :
      CompileTimeState unit :=
      (* Retrieves information about p. *)
      do pinfo <- get_pinfo p;

      (* Retrieves a fresh identifier [id__p] to name the newly
         generated PCI. *)
      do id__p <- get_nextid;
      
      (* Builds the generic map, input and output port maps for PCI
         [id__p]. *)
      do gio <- build_pci p pinfo max_marking;
      
      (* Adds the new PCI in the compile-time state's behavior. *)
      let '(g, i, o) := gio in
      do _ <- add_cs (cs_comp id__p place_id g i o);

      (* Adds a binding between place [p] and PCI [id__p] in γ. *)
      bind_place p id__p.
    
    (** Generates the PCIS in the behavior of compile-time state. *)

    Definition generate_pcis (b : P sitpn -> nat) : CompileTimeState unit :=
      do Plist <- get_lofPs;
      ListMonad.iter (fun p => generate_pci p (b p)) Plist.
    
  End GeneratePCIs.

  (** ** Generation of transition component instances (TCIs) *)

  Section GenerateTCIs.
    
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

    Definition build_tci_gmap (t : T sitpn) (tinfo : TransInfo sitpn) : CompileTimeState genmap :=

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

    (** Generates a part of the input port map for the TCI
        representing transition [t]. *)

    Definition init_tci_imap (t : T sitpn) (tinfo : TransInfo sitpn) :
      CompileTimeState inputmap :=      
      match Is t with
      | Some (MkTItval a (ninat b) _) =>
        Ret [ipa_ Transition.time_A_value a;
             ipa_ Transition.time_B_value b]
          
      | Some (MkTItval a i+ _) =>
        Ret [ipa_ Transition.time_A_value a;
             ipa_ Transition.time_B_value 0]
          
      | None =>
        Ret [ipa_ Transition.time_A_value 0;
             ipa_ Transition.time_B_value 0]
      end.

    (** Builds a TCI from a transition [t] and its associated informations. *)

    Definition build_tci (t : T sitpn) (tinfo : TransInfo sitpn) :
      CompileTimeState (genmap * inputmap * outputmap) :=
      (* Builds TCI's generic map. *)
      do g <- build_tci_gmap t tinfo;

      (* Initializes the input port map. *)
      do i <- init_tci_imap t tinfo;
      
      (* Adds a new internal signal [id__s] to the declaration list *)
      do id__s <- get_nextid;
      do _ <- add_sig_decl (sdecl_ id__s tind_boolean);
      
      (* Adds new elements to the input port map according to the set
         of input places and conditions of [t]. *)
      do i1 <- if pinputs tinfo then
                 Ret (i ++ [ipa_ (Transition.input_arcs_valid $[[0]]) true;
                            ipa_ (Transition.priority_authorizations $[[0]]) true;
                            ipa_ (Transition.reinit_time $[[0]]) (#id__s)])
               else Ret i;
      do i2 <- if conds tinfo then
                 Ret (i1 ++ [ipa_ (Transition.input_conditions $[[0]]) true])
               else Ret i1;
      Ret (g, i2, [opa_simpl Transition.fired (Some ($id__s))]).
      
    (** Generates a TCI which is a VHDL implementation of transition
        [t] and adds the TCI as a new concurrent statement in the
        behavior of the H-VHDL design being generated (i.e. the [beh]
        field of the compile-time state). *)

    Definition generate_tci (t : T sitpn) :
      CompileTimeState unit :=
      (* Retrieves information about p. *)
      do tinfo <- get_tinfo t;

      (* Retrieves a fresh identifier [id__t] to name the newly
         generated TCI. *)
      do id__t <- get_nextid;

      (* Builds the generic map, input and output port maps for TCI
         [id__t]. *)
      do gio <- build_tci t tinfo;
      
      (* Adds the new TCI in the compile-time state's behavior. *)
      let '(g, i, o) := gio in      
      do _ <- add_cs (cs_comp id__t trans_id g i o);

      (* Adds a binding between transition [t] and TCI [id__t] in γ. *)
      bind_transition t id__t.

    (** Generates the TCIS in the behavior of compile-time state. *)

    Definition generate_tcis : CompileTimeState unit :=
      do Tlist <- get_lofTs; ListMonad.iter generate_tci Tlist.
    
  End GenerateTCIs.

  (** Generates PCIs (Place Component Instances) and TCIs (Transition
      Component Instances), adds them as concurrent statements
      composing the behavior of the H-VHDL design being generated.

      PCIs and TCIs are a H-VHDL implementation of the places and the
      transitions of the input SITPN. *)

  Definition generate_architecture (b : P sitpn -> nat) :
    CompileTimeState unit :=
    (* Generates the PlaceMap that maps places to intermediary Place
         components. *)
    do _ <- generate_pcis b;
    (* Generates the TransMap that maps transitions to intermediary
         Transition components. *)
    generate_tcis.

End GenArch.

Arguments generate_pcis {sitpn}.
Arguments generate_tcis {sitpn}.
Arguments generate_architecture {sitpn}.

(* Unit tests *)

(* Require Import test.sitpn.WellDefinedSitpns. *)
(* Require Import GenerateInfos. *)

(* Local Notation "[ e ]" := (exist _ e _). *)

(* Eval cbv in (RedV ((do _ <- generate_sitpn_infos sitpn_simpl prio_simpl_dec; *)
(*                            do _ <- generate_architecture (fun p => 1); *)
(*                            get_beh) *)
(*                             (InitS2HState sitpn_simpl 10))). *)
