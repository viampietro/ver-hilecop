(** * Generation of the interconnections between PCIs and TCIs *)

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

Section GenInter.

  Variable sitpn : Sitpn.

  (* Proof of decidability for the priority relation of [sitpn] *)

  Variable decpr : forall x y : T sitpn, {x >~ y} + {~x >~ y}.

  (* Alias for the state-and-error monad instantiated with the
     compile-time state.  *)

  Definition CompileTimeState := @Mon (Sitpn2HVhdlState sitpn).
  
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
    
End GenInter.

Arguments generate_interconnections {sitpn}.
