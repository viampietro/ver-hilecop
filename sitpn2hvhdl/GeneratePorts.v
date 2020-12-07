(** * Primary ports generation. *)

Require Import common.Coqlib.
Require Import common.GlobalTypes.
Require Import common.ListsPlus.
Require Import common.ListsDep.
Require Import common.ListsMonad.
Require Import common.StateAndErrorMonad.
Require Import String.
Require Import dp.Sitpn.
Require Import dp.SitpnFacts.
Require Import dp.SitpnTypes.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Petri.
Require Import hvhdl.Place.
Require Import sitpn2hvhdl.Sitpn2HVhdlTypes.
Require Import sitpn2hvhdl.GenerateArchitecture.

(** ** Common to action/function ports and process generation. *)

Section GeneratePortsAndPs.

  Variable sitpn : Sitpn.

  (* Alias for the state-and-error monad instantiated with the
     compile-time state.  *)

  Definition CompileTimeState := @Mon (Sitpn2HVhdlState sitpn).
  
  (** Builds a signal assignment statement assigning to identifier
      [id] the expression resulting of the composition of the
      expressions in [lofexprs] with the "@||" operator. *)

  Definition build_assign_or (id : ident) (lofexprs : list expr) : ss :=
    let assigne := List.fold_left (fun assigne e => assigne @|| e) lofexprs (e_bool false) in
    id @<== assigne.
  
  (** Add two signal assignments:
      
      - "id @<== false" in the reset sequence statement.

      - "id @<== e" in the assignment sequence statement, where [e] is
        the expression resulting of the composition of the expressions
        in [lofexprs] with the "@||" operator.  .  *)
  
  Definition add_to_stmts
             (id : ident)
             (lofexprs : list expr)
             (rst_and_assign_ss : ss * ss) : CompileTimeState (ss * ss) :=
    let (rstss, assignss) := rst_and_assign_ss in
    Ret (rstss;; (id @<== false), assignss;; (build_assign_or id lofexprs)).
  
  (** ** Generation of the action ports and action activation process. *)

  Section GenerateActionPortsAndPs.
    
    (** (1) Adds the signal connected to the "marked" output port of the
      component representing place [p] to the list of expressions
      [lofexprs].
      
      (2) If no "marked" output port exist in the output port map of
      the component representing [p], then an internal signal is
      created, and added to both the output port map and [lofexprs].

      (3) Returns the new architecture, the next available identifier,
      and the new list of expressions. *)
    
    Definition connect_marked_port
               (lofexprs : list expr)
               (p : P sitpn) :
      CompileTimeState (list expr) :=

      do pcomp <- get_pcomp p;
      do opt_marked_actual <- get_actual_of_out_port Place.marked pcomp;

      match opt_marked_actual with
      (* Case where marked is connected to a name.  Then, adds the
       equivalent expression at the end of lofexprs, and returns the
       triplet (architecture, nextid, lofexprs). *)
      | Some (inl optn) =>
        match optn with
        | Some n => Ret (lofexprs ++ [e_name n])
        | _ => Err ("connect_marked_port: the marked port of P component "
                      ++ $$p ++ " is open.")
        end
      (* Error case, the [marked] port is connected to a list of names
       is the output port map of [pcomp], albeit it must be of scalar
       type (boolean).  *)
      | Some (inr _) => Err ("The marked port of place " ++ $$p ++ " must be of scalar type.")%string
      (* Case where marked is not connected yet. Then, adds a new
       interconnection signal to the arch's declaration list and at
       the end of the lofexprs, modifies the output port map of
       place p, and returns the resulting triplet. *)
      | None =>
        do id <- get_nextid;
        do pcomp' <- connect_out_port Place.marked (inl (Some ($id))) pcomp;
        do _ <- set_pcomp p pcomp';
        do _ <- add_sig_decl (sdecl_ id tind_boolean);
        
        (* Increments nextid to return the next available identifier. *)
        Ret (lofexprs ++ [#id])      
      end.
    
    (** Connects the "marked" output ports of all P components
      associated to the places of the [places] list to an internal
      signal; the list of all such signals is returned (as a list of
      expressions).  *)
    
    Definition connect_marked_ports (places : list (P sitpn)) :
      CompileTimeState (list expr) :=
      
      (* Calls the connect_marked_port function over all places of the
       places list. *)
      fold_left connect_marked_port places [].

    (** Builds a ActionMap entry for action [a]. *)

    Definition add_action_map_entry (a : A sitpn) :
      CompileTimeState unit :=
      do pls_of_a <- get_ainfo a;
      do sigs_of_a <- connect_marked_ports pls_of_a;
      set_aport a sigs_of_a.
    
    (** Returns the ActionMap built out the list of actions of [sitpn]. *)

    Definition generate_action_map : CompileTimeState unit :=
      (* Calls add_action_map_entry on each action of sitpn. *)
      titer add_action_map_entry (A2List sitpn) nat_to_A.

    (** (1) Adds a new output port representing the activation state of
      action [a] in the list of port declarations [aports].
      
      (2) Adds the signal assignment statements that sets the value of
      the created output port in the reset and falling edge part of the
      action activation process.  
      
      (3) Returns the new list of port declarations, the
      new statements, and a fresh identifier. *)
    
    Definition generate_action_port_and_ss
               (rst_and_falling_ss : ss * ss) 
               (a : A sitpn) : CompileTimeState (ss * ss) :=      
      do id <- get_nextid;
      do _ <- add_out_port (pdecl_out id tind_boolean);
      do _ <- bind_action a id;
      do lofexprs <- get_aport a;
      add_to_stmts id lofexprs rst_and_falling_ss.
    
    (** (1) Generates the list of port declarations corresponding to the
      creation of output ports for each action of [sitpn].
      
      (2) Builds the action activation process.

      (3) Returns the architecture, the action ports and ps, and the
      next available id.  *)

    Definition generate_action_ports_and_ps : CompileTimeState unit :=
      (* If there are no action in sitpn, then no need for the action
         activation process. *)
      if (actions sitpn) then Ret tt
      else
        do _ <- generate_action_map;
        
        do rst_and_falling_ss <- tfold_left
                                   generate_action_port_and_ss
                                   (A2List sitpn) (ss_null, ss_null) nat_to_A;
        let (rstss, fallingss) := rst_and_falling_ss in
        (* Builds the action activation process, and appends it to the
           behavior of the compile-time state. *)
        let body := (If (rst @= false) Then rstss Else (Falling fallingss)) in
        let aps := cs_ps action_ps_id {[clk, rst]} [] body in
        add_cs aps.
    
  End GenerateActionPortsAndPs.

  (** ** Generation of the function execution ports and process. *)

  Section GenerateFunPortsAndPs.

    (** Builds a FunMap entry for function [f]. *)

    Definition add_fun_map_entry (f : F sitpn) : CompileTimeState unit :=
      do transs_of_f <- get_finfo f;
      do sigs_of_f <- connect_fired_ports transs_of_f;
      set_fport f sigs_of_f.
          
    (** Returns the ActionMap built out the list of actions of [sitpn]. *)

    Definition generate_fun_map : CompileTimeState unit :=
      (* Calls add_fun_map_entry on each function of sitpn. *)
      titer add_fun_map_entry (F2List sitpn) nat_to_F.
    
    (** (1) Adds a new output port representing the execution state of
      function [f] in the output port declaration list.
      
      (2) Adds the signal assignment statements that sets the value of
      the created output port in the reset and rising edge part of the
      ["function"] execution process.  
      
      (3) Binds function [f] to the generated output port identifier. *)
    
    Definition generate_fun_port_and_ss (rst_and_rising_ss : ss * ss) (f : F sitpn) :
      CompileTimeState (ss * ss) :=
      do id <- get_nextid;
      do _ <- add_out_port (pdecl_out id tind_boolean);
      do _ <- bind_function f id;
      do lofexprs <- get_fport f;
      add_to_stmts id lofexprs rst_and_rising_ss.

    (** (1) Generates the list of port declarations corresponding to the
        creation of output ports for each function of [sitpn].
      
      (2) Builds the function execution process.
      
      (3) Returns the new architecture, the function ports and ps, and
      the next available identifier.  *)

    Definition generate_fun_ports_and_ps : CompileTimeState unit :=
      (* If there are no function in sitpn, then no need for the
       function execution process. *)
      if (functions sitpn) then Ret tt
      else
        do _ <- generate_fun_map;
        
        do rst_and_rising_ss <- tfold_left
                                   generate_fun_port_and_ss
                                   (F2List sitpn) (ss_null, ss_null) nat_to_F;
        let (rstss, risingss) := rst_and_rising_ss in
        (* Builds the action activation process, and appends it to the
           behavior of the compile-time state. *)
        let body := (If (rst @= false) Then rstss Else (Rising risingss)) in
        let fps := cs_ps function_ps_id {[clk, rst]} [] body in
        add_cs fps.
    
  End GenerateFunPortsAndPs.
  
  (** ** Generate and connect condition ports. *)

  Section GenerateAndConnectCondPorts.
    
    (** Builds the expression that will result in the connection of the
      input port representing condition [c] to the input port map of
      the component representing transition [t] (i.e, via the
      ["input_conditions"] composite port).

      Raises an error if condition [c] and transition [t] are not
      associated in [sitpn].  *)
    
    Definition build_cond_expr (id__c : ident) (c : C sitpn) (t : T sitpn) :
      optionE expr :=
      match has_C t c with
      | one => Success (#id__c)
      | mone => Success (e_not (#id__c))
      | zero => Err ("build_cond_expr: Condition c is not associated with transition t.")%string
      end.
    
    (** Connects the input port [id__c] that represents condition
      [c] to the input port map of the component representing
      transition [t] relatively to the association relation existing
      between [c] and [t].
   
      Returns a new Architecture, where the component representing [t]
      has been modified.

     *)

    Definition connect_in_cond_port
               (arch : Architecture sitpn)
               (id__c : ident)
               (c : C sitpn)
               (t : T sitpn) :
      optionE (Architecture sitpn) :=
      (* Destructs architecture. *)
      let '(adecls, plmap, trmap, fmap, amap) := arch in

      (* Retrieves the component representing t in TransMap. *)
      match getv Teqdec t trmap with
      | Some thcomp =>
        (* Destructs component. *)
        let '(tgmap, tipmap, topmap) := thcomp in
        (* Builds the expression that will be tha actual part of the
         port association. *)
        match build_cond_expr id__c c t with
        | Success conde =>
          (* Builds the port association between "input_conditions" and
           expression conde. *)
          match add_cassoc_to_ipmap tipmap Transition.input_conditions conde with
          | Success tipmap' =>
            (* Updates the component representing transition t. *)
            let thcomp' := (tgmap, tipmap', topmap) in
            (* Updates the architecture's TransMap. *)
            let trmap' := setv Teqdec t thcomp' trmap in
            (* Returns the new architecture *)
            Success (adecls, plmap, trmap', fmap, amap)
          | Err msg => Err msg
          end
        | Err msg => Err msg
        end
      (* Error case. *)
      | None => Err ("connect_condition_port:"
                       ++ "Transition " ++ $$t ++
                       " is not referenced in the TransMap.")%string
      end.

    (** Connects the input port [cportid] to every component's input
      mapping representing the transitions that are elements of the
      list [transs].  *)
    
    Definition connect_in_cond_ports
               (arch : Architecture sitpn)
               (id__c : ident)
               (c : C sitpn)
               (transs : list (T sitpn)) :
      optionE (Architecture sitpn) :=
      (* Wrapper around the connect_in_cond_port function. *)
      let conn_inc_port_fun :=
          (fun arch t => connect_in_cond_port arch id__c c t)
      in
      (* Calls connect_in_cond_port on each transition of the transs
       list and returns the new architecture (or an error).  *)
      oefold_left conn_inc_port_fun transs arch. 

    (** Creates an input port representing condition [c] and adds it to
      the [condports] list. Connects the created input port to the
      "input_conditions" port of all components representing the
      transitions associated to condition [c]. *)

    Definition generate_and_connect_cond_port
               (arch : Architecture sitpn)
               (nextid : ident)
               (condports : list pdecl)
               (c : C sitpn) :
      optionE (Architecture sitpn * ident * list pdecl) :=

      (* Port id for condition c is the next available id. *)
      let cportid := nextid in
      
      (* Creates a new input port representing condition c. *)
      let condports := condports ++ [pdecl_in cportid tind_boolean] in

      (* Retrieves The List Of transitions associated to c. *)
      match getv Ceqdec c (cinfos sitpn_info) with
      | Some transs =>
        (* Connects cportid to the input_conditions port of Transition
         components representing transitions of the transs list. *)
        match connect_in_cond_ports arch cportid c transs with
        | Success arch' => Success (arch', nextid + 1, condports)
        | Err msg => Err msg
        end
      | None => Err ("Condition $$c is not referenced in the SitpnInfo structure.")%string
      end.

    (** Generates an input port for each condition of [sitpn], and
      connects this input port to the proper Transition components.
      
      Returns the new architecture, the next available identifier,
      and the list of created input ports representing conditions. *)

    Definition generate_and_connect_cond_ports
               (arch : Architecture sitpn)
               (nextid : ident) :
      optionE (Architecture sitpn * ident * list pdecl) :=

      (* Wrapper around the generate_and_connect_cond_port function. *)
      let gen_and_conn_cports_fun :=
          (fun params c =>
             let '(arch, nextid, condports) := params in
             generate_and_connect_cond_port arch nextid condports c)
      in

      (* Calls generate_and_connect_cond_port for each condition of sitpn. *)
      topte_fold_left gen_and_conn_cports_fun (C2List sitpn) (arch, nextid, []) nat_to_C.
    
  End GenerateAndConnectCondPorts.

  (** Set implicit arguments for generate_action_ports_and_ps. *)

  Arguments generate_and_connect_cond_ports {sitpn}.

  (** ** Generate ports and related processes. *)

  Section GeneratePorts.
    
    (** Generates the ports of an H-VHDL design implementing [sitpn],
      that is, the input ports implementing the conditions of [sitpn],
      the output ports implementing the actions and functions of
      [sitpn].
      
      Alongside the action and function ports, the action activation
      and function execution processes are generated.

      If there are no condition in [sitpn] an empty list will stand as
      the 3rd element of the returned 5-uplet; if there are no action
      or function in [sitpn] then None is returned in the place of 4th
      or 5th element of the returned 5-uplet.  *)

    Definition generate_ports (arch : Architecture sitpn) (nextid : ident) :
      optionE (Architecture sitpn * ident * list pdecl * option (list pdecl * cs) * option (list pdecl * cs)) :=

      (* Generates the output port list representing actions and the
       action activation process. *)
      match generate_action_ports_and_ps sitpn_info arch nextid with
      (* Ports and process have been successfully generated. *)
      | Success (arch0, nextid0, aports_and_ps) =>
        (* Generates the output port list representing functions and the
         function execution process. *)
        match generate_fun_ports_and_ps sitpn_info arch0 nextid0 with
        | Success (arch1, nextid1, fports_and_ps) =>
          (* Generates the input port list representing conditions, and
         connects the ports to the associated transition
         components. *)
          match generate_and_connect_cond_ports sitpn_info arch1 nextid1  with
          | Success (arch2, nextid2, condports) =>
            Success (arch2, nextid2, condports, aports_and_ps, fports_and_ps)
          | Err msg => Err msg
          end
        | Err msg => Err msg
        end
      | Err msg => Err msg
      end.
    
  End GeneratePorts.

End GeneratePortsAndPs.

Arguments generate_ports {sitpn}.

(* Require Import test.sitpn.dp.WellDefinedSitpns. *)
(* Require Import GenerateInfos. *)

(* Local Notation "[ e ]" := (exist _ e _). *)

(* Require Import NatSet. *)

(* Eval compute in (RedS ((do _ <- generate_sitpn_infos sitpn_simpl prio_simpl_dec; *)
(*                         do _ <- generate_architecture 255; *)
(*                         generate_action_ports_and_ps) *)
(*                          (InitS2HState sitpn_simpl 10))). *)
