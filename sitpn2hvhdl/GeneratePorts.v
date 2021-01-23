(** * Primary ports generation. *)

Require Import common.Coqlib.
Require Import common.GlobalTypes.
Require Import common.ListPlus.
Require Import common.ListDep.
Require Import common.ListMonad.
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
      | Some (inr _) => Err ("connect_marked_port: the marked port of place "
                               ++ $$p ++ " must be of scalar type.")%string
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
      do Alist <- get_lofAs; iter add_action_map_entry Alist.

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
        do Alist <- get_lofAs;
        do rst_and_falling_ss <- fold_left
                                   generate_action_port_and_ss
                                   Alist (ss_null, ss_null);
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
      do Flist <- get_lofFs; iter add_fun_map_entry Flist.
    
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
        do Flist <- get_lofFs;
        do rst_and_rising_ss <- fold_left generate_fun_port_and_ss Flist (ss_null, ss_null);
        let (rstss, risingss) := rst_and_rising_ss in
        (* Builds the action activation process, and appends it to the
           behavior of the compile-time state. *)
        let body := (If (rst @= false) Then rstss Else (Rising risingss)) in
        let fps := cs_ps function_ps_id {[clk, rst]} [] body in
        add_cs fps.
    
  End GenerateFunPortsAndPs.
  
  (** ** Generate and connect condition ports. *)

  Section GenerateAndConnectCondPorts.
    
    (** Builds the expression that will result in the connection of
        the input port identifier [id__c], representing condition [c],
        to the input port map of the component representing transition
        [t] (i.e, via the ["input_conditions"] composite port).

      Raises an error if condition [c] and transition [t] are not
      associated in [sitpn].  *)
    
    Definition build_cond_expr (id__c : ident) (c : C sitpn) (t : T sitpn) :
      CompileTimeState expr :=
      match has_C t c with
      | one => Ret (#id__c)
      | mone => Ret (e_not (#id__c))
      | zero => Err ("build_cond_expr: Condition "
                       ++ $$c ++ " is not associated with transition " ++ $$t)%string
      end.
    
    (** Connects the input port [id__c], representing condition [c], in
        the input port map of the component representing transition
        [t].  *)

    Definition connect_in_cond_port (id__c : ident) (c : C sitpn) (t : T sitpn) :
      CompileTimeState unit :=

      do tcomp <- get_tcomp t;
      do condexpr <- build_cond_expr id__c c t;
      do tcomp' <- add_cassoc_to_ipmap Transition.input_conditions condexpr tcomp;
      set_tcomp t tcomp'.

    (** Connects the input port [id__c] to every input port map of T
        components representing the transitions of the [transs]
        list.  *)
    
    Definition connect_in_cond_ports
               (id__c : ident)
               (c : C sitpn)
               (transs : list (T sitpn)) :
      CompileTimeState unit :=
      (* Calls [connect_in_cond_port id__c c] on each transition of the
         transs list, thus modifying the architecture in the
         compile-time state.  *)
      iter (connect_in_cond_port id__c c) transs. 

    (** Creates an input port representing condition [c] and adds it to
        the [condports] list. Connects the created input port to the
        "input_conditions" port of all components representing the
        transitions associated to condition [c]. *)

    Definition generate_and_connect_cond_port (c : C sitpn) :
      CompileTimeState unit :=

      do id       <- get_nextid;
      do _        <- add_in_port (pdecl_in id tind_boolean);
      do _        <- bind_condition c id;
      do trs_of_c <- get_cinfo c;
      connect_in_cond_ports id c trs_of_c.

    (** Generates an input port for each condition of [sitpn], and
      connects this input port to the proper Transition components.
      
      Returns the new architecture, the next available identifier,
      and the list of created input ports representing conditions. *)

    Definition generate_and_connect_cond_ports : CompileTimeState unit :=

      (* Calls [generate_and_connect_cond_port] for each condition of [sitpn]. *)
      do Clist <- get_lofCs; iter generate_and_connect_cond_port Clist.
    
  End GenerateAndConnectCondPorts.

  (** ** Generate ports and related processes. *)

  Section GeneratePorts.
    
    (** Generates the ports of an H-VHDL design implementing [sitpn],
        that is, the input ports implementing the conditions of [sitpn],
        the output ports implementing the actions and functions of
        [sitpn].
      
        Alongside the action and function ports, the action activation
        and function execution processes are generated. *)

    Definition generate_ports : CompileTimeState unit :=
      do _ <- generate_action_ports_and_ps;
      do _ <- generate_fun_ports_and_ps;
      generate_and_connect_cond_ports.
    
  End GeneratePorts.

End GeneratePortsAndPs.

Arguments generate_ports {sitpn}.

(* Require Import test.sitpn.dp.WellDefinedSitpns. *)
(* Require Import GenerateInfos. *)

(* Local Notation "[ e ]" := (exist _ e _). *)

(* Require Import NatSet. *)

(* Eval compute in (RedS ((do _ <- generate_sitpn_infos sitpn_simpl prio_simpl_dec; *)
(*                         do _ <- generate_architecture Petri.MAXIMAL_GLOBAL_MARKING; *)
(*                         generate_ports) (InitS2HState sitpn_simpl Petri.ffid))). *)
