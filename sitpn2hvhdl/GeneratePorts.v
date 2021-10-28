(** * Primary ports generation. *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.ListPlus.
Require Import common.ListDep.
Require Import common.ListMonad.
Require Import common.StateAndErrorMonad.
Require Import String.
Require Import common.NatMap.
Require Import common.NatSet.

Require Import dp.Sitpn.
Require Import dp.SitpnFacts.
Require Import dp.SitpnTypes.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Petri.
Require Import hvhdl.Place.

Require Import sitpn2hvhdl.Sitpn2HVhdlTypes.
Require Import sitpn2hvhdl.Sitpn2HVhdlUtils.
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

  (** ** Generate and connect condition ports *)

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
      do id__t <- get_tci_id_from_binder t;
      do tci <- get_comp id__t;
      let '(id__e, g__t, i__t, o__t) := tci in
      do e   <- build_cond_expr id__c c t;
      do i__t' <- cassoc_imap i__t Transition.input_conditions e;
      put_comp id__t id__e g__t i__t' o__t.

    (** Creates an input port representing condition [c] and adds it to
        the [condports] list. Connects the created input port to the
        "input_conditions" port of all components representing the
        transitions associated to condition [c]. *)

    Definition generate_and_connect_cond_port (c : C sitpn) :
      CompileTimeState unit :=

      do id__c      <- get_nextid;
      do _        <- add_port_decl (pdecl_in id__c tind_boolean);
      do _        <- bind_condition c id__c;
      do trs_of_c <- get_cinfo c;
      iter (connect_in_cond_port id__c c) trs_of_c.

    (** Generates an input port for each condition [c] of [sitpn], and
        connects this input port to the TCIs representing the
        transitions associated with the condition [c]. *)

    Definition generate_and_connect_cond_ports : CompileTimeState unit :=
      do Clist <- get_lofCs; iter generate_and_connect_cond_port Clist.
    
  End GenerateAndConnectCondPorts.
  
  (** ** Generation of the action ports and action activation process *)

  Section GenerateActionPortsAndPs.
        
    (** Builds the "activation" expression that will determine the
        value of the output port [id__a] that reflects the activation
        status of action [a].
        
        This activation expression is assigned to port [id__a] in the
        generated action process. *)

    Definition build_activation_expr (a : A sitpn) :
      CompileTimeState expr :=
      do pls_of_a <- get_ainfo a;
      let add_or :=
        fun e p =>
          do id__p <- get_pci_id_from_binder p;
          do pci <- get_comp id__p;
          let '(id__e, g__p, i__p, o__p) := pci in
          do a <- actual Place.marked o__p;
          match a with
          | None => Err ("build_activation_expr: The marked port of PCI " ++ $$id__p ++ " is open.")
          | Some n => Ret (e_name n @|| e)
          end
      in
      ListMonad.fold_left add_or pls_of_a false.
    
    (** (1) Declares a new output port [id__a] representing the
        activation state of action [a] in the list of port
        declarations.
      
        (2) Adds the signal assignment statements that sets the value
            of the output port [id__a] in the reset and falling edge part
            of the generated "action" process.
      
        (3) Returns the new reset statement and falling statement. *)
    
    Definition generate_action_port_and_ss
               (rss_fss : ss * ss) 
               (a : A sitpn) : CompileTimeState (ss * ss) :=      
      do id__a <- get_nextid;
      do _   <- add_port_decl (pdecl_out id__a tind_boolean);
      do _   <- bind_action a id__a;
      do e   <- build_activation_expr a;
      let '(rss, fss) := rss_fss in
      Ret (rss;; id__a @<== false, fss;; id__a @<== e).
    
    (** (1) Generates the list of port declarations corresponding to
            the creation of output ports for each action of [sitpn].
      
        (2) Builds the "action" process and appends the generated
            H-VHDL design behavior.  *)

    Definition generate_action_ports_and_ps : CompileTimeState unit :=
      (* If there are no action in [sitpn], then no need to generate
         the action activation process. *)
      if (actions sitpn) then Ret tt
      else
        do Alist <- get_lofAs;
        do rss_fss <- fold_left generate_action_port_and_ss Alist (ss_null, ss_null);
        let '(rss, fss) := rss_fss in
        (* Builds the action activation process, and appends it to the
           behavior of the compile-time state. *)
        add_cs (cs_ps action_ps_id {[clk]} [] (Rst rss Else (Falling fss))).
    
  End GenerateActionPortsAndPs.

  (** ** Generation of the function execution ports and process *)

  Section GenerateFunPortsAndPs.

    (** Builds the "execution" expression that will determine the
        value of the output port [id__f] that reflects the execution
        status of function [f].
        
        This execution expression is assigned to port [id__f] in the
        generated "function" process. *)

    Definition build_execution_expr (f : F sitpn) : CompileTimeState expr :=
      do trs_of_f <- get_finfo f;
      let add_or :=
        fun e t =>
          do id__t <- get_tci_id_from_binder t;
          do tci <- get_comp id__t;
          let '(id__e, g__t, i__t, o__t) := tci in
          do a <- actual Transition.fired o__t;
          match a with
          | None => Err ("build_execution_expr: The fired port of TCI " ++ $$id__t ++ " is open.")
          | Some n => Ret (e_name n @|| e)
          end
      in
      ListMonad.fold_left add_or trs_of_f false.
    
    (** (1) Adds a new output port [id__f] representing the execution
            state of function [f] in the output port declaration list.
      
        (2) Adds the signal assignment statements that sets the value
            of the output port [id__f] in the reset and rising edge part of
            the ["function"] process.
      
        (3) Binds function [f] to the generated output port identifier
            [id__f] in [γ]. *)
    
    Definition generate_fun_port_and_ss (rstss_rss : ss * ss) (f : F sitpn) :
      CompileTimeState (ss * ss) :=
      do id__f <- get_nextid;
      do _   <- add_port_decl (pdecl_out id__f tind_boolean);
      do _   <- bind_function f id__f;
      do e   <- build_execution_expr f;
      let '(rstss, rss) := rstss_rss in
      Ret (rstss;; id__f @<== false, rss;; id__f @<== e).
    
    (** (1) Generates the list of port declarations corresponding to
        the creation of output ports for each function of [sitpn].
      
        (2) Builds the "function" process and appends it to the behavior
        of the generated H-VHDL design. *)

    Definition generate_fun_ports_and_ps : CompileTimeState unit :=
      (* If there are no function in sitpn, then no need to generate
         the function process. *)
      if (functions sitpn) then Ret tt
      else
        do Flist <- get_lofFs;
        do rstss_rss <- fold_left generate_fun_port_and_ss Flist (ss_null, ss_null);
        let (rstss, rss) := rstss_rss in
        (* Builds the function process and appends it to the behavior
           of the compile-time state. *)
        add_cs (cs_ps function_ps_id {[clk]} [] (Rst rstss Else (Rising rss))).
    
  End GenerateFunPortsAndPs.

  (** ** Generate ports and related processes. *)

  (** Generates the ports of an H-VHDL design implementing [sitpn],
      that is, the input ports implementing the conditions of [sitpn],
      the output ports implementing the actions and functions of
      [sitpn].
      
      Alongside the action and function ports, the action and function
      processes are generated. *)

  Definition generate_ports : CompileTimeState unit :=
    do _ <- generate_action_ports_and_ps;
    do _ <- generate_fun_ports_and_ps;
    generate_and_connect_cond_ports.

End GeneratePortsAndPs.

Arguments generate_ports {sitpn}.

(* Require Import test.sitpn.dp.WellDefinedSitpns. *)
(* Require Import GenerateInfos. *)

(* Local Notation "[ e ]" := (exist _ e _). *)

(* Require Import NatSet. *)

(* Eval compute in (RedS ((do _ <- generate_sitpn_infos sitpn_simpl prio_simpl_dec; *)
(*                         do _ <- generate_architecture Petri.MAXIMAL_GLOBAL_MARKING; *)
(*                         generate_ports) (InitS2HState sitpn_simpl Petri.ffid))). *)
