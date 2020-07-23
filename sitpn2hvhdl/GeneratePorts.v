(** * Primary ports generation. *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import ListsPlus.
Require Import ListsDep.
Require Import String.
Require Import dp.Sitpn.
Require Import dp.SitpnFacts.
Require Import dp.SitpnTypes.
Require Import dp.InfosTypes.
Require Import Sitpn2HVhdlTypes.
Require Import HVhdlTypes.
Require Import AbstractSyntax.
Require Import Petri.
Require Import Place.
Require Import GenerateArchitecture.

(** ** Common to action/function ports and process generation. *)

Section GeneratePortsAndPs.

  (** Builds a signal assignment statement assigning to identifier
      [id] the expression resulting of the composition of the
      expressions in [lofexprs] with the "@||" operator. *)

  Definition build_assign_or (id : ident) (lofexprs : list expr) : ss :=
    let assigne := fold_left (fun assigne e => assigne @|| e) lofexprs (e_bool false) in
    id @<== assigne.
  
  (** Add two signal assignments:
      
      - "id @<== false" in the first element of the returned ss
        couple.

      - "id @<== e" in the second element of the returned ss
        couple, where e the expression resulting of the composition of
        the expressions in [lofexprs] with the "@||" operator.  .
   *)
  
  Definition add_to_stmts
             (id : ident)
             (lofexprs : list expr)
             (stmts : option (ss * ss)) :
    (ss * ss) :=
    (* Checks if the couple of statements is empty or not.  None
       represents an empty sequential statement.  *)
    match stmts with
    | None => 
      (* Adds the signal assignment setting id to false in the
         first part of the couple. *)
      let ss1 := (id @<== false) in
      
      (* Adds the signal assignment setting id to some value in second
         part of the couple.  *)
      let ss2 := build_assign_or id lofexprs in
      (ss1, ss2)

    (* If statements exist, then add the assignment statements at the
       end as a sequence.  *)
    | Some (ss1, ss2) =>
      let ss1' := ss1 ;; (id @<== false) in
      let ss2' := ss2 ;; (build_assign_or id lofexprs) in
      (ss1', ss2')
    end.
  
End GeneratePortsAndPs.

(** ** Generation of the action ports and action activation process. *)

Section GenerateActionPortsAndPs.

  Variable sitpn : Sitpn.
  Variable sitpn_info : SitpnInfo sitpn.

  (** (1) Adds the signal connected to the "marked" output port of the
      component representing place [p] to the list of expressions
      [lofexprs].
      
      (2) If no "marked" output port exist in the output port map of
      the component representing [p], then an internal signal is
      created, and added to both the output port map and [lofexprs].

      (3) Returns the new architecture, the next available identifier,
      and the new list of expressions. *)
  
  Definition connect_marked_port
             (arch : Architecture sitpn)
             (nextid : ident)
             (lofexprs : list expr)
             (p : P sitpn) :
    optionE (Architecture sitpn * ident * list expr) :=
    (* Destructs the architecture. *)
    let '(adecls, plmap, trmap) := arch in
    
    (* Retrieves the component associated to place p in PlaceMap
       plmap.  *)
    match getv Peqdec p plmap with
    | Some (pgmap, pipmap, popmap) =>
      (* Checks if the "marked" port already belongs to the output
         port map of the component. *)
      match getv Nat.eq_dec Place.marked popmap with
      (* Case where marked is connected to a name.  Then, adds the
         equivalent expression at the end of lofexprs, and returns the
         triplet (architecture, nextid, lofexprs). *)
      | Some (inl n) => Success (arch, nextid, lofexprs ++ [e_name n])
      (* Error case, in the output port map [popmap], the marked port
         is connected to a list of names, albeit it must be of scalar
         type (boolean).  *)
      | Some (inr _) => Err ("The marked port of place " ++ $$p ++ " must be of scalar type.")%string
      (* Case where marked is not connected yet. Then, adds a new
         interconnection signal to the arch's declaration list and at
         the end of the lofexprs, modifies the output port map of
         place p, and returns the resulting triplet. *)
      | None =>
        let adecls' := adecls ++ [adecl_sig nextid tind_boolean] in
        let popmap' := setv Nat.eq_dec Place.marked (inl ($nextid)) popmap in
        let phcomp := (pgmap, pipmap, popmap') in
        let plmap' := setv Peqdec p phcomp plmap in
        let arch' := (adecls', plmap', trmap) in
        (* Increments nextid to return the next available identifier. *)
        Success (arch', nextid + 1, lofexprs ++ [#nextid])
      end
    (* Error case. *)
    | None => Err ("Place " ++ $$p ++ " is not referenced in the PlaceMap.")%string
    end.
  
  (** Returns a new architecture where the marked ports of all the
      places (precisely, the component representing the places) of the
      [places] list have been connected to an internal signal; the
      list of all such signals is returned (as a list of expressions)
      alongside the next available identifier.  *)
  
  Definition connect_marked_ports
             (arch : Architecture sitpn)
             (nextid : ident)
             (places : list (P sitpn)) :
    optionE (Architecture sitpn * ident * list expr) :=
    
    (* Destructs the architecture. *)
    let '(adecls, plmap, trmap) := arch in
    
    (* Wrapper around the connect_marked_port function. *)
    let connect_marked_port_fun :=
        (fun triplet p =>
           let '(arch, nextid, lofnames) := triplet in
           connect_marked_port arch nextid lofnames p)
    in
    (* Calls the connect_marked_port function over all places
         of the places list. *)
    oefold_left connect_marked_port_fun places (arch, nextid, []).

  (** Builds a ActionMap entry for action [a]. *)

  Definition add_action_map_entry
             (arch : Architecture sitpn)
             (nextid : ident)
             (amap : ActionMap sitpn) 
             (a : A sitpn) :
    optionE (Architecture sitpn * ident * ActionMap sitpn) :=
    (* Retrieves information about a. *)
    match getv Aeqdec a (ainfos sitpn sitpn_info) with
    | Some pls_of_a =>
      (* Calls connect_marked_ports over the list of places associated
       with action a. *)
      match connect_marked_ports arch nextid pls_of_a with
      | Success (arch', nextid', lofexprs) =>
        Success (arch', nextid', amap ++ [(a, lofexprs)])
      | Err msg => Err msg
      end
    (* Error case. *)
    | None => Err ("Action $$a is not referenced in the SitpnInfo structure.")%string
    end.
  
  (** Returns the ActionMap built out the list of actions of [sitpn]. *)

  Definition generate_action_map
             (arch : Architecture sitpn)
             (nextid : ident) :
    optionE (Architecture sitpn * ident * ActionMap sitpn) :=
    (* Wrapper around the add_action_map_entry function. *)
    let add_action_map_entry_fun :=
        (fun triplet a =>
           let '(arch, nextid, amap) := triplet in
           add_action_map_entry arch nextid amap a)
    in

    (* Calls add_action_map_entry on each action of sitpn. *)
    topte_fold_left add_action_map_entry_fun (A2List sitpn) (arch, nextid, []) nat_to_A.

  (** (1) Adds a new output port representing the activation state of
      action [a] in the list of port declarations [aports].
      
      (2) Adds the signal assignment statements that sets the value of
      the created output port in the reset and falling edge part of the
      action activation process.  
      
      (3) Returns the new list of port declarations, the
      new statements, and a fresh identifier. *)
  
  Definition generate_action_port_and_ss
             (amap : ActionMap sitpn)
             (a : A sitpn)
             (aports : list pdecl)
             (stmts : option (ss * ss))
             (nextid : ident) :
    optionE (list pdecl * (option (ss * ss)) * ident) :=
    (* Creates a new action port for representing the
       activation state of action a. *)
    let aports := aports ++ [pdecl_out nextid tind_boolean] in

    (* Retrieves the list of expressions from the ActionMap *)
    match getv Aeqdec a amap with
    | Some lofexprs =>
      
      (* Adds the proper signal assignment statements to the stmts
         couple.  *)
      let stmts' := add_to_stmts nextid lofexprs stmts in
      
      (* Don't forget to increment nextid to get a fresh identifier. *)
      Success (aports, Some stmts', nextid + 1)
    | None => Err ("Action a is not referenced in the ActionMap.")%string
    end.

  (** (1) Generates the list of port declarations corresponding to the
      creation of output ports for each action of [sitpn].
      
      (2) Builds the action activation process.

      (3) Returns the architecture, the action ports and ps, and the
      next available id.  *)

  Definition generate_action_ports_and_ps
             (arch : Architecture sitpn)
             (nextid : ident) :
    optionE (Architecture sitpn * ident * option (list pdecl * cs)) :=
    (* If there are no action in sitpn, then no need for the action
       activation process. *)
    if (actions sitpn) then Success (arch, nextid, None)
    else
      (* Generates the ActionMap that will help build the action ports
         and process. *)
      match generate_action_map arch nextid with
      | Success (arch', nextid', amap) => 
        (* Wrapper around the generate_action_port_and_ss function. *)
        let gen_action_pandss_fun :=
            (fun params a =>
               let '(aports, stmts, nextid) := params in
               generate_action_port_and_ss amap a aports stmts nextid)
        in
        (* Calls generate_action_port_and_ss on each action
           of the sitpn's action list. *)
        match topte_fold_left gen_action_pandss_fun (A2List sitpn) ([], None, nextid') nat_to_A with
        | Success (aports, stmts, nextid'') =>
          (* Checks that the action process statement body is not
           empty. *)
          match stmts with
          (* Cannot happen as the (actions sitpn) list is not empty;
             then there must be at least one signal assignment
             statement in stmts. *)
          | None => Err ("generate_action_ports_and_ps: "
                           ++ "The action activation process body cannot be empty.")%string
          | Some (rstss, fallingss) =>
            (* Builds the action activation process. *)
            let body := (If (rst @= false) Then rstss Else (Falling fallingss)) in
            let aps := cs_ps action_ps_id {[clk, rst]} [] body in
            (* Returns the architecture, the action ports and ps, and
               the next available id. *)
            Success (arch', nextid'', Some (aports, aps))
          end
        | Err msg => Err msg
        end
      | Err msg => Err msg
      end.
  
End GenerateActionPortsAndPs.

(** Set implicit arguments for generate_action_ports_and_ps. *)

Arguments generate_action_ports_and_ps {sitpn}.

(** ** Generation of the function execution ports and process. *)

Section GenerateFunPortsAndPs.

  Variable sitpn : Sitpn.
  Variable sitpn_info : SitpnInfo sitpn.

  (** Builds a FunMap entry for function [f]. *)

  Definition add_fun_map_entry
             (arch : Architecture sitpn)
             (nextid : ident)
             (fmap : list (F sitpn * list expr)) 
             (f : F sitpn) :
    optionE (Architecture sitpn * ident * FunMap sitpn) :=
    (* Retrieves information about a. *)
    match getv Feqdec f (finfos sitpn sitpn_info) with
    | Some trs_of_f =>
      (* Calls connect_marked_ports over the list of places associated
       with action a. *)
      match connect_fired_ports arch nextid trs_of_f with
      | Success (arch', nextid', lofexprs) =>
        Success (arch', nextid', fmap ++ [(f, lofexprs)])
      | Err msg => Err msg
      end
    (* Error case. *)
    | None => Err ("Action $$a is not referenced in the SitpnInfo structure.")%string
    end.
  
  (** Returns the ActionMap built out the list of actions of [sitpn]. *)

  Definition generate_fun_map
             (arch : Architecture sitpn)
             (nextid : ident) :
    optionE (Architecture sitpn * ident * FunMap sitpn) :=
    (* Wrapper around the add_action_map_entry function. *)
    let add_fun_map_entry_fun :=
        (fun triplet f =>
           let '(arch, nextid, fmap) := triplet in
           add_fun_map_entry arch nextid fmap f)
    in

    (* Calls add_fun_map_entry on each function of sitpn. *)
    topte_fold_left add_fun_map_entry_fun (F2List sitpn) (arch, nextid, []) nat_to_F.
  
  (** (1) Adds a new output port representing the execution state of
      function [f] in the list of port declarations [fports].
      
      (2) Adds the signal assignment statements that sets the value of
      the created output port in the reset and rising edge part of the
      function execution process.  
      
      (3) Returns the new list of port declarations, the
      new statements, and a fresh identifier. *)
  
  Definition generate_fun_port_and_ss
             (fmap : FunMap sitpn)
             (f : F sitpn)
             (fports : list pdecl)
             (stmts : option (ss * ss))
             (nextid : ident) :
    optionE (list pdecl * (option (ss * ss)) * ident) :=
    (* Creates a new function port representing execution state of
       function f. *)
    let fports := fports ++ [pdecl_out nextid tind_boolean] in

    (* Retrieves the list of expressions from the FunMap *)
    match getv Feqdec f fmap with
    | Some lofexprs =>

      (* Adds the proper signal assignment statements to the stmts
         couple.  *)
      let stmts' := add_to_stmts nextid lofexprs stmts in
      
      (* Don't forget to increment nextid to get a fresh identifier. *)
      Success (fports, Some stmts', nextid + 1)
    | None => Err ("generate_fun_port_and_ss: "
                     ++ "Function f is not referenced in the FunMap.")%string
    end.

  (** (1) Generates the list of port declarations corresponding to the
      creation of output ports for each function of [sitpn].
      
      (2) Builds the function execution process.
      
      (3) Returns the new architecture, the function ports and ps, and
      the next available identifier.  *)

  Definition generate_fun_ports_and_ps
             (arch : Architecture sitpn)
             (nextid : ident) :
    optionE (Architecture sitpn * ident * option (list pdecl * cs)) :=
    (* If there are no function in sitpn, then no need for the
       function execution process. *)
    if (functions sitpn) then Success (arch, nextid, None)
    else
      (* Generates the FunMap that will help built the function ports
         and ps. *)
      match generate_fun_map arch nextid with
      | Success (arch', nextid', fmap) =>
        (* Wrapper around the generate_fun_port_and_ss function. *)
        let gen_fun_pandss_fun :=
            (fun params f =>
               let '(fports, stmts, nextid) := params in
               generate_fun_port_and_ss fmap f fports stmts nextid)
        in
        (* Calls generate_fun_port_and_ss on each action
           of the sitpn's function list. *)
        match topte_fold_left gen_fun_pandss_fun (F2List sitpn) ([], None, nextid') nat_to_F with
        | Success (fports, stmts, nextid'') =>
          (* Checks that the function process body is not empty. *)
          match stmts with
          (* Cannot happen as the (functions sitpn) list is not empty;
             then there must be at least one signal assignment
             statement in stmts. *)
          | None => Err ("generate_fun_ports_and_ps: "
                           ++ "The function execution process body cannot be empty.")%string
          | Some (rstss, risingss) =>
            (* Builds the function execution process. *)
            let body := (If (rst @= false) Then rstss Else (Rising risingss)) in
            let fun_ps := cs_ps function_ps_id {[clk, rst]} [] body in
            (* Returns the new architecture, the function ports and
               ps, and the next available identifier *)
            Success (arch', nextid'', Some (fports, fun_ps))
          end
        | Err msg => Err msg
        end
      | Err msg => Err msg
      end.
  
End GenerateFunPortsAndPs.

(** Set implicit arguments for generate_action_ports_and_ps. *)

Arguments generate_fun_ports_and_ps {sitpn}.

(** ** Generate and connect condition ports. *)

Section GenerateAndConnectCondPorts.

  Variable sitpn : Sitpn.
  Variable sitpn_info : SitpnInfo sitpn.
  
  (** Builds the expression that will result in the connection of the
      input port representing condition [c] to the input port map of
      the component representing transition [t] (i.e, via the
      "input_conditions" composite port.

      Raises an error if condition [c] and transition [t] are not
      associated in [sitpn].  *)
  
  Definition build_cond_expr (condportid : ident) (c : C sitpn) (t : T sitpn) :
    optionE expr :=
    match has_C t c with
    | one => Success (#condportid)
    | mone => Success (e_not (#condportid))
    | zero => Err ("build_cond_expr: Condition c is not associated with transition t.")%string
    end.
  
  (** Connects the input port [condportid] that represents condition
      [c] to the input port map of the component representing
      transition [t] relatively to the association relation existing
      between [c] and [t].
   
      Returns a new Architecture, where the component representing [t]
      has been modified.

   *)

  Definition connect_in_cond_port
             (arch : Architecture sitpn)
             (condportid : ident)
             (c : C sitpn)
             (t : T sitpn) :
    optionE (Architecture sitpn) :=
    (* Destructs architecture. *)
    let '(adecls, plmap, trmap) := arch in

    (* Retrieves the component representing t in TransMap. *)
    match getv Teqdec t trmap with
    | Some thcomp =>
      (* Destructs component. *)
      let '(tgmap, tipmap, topmap) := thcomp in
      (* Builds the expression that will be tha actual part of the
         port association. *)
      match build_cond_expr condportid c t with
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
          Success (adecls, plmap, trmap')
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
             (condportid : ident)
             (c : C sitpn)
             (transs : list (T sitpn)) :
    optionE (Architecture sitpn) :=
    (* Wrapper around the connect_in_cond_port function. *)
    let conn_inc_port_fun :=
        (fun arch t =>
           connect_in_cond_port arch condportid c t)
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

    (* Retrieves the list of transitions associated to c. *)
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

  Variable sitpn : Sitpn.
  Variable sitpn_info : SitpnInfo sitpn.
  
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

Arguments generate_ports {sitpn}.
