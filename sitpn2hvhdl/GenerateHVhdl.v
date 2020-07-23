(** * AST Generation from an Architecture. *)

Require Import Coqlib.
Require Import Sitpn2HVhdlTypes.
Require Import HVhdlTypes.
Require Import GlobalTypes.
Require Import String.
Require Import ListsPlus.
Require Import ListsDep.
Require Import dp.Sitpn.
Require Import dp.SitpnFacts.
Require Import AbstractSyntax.
Require Import Petri.

(* Import transformation functions. *)

Require Import GenerateInfos.
Require Import GenerateArchitecture.
Require Import GeneratePorts.

Open Scope abss_scope.

(** ** Helper functions. *)

Section GenerateCompInstFuns.
  
  (** Takes an identifier, an inputmap [ipmap] and a natural number [idx]. 
      Appends the association "id([idx]) => e" at the end of [ipmap], 
      and increments the index [idx].
   *)
  
  Let expr_to_cassocip (id : ident) :=
    (fun (params : inputmap * nat) (e : expr) =>
       let '(ipmap, idx) := params in
       (ipmap ++ [associp_ (id $[[idx]]) e], idx + 1)).
  
  (** Returns an [inputmap] (i.e, a list of [associp]), where
      a subelement of the port [id] is mapped to every element
      in the list [lofexprs].

      E.g: build_cport_assocs s [0; true; false] =>
      (s(0) => 0, s(1) => true, s(2) => false)

      Raises an error if port [id] is associated with
      an empty list of expressions.
   *)

  Definition build_icport_assocs (id : ident) (lofexprs : list expr) :
    optionE inputmap :=
    if lofexprs
    (* Error if id is associated with an empty list of expressions. 
       Cannot happen for input ports. *)
    then Err ("build_cport_assocs: Input port " ++ $$id ++ " must be associated.")%string
             (* Returns only the inputmap, not interested in the index count. *)
    else Success (fst (fold_left (expr_to_cassocip id) lofexprs (nil, 0))).
  
  (** Takes an InputMap entry [assoc] and transforms it into
      an [associp], i.e an element of H-VHDL abstract syntax.
   *)

  Definition imap_entry_to_associp
             (ipmap : inputmap) 
             (assoc : ident * (expr + list expr)) :
    optionE inputmap :=
    match assoc with
    (* Simple association "id => e" *)
    | (id, inl e) => Success (ipmap ++ [associp_ id e])
    (* Composite association, "id(0) => e0, id(1) => e1, ..." *)
    | (id, inr lofexprs) =>
      match build_icport_assocs id lofexprs with
      | Success ipmap' => Success (ipmap ++ ipmap')
      | Err msg => Err msg%string
      end
    end.
  
  (** Transforms an InputMap into an input port map as defined in
       H-VHDL abstract syntax. *)

  Definition InputMap_to_AST (imap : InputMap) : optionE inputmap :=
    oefold_left imap_entry_to_associp imap [].  

  (** Takes an identifier [id], an outputmap [opmap], a natural number
      [idx] and a name [n].

      Appends the association "id([idx]) => n" at the end of [opmap],
      and increments the index [idx].  *)
  
  Let expr_to_cassocop (id : ident) :=
    (fun (params : outputmap * nat) (n : name) =>
       let '(opmap, idx) := params in
       (opmap ++ [assocop_ (id $[[idx]]) (Some n)], idx + 1)).
  
  (** Returns an [outputmap] (i.e, a list of [assocop]), where
      a subelement of the port [id] is mapped to every element
      in the list [lofnames].

      E.g: build_ocport_assocs s [s1; s2] =>
      (s(0) => s1, s(1) => s2)
      
   *)

  Definition build_ocport_assocs (id : ident) (lofnames : list name) :
    outputmap :=
    (* If lofnames is empty, port id is open int he output port
       map. *)
    if lofnames then
      [assocop_ id None]
        (* Returns only the outputmap, not interested in the index count. *)
    else
      (fst (fold_left (expr_to_cassocop id) lofnames (nil, 0))).
  
  (** Takes an OutputMap entry [assoc] and transforms it into
      an [assocop], i.e an element of H-VHDL abstract syntax. *)

  Definition omap_entry_to_assocop
             (opmap : outputmap) 
             (assoc : ident * (name + list name)) :
    outputmap :=
    match assoc with
    (* Simple association "id => n" *)
    | (id, inl n) => opmap ++ [assocop_ id (Some n)]
    (* Composite association, "id(0) => n0, id(1) => n1, ..." *)
    | (id, inr lofnames) => opmap ++ build_ocport_assocs id lofnames
    end.
  
  (** Transforms an OutputMap into an output port map as defined in
      H-VHDL abstract syntax. *)

  Definition OutputMap_to_AST (omap : OutputMap) : outputmap :=
    fold_left omap_entry_to_assocop omap [].

  (** Generates the component instantiation statement corresponding
      to an [HComponent]. 
   *)

  Definition HComponent_to_comp_inst (compid : ident) (entid : ident) (hcomp : HComponent) : optionE cs :=  
    (* Destructs the component. *)
    let '(gmap, ipmap, opmap) := hcomp in
    (* Generates AST for input port map. *)
    match InputMap_to_AST ipmap with
    | Success ipmap_AST =>
      (* Generates AST for output port map. *)
      let opmap_AST := OutputMap_to_AST opmap in
      (* Returns the component instantiation statement. *)
      Success (cs_comp compid entid gmap ipmap_AST opmap_AST)
    | Err msg => Err msg
    end.  

  (** Returns [cstmt] alone if [ocstmt] is empty (i.e, None) and
      returns the parallel composition of the two otherwise.
   *)

  Definition compose_cs (ocstmt : option cs) (cstmt : cs) : option cs :=
    match ocstmt with
    | None => Some cstmt
    | Some cstmt' => Some (cstmt' // cstmt)
    end.
  
End GenerateCompInstFuns.

(** ** Generation of Place component.  *)

Section GeneratePlaceCompInst.

  Variable sitpn : Sitpn.

  (** Generates a component instantiation statement from the
      [HComponent] instance (i.e, intermediary representation)
      associated to place [p] in the PlaceMap of architecture [arch]. *)
  
  Definition generate_place_comp_inst
             (arch: Architecture sitpn)
             (nextid : ident)
             (obeh : option cs)
             (p : P sitpn) :
    optionE (option cs * ident) :=
    
    (* Destructs the architecture. *)
    let '(adecls, plmap, trmap, fmap, amap) := arch in

    (* Retrieves the component implementing place p. *)
    match getv Peqdec p plmap with
    | Some phcomp =>
      (* Translates p's HComponent into comp. inst. stmt. *)
      match HComponent_to_comp_inst nextid place_entid phcomp with
      | Success pcomp => 
        (* Returns the parallel composition of the existing behavior and 
           the generated component instantiation statement. *)
        Success (compose_cs obeh pcomp, nextid + 1)
      | Err msg => Err msg
      end
    (* Error case. *)
    | None => Err ("Place " ++ $$p ++ " is not referenced in the PlaceMap.")%string
    end.

  (** Generates a component instantiation statement for each place
      of [sitpn]. *)
  
  Definition generate_place_comp_insts
             (arch : Architecture sitpn)
             (nextid : ident)
             (obeh : option cs) :
    optionE (option cs * ident) :=
    (* Wrapper function around generate_place_comp_inst. *)
    let gen_pl_cinst :=
        (fun params p =>
           let '(obeh, nextid) := params in
           generate_place_comp_inst arch nextid obeh p)
    in
    (* Calls generate_place_comp_inst for each place of sitpn. *)
    topte_fold_left gen_pl_cinst (P2List sitpn) (obeh, nextid) nat_to_P.
  
End GeneratePlaceCompInst.

Arguments generate_place_comp_insts {sitpn}.

(** ** Generation of Transition component.  *)

Section GenerateTransCompInst.

  Variable sitpn : Sitpn.

  (** Generates a component instantiation statement from the
      [HComponent] instance (i.e, intermediary representation)
      associated to transition [t] in the TransMap of architecture
      [arch]. *)
  
  Definition generate_trans_comp_inst
             (arch: Architecture sitpn)
             (nextid : ident)
             (obeh : option cs)
             (t : T sitpn) :
    optionE (option cs * ident) :=
    
    (* Destructs the architecture. *)
    let '(adecls, plmap, trmap, fmap, amap) := arch in

    (* Retrieves the component implementing transition t. *)
    match getv Teqdec t trmap with
    | Some thcomp =>
      (* Translates t's HComponent into comp. inst. stmt. *)
      match HComponent_to_comp_inst nextid transition_entid thcomp with
      | Success tcomp => 
        (* Returns the parallel composition of the existing behavior and 
           the generated component instantiation statement. *)
        Success (compose_cs obeh tcomp, nextid + 1)
      | Err msg => Err msg
      end
    (* Error case. *)
    | None => Err ("Transition " ++ $$t ++ " is not referenced in the TransMap.")%string
    end.

  (** Generates a component instantiation statement for each transition
      of [sitpn]. *)
  
  Definition generate_trans_comp_insts
             (arch : Architecture sitpn)
             (nextid : ident)
             (obeh : option cs) :
    optionE (option cs * ident) :=
    (* Wrapper function around generate_trans_comp_inst. *)
    let gen_tr_cinst :=
        (fun params t =>
           let '(obeh, nextid) := params in
           generate_trans_comp_inst arch nextid obeh t)
    in
    (* Calls generate_trans_comp_inst for each transition of sitpn. *)
    topte_fold_left gen_tr_cinst (T2List sitpn) (obeh, nextid) nat_to_T.
  
End GenerateTransCompInst.

Arguments generate_trans_comp_insts {sitpn}.

(** ** Generation of all component instance statements. *)

Section GenerateCompInsts.

  Variable sitpn : Sitpn.
  
  (** Generates a component instantiation statement for each place and transition
      of [sitpn]. *)

  Definition generate_comp_insts (arch : Architecture sitpn) (nextid : ident) :
    optionE (option cs * ident) :=
    (* Generates place component inst. statements. 
       Begins with an empty behavior (i.e None). *)
    match generate_place_comp_insts arch nextid None with
    | Success (obeh, nextid') =>
      (* Generates place component inst. statements. 
         Completes the behavior yielded by the last function call. *)
      generate_trans_comp_insts arch nextid' obeh  
    | Err msg => Err msg
    end.
  
End GenerateCompInsts.

Arguments generate_comp_insts {sitpn}.

(** ** Transformation from an SITPN to H-VHDL code. *)

Section Sitpn2HVhdl.

  Variable sitpn : Sitpn.

  (** Generates an H-VHDL design from the elements passed
      in parameter.

      Raises an error if the behavior [obeh] is empty (i.e, None).
      Cannot generate a design with an empty behavior. *)

  Definition generate_design
             (entid archid : ident)
             (condports : list pdecl)
             (aports_and_ps : option (list pdecl * cs))
             (fports_and_ps : option (list pdecl * cs))
             (adecls : list adecl)
             (obeh : option cs) : optionE design :=
    (* Checks that the architecture body (obeh) is not empty. *)
    match obeh with
    | Some beh =>
      (* Builds the first part of the port list. *)
      let ports := [(pdecl_in Petri.clk tind_boolean); (pdecl_in Petri.rst tind_boolean)] ++ condports in
      (* Looks for action/function ports and processes. *)
      match aports_and_ps, fports_and_ps with
      | Some (aports, aps), Some (fports, fps) =>
        (* Appends action/function ports and processes to the port
           clause and the behavior. *)
        let ports' := ports ++ aports ++ fports in
        let beh' := beh // aps // fps in
        Success (design_ entid archid [] ports' adecls beh')
      | Some (aports, aps), None =>
        (* Appends action ports and process to the port clause and the
           behavior. *)
        let ports' := ports ++ aports in
        let beh' := beh // aps in
        Success (design_ entid archid [] ports' adecls beh')
      | None, Some (fports, fps) =>
        (* Appends function ports and process to the port clause and
           the behavior. *)
        let ports' := ports ++ fports in
        let beh' := beh // fps in
        Success (design_ entid archid [] ports' adecls beh')
      | None, None =>
        Success (design_ entid archid [] ports adecls beh)
      end
    | None => Err ("generate_design: the architecture body cannot be empty.")%string
    end .
  
  (** Defines the transformation function that generates an H-VHDL design
      from an SITPN. *)

  Definition sitpn_to_hvhdl (max_marking : nat) : optionE design :=
    (* Generates information from sitpn. *)
    match generate_sitpn_infos sitpn with
    | Success sitpn_info =>
      (* Generates the intermediate representation of the H-VHDL
         design's architecture. *)
      match generate_architecture sitpn_info Petri.ffid max_marking with
      | Success (arch, nfid) =>
        (* Generates the ports of the H-VHDL design, and connects them
           to the elements of the architecture. *)
        match generate_ports sitpn_info arch nfid with
        | Success (arch', nfid', condports, aports_and_ps, fports_and_ps) =>
        (* Generates the abstract syntax for the H-VHDL design
           architecture body, i.e the component instantiation statements
           for each place and transition of sitpn. *)
          match generate_comp_insts arch' nfid' with
          | Success (obeh, nfid'') =>
            (* Generates a fresh id for the generated design entity
               and archtecture. *)
            let entid := nfid'' in
            let archid := entid + 1 in
            (* Retrieves the architecture declarative part. *)
            let '(adecls, _, _, _, _) := arch' in
            (* Generates a H-VHDL design from the results of the
               previous function calls. *)
            generate_design entid archid condports aports_and_ps fports_and_ps adecls obeh
          | Err msg => Err msg
          end
        | Err msg => Err msg
        end
      | Err msg => Err msg
      end  
    | Err msg => Err msg
    end.
  
End Sitpn2HVhdl.
