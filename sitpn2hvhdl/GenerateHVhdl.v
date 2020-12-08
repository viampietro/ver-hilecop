(** * AST Generation from an Architecture. *)

Require Import common.Coqlib.
Require Import common.GlobalTypes.
Require Import common.ListsPlus.
Require Import common.ListsDep.
Require Import common.StateAndErrorMonad.
Require Import common.ListsMonad.
Require Import String.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Petri.
Require Import hvhdl.HVhdlTypes.
Require Import dp.Sitpn.
Require Import dp.SitpnFacts.

Require Import sitpn2hvhdl.Sitpn2HVhdlTypes.

(* Import transformation functions. *)

Require Import sitpn2hvhdl.GenerateInfos.
Require Import sitpn2hvhdl.GenerateArchitecture.
Require Import sitpn2hvhdl.GeneratePorts.

Open Scope abss_scope.

(** ** Transformation from an SITPN to an H-VHDL design *)


Section Sitpn2HVhdl.

  Variable sitpn : Sitpn.

  (* Proof of decidability for the priority relation of [sitpn].
     Necessary to the [generate_sitpn_infos] function.
   *)
  Variable decpr : forall x y : T sitpn, {x >~ y} + {~x >~ y}.
  
  (* Alias for the state-and-error monad instantiated with the
     compile-time state.  *)

  Definition CompileTimeState := @Mon (Sitpn2HVhdlState sitpn).
  
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
      CompileTimeState inputmap :=
      if lofexprs
      (* Error if id is associated with an empty list of expressions. 
       Cannot happen for input ports. *)
      then Err ("build_cport_assocs: Input port " ++ $$id ++ " must be associated.")%string
               (* Returns only the inputmap, not interested in the index count. *)
      else Ret (fst (List.fold_left (expr_to_cassocip id) lofexprs (nil, 0))).
    
    (** Takes an InputMap entry [assoc] and transforms it into
      an [associp], i.e an element of H-VHDL abstract syntax.
     *)
    
    Definition imap_entry_to_associp
               (ipmap : inputmap) 
               (assoc : ident * (expr + list expr)) :
      CompileTimeState inputmap :=
      match assoc with
      (* Simple association "id => e" *)
      | (id, inl e) => Ret (ipmap ++ [associp_ id e])
      (* Composite association, "id(0) => e0, id(1) => e1, ..." *)
      | (id, inr lofexprs) =>
        do ipmap' <- build_icport_assocs id lofexprs;
        Ret (ipmap ++ ipmap')
      end.
    
    (** Transforms an InputMap into an input port map as defined in
       H-VHDL abstract syntax. *)

    Definition InputMap_to_AST (imap : InputMap) : CompileTimeState inputmap :=
      fold_left imap_entry_to_associp imap [].  

    (** Takes an identifier [id], an outputmap [opmap], a natural number
      [idx] and a name [n].

      Appends the association "id([idx]) => n" at the end of [opmap],
      and increments the index [idx].  *)
    
    Let expr_to_cassocop (id : ident) :=
      (fun (params : outputmap * nat) (n : name) =>
         let '(opmap, idx) := params in
         (opmap ++ [assocop_idx id (#idx) n], idx + 1)).
    
    (** Returns an [outputmap] (i.e, a list of [assocop]), where a
      subelement of the port [id] is mapped to every element in the
      list [lofnames].

      E.g: build_ocport_assocs s [s1; s2] => (s(0) => s1, s(1) => s2)
     
     *)

    Definition build_ocport_assocs (id : ident) (lofnames : list name) :
      CompileTimeState outputmap :=
      (* If lofnames is empty, port id is open int he output port
       map. *)
      if lofnames
      then Ret [assocop_simpl id None]
               (* Returns only the outputmap, not interested in the index count. *)
      else Ret (fst (List.fold_left (expr_to_cassocop id) lofnames (nil, 0))).
    
    (** Takes an OutputMap entry [assoc], transforms it into an
      [assocop], i.e an element of H-VHDL abstract syntax, and adds it
      to the output port map [opmap]. *)

    Definition omap_entry_to_assocop
               (opmap : outputmap) 
               (assoc : ident * (option name + list name)) :
      CompileTimeState outputmap :=
      match assoc with
      (* Simple association "id => n" *)
      | (id, inl optn) => Ret (opmap ++ [assocop_simpl id optn])
      (* Composite association, "id(0) => n0, id(1) => n1, ..." *)
      | (id, inr lofnames) =>
        do opmap' <- build_ocport_assocs id lofnames;
        Ret (opmap ++ opmap')
      end.
    
    (** Transforms an OutputMap into an output port map as defined in
      H-VHDL abstract syntax. *)

    Definition OutputMap_to_AST (omap : OutputMap) : CompileTimeState outputmap :=
      fold_left omap_entry_to_assocop omap [].

    (** Generates the component instantiation statement corresponding
      to an [HComponent]. 
     *)

    Definition HComponent_to_comp_inst (compid : ident) (entid : ident) (comp : HComponent) :
      CompileTimeState cs :=
      
      (* Destructs the component. *)
      let '(gmap, ipmap, opmap) := comp in
      
      (* Generates AST for input port map. *)
      do ipmap_AST <- InputMap_to_AST ipmap;
      (* Generates AST for output port map. *)
      do opmap_AST <- OutputMap_to_AST opmap;

      (* Returns the component instantiation statement. *)
      Ret (cs_comp compid entid gmap ipmap_AST opmap_AST).
    
  End GenerateCompInstFuns.

  (** ** Generation of Place component.  *)

  Section GeneratePlaceCompInst.

    (** - Generates a P component instantiation statement from the
        [HComponent] instance (i.e, intermediary representation)
        associated to place [p] in the architecture of the
        compile-time state.

        - Binds place [p] to the corresponding P component identifier
        in γ.

        - Adds the P component instantiation statement to the behavior
        of the compile-time state.  *)
    
    Definition generate_place_comp_inst (p : P sitpn) :
      CompileTimeState unit :=

      do id         <- get_nextid;
      do _          <- bind_place p id;
      do pcomp      <- get_pcomp p;
      do pcomp_inst <- HComponent_to_comp_inst id place_entid pcomp;
      add_cs pcomp_inst.

    (** Calls [generate_place_comp_inst] on each place of
        [sitpn], thus modifying the compile-time state. *)
    
    Definition generate_place_comp_insts : CompileTimeState unit :=
      titer generate_place_comp_inst (P2List sitpn) nat_to_P.
    
  End GeneratePlaceCompInst.

  (** ** Generation of Transition components  *)

  Section GenerateTransCompInst.

    (** - Generates a T component instantiation statement from the
        [HComponent] instance (i.e, intermediary representation)
        associated to transition [t] in the architecture of the
        compile-time state.

        - Binds transition [t] to the corresponding T component
        identifier in γ.

        - Adds the T component instantiation statement to the behavior
        of the compile-time state.  *)
    
    Definition generate_trans_comp_inst (t : T sitpn) :
      CompileTimeState unit :=

      do id         <- get_nextid;
      do tcomp      <- get_tcomp t;
      do tcomp_inst <- HComponent_to_comp_inst id transition_entid tcomp;
      do _          <- bind_transition t id;
      add_cs tcomp_inst.

    (** Calls [generate_trans_comp_inst] on each transition of
        [sitpn], thus modifying the compile-time state. *)
    
    Definition generate_trans_comp_insts : CompileTimeState unit :=
      titer generate_trans_comp_inst (T2List sitpn) nat_to_T.
    
  End GenerateTransCompInst.

  (** ** Generation of an H-VHDL design *)

  (** Generates a component instantiation statement for each place and
      transition of [sitpn]. *)

  Definition generate_comp_insts : CompileTimeState unit :=
    do _ <- generate_place_comp_insts; generate_trans_comp_insts.
        
  (** Defines the transformation function that generates an H-VHDL design
      from an SITPN. *)
  
  Definition sitpn_to_hvhdl (entid archid : ident) (max_marking : nat) :
    (design * Sitpn2HVhdlMap sitpn) + string :=
    RedV ((do _ <- generate_sitpn_infos sitpn decpr;
           do _ <- generate_architecture max_marking;
           do _ <- generate_ports;
           do _ <- generate_comp_insts;
           do s <- Get;
           let '(sigs, _, _, _, _) := (arch s) in
           Ret ((design_ entid archid [] ((iports s) ++ (oports s)) sigs (behavior s)), (γ s)))
            (InitS2HState sitpn Petri.ffid)).
  
End Sitpn2HVhdl.
