(** * AST Generation from an Architecture. *)

Require Import Coqlib.
Require Import Sitpn2HVhdlTypes.
Require Import HVhdlTypes.
Require Import GlobalTypes.
Require Import String.
Require Import ListsPlus.
Require Import dp.Sitpn.
Require Import dp.SitpnFacts.
Require Import AbstractSyntax.
Require Import Petri.

Open Scope ast_scope.

(** ** Helper functions. *)

Section GenerateASTFuns.
  
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
      an [assocop], i.e an element of H-VHDL abstract syntax.
   *)

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
    
End GenerateASTFuns.

(** ** Generation of Place component.  *)

Section GeneratePlaceAST.

  Variable sitpn : Sitpn.

  (** Generates a component instantiation statement from the
      [HComponent] instance (i.e, intermediary representation)
      associated to place [p] in the PlaceMap of architecture [arch]. *)
  
  Definition generate_place_AST
             (arch: Architecture sitpn)
             (nextid : ident)
             (p : P sitpn)
             (obeh : option cs) :
    optionE (option cs * ident) :=
    
    (* Destructs the architecture. *)
    let '(adecls, plmap, trmap) := arch in

    (* Retrieves the component implementing place p. *)
    match getv Peqdec p plmap with
    | Some phcomp =>
      (* Destructs the component. *)
      let '(pgmap, pipmap, popmap) := phcomp in
      (* Generates AST for input port map. *)
      match InputMap_to_AST pipmap with
      | Success pipmap_AST =>
        (* Generates AST for output port map. *)
        let popmap_AST := OutputMap_to_AST popmap in
        (* Creates the component instantiation statement. *)
        let pcomp := cs_comp nextid place_entid pgmap pipmap_AST popmap_AST in
        (* Checks if beh is empty or not. *)
        match obeh with
        | None => Success (Some pcomp, nextid + 1)
        | Some beh => Success (Some (beh // pcomp), nextid + 1)
        end
      | Err msg => Err msg
      end
    (* Error case. *)
    | None => Err ("Place " ++ $$p ++ " is not referenced in the PlaceMap.")%string
    end.

End GeneratePlaceAST.
