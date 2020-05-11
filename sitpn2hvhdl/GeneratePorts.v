(** * Primary ports generation. *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import ListsPlus.
Require Import ListsDep.
Require Import String.
Require Import sets.Sitpn.
Require Import sets.SitpnFacts.
Require Import sets.InfosTypes.
Require Import Sitpn2HVhdlTypes.
Require Import HVhdlTypes.
Require Import AbstractSyntax.
Require Import Place.
Require Import GenerateArchitecture.

(** Adds an association between the simple port [sportid] and the
    expression [e] in the input port map [ipmap].
    
    Raises an error if [sportid] is referenced as a composite port 
    in input map [ipmap], or if [sportid] is already associated to
    an expression in input map [ipmap].
 *)

Definition add_sassoc_to_ipmap (ipmap : InputMap) (sportid : ident) (e : expr) :
  optionE InputMap :=
  
  (* Checks if sportid is known in ipmap. *)
  match getv Nat.eq_dec sportid ipmap with
  (* If sportid is already associated in ipmap, then raises an error. *)
  | Some (inl _) => Err ("add_sassoc_to_ipmap : sportid is already associated.")%string

  (* If sportid is a composite port in ipmap, then raises an error.  *)
  | Some (inr _) => Err ("add_sassoc_to_ipmap : sportid is a composite port.")%string

  (* If sportid is not known in ipmap, then adds the association
         between sportid and expression e in ipmap. *)
  | None =>
    Success (setv Nat.eq_dec sportid (inl e) ipmap)
  end.

(** Adds an association between the simple port [sportid] and the name
    [n] in the output port map [opmap].
    
    Raises an error if [sportid] is referenced as a composite port in
    output map [opmap], or if [sportid] is already associated in
    [opmap].  *)

Definition add_sassoc_to_opmap (opmap : OutputMap) (sportid : ident) (n : name) :
  optionE OutputMap :=
  
  (* Checks if sportid is known in opmap. *)
  match getv Nat.eq_dec sportid opmap with
  (* If sportid is already associated in opmap, then raises an error. *)
  | Some (inl _) => Err ("add_sassoc_to_opmap : sportid is already associated.")%string

  (* If sportid is a composite port in opmap, then raises an error.  *)
  | Some (inr _) => Err ("add_sassoc_to_opmap : sportid is a composite port.")%string

  (* If sportid is not known in opmap, then adds the association
     between sportid and name n in opmap. *)
  | None =>
    Success (setv Nat.eq_dec sportid (inl n) opmap)
  end.

(** ** Mapping actions to activation signals. *)

Section GenerateActionMap.

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
             (amap : list (A sitpn * list expr)) 
             (a : A sitpn) :
    optionE (Architecture sitpn * ident * list (A sitpn * list expr)) :=
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
    optionE (Architecture sitpn * ident * list (A sitpn * list expr)) :=
    (* Wrapper around the add_action_map_entry function. *)
    let add_action_map_entry_fun :=
        (fun triplet a =>
           let '(arch, nextid, amap) := triplet in
           add_action_map_entry arch nextid amap a)
    in

    (* Calls add_action_map_entry on each action of sitpn. *)
    topte_fold_left add_action_map_entry_fun (A2List sitpn) (arch, nextid, []) nat_to_A.
  
End GenerateActionMap.

(** ** Mapping functions to execution signals. *)

Section GenerateFunMap.

  Variable sitpn : Sitpn.
  Variable sitpn_info : SitpnInfo sitpn.

  (** Builds a FunMap entry for function [f]. *)

  Definition add_fun_map_entry
             (arch : Architecture sitpn)
             (nextid : ident)
             (fmap : list (F sitpn * list expr)) 
             (f : F sitpn) :
    optionE (Architecture sitpn * ident * list (F sitpn * list expr)) :=
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
    optionE (Architecture sitpn * ident * list (F sitpn * list expr)) :=
    (* Wrapper around the add_action_map_entry function. *)
    let add_fun_map_entry_fun :=
        (fun triplet f =>
           let '(arch, nextid, fmap) := triplet in
           add_fun_map_entry arch nextid fmap f)
    in

    (* Calls add_fun_map_entry on each function of sitpn. *)
    topte_fold_left add_fun_map_entry_fun (F2List sitpn) (arch, nextid, []) nat_to_F.
  
End GenerateFunMap.
