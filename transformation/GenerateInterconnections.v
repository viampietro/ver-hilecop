(** * Generation of the interconnections between PCIs and TCIs *)

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
Require Import transformation.Sitpn2HVhdlUtils.

Set Implicit Arguments.

Section GenInter.

  Variable sitpn : Sitpn.

  (* Proof of decidability for the priority relation of [sitpn] *)

  Variable decpr : forall x y : T sitpn, {x >~ y} + {~x >~ y}.

  (* Alias for the state-and-error monad instantiated with the
     compile-time state.  *)

  Definition CompileTimeState := @Mon (Sitpn2HVhdlState sitpn).
  
  Local Open Scope abss_scope.

  (** Retrieves the TCI [id__t] associated with transition [t], and
      connects the [idx-th] element of the [itf] input port with the
      actual part of the [fired] output port.
      
      Returns the modified [i__p] input port map, and an incremented
      index.  *)

  Definition connect_to_input_tci
             (i__p : inputmap)
             (idx : nat)
             (t : T sitpn) :
    CompileTimeState (inputmap * nat) :=
    do id__t <- get_tci_id_from_binder t;
    do tci <- get_comp id__t;
    let '(id__e, g__t, i__t, o__t) := tci in
    do a <- actual Transition.fired o__t;
    match a with
    | None => Err ("connect_to_input_tci: The fired port of TCI " ++ $$id__t ++ " is open.")
    | Some n =>
        Ret (i__p ++ [associp_ (Place.input_transitions_fired $[[idx]]) (e_name n)], (idx + 1)%nat)
    end.

  (** Iterates and calls the [connect_to_input_tci] function over the
      set of input transitions of a place [p]. *)
  
  Definition connect_to_input_tcis
             (pinfo : PlaceInfo sitpn)
             (i__p : inputmap) :
    CompileTimeState inputmap :=
    do iidx <- ListMonad.fold_left (fun '(i, idx) => connect_to_input_tci i idx) (tinputs pinfo) (i__p, 0%nat);
    Ret (fst iidx).

  (** Parameters:

      Assume there is a place [p] such that:

      - [pinfo] represents the information associated with [p].

      - [i__p] and [o__p] represents the input and output port maps of a
        PCI [id__p], associated with [p] through the [γ] binder.

      - [t] is a conflicting output transition of [p].

      Retrieves the TCI [id__t] associated with transition [t], and
      connects elements of the input port map [i__p] and the output port
      map [o__p] to elements of the input and output port maps of the
      TCI [id__t].

      Replaces the TCI [id__t] by its modified version in the
      compile-time state behavior.
      
      Returns the modified [i__p] input port map, the modified [o__p]
      output port map, and an incremented index. *)
  
  Definition connect_to_confl_tci
             (i__p : inputmap)
             (o__p : outputmap)
             (idx : nat)
             (t : T sitpn) :
    CompileTimeState (inputmap * outputmap * nat) :=
    do id__t <- get_tci_id_from_binder t;
    do tci <- get_comp id__t;
    let '(id__e, g__t, i__t, o__t) := tci in
    (* Interconnects [o__p] to to [i__t], and [i__p] to [o__t]. *)
    do oi1 <- connect o__p i__t Place.output_arcs_valid idx Transition.input_arcs_valid;
    do oi2 <- connect (fst oi1) (snd oi1) Place.reinit_transitions_time idx Transition.reinit_time;
    do oi3 <- connect (fst oi2) (snd oi2) Place.priority_authorizations idx Transition.priority_authorizations;
    let '(o__p3, i__t3) := oi3 in
    (* Replaces TCI [id__t] by a new TCI in the compile-time state's behavior. *)
    do _ <- put_comp id__t id__e g__t i__t3 o__t;
    (* Last interconnection between [i__p] and [o__t]. *)
    do a <- actual Transition.fired o__t;
    match a with
    | None => Err ("connect_to_input_tci: The fired port of TCI " ++ $$id__t ++ " is open.")
    | Some n =>
        Ret (i__p ++ [associp_ (Place.output_transitions_fired $[[idx]]) (e_name n)], o__p3, (idx + 1)%nat)
    end.

  (** Parameters:

      Assume there is a place [p] such that:

      - [pinfo] represents the information associated with [p].

      - [i__p] and [o__p] represents the input and output port maps of a
        PCI [id__p], associated with [p] through the [γ] binder.

      - [t] is a non-conflicting output transition of [p].

      Retrieves the TCI [id__t] associated with transition [t], and
      connects elements of the input port map [i__p] and the output port
      map [o__p] to elements of the input and output port maps of the
      TCI [id__t].

      Replaces the TCI [id__t] by its modified version in the
      compile-time state behavior.
      
      Returns the modified [i__p] input port map, the modified [o__p]
      output port map, and an incremented index. *)
  
  Definition connect_to_nconfl_tci
             (i__p : inputmap)
             (o__p : outputmap)
             (idx : nat)
             (t : T sitpn) :
    CompileTimeState (inputmap * outputmap * nat) :=
    do id__t <- get_tci_id_from_binder t;
    do tci <- get_comp id__t;
    let '(id__e, g__t, i__t, o__t) := tci in
    (* Interconnects [o__p] to to [i__t], and [i__p] to [o__t]. *)
    do oi1 <- connect o__p i__t Place.output_arcs_valid idx Transition.input_arcs_valid;
    do oi2 <- connect (fst oi1) (snd oi1) Place.reinit_transitions_time idx Transition.reinit_time;

    (* Connects [pauths(idx)] to [true] in input port map [i__t2]. *)
    let '(o__p2, i__t2) := oi2 in
    do i__t3 <- cassoc_imap i__t2 Transition.priority_authorizations true;
         
    (* Interconnects [pauths(idx)] to a newly generated but
       unconnected internal signal [id__s] in output port map [o__p2]. *)
    do id__s <- get_nextid;
    do _ <- add_sig_decl (sdecl_ id__s tind_boolean);
    do o__p3 <- Ret (o__p2 ++ [assocop_idx Place.priority_authorizations idx ($id__s)]);

    (* Replaces TCI [id__t] by a new TCI in the compile-time state's behavior. *)
    do _ <- put_comp id__t id__e g__t i__t3 o__t;
    
    (* Last interconnection between [i__p] and [o__t]. *)
    do a <- actual Transition.fired o__t;
    match a with
    | None => Err ("connect_to_input_tci: The fired port of TCI " ++ $$id__t ++ " is open.")
    | Some n =>
        Ret (i__p ++ [associp_ (Place.output_transitions_fired $[[idx]]) (e_name n)], o__p3, (idx + 1)%nat)
    end.
  
  (** Iterates and calls the [connect_to_input_tci] function over the
      set of input transitions of a place [p]. *)
  
  Definition connect_to_output_tcis
             (pinfo : PlaceInfo sitpn)
             (i__p : inputmap) (o__p : outputmap) :
    CompileTimeState (inputmap * outputmap) :=
    do ioidx <- ListMonad.fold_left (fun '(i, o, idx) => connect_to_confl_tci i o idx) (tconflict pinfo) (i__p, o__p, 0%nat);
    let '(i__p1, o__p1, idx) := ioidx in
    do ioidx1 <- ListMonad.fold_left (fun '(i, o, idx) => connect_to_nconfl_tci i o idx) (toutputs pinfo) (i__p1, o__p1, idx);
    Ret (fst ioidx1).
  
  (** Retrieves the behavior [beh] (i.e. the currently generated
      behavior) the PCI [id__p] associated with place [p] (i.e. γ(p) =
      [id__p]), and connects the interface of the PCI [id__p] to the
      interface of its input and output TCIs. Then, replaces the old
      PCI [id__p] by the new in the compile-time state's behavior. *)
  
  Definition connect_place (p : P sitpn) :
    CompileTimeState unit :=

    (* Retrieves some elements from the compile-time state, namely:

       - The informations associated with place [p] in the
         [SitpnInfos] structure.
       - The identifier [id__p] associated with place [p] in the [γ] binder.
       - The PCI [id__p] from the behavior [beh]. *)
    do pinfo <- get_pinfo p;
    do id__p <- get_pci_id_from_binder p;
    do pci <- get_comp id__p;
    let '(id__e, g, i, o) := pci in
    
    (* Connects the PCI [pci] to the TCIs implementing the input
       transitions of place [p].  *)
    do i1 <- connect_to_input_tcis pinfo i;
    
    (* Connects the PCI [pci] to the TCIs implementing the output
       transitions of place [p]. *)
    do io2 <- connect_to_output_tcis pinfo i1 o;

    (* Replaces the PCI [pci] by a new PCI in the compile-time state's
       behavior. *)
    let '(i2, o2) := io2 in
    put_comp id__p id__e g i2 o2.

  (** Generates the interconnections between PCIs and TCIS by
      modifying the compile-time state's behavior. *)

  Definition generate_interconnections :
    CompileTimeState unit :=
    (* Calls connect_place on each place of sitpn. *)
    do Plist <- get_lofPs; ListMonad.iter connect_place Plist.
    
End GenInter.

Arguments generate_interconnections {sitpn}.
