(** * Sitpn-to-HVhdhl Types.  *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.GlobalFacts.
Require Import common.ListDep.
Require Import common.StateAndErrorMonad.
Require Import common.ListPlus.
Require Import common.ListMonad.
Require Import String.
Require Import sitpn.Sitpn.
Require Import sitpn.SitpnFacts.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.

Import ErrMonadNotations.

(** ** Types used in the Sitpn2HVhdl transformation. *)

Section CompileTimeTypes.

  Variable sitpn : Sitpn.

  (** *** Information structure for a given [Sitpn] *)
  
  (** Defines the type of PlaceInfo, gathering informations about a
    given place of an SITPN. *)

  Inductive PlaceInfo : Type :=
    MkPlaceInfo { tinputs : list (T sitpn);
                  tconflict : list (T sitpn);
                  toutputs : list (T sitpn);
                  acts : list (A sitpn) }.
  
  (** Defines the type of TransInfo, gathering informations about a
    given transition of an SITPN. *)

  Inductive TransInfo : Type :=
    MkTransInfo { pinputs : list (P sitpn); conds : list (C sitpn) }.
  
  (** Defines the record type that stores information about an Sitpn. *)

  Inductive SitpnInfos : Type :=
    MkSitpnInfos {
        pinfos : list (P sitpn * PlaceInfo);
        tinfos : list (T sitpn * TransInfo);
        cinfos : list (C sitpn * list (T sitpn));
        ainfos : list (A sitpn * list (P sitpn));
        finfos : list (F sitpn * list (T sitpn));
      }.

  (** Empty [SitpnInfo] structure *)

  Definition EmptySitpnInfos := MkSitpnInfos [] [] [] [] [].
  
  (** *** Source to target binder *)

  (** Maps the elements of an SITPN to their signal or component
    identifiers on the VHDL side. *)

  Inductive Sitpn2HVhdlMap : Type :=
    MkS2HMap {
        p2pci : list (P sitpn * ident);
        t2tci : list (T sitpn * ident);
        a2out   : list (A sitpn * ident);
        f2out   : list (F sitpn * ident);
        c2in    : list (C sitpn * ident);
      }.
  
  (** Empty [Sitpn2HVhdlMap] structure *)

  Definition EmptyS2HMap := MkS2HMap [] [] [] [] [].
  
  (** *** Compile-time state *)

  Inductive Sitpn2HVhdlState : Type :=
    MkS2HState {

        (* Dependently-typed lists of places, transitions, conditions,
           actions and functions *)
        lofPs : list (P sitpn);
        lofTs : list (T sitpn);
        lofCs : list (C sitpn);
        lofAs : list (A sitpn);
        lofFs : list (F sitpn);

        (* Sitpn information structure *)
        sitpninfos : SitpnInfos;
        
        (* Next id *)
        nextid : ident;

        (* Port declaration list *)
        ports : list pdecl;

        (* Internal signal declaration list *)
        sigs : list sdecl;
        
        (* Architecture body in VHDL abstract syntax *)
        beh : cs;

        (* Source-to-target binder *)
        γ : Sitpn2HVhdlMap;

      }.

  (** Empty compile-time state

      Given a first fresh id [ffid], returns an empty compile-time
      state. *)
  
  Definition InitS2HState (ffid : ident) :=
    MkS2HState [] [] [] [] [] EmptySitpnInfos ffid [] [] cs_null EmptyS2HMap.
  
End CompileTimeTypes.

(* Set implicit arguments for SitpnInfos *)

Arguments tinfos {sitpn}.
Arguments pinfos {sitpn}.
Arguments cinfos {sitpn}.
Arguments ainfos {sitpn}.
Arguments finfos {sitpn}.

(* Set implicit arguments for Sitpn2HVhdlMap *)

Arguments p2pci {sitpn}.
Arguments t2tci {sitpn}.
Arguments a2out {sitpn}.
Arguments f2out {sitpn}.
Arguments c2in {sitpn}.

(* Set implicit arguments for compile-time state *)

Arguments lofPs {sitpn}.
Arguments lofTs {sitpn}.
Arguments lofCs {sitpn}.
Arguments lofAs {sitpn}.
Arguments lofFs {sitpn}.
Arguments nextid {sitpn}.
Arguments sitpninfos {sitpn}.
Arguments ports {sitpn}.
Arguments sigs {sitpn}.
Arguments beh {sitpn}.
Arguments γ {sitpn}.

(** ** Operations on Compile-time State *)

Section CompileTimeStateOpers.

  Variable sitpn : Sitpn.

  (** *** Operations for compile-time state *)

  Definition get_lofPs : @Mon (Sitpn2HVhdlState sitpn) (list (P sitpn)) :=
    do s <- Get; Ret (lofPs s).

  Definition set_lofPs (Plist : list (P sitpn)) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkS2HState sitpn Plist (lofTs s) (lofCs s) (lofAs s) (lofFs s) (sitpninfos s) (nextid s)
                    (ports s) (sigs s) (beh s) (γ s)).

  Definition get_lofTs : @Mon (Sitpn2HVhdlState sitpn) (list (T sitpn)) :=
    do s <- Get; Ret (lofTs s).

  Definition set_lofTs (Tlist : list (T sitpn)) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkS2HState sitpn (lofPs s) Tlist (lofCs s) (lofAs s) (lofFs s) (sitpninfos s) (nextid s)
                    (ports s) (sigs s) (beh s) (γ s)).

  Definition get_lofCs : @Mon (Sitpn2HVhdlState sitpn) (list (C sitpn)) :=
    do s <- Get; Ret (lofCs s).

  Definition set_lofCs (Clist : list (C sitpn)) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkS2HState sitpn (lofPs s) (lofTs s) Clist (lofAs s) (lofFs s) (sitpninfos s) (nextid s) 
                    (ports s) (sigs s) (beh s) (γ s)).

  Definition get_lofAs : @Mon (Sitpn2HVhdlState sitpn) (list (A sitpn)) :=
    do s <- Get; Ret (lofAs s).

  Definition set_lofAs (Alist : list (A sitpn)) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkS2HState sitpn (lofPs s) (lofTs s) (lofCs s) Alist (lofFs s) (sitpninfos s)
                    (nextid s) (ports s) (sigs s) (beh s) (γ s)).

  Definition get_lofFs : @Mon (Sitpn2HVhdlState sitpn) (list (F sitpn)) :=
    do s <- Get; Ret (lofFs s).

  Definition set_lofFs (Flist : list (F sitpn)) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkS2HState sitpn (lofPs s) (lofTs s) (lofCs s) (lofAs s) Flist (sitpninfos s)
                    (nextid s) (ports s) (sigs s) (beh s) (γ s)).
  
  Definition get_infos : @Mon (Sitpn2HVhdlState sitpn) (SitpnInfos sitpn) :=
    do s <- Get; Ret (sitpninfos s).

  Definition set_infos (infos : SitpnInfos sitpn) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkS2HState sitpn (lofPs s) (lofTs s) (lofCs s) (lofAs s) (lofFs s) infos 
                    (nextid s) (ports s) (sigs s) (beh s) (γ s)).

  Definition get_beh : @Mon (Sitpn2HVhdlState sitpn) cs :=
    do s <- Get; Ret (beh s).

  Definition set_beh (beh : cs) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkS2HState sitpn (lofPs s) (lofTs s) (lofCs s) (lofAs s) (lofFs s) (sitpninfos s)
                    (nextid s) (ports s) (sigs s) beh (γ s)).
  
  Definition get_binder : @Mon (Sitpn2HVhdlState sitpn) (Sitpn2HVhdlMap sitpn) :=
    do s <- Get; Ret (γ s).

  Definition set_binder (γ : Sitpn2HVhdlMap sitpn) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkS2HState sitpn (lofPs s) (lofTs s) (lofCs s) (lofAs s) (lofFs s) (sitpninfos s)
                    (nextid s) (ports s) (sigs s) (beh s) γ).
  
  (* Returns the next available identifier, and increments the
     [nextid] value in the compile-time state. *)

  Definition get_nextid : @Mon (Sitpn2HVhdlState sitpn) ident :=
    do s <- Get;
    do _  <- Put (MkS2HState sitpn (lofPs s) (lofTs s) (lofCs s) (lofAs s) (lofFs s) (sitpninfos s) 
                             (S (nextid s)) (ports s) (sigs s) (beh s) (γ s));
    Ret (nextid s).

  (** *** Operations for the list of port declarations and internal signal declarations *)

  Definition add_port_decl (pd : pdecl) :=
    do s <- Get;
    Put (MkS2HState sitpn (lofPs s) (lofTs s) (lofCs s) (lofAs s) (lofFs s) (sitpninfos s) 
                    (nextid s) ((ports s) ++ [pd]) (sigs s) (beh s) (γ s)).

  Definition add_sig_decl (sd : sdecl) :
    @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkS2HState sitpn (lofPs s) (lofTs s) (lofCs s) (lofAs s) (lofFs s) (sitpninfos s) 
                    (nextid s) (ports s) ((sigs s) ++ [sd]) (beh s) (γ s)).
  
  (** *** Operations for SITPN-to-H-VHDL map *)

  Definition bind_action (a : A sitpn) (id : ident) :=
    do γ <- get_binder;
    (* Sets the couple [(a, id)] in the [a2out] field of [γ]. *)
    let a2out' := setv Aeqdec a id (a2out γ) in
    (* Updates the new archictecture. *)
    set_binder (MkS2HMap sitpn (p2pci γ) (t2tci γ) a2out' (f2out γ) (c2in γ)).

  Definition bind_function (f : F sitpn) (id : ident) :=
    do γ <- get_binder;
    (* Sets the couple [(f, id)] in the [f2out] field of [γ]. *)
    let f2out' := setv Feqdec f id (f2out γ) in
    (* Updates the new archictecture. *)
    set_binder (MkS2HMap sitpn (p2pci γ) (t2tci γ) (a2out γ) f2out' (c2in γ)).

  Definition bind_condition (c : C sitpn) (id : ident) :=
    do γ <- get_binder;
    (* Sets the couple [(c, id)] in the [c2in] field of [γ]. *)
    let c2in' := setv Ceqdec c id (c2in γ) in
    (* Updates the new archictecture. *)
    set_binder (MkS2HMap sitpn (p2pci γ) (t2tci γ) (a2out γ) (f2out γ) c2in').

  Definition bind_place (p : P sitpn) (id : ident) :=
    do γ <- get_binder;
    (* Sets the couple [(p, id)] in the [p2pci] field of [γ]. *)
    let p2pci' := setv Peqdec p id (p2pci γ) in
    (* Updates the new archictecture. *)
    set_binder (MkS2HMap sitpn p2pci' (t2tci γ) (a2out γ) (f2out γ) (c2in γ)).

  Definition bind_transition (t : T sitpn) (id : ident) :=
    do γ <- get_binder;
    (* Sets the couple [(t, id)] in the [t2tci] field of [γ]. *)
    let t2tci' := setv Teqdec t id (t2tci γ) in
    (* Updates the new architecture. *)
    set_binder (MkS2HMap sitpn (p2pci γ) t2tci' (a2out γ) (f2out γ) (c2in γ)).

  Definition get_pci_id_from_binder (p : P sitpn) :=
    do γ <- get_binder; getv Peqdec p (p2pci γ).

  Definition get_tci_id_from_binder (t : T sitpn) :=
    do γ <- get_binder; getv Teqdec t (t2tci γ).
  
  (** *** Operations for beh *)

  Definition add_cs (cstmt : cs) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkS2HState sitpn (lofPs s) (lofTs s) (lofCs s) (lofAs s) (lofFs s) (sitpninfos s)
                    (nextid s) (ports s) (sigs s) (cs_par cstmt (beh s)) (γ s)).
  
  (** *** Getters for SitpnInfos structure *)

  Definition get_tinfo (t : T sitpn) : @Mon (Sitpn2HVhdlState sitpn) (TransInfo sitpn) :=
    do sitpninfos <- get_infos; getv Teqdec t (tinfos sitpninfos).
  
  Definition get_pinfo (p : P sitpn) : @Mon (Sitpn2HVhdlState sitpn) (PlaceInfo sitpn) :=
    do sitpninfos <- get_infos; getv Peqdec p (pinfos sitpninfos).

  Definition get_ainfo (a : A sitpn) : @Mon (Sitpn2HVhdlState sitpn) (list (P sitpn)) :=
    do sitpninfos <- get_infos; getv Aeqdec a (ainfos sitpninfos).

  Definition get_finfo (f : F sitpn) : @Mon (Sitpn2HVhdlState sitpn) (list (T sitpn)) :=
    do sitpninfos <- get_infos; getv Feqdec f (finfos sitpninfos).
  
  Definition get_cinfo (c : C sitpn) : @Mon (Sitpn2HVhdlState sitpn) (list (T sitpn)) :=
    do sitpninfos <- get_infos; getv Ceqdec c (cinfos sitpninfos).
  
  (** *** Setters *)

  (* Adds a new place info entry to the pinfos list *)

  Definition set_pinfo (ppinfo : (P sitpn * PlaceInfo sitpn)) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do sitpninfo <- get_infos;
    set_infos (MkSitpnInfos sitpn
                           (ppinfo :: (pinfos sitpninfo))
                           (tinfos sitpninfo)
                           (cinfos sitpninfo)
                           (ainfos sitpninfo)
                           (finfos sitpninfo)).

  (* Adds a new transition info entry to the tinfos list *)

  Definition set_tinfo (ttinfo : (T sitpn * TransInfo sitpn)) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do sitpninfos <- get_infos;
    set_infos (MkSitpnInfos sitpn
                           (pinfos sitpninfos)
                           (ttinfo :: (tinfos sitpninfos))
                           (cinfos sitpninfos)
                           (ainfos sitpninfos)
                           (finfos sitpninfos)).

  (* Adds a new condition info entry to the cinfos list *)

  Definition set_cinfo (cinfo : (C sitpn * list (T sitpn))) :
    @Mon (Sitpn2HVhdlState sitpn) unit :=
    do sitpninfos <- get_infos;
    set_infos (MkSitpnInfos sitpn
                           (pinfos sitpninfos)
                           (tinfos sitpninfos)
                           (cinfo :: cinfos sitpninfos)
                           (ainfos sitpninfos)
                           (finfos sitpninfos)).

  (* Adds a new action info entry to the ainfos list *)

  Definition set_ainfo (ainfo : (A sitpn * list (P sitpn))) :
    @Mon (Sitpn2HVhdlState sitpn) unit :=
    do sitpninfos <- get_infos;
    set_infos (MkSitpnInfos sitpn
                           (pinfos sitpninfos)
                           (tinfos sitpninfos)
                           (cinfos sitpninfos)
                           (ainfo :: ainfos sitpninfos)
                           (finfos sitpninfos)).
  
  (* Adds a new function info entry to the finfos list *)

  Definition set_finfo (finfo : (F sitpn * list (T sitpn))) :
    @Mon (Sitpn2HVhdlState sitpn) unit :=
    do sitpninfos <- get_infos;
    set_infos (MkSitpnInfos sitpn
                           (pinfos sitpninfos)
                           (tinfos sitpninfos)
                           (cinfos sitpninfos)
                           (ainfos sitpninfos)
                           (finfo :: finfos sitpninfos)).
  
End CompileTimeStateOpers.

(** Set implicit arguments for PlaceInfo fields. *)

Arguments tinputs {sitpn}.
Arguments tconflict {sitpn}.
Arguments toutputs {sitpn}.
Arguments acts {sitpn}.

(** Set implicit arguments for TransInfo fields. *)

Arguments pinputs {sitpn}.
Arguments conds {sitpn}.

(** Set implicit arguments for SitpnInfos fields. *)

Arguments cinfos {sitpn}.

(* Set implicit arguments for Sitpn2HVhdlState monadic functions. *)

Arguments get_lofPs {sitpn}.
Arguments set_lofPs {sitpn}.
Arguments get_lofTs {sitpn}.
Arguments set_lofTs {sitpn}.
Arguments get_lofAs {sitpn}.
Arguments set_lofAs {sitpn}.
Arguments get_lofCs {sitpn}.
Arguments set_lofCs {sitpn}.
Arguments get_lofFs {sitpn}.
Arguments set_lofFs {sitpn}.
Arguments get_infos {sitpn}.
Arguments set_infos {sitpn}.
Arguments get_beh {sitpn}.
Arguments set_beh {sitpn}.
Arguments get_nextid {sitpn}.

(** Set implicit arguments for SitpnInfos monadic functions. *)

Arguments get_tinfo {sitpn}.
Arguments get_pinfo {sitpn}.
Arguments get_cinfo {sitpn}.
Arguments get_ainfo {sitpn}.
Arguments get_finfo {sitpn}.
Arguments set_pinfo {sitpn}.
Arguments set_tinfo {sitpn}.
Arguments set_ainfo {sitpn}.
Arguments set_cinfo {sitpn}.
Arguments set_finfo {sitpn}.

(* Set implicit arguments for SITPN-to-H-VHDL map monadic functions. *)

Arguments bind_action {sitpn}.
Arguments bind_function {sitpn}.
Arguments bind_condition {sitpn}.
Arguments bind_place {sitpn}.
Arguments bind_transition {sitpn}.
Arguments get_pci_id_from_binder {sitpn}.
Arguments get_tci_id_from_binder {sitpn}.

(* Set implicit arguments for list of ports/sigs monadic functions. *)

Arguments add_port_decl {sitpn}.
Arguments add_sig_decl {sitpn}.

(* Set implicit arguments for behavior monadic functions. *)

Arguments add_cs {sitpn}.
