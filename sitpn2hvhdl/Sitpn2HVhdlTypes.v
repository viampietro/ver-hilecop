(** * Sitpn-to-HVhdhl Types.  *)

Require Import common.Coqlib.
Require Import common.GlobalTypes.
Require Import common.GlobalFacts.
Require Import common.ListsDep.
Require Import common.StateAndErrorMonad.
Require Import common.ListsPlus.
Require Import common.ListsMonad.
Require Import String.
Require Import dp.Sitpn.
Require Import dp.SitpnFacts.
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
                  toutputs : list (T sitpn) }.
  
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

  (** *** Intermediary representation of an H-VHDL architecture *)
  
  (** Intermediary representation of a H-VHDL component input port
      map. *)

  Definition InputMap := list (ident * (expr + list expr)).

  (** Intermediary representation of a H-VHDL component output port
    map. *)

  Definition OutputMap := list (ident * ((option name) + list name)).

  (** Intermediary representation of a H-VHDL component. *)

  Definition HComponent := (genmap * InputMap * OutputMap)%type.

  (** Mapping structure between elements of P and their (intermediary)
    representation as H-VHDL components. *)

  Definition PlaceMap := list (P sitpn * HComponent).

  (** Mapping structure between elements of T and their (intermediary)
    representation as H-VHDL components. *)

  Definition TransMap := list (T sitpn * HComponent).

  (** Mapping structure between elements of A and the list of expressions
    that will composed their activation expression.
   *)

  Definition ActionMap := list (A sitpn * list expr).

  (** Mapping structure between elements of F and the list of
    expressions that will composed their execution expression.  *)

  Definition FunMap := list (F sitpn * list expr).

  (** Intermediary representation of an H-VHDL architecture as a triplet
    of list of declarations (list adecl), a mapping from P to
    HComponent and a mapping from T to HComponent.  *)

  Definition Architecture := (list sdecl * PlaceMap * TransMap * FunMap * ActionMap)%type.

  (** Empty architecture structure *)

  Definition EmptyArch : Architecture := ([], [], [], [], []).
  
  (** *** Source to target binder *)

  (** Maps the elements of an SITPN to their signal or component
    identifiers on the VHDL side. *)

  Inductive Sitpn2HVhdlMap : Type :=
    MkS2HMap {
        p2pcomp : list (P sitpn * ident);
        t2tcomp : list (T sitpn * ident);
        a2out   : list (A sitpn * ident);
        f2out   : list (F sitpn * ident);
        c2in    : list (C sitpn * ident);
      }.
  
  (** Empty [Sitpn2HVhdlMap] structure *)

  Definition EmptyS2HMap := MkS2HMap [] [] [] [] [].
  
  (** *** Compile-time state *)

  Inductive Sitpn2HVhdlState : Type :=
    MkS2HState {

        (* Next id *)
        nextid : ident;

        (* Sitpn information structure *)
        sitpninfos : SitpnInfos;
        
        (* Architecture in intermediary format *)
        arch : Architecture;

        (* Source-to-target binder *)
        γ : Sitpn2HVhdlMap;

        (* Architecture body in VHDL abstract syntax *)
        behavior : cs;
      }.

  (** Empty compile-time state

      Given a first fresh id [ffid], returns an empty compile-time
      state. *)
  
  Definition InitS2HState (ffid : ident) :=
    MkS2HState ffid EmptySitpnInfos EmptyArch EmptyS2HMap cs_null.

End CompileTimeTypes.

(* Set implicit arguments for SitpnInfos *)

Arguments tinfos {sitpn}.
Arguments pinfos {sitpn}.
Arguments cinfos {sitpn}.
Arguments ainfos {sitpn}.
Arguments finfos {sitpn}.

(* Set implicit arguments for compile-time state *)

Arguments nextid {sitpn}.
Arguments sitpninfos {sitpn}.
Arguments γ {sitpn}.
Arguments arch {sitpn}.
Arguments behavior {sitpn}.

(** ** Operations on Compile-time State *)

Section CompileTimeStateOpers.

  Variable sitpn : Sitpn.

  (** *** Compile-time state getters *)

  Definition get_infos : @Mon (Sitpn2HVhdlState sitpn) (SitpnInfos sitpn) :=
    do s <- Get; Ret (sitpninfos s).

  Definition set_infos (infos : SitpnInfos sitpn) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkS2HState sitpn (nextid s) infos (arch s) (γ s) (behavior s)).

  Definition get_arch : @Mon (Sitpn2HVhdlState sitpn) (Architecture sitpn) :=
    do s <- Get; Ret (arch s).

  Definition set_arch (arch : Architecture sitpn) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkS2HState sitpn (nextid s) (sitpninfos s) arch (γ s) (behavior s)).

  (* Returns the next available identifier, and increments the
     [nextid] value in the compile-time state. *)

  Definition get_nextid : @Mon (Sitpn2HVhdlState sitpn) ident :=
    do s <- Get;
    do _ <- Put (MkS2HState sitpn (S (nextid s)) (sitpninfos s) (arch s) (γ s) (behavior s));
    Ret (nextid s).
  
  (** *** Getters for Architecture structure *)

  Definition get_tcomp (t : T sitpn) : @Mon (Sitpn2HVhdlState sitpn) HComponent := 

    (* Retrieves the architecture from the compile-time state. *)
    do arch <- get_arch;
    
    (* Destructs the architecture. *)
    let '(sigs, plmap, trmap, fmap, amap) := arch in
    let check_t_in_trmap :=
        (fun params => let '(t', _) := params in
                       if seqdec Nat.eq_dec t t' then Ret true else Ret false) in
    do opt_ttcomp <- ListsMonad.find check_t_in_trmap trmap;
    match opt_ttcomp with
    | None => Err ("get_tcomp: transition "
                     ++ $$t ++ " is not referenced in the Architecture structure.")
    | Some ttcomp => Ret (snd ttcomp)
    end.
  
  Definition set_tcomp (t : T sitpn) (tcomp : HComponent) :
    @Mon (Sitpn2HVhdlState sitpn) unit :=
    do arch <- get_arch;
    (* Destructs the architecture. *)
    let '(sigs, plmap, trmap, fmap, amap) := arch in
    (* Sets the couple [(t, tcomp)] in [trmap]. *)
    let trmap' := setv Teqdec t tcomp trmap in
    (* Updates the new archictecture. *)
    set_arch (sigs, plmap, trmap', fmap, amap).

  Definition get_pcomp (p : P sitpn) : @Mon (Sitpn2HVhdlState sitpn) HComponent := 

    (* Retrieves the architecture from the compile-time state. *)
    do arch <- get_arch;
    
    (* Destructs the architecture. *)
    let '(sigs, plmap, trmap, fmap, amap) := arch in
    let check_p_in_plmap :=
        (fun params => let '(p', _) := params in
                       if seqdec Nat.eq_dec p p' then Ret true else Ret false) in
    do opt_ppcomp <- ListsMonad.find check_p_in_plmap plmap;
    match opt_ppcomp with
    | None => Err ("get_pcomp: place "
                     ++ $$p ++ " is not referenced in the Architecture structure.")
    | Some ppcomp => Ret (snd ppcomp)
    end.

  Definition set_pcomp (p : P sitpn) (pcomp : HComponent) :
    @Mon (Sitpn2HVhdlState sitpn) unit :=
    do arch <- get_arch;
    (* Destructs the architecture. *)
    let '(sigs, plmap, trmap, fmap, amap) := arch in
    (* Sets the couple [(p, pcomp)] in [plmap]. *)
    let plmap' := setv Peqdec p pcomp plmap in
    (* Updates the new archictecture. *)
    set_arch (sigs, plmap', trmap, fmap, amap).
  
  Definition add_sig_decl (sd : sdecl) :
    @Mon (Sitpn2HVhdlState sitpn) unit :=
    do arch <- get_arch;
    let '(sigs, plmap, trmap, fmap, amap) := arch in
    set_arch (sigs ++ [sd], plmap, trmap, fmap, amap).
  
  (** *** Getters for SitpnInfos structure *)

  Definition get_tinfo (t : T sitpn) : @Mon (Sitpn2HVhdlState sitpn) (TransInfo sitpn) :=
    let check_t_in_tinfos :=
        (fun params => let '(t', _) := params in
                       if seqdec Nat.eq_dec t t' then Ret true else Ret false) in
    do sitpninfos <- get_infos;
    do opt_ttinfo <- ListsMonad.find check_t_in_tinfos (tinfos sitpninfos);
    match opt_ttinfo with
    | None => Err ("get_tinfo: transition "
                     ++ $$t ++ " is not referenced in the SITPN information structure.")
    | Some ttinfo => Ret (snd ttinfo)
    end.

  Definition get_pinfo (p : P sitpn) : @Mon (Sitpn2HVhdlState sitpn) (PlaceInfo sitpn) :=
    let check_p_in_pinfos :=
        (fun params => let '(p', _) := params in
                       if seqdec Nat.eq_dec p p' then Ret true else Ret false) in
    do sitpninfos <- get_infos;
    do opt_ppinfo <- ListsMonad.find check_p_in_pinfos (pinfos sitpninfos);
    match opt_ppinfo with
    | None => Err ("get_pinfo: place "
                     ++ $$p ++ " is not referenced in the SITPN information structure.")
    | Some ppinfo => Ret (snd ppinfo)
    end.

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

(** Set implicit arguments for TransInfo fields. *)

Arguments pinputs {sitpn}.
Arguments conds {sitpn}.

(** Set implicit arguments for SitpnInfos fields. *)

Arguments cinfos {sitpn}.

(* Set implicit arguments for Sitpn2HVhdlState monadic functions. *)

Arguments get_arch {sitpn}.
Arguments set_arch {sitpn}.
Arguments get_infos {sitpn}.
Arguments set_infos {sitpn}.
Arguments get_nextid {sitpn}.

(** Set implicit arguments for SitpnInfos monadic functions. *)

Arguments get_tinfo {sitpn}.
Arguments get_pinfo {sitpn}.
Arguments set_pinfo {sitpn}.
Arguments set_tinfo {sitpn}.
Arguments set_ainfo {sitpn}.
Arguments set_cinfo {sitpn}.
Arguments set_finfo {sitpn}.

(* Set implicit arguments for Architecture monadic functions. *)

Arguments get_pcomp {sitpn}.
Arguments set_pcomp {sitpn}.
Arguments get_tcomp {sitpn}.
Arguments set_tcomp {sitpn}.
Arguments add_sig_decl {sitpn}.


