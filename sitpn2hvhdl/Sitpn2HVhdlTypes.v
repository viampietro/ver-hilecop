(** * Sitpn2HVhdhl intermediary types.  *)

Require Import common.Coqlib.
Require Import common.GlobalTypes.
Require Import common.GlobalFacts.
Require Import common.ListsDep.
Require Import String.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.
Require Import dp.Sitpn.
Require Import StateAndErrorMonad.

Import ErrMonadNotations.

(** ** Types used in the Sitpn2HVhdl transformation. *)

Section CompileTimeTypes.

  Variable sitpn : Sitpn.
  
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

  Inductive SitpnInfo : Type :=
    MkSitpnInfo {
        pinfos : list (P sitpn * PlaceInfo);
        tinfos : list (T sitpn * TransInfo);
        cinfos : list (C sitpn * list (T sitpn));
        ainfos : list (A sitpn * list (P sitpn));
        finfos : list (F sitpn * list (T sitpn));
      }.

  (** Aliases to types, used as intermediary data representation between
    Sitpn and H-VHDL abstract syntax.  *)

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

  Definition Architecture := (list adecl * PlaceMap * TransMap * FunMap * ActionMap)%type.

  (** **  Source to target binder *)

  (** Maps the elements of an SITPN to their signal or component
    identifiers on the VHDL side. *)

  Record Sitpn2HVhdlMap : Type :=
    BuildMap {
        p2pcomp : list (P sitpn * ident);
        t2tcomp : list (T sitpn * ident);
        a2out   : list (A sitpn * ident);
        f2out   : list (F sitpn * ident);
        c2in    : list (C sitpn * ident);
      }.

  (** ** Compile-time state *)

  Inductive Sitpn2HVhdlState : Type :=
    MkState {

        (* Next id *)
        nextid : ident;

        (* Sitpn information structure *)
        sitpninfos : SitpnInfo;
        
        (* Architecture in intermediary format *)
        arch : Architecture;

        (* Source-to-target binder *)
        γ : Sitpn2HVhdlMap;

        (* Architecture body in VHDL abstract syntax *)
        behavior : cs;
      }.

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

  Definition get_infos : @Mon (Sitpn2HVhdlState sitpn) (SitpnInfo sitpn) :=
    do s <- Get; Ret (sitpninfos s).

  Definition set_infos (infos : SitpnInfo sitpn) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do s <- Get;
    Put (MkState sitpn (nextid s) infos (arch s) (γ s) (behavior s)).
  
  (** *** Getters for SitpnInfo structure *)

  Definition get_tinfo (t : T sitpn) : @Mon (Sitpn2HVhdlState sitpn) (TransInfo sitpn) :=
    let check_t_in_tinfos :=
        (fun params => let '(t', _) := params in
                       if seqdec Nat.eq_dec t t' then Ret true else Ret false) in
    do sitpninfos <- get_infos;
    do opt_ttinfo <- find check_t_in_tinfos (tinfos sitpninfos);
    match opt_ttinfo with
    | None => Err ("get_tinfo: transition "
                     ++ $$t ++ " is not referenced in the SITPN information structure.")
    | Some ttinfo => Ret (snd ttinfo)
    end.

  (** *** Setters *)

  (* Adds a new place info entry to the pinfos list *)

  Definition set_pinfo (ppinfo : (P sitpn * PlaceInfo sitpn)) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do sitpninfo <- get_infos;
    set_infos (MkSitpnInfo sitpn
                           (ppinfo :: (pinfos sitpninfo))
                           (tinfos sitpninfo)
                           (cinfos sitpninfo)
                           (ainfos sitpninfo)
                           (finfos sitpninfo)).

  (* Adds a new transition info entry to the tinfos list *)

  Definition set_tinfo (ttinfo : (T sitpn * TransInfo sitpn)) : @Mon (Sitpn2HVhdlState sitpn) unit :=
    do sitpninfos <- get_infos;
    set_infos (MkSitpnInfo sitpn
                           (pinfos sitpninfos)
                           (ttinfo :: (tinfos sitpninfos))
                           (cinfos sitpninfos)
                           (ainfos sitpninfos)
                           (finfos sitpninfos)).

  (* Adds a new condition info entry to the cinfos list *)

  Definition set_cinfo (cinfo : (C sitpn * list (T sitpn))) :
    @Mon (Sitpn2HVhdlState sitpn) unit :=
    do sitpninfos <- get_infos;
    set_infos (MkSitpnInfo sitpn
                           (pinfos sitpninfos)
                           (tinfos sitpninfos)
                           (cinfo :: cinfos sitpninfos)
                           (ainfos sitpninfos)
                           (finfos sitpninfos)).

  (* Adds a new action info entry to the ainfos list *)

  Definition set_ainfo (ainfo : (A sitpn * list (P sitpn))) :
    @Mon (Sitpn2HVhdlState sitpn) unit :=
    do sitpninfos <- get_infos;
    set_infos (MkSitpnInfo sitpn
                           (pinfos sitpninfos)
                           (tinfos sitpninfos)
                           (cinfos sitpninfos)
                           (ainfo :: ainfos sitpninfos)
                           (finfos sitpninfos)).
  
  (* Adds a new function info entry to the finfos list *)

  Definition set_finfo (finfo : (F sitpn * list (T sitpn))) :
    @Mon (Sitpn2HVhdlState sitpn) unit :=
    do sitpninfos <- get_infos;
    set_infos (MkSitpnInfo sitpn
                           (pinfos sitpninfos)
                           (tinfos sitpninfos)
                           (cinfos sitpninfos)
                           (ainfos sitpninfos)
                           (finfo :: finfos sitpninfos)).
  
End CompileTimeStateOpers.

Arguments set_pinfo {sitpn}.
Arguments set_tinfo {sitpn}.
Arguments set_ainfo {sitpn}.
Arguments set_cinfo {sitpn}.
Arguments set_finfo {sitpn}.

(** Set implicit arguments for PlaceInfo fields. *)

Arguments tinputs {sitpn}.
Arguments toutputs {sitpn}.

(** Set implicit arguments for TransInfo fields. *)

Arguments pinputs {sitpn}.
Arguments conds {sitpn}.

(** Set implicit arguments for SitpnInfo fields. *)

Arguments cinfos {sitpn}.
