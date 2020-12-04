(** * Types of Sitpn information structures. *)

Require Import common.Coqlib.
Require Import common.ListsPlus.
Require Import common.GlobalFacts.
Require Import dp.Sitpn.
Require Import SitpnTypes.
Require Import GlobalTypes.
Require Import NatSet.

Section SitpnInfoTypes.

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

  (** ** Getters *)
  
  Definition get_tinfo (t : T sitpn) (sitpninfo : SitpnInfo) : option TransInfo :=
    let check_t_in_tinfos := (fun params => let '(t', _) := params in
                                            if seqdec Nat.eq_dec t t' then true else false) in
    match find check_t_in_tinfos (tinfos sitpninfo) with
    | Some (_, tinfo) => Some tinfo
    | None => None
    end.
  
  (** ** Setters *)
  
  (* Adds a new place info entry to the pinfos list *)
  
  Definition set_pinfo (pinfo : (P sitpn * PlaceInfo)) (sitpninfo : SitpnInfo) : SitpnInfo :=
    MkSitpnInfo (pinfo :: (pinfos sitpninfo))
                (tinfos sitpninfo)
                (cinfos sitpninfo)
                (ainfos sitpninfo)
                (finfos sitpninfo).
  
  (* Adds a new transition info entry to the tinfos list *)
  
  Definition set_tinfo (tinfo : (T sitpn * TransInfo)) : @Mon SitpnInfo unit :=
    do sitpninfo <- Get;
    Put (MkSitpnInfo (pinfos sitpninfo)
                     (tinfo :: (tinfos sitpninfo))
                     (cinfos sitpninfo)
                     (ainfos sitpninfo)
                     (finfos sitpninfo)).

  (* Adds a new condition info entry to the cinfos list *)
  
  Definition set_cinfo (cinfo : (C sitpn * list (T sitpn))) (sitpninfo : SitpnInfo) : SitpnInfo :=
    MkSitpnInfo (pinfos sitpninfo)
                (tinfos sitpninfo)
                (cinfo :: cinfos sitpninfo)
                (ainfos sitpninfo)
                (finfos sitpninfo).

  (* Adds a new action info entry to the ainfos list *)
  
  Definition set_ainfo (ainfo : (A sitpn * list (P sitpn))) (sitpninfo : SitpnInfo) : SitpnInfo :=
    MkSitpnInfo (pinfos sitpninfo)
                (tinfos sitpninfo)
                (cinfos sitpninfo)
                (ainfo :: ainfos sitpninfo)
                (finfos sitpninfo).

  (* Adds a new function info entry to the finfos list *)
  
  Definition set_finfo (finfo : (F sitpn * list (T sitpn))) (sitpninfo : SitpnInfo) : SitpnInfo :=
    MkSitpnInfo (pinfos sitpninfo)
                (tinfos sitpninfo)
                (cinfos sitpninfo)
                (ainfos sitpninfo)
                (finfo :: finfos sitpninfo).
  
End SitpnInfoTypes.

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
