(** * Types of Sitpn information structures. *)

Require Import sets.Sitpn.
Require Import SitpnTypes.
Require Import GlobalTypes.
Require Import NatSet.

Section SitpnInfoTypes.

  Variable sitpn : Sitpn.

  (** Defines the type of PlaceInfo, gathering informations about a
    given place of an SITPN. *)

  Inductive PlaceInfo : Type :=
    MkPlaceInfo { tinputs : list (T sitpn);
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
  
End SitpnInfoTypes.

Arguments tinputs {sitpn}.
Arguments toutputs {sitpn}.

Arguments pinputs {sitpn}.
Arguments conds {sitpn}.

