(** Type representing informations about Sitpn components. *)

Require Import sets.Sitpn.
Require Import SitpnTypes.
Require Import GlobalTypes.
Require Import NatSet.

(** Defines the type of PlaceInfo, gathering informations about a
    given place of an SITPN. *)

Inductive PlaceInfo (sitpn : Sitpn) : Type :=
  MkPlaceInfo { tinputs : list (T sitpn);
                toutputs : list (T sitpn * ArcT) }.

(** Defines the type of TransInfo, gathering informations about a
    given transition of an SITPN. *)

Inductive TransInfo (sitpn : Sitpn) : Type :=
  MkTransInfo { pinputs : list (P sitpn); conds : list (C sitpn) }.

(** Defines the record type that stores information about an Sitpn. *)

Inductive SitpnInfo (sitpn : Sitpn) : Type :=
  MkSitpnInfo {
      pinfos : list (P sitpn * PlaceInfo sitpn);
      tinfos : list (T sitpn * TransInfo sitpn);
      cinfos : list (C sitpn * list (T sitpn));
      ainfos : list (A sitpn * list (P sitpn));
      finfos : list (F sitpn * list (T sitpn));
    }.
