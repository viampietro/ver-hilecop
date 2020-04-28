(** Type representing informations about Sitpn components. *)

Require Import sets.Sitpn.
Require Import SitpnTypes.
Require Import GlobalTypes.
Require Import NatSet.

(** Defines the type of PlaceInfo, gathering informations about a
    given place of an SITPN. *)

Inductive PlaceInfo (sitpn : Sitpn) : Type :=
  MkPlaceInfo { inTranss : list (T sitpn);
                outTranss : list ((T sitpn) * ArcT) }.

(** Defines the type of TransInfo, gathering informations about a
    given transition of an SITPN. *)

Inductive TransInfo (sitpn : Sitpn) : Type :=
  MkTransInfo { tItval : option StaticTimeInterval; inPlaces : list (P sitpn); conds : list (C sitpn) }.
