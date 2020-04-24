(** Type representing informations about Sitpn components. *)

Require Import ArcT.
Require Import sets.Sitpn.
Require Import SitpnGlobalTypes.

(** Defines the type of PlaceInfo, gathering informations about a
    given place of an SITPN. *)

Inductive PlaceInfo (sitpn : Sitpn) : Type :=
  MkPlaceInfo { inTranss : list (T sitpn); outTranss : list ((T sitpn) * arc_t) }.

(** Defines the type of TransInfo, gathering informations about a
    given transition of an SITPN. *)

Inductive TransInfo (sitpn : Sitpn) : Type :=
  MkTransInfo { tItval : option TimeInterval; inPlaces : list (P sitpn); conds : list (C sitpn) }.
