(** * Types and functions used by the generateInfo function. *)

Require Import Coqlib.
Require Import sets.Sitpn.
Require Import NatSet.
Require Import ListsPlus.
Require Import ListsDep.
Require Import InfosTypes.
Require Import GlobalTypes.

Module Type GenerateInfosFun.

  (** Functorial signature for functions that generate information
      about places of a Sitpn. *)
  
  Section GeneratePlaceInfos.
    
    Variable sitpn : Sitpn.

    (**  *)
    Parameter get_in_transs : P sitpn -> list (T sitpn) -> list (T sitpn).

    (**  *)
    Parameter get_out_transs : P sitpn -> list (T sitpn) -> list ((T sitpn) * ArcT).

    (**  *)
    Parameter get_p_info : P sitpn -> PlaceInfo sitpn.

    (**  *)
    Parameter get_p_infos : list (P sitpn) -> list (P sitpn * PlaceInfo sitpn).
    
  End GeneratePlaceInfos.

  (** Functorial signature for functions that generate information
      about transitions of a Sitpn. *)

  Section GenerateTransInfos.

    Variable sitpn : Sitpn.
    
    (**  *)
    Parameter get_in_places : T sitpn -> list (P sitpn) -> list (P sitpn).

    (**  *)
    Parameter get_conditions : T sitpn -> list (C sitpn) -> list (C sitpn).
    
    (**  *)
    Parameter get_t_info : T sitpn -> TransInfo sitpn.

    (**  *)
    Parameter get_t_infos : list (T sitpn) -> list (T sitpn * TransInfo sitpn).
    
  End GenerateTransInfos.
  
End GenerateInfosFun.
