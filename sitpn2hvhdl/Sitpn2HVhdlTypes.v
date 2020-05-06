(** * Types used in the Sitpn2HVhdl transformation.  *)

Require Import HVhdlTypes.
Require Import AbstractSyntax.
Require Import sets.Sitpn.

Definition InputMap := list (ident * (expr + list expr)).
Definition OutputMap := list (ident * (name + list name)).
Definition PlaceMap sitpn := list (P sitpn * (genmap * InputMap * OutputMap)).
Definition TransMap sitpn := list (T sitpn * (genmap * InputMap * OutputMap)).
Definition Architecture sitpn := (list adecl * PlaceMap sitpn * TransMap sitpn)%type.
