(** * Sitpn2HVhdhl intermediary types.  *)

Require Import Coqlib.
Require Import String.
Require Import HVhdlTypes.
Require Import AbstractSyntax.
Require Import dp.Sitpn.
Require Import dp.InfosTypes.
Require Import StateAndErrorMonad.


(** ** Types used in the Sitpn2HVhdl transformation. *)

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

Definition PlaceMap sitpn := list (P sitpn * HComponent).

(** Mapping structure between elements of T and their (intermediary)
    representation as H-VHDL components. *)

Definition TransMap sitpn := list (T sitpn * HComponent).

(** Mapping structure between elements of A and the list of expressions
    that will composed their activation expression.
 *)

Definition ActionMap sitpn := list (A sitpn * list expr).

(** Mapping structure between elements of F and the list of
    expressions that will composed their execution expression.  *)

Definition FunMap sitpn := list (F sitpn * list expr).

(** Intermediary representation of an H-VHDL architecture as a triplet
    of list of declarations (list adecl), a mapping from P to
    HComponent and a mapping from T to HComponent.  *)

Definition Architecture sitpn := (list adecl * PlaceMap sitpn * TransMap sitpn * FunMap sitpn * ActionMap sitpn)%type.

(** **  Source to target binder *)

(** Maps the elements of an SITPN to their signal or component
    identifiers on the VHDL side. *)

Record Sitpn2HVhdlMap sitpn : Type :=
  BuildMap {
      p2pcomp : list (P sitpn * ident);
      t2tcomp : list (T sitpn * ident);
      a2out   : list (A sitpn * ident);
      f2out   : list (F sitpn * ident);
      c2in    : list (C sitpn * ident);
    }.

(** ** Compile-time state *)

Inductive Sitpn2HVhdlState sitpn : Type :=
  MkState {

      (* Next id *)
      nextid : ident;

      (* Sitpn information structure *)

      sitpninfos : SitpnInfo sitpn;
      
      (* Architecture in intermediary format *)
      arch : Architecture sitpn;

      (* Source-to-target binder *)
      γ : Sitpn2HVhdlMap sitpn;

      (* Architecture body in VHDL abstract syntax *)
      behavior : cs;
    }.

(** *** Operations on Compile-time State *)


