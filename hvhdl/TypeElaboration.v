(** Defines the etype relation checks the well-formedness of a type
    indication τ, and transforms it into a semantical type *)

Require Import Environment.
Require Import SemanticalDomains.
Require Import AbstractSyntax.
Require Import ConstraintElaboration.

(** The type elaboration relation (general definition). *)

Inductive etype (Δ : ElDesign) : tind -> type -> Prop :=
| ETypeBool : etype Δ tind_boolean Tbool
| ETypeNat :
    forall {e e' n n'},
      econstr Δ e e' n n' ->
      etype Δ (tind_natural e e') (Tnat n n')
| ETypeArray :
    forall {tau t e e' n n'},
      etype Δ tau t ->
      econstr Δ e e' n n' ->
      etype Δ (tind_array tau e e') (Tarray t n n').

(** The type elaboration relation for generic constant type
    indication. *)

Inductive etypeg : tind -> type -> Prop :=
| ETypeGBool : etypeg tind_boolean Tbool
| ETypeGNat :
    forall {e e' n n'},
      econstrg e e' n n' ->
      etypeg (tind_natural e e') (Tnat n n').

(** Hints for etype and etypeg *)

#[export] Hint Constructors etype : hvhdl.
#[export] Hint Constructors etypeg : hvhdl.
