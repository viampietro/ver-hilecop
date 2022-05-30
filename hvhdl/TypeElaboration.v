(** Defines the EType relation checks the well-formedness of a type
    indication τ, and transforms it into a semantical type *)

Require Import Environment.
Require Import SemanticalDomains.
Require Import AbstractSyntax.
Require Import ConstraintElaboration.

(** The type elaboration relation (general definition). *)

Inductive EType (Δ : ElDesign) : tind -> type -> Prop :=
| ETypeBool : EType Δ tind_boolean Tbool
| ETypeNat :
    forall {e e' n n'},
      EConstr Δ e e' n n' ->
      EType Δ (tind_natural e e') (Tnat n n')
| ETypeArray :
    forall {tau t e e' n n'},
      EType Δ tau t ->
      EConstr Δ e e' n n' ->
      EType Δ (tind_array tau e e') (Tarray t n n').

(** The type elaboration relation for generic constant type
    indication. *)

Inductive ETypeg : tind -> type -> Prop :=
| ETypeGBool : ETypeg tind_boolean Tbool
| ETypeGNat :
    forall {e e' n n'},
      EConstrG e e' n n' ->
      ETypeg (tind_natural e e') (Tnat n n').

(** Hints for EType and ETypeg *)

#[export] Hint Constructors EType : hvhdl.
#[export] Hint Constructors ETypeg : hvhdl.
