(** Defines the etype relation checks the well-formedness of a type
    indication τ, and transforms it into a semantical type *)

Require Import Environment.
Require Import SemanticalDomains.
Require Import AbstractSyntax.
Require Import ConstraintElaboration.

(** The type elaboration relation (general definition). *)

Inductive etype (denv : DEnv) : tind -> type -> Prop :=
| ETypeBool : etype denv tind_boolean Tbool
| ETypeArcT : etype denv tind_arc_t Tarc_t
| ETypeTransitionT : etype denv tind_transition_t Ttransition_t
| ETypeNat :
    forall {e e' n n'},
      econstr denv e e' n n' ->
      etype denv (tind_natural e e') (Tnat n n')
| ETypeArray :
    forall {tau t e e' n n'},
      etype denv tau t ->
      econstr denv e e' n n' ->
      etype denv (tind_array tau e e') (Tarray t n n').

(** The type elaboration relation for generic constant type
    indication. *)

Inductive etypeg : tind -> type -> Prop :=
| ETypeGBool : etypeg tind_boolean Tbool
| ETypeGArcT : etypeg tind_arc_t Tarc_t
| ETypeGTransitionT : etypeg tind_transition_t Ttransition_t
| ETypeGNat :
    forall {e e' n n'},
      econstrg e e' n n' ->
      etypeg (tind_natural e e') (Tnat n n').
