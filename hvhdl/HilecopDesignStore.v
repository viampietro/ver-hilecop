(** * HILECOP Design Declaration Store  *)

Require Import HVhdlTypes.
Require Import AbstractSyntax.
Require Import Petri.
Require Import Place.
Require Import Transition.

(** Declares the HILECOP global declaration store containing the
    declarations of the place and transition designs.  *)

Definition hdstore : IdMap design :=
  (NatMap.add transition_entid transition_design
              (NatMap.add place_entid place_design (NatMap.empty design))).
