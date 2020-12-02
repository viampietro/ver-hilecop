(** * HILECOP Design Declaration Store  *)

Require Import HVhdlTypes.
Require Import AbstractSyntax.
Require Import Petri.
Require Import Place.
Require Import Transition.

(** Declares the HILECOP global declaration store containing the
    declarations of the place and transition designs.  *)

Definition hdstore : IdMap design :=
  (add transition_entid transition_design
       (add place_entid place_design (NMap.empty design))).
