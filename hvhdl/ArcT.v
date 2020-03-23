(** * The type of Petri net arcs (arc_t). *)

Require Import Coqlib.

(** Defines the type of Petri net arcs. *)

Inductive arc_t : Type := basic | test | inhibitor.

(** Implements the equality between two arc_t values. *)

Definition eqb (a a' : arc_t) : bool :=
  match a, a' with
  | basic, basic => true
  | test, test => true
  | inhibitor, inhibitor => true
  | _, _ => false
  end.
