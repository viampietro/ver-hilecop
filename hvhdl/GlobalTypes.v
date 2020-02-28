(** Defines types that are used both in the
    syntactical and semantical part of H-VHDL. *)

Require Import Coqlib.

(** Type of identifiers, defined as natural. *)

Definition ident := nat.

(** Defines IdMap ∈ ident → A, as NatMap. *)

Definition IdMap (A : Type) := NatMap.t A.

(** Defines IdSet ≡ NatSet.t *)

Definition IdSet := NatSet.t.

(** Defines the type of Petri net arcs. *)

Inductive arc_t : Type := basic | test | inhibitor.

(** Defines the type of Petri net transitions. *)

Inductive transition_t : Type := not_temporal | temporal_a_b |
                                 temporal_a_a | temporal_a_inf.

(** Defines the maximum value taken by a natural number
    in H-VHDL.

    For now, NATMAX equals 2^31 - 1 (max. value on 32 bits).
 *)

Definition NATMAX := 2147483647.
