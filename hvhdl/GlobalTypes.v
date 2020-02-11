(** Defines types that are used both in the
    syntactical and semantical part of H-VHDL. *)

Require Import Coqlib.

Include NatMap.
Include NatSet.

(** Type of identifiers, defined as natural. *)

Definition ident := nat.

(** Defines IdMap ∈ ident → A, as NatMap. *)

Definition IdMap (A : Type) := NatMap.t A.

(** Defines IdSet ≡ NatSet.t *)

Definition IdSet := NatSet.t.


