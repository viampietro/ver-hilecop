(** Defines types that are used both in the
    syntactical and semantical part of H-VHDL. *)

Require Import Coqlib.
Require Export NMap.
Require Export NSet.
Require Import NArith.

(** Defines the maximum value taken by a natural number
    in H-VHDL.

    For now, NATMAX equals 2^31 - 1 (max. value on 32 bits).
    =~ 2147483647
 *)

Definition NATMAX : N := 2147483647.

(** Type of identifiers, defined as natural. *)

Definition ident := N.

(** Defines IdMap ∈ ident → A, as NMap.
    
    Useful to implement partial functions of type ident → A as mutable
    structures (addition, removal, lookup of values). *)

Definition IdMap (A : Type) := NMap.t A.

(** Defines IdSet ≡ NSet.t *)

Definition IdSet := NSet.t.


