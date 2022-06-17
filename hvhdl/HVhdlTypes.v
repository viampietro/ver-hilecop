(** Defines types that are used both in the
    syntactical and semantical part of H-VHDL. *)

Require Import CoqLib.
Require Import NatMap.
Require Import NatSet.

(** Defines the maximum value taken by a natural number in H-VHDL.

    According to the VHDL language specification, NATMAX equals at
    least 2^31 - 1 (max. value on 32 bits).  =~ 2147483647 

 *)

Definition NATMAX : N := 2147483647.

(** Type of identifiers, defined as natural. *)

Definition ident := nat.

(** Defines IdMap ∈ ident → A, as NatMap.
    
    Useful to implement partial functions of type ident → A as mutable
    structures (addition, removal, lookup of values). *)

Definition IdMap (A : Type) := NatMap.t A.

(** Defines IdSet ≡ NatSet.t *)

Definition IdSet := NatSet.t.

(** Enumerates the different phases of the H-VHDL simulation
    algorithm.  *)

Inductive simflag : Set := falling | rising | stab | init.
