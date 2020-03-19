(** Defines types that are used both in the
    syntactical and semantical part of H-VHDL. *)

Require Import Coqlib.
Require Export NatMap.
Require Export NatSet.
Require Export ArcT.
Require Export TransitionT.

(** Defines the maximum value taken by a natural number
    in H-VHDL.

    For now, NATMAX equals 2^31 - 1 (max. value on 32 bits).
 *)

Definition NATMAX := 2147483647.

(** Type of identifiers, defined as natural. *)

Definition ident := nat.

(** Defines to reserved identifiers for the clock and the reset
    signals. Every design in H-VHDL are equipped with a clock and a
    reset signal, which are ports in "in" mode.

    We must enforce the fact that a H-VHDL must declare these two
    ports in its port interface; [clk] and [rst] ports must be of the
    boolean type.

 *)

Definition clk : ident := 0.
Definition rst : ident := 1.

(** Defines IdMap ∈ ident → A, as NatMap. *)

Definition IdMap (A : Type) := NatMap.t A.

(** Defines IdSet ≡ NatSet.t *)

Definition IdSet := NatSet.t.


