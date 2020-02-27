(** Module defining the semantics domains used in H-VHDL semantics. *)

Require Import Coqlib.
Require Import Arrays.
Require Import GlobalTypes.
Require Import AbstractSyntax.

(** Defines the type of values used in the 
    semantical world.

    A value is either:
    - a boolean
    - a natural number
    - an element of arc_t
    - an element of transition_t
    - a list of values. *)

Inductive value : Type :=
| Vbool : bool -> value
| Vnat : nat -> value
| Varc : arc_t -> value
| Vtransition : transition_t -> value
| Varray : forall {n}, array value n -> value.

(** Defines the type of types used in the
    semantical world. *)

Inductive type : Type :=
| Tbool                                 (** Boolean *)
| Tnat (l : nat) (u : nat)              (** Constrained natural. *)
| Tarray (t : type) (l : nat) (u : nat) (** Fixed-size array. *)
| Tarc_t                                (** arc_t type. *)
| Ttransition_t.                        (** transition_t type. *)


