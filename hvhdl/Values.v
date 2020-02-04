(** Module defining the type of identifiers and values that are common
    to the syntax and the semantics of H-VHDL.  *)

Require Import String.

(** Type of identifiers, defined as non-empty strings. *)

Record ident : Type :=
  mk_ident { str : string; nempty : str <> EmptyString }.

(** A value is either:
    - a boolean
    - a natural number
    - a list of values. *)

Inductive value : Type :=
| Vbool : bool -> value
| Vnat : nat -> value
| Vlist : valuelist -> value
with valuelist :=
| Vnil : valuelist
| Vcons : value -> valuelist -> valuelist.
