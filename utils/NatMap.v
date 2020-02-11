Require Import FMaps.

(** Defines maps with key of the natural type. *)

Module NatMap := FMapList.Make (Nat_as_OT).
