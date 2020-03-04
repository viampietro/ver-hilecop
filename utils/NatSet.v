Require Import MSets.

(** Defines finite sets of natural. *)

Module NatSet := MSetList.Make (Nat_as_OT).
Include NatSet.

