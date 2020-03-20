Require Import MSets.

(** Defines finite sets of natural. *)

Module NatSet := MSetList.Make (Nat_as_OT).
Include NatSet.

Delimit Scope natset_scope with t.

Notation "{ x ; y ; .. ; z }" := (add x (add y .. (add z empty) ..)) : natset_scope.
