Require Import MSets.

(** Defines finite sets of natural. *)

Module NatSet := MSetList.Make (Nat_as_OT).
Include NatSet.

Declare Scope natset_scope.

Infix "U" := union (at level 60, right associativity).
Infix "U+" := add (at level 60, right associativity).
Notation "{ }" := empty (format "{ }") : natset_scope.
Notation "{ x , y , .. , z }" := (add x (add y .. (add z empty) ..)) : natset_scope.
Notation "{ x }s" := (add x empty) : natset_scope.



