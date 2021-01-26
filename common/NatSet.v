Require Import MSets.

(** Defines finite sets of natural. *)

Module NatSet := MSetWeakList.Make (Nat_as_OT).
Include NatSet.

Module NatSetFacts := Facts NatSet.

Declare Scope natset_scope.

Infix "U" := union (at level 60, right associativity).
Infix "U+" := add (at level 60, right associativity).
Notation "{[ ]}" := empty (format "{[ ]}") : natset_scope.
Notation "{[ x , y , .. , z ]}" := (add x (add y .. (add z empty) ..)) : natset_scope.
Notation "{[ x ]}" := (add x empty) (at level 0) : natset_scope.

Export NatSet NatSetFacts.

