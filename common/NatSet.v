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

(** ** Extra Facts on [NatSet] *)

Lemma nIn_nIn_Union :
  forall {x s s'}, ~NatSet.In x s -> ~NatSet.In x s' -> ~NatSet.In x (s U s').
Proof.
  intros *; intros nIn_s nIn_s' In_u.
  destruct (NatSetFacts.union_1 In_u); [apply nIn_s; assumption | apply nIn_s'; assumption ].
Qed.

Export NatSet NatSetFacts.


