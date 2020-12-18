Require Import FMaps.

(** Defines maps with key of the natural type. *)

Module NatMap := FMapWeakList.Make (Nat_as_OT).
Include NatMap.

Definition EqualDom {A} (m m' : t A) : Prop := forall (k : nat), In k m <-> In k m'.

Module NatMapFacts := Facts NatMap.
Include NatMapFacts.

(** ** Hints to solve goals with MapsTo *)

Hint Resolve MapsTo_fun : mapsto.

Export NatMap NatMapFacts.



