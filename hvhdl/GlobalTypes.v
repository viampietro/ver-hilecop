(** Defines types that are used both in the
    syntactical and semantical part of H-VHDL. *)

Require Import Coqlib.
Require Export NatMap.
Require Export NatSet.
Require Export ArcT.
Require Export TransitionT.

(** Type of identifiers, defined as natural. *)

Definition ident := nat.

(** Defines IdMap ∈ ident → A, as NatMap. *)

Definition IdMap (A : Type) := NatMap.t A.

(** Defines IdSet ≡ NatSet.t *)

Definition IdSet := NatSet.t.

(** Returns the differentiated intersection domain of to IdMaps. 
    
    Let m and m' be of type IdMap. The differentiated intersection
    domain of the two maps is defined as follows:
    
    m ∩≠ m' = { x ∈ dom(m) ∩ dom(m') | m(x) ≠ m(x') }
 *)

Import NatMap.

Inductive IsDiffIntersectDom {A} (m m' : IdMap A) : IdSet -> Prop :=
| IsDiffIntersectDom_ :
    forall (x : ident),
      MapsTo x a m ->
      MapsTo x a' m' ->
      IsDiffIntersectDom.

(** Defines the maximum value taken by a natural number
    in H-VHDL.

    For now, NATMAX equals 2^31 - 1 (max. value on 32 bits).
 *)

Definition NATMAX := 2147483647.
