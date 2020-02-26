(** Module that defines the typing relation, i.e the relation that
    checks that a value belongs to a certain type.

    Particularly for [nat] and [array], a value belongs to these type
    if it satisfies the range or index constraint.  *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import SemanticalDomains.

(** Defines the typing relation [is_of_type]. *)

Inductive is_of_type : value -> type -> Prop :=
| IsBool : forall (b : bool), is_of_type (Vbool b) Tbool
| IsArcT : forall (a : arc_t), is_of_type (Varc a) Tarc_t
| IsTransitionT : forall (t : transition_t), is_of_type (Vtransition t) Ttransition_t

(** Value n must satisfy the index constraint, i.e n ∈ [l,u]. *)
| IsNat : forall (n l u : nat), l <= n <= u -> is_of_type (Vnat n) (Tnat l u)

(** All elements of the value list [lv] must be of type [t],
    and the length of [lv] must satisfy the index constraint.
 *)
| IsArrayOfT :
    forall (lv : list value) (t : type) (l u : nat),
      (forall (v : value), In v lv -> is_of_type v t) ->
      length lv = u - l + 1 ->
      is_of_type (Vlist lv) (Tarray t l u).
      
