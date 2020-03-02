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
| IsListOfT :
    forall (lofv : lofvalues) (t : type) (l u : nat),
      lis_of_type lofv ((u - l) + 1) t ->
      is_of_type (Vlist lofv) (Tarray t l u)
                 
(** Defines the typing relation over list of values. 
    
    By construction, checks that the list length
    is equal to the second argument (of type [nat]). *)
                 
with lis_of_type : lofvalues -> nat -> type -> Prop :=
| LIsOfTypeNil : forall {t}, lis_of_type Vnil 0 t
| LIsOfTypeCons :
    forall {lofv size t v},
      is_of_type v t ->
      lis_of_type lofv size t ->
      lis_of_type (Vcons v lofv) (S size) t.
      
