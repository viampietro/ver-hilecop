(** Module that defines the array structure.

    Arrays are a main data structure of the H-VHDL semantics.  *)

Require Import Vector.

(** Defines the interface of arrays with indexes of the [nat] type. *)

Module Type ARRAY.

  (* Type of the array of [elt] of size [nat]. *)
  Parameter array : nat -> Type -> Type.
  
  (* Array creation. *)
  Parameter create : forall (n : nat) (A : Type), A -> array n A.

  (* Access to an array element. *)
  Parameter read : forall (n : nat) (A : Type), array n A -> nat -> A.

  (* Store an element in the array. *)
  Parameter write : forall (n : nat) (A : Type), A -> nat -> array n A -> array n A.

End ARRAY.

(** Implementation of the ARRAY interface with lists. *)

Module Array : ARRAY.

  Definition array (size : nat) (A : Type) := Vector.t A size.
  
End Array.
