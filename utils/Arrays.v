(** Module that defines the array structure.

    Arrays are an important data structure of the H-VHDL semantics.
 *)

Require Import Vector.
Require Import Omega.

(* (** Defines the interface of arrays with indexes of the [nat] type. *) *)

(* Module Type ARRAY. *)

(*   (** Array abstract type. *) *)
(*   Parameter array : Type -> nat -> Type. *)
  
(*   (** Array creation. *) *)
(*   Parameter create : forall {A n}, A -> array A n. *)

(*   (** Access to an array element. *) *)
(*   Parameter read : forall {A n}, array A n -> nat -> option A. *)

(*   (** Store an element in the array. *) *)
(*   Parameter write : forall {A n}, A -> nat -> array A n -> option (array A n). *)

(* End ARRAY. *)

(* (** Implementation of the ARRAY interface with vectors. *) *)

(* Module Array : ARRAY. *)

  (** Implements the array type with vectors (lists storing their length). *)
  
  Definition array A (size : nat) := Vector.t A size.
  
  (** Implements the array creation function.
 
     - [size] is the size of the array being created.
     - [A] is the type of the array elements.
     - [initvalue] is the initial value taken by all the array elements.

   *)

  Fixpoint create (A : Type) (size : nat) (initvalue : A) {struct size} : array A size :=
    @Vector.const A initvalue size.

  (** Implements the function to access an element of an array.
      
      - [a] is the array where the lookup is performed.
      - [i] is the index of the element being accessed.

      Returns an error (i.e, [None]) if the index [i] is
      out of bound.

   *)
          
  Fixpoint read {A n} (a : array A n) (i : nat) {struct i} : option A := 
    match i, a with
    (* Error, cannot read in an empty array. *)
    | _, Vector.nil _ => None
    | 0, Vector.cons _ v _ _ => Some v
    | S i', Vector.cons _ _ _ a' => read a' i'
    end.

  (** Implements the function to store a value [v] at 
      index [i] of the array [a].
      
      Returns an error (i.e, None) if index [i]
      is out of the array bounds. *)

  Fixpoint write {A n} (v : A) (i : nat) (a : array A n) {struct i} : option (array A n) :=
    match i, a with
    (* Error, cannot write in an empty array. *)
    | _, Vector.nil _ => None

    (* If [i] is 0, and [a] is not empty, then replaces the first
       element of [a] with value [v]. *)
    | 0, Vector.cons _ v' _ a' => Some (Vector.cons _ v _ a')

    (* If [i] is greater than zero, then replaces the i-1^th 
       element in the array of size [n-1]. *)
    | S i', Vector.cons _ v' _ a' =>
      match write v i' a' with
      | Some a''  => Some (Vector.cons _ v' _ a'')
      | None => None
      end
    end.

(* End Array. *)
