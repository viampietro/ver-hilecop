(** * Arrays as lists. *)

(** Defines functions and facts to mimic the behvaior of
    arrays with lists. *)

Require Import Coqlib.

(** States that an element [elt] is at index [i] in list [l].  *)

Inductive IsAt {A} : nat -> A -> list A -> Prop :=
| IsAt_0    : forall {elt l}, IsAt 0 elt (elt :: l)
| IsAt_cons : forall {i elt elt' l}, IsAt i elt l -> IsAt (S i) elt (elt' :: l).

(** Accesses the element at position [i] in list [l]. 
    Returns an error (i.e, None) if the index is greater
    than the list length.
 *)

Fixpoint get_at {A} (i : nat) (l : list A) {struct i} : option A :=
  match i, l with
  (* Error, cannot access elements *)
  | _, [] => None
  | 0, a :: l => Some a
  | (S j), a :: l' => get_at j l'
  end.




