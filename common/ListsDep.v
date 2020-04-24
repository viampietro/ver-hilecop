(** * Utilities for lists of dependent elements. *)

Require Import List.
Require Import ListsPlus.

(** Given a proof that list [sl] is included in [l], converts [sl]
    into a list of [A]s that are in [l].  *)

Fixpoint list2listin_aux A (Aeq_dec : forall x y : A, {x = y} + {x <> y}) (l sl : list A) {struct sl} :
  incl sl l -> list { a | In a l } :=
  match sl with
  | nil => (fun _ => nil)
  | n :: tl =>
    (fun (p : _) =>
       let in_n_l := (p n (in_eq n tl)) in
       let incl_tl_l := (incl_cons_inv n tl l p) in
       (exist _ n in_n_l) :: list2listin_aux _ Aeq_dec l tl incl_tl_l)
  end.

(** Converts a list [l] of type [list A] into a list of type [list {a
| a ∈ l}] of elements that verify their inclusion in [l]
    
    Useful to pass to argument to functions that map elements of a
    finite set, implemented with a list, to another set.
 
 *)

Definition list2listin A (Aeq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) :
  list {a | In a l} :=
  list2listin_aux _ Aeq_dec l l (incl_refl l).
