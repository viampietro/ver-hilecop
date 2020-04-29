(** * Utilities for lists of dependent elements. *)

Require Import List.
Require Import ListsPlus.
Require Import Coqlib.
Require Import GlobalTypes.
Require Import Nat.

Import ListNotations.

Local Notation "'|' e '|'" := (exist _ e _) (at level 50).

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

(** States that if one can obtain a term of B from a proof that 
    a ∈ (b :: l) then one can obtain a term of B from a proof that a ∈ l.  *)

Lemma in_T_in_sublist_T {A B} :
  forall b l, (forall a : A, In a (b :: l) -> B) -> (forall (a : A), In a l -> B).
  intros b l H a H'; apply (H a (in_cons b a l H')).
Defined.

(** Given a proof that all elements in [lofAs] can yield a term of
    [B], transform each element of [lofAs] into a term [b] of [B].

    If [b] passes the [test] given in parameter then, adds [b]
    to the list [lofBs].
    
 *)

Fixpoint transform_and_filter_aux {A B}
         (lofAs : list A)
         (test : B -> bool)
         (lofBs : list B)
         {struct lofAs} :
  (forall a, In a lofAs -> B) -> list B :=
  match lofAs with
  | nil => fun _ => lofBs
  | a :: tl =>
    fun pf : _ =>
      let b := pf a (in_eq a tl) in
      let pf_tl := in_T_in_sublist_T a tl pf in
      if test b then
        transform_and_filter_aux tl test (lofBs ++ [b]) pf_tl
      else
        transform_and_filter_aux tl test lofBs pf_tl
  end.

(** Wrapper around the [transform_and_filter_aux] function. *)

Definition transform_and_filter {A B}
           (lofAs : list A)
           (test : B -> bool) :
  (forall a, In a lofAs -> B) -> list B :=
  transform_and_filter_aux lofAs test nil.

(** Tests for the [transform_and_filter] function. *)

(* Tranforming a list of nat into a list of natstar. *)

Definition lofnat : list nat := [1; 2; 4; 8; 9; 12].

Lemma forall_lofnat_gt_O :
  forall a, In a lofnat -> a > 0.
Proof.
  let rec crush :=
      match goal with
      | [ H : In ?a _ |- _ ]  => induction H; crush
      | [ H: _ = ?a |- ?a > _ ] => rewrite <- H; omega
      end
  in induction 1; crush. 
Defined.

Lemma forall_lofnat_natstar (a : nat) (H : In a lofnat) : natstar.
  exact (exist _ a (forall_lofnat_gt_O a H)).
Defined.  

Compute (transform_and_filter lofnat (fun ns => even (proj1_sig ns)) forall_lofnat_natstar). 
Compute (transform_and_filter lofnat (fun ns => odd (proj1_sig ns)) forall_lofnat_natstar).
Compute (transform_and_filter lofnat (fun ns => (proj1_sig ns) <? 0) forall_lofnat_natstar).

