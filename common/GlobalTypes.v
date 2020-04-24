(** * Global type definitions. *)

(** Type definitions used in all part of the Hilecop-Cert project. *)

(** Defines the set of strictly positive natural numbers. *)

Definition natstar := { n : nat | n > 0 }.

(** Casts a natstar into a nat. *)

Definition natstar_to_nat (ns : natstar) := proj1_sig ns.
Coercion natstar_to_nat : natstar >-> nat.

(** Defines the type of relation that are a strict order 
    over a type A.
 *)

Inductive StrictOrderB {A} (rel : A -> A -> bool) : Type :=
  MkStrictOrderB {
      rel_irrefl : forall a, rel a a = false;
      rel_trans : forall a b c, rel a b = true -> rel b c = true -> rel a c = true;

      (* Irreflexivity and transitivity entail anti-symmetry. *)
      rel_antisym : forall a b, rel a b = true -> rel b a = false;
    }.

(** Defines the type of Petri net arcs. *)

Inductive ArcT : Type := basic | test | inhibitor.

(** Implements the equality between two arc_t values. *)

Definition arct_eqb (a a' : ArcT) : bool :=
  match a, a' with
  | basic, basic => true
  | test, test => true
  | inhibitor, inhibitor => true
  | _, _ => false
  end.

(** Defines the type of Petri net transitions. *)

Inductive TransitionT : Type := not_temporal | temporal_a_b |
                                temporal_a_a | temporal_a_inf.

(** Implements the equality between two transition_t values. *)

Definition transt_eqb (t t' : TransitionT) : bool :=
  match t, t' with
  | not_temporal, not_temporal => true
  | temporal_a_b, temporal_a_b => true
  | temporal_a_a, temporal_a_a => true
  | temporal_a_inf, temporal_a_inf => true
  | _, _ => false
  end.

