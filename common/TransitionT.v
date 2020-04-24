(** * The type of Petri net transitions (transition_t). *)

(** Defines the type of Petri net transitions. *)

Inductive transition_t : Type := not_temporal | temporal_a_b |
                                 temporal_a_a | temporal_a_inf.

(** Implements the equality between two transition_t values. *)

Definition eqb (t t' : transition_t) : bool :=
  match t, t' with
  | not_temporal, not_temporal => true
  | temporal_a_b, temporal_a_b => true
  | temporal_a_a, temporal_a_a => true
  | temporal_a_inf, temporal_a_inf => true
  | _, _ => false
  end.
