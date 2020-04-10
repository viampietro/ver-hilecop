(** * SITPN global types. *)

(** Defines the global types used in the definition of the SITPN
    structure and the SITPN semantics. *)

Require Import Coqlib.
Require Import NatSet.

(** Defines the type representing the disjoint union N ⊔ {∞}. *)

Inductive PositiveIntervalBound : Set :=
| pos_inf : PositiveIntervalBound
| pos_val (n : nat) : PositiveIntervalBound.

Coercion pos_val : nat >-> PositiveIntervalBound.
Notation "i+" := pos_inf (at level 0).

(** Defines the type of time interval ≡ I+
    [a,b] ∈ I+, where a ∈ N and b ∈ N ⊔ {∞} *)

Structure TimeInterval : Set :=
  mk_TimeItval {
      min_t : nat;
      max_t : PositiveIntervalBound;
    }.

Notation "'<|' a , b '|>'" := (mk_TimeItval a b) (b at level 69).

(** Returns a time interval equals to interval [i] with the value of
    its bounds decremented. *)

Definition dec_itval (i : TimeInterval) : TimeInterval :=
  match i with
  | <| a, pos_val b |> => <| (a - 1), (b - 1) |>
  | <| a, i+ |> => <| (a - 1), i+ |>
  end.

Notation "i '--'" := (dec_itval i) (at level 0).

(** Defines the type of dynamic time intervals ≡ I+ ⊔ {ψ} *)

Inductive DynamicTimeInterval : Set :=
| active : TimeInterval -> DynamicTimeInterval
| blocked : DynamicTimeInterval.

Coercion active : TimeInterval >-> DynamicTimeInterval.
