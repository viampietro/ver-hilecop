(** * SITPN global types. *)

(** Defines the global types used in the definition of the SITPN
    structure and the SITPN semantics. *)

Require Import Coqlib.
Require Import NatSet.
Require Import GlobalTypes.

(** Defines the type representing the disjoint union N ⊔ {+∞}. *)

Inductive natinf : Set :=
| niinf : natinf
| ninat : nat -> natinf.

Coercion ninat : nat >-> natinf.
Notation "i+" := niinf (at level 0).

(** Decrements a natinf. Does nothing if [ni] is +∞. *)

Definition dec_natinf (ni : natinf) : natinf :=
  match ni with
  | i+ => i+
  | ninat n => ninat (n - 1)
  end.

(** Converts a [natinf] into a [nat] given a proof that
    it is different from +∞.
 *)

Definition natinf_to_nat (ni : natinf) : ni <> i+ -> nat.
  refine (match ni return ni <> i+ -> nat with
          | i+ => (fun _ => False_rect _ _)
          | ninat n => (fun _ => n)
          end); congruence.
Defined.

Coercion natinf_to_nat : natinf >-> Funclass.

(** Defines the less than or equal relation between a nat and a
    natinf. *)

Definition le_nat_natinf (n : nat) (ni : natinf) : ni <> i+ -> Prop.
  refine (match ni with
          | i+ => _
          | ninat m => (fun _ => n <= m)
          end); contradiction.
Defined.

(** States that N is dijoint from {+∞}. *)

Definition nat_diff_inf : forall n, ninat n <> i+. congruence. Defined.

(** Defines the type of well-formed intervals [a,b] where 
    a ∈ N and b ∈ N ⊔ {+∞} and a <= b.
 *)

Inductive NatInfInterval : Set := 
  MkNatInfItval {
      a : nat;
      b : natinf;
      is_well_formed : forall notinf, le_nat_natinf a b notinf;
    }.

Notation "'<|' a , b '|>'" := (MkNatInfItval a b _) (b at level 69).

(** Defines the type of time interval ≡ I+
    [a,b] ∈ I+, where a ∈ N* and b ∈ N ⊔ {∞} 
    and a <= b *)

Structure StaticTimeInterval : Set :=
  MkSTimeItval {
      itval : NatInfInterval;
      lower_is_natstar : (a itval) > 0;
    }.

(** Defines the type of dynamic time intervals ≡ I+ ⊔ {ψ} *)

Inductive DynamicTimeInterval : Set :=
| active : NatInfInterval -> DynamicTimeInterval
| blocked : DynamicTimeInterval.

Coercion active : NatInfInterval >-> DynamicTimeInterval.

(** Returns a time interval equals to interval [i] with the value of
    its bounds decremented. *)

Definition dec_itval (i : NatInfInterval) : DynamicTimeInterval.
  refine (match i with
          | MkNatInfItval a b _ => MkNatInfItval (a - 1) (dec_natinf b) _
          end).
  intros notinf; induction b.
    - contradiction.
    - simpl.
      simpl in notinf.
      specialize (l (nat_diff_inf n)).
      apply Nat.sub_le_mono_r.
      assumption.
Defined.

Notation "i '--'" := (dec_itval i) (at level 0).

(** Defines the set {0,1,-1}, useful to express the association of
    condition and barred condition to transition. *)

Inductive MOneZeroOne : Set := mone | zero | one.
