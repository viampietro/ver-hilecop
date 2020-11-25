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

(** Equality is decidable for natinf. *)

Definition eq_natinf_dec : forall x y : natinf, {x = y} + {x <> y}. do 2 (decide equality). Defined.
  
(** Decrements a natinf. Does nothing if [ni] is +∞. *)

Lemma neqinf : i+ <> i+ -> False. congruence. Defined.

Definition dec_natinf (ni : natinf) : ni <> i+ -> natinf :=
  match ni return ni <> i+ -> natinf with
  | i+ => (fun pf : i+ <> i+ => match neqinf pf with end)
  | ninat n => (fun _ => ninat (n - 1))
  end.

(** Defines the less than or equal relation between a nat and a
    natinf. *)

Definition le_nat_natinf (n : nat) (ni : natinf) : ni <> i+ -> Prop :=
  match ni return ni <> i+ -> Prop with
  | i+ => (fun pf : i+ <> i+ => match neqinf pf with end) 
  | ninat m => (fun _ => n <= m)
  end.

(** Defines the equality relation between a nat and a
    natinf. *)

Definition eq_nat_natinf (n : nat) (ni : natinf) : ni <> i+ -> Prop :=
  match ni return ni <> i+ -> Prop with
  | i+ => (fun pf : i+ <> i+ => match neqinf pf with end) 
  | ninat m => (fun _ => n = m)
  end.

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

(** Equivalence relation between NatInfInterval. *)

Definition eq_niit (x y : NatInfInterval) : Prop :=
  (a x) = (a y) /\ if eq_natinf_dec (b x) (b y) then True else False.

(** For every NatInfInterval [a, b], if [a, b] is well-formed, that is
    a <= b \/ b = ∞, then [a - 1, b - 1] is well-formed. *)

Lemma decr_natinf_is_well_formed :
  forall a b notinf,
    le_nat_natinf a b notinf ->
    forall notinf', le_nat_natinf (a - 1) (dec_natinf b notinf) notinf'.
Proof.
  intros a b. induction b; intros.
  - contradiction.
  - simpl. apply Nat.sub_le_mono_r. assumption.
Defined.

Lemma le_nat_le_natinf :
  forall a b, a <= b -> forall notinf, le_nat_natinf a b notinf.
Proof.
  unfold le_nat_natinf. intros; assumption.
Defined.

(** Defines some NatInfInterval. *)

Definition ditval00 := MkNatInfItval 0 0 (le_nat_le_natinf 0 0 (le_n 0)).

(** Defines the type of time interval ≡ I+
    [a,b] ∈ I+, where a ∈ N* and b ∈ N ⊔ {∞} 
    and a <= b *)

Structure StaticTimeInterval : Set :=
  MkSTimeItval {
      itval : NatInfInterval;
      lower_is_natstar : (a itval) > 0;
    }.

(* Defines a predicate stating that two StaticTimeInterval do
   not overlap, i.e, the intersection of the two is empty.
 *)

Definition NoOverlap (i i' : StaticTimeInterval) : Prop :=
  match i, i' with
  | MkSTimeItval <| a, ninat b |> _, MkSTimeItval <| a', ni |> _ => b < a'
  | MkSTimeItval <| a, ni |> _, MkSTimeItval <| a', ninat b' |> _ => b' < a
  | _, _ => False
  end.

(** Defines the type of dynamic time intervals ≡ I+ ⊔ {ψ} *)

Inductive DynamicTimeInterval : Set :=
| active : NatInfInterval -> DynamicTimeInterval
| blocked : DynamicTimeInterval.

Coercion active : NatInfInterval >-> DynamicTimeInterval.

Lemma absurd_natinf : forall a b, b = i+ -> (forall bneqinf, le_nat_natinf a b bneqinf).
  intros a b beqinf bneqinf; contradiction.
Defined.

(** Returns a time interval equals to interval [i] with the value of
    its bounds decremented. *)

Definition dec_itval (i : NatInfInterval) : DynamicTimeInterval.
  refine (match eq_natinf_dec (b i) i+ with
          | left beqinf => MkNatInfItval ((a i) - 1) (b i) (absurd_natinf ((a i) - 1) (b i) beqinf)
          | right bneqinf => MkNatInfItval ((a i) - 1) (dec_natinf (b i) bneqinf) _
          end); apply decr_natinf_is_well_formed; apply (is_well_formed i).
Defined.

Notation "i '--'" := (dec_itval i) (at level 0).

(** Equivalence relation between DynamicTimeInterval. *)

Definition eq_ditval (x y : DynamicTimeInterval) : Prop :=
  match x, y with
  | blocked, blocked => True
  | active a, active b => eq_niit a b
  | _, _ => False
  end.

(** Defines the set {0,1,-1}, useful to express the association of
    condition and barred condition to transition. *)

Inductive MOneZeroOne : Set := mone | zero | one.

(** Clock events set. *)

Inductive Clk := rising_edge | falling_edge.
