(** * SITPN global types. *)

(** Defines the global types used in the definition of the SITPN
    structure and the SITPN semantics. *)

Require Import Coqlib.
Require Import NatSet.
Require Import GlobalTypes.

(** Defines the type representing the disjoint union N* ⊔ {∞}. *)

Inductive natinf : Set :=
| niinf : natinf
| ninat : natstar -> natinf.

Coercion ninat : natstar >-> natinf.
Notation "i+" := niinf (at level 0).

(** Equivalence between natinf *)

Definition eq_natinf (ni ni' : natinf) : Prop :=
  match ni, ni' with
  | niinf, niinf => True
  | ninat n, ninat m  => proj1_sig n = proj1_sig m
  | _, _ => False
  end.

(** Equality is decidable for natinf. *)

Definition eq_natinf_dec : forall x y : natinf, {eq_natinf x y} + {~eq_natinf x y}.
  destruct x, y.
  - left; simpl; exact I.
  - right; simpl; intro; contradiction.
  - right; simpl; intro; contradiction.
  - simpl; apply Nat.eq_dec.
Defined.
  
(** Decrements a natinf. Does nothing if [ni] is +∞. *)

Lemma neqinf : i+ <> i+ -> False. congruence. Defined.

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

(** Defines the greater than relation between a nat and natinf. *)

Definition gt_nat_natinf (n : nat) (ni : natinf) : ni <> i+ -> Prop :=
  match ni return ni <> i+ -> Prop with
  | i+ => (fun pf : i+ <> i+ => match neqinf pf with end) 
  | ninat m => (fun _ => n > m)
  end.

(** States that N is dijoint from {+∞}. *)

Definition nat_diff_inf : forall n, ninat n <> i+. congruence. Defined.

(** ** TimeInterval *)

(** Defines the type of well-formed time intervals [a,b] where a ∈ N*
    and b ∈ N* ⊔ {+∞} and a <= b.  *)

Inductive TimeInterval : Set := 
  MkTItval {
      a : natstar;
      b : natinf;
      is_well_formed : (forall notinf, le_nat_natinf a b notinf) \/ b = niinf;
    }.

Notation "'<|' a ',' b '|>'" := (MkTItval a b _) (b at level 69).

(** Equivalence relation between NatInfInterval. *)

Definition eq_ti (x y : TimeInterval) : Prop :=
  proj1_sig (a x) = proj1_sig (a y) /\ if eq_natinf_dec (b x) (b y) then True else False.

Lemma le_nat_le_natinf :
  forall a (b : natstar), a <= (proj1_sig b) -> forall notinf, le_nat_natinf a b notinf.
Proof.
  unfold le_nat_natinf. intros; assumption.
Defined.

(** Defines some TimeInterval. *)

Definition itAB (a b : natstar) (le_AB : a <= b) :=
  MkTItval a (ninat b) (or_introl (le_nat_le_natinf a b le_AB)).

Definition itAA (a : natstar) := MkTItval a (ninat a) (or_introl (le_nat_le_natinf a a (le_n a))).
Definition itAinf (a : natstar) := MkTItval a niinf (or_intror (eq_refl niinf)).

Definition it1inf := itAinf onens.
Definition it11 := itAA onens.
Definition it12 := itAB onens twons (le_n_Sn 1).
Definition it34 := itAB threens fourns (le_n_Sn 3).
Definition it33 := itAA threens.
Definition it10inf := itAinf tenns.

(* Defines a predicate stating that two StaticTimeInterval do
   not overlap, i.e, the intersection of the two is empty.
 *)

Definition NoOverlap (i i' : TimeInterval) : Prop :=
  match i, i' with
  | MkTItval a (ninat b) _, MkTItval a' niinf _ => b < a'
  | MkTItval a niinf _, MkTItval a' (ninat b') _ => b' < a
  | MkTItval a (ninat b) _, MkTItval a' (ninat b') _ => b' < a \/ b < a' 
  | _, _ => False
  end.

Definition nooverlap (i i' : TimeInterval) : bool :=
  match i, i' with
  | MkTItval a (ninat b) _, MkTItval a' niinf _ => b <? a'
  | MkTItval a niinf _, MkTItval a' (ninat b') _ => b' <? a
  | MkTItval a (ninat b) _, MkTItval a' (ninat b') _ => (b' <? a) || (b <? a') 
  | _, _ => false
  end.

Definition dec_nooverlap : forall i i', {NoOverlap i i'} + {~NoOverlap i i'}.
  destruct i, i'.
  destruct b0, b1.
  - right; simpl; intro; contradiction.
  - specialize (lt_dec n a0) as nat_lt_dec; destruct nat_lt_dec.
    simpl; left; assumption.
    simpl; right; assumption.
  - specialize (lt_dec n a1) as nat_lt_dec; destruct nat_lt_dec.
    simpl; left; assumption.
    simpl; right; assumption.
  - simpl. specialize (lt_dec n0 a0) as nat_lt_dec; destruct nat_lt_dec.
    left; left; assumption.
    specialize (lt_dec n a1) as nat_lt_dec. destruct nat_lt_dec.
    left; right; assumption.
    right; intro.
    induction H; [apply (n1 H) | apply (n2 H)].
Defined.

(** Defines the set {0,1,-1}, useful to express the association of
    condition and barred condition to transition. *)

Inductive MOneZeroOne : Set := mone | zero | one.

(** Clock events set = {↑, ↓}. *)

Inductive Clk := re | fe.
