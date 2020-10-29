 (** * Global type definitions. *)

Require Import Coqlib.
Require Import String.
Require Import Ascii.
Require Import HexString.

(** Type definitions used in all part of the Hilecop-Cert project. *)

(** Defines the set of strictly positive natural numbers. *)

Definition natstar := { n : nat | n > 0 }.

(** Casts a natstar into a nat. *)

Definition natstar_to_nat (ns : natstar) := proj1_sig ns.
Coercion natstar_to_nat : natstar >-> nat.

(** Defines some natstar. *)

Definition onens := exist _ 1 (gt_Sn_O 0).
Definition twons := exist _ 2 (gt_Sn_O 1).
Definition threens := exist _ 3 (gt_Sn_O 2).

(** ** Definitions and Facts about strict orders and boolean functions *)

Section StrictOrders.

  Variable A : Type.
  Variable eqA : A -> A -> Prop.
  Variable decEqA : forall x y, {eqA x y} + {~eqA x y}.

  Variable rel : A -> A -> Prop.
  Variable decRel : forall x y, {rel x y} + {~rel x y}.
  
  (** Defines the type of relation that are a strict order 
    over a type A.
   *)

  Inductive IsStrictOrder : Prop :=
    MkStrictOrder {
        rel_irrefl : forall a, ~rel a a;
        rel_trans : forall a b c, rel a b -> rel b c -> rel a c;

        (* Irreflexivity and transitivity entail anti-symmetry. *)
        (* rel_antisym : forall a b, rel a b -> ~rel b a; *)
      }.

  (** States that two elements of type A are comparable through
      the boolean relation [rel]. *)

  Definition AreComparable (x y : A) : Prop := rel x y \/ rel y x.

  (** States that [rel] is a strict total order over a type A, that is:  
    - [rel] is a strict order over type A.
    - all elements of A that are different are comparable with [rel].
   *)

  Definition IsStrictTotalOrder :=
    IsStrictOrder /\ forall x y, ~eqA x y -> AreComparable x y.

  (** States that [rel] is a strict order over the elements of a list
      [l].  *)

  Inductive IsStrictOrderOverList (l : list A) (nodupl : NoDup l) : Prop :=
    MkStrictOrderOverList {
        reloverl_irrefl : forall a, In a l -> ~rel a a;
        reloverl_trans : forall a b c, In a l -> In b l -> In c l ->
                                       rel a b -> rel b c -> rel a c;

        (* Irreflexivity and transitivity entail anti-symmetry. *)
        (* reloverl_antisym : forall a b, In a l -> In b l -> brel a b = true -> brel b a = false; *)
      }.

  (** States that [rel] is a strict total order over the elements of list [l], that is: 
      - [rel] is a strict order over the elements of [l]
      - all elements of [l] that are different are comparable with [rel].
   *)

  Definition IsStrictTotalOrderOverList (l : list A) (nodupl : NoDup l) :=
    IsStrictOrderOverList l nodupl /\ forall x y, ~eqA x y -> AreComparable x y.
  
End StrictOrders.

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

(** Cast from ArcT to nat. *)

Definition ArcT_in_nat (a : ArcT) :=
  match a with
  | basic => 0
  | test => 1
  | inhibitor => 2
  end.

Coercion ArcT_in_nat : ArcT >-> nat.

(** Defines the type of Petri net transitions. *)

Inductive TransitionT : Type := not_temporal | temporal_a_b |
                                temporal_a_a | temporal_a_inf.

(** Cast from TransitionT to nat. *)

Definition TransitionT_in_nat (t : TransitionT) :=
  match t with
  | not_temporal => 0
  | temporal_a_b => 1
  | temporal_a_a => 2
  | temporal_a_inf => 3
  end.

Coercion TransitionT_in_nat : TransitionT >-> nat.

(** Implements the equality between two transition_t values. *)

Definition transt_eqb (t t' : TransitionT) : bool :=
  match t, t' with
  | not_temporal, not_temporal => true
  | temporal_a_b, temporal_a_b => true
  | temporal_a_a, temporal_a_a => true
  | temporal_a_inf, temporal_a_inf => true
  | _, _ => false
  end.

(** Defines an option type able to return error messages. *)

Inductive optionE (A : Type) : Type :=
| Success : A -> optionE A
| Err : string -> optionE A.

Arguments Success {A} a.
Arguments Err {A}.

Module ErrMonadNotations.

  Notation "[| x |]" := (Success x).

  Notation "x <- e1 ; e2" := (match e1 with
                              | Err msg => Err msg
                              | Success x => e2
                              end)
                               (right associativity, at level 60).
  
  Notation "'|(' x , y ')|' <- e1 ; e2" :=
    (z <- e1; let '(x, y) := z in e2)
      (right associativity, at level 60).

  Notation "'|(' x , y , z ')|' <- e1 ; e2" :=
    (a <- e1; let '(x, y, z) := a in e2)
      (right associativity, at level 60).
    
  Definition f (n : nat) : optionE (nat * nat * nat) :=
    [| (0, 0, 0) |].

  Definition g (n : nat) : optionE (nat * nat) :=
    |( x, y , z )| <- f n; [| (x, y) |].

  
End ErrMonadNotations.

(** Converts a nat into its hexadecimal string representation. Useful
    to display variable values in error messages.  *)

Notation "$$ n" := (of_nat n) (at level 0, only parsing).

(** ** Global definitions for bool *)

Definition nullb {A : Type} := fun _ : A => false.
