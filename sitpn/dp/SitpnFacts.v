(** * General Facts about the Sitpn Structure. *)

Require Import Coqlib.
Require Import GlobalFacts.
Require Import dp.Sitpn.

Set Implicit Arguments.

(** For a given [sitpn], defines the equivalence relation [Peq]
    between two places as the equality between the first element
    of the [sig] type [P sitpn].  *)

Definition Peq sitpn (p p' : P sitpn) : Prop := seq p p'.
Arguments Peq {sitpn}.

(** The equivalence relation [Peq] is decidable. *)

Definition Peqdec sitpn (x y : P sitpn) : {Peq x y} + {~Peq x y} :=
  seqdec Nat.eq_dec x y.
Arguments Peqdec {sitpn}.

(** For a given [sitpn], defines the equivalence relation [Teq]
    between two transitions as the equality between the first element
    of the [sig] type [T sitpn].  *)

Definition Teq sitpn (t t' : T sitpn) : Prop := seq t t'.

(** Equivalence relation between two transitions that are elements of
    a subset of T. *)

Definition Teq' sitpn (Q : T sitpn -> Prop) (t t' : Tsubset Q) : Prop :=
  Teq (proj1_sig t) (proj1_sig t').

(** The equivalence relation [Teq] is decidable. *)

Definition Teqdec sitpn (x y : T sitpn) : {Teq x y} + {~Teq x y} :=
  seqdec Nat.eq_dec x y.
Arguments Teqdec {sitpn}.

(** The equivalence relation [Teq'] is also decidable. *)

Definition Teq'_dec sitpn {Q : T sitpn -> Prop}
           (x y : Tsubset Q) : {Teq' x y} + {~Teq' x y} :=
  Teqdec (proj1_sig x) (proj1_sig y).
Arguments Teq'_dec {sitpn Q}.

(** For a given [sitpn], defines the equivalence relation [Aeq]
    between two actions as the equality between the first element
    of the [sig] type [A sitpn].  *)

Definition Aeq sitpn (a a' : A sitpn) : Prop := seq a a'.
Arguments Aeq {sitpn}.

(** The equivalence relation [Aeq] is decidable. *)

Definition Aeqdec sitpn (x y : A sitpn) : {Aeq x y} + {~Aeq x y} :=
  seqdec Nat.eq_dec x y.
Arguments Aeqdec {sitpn}.

(** For a given [sitpn], defines the equivalence relation [Feq]
    between two functions as the equality between the first element of
    the [sig] type [F sitpn].  *)

Definition Feq sitpn (f f' : F sitpn) : Prop := seq f f'.
Arguments Feq {sitpn}.

(** The equivalence relation [Feq] is decidable. *)

Definition Feqdec sitpn (x y : F sitpn) : {Feq x y} + {~Feq x y} :=
  seqdec Nat.eq_dec x y.
Arguments Feqdec {sitpn}.

(** For a given [sitpn], defines the equivalence relation [Ceq]
    between two conditions as the equality between the first element
    of the [sig] type [C sitpn].  *)

Definition Ceq sitpn (c c' : C sitpn) : Prop := seq c c'.
Arguments Ceq {sitpn}.

(** The equivalence relation [Ceq] is decidable. *)

Definition Ceqdec sitpn (x y : C sitpn) : {Ceq x y} + {~Ceq x y} :=
  seqdec Nat.eq_dec x y.
Arguments Ceqdec {sitpn}.
