(** * General Facts about the Sitpn Structure. *)

Require Import CoqLib.
Require Import GlobalFacts.
Require Import sitpn.Sitpn.

Set Implicit Arguments.

(** For a given [sitpn], defines the equivalence relation [Peq]
    between two places as the equality between the first element
    of the [sig] type [P sitpn].  *)

Definition Peq sitpn (p p' : P sitpn) : Prop := P1SigEq p p'.

(** For a given [sitpn], defines the equivalence relation [Pkeq]
    between two pairs where places are the first elements of the
    pairs.  *)

Definition Pkeq sitpn {A : Type} (p p' : P sitpn * A) : Prop :=
  Peq (fst p) (fst p') /\ snd p = snd p'.

Arguments Peq {sitpn}.
Arguments Pkeq {sitpn A}.

(** The equivalence relation [Peq] is decidable. *)

Definition Peqdec sitpn (x y : P sitpn) : {Peq x y} + {~Peq x y} :=
  P1SigEqdec Nat.eq_dec x y.
Arguments Peqdec {sitpn}.

(* The [SetoidList.InA] predicate is decidable with [Peq] as the
   equality relation. *)

Definition InA_Peq_dec sitpn (p : P sitpn) (lofP : list (P sitpn)) :
  {SetoidList.InA Peq p lofP} + {~SetoidList.InA Peq p lofP} :=
  InA_P1SigEq_dec (fun n => In n sitpn.(places)) Nat.eq_dec p lofP.

(*  *)

Definition Equivalence_Peq sitpn := Equivalence_P1SigEq (In_P sitpn).

#[export] Hint Unfold Peq Pkeq Peqdec : core.

(** For a given [sitpn], defines the equivalence relation [Teq]
    between two transitions as the equality between the first element
    of the [sig] type [T sitpn].  *)

Definition Teq sitpn (t t' : T sitpn) : Prop := P1SigEq t t'.

(* SetoidList InA predicate is decidable if eq = Teq *)

Definition Teq' sitpn (Q : T sitpn -> Prop) (t t' : Tsubset Q) : Prop :=
  Teq (proj1_sig t) (proj1_sig t').

(** For a given [sitpn], defines the equivalence relation [Tkeq]
    between two pairs where transitions are the first elements of the
    pairs.  *)

Definition Tkeq sitpn {A : Type} (p p' : T sitpn * A) : Prop :=
  Teq (fst p) (fst p') /\ snd p = snd p'.

Arguments Teq {sitpn}.
Arguments Tkeq {sitpn A}.

(** The equivalence relation [Teq] is decidable. *)

Definition Teqdec sitpn (x y : T sitpn) : {Teq x y} + {~Teq x y} :=
  P1SigEqdec Nat.eq_dec x y.
Arguments Teqdec {sitpn}.


(** The equivalence relation [Teq'] is also decidable. *)

Definition Teq'_dec sitpn {Q : T sitpn -> Prop}
           (x y : Tsubset Q) : {Teq' x y} + {~Teq' x y} :=
  Teqdec (proj1_sig x) (proj1_sig y).
Arguments Teq'_dec {sitpn Q}.

(* The [SetoidList.InA] predicate is decidable with [Teq] as the
   equality relation. *)

Definition InA_Teq_dec sitpn (t : T sitpn) (lofT : list (T sitpn)) :
  {SetoidList.InA (@Teq sitpn) t lofT} + {~SetoidList.InA (@Teq sitpn) t lofT} :=
  InA_P1SigEq_dec (fun n => In n sitpn.(transitions)) Nat.eq_dec t lofT.

#[export] Hint Unfold Teq Tkeq Teqdec : core.

(** For a given [sitpn], defines the equivalence relation [Aeq]
    between two actions as the equality between the first element
    of the [sig] type [A sitpn].  *)

Definition Aeq sitpn (a a' : A sitpn) : Prop := P1SigEq a a'.
Arguments Aeq {sitpn}.

(** For a given [sitpn], defines the equivalence relation [Akeq]
    between two pairs where actions are the first elements of the
    pairs.  *)

Definition Akeq sitpn {B : Type} (p p' : A sitpn * B) : Prop := Aeq (fst p) (fst p') /\ snd p = snd p'.

Arguments Akeq {sitpn B}.

(** The equivalence relation [Aeq] is decidable. *)

Definition Aeqdec sitpn (x y : A sitpn) : {Aeq x y} + {~Aeq x y} :=
  P1SigEqdec Nat.eq_dec x y.
Arguments Aeqdec {sitpn}.

#[export] Hint Unfold Aeq Akeq Aeqdec : core.

(** For a given [sitpn], defines the equivalence relation [Feq]
    between two functions as the equality between the first element of
    the [sig] type [F sitpn].  *)

Definition Feq sitpn (f f' : F sitpn) : Prop := P1SigEq f f'.
Arguments Feq {sitpn}.

(** For a given [sitpn], defines the equivalence relation [Fkeq]
    between two pairs where functions are the first elements of the
    pairs.  *)

Definition Fkeq sitpn {B : Type} (p p' : F sitpn * B) : Prop := Feq (fst p) (fst p') /\ snd p = snd p'.

Arguments Fkeq {sitpn B}.

(** The equivalence relation [Feq] is decidable. *)

Definition Feqdec sitpn (x y : F sitpn) : {Feq x y} + {~Feq x y} :=
  P1SigEqdec Nat.eq_dec x y.
Arguments Feqdec {sitpn}.

#[export] Hint Unfold Feq Fkeq Feqdec : core.

(** For a given [sitpn], defines the equivalence relation [Ceq]
    between two conditions as the equality between the first element
    of the [sig] type [C sitpn].  *)

Definition Ceq sitpn (c c' : C sitpn) : Prop := P1SigEq c c'.
Arguments Ceq {sitpn}.

(** For a given [sitpn], defines the equivalence relation [Ckeq]
    between two pairs where conditions are the first elements of the
    pairs.  *)

Definition Ckeq sitpn {B : Type} (p p' : C sitpn * B) : Prop := Ceq (fst p) (fst p') /\ snd p = snd p'.

Arguments Ckeq {sitpn B}.

(** The equivalence relation [Ceq] is decidable. *)

Definition Ceqdec sitpn (x y : C sitpn) : {Ceq x y} + {~Ceq x y} :=
  P1SigEqdec Nat.eq_dec x y.
Arguments Ceqdec {sitpn}.

#[export] Hint Unfold Ceq Ckeq Ceqdec : core.
