Require Import FMaps.

(** Defines maps with key of the natural type. *)

Module NatMap := FMapWeakList.Make (Nat_as_OT).
Include NatMap.

Definition EqualDom {A} (m m' : t A) : Prop := forall (k : nat), In k m <-> In k m'.

Module NatMapFacts := Facts NatMap.
Include NatMapFacts.

(** ** Extra Facts on NatMap *)

Lemma MapsTo_add_eqv :
  forall {A : Type} {x : key} {e e' : A} {m},
    NatMap.MapsTo x e (NatMap.add x e' m) -> e = e'.
Proof.
  intros *; erewrite (NatMapFacts.add_mapsto_iff).
  inversion 1 as [(a, b) | (c ,d) ]; [auto | contradiction].
Qed.

Lemma MapsTo_add_eqv_2 :
  forall {A : Type} {x : key} {e e' : A} {m},
    e = e' -> NatMap.MapsTo x e (NatMap.add x e' m).
Proof.
  intros *; intros eq_; rewrite eq_; apply add_1; reflexivity.
Qed.

(** ** Hints to solve goals with MapsTo *)

#[export] Hint Resolve MapsTo_fun add_1 add_2 add_3 : mapsto.
#[export] Hint Extern 1 (MapsTo ?k ?v (add ?k ?v ?m)) => apply (add_1 m v eq_refl) : mapsto.

Export NatMap NatMapFacts.



