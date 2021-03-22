(** * HILECOP Design Declaration Store  *)

Require Import common.NatMap.
Require Import common.NatSet.

Require Import HVhdlTypes.
Require Import AbstractSyntax.
Require Import Petri.
Require Import Place.
Require Import Transition.

(** Declares the HILECOP global declaration store containing the
    declarations of the place and transition designs.  *)

Definition hdstore : IdMap design :=
  (NatMap.add transition_entid transition_design
              (NatMap.add place_entid place_design (NatMap.empty design))).

(** ** Facts about the HILECOP Design Store *)

Lemma is_place_design :
  forall {d}, MapsTo Petri.place_entid d hdstore -> d = place_design.
Proof.
  intros *; unfold hdstore.
  rewrite add_mapsto_iff.
  inversion 1 as [x | y];
    [ apply proj1 in x; inversion x
    | apply proj2 in y;
      rewrite add_mapsto_iff in y;
      inversion y as [x1 | y1];
      [ apply proj2 in x1; symmetry; assumption
      | apply proj1 in y1; contradiction ]
    ].
Defined.

Lemma is_transition_design :
  forall {d}, MapsTo Petri.transition_entid d hdstore -> d = transition_design.
Proof.
  intros *; unfold hdstore.
  rewrite add_mapsto_iff.
  inversion 1 as [x | y];
    [ destruct x; symmetry; assumption
    | destruct y; contradiction].
Defined.

(** ** Tactics for the HILECOP Design Store *)

Ltac subst_place_design1 H :=
  match type of H with
  | MapsTo Petri.place_entid ?d hdstore =>
    specialize (is_place_design H); intros; subst d
  end.

Ltac subst_place_design :=
  match goal with
  | [ H: MapsTo Petri.place_entid ?d hdstore |- _ ] =>
    subst_place_design1 H
  end.

Ltac subst_transition_design1 H :=
  match type of H with
  | MapsTo Petri.transition_entid ?d hdstore =>
    specialize (is_transition_design H); intros; subst d
  end.

Ltac subst_transition_design :=
  match goal with
  | [ H: MapsTo Petri.transition_entid ?d hdstore |- _ ] =>
    subst_transition_design1 H
  end.
