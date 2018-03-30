(* $Id *)

(* Propositional Logic *)

Parameters A B C : Prop.  (* Variable, Parameter, Axiom, Hypothesis *)

Lemma prop1 : A -> B -> A.
Proof.
  intros. assumption.
  (* intros H H0. exact H0. *)
Qed.

Lemma prop2 : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  intros H H0 H1.
  apply H.
  - assumption.
  - apply H0. assumption.
Qed.

Lemma prop3 : A /\ B -> B.
Proof.
  intro H.
  elim H. intros H0 H1. assumption. (* exact H0. *)
Qed.

Lemma prop4 : B -> A \/ B.
Proof.
  intro.
  right. assumption.
Qed.

Lemma prop5 : (A \/ B) -> (A -> C) -> (B -> C) -> C.
Proof.
  intros H H0 H1.
  elim H.
  - (* A -> C *) assumption.
  - (* B -> C *) assumption. 
Qed.

Lemma prop6 : A -> False -> ~A.
Proof.
  intros H H0.
  (* cut False. 
     - intro Hn; elim Hn; clear Hn. 
     (* elimtype False. *)
     - assumption.
   *)
  elim H0.  
Qed.

Lemma prop7 : False -> A.
Proof.
  intro H.
  elim H.  (* elimtype False. assumption *)
Qed.

Lemma prop8 : (A <-> B) -> (A -> B).
Proof.
  intro Ha2b.
  elim Ha2b. do 2 intro.
  assumption.
Qed.

Lemma prop9 : (A <-> B) -> (B -> A).
Proof.
  intro.
  elim H; do 2 intro.
  assumption.
Qed.

Lemma prop10 : (A -> B) -> (B -> A) -> (A <-> B).
Proof.
  intros.
  split; assumption.
Qed.

(****************************************************)
(* First Order Logic *)
Section FOL.
  Variable E : Set.
  Variable P Q : E -> Prop.   (* 2 unary predicates *)  
  
  Lemma fol1 : forall x : E,
      (P x) -> exists y : E, (P y) \/ (Q y).
  Proof.
    intros. exists x. left. assumption.
  Qed.
  
  Lemma fol2 : (exists x : E, (P x) \/ (Q x)) ->
               (exists x : E, (P x)) \/ (exists x : E, (Q x)).
  Proof.
    intro.
    elim H. intros.
    elim H0; intro.
    left.
    exists x.
    assumption.
    right.
    exists x.
    assumption.
  Qed.
  
  Lemma fol3 : (forall x : E, (P x)) /\ (forall x : E, (Q x)) ->
               forall x : E, (P x) /\ (Q x).
  Proof.
    intros.
    elim H; intros.
    split.
    apply H0.
    apply H1.
  Qed.
  
  Lemma fol4 : (forall x : E, (P x) /\ (Q x)) ->
               (forall x : E, (P x)) /\ (forall x : E, (Q x)).
  Proof.
    intro.
    split; intro; elim (H x); intros; assumption.
  Qed.
  
  Lemma fol5 : (forall x : E, ~(P x)) -> ~(exists x : E, (P x)).
  Proof.
    intros H H0.
    elim H0; intros.
    apply (H x).
    assumption.
  Qed.
  
  Require Export Classical. Print classic. Check NNPP.
  
  Lemma fol6 : ~(forall x : E, (P x)) -> exists x : E, ~(P x).
  Proof.
    intro.
    apply NNPP.
    intro.
    apply H.
    intro.
    apply NNPP.
    intro.
    apply H0.
    exists x.
    assumption.
  Qed.
End FOL.