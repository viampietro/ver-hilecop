Require Import MSets.

(** Defines finite sets of natural. *)

Module NatSet := MSetWeakList.Make (Nat_as_OT).
Include NatSet.

Module NatSetFacts := Facts NatSet.
Module NatSetProps := Properties NatSet.

Declare Scope natset_scope.

Infix "U" := union (at level 60, right associativity).
Infix "U+" := add (at level 60, right associativity).
Notation "{[ ]}" := empty (format "{[ ]}") : natset_scope.
Notation "{[ x , y , .. , z ]}" := (add x (add y .. (add z empty) ..)) : natset_scope.
Notation "{[ x ]}" := (add x empty) (at level 0) : natset_scope.

(** ** Extra Facts on [NatSet] *)

Open Scope natset_scope.

Lemma nIn_nIn_Union :
  forall {x s s'}, ~NatSet.In x s -> ~NatSet.In x s' -> ~NatSet.In x (s U s').
Proof.
  intros *; intros nIn_s nIn_s' In_u.
  destruct (NatSetFacts.union_1 In_u); [apply nIn_s; assumption | apply nIn_s'; assumption ].
Qed.

Lemma union_empty :
  forall {s s' : NatSet.t},
    Equal (s U s') empty -> Empty s /\ Empty s'.
Proof.
  split;
    [ intros a In_empty;
      eapply NatSetFacts.union_2 in In_empty;
      erewrite H in In_empty;
      erewrite <- NatSetFacts.empty_iff; eauto
    | intros a In_empty;
      eapply NatSetFacts.union_3 in In_empty;
      erewrite H in In_empty;
      erewrite <- NatSetFacts.empty_iff; eauto ].
Qed.

Lemma union_empty_l :
  forall {s s' : NatSet.t},
    Equal (s U s') empty -> Equal s empty.
Proof.
  intros.
  eapply NatSetProps.empty_is_empty_1.
  eapply (union_empty H).
Qed.

Lemma union_empty_r :
  forall {s s' : NatSet.t},
    Equal (s U s') empty -> Equal s' empty.
Proof.
  intros.
  eapply NatSetProps.empty_is_empty_1.
  eapply (union_empty H).
Qed.

Lemma not_in_union_2 :
  forall [s s' : t] [x : elt], ~ In x (s U s') -> ~ In x s /\ ~ In x s'.
Proof.
  intros; split; intro.
  apply H; eapply NatSetFacts.union_2; eauto.
  apply H; eapply NatSetFacts.union_3; eauto.
Qed.

Lemma inter_empty_1 :
  forall {s s' e},
    Equal (inter s s') {[]} ->
    In e s ->
    ~In e s'.
Proof.
  intros; intro.
  assert (In e (inter s s')) by (eapply NatSetFacts.inter_3; eauto).
  match goal with
  | [ H: Equal ?I _, H': NatSet.In _ ?I |- _ ] =>
    rewrite H in H'; inversion H'
  end.
Qed.

Lemma inter_empty_2 :
  forall {s s' e},
    Equal (inter s s') {[]} ->
    In e s' ->
    ~In e s.
Proof.
  intros; intro.
  assert (In e (inter s s')) by (eapply NatSetFacts.inter_3; eauto).
  match goal with
  | [ H: Equal ?I _, H': NatSet.In _ ?I |- _ ] =>
    rewrite H in H'; inversion H'
  end.
Qed.

Lemma add_empty_false :
  forall x s, NatSet.Equal (x U+ s) {[]} -> False.
Proof. unfold Equal.
       intros x s In_iff.
       rewrite <- (NatSetFacts.empty_iff x).
       rewrite <- In_iff; auto with set.
Qed.

(** ** Tactics for NatSet *)

Ltac contrad_add_empty :=
  match goal with
  | [ H: NatSet.Equal (_ U+ _) {[]} |- _ ] =>
    exfalso; eapply add_empty_false; eauto
  end.

Ltac contrad_not_in_add :=
  match goal with
  | [ H: ~NatSet.In ?x (?x U+ _) |- _ ] =>
    exfalso; apply H; auto with set
  end.
  
Export NatSet NatSetFacts NatSetProps.

