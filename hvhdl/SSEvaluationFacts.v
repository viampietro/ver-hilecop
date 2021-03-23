(** * Facts about Evaluation of Sequantial Statements *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.NatSet.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.SSEvaluation.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.ExpressionEvaluation.

Open Scope abss_scope.

Lemma vseq_inv_compstore :
  forall {Δ σ Λ flag stmt σ' Λ' id__c σ__c},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    MapsTo id__c σ__c (compstore σ) ->
    MapsTo id__c σ__c (compstore σ').
Proof. induction 1; try subst; auto. Qed.

Lemma vseq_maps_sstore :
  forall {Δ σ Λ flag stmt σ' Λ'},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    forall {id v},
      MapsTo id v (sigstore σ) ->
      exists v', MapsTo id v' (sigstore σ').
Proof.
  induction 1; try (solve [do 2 intro; exists v; assumption]); auto.
  1, 2:
    subst σ'; cbn; intros id0 v MapsTo_;
    destruct (Nat.eq_dec id id0) as [eq_ | neq_ ];
    [match goal with
     | |- exists v', MapsTo ?id0 v' (NatMap.add ?id ?v'' _) =>
       subst id; exists v''; eauto with mapsto
     end
    | exists v; eauto with mapsto ].
  all: intros id0 v MapsTo_; edestruct IHvseq1; eauto.
Qed.

Lemma vseq_not_in_events_if_not_assigned :
  forall {Δ σ Λ flag stmt σ' Λ' id},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    ~NatSet.In id (events σ) ->
    ~AssignedInSS id stmt ->
    ~NatSet.In id (events σ').
Proof.
  induction 1; subst; simpl; (auto || (try (rewrite add_spec; firstorder))).
  intros; apply IHvseq2; auto.
Qed.

Lemma vseq_not_in_events_if_not_sig :
  forall {Δ σ Λ flag stmt σ' Λ' id},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    ~NatSet.In id (events σ) ->
    ~OutputOf Δ id  ->
    ~DeclaredOf Δ id ->
    ~NatSet.In id (events σ').
Proof.
  induction 1; auto; subst; simpl; intros.
  all :
    destruct (Nat.eq_dec id id0) as [eq | neq]; [
    subst;
    match goal with
    | [ Hor: _ _ (_ ?t) _ \/ _, Hndecl: ~DeclaredOf _ _, Hnout: ~OutputOf _ _ |- _ ] =>
      inversion Hor; [ exfalso; apply Hndecl; exists t; auto |
                       exfalso; apply Hnout; exists t; auto ]
    end
  |
  rewrite add_spec; destruct 1; [contradiction | auto]
  ].
Qed.
     
Lemma vseq_eq_state_if_no_events :
  forall {Δ σ Λ flag stmt σ' Λ'},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    Equal (events σ') {[]} ->
    σ = σ'.
Proof.
  induction 1; auto; subst; simpl; intros.
  3, 4: transitivity σ'; [rewrite IHvseq1; auto; rewrite IHvseq2; auto | rewrite IHvseq2; auto].
  1, 2: contrad_add_empty.
Qed.

Lemma vseq_inv_not_in_events :
  forall {Δ σ Λ flag stmt σ' Λ'},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    forall {id},
      ~NatSet.In id (events σ') ->
      ~NatSet.In id (events σ).
Proof.
  induction 1; try (solve [intro; auto]);
    subst σ'; cbn; intros id0; eauto with set.
Qed.
