(** * Facts about Evaluation of Sequantial Statements *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.NatMapTactics.
Require Import common.NatSet.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.SSEvaluation.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.ExpressionEvaluation.

Require Import hvhdl.SemanticalDomainsFacts.

Open Scope abss_scope.

Lemma vseq_inv_compstore :
  forall {Δ σ Λ flag stmt σ' Λ' id__c σ__c},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    MapsTo id__c σ__c (compstore σ) ->
    MapsTo id__c σ__c (compstore σ').
Proof. induction 1; try subst; auto. Qed.

Lemma vseq_inv_compstore_2 :
  forall {Δ σ Λ flag stmt σ' Λ' id__c σ__c},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    MapsTo id__c σ__c (compstore σ') ->
    MapsTo id__c σ__c (compstore σ).
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

Lemma vseq_inv_well_typed_values_in_sstore : 
  forall {Δ σ Λ flag stmt σ' Λ'},
    vseq Δ σ Λ flag stmt σ' Λ' ->
    (forall {id t v},
        (MapsTo id (Declared t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
        MapsTo id v (sigstore σ) ->
        is_of_type v t) ->
    forall {id t v},
      (MapsTo id (Declared t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
      MapsTo id v (sigstore σ') ->
      is_of_type v t.
Proof.
  induction 1; try (solve [auto]).
  (* CASE eventful signal assignment *)
  - intros WT id0 t1 v MapsTo_Δ; subst σ'; cbn.
    destruct (Nat.eq_dec id id0) as [eq_ | neq_ ].
    (* CASE [id0 = id] *)
    rewrite eq_ in *.
    assert (eq_t : t0 = t1).
    { match goal with
      | [ H1: MapsTo _ _ _ \/ MapsTo _ _ _ |- _ ] =>
        inversion_clear H1;
          [ inversion_clear MapsTo_Δ; [ mapsto_fun_inj_val | mapsto_discriminate ]
          | inversion_clear MapsTo_Δ as [ | MapsTo_or];
            [ mapsto_discriminate
            | inversion_clear MapsTo_or;
              [ mapsto_discriminate | mapsto_fun_inj_val ] ] ]
      end. }
    intros MapsTo_sstore.
    erewrite @MapsTo_add_eqv with (e := v) (e' := newv); eauto.
    rewrite <- eq_t; assumption.
    (* CASE [id0 ≠ id] *)
    intro; eapply WT; eauto with mapsto.
  (* CASE eventful idx signal assignment *)
  - intros WT id0 t1 v MapsTo_Δ; subst σ'; cbn.
    destruct (Nat.eq_dec id id0) as [eq_ | neq_ ].
    (* CASE [id0 = id] *)
    rewrite eq_ in *.
    assert (eq_t : (Tarray t0 l u) = t1).
    { match goal with
      | [ H1: MapsTo _ _ _ \/ MapsTo _ _ _ |- _ ] =>
        inversion_clear H1;
          [ inversion_clear MapsTo_Δ; [ mapsto_fun_inj_val | mapsto_discriminate ]
          | inversion_clear MapsTo_Δ as [ | MapsTo_or];
            [ mapsto_discriminate
            | inversion_clear MapsTo_or;
              [ mapsto_discriminate | mapsto_fun_inj_val ] ] ]
      end. }
    intros MapsTo_sstore.
    erewrite @MapsTo_add_eqv
      with (e := v) (e' := (Varr (set_at newv idx curraofv idx_in_bounds))); eauto.
    rewrite <- eq_t.
    eapply is_of_type_inv_set_at; eauto.      
    (* CASE [id0 ≠ id] *)
    intro; eapply WT; eauto with mapsto.
  (* CASE for loop *)
  - intros WT; eapply IHvseq2; eauto.
  (* CASE seq *)
  - intros WT; eapply IHvseq2; eauto.
Qed.
