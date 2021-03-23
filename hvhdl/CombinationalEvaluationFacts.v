(** ** Facts about Evaluation of Combinational Concurrent Statement *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.NatMapTactics.
Require Import common.InAndNoDup.
Require Import common.NatSet.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.Place.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.SSEvaluation.
Require Import hvhdl.SSEvaluationFacts.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.PortMapEvaluationFacts.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.AbstractSyntaxTactics.
Require Import hvhdl.WellDefinedDesignFacts.
Require Import hvhdl.WellDefinedDesignTactics.
Require Import hvhdl.EnvironmentFacts.
Require Import hvhdl.EnvironmentTactics.

(** ** Facts about [vcomb] *)

Lemma vcomb_maps_compstore_id :
  forall {D__s Δ σ behavior σ' id__c σ__c},
    vcomb D__s Δ σ behavior σ' ->
    MapsTo id__c σ__c (compstore σ) ->
    exists σ__c', MapsTo id__c σ__c' (compstore σ').
Proof.
  induction 1; try (simpl; exists σ__c; assumption).
  
  (* CASE process evaluation, no events in sl *)
  - exists σ__c; eapply vseq_inv_compstore; simpl; eauto.
    
  (* CASE comp evaluation with events.
       2 subcases, [id__c = compid] or [id__c ≠ compid] *)
  - simpl; destruct (Nat.eq_dec compid id__c).
    + exists σ__c''; rewrite e; apply NatMap.add_1; auto.
    + exists σ__c; apply NatMap.add_2; auto.
      eapply mapop_inv_compstore; eauto.

  (* CASE comp evaluation with no events. *)
  - exists σ__c; eapply mapop_inv_compstore; eauto.

  (* CASE par *)
  - unfold IsMergedDState in H2; apply proj2, proj1 in H2.
    unfold EqualDom in H2; rewrite <- (H2 id__c); exists σ__c; assumption.
Qed.

Lemma vcomb_par_comm :
  forall {D__s Δ σ cstmt cstmt' σ'},
    vcomb D__s Δ σ (cstmt // cstmt') σ' <->
    vcomb D__s Δ σ (cstmt' // cstmt) σ'.
Proof.
  split; inversion_clear 1.
  all :
    eapply @VCombPar; eauto;
    [ transitivity (inter (events σ'0) (events σ'')); auto with set
    | erewrite IsMergedDState_comm; auto ].
Qed.

Lemma vcomb_par_assoc :
  forall {D__s Δ σ cstmt cstmt' cstmt'' σ'},
    vcomb D__s Δ σ (cstmt // cstmt' // cstmt'') σ' <->
    vcomb D__s Δ σ ((cstmt // cstmt') // cstmt'')  σ'.
Proof.
  split.
  (* CASE A *)
  - inversion_clear 1;
      match goal with
      | [ H: vcomb _ _ _ (_ // _) _ |- _ ] => inversion_clear H
      end;
      rename σ'0 into σ0, σ'' into σ1, σ'1 into σ2, σ''0 into σ3.

    assert (Equal (inter (events σ0) (events σ2)) {[]}).
    {
      do 2 decompose_IMDS.
      assert (Equal_empty : Equal (inter (events σ0) (events σ2 U events σ3)) {[]})
        by (match goal with
            | [ H: Equal _ ?u |- Equal (_ _ ?u) _ ] => rewrite <- H
            end; assumption).
      apply empty_is_empty_1.
      rewrite inter_sym, union_inter_1, inter_sym in Equal_empty.
      eapply proj1; eapply @union_empty with (s := (inter (events σ0) (events σ2))); eauto.
    }
    destruct (@IsMergedDState_ex σ σ0 σ2) as (σ4, IsMergedDState_σ4);
      (solve [do 2 decompose_IMDS; auto] || auto).
    eapply @VCombPar with (σ' := σ4) (σ'' := σ3); eauto with hvhdl.
    
    (* [events σ4 ∩ events σ3 = ∅] *)
    + do 3 decompose_IMDS.
      match goal with
      | [ H: Equal ?ev _ |- Equal (_ ?ev _) _] =>
        rewrite H; rewrite union_inter_1
      end.      
      match goal with
      | [ H: Equal ?i {[]} |- Equal (_ U ?i) {[]} ] =>
        rewrite H; apply empty_union_1
      end.
      assert (Equal_empty : Equal (inter (events σ0) ((events σ2) U (events σ3))) {[]})
        by (match goal with
            | [ H: Equal _ ?A  |- Equal (inter _ ?A) _ ] =>
              rewrite <- H
            end; assumption).
      rewrite inter_sym, union_inter_1, union_sym, inter_sym in Equal_empty.
      eapply proj1; eapply union_empty; eauto.
      
    (* Associativity of IsMErgeddstate relation *)
    + eapply IsMergedDState_assoc_1; eauto.

  (* CASE B *)
  - inversion_clear 1;
      match goal with
      | [ H: vcomb _ _ _ (_ // _) _ |- _ ] => inversion_clear H
      end.
    rename σ'1 into σ0, σ''0 into σ1, σ'' into σ2, σ'0 into σ3.
    assert (Equal (inter (events σ1) (events σ2)) {[]}).
    {
      do 2 decompose_IMDS.
      assert (Equal_empty : Equal (inter (events σ0 U events σ1) (events σ2) ) {[]})
        by (match goal with
            | [ H: Equal _ ?u |- Equal (_ ?u _) _ ] => rewrite <- H
            end; assumption).
      apply empty_is_empty_1.
      rewrite union_inter_1 in Equal_empty.
      eapply proj2; eapply @union_empty; eauto.
    }
    destruct (@IsMergedDState_ex σ σ1 σ2) as (σ4, IsMergedDState_σ4);
      (solve [do 2 decompose_IMDS; auto] || auto).
    eapply @VCombPar with (σ' := σ0) (σ'' := σ4); eauto with hvhdl.
    
    (* [events σ0 ∩ events σ4 = ∅] *)
    + do 3 decompose_IMDS.
      match goal with
      | [ H: Equal ?ev _ |- Equal (_ _ ?ev) _ ] =>
        rewrite H; rewrite inter_sym; rewrite union_inter_1
      end.
      rewrite inter_sym, union_sym.
      match goal with
      | [ H: Equal ?i {[]} |- Equal (_ U ?i) {[]} ] =>
        rewrite H; apply empty_union_1
      end.
      rewrite inter_sym.
      assert (Equal_empty : Equal (inter (events σ0 U events σ1) (events σ2)) {[]})
        by (match goal with
            | [ H: Equal _ ?A  |- Equal (_ ?A  _) _ ] =>
              rewrite <- H
            end; assumption).
      rewrite union_inter_1 in Equal_empty.
      eapply proj1; eapply union_empty; eauto.

    (* Associativity of IsMErgeddstate relation *)
    + eapply IsMergedDState_assoc_2; eauto.
Qed.

Lemma vcomb_not_in_events_if_not_assigned :
  forall {D__s Δ σ cstmt σ' id},
    vcomb D__s Δ σ cstmt σ' ->
    ~CompOf Δ id ->
    ~AssignedInCs id cstmt ->
    ~NatSet.In id (events σ').
Proof.
  induction 1; (try (solve [simpl; auto with set])).
  
  (* CASE eventful process *)
  - simpl; intros; eapply vseq_not_in_events_if_not_assigned; eauto with set.

  (* CASE eventful component *)
  - simpl; intros.
    erewrite add_spec; inversion_clear 1;
      [ subst; match goal with
               | [ H: ~CompOf _ _ |- _ ] =>
                 apply H; exists Δ__c; auto
               end
      | eapply mapop_not_in_events_if_not_assigned; eauto with set].

  (* CASE eventless component *)
  - simpl; intros;
      eapply mapop_not_in_events_if_not_assigned; eauto with set.

  (* CASE || *)
  - simpl; intros.
    decompose_IMDS; match goal with | [ H: Equal _ _ |- _ ] => rewrite H end.
    apply not_in_union; [ apply IHvcomb1; auto | apply IHvcomb2; auto ].
Qed.

Lemma vcomb_inv_cstate :
  forall {D__s Δ σ behavior σ' id__c σ__c},
    vcomb D__s Δ σ behavior σ' ->
    MapsTo id__c σ__c (compstore σ) ->
    ~NatSet.In id__c (events σ') ->
    MapsTo id__c σ__c (compstore σ').
Proof.
  induction 1; auto.

  (* CASE eventful process *)
  - intros; eapply vseq_inv_compstore; eauto.

  (* CASE eventful component *)
  - simpl; intros.
    erewrite NatMap.add_neq_mapsto_iff; eauto.
    eapply mapop_inv_compstore; eauto.
    intro; subst;
    match goal with
    | [ H: ~NatSet.In _ _ |- _ ] => apply H; auto with set
    end.

  (* CASE eventless component *)
  - intros; eapply mapop_inv_compstore; eauto.

  (* CASE || *)
  - intros;
      decompose_IMDS;
      match goal with
      | [ H: _ -> _ -> ~NatSet.In _ _ -> _ <-> _, H': Equal _ _ |- _ ] =>
        erewrite <- H; auto; (assumption || (rewrite <- H'; assumption))
      end.
Qed.

Lemma vcomb_compid_not_in_events :
  forall {D__s Δ σ cstmt σ'},
    vcomb D__s Δ σ cstmt σ' ->
    forall {id__c Δ__c compids},
    AreCsCompIds cstmt compids ->
    MapsTo id__c (Component Δ__c) Δ ->
    ~List.In id__c compids ->
    ~NatSet.In id__c (events σ').
Proof.
  induction 1; auto with set.

  (* CASE eventful process *)
  - intros; eapply vseq_not_in_events_if_not_sig; simpl.
    1, 2: eauto with set.
    1, 2: destruct 1; mapsto_discriminate.

  (* CASE eventful component *)
  - simpl; inversion_clear 1; intros.
    rewrite add_spec; inversion_clear 1.
    match goal with
    | [ H: ~List.In _ _ |- _ ] =>
      apply H; firstorder
    end.
    eapply mapop_not_in_events_if_not_sig; eauto with set;
      destruct 1; mapsto_discriminate.
    
  (* CASE eventless component *)
  - intros; eapply mapop_not_in_events_if_not_sig; eauto with set;
    destruct 1; mapsto_discriminate.

  (* CASE || *)
  - destruct (AreCsCompIds_ex cstmt) as (compids1, AreCsCompIds_1);
      destruct (AreCsCompIds_ex cstmt') as (compids2, AreCsCompIds_2).
    do 4 intro;
      erewrite (AreCsCompIds_eq_app cstmt cstmt' compids1 compids2)
        with (compids'' := compids); eauto.
    rename H2 into IMDS; erw_IMDS_events_m IMDS; intros; apply not_in_union.
    eapply IHvcomb1; eauto; eapply proj1; eapply not_app_in; eauto.
    eapply IHvcomb2; eauto; eapply proj2; eapply not_app_in; eauto.
Qed.

Lemma vcomb_maps_sstore :
  forall {D__s Δ σ cstmt σ'},
    vcomb D__s Δ σ cstmt σ' ->
    forall {id v},
      MapsTo id v (sigstore σ) ->
      exists v', MapsTo id v' (sigstore σ').
Proof.
  induction 1.
  
  (* CASE idle process *)
  - intros; exists v; assumption.
    
  (* CASE active process *)
  - eapply @vseq_maps_sstore with (σ := NoEvDState σ); eauto.
    
  (* CASE comp evaluation with events. *)
  - cbn; eapply @mapop_maps_sstore with (σ := NoEvDState σ); eauto.

  (* CASE comp evaluation with no events. *)
  - cbn; eapply @mapop_maps_sstore with (σ := NoEvDState σ); eauto.

  (* CASE null *)
  - intros; exists v; assumption.

  (* CASE par *)
  - rename H2 into IMDS; intros.
    apply proj1 in IMDS; unfold EqualDom in IMDS.
    rewrite <- (IMDS id); exists v; assumption.        
Qed.

Lemma vcomb_compid_in_events_comp_in_cs :
  forall {D__s Δ σ cstmt σ'},
    vcomb D__s Δ σ cstmt σ' ->
    forall {id__c},
      CompOf Δ id__c ->
      NatSet.In id__c (events σ') ->
      exists id__e gm ipm opm,
        InCs (cs_comp id__c id__e gm ipm opm) cstmt.
Proof.
  induction 1.

  (* CASE idle process *)
  - cbn; inversion 2.

  (* CASE active process *)
  - intros id__c CompOf_; intros; exfalso.
    eapply vseq_not_in_events_if_not_sig; eauto.
    cbn; eauto with set.
    destruct 1; destruct CompOf_; mapsto_discriminate.
    destruct 1; destruct CompOf_; mapsto_discriminate.
    
  (* CASE eventful comp *)
  - cbn; intros id__c CompOf_.
    rewrite add_iff; inversion 1.
    subst compid; exists entid, gmap, ipmap, opmap; reflexivity.
    exfalso.
    eapply mapop_not_in_events_if_not_sig; eauto.
    cbn; eauto with set.
    destruct 1; destruct CompOf_; mapsto_discriminate.
    destruct 1; destruct CompOf_; mapsto_discriminate.

  (* CASE eventless comp *)
  - cbn; intros id__c CompOf_; intros.
    exfalso.
    eapply mapop_not_in_events_if_not_sig; eauto.
    cbn; eauto with set.
    destruct 1; destruct CompOf_; mapsto_discriminate.
    destruct 1; destruct CompOf_; mapsto_discriminate.

  (* CASE cs_null *)
  - cbn; inversion 2.

  (* CASE || *)
  - rename H2 into IMDS; intros id__c CompOf_.
    erw_IMDS_events_m IMDS.
    rewrite union_spec; inversion 1.
    edestruct IHvcomb1 as (id__e, (g, (i, (o, InCs_)))); eauto.
    exists id__e, g, i, o; cbn; left; assumption.
    edestruct IHvcomb2 as (id__e, (g, (i, (o, InCs_)))); eauto.
    exists id__e, g, i, o; cbn; right; assumption.
Qed.

Lemma vcomb_is_compof_if_in_cs :
  forall {D__s Δ σ cstmt σ'},
    vcomb D__s Δ σ cstmt σ' ->
    forall {id__c id__e gm ipm opm},
      InCs (cs_comp id__c id__e gm ipm opm) cstmt ->
      CompOf Δ id__c.
Proof.
  induction 1; try (solve [inversion 1]).

  (* CASE eventful comp *)
  - inversion 1; subst; unfold CompOf; eauto.

  (* CASE eventless comp *)
  - inversion 1; subst; unfold CompOf; eauto.

  (* CASE || *)
  - inversion 1; eauto.
Qed.

Lemma vcomb_maps_sstore_of_comp :
  forall {D__s Δ σ cstmt σ'},
    vcomb D__s Δ σ cstmt σ' ->
    forall {id__c id__e gm ipm opm σ__c σ'__c id v},
      InCs (cs_comp id__c id__e gm ipm opm) cstmt ->
      MapsTo id__c σ__c (compstore σ) ->
      MapsTo id v (sigstore σ__c) ->
      MapsTo id__c σ'__c (compstore σ') ->
      exists v', MapsTo id v' (sigstore σ'__c).
Proof.
  induction 1; try (solve [inversion 1]).
  (* CASE comp evaluation with events.*)
  - inversion_clear 1; cbn; intros.
    erewrite @MapsTo_add_eqv with (e := σ'__c) (e' := σ__c''); eauto.
    edestruct @mapip_maps_sstore with (Δ := Δ); eauto.
    erewrite <- MapsTo_fun with (e := σ__c0) (e' := σ__c); eauto.
    eapply vcomb_maps_sstore; eauto.
  (* CASE comp evaluation with no events.*)
  - inversion_clear 1; cbn; intros.
    exists v.
    assert (MapsTo compid σ__c (compstore σ'))
      by (eapply mapop_inv_compstore; eauto).      
    erewrite <- MapsTo_fun with (e := σ__c) (e' := σ'__c); eauto.
    erewrite <- MapsTo_fun with (e := σ__c0) (e' := σ__c); eauto.
  (* CASE || *)
  - rename H2 into IMDS; intros until σ__c; intros σ__mc.

    (* 2 CASES: [comp ∈ cs] or [comp ∈ cs'] *)
    inversion_clear 1; intros.

    (* CASE [comp ∈ cs] *)
    + (* 2 CASES: [id__c ∈ events σ'] or [id__c ∉ events σ'] *)
      destruct (In_dec id__c (events σ')) as [ In_ev' | nIn_ev' ].
      (* CASE [id__c ∈ events σ'] *)
      -- eapply IHvcomb1; eauto.
         erw_IMDS_cstore_1 IMDS; eauto.

      (* CASE [id__c ∉ events σ'] *)
      -- (* 2 CASES: [id__c ∈ events σ''] or [id__c ∉ events σ''] *)
        destruct (In_dec id__c (events σ'')) as [ In_ev'' | nIn_ev'' ].

        (* CASE [id__c ∈ events σ''] *)
        ++ edestruct @vcomb_compid_in_events_comp_in_cs with (D__s := D__s) (id__c := id__c)
            as (id__e', (g, (i, (o, InCs_)))); eauto.
           eapply @vcomb_is_compof_if_in_cs with (cstmt := cstmt); eauto.
           eapply IHvcomb2; eauto.
           erw_IMDS_cstore_2 IMDS; eauto.

        (* CASE [id__c ∉ events σ''] *)
        ++ assert (eq_cstate: σ__c = σ__mc).
           { eapply MapsTo_fun; eauto.
             erw_IMDS_cstore_m IMDS; eauto.
             eapply not_in_union; eauto. }
           rewrite <- eq_cstate; exists v; assumption.

    (* CASE [comp ∈ cs'] *)
    + (* 2 CASES: [id__c ∈ events σ''] or [id__c ∉ events σ''] *)
      destruct (In_dec id__c (events σ'')) as [ In_ev'' | nIn_ev'' ].
      (* CASE [id__c ∈ events σ''] *)
      -- eapply IHvcomb2; eauto.
         erw_IMDS_cstore_2 IMDS; eauto.

      (* CASE [id__c ∉ events σ''] *)
      -- (* 2 CASES: [id__c ∈ events σ'] or [id__c ∉ events σ'] *)
        destruct (In_dec id__c (events σ')) as [ In_ev' | nIn_ev' ].

        (* CASE [id__c ∈ events σ'] *)
        ++ edestruct @vcomb_compid_in_events_comp_in_cs
          with (D__s := D__s) (id__c := id__c) (cstmt := cstmt)
            as (id__e', (g, (i, (o, InCs_)))); eauto.
           eapply @vcomb_is_compof_if_in_cs with (cstmt := cstmt'); eauto.
           eapply IHvcomb1; eauto.
           erw_IMDS_cstore_1 IMDS; eauto.

        (* CASE [id__c ∉ events σ'] *)
        ++ assert (eq_cstate: σ__c = σ__mc).
           { eapply MapsTo_fun; eauto.
             erw_IMDS_cstore_m IMDS; eauto.
             eapply not_in_union; eauto. }
           rewrite <- eq_cstate; exists v; assumption.
Qed.

