(** ** Facts about Evaluation of Combinational Concurrent Statement *)

Require Import common.Coqlib.
Require Import common.NatSet.
Require Import common.NatMap.
Require Import common.InAndNoDup.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.Place.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.SSEvaluationFacts.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.PortMapEvaluationFacts.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.AbstractSyntaxTactics.
Require Import hvhdl.WellDefinedDesignTactics.

(** ** Facts about [vcomb] *)

Lemma vcomb_maps_compstore_id :
  forall {D__s Δ σ behavior σ' id__c σ__c},
    vcomb D__s Δ σ behavior σ' ->
    MapsTo id__c σ__c (compstore σ) ->
    exists σ__c', MapsTo id__c σ__c' (compstore σ').
Proof.
  induction 1; try (simpl; exists σ__c; assumption).
  
  (* CASE process evaluation, no events in sl *)
  - exists σ__c; eapply vseq_inv_compstore_id; simpl; eauto.
    
  (* CASE comp evaluation with events.
       2 subcases, [id__c = compid] or [id__c ≠ compid] *)
  - simpl; destruct (Nat.eq_dec compid id__c).
    + exists σ__c''; rewrite e; apply NatMap.add_1; auto.
    + exists σ__c; apply NatMap.add_2; auto.
      eapply mapop_inv_compstore_id; eauto.

  (* CASE comp evaluation with no events. *)
  - exists σ__c; eapply mapop_inv_compstore_id; eauto.

  (* CASE par *)
  - unfold IsMergedDState in H2; apply proj2, proj1 in H2.
    unfold EqualDom in H2; rewrite <- (H2 id__c); exists σ__c; assumption.
Qed.

Lemma nIn_nIn_Union :
  forall {x s s'}, ~NatSet.In x s -> ~NatSet.In x s' -> ~NatSet.In x (s U s').
Admitted.

Lemma in_cs_comp_in_compids :
  forall {cstmt compids id__c id__e gm ipm opm},
    AreCsCompIds cstmt compids ->
    InCs (cs_comp id__c id__e gm ipm opm) cstmt ->
    List.In id__c compids.
Admitted.

Lemma AreCsCompIds_app :
  forall cstmt cstmt' compids compids',
    AreCsCompIds cstmt compids ->
    AreCsCompIds cstmt' compids' ->
    AreCsCompIds (cstmt // cstmt') (compids ++ compids').
Admitted.

Lemma AreCsCompIds_ex : forall cstmt, exists compids, AreCsCompIds cstmt compids.
Admitted.

Lemma AreCsCompIds_determ :
  forall cstmt compids compids',
    AreCsCompIds cstmt compids ->
    AreCsCompIds cstmt compids' ->
    compids = compids'.
Admitted.

Lemma vcomb_inv_cstate :
  forall {D__s Δ σ behavior σ' id__c σ__c},
    vcomb D__s Δ σ behavior σ' ->
    MapsTo id__c σ__c (compstore σ) ->
    ~NatSet.In id__c (events σ') ->
    MapsTo id__c σ__c (compstore σ').
Admitted.

Lemma vcomb_compid_not_in_events_1 :
  forall {D__s Δ σ cstmt σ' id__c Δ__c compids},
    vcomb D__s Δ σ cstmt σ' ->
    MapsTo id__c (Component Δ__c) Δ ->
    AreCsCompIds cstmt compids ->
    ~List.In id__c compids ->
    ~NatSet.In id__c (events σ) ->
    ~NatSet.In id__c (events σ').
Admitted.

Lemma vcomb_compid_not_in_events_2 :
  forall {D__s Δ σ cstmt σ' id__c Δ__c},
    vcomb D__s Δ σ cstmt σ' ->
    MapsTo id__c (Component Δ__c) Δ ->
    ~NatSet.In id__c (events σ') ->
    ~NatSet.In id__c (events σ).
Admitted.

Definition CsHasUniqueCompIds (behavior : cs) (compids : list ident) : Prop :=
  AreCsCompIds behavior compids /\ List.NoDup compids.

Lemma vcomb_inv_s_marking :
  forall Δ σ behavior σ',
    vcomb hdstore Δ σ behavior σ' ->
    forall id__p gm ipm opm σ__p σ__p' v Δ__p compids,
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) behavior ->
      MapsTo id__p (Component Δ__p) Δ ->
      AreCsCompIds behavior compids -> 
      List.NoDup compids ->
      MapsTo id__p σ__p (compstore σ) ->
      MapsTo s_marking v (sigstore σ__p) ->
      MapsTo id__p σ__p' (compstore σ') ->
      MapsTo s_marking v (sigstore σ__p').
Proof.
  induction 1; inversion 1; intros.

  (* CASE component with events. *)
  - admit.

  (* CASE component with no events. *)
  - erewrite @MapsTo_fun with (e := σ__p') (e' := σ__p); eauto.
    eapply mapop_inv_compstore_id; eauto.    

  (* CASE in left of || *)
  - destruct (AreCsCompIds_ex cstmt) as (compids1, HAreCsCompIds1).
    destruct (AreCsCompIds_ex cstmt') as (compids2, HAreCsCompIds2).
    eapply IHvcomb1; eauto.

    (* Component ids are unique in [cstmt]. *)
    apply @proj1 with (B := List.NoDup compids2); apply nodup_app.
    erewrite AreCsCompIds_determ; eauto.
    apply AreCsCompIds_app; auto.

    (* 2 subcases: [id__p ∈ (events σ')] or [id__p ∉ (events σ')] *)
    destruct (InA_dec Nat.eq_dec id__p (NatSet.elements (events σ'))); rewrite <- elements_iff in *.

    (* [id__p ∈ (events σ')] *)
    + edestruct @vcomb_maps_compstore_id with (σ' := σ') as (σ__p0, MapsTo_σ__p0); eauto.
      erewrite @MapsTo_fun with (e := σ__p') (e' := σ__p0); eauto.
      apply proj2, proj2, proj2, proj2, proj2, proj1 in H2. 
      eapply H2; eauto.
      
    (* [id__p ∉ (events σ')] *)
    + eapply vcomb_inv_cstate; eauto.
      erewrite @MapsTo_fun with (e := σ__p') (e' := σ__p); eauto.
      do 7 (apply proj2 in H2); apply proj1 in H2; eapply H2; eauto.
      eapply nIn_nIn_Union; eauto.
      (* Prove [id__p ∉ (events σ'')] *)
      eapply vcomb_compid_not_in_events_1; eauto.
      -- apply nodup_app_not_in with (l := compids1).
         { erewrite AreCsCompIds_determ; eauto.
           apply AreCsCompIds_app; auto. }
         { eapply in_cs_comp_in_compids; eauto. }
      -- eapply @vcomb_compid_not_in_events_2 with (σ' := σ'); eauto.
      
  (* CASE in right of || *)
  - destruct (AreCsCompIds_ex cstmt) as (compids1, HAreCsCompIds1).
    destruct (AreCsCompIds_ex cstmt') as (compids2, HAreCsCompIds2).
    eapply IHvcomb2; eauto.

    (* Component ids are unique in [cstmt]. *)
    apply @proj2 with (A := List.NoDup compids1); apply nodup_app.
    erewrite AreCsCompIds_determ; eauto.
    apply AreCsCompIds_app; auto.

    (* 2 subcases: [id__p ∈ (events σ'')] or [id__p ∉ (events σ'')] *)
    destruct (InA_dec Nat.eq_dec id__p (NatSet.elements (events σ''))); rewrite <- elements_iff in *.

    (* [id__p ∈ (events σ'')] *)
    + edestruct @vcomb_maps_compstore_id with (σ' := σ'') as (σ__p0, MapsTo_σ__p0); eauto.
      erewrite @MapsTo_fun with (e := σ__p') (e' := σ__p0); eauto.
      apply proj2, proj2, proj2, proj2, proj2, proj2, proj1 in H2. 
      eapply H2; eauto.
      
    (* [id__p ∉ (events σ')] *)
    + eapply vcomb_inv_cstate; eauto.
      erewrite @MapsTo_fun with (e := σ__p') (e' := σ__p); eauto.
      do 7 (apply proj2 in H2); apply proj1 in H2; eapply H2; eauto.
      eapply nIn_nIn_Union; eauto.
      (* Prove [id__p ∉ (events σ')] *)
      eapply vcomb_compid_not_in_events_1; eauto.
      -- eapply nodup_app_not_in with (l := compids2).
         { eapply NoDup_app_comm.
           erewrite AreCsCompIds_determ; eauto.
           apply AreCsCompIds_app; auto. }
         { eapply in_cs_comp_in_compids; eauto. }
      -- eapply @vcomb_compid_not_in_events_2 with (σ' := σ''); eauto.
Admitted.



