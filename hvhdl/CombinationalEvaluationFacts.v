(** ** Facts about Evaluation of Combinational Concurrent Statement *)

Require Import common.Coqlib.
Require Import common.NatSet.
Require Import common.NatMap.

Require Import hvhdl.Environment.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.Place.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.SSEvaluationFacts.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.PortMapEvaluationFacts.

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
    + exists σ__c''; rewrite e; apply add_1; auto.
    + exists σ__c; apply add_2; auto.
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

Lemma vcomb_compid_not_in_events :
  forall {D__s Δ σ behavior σ' id__c σ__c},
    vcomb D__s Δ σ behavior σ' ->
    MapsTo id__c σ__c (compstore σ) ->
    ~NatSet.In id__c (events σ') ->
    MapsTo id__c σ__c (compstore σ').
Admitted.

Lemma vcomb_inv_s_marking :
  forall Δ σ behavior σ',
    vcomb hdstore Δ σ behavior σ' ->
    forall id__p gm ipm opm σ__p σ__p' v,
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) behavior ->
      MapsTo id__p σ__p (compstore σ) ->
      MapsTo s_marking v (sigstore σ__p) ->
      MapsTo id__p σ__p' (compstore σ') ->
      MapsTo s_marking v (sigstore σ__p').
Proof.
  induction 1; inversion 1; intros.

  (* CASE component with events. *)
  - admit.

  (* CASE component with no events. *)
  - specialize (mapop_inv_compstore_id H1 H7) as MapsTo_σ__p.
    erewrite @MapsTo_fun with (e := σ__p') (e' := σ__p); eauto.

  (* CASE in left of || *)
  - eapply IHvcomb1; eauto.    
    
    (* 2 subcases: [id__p ∈ (events σ')] or [id__p ∈ (events σ')] *)
    destruct (InA_dec Nat.eq_dec id__p (NatSet.elements (events σ'))) as [In_σ'_id__p | nIn_σ'_id__p ];
      [ rewrite <- elements_iff in In_σ'_id__p | rewrite <- elements_iff in nIn_σ'_id__p ].

    (* [id__p ∈ (events σ')] *)
    + apply proj2, proj2, proj2, proj2, proj2, proj1 in H2.
      destruct (vcomb_maps_compstore_id H H5) as (σ__p0, MapsTo_σ__p0).
      specialize (H2 id__p σ__p0 In_σ'_id__p MapsTo_σ__p0) as MapsTo_σp0_m.
      erewrite @MapsTo_fun with (e := σ__p') (e' := σ__p0); eauto.

    (* [id__p ∉ (events σ')], then [σ(id__p) = σ'(id__p)]
       2 subcases: [id__p ∈ (events σ'')] or [id__p ∉ (events σ'')] *)
    + destruct (InA_dec Nat.eq_dec id__p (NatSet.elements (events σ''))) as [In_σ''_id__p | nIn_σ''_id__p ];
        [ rewrite <- elements_iff in In_σ''_id__p | rewrite <- elements_iff in nIn_σ''_id__p ].

      (* [id__p ∈ (events σ'')], contradicts [id__p ∈ cstmt] and [NoDupCompIds(cstmt // cstmt')] *)
      -- admit.

      (* [id__p ∉ (events σ''), then [id__p ∉ (events σ') ∪ (events σ'')] *)
      -- unfold IsMergedDState in H2.
         specialize (nIn_nIn_Union nIn_σ'_id__p nIn_σ''_id__p) as nIn_Union.
         do 7 (apply proj2 in H2); apply proj1 in H2.
         (* [merged(id__p) = σ__p], then [σ__p = σ__p']. *)
         specialize (H2 id__p σ__p nIn_Union H5) as MapsTo_merged_σ__p.
         erewrite @MapsTo_fun with (e := σ__p') (e' := σ__p); eauto.
         eapply vcomb_compid_not_in_events; eauto.

  (* CASE in right of || *)
  - eapply IHvcomb2; eauto;

    (* 2 subcases: [id__p ∈ (events σ')] or [id__p ∈ (events σ')] *)
      destruct (InA_dec Nat.eq_dec id__p (NatSet.elements (events σ''))) as [In_σ''_id__p | nIn_σ''_id__p ];
      
      (* [id__p ∈ (events σ'')] *)
      [  rewrite <- elements_iff in In_σ''_id__p;
         apply proj2, proj2, proj2, proj2, proj2, proj2, proj1 in H2;
         destruct (vcomb_maps_compstore_id H0 H5) as (σ__p0, MapsTo_σ__p0);
         specialize (H2 id__p σ__p0 In_σ''_id__p MapsTo_σ__p0) as MapsTo_σp0_m;
         erewrite @MapsTo_fun with (e := σ__p') (e' := σ__p0); eauto
       |

       rewrite <- elements_iff in nIn_σ''_id__p;
       destruct (InA_dec Nat.eq_dec id__p (NatSet.elements (events σ'))) as [In_σ'_id__p | nIn_σ'_id__p ];
       [
         rewrite <- elements_iff in In_σ'_id__p; admit
       |

       rewrite <- elements_iff in nIn_σ'_id__p;
       unfold IsMergedDState in H2;
       specialize (nIn_nIn_Union nIn_σ'_id__p nIn_σ''_id__p) as nIn_Union;
       do 7 (apply proj2 in H2); apply proj1 in H2;
       specialize (H2 id__p σ__p nIn_Union H5) as MapsTo_merged_σ__p;
       erewrite @MapsTo_fun with (e := σ__p') (e' := σ__p); eauto;
       eapply vcomb_compid_not_in_events; eauto
       ] 

      ].

Admitted.



