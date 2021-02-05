(** Facts about Evaluation of the Place Design Behavior *)

Require Import common.NatSet.
Require Import common.NatMap.
Require Import common.NatMapTactics.

Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Place.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.HVhdlTypes.



Lemma vcomb_marking_ps_inv_sigstore :
  forall {D__s Δ σ σ' id v},
    vcomb D__s Δ σ marking_ps σ' ->
    MapsTo id v (sigstore σ) ->
    MapsTo id v (sigstore σ').
Admitted.

Lemma vcomb_sigid_not_in_events_1 :
  forall {D__s Δ σ σ' cstmt id v},
    vcomb D__s Δ σ cstmt σ' ->
    MapsTo id v (sigstore σ) ->
    MapsTo id v (sigstore σ') ->
    ~CompOf Δ id ->
    ~NatSet.In id (events σ').
Admitted.

Definition AssignedInCs (id : ident) (cstmt : cs) := False.

Lemma vcomb_inv_sigstore_if_not_assigned :
  forall {D__s Δ σ cstmt σ' id v},
    vcomb D__s Δ σ cstmt σ' ->
    MapsTo id v (sigstore σ) ->
    ~AssignedInCs id cstmt ->
    MapsTo id v (sigstore σ').
Admitted.

Lemma vcomb_place_inv_s_marking :
  forall {Δ σ σ' v m},
    vcomb hdstore Δ σ place_behavior σ' ->
    MapsTo s_marking (Declared (Tnat 0 m)) Δ ->
    MapsTo s_marking v (sigstore σ) ->
    MapsTo s_marking v (sigstore σ').
Proof.
  intros *; unfold place_behavior.
  do 2 (rewrite vcomb_par_comm; rewrite <- vcomb_par_assoc);
    rewrite <- vcomb_par_assoc.
  inversion_clear 1; intros.

  (* Use merge state definition *)
  match goal with
  | [ H: IsMergedDState _ _ _ _ |- _ ] =>
    do 4 (apply proj2 in H); apply proj1 in H; apply H; clear H; auto
  end.
  apply nIn_nIn_Union.

  (* CASE [id ∉ (events σ'0)] *)
  - eapply vcomb_sigid_not_in_events_1; eauto.
    eapply vcomb_marking_ps_inv_sigstore; eauto.    
    destruct 1; mapsto_discriminate.

  (* CASE [id ∉ (events σ'')] *)
  - eapply vcomb_sigid_not_in_events_1; eauto.
    eapply vcomb_inv_sigstore_if_not_assigned; eauto.
    destruct 1; mapsto_discriminate.
Qed.

Lemma vcomb_inv_s_marking :
  forall Δ σ behavior σ',
    vcomb hdstore Δ σ behavior σ' ->
    forall id__p gm ipm opm σ__p σ__p' v Δ__p compids mm,
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) behavior ->
      MapsTo id__p (Component Δ__p) Δ ->
      AreCsCompIds behavior compids -> 
      List.NoDup compids ->
      MapsTo id__p σ__p (compstore σ) ->
      MapsTo s_marking v (sigstore σ__p) ->
      MapsTo s_marking (Declared (Tnat 0 mm)) Δ__p -> 
      MapsTo id__p σ__p' (compstore σ') ->
      MapsTo s_marking v (sigstore σ__p').
Proof.
  induction 1; inversion 1; intros.

  (* CASE component with events. *)
  - subst; subst_place_design.
    match goal with
    | [ H: MapsTo _ _ (compstore (cstore_add _ _ _)) |- _ ] => simpl in H
    end.
    erewrite @MapsTo_add_eqv with (e' := σ__c'') (e := σ__p'); eauto.    
    erewrite @MapsTo_fun with (x := compid) (e := σ__p) (e' := σ__c) in *; eauto.
    assert (e : Component Δ__p = Component Δ__c) by (eapply MapsTo_fun; eauto).
    inject_left e; eauto.
    eapply vcomb_place_inv_s_marking; eauto.    
    eapply mapip_inv_sigstore; eauto.
    unfold InputOf; destruct 1; mapsto_discriminate.

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
         { eapply (AreCsCompIds_compid_iff HAreCsCompIds1); eauto. }
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
         { eapply (AreCsCompIds_compid_iff HAreCsCompIds2); eauto. }
      -- eapply @vcomb_compid_not_in_events_2 with (σ' := σ''); eauto.
Qed.
