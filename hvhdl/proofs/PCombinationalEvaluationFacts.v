(** * Facts about Combinational Evaluation of the Place Design Behavior *)

Require Import common.CoqLib.
Require Import common.InAndNoDup.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.
Require Import common.NatSet.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.proofs.HVhdlCoreFactsLib.
Require Import hvhdl.proofs.HVhdlCoreTacticsLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.proofs.HVhdlSimulationFactsLib.
Require Import hvhdl.proofs.CombinationalEvaluationTactics.

Lemma vcomb_marking_ps_inv_sstore :
  forall {D__s Δ σ σ' id v},
    vcomb D__s Δ σ marking_ps σ' ->
    MapsTo id v (sstore σ) ->
    MapsTo id v (sstore σ').
Proof.
  unfold marking_ps.
  inversion 1; auto.
  do 2 (match goal with
        | [ H: vseq _ _ _ _ _ _ _ _ |- _ ] =>
          inversion H
        end); simpl; auto.
Qed.

Lemma vcomb_marking_ps_no_events :
  forall {D__s Δ σ σ'},
    vcomb D__s Δ σ marking_ps σ' ->
    Equal (events σ') {[]}.
Proof.
  unfold marking_ps.
  inversion 1; auto; simpl; try reflexivity.
  do 2 (match goal with
        | [ H: vseq _ _ _ _ _ _ _ _ |- _ ] =>
          inversion H
        end); simpl; auto; try reflexivity.
Qed.

Lemma vcomb_place_inv_s_marking :
  forall {Δ σ σ' v m},
    vcomb hdstore Δ σ place_behavior σ' ->
    MapsTo s_marking (Declared (Tnat 0 m)) Δ ->
    MapsTo s_marking v (sstore σ) ->
    MapsTo s_marking v (sstore σ').
Proof.
  intros *; unfold place_behavior.
  do 2 (rewrite vcomb_par_comm; rewrite <- vcomb_par_assoc);
    rewrite <- vcomb_par_assoc.
  inversion_clear 1; intros.

  (* Use merge state definition *)
  decompose_IMDS.
  match goal with
  | [ H: _ -> _ -> ~NatSet.In _ _ -> _ |- _ ] =>
    erewrite <- H; clear H; auto
  end.
  apply nIn_nIn_Union.

  (* CASE [id ∉ (events σ'0)] *)
  - erewrite vcomb_marking_ps_no_events; eauto with set.

  (* CASE [id ∉ (events σ'')] *)
  - eapply vcomb_not_in_events_if_not_assigned; eauto.
    destruct 1; mapsto_discriminate.
    simpl; cbv; lia.
Qed.

Lemma vcomb_inv_s_marking :
  forall Δ σ behavior σ',
    vcomb hdstore Δ σ behavior σ' ->
    forall id__p gm ipm opm σ__p σ__p' v Δ__p compids mm,
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) behavior ->
      MapsTo id__p (Component Δ__p) Δ ->
      AreCsCompIds behavior compids -> 
      List.NoDup compids ->
      MapsTo id__p σ__p (cstore σ) ->
      MapsTo s_marking v (sstore σ__p) ->
      MapsTo s_marking (Declared (Tnat 0 mm)) Δ__p -> 
      MapsTo id__p σ__p' (cstore σ') ->
      MapsTo s_marking v (sstore σ__p').
Proof.
  induction 1; inversion 1; intros.

  (* CASE component with events. *)
  - subst; subst_place_design.
    match goal with
    | [ H: MapsTo _ _ (cstore (cstore_add _ _ _)) |- _ ] => simpl in H
    end.
    erewrite @MapsTo_add_eqv with (e' := σ__c'') (e := σ__p'); eauto.    
    erewrite @MapsTo_fun with (x := id__c) (e := σ__p) (e' := σ__c) in *; eauto.
    assert (e : Component Δ__p = Component Δ__c) by (eapply MapsTo_fun; eauto).
    inject_left e; eauto.
    eapply vcomb_place_inv_s_marking; eauto.    
    eapply mapip_inv_sstore; eauto.
    unfold InputOf; destruct 1; mapsto_discriminate.

  (* CASE component with no events. *)
  - erewrite @MapsTo_fun with (e := σ__p') (e' := σ__p); eauto.
    eapply mapop_inv_cstore; eauto.    

  (* CASE in left of || *)
  - destruct (AreCsCompIds_ex cstmt) as (compids1, HAreCsCompIds1).
    destruct (AreCsCompIds_ex cstmt') as (compids2, HAreCsCompIds2).
    eapply IHvcomb1; eauto; [ solve_nodup_compids_l | solve_vcomb_par_l ].
         
  (* CASE in right of || *)
  - destruct (AreCsCompIds_ex cstmt) as (compids1, HAreCsCompIds1).
    destruct (AreCsCompIds_ex cstmt') as (compids2, HAreCsCompIds2).
    eapply IHvcomb2; eauto; [ solve_nodup_compids_r | solve_vcomb_par_r ].
Qed.
