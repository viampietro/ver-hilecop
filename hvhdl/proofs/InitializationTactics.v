(** * Tactics for Initialization *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.
Require Import common.NatSet.
Require Import common.InAndNoDup.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.proofs.HVhdlCoreFactsLib.
Require Import hvhdl.proofs.HVhdlCoreTacticsLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.ValidPortMap.

Require Import hvhdl.proofs.StabilizeFacts.
Require Import hvhdl.proofs.SSEvaluationFacts.
Require Import hvhdl.proofs.PortMapEvaluationFacts.
Require Import hvhdl.proofs.InitializationFacts.
Require Import hvhdl.proofs.PStabilizeFacts.

Ltac solve_vruninit_par_l :=
  match goal with
  | [ vruninitl: vruninit ?D__s ?Δ ?σ0 ?cs1 ?σ1,
      vruninitr: vruninit ?D__s ?Δ ?σ0 ?cs2 ?σ2,
      ACCI1: AreCsCompIds ?cs1 ?compids1,
      ACCI2: AreCsCompIds ?cs2 ?compids2,
      ACCIpar: AreCsCompIds (?cs1 // ?cs2) ?compids,
      NoDupcids: List.NoDup ?compids,
      IMDS: IsMergedDState ?σ0 ?σ1 ?σ2 ?σ__m,
      MapsTom: MapsTo ?k ?v (?store ?σ__m)                      
      |- MapsTo ?k ?v (?store ?σ1) ] =>
    (* 2 SUBCASES: [k ∈ (events σ1)] or [k ∉ (events σ1)] *)
    destruct (In_dec k (events σ1));
    [
      (* SUBCASE [k ∈ (events σ1)] *)
      erw_IMDS_cstore_1 IMDS; assumption
    |
    (* SUBCASE [k ∉ (events σ1)], 
       then [k ∉ (events σ1) ∪ (events σ2)] *)
    eapply vruninit_inv_cstate; eauto;
    erw_IMDS_cstore_m IMDS; eauto;
    eapply nIn_nIn_Union; eauto;
    
    (* Proves [id ∉ (events σ2)] *)
    eapply vruninit_compid_not_in_events; eauto;
    apply nodup_app_not_in with (l := compids1);
    [ solve_nodup_compids_app
    | eapply (AreCsCompIds_compid_iff ACCI1); eauto ]
    ]
  end.

Ltac solve_vruninit_par_r :=
  match goal with
  | [ vruninitl: vruninit ?D__s ?Δ ?σ0 ?cs1 ?σ1,
      vruninitr: vruninit ?D__s ?Δ ?σ0 ?cs2 ?σ2,
      ACCI1: AreCsCompIds ?cs1 ?compids1,
      ACCI2: AreCsCompIds ?cs2 ?compids2,
      ACCIpar: AreCsCompIds (?cs1 // ?cs2) ?compids,
      NoDupcids: List.NoDup ?compids,
      IMDS: IsMergedDState ?σ0 ?σ1 ?σ2 ?σ__m,
      MapsTom: MapsTo ?k ?v (?store ?σ__m)                      
      |- MapsTo ?k ?v (?store ?σ2) ] =>
    (* 2 SUBCASES: [k ∈ (events σ2)] or [k ∉ (events σ2)] *)
    destruct (In_dec k (events σ2));
    [
      (* SUBCASE [k ∈ (events σ2)] *)
      erw_IMDS_cstore_2 IMDS; assumption
    |
    (* SUBCASE [k ∉ (events σ2)], 
       then [k ∉ (events σ1) ∪ (events σ2)] *)
    eapply vruninit_inv_cstate; eauto;
    erw_IMDS_cstore_m IMDS; eauto;
    eapply nIn_nIn_Union; eauto;
    
    (* Proves [id ∉ (events σ1)] *)
    eapply vruninit_compid_not_in_events; eauto;
    apply nodup_app_not_in with (l := compids2);
    [ eapply NoDup_app_comm; solve_nodup_compids_app
    | eapply (AreCsCompIds_compid_iff ACCI2); eauto ]
    ]
  end.
