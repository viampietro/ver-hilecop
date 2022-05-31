(** * Evaluation of concurrent statements *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.SSEvaluation.
Require Import hvhdl.PortMapEvaluation.

Import NatMap.

(** Defines the relation that evaluates H-VHDL concurrent
    statements. *)

Inductive VConc (D__s : IdMap design) (Δ : ElDesign) (σ : DState) (flag : simflag) :
  cs -> DState -> Prop :=

(** Evaluation of a process statement *)
| VConcPs :
  forall id vars stmt Λ sst' Λ',

    (* * Premises * *)
    VSeq Δ (sstore σ) (sstore σ) Λ flag stmt sst' Λ' ->

    (* * Side conditions * *)
    MapsTo id (Process Λ) Δ ->

    (* * Conclusion * *)
    VConc D__s Δ σ flag (cs_ps id vars stmt) (MkDState sst' (cstore σ ))

(** Evaluation of a design instantiation statement *)
| VConcComp :
  forall id__c id__e g i o d Δ__c σ__c sst__c' σ__c'' sst',
  
    (* * Premises * *)
    MIP Δ Δ__c (sstore σ) (sstore σ__c) i sst__c' ->
    VConc D__s Δ__c (MkDState sst__c' (cstore σ__c)) flag (beh d) σ__c'' ->
    MOP Δ Δ__c (sstore σ) (sstore σ__c'') o sst' ->

    (* * Side conditions * *)
    MapsTo id__e d D__s ->
    MapsTo id__c (Component Δ__c) Δ ->
    MapsTo id__c σ__c (cstore σ) ->
    
    (* * Conclusion * *)
    VConc D__s Δ σ flag (cs_comp id__c id__e g i o) (MkDState sst' (add id__c σ__c'' (cstore σ)))

(** Evaluation the parallel composition of two concurrent statements *)
| VConcPar :
  forall cstmt1 cstmt2 σ1 σ2,

    (* * Premises * *)
    VConc D__s Δ σ flag cstmt1 σ1 ->
    VConc D__s Δ σ flag cstmt2 σ2 ->
          
    (* * Conclusion * *)
    VConc D__s Δ σ flag (cs_par cstmt1 cstmt2) (merge σ σ1 σ2)
          
(** Evaluation of the null statement (no operation) *)
| VConcNull : VConc D__s Δ σ flag cs_null σ.
