(** * Stabilization *)

(** Evaluation of concurrent statements during the stabilization
    phase. *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.NatSet.
Require Import common.ListPlus.

Require Import hvhdl.Environment.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.CSEvaluation.
Require Import hvhdl.HVhdlTypes.

(** Defines the stabilization relation *)

Inductive Stabilize (D__s : IdMap design) (Δ : ElDesign) (σ : DState) (cstmt : cs) : DState -> Prop :=

(** Case when the evaluation of [cstmt] yields a state [σ'] equal to
    starting state [σ]. Thus, the stabilization phase ends. *)

| StabilizeEnd :
  forall σ',
    
    (* * Premises * *)
    VConc D__s Δ σ stab cstmt σ' ->

    (* * Side conditions * *)
    DStateEq σ σ' ->
    
    (* * Conclusion * *)
    Stabilize D__s Δ σ cstmt σ'
  
(** Case when the evaluation of [cstmt] yields a state [σ'] different
    from starting state [σ]. Then, the stabilization continues with
    [σ'] as new starting state. *)

| StabilizeLoop :
    forall σ' σ'',
      
      (* * Premises * *)
      VConc D__s Δ σ stab cstmt σ' ->
      Stabilize D__s Δ σ' cstmt σ'' ->

      (* * Side conditions * *)
      ~DStateEq σ σ' ->
        
      (* * Conclusion * *)
      Stabilize D__s Δ σ cstmt σ''.

Lemma Stabilize_end_state :
  forall D__s Δ σ cstmt σ',
    Stabilize D__s Δ σ cstmt σ' ->
    exists σ'', VConc D__s Δ σ'' stab cstmt σ' /\ DStateEq σ'' σ'.
Proof. induction 1; trivial.
       eexists; eauto.
Qed.
