(** * Initialization *)

(** Evalution of concurrent statements during the initialization phase
    of the simulation.

    The initialization phase is composed of the evaluation of the
    first part of reset blocks followed by a stabilization phase. *)

Require Import common.GlobalTypes.
Require Import common.NatSet.

Require Import hvhdl.Environment.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SSEvaluation.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.Stabilization.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Petri.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.CSEvaluation.

Include HVhdlCsNotations.

(** Relational definition of the initialization phase. *)

Inductive Init (D__s : IdMap design) (Δ : ElDesign) (σ : DState) (cstmt : cs) (σ0 : DState) : Prop :=
| Init_ :
    forall σ',

      (* * Premises * *)

      (* Executes the first part of reset blocks.  *)
      VConc D__s Δ σ init cstmt σ' ->

      (* Stabilization phase.  *)
      Stabilize D__s Δ σ' cstmt σ0 ->
      
      (* * Conclusion * *)
      Init D__s Δ σ cstmt σ0.

#[export] Hint Constructors Init : hvhdl.
