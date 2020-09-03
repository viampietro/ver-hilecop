(** * Stabilization relation. *)

(** Defines the relation that evaluates the behavioral
    part of a design until there are no more events
    on signals or component instances generated;
    then the design is said to be stabilized.
 *)

Require Import Coqlib.
Require Import NatSet.
Require Import Environment.
Require Import AbstractSyntax.
Require Import CombinationalEvaluation.

(** Defines the stabilization relation. *)

Inductive stabilize (Δ : ElDesign) (σ : DState) (behavior : cs) : list DState -> DState -> Prop :=

(** Case when the design state [σ] registered no event; it has
    stabilized.  The stabilization trace is empty (4th argument). *)

| StabilizeEnd :
    (* * Side conditions * *)
    events σ = NatSet.empty ->
    
    (* * Conclusion * *)
    stabilize Δ σ behavior [] σ 
  
(** Case when the design state [σ] registered some events;
    therefore it has not stabilized.

    Evaluates [behavior] with the [vcomb] relation and sees if the
    newly generated state has stabilized. *)

| StabilizeLoop :
    forall σ' σ'' θ,
      
      (* * Premises * *)
      vcomb Δ σ behavior σ' ->
      stabilize Δ σ' behavior θ σ'' ->

      (* * Side conditions * *)
      
      (* Some events are registered in σ. *)
      events σ <> NatSet.empty ->

      (* σ'' is a quiet state (i.e, no events) *)
      events σ'' = NatSet.empty ->
      
      (* * Conclusion * *)
      stabilize Δ σ behavior (σ' :: θ) σ''.
