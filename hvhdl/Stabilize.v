(** * Stabilization relation. *)

(** Defines the relation that evaluates the behavioral
    part of a design until there are no more events
    on signals or component instances generated;
    then the design is said to be stabilized.
 *)

Require Import Environment.
Require Import AbstractSyntax.
Require Import CombinationalEvaluation.

(** Defines the stabilization relation. *)

Inductive stabilize (denv : DEnv) (dstate : DState) (behavior : cs) : DState -> Prop :=

(** Case when the design state [dstate] registered no event; it has
    stabilized.  *)

| StabilizeEnd :
    (* * Side conditions * *)
    events dstate = NatSet.empty ->
    
    (* * Conclusion * *)
    stabilize denv dstate behavior dstate 
  
(** Case when the design state [dstate] registered some events;
    therefore it has not stabilized.

    Evaluates [behavior] with the [vcomb] relation and sees if the
    newly generated state has stabilized. *)

| StabilizeLoop :
    forall {dstate' dstate''},
      
      (* * Premises * *)
      vcomb denv dstate behavior dstate' ->
      stabilize denv dstate' behavior dstate'' ->

      (* * Side conditions * *)
      (* Some events are registered in dstate. *)
      events dstate <> NatSet.empty ->
      
      (* * Conclusion * *)
      stabilize denv dstate behavior dstate''.
