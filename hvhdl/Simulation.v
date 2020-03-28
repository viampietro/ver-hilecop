(** * H-VHDL Simulation loop. *)

(** Defines the relations involved in the expression of the 
    H-VHDL simulation loop, i.e:
    
    - The relation [simcycle] expressing a simulation cycle.
    - The relation [simloop] expressing the simulation loop.
    - The relation [simwf] expressing the whole workflow
      needed to simulate a H-VHDL design (elaboration and simulation).
 *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import SemanticalDomains.
Require Import Environment.
Require Import AbstractSyntax.
Require Import SitpnSemantics.
Require Import SynchronousEvaluation.
Require Import Stabilize.
Require Import DesignElaboration.
Require Import Initialization.

(** Defines the relation that computes a simulation cycle in the
    context of a design environment [denv], starting from a design
    state [dstate] at the beginning of the cycle.  A simulation cycle
    executes the [behavior] of a design, with respect to the different
    phases that happen during a cycle, and generates a new simulation
    trace, and a new final state for the simulated design.

    - [ivals] is the function yielding the values of input ports at a
      given simulation time and for a given clock signal event.

    - [trace] represents the simulation trace, that is the ordered
      list of design states computed during the previous simulation
      cycles.
      
    - [time] corresponds to the number of simulation cycles that are
      yet to be executed.  *)

Inductive simcycle
          (ivals : nat -> Clock -> IdMap value)
          (denv : DEnv)
          (dstate : DState)
          (trace : list DState)
          (time : nat)
          (behavior : cs) : list DState -> DState -> Prop :=

(** Defines one simulation cycle *)
| SimCycle :
    forall {dstate_re dstate_fe dstate1 dstate2 dstate3 dstate4},
      
      (* * Premises * *)
      vrising denv dstate_re behavior dstate1 ->
      stabilize denv dstate1 behavior dstate2 ->
      vfalling denv dstate_fe behavior dstate3 ->
      stabilize denv dstate3 behavior dstate4 ->

      (* * Side conditions * *)

      (* ⊌ stands for the overriding union and ∩≠ stands for the
         differentiated intersection. *)
      
      (* σ = <S, C, E> and σre = <S ⊌ Pi(Tc, ↑), C, E ∪ (S ∩≠ Pi(Tc, ↑))> *)
      IsInjectedDState dstate (ivals time rising_edge) dstate_re ->

      (* σ2 = <S2, C2, E2> and σfe = <S2 ∪← Pi(Tc, ↓), C2, E2 ∪ (S ∩≠ Pi(Tc, ↑))> *)
      IsInjectedDState dstate2 (ivals time falling_edge) dstate_fe ->
      
      (* * Conclusion * *)
      simcycle ivals denv dstate trace time behavior (trace ++ [dstate1; dstate2; dstate3; dstate4]) dstate4.

(** Defines the simulation loop relation, that computes simulation
    cycles until the time counter reaches zero.
    
    The simulation loop produces a simulation trace, that is, an
    time-ordered list of design states.  *)

Inductive simloop
          (ivals : nat -> Clock -> IdMap value)
          (denv : DEnv)
          (dstate : DState)
          (trace : list DState)
          (behavior : cs) : nat -> list DState -> Prop :=

(** Loops if time counter is greater than zero. *)
  
| SimLoop :
    forall {time trace' dstate' trace''},

      (* * Premises * *)
      simcycle ivals denv dstate trace time behavior trace' dstate' ->
      simloop ivals denv dstate' trace' behavior (time - 1) trace'' ->
      
      (* * Side conditions * *)
      time > 0 ->
      
      (* * Conclusion * *)
      simloop ivals denv dstate trace behavior time trace''

(** Stops if time counter is zero. *)
| SimLoopEnd :
    simloop ivals denv dstate trace behavior 0 trace.

(** Defines the whole workflow necessary to simulate a H-VHDL
    description (elaboration + simulation).

    - [dstore], the design store that maps design identifiers (i.e,
      the identifier of the entity part of the design) to their
      description in abstract syntax.

    - [dimen], the dimensioning (partial) function that yields the
      values attached to the generic constant of the design.

    - [ivals], the function that yields the values for the input
      ports of the design at a certain time and clock event.

    - [time], the number of simulation cycle to be performed after
      the initialization.

    - [d], the design that will elaborated and simulated.
*)

Inductive simwf
          (dstore : IdMap design)
          (dimen : IdMap value)
          (ivals : nat -> Clock -> IdMap value)
          (time : nat)
          (d : design) : list DState -> Prop :=
  
| SimWorkflow :
    forall {trace denv dstate dstate' entid archid
                  gens ports adecls behavior},
      
      (* * Premises * *)

      edesign dstore dimen d denv dstate ->                       (* Elaboration *)
      init denv dstate behavior dstate' ->                        (* Initialization *)
      simloop ivals denv dstate' [dstate'] behavior time trace -> (* Simulation loop *)
              
      (* * Side conditions * *)
      
      (* Needed to retrieve the behavioral part of the design. *)
      d = design_ entid archid gens ports adecls behavior ->
      
      (* * Conclusion * *)
      simwf dstore dimen ivals time d trace.
