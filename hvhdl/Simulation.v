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
Require Import dp.SitpnTypes.
Require Import SynchronousEvaluation.
Require Import Stabilize.
Require Import DesignElaboration.
Require Import Initialization.
Require Import HVhdlTypes.

(** Defines the relation that computes a simulation cycle in the
    context of an elaborated design [ed], starting from a design
    state [dstate] at the beginning of the cycle.  A simulation cycle
    executes the [behavior] of a design, with respect to the different
    phases that happen during a cycle, and generates a new design
    state.

    - [Ep] is the function yielding the values of input ports at a
      given simulation time and for a given clock signal event.
      
    - [tau] corresponds to the number of simulation cycles that are
      yet to be executed.  *)

Inductive simcycle
          (Ep : nat -> Clk -> IdMap value)
          (ed : ElDesign)
          (tau : nat)
          (dstate : DState)
          (behavior : cs) : DState -> Prop :=

(** Defines one simulation cycle *)
| SimCycle :
    forall {dstate_re dstate_fe dstate1 dstate2 dstate3 dstate'},
      
      (* * Premises * *)
      vrising ed dstate_re behavior dstate1 ->
      stabilize ed dstate1 behavior dstate2 ->
      vfalling ed dstate_fe behavior dstate3 ->
      stabilize ed dstate3 behavior dstate' ->

      (* * Side conditions * *)

      (* ⊌ stands for the overriding union and ∩≠ stands for the
         differentiated intersection. *)
      
      (* σ = <S, C, E> and σre = <S ⊌ Pi(Tc, ↑), C, E ∪ (S ∩≠ Pi(Tc, ↑))> *)
      IsInjectedDState dstate (Ep tau rising_edge) dstate_re ->

      (* σ2 = <S2, C2, E2> and σfe = <S2 ∪← Pi(Tc, ↓), C2, E2 ∪ (S ∩≠ Pi(Tc, ↑))> *)
      IsInjectedDState dstate2 (Ep tau falling_edge) dstate_fe ->
      
      (* * Conclusion * *)
      simcycle Ep ed tau dstate behavior dstate'.

(** Defines the simulation loop relation, that relates the design
    state through simulation cycles, until the time counter reaches
    zero.
    
    The simulation loop relation binds the state of a design at the
    beginning of the simulation and the state of the design at the end
    of the simulation.  *)

Inductive simloop
          (Ep : nat -> Clk -> IdMap value)
          (ed : ElDesign)
          (dstate : DState)
          (behavior : cs) : nat -> DState -> Prop :=

(** Loops if time counter is greater than zero. *)
  
| SimLoop :
    forall {tau dstate' dstate''},

      (* * Premises * *)
      simcycle Ep ed tau dstate behavior dstate' ->
      simloop Ep ed dstate' behavior (tau - 1) dstate'' ->
      
      (* * Side conditions * *)
      tau > 0 ->
      
      (* * Conclusion * *)
      simloop Ep ed dstate behavior tau dstate''

(** Stops if time counter is zero. *)
| SimLoopEnd :
    simloop Ep ed dstate behavior 0 dstate.

(** Defines the whole workflow necessary to simulate a H-VHDL
    description (elaboration + simulation).

    - [dstore], the design store that maps design identifiers (i.e,
      the identifier of the entity part of the design) to their
      description in abstract syntax.

    - [Mg], the dimensioning (partial) function that yields the
      values attached to the generic constant of the design.

    - [Ep], the function that yields the values for the input
      ports of the design at a certain time and clock event.

    - [tau], the number of simulation cycle to be performed after
      the initialization.

    - [d], the design that will elaborated and simulated.
*)

Inductive simwf
          (dstore : IdMap design)
          (Mg : IdMap value)
          (Ep : nat -> Clk -> IdMap value)
          (tau : nat)
          (d : design) : DState -> Prop :=
  
| SimWorkflow :
    forall {ed dstate dstate0 dstate'},
      
      (* * Premises * *)

      edesign dstore Mg d ed dstate ->                   (* Elaboration *)
      init ed dstate (get_behavior d) dstate0 ->            (* Initialization *)
      simloop Ep ed dstate0 (get_behavior d) tau dstate' -> (* Simulation loop *)
                    
      (* * Conclusion * *)
      simwf dstore Mg Ep tau d dstate'.
