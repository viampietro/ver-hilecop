(** * H-VHDL Simulation loop. *)

(** Defines the relations involved in the expression of the 
    H-VHDL simulation loop, i.e:
    
    - The relation [simcycle] expressing a simulation cycle.
    - The relation [simloop] expressing the simulation loop.
    - The relation [simwf] expressing the whole workflow
      needed to simulate a H-VHDL design (elaboration and simulation).
 *)

Require Import common.Coqlib.
Require Import common.GlobalTypes.

Require Import dp.SitpnTypes.

Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Environment.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SynchronousEvaluation.
Require Import hvhdl.Stabilize.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.Initialization.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.HilecopDesignStore.

(** Defines the relation that computes a simulation cycle in the
    context of an elaborated design [ed], starting from a design
    state [σ] at the beginning of the cycle.  A simulation cycle
    executes the [behavior] of a design, with respect to the different
    phases that happen during a cycle, and generates a new design
    state [σ'].

    - [E__p] is the function yielding the values of input ports at a
      given simulation time and for a given clock signal event.
      
    - [τ] corresponds to the number of simulation cycles that are
      yet to be executed.  *)

Inductive simcycle
          (E__p : nat -> Clk -> IdMap value)
          (Δ : ElDesign)
          (τ : nat)
          (σ : DState)
          (behavior : cs) : DState -> Prop :=

(** Defines one simulation cycle *)
  
| SimCycle :
    forall σ__injr σ__r σ' σ__injf σ__f σ'' θ θ',
      
      (* * Premises * *)
      
      vrising Δ σ__injr behavior σ__r ->
      stabilize Δ σ__r behavior θ σ' ->
      vfalling Δ σ__injf behavior σ__f ->
      stabilize Δ σ__f behavior θ' σ'' ->

      (* * Side conditions * *)

      (* ⊌ stands for the overriding union and ∩≠ stands for the
         differentiated intersection. *)
      
      (* σ = <S, C, E> and [σ__re = <S ⊌ E__p(Tc, ↑), C, E ∪ (S ∩≠ E__p(Tc, ↑))>] *)
      IsInjectedDState σ (E__p τ rising_edge) σ__injr ->

      (* σ' = <S', C', E'> and [σ__fe = <S' ⊌ E__p(Tc, ↓), C', E' ∪ (S ∩≠ E__p(Tc, ↑))>] *)
      IsInjectedDState σ' (E__p τ falling_edge) σ__injf ->
      
      (* * Conclusion * *)
      simcycle E__p Δ τ σ behavior σ''.

(** Defines the simulation loop relation, that relates the design
    state through simulation cycles, until the time counter reaches
    zero.
    
    The simulation loop relation binds the state of a design at the
    beginning of the simulation and the state of the design at the end
    of the simulation.  *)

Inductive simloop
          (E__p : nat -> Clk -> IdMap value)
          (Δ : ElDesign)
          (σ : DState)
          (behavior : cs) : nat -> list DState -> Prop :=

(** Loops if time counter is greater than zero, and adds the state at
    the end cycle to the simulation trace. *)
  
| SimLoop :
    forall τ σ' θ,

      (* * Premises * *)
      simcycle E__p Δ (S τ) σ behavior σ' ->
      
      simloop E__p Δ σ' behavior τ θ ->
            
      (* * Conclusion * *)
      simloop E__p Δ σ behavior (S τ) (σ' :: θ)

(** Stops if time counter is zero and produce an empty loop trace. *)
              
| SimLoopEnd :
    simloop E__p Δ σ behavior 0 [].

Hint Constructors simloop : hvhdl.

(** Defines the full simulation (elaboration + simulation from initial
    state) relation that establish a link between a H-VHDL design and
    its simulation trace .

    - [dstore], the design store that maps design identifiers (i.e,
      the identifier of the entity part of the design) to their
      description in abstract syntax.

    - [Mg], the dimensioning (partial) function that yields the values
      attached to the generic constant of the design.

    - [E__p], the input port environment function that yields the values
      for the input ports of the design at a certain time and clock
      event during the simulation.

    - [τ], the number of simulation cycles to be performed after the
      initialization.

    - [d], the design that will elaborated and simulated.  

    - [Δ], a given elaborated version of design [d].
 *)

Inductive fullsim
          (dstore : IdMap design)
          (Mg : IdMap value)
          (E__p : nat -> Clk -> IdMap value)
          (τ : nat)
          (Δ : ElDesign) 
          (d : design) : list DState -> Prop :=
  
| FullSim :
    forall σ__e σ0 θ,
      
      (* * Premises * *)

      edesign dstore Mg d Δ σ__e ->         (* Elaboration *)
      init Δ σ__e (behavior d) σ0 ->        (* Initialization *)
      simloop E__p Δ σ0 (behavior d) τ θ -> (* Simulation loop *)
                    
      (* * Conclusion * *)
      fullsim dstore Mg E__p τ Δ d (σ0 :: θ).

Hint Constructors fullsim : hvhdl.

(** Defines the full simulation relation for a H-VHDL design, in the
    HILECOP presets.
    
    What's changing compared to a standard full simulation is that the
    design store is the HILECOP design store (i.e, with the Place and
    Transition components), and the dimensioning function is always
    empty. *)

Definition hfullsim
          (E__p : nat -> Clk -> IdMap value)
          (τ : nat)
          (Δ : ElDesign)
          (d : design)
          (θ__σ : list DState) : Prop :=
  fullsim hdstore (empty value) E__p τ Δ d θ__σ.

