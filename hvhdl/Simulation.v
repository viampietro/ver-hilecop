(** * H-VHDL Simulation loop. *)

(** Defines the relations involved in the expression of the 
    H-VHDL simulation loop, i.e:
    
    - The relation [simcycle] expressing a simulation cycle.
    - The relation [simloop] expressing the simulation loop.
    - The relation [simwf] expressing the whole workflow
      needed to simulate a H-VHDL design (elaboration and simulation).
 *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.

Require Import sitpn.SitpnTypes.

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
    context of an elaborated design [Δ], starting from a design state
    [σ] at the beginning of the cycle.  A simulation cycle executes
    the [behavior] of a design, with respect to the different phases
    that happen during a cycle, and generates an intermediate design
    state [σ'] (i.e. the stable state after the rising edge of the
    clock), and a final state [σ''] (i.e. the stable state after the
    falling edge of the clock).

    - [D__s] is the global design store.

    - [E__p] is the function yielding the values of input ports at a
      given simulation time (i.e. a given count of clock cycle).
      
    - [τ] corresponds to the number of simulation cycles that are yet
      to be executed.  *)

Inductive simcycle
          (D__s : IdMap design)
          (E__p : nat -> IdMap value)
          (Δ : ElDesign)
          (τ : nat)
          (σ : DState)
          (behavior : cs)
          (σ' σ'' : DState) : Prop :=

(** Defines one simulation cycle *)
  
| SimCycle :
    forall σ__i σ__r σ__f,
      
      (* * Premises * *)
      
      vrising D__s Δ σ__i behavior σ__r ->
      stabilize D__s Δ σ__r behavior σ' ->
      vfalling D__s Δ σ' behavior σ__f ->
      stabilize D__s Δ σ__f behavior σ'' ->

      (* * Side conditions * *)

      (* ⊌ stands for the overriding union, i.e. for all partial
         functions f and f' ∈ X ↛ Y, f ⊌ f' (x) = f'(x) if x ∈ dom(f')
         and f(x) otherwise. *)
      
      (* σ = <S, C, E> and [σ__i = <S ⊌ E__p(τ), C, E>] *)
      IsInjectedDState σ (E__p τ) σ__i ->
      
      (* * Conclusion * *)
      simcycle D__s E__p Δ τ σ behavior σ' σ''.

(** Defines the simulation loop relation, that relates the design
    state through simulation cycles, until the time counter reaches
    zero.
    
    The simulation loop relation binds the state of a design at the
    beginning of the simulation and the state of the design at the end
    of the simulation.  *)

Inductive simloop
          (D__s : IdMap design)
          (E__p : nat -> IdMap value)
          (Δ : ElDesign)
          (σ : DState)
          (behavior : cs) : nat -> list DState -> Prop :=

(** Loops if time counter is greater than zero, and adds the state at
    the end cycle to the simulation trace. *)
  
| SimLoop :
    forall τ σ' σ'' θ,

      (* * Premises * *)
      simcycle D__s E__p Δ (S τ) σ behavior σ' σ'' ->
      
      simloop D__s E__p Δ σ'' behavior τ θ ->
            
      (* * Conclusion * *)
      simloop D__s E__p Δ σ behavior (S τ) (σ' :: σ'' :: θ)

(** Stops if time counter is zero and produce an empty loop trace. *)
              
| SimLoopEnd :
    simloop D__s E__p Δ σ behavior 0 [].

#[export] Hint Constructors simloop : hvhdl.

(** Defines the full simulation (elaboration + simulation from initial
    state) relation that establish a link between a H-VHDL design and
    its simulation trace .

    - [D__s], the design store that maps design identifiers (i.e, the
      identifier of the entity part of the design) to their
      description in abstract syntax.

    - [Mg], the dimensioning (partial) function that yields the values
      attached to the generic constant of the design.

    - [E__p], the input port environment function that yields the values
      for the input ports of the design at a certain time (i.e. clock
      count) during the simulation.

    - [τ], the number of simulation cycles to be performed after the
      initialization.

    - [d], the design that will elaborated and simulated.

    - [Δ], a given elaborated version of design [d].  *)

Inductive fullsim
          (D__s : IdMap design)
          (Mg : IdMap value)
          (E__p : nat -> IdMap value)
          (τ : nat)
          (d : design) : list DState -> Prop :=
  
| FullSim :
    forall Δ σ__e σ0 θ,
      
      (* * Premises * *)

      EDesign D__s Mg d Δ σ__e ->                (* Elaboration *)
      init D__s Δ σ__e (behavior d) σ0 ->        (* Initialization *)
      simloop D__s E__p Δ σ0 (behavior d) τ θ -> (* Simulation loop *)
                    
      (* * Conclusion * *)
      fullsim D__s Mg E__p τ d (σ0 :: θ).

#[export] Hint Constructors fullsim : hvhdl.

(** Defines the full simulation relation for a H-VHDL design, in the
    HILECOP presets.
    
    What's changing compared to a standard full simulation is that the
    design store is the HILECOP design store (i.e, with the Place and
    Transition components), and the dimensioning function is always
    empty. *)

Definition hfullsim
          (E__p : nat -> IdMap value)
          (τ : nat)
          (d : design)
          (θ__σ : list DState) : Prop :=
  fullsim hdstore (NatMap.empty value) E__p τ d θ__σ.

