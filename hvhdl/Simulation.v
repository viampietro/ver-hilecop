(** * Simulation of H-VHDL designs *)

(** Defines the simulation algorithm for H-HVDL designs. *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.

Require Import sitpn.SitpnTypes.

Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Environment.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Stabilization.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.Initialization.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.CSEvaluation.

(** Defines the relation that computes a simulation cycle in the
    context of an elaborated design [Δ], starting from a design state
    [σ] at the beginning of the cycle.  A simulation cycle executes
    the concurrent statement defining the behavior of a design, with
    respect to the different phases that happen during a whole clock
    cycle. A simulation cycle generates an intermediate design state
    [σ'] (i.e. the stable state after the rising edge of the clock),
    and a final state [σ''] (i.e. the stable state after the falling
    edge of the clock).

    - [D__s] is the global design store.

    - [E__p] is the function yielding the values of input ports at a
      given simulation time (i.e. a given count of clock cycles).
      
    - [τ] corresponds to the number of simulation cycles that are yet
      to be executed, and acts as the current count of clock cycles.
      *)

Inductive SimCycle
          (D__s : IdMap design)
          (E__p : nat -> IdMap value)
          (Δ : ElDesign)
          (τ : nat)
          (σ : DState)
          (cstmt : cs)
          (σ' σ'' : DState) : Prop :=

(** Defines one simulation cycle *)
  
| SimCycle_ :
    forall σ__r σ__f,
      
      (* * Premises * *)
      
      VConc D__s Δ (inj σ (E__p τ)) rising cstmt σ__r ->
      Stabilize D__s Δ σ__r cstmt σ' ->
      VConc D__s Δ σ' falling cstmt σ__f ->
      Stabilize D__s Δ σ__f cstmt σ'' ->

      (* * Conclusion * *)
      SimCycle D__s E__p Δ τ σ cstmt σ' σ''.

(** Defines the simulation loop relation that evaluates a design's
    behavior through a given count of simulation cycles, until the
    counter reaches zero. The simulation trace is preserved. *)

Inductive SimLoop
          (D__s : IdMap design)
          (E__p : nat -> IdMap value)
          (Δ : ElDesign)
          (σ : DState)
          (behavior : cs) : nat -> list DState -> Prop :=

(** Executes a simulation cycle and loops if the count of simulation
    cycles is greater than zero. *)
  
| SimLoop_ :
    forall τ σ' σ'' θ,

      (* * Premises * *)
      SimCycle D__s E__p Δ (S τ) σ behavior σ' σ'' ->
      
      SimLoop D__s E__p Δ σ'' behavior τ θ ->
            
      (* * Conclusion * *)
      SimLoop D__s E__p Δ σ behavior (S τ) (σ' :: σ'' :: θ)

(** Stops if the counter is zero and produces an empty trace. *)
              
| SimLoopEnd :
    SimLoop D__s E__p Δ σ behavior 0 [].

#[export] Hint Constructors SimLoop : hvhdl.

(** Defines the full simulation (elaboration + simulation from initial
    state) relation that establish a link between a H-VHDL design and
    its simulation trace.

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

    - [d], the design that will be elaborated and simulated. *)

Inductive FullSim
          (D__s : IdMap design)
          (Mg : IdMap value)
          (E__p : nat -> IdMap value)
          (τ : nat)
          (d : design) : list DState -> Prop :=
  
| FullSim_ :
    forall Δ σ__e σ0 θ,
      
      (* * Premises * *)

      EDesign D__s Mg d Δ σ__e ->           (* Elaboration *)
      Init D__s Δ σ__e (beh d) σ0 ->        (* Initialization *)
      SimLoop D__s E__p Δ σ0 (beh d) τ θ -> (* Simulation loop *)

      (* * Side conditions * *)
      
      
      (* * Conclusion * *)
      FullSim D__s Mg E__p τ d (σ0 :: θ).

#[export] Hint Constructors FullSim : hvhdl.

(** Defines the full simulation relation for a H-VHDL design, in the
    HILECOP presets.
    
    What's changing compared to a standard full simulation is that the
    design store is the HILECOP design store (i.e, with the Place and
    Transition components), and the dimensioning function is always
    empty. *)

Definition HFullSim
          (E__p : nat -> IdMap value)
          (τ : nat)
          (d : design)
          (θ__σ : list DState) : Prop :=
  FullSim hdstore (NatMap.empty value) E__p τ d θ__σ.

