(** * Soundness Proof Definitions *)

(* Common libraries *)

Require Import common.Coqlib.

(* SITPN Libraries *)

Require Import dp.SitpnTypes.
Require Import dp.Sitpn.

(* H-VHDL Libraries *)

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.SynchronousEvaluation.
Require Import hvhdl.Initialization.
Require Import hvhdl.Stabilize.

(** Defines the relation stating that an SITPN execution environment
    and a H-VHDL design execution environment described the same
    behavior.

    - The environment [Ec] provides boolean values to the conditions
    of [sitpn] depending on the cycle count [tau] 
    
    - The environment [Ep] provides values (must be boolean) to the input
    ports of design [d] that implements the conditions of [sitpn].
*)

Definition EnvEq sitpn (Ec : nat -> C sitpn -> bool) (Ep : nat -> Clk -> IdMap value) : Prop := True.

(** Defines the state similarity relation between an SITPN state and
    a H-VHDL design state.
 *)

Definition SimState {sitpn} (γ : P sitpn + T sitpn -> ident) (s : SitpnState sitpn) (σ : DState) : Prop :=

  (* Markings are similar. *)
  
  forall (p : P sitpn) id__p σ__p,
    (* [idp] is the identifier of the place component associated with
       place [p] by the [γ] binder. *)
    γ (inl p) = id__p ->

    (* [σp] is the current state of component [idp] is the global design
       state [σ]. *)
    MapsTo id__p σ__p (compstore σ) ->

    (* Marking of place [p] at state [s] equals value of signal
       [s_marking] at state [σp]. *)
    MapsTo Place.s_marking (Vnat (M s p)) (sigstore σ__p).

Notation "γ ⊢ s '∼' σ" := (SimState γ s σ) (at level 50).

(** States that two execution trace are similar. The first list
    argument is the execution trace of an SITPN and the second list
    argument is the execution trace of a VHDL design.
    
    By construction, and in order to be similar, the two traces must
    have the same length, and must have pair-wise similar states. *)

Inductive SimTrace {sitpn} γ : list (SitpnState sitpn) -> list DState -> Prop :=
| SimTraceInit: SimTrace γ nil nil
| SimTraceCons: forall s σ θ__s θ__σ,
    γ ⊢ s ∼ σ ->
    SimTrace γ θ__s θ__σ ->
    SimTrace γ (s :: θ__s) (σ :: θ__σ).

(** *** PastSim Relations

    Defines a simulation trace as the trace that led to the current
    state in parameter.

    A simulation trace is always linked to a design (or its elaborated
    version) and its corresponding behavior.

    There are 4 possible past simulation traces; following
    the definition order, the current state is reached after:

    - a falling edge phase (PastSimFalling) 
    - a stabilization phase following a rising edge (PastSimRisingStab)
    - a rising edge phase (PastSimRising)
    - a stabilization phase following a falling edge (PastSimFallingStab)
        
 *)

Inductive PastSimFalling (D : IdMap design) (M : IdMap value) (d : design) (Δ : ElDesign) : list DState -> DState -> Prop :=
  PastSimFalling_cons :
    forall σ__e θ σ σ__f,
      (* Side conditions *)
      edesign D M d Δ σ__e -> 
      
      (* Premises *)
      PastSimRisingStab D M d Δ θ σ ->
      vfalling Δ σ (get_behavior d) σ__f ->

      (* Conclusion *)
      PastSimFalling D M d Δ (θ ++ [σ]) σ__f
                     
with PastSimRisingStab (D : IdMap design) (M : IdMap value) (d : design) (Δ : ElDesign) : list DState -> DState -> Prop :=
| PastSimRisingStab_cons :
    forall σ__e θ θ' σ σ',
      (* Side conditions *)
      edesign D M d Δ σ__e -> 
      
      (* Premises *)
      PastSimRising D M d Δ θ σ ->
      stabilize Δ σ (get_behavior d) θ' σ' ->

      (* Conclusion *)
      PastSimRisingStab D M d Δ (θ ++ [σ]) σ'
                        
with PastSimRising (D : IdMap design) (M : IdMap value) (d : design) (Δ : ElDesign) : list DState -> DState -> Prop :=
  PastSimRising_cons :
    forall σ__e θ σ σ__r,
      (* Side conditions *)
      edesign D M d Δ σ__e -> 
      
      (* Premises *)
      PastSimFallingStab D M d Δ θ σ ->
      vrising Δ σ (get_behavior d) σ__r ->

      (* Conclusion *)
      PastSimRising D M d Δ (θ ++ [σ]) σ__r
                     
with PastSimFallingStab (D : IdMap design) (M : IdMap value) (d : design) (Δ : ElDesign)  : list DState -> DState -> Prop :=
| PastSimFallingStab_init :
    forall σ__e σ0,
      (* Side conditions *)
      edesign D M d Δ σ__e -> 

      (* Premises *)
      init Δ σ__e (get_behavior d) σ0 ->

      (* Conclusion *)
      PastSimFallingStab D M d Δ [] σ0
                         
| PastSimFallingStab_cons :
    forall σ__e θ θ' σ σ',
      (* Side conditions *)
      edesign D M d Δ σ__e -> 
      
      (* Premises *)
      PastSimFalling D M d Δ θ σ ->
      stabilize Δ σ (get_behavior d) θ' σ' ->

      (* Conclusion *)
      PastSimFallingStab D M d Δ (θ ++ [σ]) σ'.


