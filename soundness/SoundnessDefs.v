(** * Soundness Proof Definitions *)

(* Common libraries *)

Require Import common.Coqlib.
Require Import common.GlobalTypes.
Require Import common.GlobalFacts.
Require Import common.ListPlus.

(* SITPN Libraries *)

Require Import dp.SitpnTypes.
Require Import dp.Sitpn.
Require Import dp.SitpnFacts.
Require Import dp.SitpnSemanticsDefs.
Require Import dp.Fired.

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
Require Import hvhdl.Place.
Require Import hvhdl.Transition.

(* SITPN-to-H-HVDL libraries *)

Require Import sitpn2hvhdl.Sitpn2HVhdlTypes.

(** Defines the relation stating that an SITPN execution environment
    and a H-VHDL design execution environment described the same
    behavior.

    - The environment [Ec] provides boolean values to the conditions
    of [sitpn] depending on the cycle count [tau] 
    
    - The environment [Ep] provides values (must be boolean) to the input
    ports of design [d] that implements the conditions of [sitpn].
*)

Definition SimEnv sitpn (γ : Sitpn2HVhdlMap sitpn) (E__c : nat -> C sitpn -> bool) (E__p : nat -> Clk -> IdMap value) : Prop :=
  forall τ clk c id__c,
    (* [γ(c) = id__c] *)
    InA Ckeq (c, id__c) (c2in γ)  ->
    (* [E__p(τ,clk)(id__c) = E__c(τ)(c)] *)
    MapsTo id__c (Vbool (E__c τ c)) (E__p τ clk).

(** Defines the state similarity relation between an SITPN state and a
    H-VHDL design state, without similarity of condition values.  *)

Definition SimStateNoConds {sitpn} (γ : Sitpn2HVhdlMap sitpn) (s : SitpnState sitpn) (σ : DState) : Prop :=

  (* Markings are similar. *)  
  (forall p id__p σ__p,
      (* [id__p] is the identifier of the place component associated with
         place [p] by the [γ] binder. *)
      InA Pkeq (p, id__p) (p2pcomp γ) ->

      (* [σ__p] is the current state of component [id__p] is the global
         design state [σ]. *)
      MapsTo id__p σ__p (compstore σ) ->

      (* Marking of place [p] at state [s] equals value of signal
         [s_marking] at state [σ__p]. *)
      MapsTo s_marking (Vnat (M s p)) (sigstore σ__p))

  (* Time counters are similar *)
  /\ (forall (t : Ti sitpn) id__t σ__t,
         (* [id__t] is the identifier of the T component associated with
            transition [t] by the [γ] binder. *)
         InA Tkeq (proj1_sig t, id__t) (t2tcomp γ) ->
         
         (* [σ__t] is the current state of T component [id__t] is the global
            design state [σ]. *)
         MapsTo id__t σ__t (compstore σ) ->

         (* Then, time counter similarity is: *)
         (upper t = i+ /\ TcLeLower s t -> MapsTo s_time_counter (Vnat (I s t)) (sigstore σ__t)) /\
         (upper t = i+ /\ TcGtLower s t -> MapsTo s_time_counter (Vnat (lower t)) (sigstore σ__t)) /\
         (forall pf : upper t <> i+, TcGtUpper s t -> MapsTo s_time_counter (Vnat (natinf_to_natstar (upper t) pf)) (sigstore σ__t)) /\
         (upper t <> i+ /\ TcLeUpper s t -> MapsTo s_time_counter (Vnat (I s t)) (sigstore σ__t)))

  (* Reset orders are similar. *)
  /\ (forall (t : Ti sitpn) id__t σ__t,
         (* [id__t] is the identifier of the T component associated with
            transition [t] by the [γ] binder. *)
         InA Tkeq (proj1_sig t, id__t) (t2tcomp γ) ->
         
         (* [σ__t] is the current state of T component [id__t] is the global
            design state [σ]. *)
         MapsTo id__t σ__t (compstore σ) ->

         (* Signal ["s_reinit_time_counter"] equals [reset s t] at state [σ__t] *)
         MapsTo s_reinit_time_counter (Vbool (reset s t)) (sigstore σ__t))

  (* Action executions are similar. *)
  /\ (forall a id__a,
         (* [id__a] is the output port identifier associated to action
            [a] in the [γ] binder. *)
         InA Akeq (a, id__a) (a2out γ) ->
         
         (* Output port [id__a] equals [ex s (inl a)] at state [σ] *)
         MapsTo id__a (Vbool (ex s (inl a))) (sigstore σ))

  (* Function executions are similar. *)
  /\ (forall f id__f,
         (* [id__f] is the output port identifier associated to function
            [f] in the [γ] binder. *)
         InA Fkeq (f, id__f) (f2out γ) ->
         
         (* Output port [id__f] equals [ex s (inr f)] at state [σ] *)
         MapsTo id__f (Vbool (ex s (inr f))) (sigstore σ)).

(** Defines the general state similarity relation between an SITPN state and a
    H-VHDL design state, with similarity of condition values.  *)

Definition SimState sitpn (γ : Sitpn2HVhdlMap sitpn) (s : SitpnState sitpn) (σ : DState) : Prop :=
  SimStateNoConds γ s σ

  (* Condition values are similar. *)
  /\ (forall c id__c,
         (* [id__c] is the input port identifier associated to condition
            [c] in the [γ] binder. *)
         InA Ckeq (c, id__c) (c2in γ) ->
         
         (* Input port [id__c] equals [cond s c] at state [σ] *)
         MapsTo id__c (Vbool (cond s c)) (sigstore σ)).

Notation "γ ⊢ s '∼' σ" := (SimState _ γ s σ) (at level 50).

(** Defines the state similarity relation, after a rising edge,
    between an SITPN state and a H-VHDL design state.  *)

Definition SimStateAfterRE sitpn (γ : Sitpn2HVhdlMap sitpn) (s : SitpnState sitpn) (σ : DState) : Prop :=

  (* State similarity without similar condition values. *)
  SimStateNoConds γ s σ
                  
  (* Sensitization is similar *)
  /\ (forall t id__t σ__t,
         (* [id__t] is the identifier of the T component associated with
            transition [t] by the [γ] binder. *)
         InA Tkeq (t, id__t) (t2tcomp γ) ->
         
         (* [σ__t] is the current state of T component [id__t] is the global
            design state [σ]. *)
         MapsTo id__t σ__t (compstore σ) ->

         (* Signal ["s_enabled"] equals [true] is equivalent to t ∈ Sens(M). *)
         Sens (M s) t <-> MapsTo s_enabled (Vbool true) (sigstore σ__t)).

(** Defines the state similarity relation, after a falling edge,
    between an SITPN state and a H-VHDL design state.  *)

Definition SimStateAfterFE sitpn (γ : Sitpn2HVhdlMap sitpn) (s : SitpnState sitpn) (σ : DState) : Prop :=
  (* General state similarity *)
  γ ⊢ s ∼ σ 

  (* Fired are similar. *)
  /\ (forall t id__t σ__t fired,
         (* [id__t] is the identifier of the T component associated with
            transition [t] by the [γ] binder. *)
         InA Tkeq (t, id__t) (t2tcomp γ) ->
         
         (* [σ__t] is the current state of T component [id__t] is the global
            design state [σ]. *)
         MapsTo id__t σ__t (compstore σ) ->

         (* Output port ["fired"] equals [true] is equivalent to t ∈ Fired(s,fired). *)
         Fired s fired t <-> MapsTo Transition.fired (Vbool true) (sigstore σ__t))
       
  (* Pre sum are similar. *)
  /\ (forall p id__p σ__p fired pre__sum,
         (* [id__p] is the identifier of the place component associated with
            place [p] by the [γ] binder. *)
         InA Pkeq (p, id__p) (p2pcomp γ) ->

         (* [σ__p] is the current state of component [id__p] is the global
            design state [σ]. *)
         MapsTo id__p σ__p (compstore σ) ->

         (* ∑ pre(p,t), for all t ∈ Fired(s). *)
         PreSum p (Fired s fired) pre__sum -> 
           
         (* [∑ pre(p,t) = σ__p("s_output_token_sum")]. *)
         MapsTo s_output_token_sum (Vnat pre__sum) (sigstore σ__p))

  (* Post sum are similar. *)
  /\ (forall p id__p σ__p fired post__sum,
         (* [id__p] is the identifier of the place component associated with
            place [p] by the [γ] binder. *)
         InA Pkeq (p, id__p) (p2pcomp γ) ->

         (* [σ__p] is the current state of component [id__p] is the global
            design state [σ]. *)
         MapsTo id__p σ__p (compstore σ) ->

         (* ∑ post(t,p), for all t ∈ Fired(s). *)
         PostSum p (Fired s fired) post__sum -> 
         
         (* [∑ pre(p,t) = σ__p("s_input_token_sum")]. *)
         MapsTo s_input_token_sum (Vnat post__sum) (sigstore σ__p)).

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

Hint Constructors SimTrace : core.

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

(* Inductive PastSimFalling (D : IdMap design) (M : IdMap value) (d : design) (Δ : ElDesign) : list DState -> DState -> Prop := *)
(*   PastSimFalling_cons : *)
(*     forall σ__e θ σ σ__f, *)
(*       (* Side conditions *) *)
(*       edesign D M d Δ σ__e ->  *)
      
(*       (* Premises *) *)
(*       PastSimRisingStab D M d Δ θ σ -> *)
(*       vfalling Δ σ (behavior d) σ__f -> *)

(*       (* Conclusion *) *)
(*       PastSimFalling D M d Δ (θ ++ [σ]) σ__f *)
                     
(* with PastSimRisingStab (D : IdMap design) (M : IdMap value) (d : design) (Δ : ElDesign) : list DState -> DState -> Prop := *)
(* | PastSimRisingStab_cons : *)
(*     forall σ__e θ θ' σ σ', *)
(*       (* Side conditions *) *)
(*       edesign D M d Δ σ__e ->  *)
      
(*       (* Premises *) *)
(*       PastSimRising D M d Δ θ σ -> *)
(*       stabilize Δ σ (behavior d) θ' σ' -> *)

(*       (* Conclusion *) *)
(*       PastSimRisingStab D M d Δ (θ ++ [σ]) σ' *)
                        
(* with PastSimRising (D : IdMap design) (M : IdMap value) (d : design) (Δ : ElDesign) : list DState -> DState -> Prop := *)
(*   PastSimRising_cons : *)
(*     forall σ__e θ σ σ__r, *)
(*       (* Side conditions *) *)
(*       edesign D M d Δ σ__e ->  *)
      
(*       (* Premises *) *)
(*       PastSimFallingStab D M d Δ θ σ -> *)
(*       vrising Δ σ (behavior d) σ__r -> *)

(*       (* Conclusion *) *)
(*       PastSimRising D M d Δ (θ ++ [σ]) σ__r *)
                     
(* with PastSimFallingStab (D : IdMap design) (M : IdMap value) (d : design) (Δ : ElDesign)  : list DState -> DState -> Prop := *)
(* | PastSimFallingStab_init : *)
(*     forall σ__e σ0, *)
(*       (* Side conditions *) *)
(*       edesign D M d Δ σ__e ->  *)

(*       (* Premises *) *)
(*       init Δ σ__e (behavior d) σ0 -> *)

(*       (* Conclusion *) *)
(*       PastSimFallingStab D M d Δ [] σ0 *)
                         
(* | PastSimFallingStab_cons : *)
(*     forall σ__e θ θ' σ σ', *)
(*       (* Side conditions *) *)
(*       edesign D M d Δ σ__e ->  *)
      
(*       (* Premises *) *)
(*       PastSimFalling D M d Δ θ σ -> *)
(*       stabilize Δ σ (behavior d) θ' σ' -> *)

(*       (* Conclusion *) *)
(*       PastSimFallingStab D M d Δ (θ ++ [σ]) σ'. *)


