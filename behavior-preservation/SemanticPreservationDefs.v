(** * Soundness Proof Definitions *)

(* Common libraries *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.GlobalFacts.
Require Import common.ListPlus.
Require Import common.NatMap.
Require Import common.NatSet.

(* SITPN Libraries *)

Require Import sitpn.SitpnTypes.
Require Import sitpn.Sitpn.
Require Import sitpn.SitpnFacts.
Require Import sitpn.SitpnSemanticsDefs.
Require Import sitpn.Fired.

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

Require Import transformation.Sitpn2HVhdlTypes.

(** Defines the state similarity relation between an SITPN state and a
    H-VHDL design state, without similarity of condition values and reset orders.  *)

Definition SimStateNoCondsNoReset {sitpn} (γ : Sitpn2HVhdlMap sitpn) (s : SitpnState sitpn) (σ : DState) : Prop :=

  (* Markings are similar. *)  
  (forall p id__p σ__p,
      (* [id__p] is the identifier of the place component associated with
         place [p] by the [γ] binder. *)
      InA Pkeq (p, id__p) (p2pci γ) ->

      (* [σ__p] is the current state of component [id__p] is the global
         design state [σ]. *)
      MapsTo id__p σ__p (cstore σ) ->

      (* Marking of place [p] at state [s] equals value of signal
         [s_marking] at state [σ__p]. *)
      MapsTo s_marking (Vnat (M s p)) (sstore σ__p))

  (* Time counters are similar *)
  /\ (forall (t : Ti sitpn) id__t σ__t,
         (* [id__t] is the identifier of the T component associated with
            transition [t] by the [γ] binder. *)
         InA Tkeq (proj1_sig t, id__t) (t2tci γ) ->
         
         (* [σ__t] is the current state of T component [id__t] is the global
            design state [σ]. *)
         MapsTo id__t σ__t (cstore σ) ->

         (* Then, time counter similarity is: *)
         (upper t = i+ /\ TcLeLower s t -> MapsTo s_time_counter (Vnat (I s t)) (sstore σ__t)) /\
         (upper t = i+ /\ TcGtLower s t -> MapsTo s_time_counter (Vnat (lower t)) (sstore σ__t)) /\
         (forall pf : upper t <> i+, TcGtUpper s t -> MapsTo s_time_counter (Vnat (natinf_to_natstar (upper t) pf)) (sstore σ__t)) /\
         (upper t <> i+ /\ TcLeUpper s t -> MapsTo s_time_counter (Vnat (I s t)) (sstore σ__t)))


  (* Action executions are similar. *)
  /\ (forall a id__a,
         (* [id__a] is the output port identifier associated to action
            [a] in the [γ] binder. *)
         InA Akeq (a, id__a) (a2out γ) ->
         
         (* Output port [id__a] equals [ex s (inl a)] at state [σ] *)
         MapsTo id__a (Vbool (ex s (inl a))) (sstore σ))

  (* Function executions are similar. *)
  /\ (forall f id__f,
         (* [id__f] is the output port identifier associated to function
            [f] in the [γ] binder. *)
         InA Fkeq (f, id__f) (f2out γ) ->
         
         (* Output port [id__f] equals [ex s (inr f)] at state [σ] *)
         MapsTo id__f (Vbool (ex s (inr f))) (sstore σ)).

(** Defines the general state similarity relation between an SITPN
    state and a H-VHDL design state, with similarity of condition
    values and reset orders.  *)

Definition SimState sitpn (γ : Sitpn2HVhdlMap sitpn) (s : SitpnState sitpn) (σ : DState) : Prop :=
  SimStateNoCondsNoReset γ s σ

  (* Reset orders are similar. *)
  /\ (forall (t : Ti sitpn) id__t σ__t,
         (* [id__t] is the identifier of the T component associated with
            transition [t] by the [γ] binder. *)
         InA Tkeq (proj1_sig t, id__t) (t2tci γ) ->
         
         (* [σ__t] is the current state of T component [id__t] is the global
            design state [σ]. *)
         MapsTo id__t σ__t (cstore σ) ->

         (* Signal ["s_reinit_time_counter"] equals [reset s t] at state [σ__t] *)
         MapsTo s_reinit_time_counter (Vbool (reset s t)) (sstore σ__t))
                  
  (* Condition values are similar. *)
  /\ (forall c id__c,
         (* [id__c] is the input port identifier associated to condition
            [c] in the [γ] binder. *)
         InA Ckeq (c, id__c) (c2in γ) ->
         
         (* Input port [id__c] equals [cond s c] at state [σ] *)
         MapsTo id__c (Vbool (cond s c)) (sstore σ)).

Notation "γ ⊢ s '∼' σ" := (SimState _ γ s σ) (at level 50).

(** Defines the state similarity relation, after a rising edge,
    between an SITPN state and a H-VHDL design state. Only condition
    values are not similar. *)

Definition SimStateAfterRE sitpn (γ : Sitpn2HVhdlMap sitpn) (s : SitpnState sitpn) (σ : DState) : Prop :=

  (* State similarity without similar condition values and reset
     orders. *)
  SimStateNoCondsNoReset γ s σ
                         
  (* Reset orders are similar. *)
  /\ (forall (t : Ti sitpn) id__t σ__t,
         (* [id__t] is the identifier of the T component associated with
            transition [t] by the [γ] binder. *)
         InA Tkeq (proj1_sig t, id__t) (t2tci γ) ->
         
         (* [σ__t] is the current state of T component [id__t] is the global
            design state [σ]. *)
         MapsTo id__t σ__t (cstore σ) ->

         (* Signal ["s_reinit_time_counter"] equals [reset s t] at state [σ__t] *)
         MapsTo s_reinit_time_counter (Vbool (reset s t)) (sstore σ__t)).

(** Defines the full state similarity relation, after a rising edge,
    between an SITPN state and a H-VHDL design state.  *)

Definition FullSimStateAfterRE sitpn
           (γ : Sitpn2HVhdlMap sitpn)
           (E : nat -> C sitpn -> bool)
           (τ : nat)
           (s : SitpnState sitpn) (σ : DState) : Prop :=

  (* State similarity after rising edge is verified. *)
  SimStateAfterRE sitpn γ s σ 
                  
  (* Sensitization is similar *)
  /\ (forall t id__t σ__t,
         (* [id__t] is the identifier of the T component associated with
            transition [t] by the [γ] binder. *)
         InA Tkeq (t, id__t) (t2tci γ) ->
         
         (* [σ__t] is the current state of T component [id__t] is the global
            design state [σ]. *)
         MapsTo id__t σ__t (cstore σ) ->

         (* Signal ["s_enabled"] equals [true] is equivalent to t ∈ Sens(M). *)
         Sens (M s) t <-> MapsTo s_enabled (Vbool true) (sstore σ__t))
       
  /\ (forall t id__t σ__t,
         (* [id__t] is the identifier of the T component associated with
            transition [t] by the [γ] binder. *)
         InA Tkeq (t, id__t) (t2tci γ) ->
         
         (* [σ__t] is the current state of T component [id__t] is the global
            design state [σ]. *)
         MapsTo id__t σ__t (cstore σ) ->

         (* Signal ["s_enabled"] equals [false] is equivalent to t ∉ Sens(M). *)
         ~Sens (M s) t <-> MapsTo s_enabled (Vbool false) (sstore σ__t))
       
  (* Condition combination is equal to signal [s_condition_combination]. *)
  /\ (forall t id__t σ__t conds_of_t bprod,
         (* [id__t] is the identifier of the T component associated with
            transition [t] by the [γ] binder. *)
         InA Tkeq (t, id__t) (t2tci γ) ->
         
         (* [σ__t] is the current state of TCI [id__t] is the global
            design state [σ]. *)
         MapsTo id__t σ__t (cstore σ) ->

         (* Signal [s_condition_combination] is equal the Boolean
            product of value of conditions attached to transition
            [t]. *)

         let cond_val_fun :=
           (fun c => match has_C t (proj1_sig c) with
                       one => E τ (proj1_sig c)
                     | mone => negb (E τ (proj1_sig c))
                     | _ => true end) in
         
         @Sig_in_List (C sitpn) (fun c => has_C t c = one \/ has_C t c = mone) conds_of_t ->
         BProd cond_val_fun conds_of_t bprod ->
         MapsTo s_condition_combination (Vbool bprod) (sstore σ__t))
       
  (* Condition input port values are equal to condition values at
     clock count [τ]. *)

  /\ (forall c id__c,
         (* [id__c] is the input port identifier associated to condition
            [c] in the [γ] binder. *)
         InA Ckeq (c, id__c) (c2in γ) ->
         
         (* Value of input port [id__c] at state [σ] equals [E τ c]. *)
         MapsTo id__c (Vbool (E τ c)) (sstore σ)).

(** Defines the state similarity relation, after a falling edge,
    between an SITPN state and a H-VHDL design state. This relation is
    similar to the general state similarity except for the equality of
    the value of reset orders (which does not hold after a falling
    edge). *)

Definition SimStateAfterFE sitpn (γ : Sitpn2HVhdlMap sitpn) (s : SitpnState sitpn) (σ : DState) : Prop :=
  (* State similarity without similar condition values and reset
     orders. *)
  SimStateNoCondsNoReset γ s σ

  (* Then, add similarity of condition values. *)
  /\ (forall c id__c,
         (* [id__c] is the input port identifier associated to condition
            [c] in the [γ] binder. *)
         InA Ckeq (c, id__c) (c2in γ) ->
         
         (* Input port [id__c] equals [cond s c] at state [σ] *)
         MapsTo id__c (Vbool (cond s c)) (sstore σ)).

(** Defines the full state similarity relation, after a falling edge,
    between an SITPN state and a H-VHDL design state.  *)

Definition FullSimStateAfterFE sitpn (γ : Sitpn2HVhdlMap sitpn) (s : SitpnState sitpn) (σ : DState) : Prop :=
  
  (* State similarity after falling edge *)
  SimStateAfterFE sitpn γ s σ 

  (* Fired are similar. *)
  /\ (forall t id__t σ__t fired,
         (* [id__t] is the identifier of the T component associated with
            transition [t] by the [γ] binder. *)
         InA Tkeq (t, id__t) (t2tci γ) ->
         
         (* [σ__t] is the current state of T component [id__t] is the global
            design state [σ]. *)
         MapsTo id__t σ__t (cstore σ) ->

         (* Output port ["fired"] equals [true] is equivalent to t ∈ Fired(s,fired). *)
         (Fired s fired t <-> MapsTo Transition.fired (Vbool true) (sstore σ__t))
         /\ (~Fired s fired t <-> MapsTo Transition.fired (Vbool false) (sstore σ__t)))

  (* Firable are similar. *)
  /\ (forall t id__t σ__t,
         (* [id__t] is the identifier of the T component associated with
            transition [t] by the [γ] binder. *)
         InA Tkeq (t, id__t) (t2tci γ) ->
         
         (* [σ__t] is the current state of T component [id__t] is the global
            design state [σ]. *)
         MapsTo id__t σ__t (cstore σ) ->

         (* Output port ["firable"] equals [true] is equivalent to t ∈ Firable(s). *)
         (Firable s t <-> MapsTo Transition.firable (Vbool true) (sstore σ__t))
         /\ (~Firable s t <-> MapsTo Transition.firable (Vbool false) (sstore σ__t)))
       
  (* Pre sum are similar. *)
  /\ (forall p id__p σ__p fired pre__sum,
         (* [id__p] is the identifier of the place component associated with
            place [p] by the [γ] binder. *)
         InA Pkeq (p, id__p) (p2pci γ) ->

         (* [σ__p] is the current state of component [id__p] is the global
            design state [σ]. *)
         MapsTo id__p σ__p (cstore σ) ->

         (* ∑ pre(p,t), for all t ∈ Fired(s). *)
         PreSum p (Fired s fired) pre__sum -> 
           
         (* [∑ pre(p,t) = σ__p("s_output_token_sum")]. *)
         MapsTo s_output_token_sum (Vnat pre__sum) (sstore σ__p))

  (* Post sum are similar. *)
  /\ (forall p id__p σ__p fired post__sum,
         (* [id__p] is the identifier of the place component associated with
            place [p] by the [γ] binder. *)
         InA Pkeq (p, id__p) (p2pci γ) ->

         (* [σ__p] is the current state of component [id__p] is the global
            design state [σ]. *)
         MapsTo id__p σ__p (cstore σ) ->

         (* ∑ post(t,p), for all t ∈ Fired(s). *)
         PostSum p (Fired s fired) post__sum -> 
         
         (* [∑ pre(p,t) = σ__p("s_input_token_sum")]. *)
         MapsTo s_input_token_sum (Vnat post__sum) (sstore σ__p)).

(** Defines the relation stating that an SITPN execution environment
    and a H-VHDL design execution environment described the same
    behavior.

    - The environment [Ec] provides boolean values to the conditions
    of [sitpn] depending on the cycle count [τ] 
    
    - The environment [Ep] provides values (must be boolean) to the input
    ports of design [d] that implements the conditions of [sitpn].
 *)

Definition SimEnv sitpn (γ : Sitpn2HVhdlMap sitpn) (E__c : nat -> C sitpn -> bool) (E__p : nat -> IdMap value) : Prop :=
  forall τ c id__c,
    (* [γ(c) = id__c] *)
    InA Ckeq (c, id__c) (c2in γ)  ->
    (* [E__p(τ)(id__c) = E__c(τ)(c)] *)
    MapsTo id__c (Vbool (E__c τ c)) (E__p τ).

(** States that two execution trace are similar. The first list
    argument is the execution trace of an SITPN and the second list
    argument is the execution trace of a VHDL design.
    
    By construction, and in order to be similar, the two traces must
    have the same length, and must have pair-wise similar states. *)

Inductive SimTrace {sitpn} γ : list (SitpnState sitpn) -> list DState -> Clk -> Prop :=
| SimTraceInit: forall clk, SimTrace γ nil nil clk
                                     
| SimTraceRE: forall s σ θ__s θ__σ,
    SimStateAfterRE sitpn γ s σ -> 
    SimTrace γ θ__s θ__σ fe ->
    SimTrace γ (s :: θ__s) (σ :: θ__σ) re
             
| SimTraceFE: forall s σ θ__s θ__σ,
    SimStateAfterFE sitpn γ s σ -> 
    SimTrace γ θ__s θ__σ re ->
    SimTrace γ (s :: θ__s) (σ :: θ__σ) fe.

#[export] Hint Constructors SimTrace : core.

(** States that two execution trace are fully similar. The first
    states of each trace must verify the general state similarity
    relation, and the tail traces must verify the execution trace
    similarity relation.
    
    The [FullSimTrace] relation permits us to express the similarity
    between two traces where the head states of traces are initial
    states. *)

Inductive FullSimTrace {sitpn} γ : list (SitpnState sitpn) -> list DState -> Prop :=
| FullSimTraceInit: FullSimTrace γ nil nil
                                     
| FullSimTraceCons: forall s σ θ__s θ__σ,
    SimState sitpn γ s σ ->
    SimTrace γ θ__s θ__σ re ->
    FullSimTrace γ (s :: θ__s) (σ :: θ__σ).

#[export] Hint Constructors FullSimTrace : core.

