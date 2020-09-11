(** * Semantic Preservation Theorem *)

Require Import GlobalTypes.
Require Import SitpnSemanticsDefs.

(* SITPN Libraries *)

Require Import dp.SitpnTypes.
Require Import dp.Sitpn.
Require Import dp.SitpnSemantics.
Require Import dp.Fired.

(* H-VHDL Libraries *)

Require Import HVhdlTypes.
Require Import Environment.
Require Import SemanticalDomains.
Require Import Simulation.
Require Import CombinationalEvaluation.
Require Import SynchronousEvaluation.
Require Import DesignElaboration.
Require Import AbstractSyntax.
Require Import HilecopDesignStore.
Require Import Initialization.
Require Import Stabilize.

(* SITPN to H-VHDL Libraries *)

Require Import GenerateHVhdl.

(* Specific Tactics. *)

Require Import Coq.Program.Equality.

(** Defines the relation stating that an SITPN execution environment
    and a H-VHDL design execution environment described the same
    behavior.

    - The environment [Ec] provides boolean values to the conditions
    of [sitpn] depending on the cycle count [tau] 
    
    - The environment [Ep] provides values (must be boolean) to the input
    ports of design [d] that implements the conditions of [sitpn].
*)

Definition EnvEq sitpn (Ec : nat -> C sitpn -> bool) (Ep : nat -> Clk -> IdMap value) : Prop := False.

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

Local Notation "γ ⊢ s '∼' σ" := (SimState γ s σ) (at level 50).

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

(** ** Rising edge marking equal lemma

    States that starting from similar state, markings are equal
    after the rising edge of the clock signal.  *)

Lemma rising_edge_marking_equal :
  forall Δ σ__r d θ σ' σ sitpn Ec τ s s' mm γ,

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Similar starting states *)
    γ ⊢ s ∼ σ ->
    
    (* Rising edge from s to s', s ⇝↑ s' *)
    SitpnStateTransition Ec τ s s' rising_edge -> 

    (* Rising edge from σ to σr *)
    vrising Δ σ (get_behavior d) σ__r -> 

    (* Stabilize from σr to σ' *)
    stabilize Δ σ__r (get_behavior d) θ σ' ->
    
    (* Conclusion *)
    forall p id__p σ'__p,
      (* [idp] is the identifier of the place component associated with
       place [p] by the [γ] binder. *)
      γ (inl p) = id__p ->

      (* [σp] is the current state of component [idp] is the global design
       state [σ]. *)
      MapsTo id__p σ'__p (compstore σ') ->

      (* Marking of place [p] at state [s] equals value of signal
         [s_marking] at state [σp]. *)
      MapsTo Place.s_marking (Vnat (@M sitpn s' p)) (sigstore σ'__p).
Proof.
Admitted.

(** ** Rising edge states equal.
 
    Utopic lemma; not sure it is provable. *)

Lemma rising_edge_states_equal :
  forall Δ σ__r d θ σ' σ sitpn E__c τ s s' mm (γ : P sitpn + T sitpn -> ident),

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Similar starting states *)
    γ ⊢ s ∼ σ ->
    
    (* Rising edge from s to s', s ⇝↑ s' *)
    SitpnStateTransition E__c τ s s' rising_edge -> 

    (* Rising edge from σ to σr *)
    vrising Δ σ (get_behavior d) σ__r -> 

    (* Stabilize from σr to σ' *)
    stabilize Δ σ__r (get_behavior d) θ σ' ->
    
    (* Conclusion *)
    γ ⊢ s' ∼ σ'.
Proof.
Admitted.

(** ** Falling edge compute fired lemma

    States that starting from similar state, after the falling edge of
    the clock signal, all fired transitions are associated with
    transition components with a fired out port valuated to true (or
    false otherwise).  *)

Lemma falling_edge_compute_fired_aux :
  
  forall sitpn s lofT fset t,
    
    (* t ∈ fired(s) *)
    @IsFiredListAux sitpn s lofT (M s) nil fset ->
    List.In t fset ->
    @Set_in_List (T sitpn) lofT ->

    False.
Proof.
  intros sitpn s lofT fset t Hfired; induction Hfired.
  - intros Hin_fired Hset_in_l.
    inversion_clear Hset_in_l as (Hin_T, Hnodup).
    specialize (Hin_T t); contradiction.
  - intros Hin_f'' Hset_in_l; specialize (IHHfired Hin_f'').
    apply IHHfired.
    unfold Set_in_List in *.
    split.
    + unfold IsDiff in H1.
      inversion_clear Hset_in_l as (Hall_in_T, Hnodup).
      admit.
    + inversion_clear Hset_in_l as (Hall_in_T, Hnodup).
      induction Hnodup.
      -- specialize (Hall_in_T t); contradiction.
      -- apply List.NoDup_cons.
         ++ 
    (* forall d mm Δ σ θ σ' (γ : (P sitpn) + (T sitpn) -> ident) id__t σ'__t, *)
      
    (* (* sitpn translates into d. *) *)
    (* sitpn_to_hvhdl sitpn mm = Success d -> *)
    
    (* (* Stabilize from σf to σ' *) *)
    (* stabilize Δ σ (get_behavior d) θ σ' -> *)
    
    (* (** Component idt implements transition t *) *)
    (* γ (inr t) = id__t -> *)

    (* (* σ't is the state of component idt at design's state σ'. *) *)
    (* MapsTo id__t σ'__t (compstore σ') -> *)

    (* (* Conclusion *) *)

    (* (* σ't(fired) = true *) *)
    (* MapsTo Transition.fired (Vbool true) (sigstore σ'__t). *)
Proof.
  induction 3.
  - admit.
  -
  intros sitpn mm d s fset t Hfired.
  inversion_clear Hfired as (His_fset, Hin_fset).
  inversion_clear His_fset as (Tlist, His_fset_aux).
  dependent induction His_fset_aux.

  (* Base case *)
  - contradiction.
  - apply (IHHis_fset_aux Hin_fset).
Admitted.
     
Lemma falling_edge_compute_fired :
  forall Δ σ__f d θ σ' σ sitpn Ec τ s s' mm γ id__t σ'__t,

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Similar starting states *)
    γ ⊢ s ∼ σ ->
    
    (* Falling edge from s to s', s ⇝↓ s' *)
    SitpnStateTransition Ec τ s s' falling_edge -> 

    (* Falling edge from σ to σf *)
    vfalling Δ σ (get_behavior d) σ__f -> 

    (* Stabilize from σf to σ' *)
    stabilize Δ σ__f (get_behavior d) θ σ' ->
    
    (* Conclusion *)
    forall fset t,
      (** Component idt implements transition t *)
      γ (inr t) = id__t ->

      (* σ't is the state of component idt at design's state σ'. *)
      MapsTo id__t σ'__t (compstore σ') ->

      (* Conclusion *)
      @Fired sitpn s' fset t ->
      MapsTo Transition.fired (Vbool true) (sigstore σ'__t).
Proof.
  intros
  inversion_clear H6.
  inversion_clear H7.
  dependent induction H6.
  - contradiction.
  - induction H8.
    generalize (H8 t).
Admitted.  

(** ** Falling edge states equal.
 
    Utopic lemma; not sure it is provable. *)

Lemma falling_edge_states_equal :
  forall Δ σ__f d θ σ' σ sitpn Ec τ s s' mm (γ : P sitpn + T sitpn -> ident),

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Similar starting states *)
    γ ⊢ s ∼ σ ->
    
    (* Falling edge from s to s', s ⇝↓ s' *)
    SitpnStateTransition Ec τ s s' falling_edge -> 

    (* Falling edge from σ to σf *)
    vfalling Δ σ (get_behavior d) σ__f -> 

    (* Stabilize from σf to σ' *)
    stabilize Δ σ__f (get_behavior d) θ σ' ->

    (* Conclusion *)
    γ ⊢ s' ∼ σ'.
Proof.
Admitted.

(** ** Step lemma
    
    States that starting from similar state, state are similar after
    one execution cycle.

 *)

Lemma step_lemma :
  forall sitpn mm d s s' E__c σ σ' Δ Mg σ__e P__i τ γ,
    
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Starting states are similar *)
    γ ⊢ s ∼ σ ->

    (* Δ, σ are the results of the elaboration of d. *)
    edesign hdstore Mg d Δ σ__e ->
    
    (* One execution cycle for SITPN *)
    
    @SitpnCycle sitpn E__c τ s s' ->

    (* One execution cycle for VHDL *)
    simcycle P__i Δ τ σ (get_behavior d) σ' ->
     
    (* Final states are similar *)
    γ ⊢ s' ∼ σ'.
Proof.
  intros *; intros Htransl Hsim Helab Hsitpn_cyc Hhdl_cyc.
  unfold SitpnCycle in Hsitpn_cyc.
  inversion_clear Hsitpn_cyc as (s__i & (Hrising, Hfalling)).
  inversion_clear Hhdl_cyc as
      (σ__injr, σ__r, σ__i, σ__injf, σ__f, σ'', θ, θ',
       Hhdl_rising, Hstab_rising, Hhdl_falling, Hstab_falling, Hinj_rising, Hinj_falling).

  (* Must prove s similar to σ after capture of input values on rising edge. 
     Necessary premise to apply [rising_edge_states_equal].      
   *)
  cut (γ ⊢ s ∼ σ__injr); intros Hsim_injr.
  specialize (rising_edge_states_equal
           Δ σ__r d θ σ__i σ__injr sitpn E__c τ s s__i mm γ
           Htransl Hsim_injr Hrising Hhdl_rising Hstab_rising); intros Heq_int_states.

  (* Must prove s similar to σ after capture of input values on falling edge. 
     Necessary premise to apply [falling_edge_states_equal].
   *)
  cut (γ ⊢ s__i ∼ σ__injf); intros Hsim_injf.
  apply (falling_edge_states_equal Δ σ__f d θ' σ' σ__injf sitpn E__c τ s__i s' mm γ
                                   Htransl Hsim_injf Hfalling Hhdl_falling Hstab_falling).
  
  - admit.
  - admit.
Admitted.

(** ** Equal Initial States  *)

Lemma init_states_sim :
  forall sitpn mm d Mg Δ σ__e σ0 γ,
    
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* ed, dstate are the results of the elaboration of d. *)
    edesign hdstore Mg d Δ σ__e ->

    (* initialization d's state. *)
    init Δ σ__e (get_behavior d) σ0 ->

    (* init states are similar *)
    γ ⊢ (s0 sitpn) ∼ σ0.
Proof.
  intros *; intros Htransl Helab Hinit.
  inversion_clear Hinit as (σ, beh, σ', σ'', θ, Hruninit, Hstab).

Admitted.
  
(** ** Simulation Lemma *)

Lemma simulation_lemma :
  
  forall sitpn Ec τ s θ__s s',

    (* From state s to state s' after τ execution cycles, and
       producing trace θs. *)
    SitpnExecute Ec s τ θ__s s' ->

    forall d mm Ep Mg Δ σ__e θ__σ σ σ' γ,
      
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* Environments are similar. *)
    EnvEq sitpn Ec Ep ->

    (* Δ, σe are the results of the elaboration of d. *)
    edesign hdstore Mg d Δ σ__e ->

    (* States s and σ are similar; *)
    γ ⊢ s ∼ σ ->
    
    (* From σ to σ' after τ execution cycles, producing trace θσ. *)
    simloop Ep Δ σ (get_behavior d) τ θ__σ σ' ->

    (* Conclusion *)
    SimTrace γ θ__s θ__σ.
Proof.
  intros *; intros Hexec; dependent induction Hexec;
  intros *; intros Htransl Henveq Helab Hsimstate Hsim.
  
  (* CASE tau = 0, trivial. *)
  - inversion Hsim; apply SimTraceInit.

  (* CASE tau > 0 *)
  - inversion_clear Hsim as [ τ0 σ0 σ'0 θ0 Hcyc Hsiml |  ].
    
    (* Specializes the induction hypothesis, then apply the step lemma. *)
    
    specialize (IHHexec d mm Ep Mg Δ σ__e θ0 σ0 σ').
    specialize (IHHexec γ Htransl Henveq Helab).

    (* Then, we need a lemma stating that s' ∼ σ0. That is, state are
       similar after one execution cycle. *)

    specialize (step_lemma sitpn mm d s s' Ec σ σ0 Δ Mg σ__e Ep (S tau) γ
                           Htransl Hsimstate Helab H Hcyc)
      as Heq_state_cyc.

    (* Solve the induction case. *)
    apply (@SimTraceCons sitpn γ s' σ0 θ θ0);
      [ assumption | apply (IHHexec Heq_state_cyc Hsiml)].
Qed.

(** ** Semantic Preservation Theorem *)

Theorem sitpn2vhdl_sound :
  forall sitpn E__c τ θ__s s' d Mg E__p σ' mm Δ σ__e σ0 θ__σ γ,
      
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* (* Environments are similar. *) *)
    EnvEq sitpn E__c E__p ->

    (* sitpn is in state s' after τ execution cycles and yields
       exec. trace θs. *)
    
    SitpnExecute E__c (s0 sitpn) τ θ__s s' ->    
    
    (* Design elaboration *)
    edesign hdstore Mg d Δ σ__e ->
    
    (* Initialization of design state *)
    init Δ σ__e (get_behavior d) σ0 ->

    (* Simulation of design *)
    simloop E__p Δ σ0 (get_behavior d) τ θ__σ σ' ->
    
    (* ** Conclusion: exec. traces are equal. ** *)
    SimTrace γ θ__s θ__σ.
Proof.
  intros.

  lazymatch goal with
  | [
    Htransl: sitpn_to_hvhdl _ _ = Success _,
    Henveq: EnvEq _ _ _,
    Hsitpnexec: SitpnExecute _ _ _ _ _,
    Helab: edesign _ _ _ _ _,
    Hinit: init _ _ _ _,
    Hsimloop: simloop _ _ _ _ _ _ _
    |- _ ] =>
    specialize (init_states_sim sitpn mm d Mg Δ σ__e σ0 γ Htransl Helab Hinit) as Hinit_eq;
      apply (simulation_lemma
               sitpn E__c τ (s0 sitpn) θ__s s' Hsitpnexec d mm E__p Mg Δ σ__e θ__σ σ0 σ' γ
               Htransl Henveq Helab Hinit_eq Hsimloop)
  end.

Qed.
    
