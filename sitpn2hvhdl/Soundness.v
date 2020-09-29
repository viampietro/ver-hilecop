(** * Semantic Preservation Theorem *)

Require Import NatMap.

Require Import Coqlib.
Require Import InAndNoDup.
Require Import GlobalTypes.
Require Import ListsPlus.
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
Require Import PortMapEvaluation.

(* SITPN to H-VHDL Libraries *)

Require Import GenerateHVhdl.

(* Facts about NatMap. *)

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

(** ** Falling edge compute fired lemma *)

(*  *)

(* All signals get a stable value at a certain point of the
   stabilization trace. *)

Lemma stable_value_signal :
  forall θ Δ σ behavior σ',
    stabilize Δ σ behavior θ σ' ->
    forall s,
      (exists v, MapsTo s v (sigstore σ)) ->
      (exists θ' v,
          (θ' <> [] \/ σ = σ') 
          /\ LeListCons θ' θ 
          /\ forall σ__j, List.In σ__j θ' -> MapsTo s v (sigstore σ__j)).
Proof.
  
  induction 1; intros s Hx_sval.

  (* BASE CASE *)
  - exists nil.
    inversion_clear Hx_sval as (v, Hmaps).
    exists v.
    split; [ right; reflexivity |
             split; [apply LeListCons_refl |
                     contradiction
                    ]
           ].

  (* IND. CASE *)
  - lazymatch goal with
    | [ Hvcomb: vcomb _ _ _ _, H: (exists v, MapsTo s v (sigstore σ)) |- _ ] =>

      (* s has a value at σ' *)
      inversion_clear H as (v, Hmaps);
        specialize (comb_maps_sigid Δ σ behavior σ' s v Hvcomb Hmaps) as Hex_v'
    end.

    specialize (IHstabilize s Hex_v').
    inversion_clear IHstabilize as (θ', Hx); inversion_clear Hx as (v'', Hw).
    decompose [and] Hw.

    (* 2 CASES: θ' <> [] or σ' = σ'' *)
    lazymatch goal with
    | [ H: θ' <> [] \/ σ' = σ'' |- _ ] =>
      inversion_clear H as [Hnotnil | Heq_σ']
    end.

    (* CASE θ' <> [] 
       Instantiates θ' and v with the values coming from the IH, then trivial
     *)
    
    + exists θ', v'';
        split; [left; assumption |
                split; [ apply LeListCons_cons; assumption | assumption]
               ].

    (* CASE σ' = σ''

       Means that θ = [], otherwise contradicts the fact that σ' has
       an empty event set. *)
      
    + lazymatch goal with
      | [ H: stabilize _ _ _ _ _ |- _ ] =>
        inversion H
      end.

      (* CASE θ = [] 
         Then, there is but one non-empty trace θ' verifying
         θ' <= [σ''], that is θ' = [σ'']
       *)
      -- exists [σ'']; inversion_clear Hex_v' as (v', Hmaps'); exists v'.
         
         (* Solves [σ''] <> [] \/ σ = σ'' *)
         split; [ left; inversion 1 | auto].

         (* Solves LeListCons [σ''] [σ''] *)
         split; [ apply LeListCons_refl | auto].

         (* Solves ∀ σj, σj ∈ [σ''] -> σj(s) = v' 
            There's only one σj verifying σj ∈ [σ''].
          *)
         intros σ__j Hin; inversion_clear Hin as [Heq_σ'' | ];
           [rewrite <- Heq_σ''; rewrite <- Heq_σ'; assumption |
            contradiction].

      (* CASE θ non-empty, then contradiction *)
      -- lazymatch goal with
         | [ H: events σ' <> _ |- _ ] =>
           rewrite Heq_σ' in H; contradiction
         end.
Qed.

(*  *)

Lemma stabilize_compute_auth :
  forall sitpn mm d Δ σ θ σ' s' (γ : P sitpn + T sitpn -> ident),

    (* Stabilize from σf to σ' *)
    stabilize Δ σ (get_behavior d) θ σ' ->
    
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->
    
    (* Conclusion *)
    
    forall id__t t m fired fset,

      (** Component idt implements transition t *)
      γ (inr t) = id__t ->
            
      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t' => List.In t' fired) (M s') m ->

      (* [fset] is the list of fired transitions *)
      IsFiredList s' fset ->
      
      (* fired ≡ { t' | t' ≻ t ∧ t' ∈ fired(s') } *)
      (forall t', List.In t' fired -> t' >~ t = true /\ List.In t' fset) ->

      (* t ∈ sens(m) *)
      @Sens sitpn m t ->

      forall s, exists θ' v,
          LeListCons θ' θ 
          /\ forall σ__j, List.In σ__j θ' -> MapsTo s v (sigstore σ__j) ->
      
      (* Conclusion *)
      
      exists θ',
        LeListCons θ' θ
        /\ forall σ__j σ__jt lofbool,
          List.In σ__j θ' ->
          MapsTo id__t σ__jt (compstore σ__j) ->
          MapsTo Transition.priority_authorizations (Vlist lofbool) (sigstore σ__jt) ->
          forall i v, get_at i lofbool = Some v -> v = Vbool true.
Proof.
Admitted.

(*  *)

Lemma stabilize_compute_priority :
  forall sitpn mm d Δ σ θ σ' s' (γ : P sitpn + T sitpn -> ident),
    
    (* Stabilize from σf to σ' *)
    stabilize Δ σ (get_behavior d) θ σ' ->

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->
    
    (* Conclusion *)
    
    forall id__t σ__t σ'__t t m fired fset,

      (** Component idt implements transition t *)
      γ (inr t) = id__t ->

      (* σt is the state of component idt at design's state σ. *)
      MapsTo id__t σ__t (compstore σ) ->
      
      (* σ't is the state of component idt at design's state σ'. *)
      MapsTo id__t σ'__t (compstore σ') ->
      
      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t' => List.In t' fired) (M s') m ->

      (* [fset] is the list of fired transitions *)
      IsFiredList s' fset ->
      
      (* fired ≡ { t' | t' ≻ t ∧ t' ∈ fired(s') } *)
      (forall t', List.In t' fired -> t' >~ t = true /\ List.In t' fset) ->

      (* t ∈ sens(m) *)
      @Sens sitpn m t ->
      
      (* Signal σ't("s_priority_combination") = true *)
      exists θ',
        LeListCons θ' θ
        /\ forall σ__i σ__it,
          List.In σ__i θ' ->
          MapsTo id__t σ__it (compstore σ__i) ->
          MapsTo Transition.s_priority_combination (Vbool true) (sigstore σ__it).
Proof.
  induction 1.

  (* BASE CASE, θ = [] *)
  - exists nil.
    split; [apply LeListCons_refl | contradiction].
    
  (* IND. CASE *)
  - intros Htransl id__t σ__t σ''__t t m fired fset Hbind_t Hσ__t Hσ''__t Hresm Hfiredl Hprt Hsens.

    (** Need a lemma saying: 
        σ ⇝ σ' ⇒ σ(idt) = σt ⇒ ∃σ't, σ'(idt) = σ't 
        where ⇝ is an "execution" relation between σ and σ'.
     *)

    lazymatch goal with
    | [ Hvcomb: vcomb _ _ _ _, Hσ__t: MapsTo id__t σ__t (compstore σ) |- _ ] =>
      specialize (comb_maps_id Δ σ behavior σ' id__t σ__t Hvcomb Hσ__t) as Hex_σ'__t;
        inversion_clear Hex_σ'__t as (σ'__t, Hσ'__t)
    end.

    (* Specialize and use the induction hypothesis *)
    
    specialize (IHstabilize Htransl id__t σ'__t σ''__t t m fired fset Hbind_t Hσ'__t Hσ''__t Hresm Hfiredl Hprt Hsens).
    inversion_clear IHstabilize as (θ', Hw); inversion_clear Hw as (Hle, Hprio_comb_true).
    exists θ'; split; [ apply LeListCons_cons; assumption | assumption].
Qed.

(* All transitions that are in the list of transitions elected to be
   fired - at state [s'] and considering the residual marking [m] -
   have a bounded transition component (binding through γ) with a
   "fired" port set to true at state σ'. *)

Lemma elect_fired_compute_fired :
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
    
    forall m fired  tp m' fired',

      (* All transitions of the fired list verify the conclusion *)
      (forall t,
          List.In t fired ->
          γ (inr t) = id__t ->
          MapsTo id__t σ'__t (compstore σ') ->
          MapsTo Transition.fired (Vbool true) (sigstore σ'__t)) ->

      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t => List.In t fired) (M s') m ->

      @ElectFired sitpn s' m fired tp (m', fired') ->
      
      forall t,
        List.In t fired' ->
      
        (** Component idt implements transition t *)
        γ (inr t) = id__t ->

        (* σ't is the state of component idt at design's state σ'. *)
        MapsTo id__t σ'__t (compstore σ') ->

        (* Conclusion *)
        MapsTo Transition.fired (Vbool true) (sigstore σ'__t).
Proof.
  intros *;
    intros Htransl Hsim Hfalling Hfall_hdl Hstab;
    intros m fired tp m' fired' Hin_fired_compute Hresm Helect;
    dependent induction Helect;

    (* BASE CASE *)
    auto;

    (* IND. CASES *)
    (* [auto] solves the case where (t ∉ firable(s) or t ∉ sens(m)) *)
    apply IHHelect with (Ec := Ec) (s := s) (γ := γ) (m'0 := m') (fired'0 := fired'); auto.

  (* CASE t ∈ firable(s) ∧ t ∈ sens(m) *)

  (* ∀ t' ∈ fired ++ [t] → C *)
  - intros t' Hin_app Hbind_t' Hid__t; destruct_in_app_or.
    
    (* Case t ∈ fired *)
    + apply Hin_fired_compute with (t := t'); auto.
    
    (* Case t = t' *)
    (* Use [falling_compute_firable] and [stabilize_compute_priority] to solve the subgoal *)
    + singleton_eq. admit.

  (* CASE msub = M s' - ∑ pre(ti), ∀ ti ∈ fired ++ [t] *)
  - admit.
    
Admitted.
  
(*  States that starting from similar state, after the falling edge of
    the clock signal, all fired transitions are associated with
    transition components with a fired out port valuated to true (or
    false otherwise). *)

Lemma falling_edge_compute_fired_aux :
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
    
    forall Tlist m fired lofT fset,

      (* Tlist implements the set of transitions T *)
      Set_in_List Tlist ->
      
      (* (fired ++ lofT) is a permutation of Tlist *)
      incl (fired ++ lofT) Tlist ->

      (* No duplicate in (fired ++ lofT) *)
      NoDup (fired ++ lofT) ->

      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t : T sitpn => List.In t fired) (M s') m -> 

      (* All transitions of the fired list verify the conclusion *)
      (forall t,
          List.In t fired ->
          γ (inr t) = id__t ->
          MapsTo id__t σ'__t (compstore σ') ->
          MapsTo Transition.fired (Vbool true) (sigstore σ'__t)) ->
      
      (* t ∈ fired(s') *)
      @IsFiredListAux sitpn s' m fired lofT fset ->
      
      forall t,
        List.In t fset ->
      
        (** Component idt implements transition t *)
        γ (inr t) = id__t ->

        (* σ't is the state of component idt at design's state σ'. *)
        MapsTo id__t σ'__t (compstore σ') ->

        (* Conclusion *)
        MapsTo Transition.fired (Vbool true) (sigstore σ'__t).
Proof.
  intros Δ σ__f d θ σ' σ sitpn Ec τ s s' mm γ id__t σ'__t
         Htransl Hsim Hfalling Hfall_hdl Hstab
         Tlist m fired lofT fset
         HTlist Hincl Hnodup Hresm Hin_fired_compute Hfired_aux. 
  induction Hfired_aux.

  (* BASE CASE *)
  - assumption.

  (* IND. CASE *)
  - apply IHHfired_aux.

    (* CASE incl in Tlist *)
    + admit.

    (* CASE no duplicate  *)
    + admit.
      
    (* CASE elect fired compute residual *)
    + admit.

    (* CASE elect fired compute fired *)
    + eapply (elect_fired_compute_fired); eauto.
      
Admitted.  

(*  Corollary of the [falling_edge_compute_fired_aux] lemma.

    States that starting from similar state, after the falling edge of
    the clock signal, all fired transitions are associated with
    transition components with a fired out port valuated to true (or
    false otherwise). *)

Lemma falling_edge_compute_fired_list :
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
    
    forall fset,
      
      (* t ∈ fired(s') *)
      @IsFiredList sitpn s' fset ->
      
      forall t,
        List.In t fset ->
        
        (** Component idt implements transition t *)
        γ (inr t) = id__t ->

        (* σ't is the state of component idt at design's state σ'. *)
        MapsTo id__t σ'__t (compstore σ') ->

        (* Conclusion *)
        MapsTo Transition.fired (Vbool true) (sigstore σ'__t).
Proof.
  intros until t0;
    lazymatch goal with
    | [ H: IsFiredList _ _ |- _ ] =>
      inversion H;
        eapply falling_edge_compute_fired_aux;
        eauto    
    end.

  (* incl ([] ++ Tlist) Tlist *)
  - apply incl_refl.

  (* NoDup ([] ++ Tlist) *)
  - lazymatch goal with
    | [ H: Set_in_List Tlist |- _ ] =>
      inversion H; assumption
    end.
    
  (* M s' = M s' - ∑ pre(ti), ∀ ti ∈ [] *)
  - apply MarkingSubPreSum_;
      inversion_clear 1;
      lazymatch goal with
      | [ H: PreSumList _ _ _ _ |- _ ] =>
        inversion H; [omega |
                      lazymatch goal with
                      | [ t : { _ : T sitpn | _ } |- _ ] =>
                        assert (Hfalse := proj2_sig t); contradiction
                      end
                     ]
      end.
  
  (* ∀ t ∈ [] ⇒ C *)
  - contradiction.

Qed.

(*  Corollary of the [falling_edge_compute_fired_list] lemma. *)

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
      
      (* t ∈ fired(s') *)
      @Fired sitpn s' fset t ->
        
      (** Component idt implements transition t *)
      γ (inr t) = id__t ->

      (* σ't is the state of component idt at design's state σ'. *)
      MapsTo id__t σ'__t (compstore σ') ->

      (* Conclusion *)
      MapsTo Transition.fired (Vbool true) (sigstore σ'__t).
Proof.
  intros;
    lazymatch goal with
    | [ H: Fired _ _ _ |- _ ] =>
      inversion H;
        eapply falling_edge_compute_fired_list;
        eauto
    end.
Qed.
  
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
    
