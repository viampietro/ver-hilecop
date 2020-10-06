(** * Facts about Falling Edge and the Soundness Proof *)

Require Import Coqlib.
Require Import ListsPlus.
Require Import common.GlobalTypes.

Require Import dp.Sitpn.
Require Import dp.SitpnSemanticsDefs.
Require Import dp.Fired.
Require Import dp.SitpnSemantics.
Require Import dp.SitpnTypes.

Require Import HVhdlTypes.
Require Import SemanticalDomains.
Require Import Environment.
Require Import HilecopDesignStore.
Require Import hvhdl.Stabilize.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.SynchronousEvaluation.

Require Import GenerateHVhdl.

Require Import SoundnessDefs.

(** ** Falling edge compute fired lemma *)

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

      (forall s, exists θ' v,
          θ' <> []
          /\ LeListCons θ' θ 
          /\ forall σ__j, List.In σ__j θ' -> MapsTo s v (sigstore σ__j))
      \/ σ = σ' ->
      
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
    
    forall m fired tp m' fired',

      (* All transitions of the fired list verify the conclusion *)
      (forall t,
          List.In t fired ->
          γ (inr t) = id__t ->
          MapsTo id__t σ'__t (compstore σ') ->
          MapsTo Transition.fired (Vbool true) (sigstore σ'__t)) ->

      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t => List.In t fired) (M s') m ->

      (* Elect transitions to be fired from the [tp] list *)
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
