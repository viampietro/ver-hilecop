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
Require Import hvhdl.TransitionFacts.

Require Import GenerateHVhdl.

Require Import SoundnessDefs.

(** ** Falling edge compute fired lemma *)

(** *** Falling edge compute fired: σ'__t(fired) = false ⇒ t ∉ fired(s') *)

(** *** Falling edge compute fired: σ'__t(fired) = true ⇒ t ∈ fired(s') *)

(** *** Falling edge compute fired: t ∉ fired(s') ⇒ σ'__t(fired) = false *)

(* States that starting from similar state, after the falling edge of
    the clock signal, all transitions that are not fired are
    associated with transition components with a fired out port
    valuated to false. *)

Lemma falling_edge_compute_not_fired_aux :
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
          γ (inr t) = id__t ->
          MapsTo id__t σ'__t (compstore σ') ->
          ~List.In t fired /\ ~List.In t lofT ->
          MapsTo Transition.fired (Vbool false) (sigstore σ'__t)) ->
      
      (* t ∈ fired(s') *)
      @IsFiredListAux sitpn s' m fired lofT fset ->
      
      forall t,
        
        (** Component idt implements transition t *)
        γ (inr t) = id__t ->

        (* σ't is the state of component idt at design's state σ'. *)
        MapsTo id__t σ'__t (compstore σ') ->
        
        (* t ∉ fired(s') *)
        ~List.In t fset ->
        
        (* Conclusion: σ't(fired) = false *)
        MapsTo Transition.fired (Vbool false) (sigstore σ'__t).
Proof.
  intros Δ σ__f d θ σ' σ sitpn Ec τ s s' mm γ id__t σ'__t
         Htransl Hsim Hfalling Hfall_hdl Hstab
         Tlist m fired lofT fset
         HTlist Hincl Hnodup Hresm Hcompute_not_fired Hfired_aux. 
  induction Hfired_aux.

  (* BASE CASE *)
  - assert (Hnot_in_nil: ~List.In t []) by inversion 1.
    intros t Hbind_t Hσ'__t Hnot_in_fired;
      apply (Hcompute_not_fired t Hbind_t Hσ'__t (conj Hnot_in_fired Hnot_in_nil)).
    
  (* IND. CASE *)
  - intros t Hbind_t Hσ'__t; apply IHHfired_aux; auto.
    
    (* CASE incl in Tlist *)
    + admit.

    (* CASE no duplicate  *)
    + admit.
      
    (* CASE elect fired compute residual *)
    + admit.

    (* CASE elect fired discard not fired *)
    + admit.
      
Admitted.

(** *** Falling edge compute fired: t ∈ fired(s') ⇒ σ'__t(fired) = true *)

(* ∀ t ∈ firable(s') ⇒ σ't(s_firable) = true *)

Lemma falling_edge_compute_firable : 
  forall Δ σ__f d θ σ' σ sitpn Ec τ s s' mm γ,

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
    (forall t id__t σ'__t,
        γ (inr t) = id__t ->
        MapsTo id__t σ'__t (compstore σ') ->
        @Firable sitpn s' t ->
        MapsTo Transition.s_firable (Vbool true) (sigstore σ'__t)).
Admitted.

(* All transitions that are sensitized by the residual marking have an
   input port "priority_authorizations" of type boolean vector with
   all its subelements set to true.  *)

Lemma stabilize_compute_auth_after_falling :
  forall sitpn mm d Δ σ θ σ' s' (γ : P sitpn + T sitpn -> ident),

    (* Stabilize from σf to σ' *)
    stabilize Δ σ (get_behavior d) θ σ' ->
    
    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->
    
    (* Conclusion *)
    
    forall t id__t σ'__t m fired fset lofbool,

      (** Component idt implements transition t *)
      γ (inr t) = id__t ->

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
      
      (* Conclusion *)
      
      MapsTo Transition.priority_authorizations (Vlist lofbool) (sigstore σ'__t) ->
      forall i v, get_at i lofbool = Some v -> v = Vbool true.
Admitted.

(*  *)

Lemma stabilize_compute_priority_after_falling :
  forall sitpn mm d Δ σ θ σ' s' (γ : P sitpn + T sitpn -> ident),
    
    (* Stabilize from σf to σ' *)
    stabilize Δ σ (get_behavior d) θ σ' ->

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->
    
    (* Conclusion *)
    
    forall id__t σ'__t t m fired fset,

      (** Component idt implements transition t *)
      γ (inr t) = id__t ->
      
      (* σ't is the state of component idt at design's state σ'. *)
      MapsTo id__t σ'__t (compstore σ') ->
      
      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t' => List.In t' fired) (M s') m ->

      (* [fset] is the list of fired transitions *)
      IsFiredList s' fset ->
      
      (* fired ≡ { t' | t' ≻ t ∧ t' ∈ fired(s') } *)
      (forall t', List.In t' fired -> t' >~ t = true /\ List.In t' fset) ->

      (* All transitions of the fired list verify "fired" port
         equals true at σ' *)
      (forall t' id__t' σ'__t',
          List.In t' fired ->
          γ (inr t') = id__t' ->
          MapsTo id__t' σ'__t' (compstore σ') ->
          MapsTo Transition.fired (Vbool true) (sigstore σ'__t')) ->
      
      (* t ∈ sens(m) *)
      @Sens sitpn m t ->
      
      (* σ't("s_priority_combination") = true *)
      MapsTo Transition.s_priority_combination (Vbool true) (sigstore σ'__t).
Proof.
Admitted.

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
      
    (* Use [falling_edge_compute_firable] and [stabilize_compute_priority_after_falling] to solve the subgoal *)
    + singleton_eq; rewrite Heq in *.

      (* Specialize [falling_edge_compute_firable] *)
      lazymatch goal with
      | [ H: Firable _ _ |- _ ] =>
        specialize (falling_edge_compute_firable
                      Δ σ__f d θ σ' σ sitpn Ec τ s s' mm γ
                      Htransl Hsim Hfalling Hfall_hdl Hstab
                      t' id__t σ'__t Hbind_t' Hid__t H) as Hfirable
      end.

      (* Specialize [stabilize_compute_priority_after_falling] *)
      assert (Hprio_comb: MapsTo Transition.s_priority_combination (Vbool true) (sigstore σ'__t)) by admit.

      (* Specialize [fired_assign_on_stabilize] with Hfirable and Hprio_comb *)
      assert (Hfired_assign: MapsTo Transition.fired (Vbool true) (sigstore σ'__t)) by admit.

      assumption.
      
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
