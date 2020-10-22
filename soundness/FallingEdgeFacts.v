(** * Facts about Falling Edge and the Soundness Proof *)

Require Import common.Coqlib.
Require Import common.ListsPlus.
Require Import common.GlobalTypes.
Require Import SetoidList.

Require Import dp.Sitpn.
Require Import dp.SitpnSemanticsDefs.
Require Import dp.Fired.
Require Import dp.SitpnSemantics.
Require Import dp.SitpnTypes.
Require Import dp.SitpnFacts.
Require Import dp.FiredFacts.

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

(** ** Facts about Falling Edge and Firable *)

(* [∀ t ∈ firable(s') ⇒ σ'__t("s_firable") = true] *)

Lemma falling_edge_compute_s_firable_true : 
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

(* [∀ t ∉ firable(s') ⇒ σ'__t("s_firable") = false] *)

Lemma falling_edge_compute_s_firable_false : 
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
        ~@Firable sitpn s' t ->
        MapsTo Transition.s_firable (Vbool false) (sigstore σ'__t)).
Admitted.

(* [∀ σ'__t("s_firable") = true ⇒ t ∈ firable(s')] *)

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
    forall t id__t σ'__t,
      γ (inr t) = id__t ->
      MapsTo id__t σ'__t (compstore σ') ->
      MapsTo Transition.s_firable (Vbool true) (sigstore σ'__t) ->
      @Firable sitpn s' t.
Admitted.

(* [∀ σ'__t("s_firable") = false ⇒ t ∉ firable(s')] *)

Lemma falling_edge_compute_nfirable : 
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
    forall t id__t σ'__t,
      γ (inr t) = id__t ->
      MapsTo id__t σ'__t (compstore σ') ->
      MapsTo Transition.s_firable (Vbool false) (sigstore σ'__t) ->
      ~@Firable sitpn s' t.
Admitted.

(** ** Facts about Falling Edge and Fired *)

(** *** Falling edge compute fired: [σ'__t(fired) = true ⇒ t ∈ fired(s')] *)

(* [∀ t ∈ T, p ∈ input(t), i, j ∈ N, s ∈ Internal(Δ),]

      [<p.prior_auth(i) ⤳ s ⤳ t.prior_auth(j)>] ⇒
      [σ'__p("prior_auth")(i) = true] ⇒
      [pre(p,t) = (basic, n)] ⇒    
      [m(p) - (∑ pre(p, t__i), ∀ t__i ∈ Pr(p,t)) ≥ n]

 *)

Require Import hvhdl.AbstractSyntaxDefs.
Require Import hvhdl.Petri.
Require Import hvhdl.DesignElaboration.
Require Import common.GlobalTypes.

Lemma stabilize_compute_sens_by_place_after_falling :
  forall sitpn mm d Δ σ__e σ θ σ' s' (γ : P sitpn + T sitpn -> ident),

    (* [sitpn] translates into [d] *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* [d] elaborates into [Δ], [σ__e] *)
    ehdesign d Δ σ__e ->
    
    (* Stabilize from σf to σ' *)
    stabilize Δ σ (get_behavior d) θ σ' ->
    
    (* Conclusion *)
    
    forall t id__t σ'__t tg tip top p id__p σ'__p pg pip pop s (i j : nat) pauths fired lofT fset m n,

      (** Component [id__t] implements place [p] *)
      γ (inr t) = id__t ->
      
      (* [σ'__t] is the state of component [id__t] at design's state [σ'] *)
      MapsTo id__t σ'__t (compstore σ') ->

      (** Component [id__p] implements place [p] *)
      γ (inl p) = id__p ->
      
      (* [σ'__p] is the state of component [id__p] at design's state [σ'] *)
      MapsTo id__p σ'__p (compstore σ') ->

      (* Components [id__t] and [id__p] are part of the design behavior *)
      InCs (cs_comp id__t transition_entid tg tip top) (get_behavior d) ->
      InCs (cs_comp id__p place_entid pg pip pop) (get_behavior d) ->

      (* Signal [s] is an declared boolean signal of design [d] *)
      MapsTo s (Declared Tbool) Δ ->

      (* [<p.prior_auth(i) ⤳ s ⤳ t.prior_auth(j)>] *)
      List.In (assocop_ (Transition.priority_authorizations $[[i]]) (Some ($s))) pop ->
      List.In (associp_ (Transition.priority_authorizations $[[j]]) (#s)) tip ->

      (* [σ'__p("prior_auth")(i) = true] *)
      MapsTo Transition.priority_authorizations (Vlist pauths) (sigstore σ'__p) ->
      get_at i pauths = Some (Vbool true) -> 
      
      (* [fset ≡ fired(s')] *)
      IsFiredListAux s' m fired lofT fset ->
      
      (* Marking [m] is the current residual marking computed from
         start marking, s. t., [m = M s' - (∑ pre p t__i, ∀ t__i ∈ fired)].  *)
      
      MarkingSubPreSum (fun t__i => List.In t__i fired) (M s') m ->

      (* [pre(p,t) = (basic, n) \/ pre(p,t) = (test, n)] *)
      pre p t = Some (basic, n) \/ pre p t = Some (test, n) ->
      
      (* [(M s')(p) - (∑ pre(p, t__i), ∀ t__i ∈ fired) >= pre(p,t)] *)
      m p >= n.
Admitted.

(* [∀ t ∈ T, σ'__t("s_priority_combination") = true ⇒ t ∈ sens(m)]
   where [m] is a residual marking.
 *)

Lemma stabilize_compute_sens_by_residual_after_falling :
  forall sitpn mm d Δ σ θ σ' s' (γ : P sitpn + T sitpn -> ident),
    
    (* Stabilize from σf to σ' *)
    stabilize Δ σ (get_behavior d) θ σ' ->

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->
    
    (* Conclusion *)
    
    forall id__t σ'__t t m fired lofT fset,

      (** Component [id__t] implements transition [t] *)
      γ (inr t) = id__t ->
      
      (* [σ'__t] is the state of component [id__t] at design's state [σ']. *)
      MapsTo id__t σ'__t (compstore σ') ->
      
      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t__i => List.In t__i fired) (M s') m ->

      (* [fset ≡ fired(s')] *)
      IsFiredListAux s' m fired lofT fset ->
      
      (* [σ'__t("s_priority_combination") = true] *)
      MapsTo Transition.s_priority_combination (Vbool true) (sigstore σ'__t) ->
      
      (* [t ∈ sens(m)] *)
      @Sens sitpn m t.
Proof.
  split; intros.
  
  (* CASE [pre(p, t) = (test, n) \/ pre(p, t) = (basic, n)] *)
  - lazymatch goal with
    | [ H: _ \/ _ |- _ ] =>
      inversion_clear H as [Htest | Hbasic]
    end.

    (* CASE [pre(p, t) = (test, n)] *)
    
    + assert (Hxbind_p : exists id__p, γ (inl p) = id__p) by  (exists (γ (inl p)); reflexivity).
      inversion_clear Hxbind_p as (id__p, Hbind_p).
      assert (Hxσ'__p: exists σ'__p, MapsTo id__p σ'__p (compstore σ')) by admit.
      inversion_clear Hxσ'__p as (σ'__p, Hσ'__p).      
      assert (Hxpauths : exists pauths, MapsTo Transition.priority_authorizations (Vlist pauths) (sigstore σ'__p)) by admit.
      inversion_clear Hxpauths as (pauths, Hpauths).
      assert (Hpauth_true: forall i b, get_at i pauths = Some (Vbool b) -> b = true) by admit.
      
Admitted.

(* [∀ t ∈ T, 
      ElectFired(sitpn, s', m, fired, tp, (m', fired')) 
      /\ t ∈ tp 
      /\ [σ'__t]("fired") = true ⇒ 
      t ∈ fired'] *)

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
    
    forall m fired tp m' fired' lofT fset,

      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t => List.In t fired) (M s') m ->

      (* [fset ≡ fired(s')] *)
      IsFiredListAux s' m fired lofT fset ->
      
      (* Elect transitions to be fired from the [tp] list *)
      @ElectFired sitpn s' m fired tp (m', fired') ->
      
      forall t,
        
        (** Component [id__t] implements transition [t] *)
        γ (inr t) = id__t ->

        (* [σ'__t] is the state of component idt at design's state [σ']. *)
        MapsTo id__t σ'__t (compstore σ') ->

        (* [t] is top-priority *)
        List.In t tp ->
        
        (* Component [id__t] has a fired port valuated to true *)
        MapsTo Transition.fired (Vbool true) (sigstore σ'__t) ->

        (* Conclusion *)
        List.In t fired'.
Proof.
  intros *;
    intros Htransl Hsim Hfalling Hfall_hdl Hstab;
    intros m fired tp m' fired' lofT fset
           Hresm Hfiredaux Helect;

    dependent induction Helect;
    
    intros t Hbind_t Hσ'__t Hin_tp Hfired_true.

  (* BASE CASE, tp = [] *)
  - contradiction.

  (* IND. CASES, tp = (t :: _) *)
    
  (* CASE t ∈ firable(s') and t ∈ sens(m) *)
  - lazymatch goal with
    | [ H: List.In _ (_ :: _) |- _ ] =>
      inversion_clear H
    end.

    (* [t] is hd element *)
    + lazymatch goal with
      | [ H: t0 = t, H': ElectFired _ _ _ ?lofT _ |- _ ] =>
        eapply (elect_fired_in_acc sitpn s' msub (fired ++ [t0]) lofT m' fired' H');
        rewrite <- H; apply in_last
      end.
      
    (* [t] in tail; need [elect_fired_compute_residual] to complete
       the goal. *)
    + eapply IHHelect with (lofT := lofT) (fset := fset); eauto; admit.

  (* CASE t ∉ firable(s') \/ t ∉ sens(m) *)
  - lazymatch goal with
    | [ H: List.In _ (_ :: _) |- _ ] =>
      inversion_clear H
    end.

    (* [t] is hd element; contradiction with [σ'__t("fired") = true] *)
    + lazymatch goal with
      | [ H: t0 = t, H': ~(Firable _ _ /\ Sens _ _) |- _ ] =>
        rewrite H in *; clear H; elimtype False; apply H'; split
      end.

      (* SUBGOAL [t ∈ firable(s')] *)
      -- assert (Hsfirable_true : MapsTo Transition.s_firable (Vbool true) (sigstore σ'__t)) by admit.
         eapply falling_edge_compute_firable; eauto.

      (* SUBGOAL [t ∈ sens(m)] *)
      -- assert (Hspriocomb_true : MapsTo Transition.s_priority_combination (Vbool true) (sigstore σ'__t)) by admit.
         eapply stabilize_compute_sens_by_residual_after_falling; eauto.
         
    (* [t] in tail; need [elect_fired_compute_residual] to complete
       the goal. *)
    + apply IHHelect with (Ec := Ec) (s := s) (γ := γ) (m'0 := m') (lofT := lofT) (fset := fset); auto.      
Admitted.

(* Starting from similar state, after the falling edge of the clock
    signal, if a transition component has a fired out port valuated to
    [true] then its corresponding transition is fired. *)

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

      (* List [Tlist] implements the set of transitions [T sitpn] *)
      Set_in_List (fun t => True) Tlist ->
      
      (* (fired ++ lofT) is included in [Tlist] *)
      incl (fired ++ lofT) Tlist ->

      (* No duplicate in [fired ++ lofT] *)
      NoDup (fired ++ lofT) ->

      (* Marking [m] is the current residual marking computed from
         start marking [M s']  *)
      
      MarkingSubPreSum (fun t : T sitpn => List.In t fired) (M s') m -> 

      (* All transitions of the [fired] list verify the conclusion *)
      (forall t,
          γ (inr t) = id__t ->
          MapsTo id__t σ'__t (compstore σ') ->
          MapsTo Transition.fired (Vbool true) (sigstore σ'__t) ->
          List.In t fired \/ List.In t lofT) ->

      (*  *)
      (* (forall tp t t', IsTopPriorityList lofT tp -> List.In t tp -> t' >~ t = true -> List.In t' fired) -> *)

      (* [fset ≡ fired(s')] *)
      @IsFiredListAux sitpn s' m fired lofT fset ->
      
      forall t,
      
        (** Transition component [id__t] implements transition [t] *)
        γ (inr t) = id__t ->

        (* [σ'__t] is the state of [id__t] at design's state [σ'] *)
        MapsTo id__t σ'__t (compstore σ') ->

        (* Transition component [id__t] has a fired port valuated to [true] *)
        MapsTo Transition.fired (Vbool true) (sigstore σ'__t) ->
               
        (* [t] is fired at state [s'] *)
        List.In t fset.
Proof.
  intros Δ σ__f d θ σ' σ sitpn Ec τ s s' mm γ id__t σ'__t
         Htransl Hsim Hfalling Hfall_hdl Hstab
         Tlist m fired lofT fset
         HTlist Hincl Hnodup Hresm Hin_fired_compute Hfired_aux.

  dependent induction Hfired_aux.

  (* BASE CASE, solved by specializing [Hin_fired_compute] hypothesis *)
  - intros;
      lazymatch goal with
      | [ t: T sitpn, Hbind: γ _ = _, Hmaps_comp: MapsTo id__t _ _, Hmaps_fired: MapsTo Transition.fired _ _ |- _ ] =>
        specialize (Hin_fired_compute t Hbind Hmaps_comp Hmaps_fired) as Hv;
          inversion_clear Hv as [Hin_fired | Hin_nil]; [assumption | contradiction]
      end.

  (* IND. CASE *)
  - specialize (IsFiredListAux_cons H H0 H1 Hfired_aux) as Hfiredaux_cons. apply IHHfired_aux.

    (* CASE incl in Tlist *)
    + admit.

    (* CASE no duplicate  *)
    + admit.
      
    (* CASE elect fired compute residual *)
    + admit.

    (* CASE elect fired compute fired port *)
    + intros t Hbind Hmaps_comp Hmaps_fired;
        specialize (Hin_fired_compute t Hbind Hmaps_comp Hmaps_fired) as Hv;
        inversion_clear Hv as [Hin_fired | Hin_lofT].

      (* [ElectFired(s', m, fired, tp, (m', fired')) /\ t ∈ fired ⇒ t ∈ fired'] *)
      -- left;
           lazymatch goal with
           | [ H: ElectFired _ _ _ _ _ |- _ ] =>
             apply (elect_fired_in_acc sitpn s' m fired tp m' fired' H t Hin_fired)
           end.

      (* CASE [t ∈ lofT] *)
         
      -- lazymatch goal with
         | [ H: IsTopPriorityList _ _, H': IsDiff _ _ _ |- _ ] =>
           specialize (is_top_prio_diff_v sitpn lofT [] tp H lofT' t H' Hin_lofT)
             as Hv;
             inversion_clear Hv as [Hin_lofT' | Hin_tp]; [

               (* CASE t ∈ lofT' *)
               right; assumption |

               (* CASE t ∈ tp *)
               left; eapply elect_fired_compute_fired; eauto
             ]
         end.
         
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
      
      (* [fset ≡ fired(s')] *)
      @IsFiredList sitpn s' fset ->

      forall t,
        
        (** Transition component [id__t] implements transition [t] *)
        γ (inr t) = id__t ->

        (* [σ'__t] is the state of [id__t] at design's state [σ'] *)
        MapsTo id__t σ'__t (compstore σ') ->

        (* Transition component [id__t] has a fired port valuated to [true] *)
        MapsTo Transition.fired (Vbool true) (sigstore σ'__t) ->
        
        (* [t] is fired at state [s'] *)
        List.In t fset.
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
    | [ H: Set_in_List _ Tlist |- _ ] =>
      inversion H; assumption
    end.
    
  (* M s' = M s' - ∑ pre(ti), ∀ ti ∈ [] *)
  - apply MarkingSubPreSum_;
      inversion_clear 1;
      lazymatch goal with
      | [ H: PreSumList _ _ _ |- _ ] =>
        inversion H; [omega |
                      lazymatch goal with
                      | [ H: Set_in_List _ _, Heq: ?t :: ?tl = _ |- _ ] =>
                        unfold Set_in_List in H;
                        decompose [and] H;
                        lazymatch goal with
                        | [ Hset: forall _ : _, (List.In _ _ <-> List.In _ _) |- _ ] =>
                          rewrite <- Heq in Hset;
                          specialize (Hset t);
                          specialize (in_eq t tl) as Hineq;
                          rewrite <- Hset in Hineq;
                          contradiction
                        end
                      end
                     ]
      end.

  (* ∀ t ∈ T, T ≡ Tlist ⇒ t ∈ Tlist *)
  - lazymatch goal with
    | [ H: Set_in_List _ _ |- _ ] =>
      unfold Set_in_List in H; inversion_clear H as (Hset, Hnodup)
    end.
    
    intros t; intros; specialize (Hset t); rewrite <- Hset; right; trivial.

Qed.

(** *** Falling edge compute fired: [σ'__t(fired) = false ⇒ t ∉ fired(s')] *)

(** *** Falling edge compute fired: [t ∉ fired(s') ⇒ σ'__t(fired) = false] *)

(* All transitions that are elected to be fired, have an output fired
   port equal to false. *)

Lemma elect_fired_compute_fired_port_false :
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

      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t => List.In t fired) (M s') m ->

      (* Elect transitions to be fired from the [tp] list *)
      @ElectFired sitpn s' m fired tp (m', fired') ->
      
      forall t,
        
        (** Component idt implements transition t *)
        γ (inr t) = id__t ->

        (* σ't is the state of component idt at design's state σ'. *)
        MapsTo id__t σ'__t (compstore σ') ->

        (* t is top-priority *)
        List.In t tp ->

        (* t not elected to be fired *)
        ~List.In t fired' ->
        
        (* Conclusion *)
        MapsTo Transition.fired (Vbool false) (sigstore σ'__t).
Proof.
  intros *;
    intros Htransl Hsim Hfalling Hfall_hdl Hstab;
    intros m fired tp m' fired' Hresm Helect;
    dependent induction Helect;
    intros t Hbind_t Hσ'__t Hin_tp Hnot_in_fired'.

  (* BASE CASE, tp = [] *)
  - contradiction.

  (* IND. CASES, tp = (t :: _) *)
    
  (* CASE t ∈ firable(s') and t ∈ sens(m) *)
  - lazymatch goal with
    | [ H: List.In _ (_ :: _) |- _ ] =>
      inversion_clear H
    end.

    (* Contradiction between t ∈ fired ++ [t] and t ∉ fired' *)
    + admit.

    (* Apply IH *)
    (* Need to solve a subgoal on the computation of the residual
       marking *)
    + eapply IHHelect; eauto; admit.
      
  (* CASE t ∉ firable(s') or t ∉ sens(m) *)
  - lazymatch goal with
    | [ H: List.In _ (_ :: _) |- _ ] =>
      inversion_clear H
    end.

    (* Hard case *)
    + admit.

    (* Apply IH *)
    + eapply IHHelect; eauto.
          
Admitted.

(* States that starting from similar state, after the falling edge of
    the clock signal, all transitions that are not fired are
    associated with transition components with a fired out port
    valuated to false. *)

Lemma falling_edge_compute_fired_port_false_aux :
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
      Set_in_List (fun t => True) Tlist ->
      
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

    (* CASE elect fired compute fired port false *)
    + admit.
      
Admitted.

(*  Corollary of the [falling_edge_compute_not_fired_aux] lemma.

    States that starting from similar state, after the falling edge of
    the clock signal, all transitions that not fired are associated with
    transition components with a fired out port valuated to false. *)

Lemma falling_edge_compute_fired_port_false_list :
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
        (** Component idt implements transition t *)
        γ (inr t) = id__t ->

        (* σ't is the state of component idt at design's state σ'. *)
        MapsTo id__t σ'__t (compstore σ') ->
        
        ~List.In t fset ->

        (* Conclusion *)
        MapsTo Transition.fired (Vbool false) (sigstore σ'__t).
Proof.  
  intros until t0;
    lazymatch goal with
    | [ H: IsFiredList _ _ |- _ ] =>
      inversion H;
        eapply falling_edge_compute_fired_port_false_aux;
        eauto    
    end.

    (* incl ([] ++ Tlist) Tlist *)
  - apply incl_refl.

  (* NoDup ([] ++ Tlist) *)
  - lazymatch goal with
    | [ H: Set_in_List _ Tlist |- _ ] =>
      inversion H; assumption
    end.
    
  (* M s' = M s' - ∑ pre(ti), ∀ ti ∈ [] *)
  - apply MarkingSubPreSum_;
      inversion_clear 1;
      lazymatch goal with
      | [ H: PreSumList _ _ _ |- _ ] =>
        inversion H; [omega |
                      lazymatch goal with
                      | [ H: Set_in_List _ _, Heq: ?t :: ?tl = _ |- _ ] =>
                        unfold Set_in_List in H;
                        decompose [and] H;
                        lazymatch goal with
                        | [ Hset: forall _ : _, (List.In _ _ <-> List.In _ _) |- _ ] =>
                          rewrite <- Heq in Hset;
                          specialize (Hset t);
                          specialize (in_eq t tl) as Hineq;
                          rewrite <- Hset in Hineq;
                          contradiction
                        end
                      end
                     ]
      end.
    
  (* ∀ t ∈ T, t ∈ [] /\ t ∉ T ⇒ C *)
  - lazymatch goal with
    | [ H: Set_in_List _ _ |- _ ] =>
      unfold Set_in_List in H; inversion_clear H as (Hset, Hnodup)
    end.
    
    intros t; intros.
    lazymatch goal with
    | [ H: _ /\ _ |- _ ] =>
      inversion H as (Hnotinnil, Hnin_Tlist);
        specialize (Hset t);
        rewrite <- Hset in Hnin_Tlist;
        contradiction
    end.
Qed.
  
(** *** Falling edge compute fired port true: [t ∈ fired(s') ⇒ σ'__t(fired) = true] *)

Definition add_out_arc_weight (σ__p : DState) :=
  fun sum i =>
    match find Place.output_arcs_weights (sigstore σ__p) with
    | Some (Vlist ws) =>
      match get_at i ws with
      | Some (Vnat ω) => sum + ω
      | _ => sum
      end
    | _ => sum
    end.

Definition PreSumListVhdl (σ__p : DState) (idxs : list nat) (sum : nat) : Prop :=
  FoldL (add_out_arc_weight σ__p) idxs 0 sum.

Inductive PreSumVhdl (σ__p : DState) (P : nat -> Prop) (sum__pre : nat) : Prop :=
| PreSum_ :
    forall idxs,
      Set_in_List P idxs ->
      PreSumListVhdl σ__p idxs sum__pre ->
      PreSumVhdl σ__p P sum__pre.

Definition PrVhdl (σ__p : DState) (j : nat) : nat -> Prop :=
  fun n =>
    (* n ∈ [0, j-1] *)
    0 <= n <= j - 1
    /\
    (* [σ__p]("output_arcs_weights")(n) = basic *)
    (forall types,
        MapsTo Place.output_arcs_types (Vlist types) (sigstore σ__p) ->
        get_at n types = Some (Vnat basic))
    /\
    (* [σ__p]("output_transitions_fired")(n) = true *)
    (forall vfired,
        MapsTo Place.output_transitions_fired (Vlist vfired) (sigstore σ__p) ->
        get_at n vfired = Some (Vbool true)).

(* [∀ t ∈ T, p ∈ input(t), i, j ∈ N, s ∈ Declared(Δ),]

      [<p.prior_auth(i) ⤳ s ⤳ t.prior_auth(j)>] ⇒
      [pre(p,t) = (basic, n)] ⇒    
      [(M s' p) - (∑ pre(p, t__i), ∀ t__i ∈ fired) ≥ n] ⇒
      [σ'__p("s_marking") - ∑ σ'__p("output_arcs_weights")(k) ≥ σ'__p("output_arcs_weights")(j)]
      where k ∈ { n | n ∈ [0, j-1] 
                      & [σ'__p]("output_arcs_weights")(n) = basic 
                      & [σ'__p]("output_transitions_fired")(n) = true }
 *)

Local Notation "'|' e '|'" := (exist _ e _) (at level 100).

Lemma stabilize_compute_auth_after_falling :
  forall sitpn mm d Δ σ__e σ θ σ' s' (γ : P sitpn + T sitpn -> ident),

    (* [sitpn] translates into [d] *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* [d] elaborates into [Δ], [σ__e] *)
    ehdesign d Δ σ__e ->
    
    (* Stabilize from σf to σ' *)
    stabilize Δ σ (get_behavior d) θ σ' ->
    
    (* Conclusion *)
    
    forall t id__t tg tip top p id__p σ'__p pg pip pop s (i j : nat)
           weights m fired lofT fset m__p ω pf ω' n n',

      (** Component [id__t] implements transition [t] *)
      γ (inr t) = id__t ->

      (** Component [id__p] implements place [p] *)
      γ (inl p) = id__p ->
      
      (* [σ'__p] is the state of component [id__p] at design's state [σ'] *)
      MapsTo id__p σ'__p (compstore σ') ->

      (* Components [id__t] and [id__p] are part of the design behavior *)
      InCs (cs_comp id__t transition_entid tg tip top) (get_behavior d) ->
      InCs (cs_comp id__p place_entid pg pip pop) (get_behavior d) ->

      (* Signal [s] is an declared boolean signal of design [d] *)
      MapsTo s (Declared Tbool) Δ ->

      (* [<p.prior_auth(i) ⤳ s ⤳ t.prior_auth(j)>] *)
      List.In (assocop_ (Transition.priority_authorizations $[[i]]) (Some ($s))) pop ->
      List.In (associp_ (Transition.priority_authorizations $[[j]]) (#s)) tip ->
      
      (* [fset ≡ fired(s')] *)
      IsFiredListAux s' m fired lofT fset ->

      (* All fired transitions with a higher priority than [t] are in
         the [fired] list *)
      (forall t', t' >~ t = true /\ List.In t' fset -> List.In t' fired) ->

      (* All transitions of the fired list verify "fired" port
         equals true at [σ'] *)
      (forall t' id__t' σ'__t',
          γ (inr t') = id__t' ->
          MapsTo id__t' σ'__t' (compstore σ') ->
          List.In t' fired ->
          MapsTo Transition.fired (Vbool true) (sigstore σ'__t')) ->
      
      (* [n] is the sum of the basic arc weights between [p] and
         transitions of the [fired] list, i.e., 
         [n = ∑ pre p t__i, ∀ t__i ∈ fired].  *)
      
      PreSum p (fun t__i => List.In t__i fired) n ->

      (* [pre(p,t) = (basic, ω) \/ pre(p,t) = (test, ω)] *)
      pre p t = Some (basic, exist _ ω pf) \/ pre p t = Some (test, exist _ ω pf) ->
      
      (* [(M s')(p) - (∑ pre(p, t__i), ∀ t__i ∈ fired) >= pre(p,t)] *)
      M s' p - n >= ω ->

      (* [σ'__p("s_marking") = m__p] *)
      MapsTo Place.s_marking (Vnat m__p) (sigstore σ'__p) ->

      (* [σ'__p("output_arcs_weights")(j) = ω'] *)
      MapsTo Place.output_arcs_weights (Vlist weights) (sigstore σ'__p) ->
      get_at j weights = Some (Vnat ω') ->

      (* [∑ σ'__p("output_arcs_weights")(k) = n']
         where k ∈ { n | n ∈ [0, j-1] 
                         & [σ'__p]("output_arcs_weights")(n) = basic 
                         & [σ'__p]("output_transitions_fired")(n) = true } *)
      PreSumVhdl σ'__p (PrVhdl σ'__p j) n' ->
      
      (* [σ'__p("s_marking") - ∑ σ'__p("output_arcs_weights")(k) ≥ σ'__p("output_arcs_weights")(j)]
         where k ∈ { n | n ∈ [0, j-1] 
                         & [σ'__p]("output_arcs_weights")(n) = basic 
                         & [σ'__p]("output_transitions_fired")(n) = true } *)      
      m__p - n' >= ω'.
Proof.
  intros.

  (* Markings are equal at [s'] and [σ']. 
     Deduced from [s ∼ σ] and lemma "marking idle on falling"
     and "sync. signal idle on stabilize".
   *)
  assert (Hmeq : M s' p = m__p) by admit.

  (* Basic arc weight between [p] and [t0] equals value of port
     [output_arcs_weights(j)].
     Deduced from translation function. *)
  assert (Hweq : ω = ω') by admit.

  (* Induction on [PreSum] to prove [n = n'] *)
  assert (Heqsum : n = n').
  {
    
    lazymatch goal with
    | [ H: PreSum _ _ _ |- _ ] => 
      inversion H;
        lazymatch goal with
        | [ Hpresuml: PreSumList _ _ _ |- _ ] =>
          inversion Hpresuml
        end
    end.
    
    (* CASE, fired = [] implies [n = 0].

       Then, there are no transitions that are in the output of [p]
       and with a higher priority than [t] that are [fired].
     *)
    - admit.

    (* CASE fired = (b :: l) *)
    - admit.
        
  }
    
Admitted.

(* All transitions that are sensitized by the residual marking have an
   input port "priority_authorizations" of type boolean vector with
   all its subelements set to true.  *)

(* [∀ t ∈ T, p ∈ input(t), i, j ∈ N, s ∈ Declared(Δ),]

      [<p.prior_auth(i) ⤳ s ⤳ t.prior_auth(j)>] ⇒
      [pre(p,t) = (basic, ω)] ⇒    
      [(M s' p) - (∑ pre(p, t__i), ∀ t__i ∈ fired) ≥ ω] ⇒
      [σ'__p("prior_auth")(i) = true]

 *)

Lemma stabilize_compute_input_prior_auth_true_after_falling :
  forall sitpn mm d Δ σ__e σ θ σ' s' (γ : P sitpn + T sitpn -> ident),

    (* [sitpn] translates into [d] *)
    sitpn_to_hvhdl sitpn mm = Success d ->

    (* [d] elaborates into [Δ], [σ__e] *)
    ehdesign d Δ σ__e ->
    
    (* Stabilize from σf to σ' *)
    stabilize Δ σ (get_behavior d) θ σ' ->
    
    (* Conclusion *)
    
    forall t id__t σ'__t tg tip top p id__p σ'__p pg pip pop s (i j : nat)
           pauths m fired lofT fset sum__pre ω,

      (** Component [id__t] implements place [p] *)
      γ (inr t) = id__t ->
      
      (* [σ'__t] is the state of component [id__t] at design's state [σ'] *)
      MapsTo id__t σ'__t (compstore σ') ->

      (** Component [id__p] implements place [p] *)
      γ (inl p) = id__p ->
      
      (* [σ'__p] is the state of component [id__p] at design's state [σ'] *)
      MapsTo id__p σ'__p (compstore σ') ->

      (* Components [id__t] and [id__p] are part of the design behavior *)
      InCs (cs_comp id__t transition_entid tg tip top) (get_behavior d) ->
      InCs (cs_comp id__p place_entid pg pip pop) (get_behavior d) ->

      (* Signal [s] is an declared boolean signal of design [d] *)
      MapsTo s (Declared Tbool) Δ ->

      (* [<p.prior_auth(i) ⤳ s ⤳ t.prior_auth(j)>] *)
      List.In (assocop_ (Transition.priority_authorizations $[[i]]) (Some ($s))) pop ->
      List.In (associp_ (Transition.priority_authorizations $[[j]]) (#s)) tip ->
      
      (* [fset ≡ fired(s')] *)
      IsFiredListAux s' m fired lofT fset ->

      (* All fired transitions with a higher priority than [t] are in
         the [fired] list *)
      (forall t', t' >~ t = true /\ List.In t' fset -> List.In t' fired) ->

      (* All transitions of the fired list verify "fired" port
         equals true at [σ'] *)
      (forall t' id__t' σ'__t',
          γ (inr t') = id__t' ->
          MapsTo id__t' σ'__t' (compstore σ') ->
          List.In t' fired ->
          MapsTo Transition.fired (Vbool true) (sigstore σ'__t')) ->
      
      (* Marking [m] is the current residual marking computed from
         start marking, s. t., [m = M s' - (∑ pre p t__i, ∀ t__i ∈ fired)].  *)
      
      PreSum p (fun t__i => List.In t__i fired) sum__pre ->

      (* [pre(p,t) = (basic, n) \/ pre(p,t) = (test, n)] *)
      pre p t = Some (basic, ω) \/ pre p t = Some (test, ω) ->
      
      (* [(M s')(p) - (∑ pre(p, t__i), ∀ t__i ∈ fired) >= pre(p,t)] *)
      M s' p - sum__pre >= ω ->

      (* [σ'__p("prior_auth")(i) = true] *)
      MapsTo Place.priority_authorizations (Vlist pauths) (sigstore σ'__p) ->
      get_at i pauths = Some (Vbool true).  
Admitted.


(* All transitions that are sensitized by the residual marking have a
   "s_priority_combination" signal of type boolean set to true. *)

Definition andb_if_vbool (asum : bool) (v : value) : bool :=
  match v with
  | Vbool b => andb b asum
  | _ => asum
  end.
  
Definition VBoolAndSum (lofv : lofvalues) (asum : bool) :=
  FoldL andb_if_vbool lofv true asum.

Lemma VBoolAndSum_xasum : forall lofv, exists asum, VBoolAndSum lofv asum.
Proof. intros; apply FoldL_xres. Qed.
 
Definition LOfVBoolTrue (lofv : lofvalues) :=
  Forall (fun v => v = Vbool true) lofv.

Require Import sitpn.dp.GenerateInfos.
Require Import sitpn.dp.InfosTypes.

Lemma stabilize_compute_prior_auths_true_after_falling :
  forall sitpn mm d Δ σ θ σ' s' (γ : P sitpn + T sitpn -> ident),
    
    (* Stabilize from σf to σ' *)
    stabilize Δ σ (get_behavior d) θ σ' ->

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->
    
    (* Conclusion *)
    
    forall id__t σ'__t t m fired pauths,

      (** Component idt implements transition t *)
      γ (inr t) = id__t ->
      
      (* σ't is the state of component idt at design's state σ'. *)
      MapsTo id__t σ'__t (compstore σ') ->
      
      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t' => List.In t' fired) (M s') m ->
      
      (* All transitions of the fired list verify "fired" port
         equals true at [σ'] *)
      (forall t' id__t' σ'__t',
          γ (inr t') = id__t' ->
          MapsTo id__t' σ'__t' (compstore σ') ->
          List.In t' fired ->
          MapsTo Transition.fired (Vbool true) (sigstore σ'__t')) ->
      
      (* t ∈ sens(m) *)
      @Sens sitpn m t ->
      
      (* σ't("priority_authorizations") = (true,...,true)  *)
      MapsTo Transition.priority_authorizations (Vlist pauths) (sigstore σ'__t) ->
      LOfVBoolTrue pauths.
Admitted.

Lemma stabilize_compute_s_prio_comb_true_after_falling :
  forall sitpn mm d Δ σ θ σ' s' (γ : P sitpn + T sitpn -> ident),
    
    (* Stabilize from σf to σ' *)
    stabilize Δ σ (get_behavior d) θ σ' ->

    (* sitpn translates into d. *)
    sitpn_to_hvhdl sitpn mm = Success d ->
    
    (* Conclusion *)
    
    forall id__t σ'__t t m fired,

      (** Component idt implements transition t *)
      γ (inr t) = id__t ->
      
      (* σ't is the state of component idt at design's state σ'. *)
      MapsTo id__t σ'__t (compstore σ') ->
      
      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t' => List.In t' fired) (M s') m ->
      
      (* All transitions of the fired list verify "fired" port
         equals true at [σ'] *)
      (forall t' id__t' σ'__t',
          γ (inr t') = id__t' ->
          MapsTo id__t' σ'__t' (compstore σ') ->
          List.In t' fired ->
          MapsTo Transition.fired (Vbool true) (sigstore σ'__t')) ->
      
      (* t ∈ sens(m) *)
      @Sens sitpn m t ->
      
      (* σ't("s_priority_combination") = true *)
      MapsTo Transition.s_priority_combination (Vbool true) (sigstore σ'__t).
Proof.

  intros.

  (* [σ'__t("s_priority_combination") = ⋀i=0..n σ'__t("priority_authorizations")(i)] *)

  assert (Hxpauths : exists pauths, MapsTo Transition.priority_authorizations (Vlist pauths) (sigstore σ'__t)) by admit.
  inversion_clear Hxpauths as (pauths, Hpauths).
  
  assert (Hxasum : exists asum, VBoolAndSum pauths asum) by (apply (VBoolAndSum_xasum pauths)).
  inversion_clear Hxasum as (asum, Hasum).
  
  assert (Heq_pcomb_asum : MapsTo Transition.s_priority_combination (Vbool asum) (sigstore σ'__t)) by admit.
  specialize (stabilize_compute_prior_auths_true_after_falling
                sitpn mm d Δ σ θ σ' s' γ H H0 id__t σ'__t t0 m fired pauths H1 H2 H3 H4 H5 Hpauths)
    as Hlofbtrue.
  
  (* Reason on the input of [t0] *)

  (* CASE [t0] has no input. 

     Then, [priority_authorizations] has an only subelement at position [0]
     that is set to [true].
     
   *)
  
  (* CASE [t0] has some input.
     
     We know:

     - for all p ∈ input(t), exists i j sig,
       <p.priority_authorizations(j) → sig → t.priority_authorizations(i)>

     -                             
     Then show, thanks to the "stabilize compute output priority
     authorizations true after falling" lemma, that
     [p.priority_authorizations(j) = true] and therefore that
     [t.priority_authorizations(i)] *)

Admitted.

(* All transitions that are in the list of transitions elected to be
   fired - at state [s'] and considering the residual marking [m] -
   have a bounded transition component (binding through γ) with a
   "fired" port set to true at state σ'. *)

Lemma elect_fired_compute_fired_port_true :
  forall Δ σ__f d θ σ' σ sitpn Ec τ s s' mm γ ,

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
      (forall t id__t σ'__t,
          γ (inr t) = id__t ->
          MapsTo id__t σ'__t (compstore σ') ->
          List.In t fired ->
          MapsTo Transition.fired (Vbool true) (sigstore σ'__t)) ->

      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t => List.In t fired) (M s') m ->

      (* Elect transitions to be fired from the [tp] list *)
      @ElectFired sitpn s' m fired tp (m', fired') ->
      
      forall t id__t σ'__t,
        (** Component idt implements transition t *)
        γ (inr t) = id__t ->

        (* σ't is the state of component idt at design's state σ'. *)
        MapsTo id__t σ'__t (compstore σ') ->

        (* [t] is elected to be fired *)
        List.In t fired' ->
      
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
  - intros t' id__t' σ'__t' Hbind_t' Hid__t Hin_app; destruct_in_app_or.
    
    (* Case t ∈ fired *)
    + eapply Hin_fired_compute with (σ'__t := σ'__t'); eauto.
    
    (* Case t = t' *)
      
    (* Use [falling_edge_compute_firable] and [stabilize_compute_priority_after_falling] to solve the subgoal *)
    + singleton_eq; rewrite Heq in *.

      (* Specialize [falling_edge_compute_firable] *)
      lazymatch goal with
      | [ H: Firable _ _ |- _ ] =>
        specialize (falling_edge_compute_s_firable_true
                      Δ σ__f d θ σ' σ sitpn Ec τ s s' mm γ
                      Htransl Hsim Hfalling Hfall_hdl Hstab
                      t' id__t' σ'__t' Hbind_t' Hid__t H) as Hfirable
      end.

      (* Specialize [stabilize_compute_priority_after_falling] *)
      lazymatch goal with
      | [ H: Sens _ _ |- _ ] =>
        specialize (stabilize_compute_s_prio_comb_after_falling
                      sitpn mm d Δ σ__f θ σ' s' γ
                      Hstab Htransl 
                      id__t' σ'__t' t' m fired Hbind_t' Hid__t Hresm Hin_fired_compute H) as Hprio_comb
      end.

      (* Specialize [fired_assign_on_stabilize] with [Hfirable] and [Hprio_comb] *)
      assert (Hfired_assign: MapsTo Transition.fired (Vbool true) (sigstore σ'__t')) by admit.

      assumption.
      
  (* CASE msub = M s' - ∑ pre(ti), ∀ ti ∈ fired ++ [t] *)
  - admit.
    
Admitted.
  
(*  States that starting from similar state, after the falling edge of
    the clock signal, all fired transitions are associated with
    transition components with a fired out port valuated to true (or
    false otherwise). *)

Lemma falling_edge_compute_fired_port_true_aux :
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
      Set_in_List (fun t => True) Tlist ->
      
      (* (fired ++ lofT) is a permutation of Tlist *)
      incl (fired ++ lofT) Tlist ->

      (* No duplicate in (fired ++ lofT) *)
      NoDup (fired ++ lofT) ->

      (* Marking [m] is the current residual marking computed from
         start marking [M s'].  *)
      
      MarkingSubPreSum (fun t : T sitpn => List.In t fired) (M s') m -> 

      (* All transitions of the fired list verify the conclusion *)
      (forall t id__t σ'__t,
          γ (inr t) = id__t ->
          MapsTo id__t σ'__t (compstore σ') ->
          List.In t fired ->
          MapsTo Transition.fired (Vbool true) (sigstore σ'__t)) ->
      
      (* [fset ≡ fired(s')] *)
      @IsFiredListAux sitpn s' m fired lofT fset ->
      
      forall t,
        (** Component [id__t] implements transition [t] *)
        γ (inr t) = id__t ->

        (* [σ'__t] is the state of component [id__t] at design's state [σ'] *)
        MapsTo id__t σ'__t (compstore σ') ->

        (* [t ∈ fired(s')] *)
        List.In t fset ->

        (* Conclusion *)
        MapsTo Transition.fired (Vbool true) (sigstore σ'__t).
Proof.
  intros Δ σ__f d θ σ' σ sitpn Ec τ s s' mm γ id__t σ'__t
         Htransl Hsim Hfalling Hfall_hdl Hstab
         Tlist m fired lofT fset
         HTlist Hincl Hnodup Hresm Hin_fired_compute Hfired_aux. 
  induction Hfired_aux.

  (* BASE CASE *)
  - intros; eapply Hin_fired_compute; eauto.
    
  (* IND. CASE *)
  - apply IHHfired_aux.
    
    (* CASE incl in Tlist *)
    + admit.

    (* CASE no duplicate  *)
    + admit.
      
    (* CASE elect fired compute residual *)
    + admit.

    (* CASE elect fired compute fired *)
    + intros; eapply (elect_fired_compute_fired_port_true); eauto.
      
Admitted.  

(*  Corollary of the [falling_edge_compute_fired_aux] lemma.

    States that starting from similar state, after the falling edge of
    the clock signal, all fired transitions are associated with
    transition components with a fired out port valuated to true (or
    false otherwise). *)

Lemma falling_edge_compute_fired_port_true_list :
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
        eapply falling_edge_compute_fired_port_true_aux;
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

Lemma falling_edge_compute_fired_port_true :
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
        eapply falling_edge_compute_fired_port_true_list;
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


