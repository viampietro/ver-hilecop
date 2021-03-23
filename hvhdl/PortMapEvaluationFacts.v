(** * Facts about Port Map Evaluation *)

Require Import common.NatSet.
Require Import common.NatMap.
Require Import common.CoqLib.
Require Import common.NatSet.
Require Import common.InAndNoDup.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.ValidPortMap.
Require Import hvhdl.SemanticalDomains.

Require Import hvhdl.EnvironmentFacts.
Require Import hvhdl.ValidPortMapFacts.

(** ** Facts about Input Port Map Evaluation *)

Section IPMap.

  Lemma vassocip_inv_sigstore :
    forall {Δ Δ__c σ σ__c asip σ__c' id v},
      vassocip Δ Δ__c σ σ__c asip σ__c' -> 
      ~InputOf Δ__c id ->
      MapsTo id v (sigstore σ__c) ->
      MapsTo id v (sigstore σ__c').
  Proof.
    inversion 1; subst; simpl; auto; intros.
    all :
      destruct (Nat.eq_dec id id0) as [e1 | ne1]; try subst;
      [ elimtype False;
        match goal with
        | [ H: ~InputOf _ _, H': MapsTo _ (Input ?t) _ |- _ ] =>
          apply H; exists t; assumption
        end
      | eapply NatMap.add_2; eauto ].
  Qed.

  Lemma vassocip_not_in_events_if_not_input :
    forall {Δ Δ__c σ σ__c asip σ__c' id},
      vassocip Δ Δ__c σ σ__c asip σ__c' ->
      ~InputOf Δ__c id ->
      ~NatSet.In id (events σ__c) ->
      ~NatSet.In id (events σ__c').
  Proof.
    inversion_clear 1; auto; simpl; subst; intros;
      rewrite add_spec; inversion 1;
        (auto ||
         match goal with
         | [ H: MapsTo _ (Input ?t) _, H': ~InputOf _ _ |- _ ] =>
           subst; apply H'; exists t; auto
         end).
  Qed.
  
  Lemma vassocip_eval_simpl_associp :
    forall {Δ Δ__c σ σ__c σ__c'} {id : ident} {e},
      vassocip Δ Δ__c σ σ__c (associp_ id e) σ__c' ->
      exists v, vexpr Δ σ EmptyLEnv false e v /\
                MapsTo id v (sigstore σ__c').
  Proof. inversion 1.
         subst; simpl; exists newv; auto with mapsto.
         subst; simpl; exists currv; split; [ | auto].
         erewrite <- OVEq_eq_1; eauto.
  Qed.

  Lemma vassocip_inv_if_not_assoc :
    forall {Δ Δ__c σ σ__c asip σ__c'},
      vassocip Δ Δ__c σ σ__c asip σ__c' ->
      forall {id__i : ident} {v},
        ~(exists e, (associp_ id__i e) = asip) ->
        ~(exists e e__i, (associp_ (n_xid id__i e__i) e) = asip) ->
        MapsTo id__i v (sigstore σ__c) ->
        MapsTo id__i v (sigstore σ__c').
  Proof.
    inversion 1; subst; simpl; auto.
    all : intros id__i v nex_1 nex_2; intros.
    destruct (Nat.eq_dec id__i id) as [eq1 | neq1].
    subst; elimtype False; apply nex_1; exists e; reflexivity.
    eauto with mapsto.
    destruct (Nat.eq_dec id__i id) as [eq1 | neq1].
    subst; elimtype False; apply nex_2; exists e, ei; reflexivity.
    eauto with mapsto.
  Qed.
  
  Lemma vassocip_no_events :
    forall {Δ Δ__c σ σ__c asip σ__c'},
      vassocip Δ Δ__c σ σ__c asip σ__c' ->
      Equal (events σ__c') {[]} ->
      Equal (events σ__c) {[]}.
  Proof.
    inversion 1; subst; simpl; auto;
    intros; exfalso; eapply add_empty_false; eauto.
  Qed.
  
  Lemma vassocip_eq_state_if_no_events :
    forall {Δ Δ__c σ σ__c asip σ__c'},
      vassocip Δ Δ__c σ σ__c asip σ__c' ->
      Equal (events σ__c') {[]} ->
      σ__c = σ__c'.
  Proof.
    inversion 1; auto; subst; simpl;
      intros; exfalso; eapply add_empty_false; eauto.
  Qed.

  Lemma vassocip_maps_sstore :
    forall {Δ Δ__c σ σ__c asip σ__c' id v},
      vassocip Δ Δ__c σ σ__c asip σ__c' -> 
      MapsTo id v (sigstore σ__c) ->
      exists v', MapsTo id v' (sigstore σ__c').
  Proof.
    inversion_clear 1; subst; cbn; (try solve [exists v; assumption]);
      destruct (Nat.eq_dec id id0) as [eq_ | neq_ ].
    subst; exists newv; eauto with mapsto.
    exists v; eauto with mapsto.
    subst; exists (Varr (set_at newv idx aofv idx_in_bounds)); eauto with mapsto.
    exists v; eauto with mapsto.
  Qed.
  
  Lemma mapip_inv_sigstore :
    forall {Δ Δ__c σ σ__c ipm σ__c' id v},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      ~InputOf Δ__c id ->
      MapsTo id v (sigstore σ__c) ->
      MapsTo id v (sigstore σ__c').
  Proof.
    induction 1; intros; auto.
    apply IHmapip; auto.
    eapply vassocip_inv_sigstore; eauto.
  Qed.

  Lemma mapip_inv_compstore :
    forall {Δ Δ__c σ σ__c ipm σ__c' id σ__c0},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      MapsTo id σ__c0 (compstore σ__c) ->
      MapsTo id σ__c0 (compstore σ__c').
  Proof.
    induction 1; try subst; auto.
    induction H; try subst; auto.
  Qed.
  
  Lemma mapip_not_in_events_if_not_input :
    forall {Δ Δ__c : ElDesign} {σ σ__c : DState} {ipm : list associp} {σ__c' : DState} {id : key},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      ~InputOf Δ__c id ->
      ~NatSet.In id (events σ__c) ->
      ~NatSet.In id (events σ__c').
  Proof.
    induction 1; auto.
    intros; apply IHmapip; auto.
    eapply vassocip_not_in_events_if_not_input; eauto.
  Qed.
  
  Lemma mapip_inv_if_not_assoc :
    forall {Δ Δ__c σ σ__c ipm σ__c'},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      forall {id__i : ident} {v},
      ~(exists e, List.In (associp_ id__i e) ipm) ->
      ~(exists e e__i, List.In (associp_ (n_xid id__i e__i) e) ipm) ->
      MapsTo id__i v (sigstore σ__c) ->
      MapsTo id__i v (sigstore σ__c').
  Proof.
    induction 1; auto.
    intros id__i v nex_1 nex_2; intros.
    apply IHmapip.
    destruct 1 as (e, In_lofasips).
    apply nex_1; exists e; auto.
    destruct 1 as (e, (e__i, In_lofasips)).
    apply nex_2; exists e, e__i; auto.
    eapply vassocip_inv_if_not_assoc; eauto.
    destruct 1 as (e, e1).
    apply nex_1; exists e; rewrite e1; auto with datatypes.
    destruct 1 as (e, (e__i, e1)).
    apply nex_2; exists e, e__i; rewrite e1; auto with datatypes.
  Qed.  
  
  Lemma mapip_eval_simpl_associp :
    forall {Δ Δ__c σ σ__c ipm σ__c'} ,
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      forall {id__i : ident} {e formals formals'},
        List.In (associp_ id__i e) ipm ->
        listipm Δ Δ__c σ formals ipm formals' ->
        exists v, vexpr Δ σ EmptyLEnv false e v /\
                  MapsTo id__i v (sigstore σ__c').
  Proof.
    induction 1; try (solve [inversion 1]).
    inversion 1; subst; auto.
    edestruct @vassocip_eval_simpl_associp with (Δ := Δ)
      as (v, (vexpr_v, MapsTo_v));
      eauto.
    exists v; split; auto.
    inversion H2; subst. inversion H5; subst.
    eapply mapip_inv_if_not_assoc; eauto.
    eapply proj1; eapply listipm_unique_simpl_associp; eauto.
    eapply proj2; eapply listipm_unique_simpl_associp; eauto.
    inversion 1; subst.
    intros; eapply IHmapip; eauto.
  Qed.
  
  Lemma mapip_no_events :
    forall {Δ Δ__c σ σ__c ipm σ__c'},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      Equal (events σ__c') {[]} ->
      Equal (events σ__c) {[]}.
  Proof.
    induction 1; auto.
    intros; eapply vassocip_no_events; eauto.
  Qed.
  
  Lemma mapip_eq_state_if_no_events :
    forall {Δ Δ__c σ σ__c ipm σ__c'},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      Equal (events σ__c') {[]} ->
      σ__c = σ__c'.
  Proof.
    induction 1; auto.
    intros Equal_emp.
    transitivity σ__c'; auto.
    eapply vassocip_eq_state_if_no_events; eauto.
    eapply mapip_no_events; eauto.
  Qed.

  Lemma mapip_maps_sstore :
    forall {Δ Δ__c σ σ__c ipm σ__c' },
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      forall {id v},
        MapsTo id v (sigstore σ__c) ->
        exists v', MapsTo id v' (sigstore σ__c').
  Proof.
    induction 1; intros; auto.
    exists v; assumption.
    edestruct @vassocip_maps_sstore with (Δ := Δ); eauto.
  Qed.
  
End IPMap.

(** ** Facts about Output Port Map Evaluation *)

Section OPMap.

  Lemma vassocop_maps_sstore :
    forall {Δ Δ__c σ σ__c asop σ'},
      vassocop Δ Δ__c σ σ__c asop σ' ->
      forall {id v},
        MapsTo id v (sigstore σ) ->
        exists v', MapsTo id v' (sigstore σ').
  Proof.
    induction 1; try (solve [intros; exists v; auto]).
    all : subst σ'; subst sigstore'; cbn;
      intros id v MapsTo_; destruct (Nat.eq_dec id id__a); 
        [ subst id; eauto with mapsto
        | exists v; eauto with mapsto ].
  Qed.
  
  Lemma vassocop_eq_state_if_no_events :
    forall {Δ Δ__c σ σ__c asop σ'},
      vassocop Δ Δ__c σ σ__c asop σ' ->
      Equal (events σ') {[]} ->
      σ = σ'.
  Proof.
    induction 1; try reflexivity; subst; simpl;
      intros; contrad_add_empty.
  Qed.
  
  Lemma vassocop_not_in_events_if_not_sig :
    forall {Δ Δ__c σ σ__c asop σ' id},
      vassocop Δ Δ__c σ σ__c asop σ' ->
      ~OutputOf Δ id ->
      ~DeclaredOf Δ id ->
      ~NatSet.In id (events σ) ->
      ~NatSet.In id (events σ').
  Proof.
    inversion_clear 1; subst; simpl; auto; intros;
      rewrite add_spec; inversion 1;
        (solve [contradiction] ||
         match goal with
         | [ Hor: MapsTo _ _ _ \/ _ |- _ ] =>
           inversion Hor;
           [ match goal with
             | [ H: MapsTo _ (Declared ?t) _, Hdecl: ~DeclaredOf _ _  |- _ ] =>
               subst; apply Hdecl; exists t; auto
             end
           | match goal with
             | [ H: MapsTo _ (Output ?t) _, Hout: ~OutputOf _ _  |- _ ] =>
               subst; apply Hout; exists t; auto
             end
           ]
         end).
  Qed.

  Lemma vassocop_inv_in_events :
    forall {Δ Δ__c σ σ__c asop σ' id},
      vassocop Δ Δ__c σ σ__c asop σ' ->
      NatSet.In id (events σ) ->
      NatSet.In id (events σ').
  Proof.
    induction 1; auto;
      subst σ'; subst events'; cbn; eauto with set.
  Qed.
  
  Lemma mapop_inv_in_events :
    forall {Δ Δ__c σ σ__c opmap σ' id},
      mapop Δ Δ__c σ σ__c opmap σ' ->
      NatSet.In id (events σ) ->
      NatSet.In id (events σ').
  Proof.
    induction 1; auto; intros.
    eapply IHmapop; eapply vassocop_inv_in_events; eauto.
  Qed.
  
  Lemma mapop_inv_compstore :
    forall {Δ Δ__c σ σ__c1 opmap σ' id__c σ__c2},
      mapop Δ Δ__c σ σ__c1 opmap σ' ->
      MapsTo id__c σ__c2 (compstore σ) ->
      MapsTo id__c σ__c2 (compstore σ').
  Proof.
    induction 1; try subst; auto.
    induction H; try subst; auto.
  Qed.
  
  Lemma mapop_maps_sstore :
    forall {Δ Δ__c σ σ__c opmap σ'},
      mapop Δ Δ__c σ σ__c opmap σ' ->
      forall {id v},
        MapsTo id v (sigstore σ) ->
        exists v', MapsTo id v' (sigstore σ').
  Proof.
    induction 1.
    intros; exists v; assumption.
    intros; edestruct @vassocop_maps_sstore with (Δ := Δ); eauto.
  Qed.
  
  Lemma mapop_not_in_events_if_not_assigned :
    forall {Δ Δ__c σ σ__c opmap σ' id},
      mapop Δ Δ__c σ σ__c opmap σ' ->
      ~NatSet.In id (events σ) ->
      ~AssignedInOPM id opmap ->
      ~NatSet.In id (events σ').
  Proof.
    induction 1; subst; auto.
    inversion H; subst; simpl; auto.
    all : simpl in IHmapop; intros; apply IHmapop;
      auto; rewrite add_spec; firstorder.
  Qed.
  
  Lemma mapop_not_in_events_if_not_sig :
    forall {Δ Δ__c σ σ__c opmap σ' id},
      mapop Δ Δ__c σ σ__c opmap σ' ->
      ~NatSet.In id (events σ) ->
      ~OutputOf Δ id ->
      ~DeclaredOf Δ id ->
      ~NatSet.In id (events σ').
  Proof.
    induction 1; auto.
    intros; apply IHmapop; auto.
    eapply vassocop_not_in_events_if_not_sig; eauto.
  Qed.
    
  Lemma mapop_eq_state_if_no_events :
    forall {Δ Δ__c σ σ__c opmap σ'},
      mapop Δ Δ__c σ σ__c opmap σ' ->
      Equal (events σ') {[]} ->
      σ = σ'.
  Proof.
    induction 1; auto.
    transitivity σ'; auto.
    eapply vassocop_eq_state_if_no_events; eauto.
    rewrite IHmapop; auto.
  Qed.
  
End OPMap.
