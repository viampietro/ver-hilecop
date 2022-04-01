(** * Facts about Initialization and Place Design *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.
Require Import common.NatSet.
Require Import common.InAndNoDup.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.proofs.HVhdlCoreFactsLib.
Require Import hvhdl.proofs.HVhdlCoreTacticsLib.
Require Import hvhdl.HVhdlSimulationLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.ValidPortMap.

Require Import hvhdl.proofs.StabilizeFacts.
Require Import hvhdl.proofs.SSEvaluationFacts.
Require Import hvhdl.proofs.PortMapEvaluationFacts.
Require Import hvhdl.proofs.InitializationFacts.
Require Import hvhdl.proofs.PStabilizeFacts.
Require Import hvhdl.proofs.InitializationTactics.
Require Import hvhdl.proofs.SSEvaluationTactics.
Require Import hvhdl.proofs.ExpressionEvaluationTactics.

(** ** Facts about [vruninit] and Place Design *)

Section PVRunInit.

  Lemma vruninit_marking_ps_assign_s_marking :
    forall {Δ σ σ' n},
      vruninit hdstore Δ σ marking_ps σ' ->
      InputOf Δ initial_marking ->
      MapsTo initial_marking (Vnat n) (sigstore σ) ->
      MapsTo s_marking (Vnat n) (sigstore σ').
  Proof.
    inversion_clear 1; intros.
    vseqinv_cl; [ contradiction | ].
    vseqinv; subst; simpl.
    (* CASE event on s_marking *)
    vexprinv_cl.
    match goal with
    | [ H: OVEq _ _ _ |- _ ] =>
      erewrite MapsTo_fun with (e := newv) (e' := Vnat n); eauto;
        eapply NatMap.add_1; eauto
    end.
    match goal with
    | [ H: ~NatMap.In _ _, H': InputOf _ _ |- _ ] =>
      let Hf := fresh "H" in
      elimtype False; apply H; destruct H' as (x, Hf);
        exists (Input x); auto
    end.
    match goal with
    | [ H: InputOf _ _ |- _ ] => destruct H; mapsto_discriminate
    end.
    (* CASE no event on [s_marking] *)
    vexprinv_cl.
    match goal with
    | [ H: OVEq _ _ _ |- _ ] =>
      erewrite MapsTo_fun with (e := newv) (e' := Vnat n) in H; eauto;
        inversion H; subst; auto
    end.
    match goal with
    | [ H: ~NatMap.In _ _, H': InputOf _ _ |- _ ] =>
      let Hf := fresh "H" in
      elimtype False; apply H; destruct H' as (x, Hf);
        exists (Input x); auto
    end.
    match goal with
    | [ H: InputOf _ _ |- _ ] => destruct H; mapsto_discriminate
    end.
  Qed.
  
  Lemma vruninit_marking_ps_no_events_s_marking :
    forall {Δ σ σ' n},
      vruninit hdstore Δ σ marking_ps σ' ->
      InputOf Δ initial_marking ->
      MapsTo initial_marking (Vnat n) (sigstore σ) ->
      ~NatSet.In s_marking (events σ') ->
      MapsTo s_marking (Vnat n) (sigstore σ).
  Proof.
    inversion_clear 1; intros.
    vseqinv_cl; [contradiction |].
    vseqinv; subst; simpl; [
      match goal with
      | [ H: ~NatSet.In _ _ |- _ ] =>
        elimtype False; apply H; simpl; auto with set
      end
    |
    match goal with
    | [ H: VExpr _ _ _ _ _ _ |- _ ] =>
      inversion_clear H
    end
    ].
    match goal with
    | [ H: OVEq _ _ _ |- _ ] =>
      erewrite MapsTo_fun with (e := newv) (e' := Vnat n) in H; eauto;
        inversion H; subst; auto
    end.
    match goal with
    | [ H: ~NatMap.In _ _, H': InputOf _ _ |- _ ] =>
      let Hf := fresh "H" in
      elimtype False; apply H; destruct H' as (x, Hf);
        exists (Input x); auto
    end.
    match goal with
    | [ H: InputOf _ _ |- _ ] => destruct H; mapsto_discriminate
    end.
  Qed.
  
  Lemma vruninit_P_s_marking_eq_nat :    
    forall Δ σ σ' n m,
      vruninit hdstore Δ σ place_behavior σ' ->
      ~NatSet.In s_marking (events σ) ->
      InputOf Δ initial_marking ->
      MapsTo s_marking (Declared (Tnat 0 m)) Δ ->
      MapsTo initial_marking (Vnat n) (sigstore σ) ->
      MapsTo s_marking (Vnat n) (sigstore σ').
  Proof.
    intros *; unfold place_behavior.
    do 2 (rewrite vruninit_par_comm; rewrite <- vruninit_par_assoc);
      rewrite <- vruninit_par_assoc.
    inversion_clear 1; intros.

    (* 2 CASES: [s_marking ∈ events σ'0] or [s_marking ∉ events σ'0] *)
    destruct (In_dec s_marking (events σ'0)).

    (* CASE [s_marking ∈ (events σ'0)] *)
    - erw_IMDS_sstore_1 <- H3; eauto.
      eapply vruninit_marking_ps_assign_s_marking; eauto with set.

    (* CASE [s_marking ∉ (events σ'0)], 
       then [σ(s_marking) = σ'0(s_marking)] *)
    - erw_IMDS_sstore_m <- H3.
      eapply vruninit_marking_ps_no_events_s_marking; eauto.
      eapply not_in_union; eauto.
      eapply vruninit_not_in_events_if_not_assigned; eauto.
      destruct 1; mapsto_discriminate.
      simpl; cbv; lia.    
  Qed.

  Lemma vruninit_s_marking_eq_nat :
    forall Δ σ behavior σ',
      vruninit hdstore Δ σ behavior σ' ->
      forall id__p g__p i__p o__p σ__p σ__p' n Δ__p cids m formals,
        InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) behavior ->
        AreCsCompIds behavior cids -> 
        List.NoDup cids ->
        List.In (associp_ ($initial_marking) (e_nat n)) i__p ->
        Equal (events σ) {[]} ->
        MapsTo id__p (Component Δ__p) Δ ->
        MapsTo id__p σ__p (compstore σ) ->
        NatMap.MapsTo id__p σ__p' (compstore σ') ->
        listipm Δ Δ__p σ [] i__p formals ->
        InputOf Δ__p initial_marking ->
        MapsTo s_marking (Declared (Tnat 0 m)) Δ__p ->
        ~NatSet.In s_marking (events σ__p) ->
        NatMap.MapsTo Place.s_marking (Vnat n) (sigstore σ__p').
  Proof.
    induction 1; try (solve [inversion 1]).

    (* CASE eventful component *)
    - inversion 1; subst; subst_place_design.
      clear IHvruninit; simpl in *.
      erewrite @MapsTo_fun with (e' := σ__c) (e := σ__p) in *; eauto.
      erewrite @MapsTo_add_eqv with (e' := σ__c'') (e := σ__p'); eauto.
      assert (e : Component Δ__p = Component Δ__c) by (eapply MapsTo_fun; eauto).
      inject_left e.
      eapply vruninit_P_s_marking_eq_nat; eauto.
      eapply mapip_not_in_events_if_not_input; eauto.
      destruct 1; mapsto_discriminate.
      edestruct @mapip_eval_simpl_associp with (Δ := Δ) as (v, (vexpr_v, MapsTo_σ__c'));
        eauto; inversion vexpr_v; subst; try assumption.

    (* CASE eventless component *)
    - inversion 1; subst; subst_place_design.
      clear IHvruninit; simpl in *.
      erewrite @MapsTo_fun with (e := σ__p') (e' := σ__c); eauto;
        [ | eapply mapop_inv_compstore; eauto ].
      (* [events σ__c'' = ∅ then σ__c = σ__c'' ] *)
      (* erewrite mapip_eq_state_if_no_events; eauto; *)
      (* [ pattern σ__c'; erewrite vruninit_eq_state_if_no_events; eauto *)
      (* | erewrite @vruninit_eq_state_if_no_events with (σ' := σ__c''); eauto ]. *)
      (* With no events, s_marking ⇐ initial_marking happened,
         but both already had the same value. *)
      (* assert (e : Component Δ__p = Component Δ__c) by (eapply MapsTo_fun; eauto). *)
      (* inject_left e. *)
      (* eapply vruninit_P_s_marking_eq_nat; eauto. *)
      (* eapply mapip_not_in_events_if_not_input; eauto. *)
      (* destruct 1; mapsto_discriminate. *)
      (* erewrite <- @MapsTo_fun with (e := σ__p) (e' := σ__c); eauto. *)
      (* edestruct @mapip_eval_simpl_associp with (Δ := Δ) as (v, (vexpr_v, MapsTo_σ__c')); *)
      (*   eauto; inversion vexpr_v; subst; assumption. *)
      admit.
      
    (* CASE || *)
    - inversion_clear 1;
        destruct (AreCsCompIds_ex cstmt) as (cids1, HAreCsCompIds1);
        destruct (AreCsCompIds_ex cstmt') as (cids2, HAreCsCompIds2).
      
      (* SUBCASE [comp ∈ cstmt] *)
      + intros; eapply IHvruninit1; eauto; [ solve_nodup_compids_l | solve_vruninit_par_l ].        
      (* SUBCASE [comp ∈ cstmt'] *)
      + intros; eapply IHvruninit2; eauto; [ solve_nodup_compids_r | solve_vruninit_par_r ].
  Admitted.
  
End PVRunInit.

(** ** Facts about [init] and Place Design *)

Section PInit.

  Lemma init_s_marking_eq_nat :
    forall Δ σ behavior σ0,
      init hdstore Δ σ behavior σ0 ->
      forall id__p g__p i__p o__p σ__p σ__p0 n Δ__p cids mm formals,
        InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) behavior ->
        Equal (events σ) {[]} ->
        MapsTo id__p (Component Δ__p) Δ ->
        MapsTo id__p σ__p (compstore σ) ->
        AreCsCompIds behavior cids ->
        List.NoDup cids ->
        listipm Δ Δ__p σ [] i__p formals ->
        List.In (associp_ ($initial_marking) (e_nat n)) i__p ->
        InputOf Δ__p initial_marking ->
        MapsTo id__p σ__p0 (compstore σ0) ->
        ~NatSet.In s_marking (events σ__p) ->
        MapsTo Place.s_marking (Declared (Tnat 0 mm)) Δ__p ->
        MapsTo Place.s_marking (Vnat n) (sigstore σ__p0).
  Proof.
    inversion 1.
    intros.

    (* [∃ σ__p s.t. σ(id__p) = σ__p] *)
    match goal with
    | [ MapsTo_σ__p: MapsTo id__p σ__p _, Hvr: vruninit _ _ _ _ _ |- _ ] =>
      specialize (vruninit_maps_compstore_id Hvr MapsTo_σ__p) as ex_MapsTo_σp';
        inversion ex_MapsTo_σp' as (σ__p', MapsTo_σ__p'); clear ex_MapsTo_σp'
    end.
    
    (* [s_marking] value stays the same during stabilization. *)
    eapply stab_inv_s_marking; eauto.    

    (* [s_marking] takes [n] during [vruninit], if [<initial_marking => n>] *)
    eapply vruninit_s_marking_eq_nat; eauto.
  Qed.

  Lemma init_PCI_eval_rtt_i :
    forall D__s Δ σ behavior σ0,
      init D__s Δ σ behavior σ0 ->
      forall id__p g__p i__p o__p σ__p0 aofv id i b ,
        InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) behavior ->
        MapsTo id__p σ__p0 (compstore σ0) ->
        MapsTo reinit_transitions_time (Varr aofv) (sigstore σ__p0) ->
        List.In (assocop_idx reinit_transitions_time (e_nat i) ($id)) o__p ->
        get_bool_at aofv (N.to_nat i) = b ->
        MapsTo id (Vbool b) (sigstore σ0).
  Admitted.
  
  Lemma init_PCI_rtt_eq_false :
    forall D__s Δ σ behavior σ0,
      init D__s Δ σ behavior σ0 ->
      forall id__p g__p i__p o__p σ__p0 Δ__p aofv i t n,
        InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) behavior ->
        MapsTo id__p (Component Δ__p) Δ ->
        MapsTo output_arcs_number (Generic t (Vnat n)) Δ__p ->
        MapsTo id__p σ__p0 (compstore σ0) ->
        MapsTo reinit_transitions_time (Varr aofv) (sigstore σ__p0) ->
        0 <= i < n ->
        get_bool_at aofv (N.to_nat i) = false.
  Admitted.
  
End PInit.



