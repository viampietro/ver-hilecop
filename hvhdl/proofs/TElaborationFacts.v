(** * Facts about Elaboration of Transition Design *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.proofs.HVhdlElaborationFactsLib.
Require Import hvhdl.proofs.TGenericElaborationFacts.
Require Import hvhdl.proofs.TPortElaborationFacts.

(** ** Facts about the [input_arcs_number] generic constant *)

Lemma elab_T_Δ_in_arcs_nb_1 :
  forall {M__g Δ σ__e},
    EDesign hdstore M__g transition_design Δ σ__e ->
    exists t n, MapsTo Transition.input_arcs_number (Generic t (Vnat n)) Δ.
Proof.
  inversion 1; subst.
  edestruct @EGens_T_Δ_in_arcs_nb_1 with (Δ := EmptyElDesign) as (t, (n, MapsTo_Δ0)); eauto.
  exists t, n.
  eapply EBeh_inv_Δ; eauto.
  erewrite <- @EDecls_inv_gens with (Δ := Δ') (Δ' := Δ''); eauto 1.
  erewrite <- @EPorts_inv_gens with (Δ := Δ0) (Δ' := Δ'); eauto 1.
Qed.

Lemma EBeh_TCI_Δ_in_arcs_nb_1 : 
  forall {Δ σ behavior Δ' σ' id__t gm ipm opm Δ__t},
    EBeh hdstore Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__t Petri.trans_id gm ipm opm) behavior ->
    MapsTo id__t (Component Δ__t) Δ' ->
    exists t n, MapsTo Transition.input_arcs_number (Generic t (Vnat n)) Δ__t.
Proof.
  induction 1; inversion 1.

  (* CASE comp *)
  - subst; subst_transition_design.
    assert (e : Component Δ__t = Component Δ__c) by (eapply MapsTo_add_eqv; eauto).
    inject_left e.
    eapply @elab_T_Δ_in_arcs_nb_1; eauto.
    
  (* CASE left of || *)
  - intros.
    edestruct @EBeh_compid_in_comps with (D__s := hdstore) (behavior := cstmt) as (Δ__t', MapsTo_Δ__t'); eauto.
    assert (MapsTo id__t (Component Δ__t') Δ'') by (eapply EBeh_inv_Δ; eauto).
    assert (e : Component Δ__t = Component Δ__t') by (eapply MapsTo_fun; eauto).
    inject_left e; apply IHEBeh1; auto.
    
  (* CASE right of || *)
  - apply IHEBeh2; auto.  
Qed.

Lemma elab_TCI_Δ_in_arcs_nb_1 :
  forall {d Δ σ__e id__t gm ipm opm Δ__t},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.trans_id gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    exists t n, MapsTo input_arcs_number (Generic t (Vnat n)) Δ__t.
Proof.
  inversion 1.
  eapply EBeh_TCI_Δ_in_arcs_nb_1; eauto.
Qed.

Lemma elab_TCI_Δ_in_arcs_nb_2 :
  forall {d Δ σ__e id__t gm ipm opm Δ__t e v},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.trans_id gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    List.In (assocg_ input_arcs_number e) gm ->
    VExpr EmptyElDesign EmptyDState EmptyLEnv false e v ->
    exists t, MapsTo input_arcs_number (Generic t v) Δ__t.
Admitted.

(** ** Facts about the [reinit_time] input port *)

Lemma elab_T_Δ_rt :
  forall {M__g Δ σ__e},
    EDesign hdstore M__g transition_design Δ σ__e ->
    forall {t n},
      MapsTo input_arcs_number (Generic t (Vnat n)) Δ ->
      MapsTo Transition.reinit_time (Input (Tarray Tbool 0 (n - 1))) Δ.
Proof.
  inversion 1; subst.
  intros t n MapsTo_ian.
  assert (MapsTo Transition.reinit_time (Input (Tarray Tbool 0 (n - 1))) Δ').
  { eapply @EPorts_T_Δ_rt with (Δ := Δ0); eauto.
    match goal with
    | [ H0: EPorts _ _ _ _ _, H1: EDecls _ _ _ _ _, H2: EBeh _ _ _ _ _ _ |- _ ] =>
      rewrite ((EPorts_inv_gens H0) input_arcs_number t (Vnat n));
        rewrite ((EDecls_inv_gens H1) input_arcs_number t (Vnat n));
        rewrite ((EBeh_eq_gens H2) input_arcs_number t (Vnat n));
        assumption
    end. }
  eapply EBeh_inv_Δ; eauto.
  eapply EDecls_inv_Δ; eauto.
Qed.

Lemma EBeh_TCI_Δ_rt : 
  forall {Δ σ behavior Δ' σ'},
    EBeh hdstore Δ σ behavior Δ' σ' ->
    forall {id__t gm ipm opm Δ__t t n},
      InCs (cs_comp id__t Petri.trans_id gm ipm opm) behavior ->
      MapsTo id__t (Component Δ__t) Δ' ->
      MapsTo input_arcs_number (Generic t (Vnat n)) Δ__t ->
      MapsTo Transition.reinit_time (Input (Tarray Tbool 0 (n - 1))) Δ__t.
Proof.
  induction 1; try (solve [inversion 1]).

  (* CASE comp *)
  - inversion 1; subst; subst_transition_design.
    assert (e : Component Δ__t = Component Δ__c) by
        (eapply @MapsTo_add_eqv with (x := id__c) (m := Δ); eauto).
    inject_left e.
    eapply @elab_T_Δ_rt; eauto.
    
  (* CASE || *)
  - inversion 1; intros.

    (* CASE comp ∈ cstmt *)
    eapply IHEBeh1; eauto.
    edestruct @EBeh_compid_in_comps
      with (D__s := hdstore) (behavior := cstmt) as (Δ'__t, MapsTo_Δ'__t); eauto.
    assert (MapsTo id__t (Component Δ'__t) Δ'') by (eapply EBeh_inv_Δ; eauto).
    erewrite MapsTo_fun with (e := Component Δ__t); eauto.
    
    (* CASE comp ∈ cstmt' *)
    eapply IHEBeh2; eauto.
Qed.

Lemma elab_TCI_Δ_rt : 
  forall {d Δ σ__e},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    forall {id__t gm ipm opm Δ__t t n},
      InCs (cs_comp id__t Petri.trans_id gm ipm opm) (behavior d) ->
      MapsTo id__t (Component Δ__t) Δ ->
      MapsTo input_arcs_number (Generic t (Vnat n)) Δ__t ->
      MapsTo Transition.reinit_time (Input (Tarray Tbool 0 (n - 1))) Δ__t.
Proof.
  inversion 1.
  eapply EBeh_TCI_Δ_rt; eauto.
Qed.

Lemma elab_T_σ_rt :
  forall {M__g Δ σ__e},
    EDesign hdstore M__g transition_design Δ σ__e ->
    exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sstore σ__e).
Proof.
  inversion 1; subst.
  edestruct @EPorts_T_σ_rt with (Δ := Δ0) as (aofv, MapsTo_σ); eauto.
  exists aofv.
  eapply EBeh_inv_sstore; eauto.
  eapply EDecls_inv_sstore; eauto.
Qed.

Lemma EBeh_TCI_σ_rt : 
  forall {Δ σ behavior Δ' σ' id__t gm ipm opm σ'__t},
    EBeh hdstore Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__t Petri.trans_id gm ipm opm) behavior ->
    MapsTo id__t σ'__t (cstore σ') ->
    exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sstore σ'__t).
Proof.
  induction 1; inversion 1.

  (* CASE comp *)
  - subst; subst_transition_design.
    assert (e : σ'__t = σ__c) by
        (eapply @MapsTo_add_eqv with (x := id__c) (m := cstore σ); eauto).
    inject_left e.
    eapply @elab_T_σ_rt; eauto.
    
  (* CASE left of || *)
  - intros.
    edestruct @EBeh_compid_in_cstore with (D__s := hdstore) (behavior := cstmt) as (σ'__t0, MapsTo_σ'__t0); eauto.
    assert (MapsTo id__t σ'__t0 (cstore σ'')) by (eapply EBeh_inv_cstore; eauto).
    assert (e : σ'__t0 = σ'__t) by (eapply MapsTo_fun; eauto).
    inject_left e; apply IHEBeh1; auto.
    
  (* CASE right of || *)
  - apply IHEBeh2; auto.  
Qed.

Lemma elab_TCI_σ_rt : 
  forall {d Δ σ__e id__t gm ipm opm σ__te},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.trans_id gm ipm opm) (behavior d) ->
    MapsTo id__t σ__te (cstore σ__e) ->
    exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sstore σ__te).
Proof.
  inversion 1.
  eapply EBeh_TCI_σ_rt; eauto.
Qed.

Lemma elab_TCI_σ_rt_2 : 
  forall {d Δ σ__e id__t gm ipm opm σ__te Δ__t t n},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.trans_id gm ipm opm) (behavior d) ->
    MapsTo id__t σ__te (cstore σ__e) ->
    MapsTo id__t (Component Δ__t) Δ ->
    MapsTo Transition.input_arcs_number (Generic t (Vnat n)) Δ__t ->
    MapsTo Transition.reinit_time (Varr (create_arr (S (((N.to_nat n) - 1) - 0)) (Vbool false) (gt_Sn_O (((N.to_nat n) - 1) - 0)))) (sstore σ__te).
Proof.
  
Admitted.

(** ** Facts about the [s_time_counter] declared signal *)

Lemma elab_TCI_Δ_s_tc :
  forall {d Δ σ__e id__t gm ipm opm Δ__t},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.trans_id gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    InternalOf Δ__t s_time_counter.
Proof.
  inversion 1; subst; intros; eapply @elab_decl_of_comp with (d__e := transition_design); eauto.
  apply NatMap.add_1; reflexivity.
  firstorder.
Qed.

Lemma elab_TCI_Δ_s_rtc :
  forall {d Δ σ__e id__t gm ipm opm Δ__t},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.trans_id gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    InternalOf Δ__t s_reinit_time_counter.
Proof.
  inversion 1; subst; intros; eapply @elab_decl_of_comp with (d__e := transition_design); eauto.
  apply NatMap.add_1; reflexivity.
  firstorder.
Qed.
  



