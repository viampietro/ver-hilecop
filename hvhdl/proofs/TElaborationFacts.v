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
    edesign hdstore M__g transition_design Δ σ__e ->
    exists t n, MapsTo Transition.input_arcs_number (Generic t (Vnat n)) Δ.
Proof.
  inversion 1; subst.
  edestruct @egens_T_Δ_in_arcs_nb_1 with (Δ := EmptyElDesign) as (t, (n, MapsTo_Δ0)); eauto.
  exists t, n.
  eapply ebeh_inv_Δ; eauto.
  erewrite <- @edecls_inv_gens with (Δ := Δ') (Δ' := Δ''); eauto 1.
  erewrite <- @eports_inv_gens with (Δ := Δ0) (Δ' := Δ'); eauto 1.
Qed.

Lemma ebeh_TCI_Δ_in_arcs_nb_1 : 
  forall {Δ σ behavior Δ' σ' id__t gm ipm opm Δ__t},
    ebeh hdstore Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
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
    edestruct @ebeh_compid_in_comps with (D__s := hdstore) (behavior := cstmt) as (Δ__t', MapsTo_Δ__t'); eauto.
    assert (MapsTo id__t (Component Δ__t') Δ'') by (eapply ebeh_inv_Δ; eauto).
    assert (e : Component Δ__t = Component Δ__t') by (eapply MapsTo_fun; eauto).
    inject_left e; apply IHebeh1; auto.
    
  (* CASE right of || *)
  - apply IHebeh2; auto.  
Qed.

Lemma elab_TCI_Δ_in_arcs_nb_1 :
  forall {d Δ σ__e id__t gm ipm opm Δ__t},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    exists t n, MapsTo input_arcs_number (Generic t (Vnat n)) Δ__t.
Proof.
  inversion 1.
  eapply ebeh_TCI_Δ_in_arcs_nb_1; eauto.
Qed.

Lemma elab_TCI_Δ_in_arcs_nb_2 :
  forall {d Δ σ__e id__t gm ipm opm Δ__t e v},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    List.In (assocg_ input_arcs_number e) gm ->
    vexpr EmptyElDesign EmptyDState EmptyLEnv false e v ->
    exists t, MapsTo input_arcs_number (Generic t v) Δ__t.
Admitted.

(** ** Facts about the [reinit_time] input port *)

Lemma elab_T_Δ_rt :
  forall {M__g Δ σ__e},
    edesign hdstore M__g transition_design Δ σ__e ->
    forall {t n},
      MapsTo input_arcs_number (Generic t (Vnat n)) Δ ->
      MapsTo Transition.reinit_time (Input (Tarray Tbool 0 (n - 1))) Δ.
Proof.
  inversion 1; subst.
  intros t n MapsTo_ian.
  assert (MapsTo Transition.reinit_time (Input (Tarray Tbool 0 (n - 1))) Δ').
  { eapply @eports_T_Δ_rt with (Δ := Δ0); eauto.
    match goal with
    | [ H0: eports _ _ _ _ _, H1: edecls _ _ _ _ _, H2: ebeh _ _ _ _ _ _ |- _ ] =>
      rewrite ((eports_inv_gens H0) input_arcs_number t (Vnat n));
        rewrite ((edecls_inv_gens H1) input_arcs_number t (Vnat n));
        rewrite ((ebeh_eq_gens H2) input_arcs_number t (Vnat n));
        assumption
    end. }
  eapply ebeh_inv_Δ; eauto.
  eapply edecls_inv_Δ; eauto.
Qed.

Lemma ebeh_TCI_Δ_rt : 
  forall {Δ σ behavior Δ' σ'},
    ebeh hdstore Δ σ behavior Δ' σ' ->
    forall {id__t gm ipm opm Δ__t t n},
      InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
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
    eapply IHebeh1; eauto.
    edestruct @ebeh_compid_in_comps
      with (D__s := hdstore) (behavior := cstmt) as (Δ'__t, MapsTo_Δ'__t); eauto.
    assert (MapsTo id__t (Component Δ'__t) Δ'') by (eapply ebeh_inv_Δ; eauto).
    erewrite MapsTo_fun with (e := Component Δ__t); eauto.
    
    (* CASE comp ∈ cstmt' *)
    eapply IHebeh2; eauto.
Qed.

Lemma elab_TCI_Δ_rt : 
  forall {d Δ σ__e},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    forall {id__t gm ipm opm Δ__t t n},
      InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
      MapsTo id__t (Component Δ__t) Δ ->
      MapsTo input_arcs_number (Generic t (Vnat n)) Δ__t ->
      MapsTo Transition.reinit_time (Input (Tarray Tbool 0 (n - 1))) Δ__t.
Proof.
  inversion 1.
  eapply ebeh_TCI_Δ_rt; eauto.
Qed.

Lemma elab_T_σ_rt :
  forall {M__g Δ σ__e},
    edesign hdstore M__g transition_design Δ σ__e ->
    exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sigstore σ__e).
Proof.
  inversion 1; subst.
  edestruct @eports_T_σ_rt with (Δ := Δ0) as (aofv, MapsTo_σ); eauto.
  exists aofv.
  eapply ebeh_inv_sigstore; eauto.
  eapply edecls_inv_sigstore; eauto.
Qed.

Lemma ebeh_TCI_σ_rt : 
  forall {Δ σ behavior Δ' σ' id__t gm ipm opm σ'__t},
    ebeh hdstore Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) behavior ->
    MapsTo id__t σ'__t (compstore σ') ->
    exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sigstore σ'__t).
Proof.
  induction 1; inversion 1.

  (* CASE comp *)
  - subst; subst_transition_design.
    assert (e : σ'__t = σ__c) by
        (eapply @MapsTo_add_eqv with (x := id__c) (m := compstore σ); eauto).
    inject_left e.
    eapply @elab_T_σ_rt; eauto.
    
  (* CASE left of || *)
  - intros.
    edestruct @ebeh_compid_in_compstore with (D__s := hdstore) (behavior := cstmt) as (σ'__t0, MapsTo_σ'__t0); eauto.
    assert (MapsTo id__t σ'__t0 (compstore σ'')) by (eapply ebeh_inv_compstore; eauto).
    assert (e : σ'__t0 = σ'__t) by (eapply MapsTo_fun; eauto).
    inject_left e; apply IHebeh1; auto.
    
  (* CASE right of || *)
  - apply IHebeh2; auto.  
Qed.

Lemma elab_TCI_σ_rt : 
  forall {d Δ σ__e id__t gm ipm opm σ__te},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t σ__te (compstore σ__e) ->
    exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sigstore σ__te).
Proof.
  inversion 1.
  eapply ebeh_TCI_σ_rt; eauto.
Qed.

Lemma elab_TCI_σ_rt_2 : 
  forall {d Δ σ__e id__t gm ipm opm σ__te Δ__t t n},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t σ__te (compstore σ__e) ->
    MapsTo id__t (Component Δ__t) Δ ->
    MapsTo Transition.input_arcs_number (Generic t (Vnat n)) Δ__t ->
    MapsTo Transition.reinit_time (Varr (create_arr (S ((n - 1) - 0)) (Vbool false) (gt_Sn_O ((n - 1) - 0)))) (sigstore σ__te).
Proof.
  
Admitted.

(** ** Facts about the [s_time_counter] declared signal *)

Lemma elab_TCI_Δ_s_tc :
  forall {d Δ σ__e id__t gm ipm opm Δ__t},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    DeclaredOf Δ__t s_time_counter.
Proof.
  inversion 1; subst; intros; eapply @elab_decl_of_comp with (d__e := transition_design); eauto.
  apply NatMap.add_1; reflexivity.
  firstorder.
Qed.

Lemma elab_TCI_Δ_s_rtc :
  forall {d Δ σ__e id__t gm ipm opm Δ__t},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    DeclaredOf Δ__t s_reinit_time_counter.
Proof.
  inversion 1; subst; intros; eapply @elab_decl_of_comp with (d__e := transition_design); eauto.
  apply NatMap.add_1; reflexivity.
  firstorder.
Qed.
  



