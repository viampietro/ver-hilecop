(** * Facts about Design Elaboration Relations *)

Require Import common.CoqLib.
Require Import common.proofs.CoqTactics.
Require Import common.NatSet.
Require Import common.NatMap.
Require Import common.InAndNoDup.
Require Import common.proofs.NatMapTactics.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.proofs.AbstractSyntaxFacts.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.Place.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.ValidPortMap.
Require Import hvhdl.proofs.WellDefinedDesignFacts.
Require Import hvhdl.proofs.ArchitectureElaborationFacts.
Require Import hvhdl.proofs.PortElaborationFacts.
Require Import hvhdl.proofs.ValidPortMapFacts.
Require Import hvhdl.proofs.DefaultValueFacts.
Require Import hvhdl.proofs.GenericElaborationFacts.

Require Import hvhdl.proofs.EnvironmentFacts.

(** ** Facts about Behavior Elaboration *)

Lemma ebeh_eq_gens :
  forall {D__s Δ σ behavior Δ' σ'},
    ebeh D__s Δ σ behavior Δ' σ' ->
    EqGens Δ Δ'.
Proof.
  induction 1; (reflexivity || auto).
  unfold EqGens; intros; try solve_mapsto_iff.
  unfold EqGens; intros; try solve_mapsto_iff.
  transitivity Δ'; eauto with hvhdl.
Qed.

#[export] Hint Resolve ebeh_eq_gens : hvhdl.

Lemma ebeh_eq_sigs :
  forall {D__s Δ σ behavior Δ' σ'},
    ebeh D__s Δ σ behavior Δ' σ' ->
    EqSigs Δ Δ'.
Proof.
  induction 1; (reflexivity || auto).
  unfold EqSigs; intros; split_and; do 2 intro; try solve_mapsto_iff.
  unfold EqSigs; intros; split_and; do 2 intro; try solve_mapsto_iff.
  transitivity Δ'; eauto with hvhdl.
Qed.

Lemma ebeh_eq_sstore :
  forall {D__s Δ σ behavior Δ' σ'},
    ebeh D__s Δ σ behavior Δ' σ' ->
    EqSStore σ σ'.
Proof.
  induction 1; try reflexivity.
  unfold EqSStore; simpl; reflexivity.
  transitivity σ'; auto.
Qed.

Lemma ebeh_inv_Δ :
  forall {D__s Δ σ behavior Δ' σ' id sobj},
    ebeh D__s Δ σ behavior Δ' σ' ->
    MapsTo id sobj Δ ->
    MapsTo id sobj Δ'.
Proof.
  induction 1; intros; auto;
  match goal with
   | [ H: ~NatMap.In (elt:=_) ?id2 _ |- MapsTo ?id1 _ (add ?id2 _ _) ] =>
       destruct (Nat.eq_dec id2 id1) as [e | ne];
         [elimtype False; apply H; exists sobj; rewrite e; assumption
         | eapply add_2; eauto]
  end.
Qed.

Lemma ebeh_inv_sstore :
  forall D__s Δ σ beh Δ' σ' id v,
    ebeh D__s Δ σ beh Δ' σ' ->
    MapsTo id v (sstore σ) ->
    MapsTo id v (sstore σ').
Proof. induction 1; intros; auto. Defined.

Lemma ebeh_inv_cstore :
  forall {D__s Δ σ behavior Δ' σ' id σ__c},
    ebeh D__s Δ σ behavior Δ' σ' ->
    MapsTo id σ__c (cstore σ) ->
    MapsTo id σ__c (cstore σ').
Proof.
  induction 1; intros; auto; simpl.
  match goal with
  | [ H: ~NatMap.In (elt:=DState) ?id2 _ |- MapsTo ?id1 _ (add ?id2 _ _) ] =>
    destruct (Nat.eq_dec id2 id1) as [e | ne];
      [elimtype False; apply H; exists σ__c; rewrite e; assumption
      | eapply add_2; eauto]
  end.
Qed.

Lemma ebeh_compid_in_comps :
  forall {D__s Δ σ behavior Δ' σ' id__c id__e gm ipm opm},
    ebeh D__s Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__c id__e gm ipm opm) behavior ->
    exists Δ__c, MapsTo id__c (Component Δ__c) Δ'.
Proof.
  induction 1; inversion 1.
  exists Δ__c; apply add_1; auto.
  - edestruct IHebeh1 as (Δ__c, MapsTo_Δ'); eauto; exists Δ__c.
    eapply ebeh_inv_Δ; eauto.
  - eapply IHebeh2; eauto.
Qed.

Lemma ebeh_compid_in_cstore :
  forall {D__s Δ σ behavior Δ' σ' id__c id__e gm ipm opm},
    ebeh D__s Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__c id__e gm ipm opm) behavior ->
    exists σ__c, MapsTo id__c σ__c (cstore σ').
Proof.
  induction 1; inversion 1.
  exists σ__c; apply add_1; auto.
  - edestruct IHebeh1 as (σ__c, MapsTo_σ'); eauto; exists σ__c.
    eapply ebeh_inv_cstore; eauto.
  - eapply IHebeh2; eauto.
Qed.

Lemma ebeh_compid_is_unique :
  forall {D__s Δ σ behavior Δ' σ' id__c id__e gm ipm opm},
    ebeh D__s Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__c id__e gm ipm opm) behavior ->
    ~NatMap.In id__c Δ /\ ~NatMap.In id__c (cstore σ).
Proof.
  induction 1; inversion 1; auto.
  edestruct (IHebeh2) as (nIn_Δ, nIn_cstore); eauto; split; destruct 1.
  - apply nIn_Δ; eexists; eapply ebeh_inv_Δ; eauto.
  - apply nIn_cstore; eexists; eapply ebeh_inv_cstore; eauto.
Qed.

Lemma ebeh_nodup_compids :
  forall {D__s Δ σ behavior Δ' σ'},
    ebeh D__s Δ σ behavior Δ' σ' ->
    forall {compids},
      AreCsCompIds behavior compids ->
      List.NoDup compids.
Proof.
  induction 1; inversion_clear 1; try (rewrite app_nil_l); auto.

  (* CASE (cstmt || cstmt') *)
  rename a' into compids1.
  edestruct @AreCsCompIds_ex with (cstmt := cstmt') as (compids2, AreCsCompIds2).
  erewrite @FoldLCs_determ with (res := compids) (res' := compids1 ++ compids2); eauto;
    try (apply (AreCsCompIds_app1 cstmt' compids2 AreCsCompIds2 compids1)).
  apply NoDup_app_cons; [ apply IHebeh1; auto | apply IHebeh2; auto | ].

  (* Prove [∀id ∈ compids1, id ∉ compids2] *)
  intros id__c In_compids1 In_compids2.
  edestruct (proj1 (AreCsCompIds_compid_iff H2)) as (id__e1, (gm1, (ipm1, (opm1, InCs_id__c1)))); eauto.
  edestruct (proj1 (AreCsCompIds_compid_iff AreCsCompIds2)) as (id__e2, (gm2, (ipm2, (opm2, InCs_id__c2)))); eauto.
  edestruct @ebeh_compid_in_comps with (D__s := D__s) (behavior := cstmt); eauto.
  eapply (proj1 (ebeh_compid_is_unique H0 InCs_id__c2)); eauto.
  exists (Component x); assumption.
Qed.

Lemma ebeh_inv_events:
  forall {D__s Δ σ behavior Δ' σ'},
    ebeh D__s Δ σ behavior Δ' σ' ->
    NatSet.Equal (events σ) (events σ').
Proof.
  induction 1; auto with set.
  transitivity (events σ'); auto.
Qed.

(** ** Facts about the [edesign] relation *)

Lemma elab_compid_in_comps :
  forall {D__s M__g d Δ σ__e id__c id__e gm ipm opm},
    edesign D__s M__g d Δ σ__e ->
    InCs (cs_comp id__c id__e gm ipm opm) (behavior d) ->
    exists Δ__c, MapsTo id__c (Component Δ__c) Δ.
Proof.
  inversion 1.
  eapply ebeh_compid_in_comps; eauto.
Qed.

Lemma elab_compid_in_cstore :
  forall {D__s M__g d Δ σ__e id__c id__e gm ipm opm},
    edesign D__s M__g d Δ σ__e ->
    InCs (cs_comp id__c id__e gm ipm opm) (behavior d) ->
    exists σ__c, MapsTo id__c σ__c (cstore σ__e).
Proof.
  inversion 1.
  eapply ebeh_compid_in_cstore; eauto.
Qed.

Lemma elab_nodup_compids :
  forall {D__s M__g d Δ σ__e compids},
    edesign D__s M__g d Δ σ__e ->
    AreCsCompIds (behavior d) compids ->
    List.NoDup compids.
Proof.
  inversion 1.
  eapply ebeh_nodup_compids; eauto.
Qed.

Lemma elab_empty_events:
  forall {D__s M__g d Δ σ__e},
    edesign D__s M__g d Δ σ__e ->
    NatSet.Equal (events σ__e) {[]}.
Proof.
  inversion 1; subst.
  erewrite <- ebeh_inv_events; eauto.
  erewrite <- edecls_inv_events; eauto.
  erewrite <- eports_inv_events; eauto.
  simpl; auto with set.
Qed.

Lemma ebeh_empty_events_for_comps:
  forall {D__s Δ σ behavior Δ' σ'},
    ebeh D__s Δ σ behavior Δ' σ' ->
    forall { id__c id__e gm ipm opm σ__c'},
      InCs (cs_comp id__c id__e gm ipm opm) behavior ->
      MapsTo id__c σ__c' (cstore σ') ->
      NatSet.Equal (events σ__c') {[]}.
Proof.
  induction 1; try (solve [inversion 1]).
  
  (* CASE comp *)
  - inversion_clear 1; simpl; intros.
    erewrite @MapsTo_add_eqv with (e := σ__c'); eauto.
    eapply elab_empty_events; eauto.

  (* CASE || *)
  - inversion_clear 1; simpl; intros.
    (* SUBCASE comp ∈ cstmt *)
    eapply IHebeh1; eauto.
    edestruct @ebeh_compid_in_cstore
      with (D__s := D__s) (behavior := cstmt)
      as (σ__c0', MapsTo_σ'); eauto.
    assert (MapsTo id__c σ__c0' (cstore σ''))
      by (eapply ebeh_inv_cstore; eauto).
    erewrite MapsTo_fun with (e := σ__c'); eauto.
    (* SUBCASE comp ∈ cstmt' *)
    eapply IHebeh2; eauto.
Qed.

Lemma elab_empty_events_for_comps:
  forall {D__s M__g d Δ σ__e},
    edesign D__s M__g d Δ σ__e ->
    forall {id__c id__e gm ipm opm σ__ce},
      InCs (cs_comp id__c id__e gm ipm opm) (behavior d) ->
      MapsTo id__c σ__ce (cstore σ__e) ->
      NatSet.Equal (events σ__ce) {[]}.
Proof.
  inversion 1.
  eapply ebeh_empty_events_for_comps; eauto.
Qed.

Lemma elab_input :
  forall {D__s M__g d Δ σ__e id τ},
    edesign D__s M__g d Δ σ__e ->
    List.In (pdecl_in id τ) (ports d) ->
    InputOf Δ id.
Proof.
  inversion 1; subst; intros.
  edestruct @eports_input with (Δ := Δ0) as (t, MapsTo_Δ'); eauto. 
  exists t; eapply ebeh_inv_Δ; eauto.
  eapply edecls_inv_Δ; eauto.
Qed.

Lemma elab_decl :
  forall {D__s M__g d Δ σ__e id τ},
    edesign D__s M__g d Δ σ__e ->
    List.In (sdecl_ id τ) (sigs d) ->
    DeclaredOf Δ id.
Proof.
  inversion 1; subst; intros.
  edestruct @edecls_decl with (Δ := Δ') as (t, MapsTo_Δ'); eauto. 
  exists t; eapply ebeh_inv_Δ; eauto.
Qed.

Lemma ebeh_input_of_comp :
  forall {D__s Δ σ behavior Δ' σ' id__c id__e gm ipm opm d__e Δ__c id τ},
    ebeh D__s Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__c id__e gm ipm opm) behavior ->
    MapsTo id__e d__e D__s ->
    MapsTo id__c (Component Δ__c) Δ' ->
    List.In (pdecl_in id τ) (ports d__e) ->
    InputOf Δ__c id.
Proof.
  induction 1; try (solve [inversion 1]).

  (* CASE comp *)
  - inversion_clear 1; simpl; intros.
    assert (e : Component Δ__c = Component Δ__c0)
      by (eapply @MapsTo_add_eqv; eauto).
    inject_left e.
    eapply elab_input; eauto.
    erewrite MapsTo_fun with (e := cdesign); eauto.
    
  (* CASE || *)
  - inversion_clear 1; simpl; intros.
    (* SUBCASE comp ∈ cstmt *)
    eapply IHebeh1; eauto.
    edestruct @ebeh_compid_in_comps
      with (D__s := D__s) (behavior := cstmt)
      as (Δ__c0, MapsTo_Δ__c0); eauto.
    assert (MapsTo id__c (Component Δ__c0) Δ'')
      by (eapply ebeh_inv_Δ; eauto).
    assert (e : Component Δ__c = Component  Δ__c0)
      by (eapply MapsTo_fun; eauto).
    inject_left e; auto.
    (* SUBCASE comp ∈ cstmt' *)
    eapply IHebeh2; eauto.
Qed.

Lemma elab_input_of_comp :
  forall {D__s M__g d Δ σ__e id__c id__e gm ipm opm d__e Δ__c id τ},
    edesign D__s M__g d Δ σ__e ->
    InCs (cs_comp id__c id__e gm ipm opm) (behavior d) ->
    MapsTo id__e d__e D__s ->
    MapsTo id__c (Component Δ__c) Δ ->
    List.In (pdecl_in id τ) (ports d__e) ->
    InputOf Δ__c id.
Proof.
  inversion 1.
  eapply ebeh_input_of_comp; eauto.
Qed.

Lemma ebeh_decl_of_comp :
  forall {D__s Δ σ behavior Δ' σ' id__c id__e gm ipm opm d__e Δ__c id τ},
    ebeh D__s Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__c id__e gm ipm opm) behavior ->
    MapsTo id__e d__e D__s ->
    MapsTo id__c (Component Δ__c) Δ' ->
    List.In (sdecl_ id τ) (sigs d__e) ->
    DeclaredOf Δ__c id.
Proof.
  induction 1; try (solve [inversion 1]).

  (* CASE comp *)
  - inversion_clear 1; simpl; intros.
    assert (e : Component Δ__c = Component Δ__c0)
      by (eapply @MapsTo_add_eqv; eauto).
    inject_left e.
    eapply elab_decl; eauto.
    erewrite MapsTo_fun with (e := cdesign); eauto.
    
  (* CASE || *)
  - inversion_clear 1; simpl; intros.
    (* SUBCASE comp ∈ cstmt *)
    eapply IHebeh1; eauto.
    edestruct @ebeh_compid_in_comps
      with (D__s := D__s) (behavior := cstmt)
      as (Δ__c0, MapsTo_Δ__c0); eauto.
    assert (MapsTo id__c (Component Δ__c0) Δ'')
      by (eapply ebeh_inv_Δ; eauto).
    assert (e : Component Δ__c = Component  Δ__c0)
      by (eapply MapsTo_fun; eauto).
    inject_left e; auto.
    (* SUBCASE comp ∈ cstmt' *)
    eapply IHebeh2; eauto.
Qed.

Lemma elab_decl_of_comp :
  forall {D__s M__g d Δ σ__e id__c id__e gm ipm opm d__e Δ__c id τ},
    edesign D__s M__g d Δ σ__e ->
    InCs (cs_comp id__c id__e gm ipm opm) (behavior d) ->
    MapsTo id__e d__e D__s ->
    MapsTo id__c (Component Δ__c) Δ ->
    List.In (sdecl_ id τ) (sigs d__e) ->
    DeclaredOf Δ__c id.
Proof.
  inversion 1.
  eapply ebeh_decl_of_comp; eauto.
Qed.

Lemma ebeh_validipm :
  forall {D__s Δ σ behavior Δ' σ'},
    ebeh D__s Δ σ behavior Δ' σ' ->
    forall {id__c id__e gm ipm opm Δ__c},
      InCs (cs_comp id__c id__e gm ipm opm) behavior ->
      MapsTo id__c (Component Δ__c) Δ' ->
      exists formals, listipm Δ' Δ__c σ' [] ipm formals /\ checkformals Δ__c formals.
Proof.
  induction 1; try (solve [inversion 1]).

  (* CASE comp *)
  - inversion 1; subst; intros.
    assert (e : Component Δ__c0 = Component Δ__c).
    erewrite @MapsTo_add_eqv with (e := Component Δ__c0) (e' := Component Δ__c); eauto.
    inject_left e.
    match goal with
    | [ H: validipm _ _ _ _ |- _ ] =>
        destruct H; exists formals; split; auto
    end.
    (* SUBCASE listpipm *)
    erewrite @listipm_eq_iff_eq_sigs with (Δ2 := Δ) (σ2 := σ); eauto.
    (* Prove EqGens, EqSigs and EqSStore *)
    split; unfold EqGens; intros; try solve_mapsto_iff.
    split; unfold EqIns; intros; try solve_mapsto_iff.
    split; unfold EqOuts; intros; try solve_mapsto_iff.
    unfold EqDecls; intros; try solve_mapsto_iff.
    simpl; firstorder.

  (* CASE || *)
  - inversion 1; [intros | eapply IHebeh2; eauto].
    edestruct @ebeh_compid_in_comps with (D__s := D__s) (behavior := cstmt); eauto.
    edestruct IHebeh1 as (formals, (listipm1, checkformals1)); eauto.
    assert (MapsTo id__c (Component x) Δ'') by (eapply ebeh_inv_Δ; eauto).
    assert (e : Component Δ__c = Component x) by (eapply MapsTo_fun; eauto).
    inject_left e.
    exists formals; split; [|auto].
    erewrite <- listipm_eq_iff_eq_sigs; eauto.    
    split; [eapply ebeh_eq_gens; eauto | eapply ebeh_eq_sigs; eauto ].
    eapply ebeh_eq_sstore; eauto.
Qed.

Lemma elab_validipm :
  forall {D__s M__g d Δ σ__e},
    edesign D__s M__g d Δ σ__e ->
    forall {id__c id__e gm ipm opm Δ__c},
      InCs (cs_comp id__c id__e gm ipm opm) (behavior d) ->
      MapsTo id__c (Component Δ__c) Δ ->
      exists formals, listipm Δ Δ__c σ__e [] ipm formals /\ checkformals Δ__c formals.
Proof.
  inversion 1.
  eapply ebeh_validipm; eauto.
Qed.

Lemma elab_wf_gmap_expr :
  forall {D__s M__g d Δ σ__e id__c id__e gm ipm opm id e},
    edesign D__s M__g d Δ σ__e ->
    InCs (cs_comp id__c id__e gm ipm opm) (behavior d) ->
    List.In (assocg_ id e) gm ->
    exists v, VExpr EmptyElDesign EmptyDState EmptyLEnv false e v.
Admitted.

Lemma ebeh_inv_well_typed_values_in_sstore :
  forall {D__s Δ σ behavior Δ' σ'},
    ebeh D__s Δ σ behavior Δ' σ' ->
    (forall {id t v},
        (MapsTo id (Declared t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
        MapsTo id v (sstore σ) ->
        IsOfType v t) ->
    forall {id t v},
      (MapsTo id (Declared t) Δ' \/ MapsTo id (Input t) Δ' \/ MapsTo id (Output t) Δ') ->
      MapsTo id v (sstore σ') ->
      IsOfType v t.
Proof.
  intros *; intros ebeh_ WT; intros *; intros MapsTo_or MapsTo_sstore.
  eapply WT with (id := id); eauto.
  2: { pattern σ; rewrite (ebeh_eq_sstore ebeh_); eauto. }
  inversion_clear MapsTo_or as [ | MapsTo_or1];
    [ left; rewrite (ebeh_eq_sigs ebeh_); assumption
    |  inversion_clear MapsTo_or1 as [ | MapsTo_or2];
        [ right; left; rewrite (ebeh_eq_sigs ebeh_); assumption
         | right; right; rewrite (ebeh_eq_sigs ebeh_); assumption ] ].
Qed.

Lemma elab_well_typed_values_in_sstore :
  forall {D__s M__g d Δ σ__e},
    edesign D__s M__g d Δ σ__e ->
    forall {id t v},
      (MapsTo id (Declared t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
      MapsTo id v (sstore σ__e) ->
      IsOfType v t.
Proof.
  inversion 1.
  eapply ebeh_inv_well_typed_values_in_sstore; eauto.
  eapply edecls_inv_well_typed_values_in_sstore; eauto.
  eapply eports_inv_well_typed_values_in_sstore; eauto.
  cbn; inversion 2.
Qed.

Lemma ebeh_inv_well_typed_values_in_sstore_of_comp :
  forall {D__s Δ σ behavior Δ' σ'},
    ebeh D__s Δ σ behavior Δ' σ' ->
    (forall {id__c Δ__c σ__c},
        MapsTo id__c (Component Δ__c) Δ ->
        MapsTo id__c σ__c (cstore σ) ->
        forall {id t v},
          (MapsTo id (Declared t) Δ__c \/ MapsTo id (Input t) Δ__c \/ MapsTo id (Output t) Δ__c) ->
          MapsTo id v (sstore σ__c) ->
          IsOfType v t) ->
    forall {id__c Δ'__c σ'__c},
      MapsTo id__c (Component Δ'__c) Δ' ->
      MapsTo id__c σ'__c (cstore σ') ->
      forall {id t v},
        (MapsTo id (Declared t) Δ'__c \/ MapsTo id (Input t) Δ'__c \/ MapsTo id (Output t) Δ'__c) ->
        MapsTo id v (sstore σ'__c) ->
        IsOfType v t.
Proof.
  induction 1.

  (* CASE Process *)
  - intros WT; intros; eapply WT; eauto.
    eapply add_3 with (x := id__p) (e' := Process Λ); eauto.
    intros eq_id.
    inject_right eq_id; mapsto_discriminate.

  (* CASE Component *)
  - cbn; intros WT; intros.
    (* 2 CASES: [id__c0 = id__c] or [id__c0 ≠ id__c] *)
    destruct (Nat.eq_dec id__c0 id__c) as [ eq_ | neq_ ].

    (* CASE [id__c0 = id__c] *)
    + inject_left eq_.
      assert (eq_σ : σ'__c = σ__c) by (eapply MapsTo_add_eqv; eauto).
      assert (eq_comp_Δ : Component Δ'__c = Component Δ__c) by
          (eapply MapsTo_add_eqv; eauto).
      inject_left eq_σ; inject_left eq_comp_Δ.
      eapply elab_well_typed_values_in_sstore; eauto.

    (* CASE [id__c0 ≠ id__c] *)
    + eapply WT; eauto;
        eapply add_3 with (x := id__c) (y := id__c0); eauto.

  (* CASE Null *)
  - eauto.

  (* CASE || *)
  - intros WT; eapply IHebeh2; eauto.
Qed.

Lemma elab_well_typed_values_in_sstore_of_comp :
  forall {D__s M__g d Δ σ__e},
    edesign D__s M__g d Δ σ__e ->
    forall {id__c Δ__c σ__ce},
      MapsTo id__c (Component Δ__c) Δ ->
      MapsTo id__c σ__ce (cstore σ__e) ->
      forall {id t v},
        (MapsTo id (Declared t) Δ__c \/ MapsTo id (Input t) Δ__c \/ MapsTo id (Output t) Δ__c) ->
        MapsTo id v (sstore σ__ce) ->
        IsOfType v t.
Proof.
  inversion 1.
  eapply ebeh_inv_well_typed_values_in_sstore_of_comp; eauto.
  do 3 intro; intros MapsTo_Δ__c.
  exfalso.
  assert (MapsTo_ : MapsTo id__c (Component Δ__c) EmptyElDesign).
  { erewrite <- @egens_inv_Δ_if_not_gen with (Δ' := Δ0); eauto.
    erewrite <- @eports_inv_Δ_if_not_port with (Δ := Δ0) (Δ' := Δ'); eauto.
    erewrite <- @edecls_inv_Δ_if_not_decl with (Δ := Δ') (Δ' := Δ''); eauto.
    destruct 1 as (t, eq_); inversion eq_.
    destruct 1 as (t, [eq_ | eq_]); inversion eq_.
    destruct 1 as (t, (v, eq_)); inversion eq_. }    
  inversion MapsTo_.
Qed.

