(** * Facts about the H-VHDL Generating Functions *)

Require Import String.
Require Import common.Coqlib.
Require Import common.GlobalFacts.
Require Import common.FstSplit.
Require Import common.InAndNoDup.
Require Import common.ListDep.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListMonad.
Require Import common.ListMonadFacts.
Require Import common.ListMonadTactics.
Require Import common.SetoidListFacts.
Require Import common.ListPlus.

Require Import sitpn.dp.Sitpn.
Require Import sitpn.dp.SitpnFacts.
Require Import sitpn.dp.SitpnWellDefined.
Require Import sitpn.dp.SitpnWellDefinedTactics.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Place.

Require Import sitpn2hvhdl.Sitpn2HVhdl.
Require Import sitpn2hvhdl.GenerateInfosFacts.
Require Import sitpn2hvhdl.GenerateArchitectureFacts.
Require Import sitpn2hvhdl.GeneratePortsFacts.

(** ** Facts about [InputMap_to_AST] Function *)

Section InputMap2AST.

  Lemma imap_entry_to_associp_inv_state :
    forall {sitpn im ime s v s'},
      imap_entry_to_associp sitpn im ime s = OK v s' ->
      s = s'.
  Proof.
    unfold imap_entry_to_associp.
    destruct ime; destruct s; intros s v s' e1; monadFullInv e1;
      [ auto | destruct l; monadFullInv EQ; auto ].
  Qed.

  Lemma InputMap_to_AST_inv_state :
    forall {sitpn imap s ipm s'},
      InputMap_to_AST sitpn imap s = OK ipm s' ->
      s = s'.
  Proof.
    unfold InputMap_to_AST; intros.
    eapply foldl_inv_state; eauto with typeclass_instances;
      intros; eapply imap_entry_to_associp_inv_state; eauto.
  Qed.

  Lemma foldl_imap_entry_to_associp_In_inl :
    forall {sitpn imap s ipm1 ipm2 s' id e},
      fold_left (imap_entry_to_associp sitpn) imap ipm1 s = OK ipm2 s' ->
      List.In (id, inl e) imap ->
      List.In (associp_ id e) ipm2.
  Proof.
    induction imap.
    (* CASE imap = [] *)
    inversion 2.
    (* CASE imap = a :: tl *)
    cbn; intros *; intros EQ; inversion_clear 1 as [eq_a | In_imap]; minv EQ.
    (* SUBCASE [a = (id, inl e)] *)
    inject_left eq_a.
    eapply foldl_build_list_by_app; eauto.
    intros *; intros EQ; minv EQ; eexists; eauto.
    inversion eq_a.
    (* SUBCASE [(id, inl e) ∈ imap] *)
    all : eapply IHimap; eauto.
  Qed.
  
  Lemma InputMap_to_AST_In_inl :
    forall imap sitpn s ipm s' id e,
      InputMap_to_AST sitpn imap s = OK ipm s' ->
      List.In (id, inl e) imap ->
      List.In (associp_ id e) ipm.
  Proof.
    unfold InputMap_to_AST; intros.
    eapply foldl_imap_entry_to_associp_In_inl; eauto.
  Qed.
  
End InputMap2AST.

(** ** Facts about [OutputMap_to_AST] Function *)

Section OutputMap2AST.

  Lemma omap_entry_to_assocop_inv_state :
    forall {sitpn om ome s v s'},
      omap_entry_to_assocop sitpn om ome s = OK v s' ->
      s = s'.
  Proof.
    unfold omap_entry_to_assocop.
    destruct ome; destruct s; intros s v s' e1; monadFullInv e1;
      [ auto | destruct l; monadFullInv EQ; auto ].
  Qed.

  Lemma OutputMap_to_AST_inv_state :
    forall {sitpn omap s opm s'},
      OutputMap_to_AST sitpn omap s = OK opm s' ->
      s = s'.
  Proof.
    unfold OutputMap_to_AST; intros.
    eapply foldl_inv_state; eauto with typeclass_instances;
      intros; eapply omap_entry_to_assocop_inv_state; eauto.
  Qed.
  
End OutputMap2AST.

(** ** Facts about [HComponent_to_comp_inst] Function *)

Section HComp2CompInst.

  Lemma HComp_to_comp_inst_inv_state :
    forall {sitpn id__c id__e hcomp s v s'},
      HComponent_to_comp_inst sitpn id__c id__e hcomp s = OK v s' ->
      s = s'.
  Proof.
    intros until s'; intros e; destruct hcomp as ((gm, ipm), opm).
    monadFullInv e; transitivity s0.
    eapply InputMap_to_AST_inv_state; eauto.
    eapply OutputMap_to_AST_inv_state; eauto.
  Qed.

  Lemma HComp_to_comp_inst_p_comp :
    forall {sitpn id__c id__e hcomp s v s'},
      HComponent_to_comp_inst sitpn id__c id__e hcomp s = OK v s' ->
      exists gm ipm opm,
        v = cs_comp id__c id__e gm ipm opm.
  Proof.
    intros until s'; intros e; destruct hcomp as ((gm, ipm), opm).
    monadFullInv e.
    exists gm, x, x0; reflexivity.
  Qed.
  
End HComp2CompInst.

(** ** Facts about Generation of P Component Instances *)

Section GeneratePlaceCompInst.

  (** *** P Component Generation *)
  
  Lemma gen_pcomp_inst_inv_p_comp_1 :
    forall {sitpn x y s v s' id__p gm ipm opm},
      generate_place_comp_inst sitpn y s = OK v s' ->
      ~Peq x y ->
      InA Pkeq (x, id__p) (p2pcomp (γ s)) ->
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s) ->
      InA Pkeq (x, id__p) (p2pcomp (γ s')) /\
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until opm; intros e; intros; split;
      monadFullInv e; simpl; simpl in EQ4;
        specialize (getv_inv_state EQ4) as e1;
        specialize (HComp_to_comp_inst_inv_state EQ2) as e2;
        rewrite <- e2, <- e1; clear e1 e2; simpl;
          [ apply InA_setv_inv_1; auto | right; assumption ].
  Qed.

  Lemma gen_pcomp_inst_inv_p_comp_2 :
    forall {sitpn x y s v s' id__p gm ipm opm},
      generate_place_comp_inst sitpn y s = OK v s' ->
      ~Peq x y ->
      InA Pkeq (x, id__p) (p2pcomp (γ s')) ->
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s') ->
      ~(exists p1 id__p1, InA Pkeq (p1, id__p1) (p2pcomp (γ s)) /\ id__p1 >= nextid s) ->
      InA Pkeq (x, id__p) (p2pcomp (γ s)) /\
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s).
  Proof.
    intros until opm; intros e nPeq InA_p2pcomp InCs_beh; minv e; shelf_state EQ5.
    (* Stores the first subgoal (need it in the second subgoal). *)
    assert (InA_p2pcomp0 : InA Pkeq (x, id__p) (p2pcomp (γ s0))).
    { eapply @InA_setv_inv_2 with (eqk_dec := Peqdec) (v := nextid s0); eauto.
      change (setv Peqdec y (nextid s0) (p2pcomp (γ s0))) with (p2pcomp (γ s)).
      assert (e : p2pcomp (γ s4) = (p2pcomp (γ s))).
      { rewrite (getv_inv_state EQ5), (InputMap_to_AST_inv_state EQ3),
        (OutputMap_to_AST_inv_state EQ2); reflexivity. }
      rewrite <- e; auto. }
    intros nex_InA; split; auto.
    (* SUBGOAL [comp(id__p, "place", ...) ∈ (beh s0)] *)
    destruct InCs_beh as [eq_comp | InCs_beh4].
    (* CASE comp. are equal. *)
    inject_left eq_comp; exfalso; apply nex_InA; exists x, (nextid s0); auto.
    (* CASE [comp ∈ beh s0] *)
    assert (e : beh s = beh s4).
    { rewrite (getv_inv_state EQ5), (InputMap_to_AST_inv_state EQ3),
      (OutputMap_to_AST_inv_state EQ2); reflexivity. }
    change (beh s0) with (beh s); rewrite e; auto.
  Qed.
  
  Lemma gen_p_comp_inst_p_comp :
    forall {sitpn p s v s'},
      generate_place_comp_inst sitpn p s = OK v s' ->
      exists (id__p : ident) (gm : genmap) (ipm : inputmap) (opm : outputmap),
        InA Pkeq (p, id__p) (p2pcomp (γ s')) /\ InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until s'; intros e; monadFullInv e.
    simpl; simpl in EQ4.
    specialize (HComp_to_comp_inst_p_comp EQ2) as (gm, (ipm, (opm, e1))); rewrite e1.
    exists (nextid s0), gm, ipm, opm; simpl.
    specialize (getv_inv_state EQ4) as e2; subst s2.
    specialize (HComp_to_comp_inst_inv_state EQ2) as e2; subst s4.
    split; [ apply InA_setv; auto | auto].
  Qed.
  
  Lemma iter_gen_p_comp_inst_p_comp :
    forall {sitpn pls} {s v s'},
      iter (generate_place_comp_inst sitpn) pls s = OK v s' ->
      NoDupA Peq pls ->
      forall p, InA Peq p pls ->
        exists id__p gm ipm opm,
          InA Pkeq (p, id__p) (p2pcomp (γ s')) /\
          InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until pls; functional induction (iter (generate_place_comp_inst sitpn) pls) using iter_ind.

    (* BASE CASE *)
    - inversion 3.

    (* IND. CASE *)
    - intros;
        lazymatch goal with
        | [ Hm : (do _ <- _; _) _ = _, Hin: InA _ _ (_ :: _) |- _ ] =>
          inversion_clear Hin as [ e1 e2 Peq_pb | e1 e2 HIn_ntl ]; monadInv Hm
        end.

      (* CASE a = n *)
      + specialize (gen_p_comp_inst_p_comp EQ0) as (id__p, (gm, (ipm, (opm, (Hin_γs', Hin_behs'))))).
        exists id__p, gm, ipm, opm; split; [ | auto].
        eapply InA_eqk; eauto; symmetry; assumption.        

      (* CASE n ∈ tl *)
      + lazymatch goal with
        | [ H: NoDupA _ _ |- _ ] => inversion_clear H as [ | e1 e2 Hnotin_a_tl Hnodup_tl ]
        end.
        specialize (IHm s x s0 EQ Hnodup_tl p HIn_ntl) as (id__p, (gm, (ipm, (opm, (Hγ, Hincs_comp))))).

        (* Apply gen_pcomp_inst_inv_p_comp_1 *)
        assert (nPeq : ~Peq p b) by (eapply InA_neqA; eauto).
        specialize (gen_pcomp_inst_inv_p_comp_1 EQ0 nPeq Hγ Hincs_comp) as (Hγ', Hincs_comp').
        exists id__p, gm, ipm, opm; auto.
  Qed.
  
  Lemma gen_p_comp_insts_p_comp :
    forall {sitpn s v s'},
      generate_place_comp_insts sitpn s = OK v s' ->
      Sig_in_List (lofPs s) ->
      forall p, exists id__p gm ipm opm,
          InA Pkeq (p, id__p) (p2pcomp (γ s')) /\
          InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until s'; intros e; minv e; intros SIL p.
    eapply iter_gen_p_comp_inst_p_comp; eauto;
      [ apply (proj2 SIL) | apply ((proj1 SIL) p)].
  Qed.

  (** *** NoDup in p2pcomp *)
  
  Lemma gen_p_comp_inst_nodup_p2pcomp :
    forall {sitpn p s v s'},
      generate_place_comp_inst sitpn p s = OK v s' ->
      ~InA Peq p (fs (p2pcomp (γ s))) ->
      NoDupA Peq (fs (p2pcomp (γ s))) ->
      NoDupA Peq (fs (p2pcomp (γ s'))).
  Proof.
    intros until s'; intros e; monadFullInv e;
      simpl; simpl in EQ4;
        specialize (getv_inv_state EQ4) as e1;
        specialize (HComp_to_comp_inst_inv_state EQ2) as e2;
        rewrite <- e2, <- e1; clear e1 e2; simpl.
    apply NoDupA_setv_cons; auto.
  Qed.

  Lemma gen_p_comp_inst_inv_p2pcomp :
    forall {sitpn x y s v s'},
      generate_place_comp_inst sitpn y s = OK v s' ->
      ~Peq y x ->
      ~InA Peq x (fs (p2pcomp (γ s))) ->
      ~InA Peq x (fs (p2pcomp (γ s'))).
  Proof.
    intros until s'; intros e; intros;
      monadFullInv e; simpl; simpl in EQ4;
        specialize (getv_inv_state EQ4) as e1;
        specialize (HComp_to_comp_inst_inv_state EQ2) as e2;
        rewrite <- e2, <- e1; clear e1 e2; simpl; auto with setoidl.
  Qed.

  Lemma iter_gen_pcomp_inst_inv_nodup_p2pcomp :
    forall {sitpn pls} {s v s'},
      iter (generate_place_comp_inst sitpn) pls s = OK v s' ->
      forall p,
        ~InA Peq p (fs (p2pcomp (γ s))) ->
        ~InA Peq p pls ->
        ~InA Peq p (fs (p2pcomp (γ s'))).
  Proof.
    intros until pls;
      functional induction (iter (generate_place_comp_inst sitpn) pls) using iter_ind;
      intros s v s' e; monadInv e; auto; intros.
    eapply gen_p_comp_inst_inv_p2pcomp; eauto with setoidl.
    intro; apply H0; symmetry in H1; auto.
  Qed.

  Lemma iter_gen_pcomp_inst_nodup_p2pcomp :
    forall {sitpn pls s v s'},
      iter (generate_place_comp_inst sitpn) pls s = OK v s' ->
      NoDupA Peq pls ->
      (forall p, InA Peq p pls -> ~InA Peq p (fs (p2pcomp (γ s)))) ->
      NoDupA Peq (fs (p2pcomp (γ s))) ->
      NoDupA Peq (fs (p2pcomp (γ s'))).
  Proof.
    intros until pls;
      functional induction (iter (generate_place_comp_inst sitpn) pls) using iter_ind;
      intros s v s' e; monadInv e; auto; intros.
    
    eapply gen_p_comp_inst_nodup_p2pcomp; eauto;
      lazymatch goal with
      | [ Hnd: NoDupA _ (?a :: ?tl), Hnin: forall _, _ -> ~_ |- _ ] =>
        (eapply iter_gen_pcomp_inst_inv_nodup_p2pcomp; eauto; [
           apply Hnin; apply InA_cons_hd; reflexivity
         | inversion Hnd; assumption])
        || (eapply IHm; eauto; inversion Hnd; assumption)
      end.
  Qed.

  (** *** Bind initial marking *)

  Lemma gen_p_comp_inst_inv_nextid_2 :
    forall {sitpn p s v s'},
      generate_place_comp_inst sitpn p s = OK v s' ->
      ~(exists p id__p, InA Pkeq (p, id__p) (p2pcomp (γ s)) /\ id__p >= nextid s) ->
      ~(exists p id__p, InA Pkeq (p, id__p) (p2pcomp (γ s')) /\ id__p >= nextid s').
  Proof.
    intros until s'; intros e; minv e; shelf_state EQ5.
    intros nex_InA; destruct 1 as (p1, (id__p1, (InA_p2pcomp0, GE_nxtid0))).
    assert (s = s2) by (eapply getv_inv_state; eauto); subst.
    assert (s = s3) by (eapply InputMap_to_AST_inv_state; eauto); subst.
    assert (s = s4) by (eapply OutputMap_to_AST_inv_state; eauto); subst.
    change (p2pcomp (γ s))
      with (setv Peqdec p (nextid s0) (p2pcomp (γ s0))) in InA_p2pcomp0.
    edestruct @InA_setv_fst_or_in_tl as [(Peq_, e) | InA_beh0]; eauto.
    (* CASE [Peq p1 p] and [id__p1 = nextid s0] *)
    subst; change (nextid s) with (S (nextid s0)) in GE_nxtid0; lia.
    (* CASE [InA Pkeq (p1, id__p1) (p2pcomp (γ s0))] *)
    apply nex_InA; exists p1, id__p1; split;
      [ assumption | change (nextid s) with (S (nextid s0)) in GE_nxtid0; lia ].
  Qed.

  Lemma iter_gen_pcomp_inst_inv_nextid_2 :
    forall {sitpn pls} {s v s'},
      iter (generate_place_comp_inst sitpn) pls s = OK v s' ->
      ~(exists p id__p, InA Pkeq (p, id__p) (p2pcomp (γ s)) /\ id__p >= nextid s) ->
      ~(exists p id__p, InA Pkeq (p, id__p) (p2pcomp (γ s')) /\ id__p >= nextid s').
  Proof.
    intros until s'; intros e; solve_listm e.
    intros; eapply gen_p_comp_inst_inv_nextid_2; eauto.
  Qed.
  
  Lemma gen_p_comp_inst_inv_nextid_1 :
    forall {sitpn p s v s'},
      generate_place_comp_inst sitpn p s = OK v s' ->
      ~(exists id__c id__e g i o, InCs (cs_comp id__c id__e g i o) (beh s) /\ id__c >= nextid s) ->
      ~(exists id__c id__e g i o, InCs (cs_comp id__c id__e g i o) (beh s') /\ id__c >= nextid s').
  Proof.
    intros until s'; intros e; minv e; shelf_state EQ5.
    intros nex_InCs; destruct 1 as (id__c, (id__e, (g1, (i1, (o1, (InCs_or, GE_nxtid)))))).
    destruct InCs_or as [eq_comp | InCs_beh ].
    (* CASE comp. are equal *)
    inject_left eq_comp.
    assert (s = s2) by (eapply getv_inv_state; eauto); subst.
    assert (s = s3) by (eapply InputMap_to_AST_inv_state; eauto); subst.
    assert (s = s4) by (eapply OutputMap_to_AST_inv_state; eauto); subst.
    change (nextid s) with (S (nextid s0)) in GE_nxtid; lia.
    (* CASE [comp(id__c, id__e, g1, i1, o1) ∈ (beh s4)] *)
    apply nex_InCs; exists id__c, id__e, g1, i1, o1.
    assert (s = s2) by (eapply getv_inv_state; eauto); subst.
    assert (s = s3) by (eapply InputMap_to_AST_inv_state; eauto); subst.
    assert (s = s4) by (eapply OutputMap_to_AST_inv_state; eauto); subst.
    split; auto; cbn in GE_nxtid; lia.
  Qed.
    
  Lemma iter_gen_pcomp_inst_inv_nextid_1 :
    forall {sitpn pls} {s v s'},
      iter (generate_place_comp_inst sitpn) pls s = OK v s' ->
      ~(exists id__c id__e g i o, InCs (cs_comp id__c id__e g i o) (beh s) /\ id__c >= nextid s) ->
      ~(exists id__c id__e g i o, InCs (cs_comp id__c id__e g i o) (beh s') /\ id__c >= nextid s').
  Proof.
    intros until s'; intros e; solve_listm e.
    intros; eapply gen_p_comp_inst_inv_nextid_1; eauto.
  Qed.
  
  Lemma gen_pcomp_inst_bind_init_marking :
    forall {sitpn p s v s' g i o},
      generate_place_comp_inst sitpn p s = OK v s' ->
      forall (id__p : ident) (gm : genmap) (ipm : inputmap) (opm : outputmap),
        InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s') ->
        InA Pkeq (p, id__p) (p2pcomp (γ s')) ->
        ~(exists id__e gm ipm opm, InCs (cs_comp (nextid s) id__e gm ipm opm) (beh s)) ->
        InA Pkeq (p, (g, i, o)) (plmap (arch s)) ->
        List.In (initial_marking, inl (e_nat (M0 p))) i ->
        NoDupA Peq (fs (plmap (arch s))) ->
        NoDupA Peq (fs (p2pcomp (γ s))) ->
        List.In (associp_ initial_marking (M0 p)) ipm.
  Proof.
    intros until o; intros e; minv e; shelf_state EQ5.
    inversion_clear 1 as [eq_comp | InCs_beh].
    (* CASE comp are equal *)
    inject_left eq_comp.
    do 3 intro; intros InA_plmap; intros.
    eapply InputMap_to_AST_In_inl; eauto.
    assert (s = s2) by (eapply getv_inv_state; eauto); subst.
    change (plmap (arch s0)) with (plmap (arch s)) in InA_plmap.
    erewrite getv_compl in EQ5; eauto.
    inject_left EQ5; auto.
    (* CASE [comp(id__p, "place", gm, ipm, opm) ∈ (beh s)], 
       contradiction. *)
    assert (s = s2) by (eapply getv_inv_state; eauto); subst.
    assert (s = s3) by (eapply InputMap_to_AST_inv_state; eauto); subst.
    assert (s = s4) by (eapply OutputMap_to_AST_inv_state; eauto); subst.
    change (p2pcomp (γ s)) with (setv Peqdec p (nextid s0) (p2pcomp (γ s0))).
    intros InA_setv nex_InCs; intros;
      erewrite @eqv_if_InA_NoDupA_setv with (y := id__p) (eqk := Peq) in InCs_beh;
      eauto with typeclass_instances.
    exfalso; apply nex_InCs; exists Petri.place_entid, gm, ipm, opm; auto.
  Qed.

  Lemma iter_gen_pcomp_inst_inv_arch :
    forall {sitpn pls} {s v s'},
      iter (generate_place_comp_inst sitpn) pls s = OK v s' ->
      arch s = arch s'.
  Proof. intros *; intros e; solve_listm e.
         intros *; intros e; minv e.
         shelf_state EQ5; change (arch s0) with (arch s1).
         rewrite (getv_inv_state EQ5),
         (InputMap_to_AST_inv_state EQ3),
         (OutputMap_to_AST_inv_state EQ2).
         reflexivity.
  Qed.
  
  Lemma iter_gen_pcomp_inst_bind_init_marking :
    forall {sitpn pls} {s v s'},
      iter (generate_place_comp_inst sitpn) pls s = OK v s' ->
      forall p id__p gm ipm opm g i o,
        IsWellDefined sitpn ->
        NoDupA Peq pls ->
        InA Peq p pls ->
        InA Pkeq (p, id__p) (p2pcomp (γ s')) ->
        InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s') ->
        NoDupA Peq (fs (plmap (arch s))) ->
        ~(exists p1 id__p1, InA Pkeq (p1, id__p1) (p2pcomp (γ s)) /\ id__p1 >= nextid s) ->
        ~(exists id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) (beh s) /\ id__c >= nextid s) ->
        InA Pkeq (p, (g, i, o)) (plmap (arch s)) ->
        List.In (initial_marking, inl (e_nat (M0 p))) i ->
        NoDupA Peq (fs (p2pcomp (γ s))) ->
        (forall p, InA Peq p pls -> ~InA Peq p (fs (p2pcomp (γ s)))) ->
        List.In (associp_ ($initial_marking) (@M0 sitpn p)) ipm.
  Proof.
    intros until pls;
      functional induction (iter (generate_place_comp_inst sitpn) pls) using iter_ind;
      try (solve [inversion 4]).
    intros s v s' e; monadInv e; intros *; intros IWD_sitpn NoDupA_pls.
    inversion_clear 1.

    (* CASE [Peq p b] *)
    erewrite (wi_M0 (wi_funs IWD_sitpn)); eauto.
    intros; eapply @gen_pcomp_inst_bind_init_marking
              with (p := b) (g := g) (o := o);
      eauto with setoidl.
    (* SUBCASE [∄ comp((nextid s0),...) ∈ (beh s0)] *)
    destruct 1 as (id__e, (g0, (i0, (o0, InCs_behs0)))).
    eapply iter_gen_pcomp_inst_inv_nextid_1; eauto.
    exists (nextid s0), id__e, g0, i0, o0; auto.
    (* SUBCASE [(b, (g, i, o)) ∈ (plmap (arch s0))] *)
    erewrite <- iter_gen_pcomp_inst_inv_arch; eauto with setoidl.
    (* SUBCASE [NoDupA Peq (fs (plmap (arch s0)))] *)
    erewrite <- iter_gen_pcomp_inst_inv_arch; eauto with setoidl.
    (* SUBCASE [NoDupA Peq (fs (p2pcomp (γ s0)))] *)
    eapply iter_gen_pcomp_inst_nodup_p2pcomp; eauto with setoidl.
    
    (* CASE [p ∈ tl] *)
    intros; eapply IHm with (s' := s0) (id__p := id__p) (gm := gm) (opm := opm);
      eauto with setoidl; inversion NoDupA_pls; subst.
    all : eapply gen_pcomp_inst_inv_p_comp_2; eauto with setoidl;
      eapply iter_gen_pcomp_inst_inv_nextid_2; eauto.
  Qed.

  Lemma gen_pcomp_insts_bind_init_marking :
    forall {sitpn s v s'},
      generate_place_comp_insts sitpn s = OK v s' ->
      IsWellDefined sitpn ->
      Sig_in_List (lofPs s) ->
      NoDupA Peq (fs (plmap (arch s))) ->
      NoDupA Peq (fs (p2pcomp (γ s))) ->
      (forall p, InA Peq p (lofPs s) -> ~ InA Peq p (fs (p2pcomp (γ s)))) ->
      ~(exists p id__p, InA Pkeq (p, id__p) (p2pcomp (γ s)) /\ id__p >= nextid s) ->
      ~(exists id__c id__e gm ipm opm,
           InCs (cs_comp id__c id__e gm ipm opm) (beh s) /\ id__c >= nextid s) ->
      forall p id__p gm ipm opm g i o,
        InA Pkeq (p, id__p) (p2pcomp (γ s')) ->
        InA Pkeq (p, (g, i, o)) (plmap (arch s)) ->
        List.In (initial_marking, inl (e_nat (M0 p))) i ->
        InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s') ->
        List.In (associp_ ($initial_marking) (@M0 sitpn p)) ipm.
  Proof.
    intros until s'; intros e; minv e.
    intros IWD_sitpn SIL_lofPs; intros.
    eapply iter_gen_pcomp_inst_bind_init_marking; eauto;
      destruct SIL_lofPs; auto.
  Qed.
  
End GeneratePlaceCompInst.

(** ** Facts about Generation of T Component Instances *)

Section GenerateTransCompInst.

  Lemma gen_t_comp_inst_inv_p2pcomp :
    forall {sitpn t s v s'},
      generate_trans_comp_inst sitpn t s = OK v s' ->
      p2pcomp (γ s) = p2pcomp (γ s').
  Proof.
    intros until s'; intros e; monadFullInv e; simpl; simpl in EQ3.
    specialize (getv_inv_state EQ3) as e1;
      specialize (HComp_to_comp_inst_inv_state EQ0) as e2;
      rewrite <- e2, <- e1; clear e1 e2; simpl; reflexivity.
  Qed.
  
  Lemma iter_gen_tcomp_inst_inv_p2pcomp :
    forall {sitpn trs s v s'},
      iter (generate_trans_comp_inst sitpn) trs s = OK v s' ->
      p2pcomp (γ s) = p2pcomp (γ s').
  Proof.
    intros until s'; intros e; solveSInv e.
    intros; eapply gen_t_comp_inst_inv_p2pcomp; eauto.
  Qed.
  
  Lemma gen_t_comp_inst_inv_in_beh :
    forall {sitpn t s v s'},
      generate_trans_comp_inst sitpn t s = OK v s' ->
      forall cstmt,
        InCs cstmt (beh s) -> InCs cstmt (beh s').
  Proof.
    intros until s'; intros e; monadFullInv e; simpl; simpl in EQ3.
    specialize (getv_inv_state EQ3) as e1;
      specialize (HComp_to_comp_inst_inv_state EQ0) as e2;
      rewrite <- e2, <- e1; clear e1 e2; simpl.
    intros; right; assumption.
  Qed.

  Lemma iter_gen_tcomp_inst_inv_in_beh :
    forall {sitpn trs s v s'},
      iter (generate_trans_comp_inst sitpn) trs s = OK v s' ->
      forall cstmt, InCs cstmt (beh s) -> InCs cstmt (beh s').
  Proof.
    intros until s'; intros e; solveSInv e.
    intros; eapply gen_t_comp_inst_inv_in_beh; eauto.
  Qed.
  
  Lemma gen_tcomp_insts_inv_p_comp :
    forall {sitpn s v s' p id__p gm ipm opm},
      generate_trans_comp_insts sitpn s = OK v s' ->
      InA Pkeq (p, id__p) (p2pcomp (γ s)) ->
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s) ->
      InA Pkeq (p, id__p) (p2pcomp (γ s')) /\
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until opm; intros e; monadFullInv e.
    split;
      [rewrite <- (iter_gen_tcomp_inst_inv_p2pcomp EQ0); assumption |
       eapply iter_gen_tcomp_inst_inv_in_beh; eauto].
  Qed.

  Lemma gen_tcomp_insts_inv_p2pcomp :
    forall {sitpn s v s'},
      generate_trans_comp_insts sitpn s = OK v s' ->
      p2pcomp (γ s) = p2pcomp (γ s').
  Proof.
    intros *; intros e; minv e.
    eapply iter_gen_tcomp_inst_inv_p2pcomp; eauto.
  Qed.

  Lemma gen_tcomp_insts_gen_only_tcomp :
    forall {sitpn s v s'},
      generate_trans_comp_insts sitpn s = OK v s' ->
      forall {id__c id__e gm ipm opm},
        id__e <> Petri.transition_entid ->
        InCs (cs_comp id__c id__e gm ipm opm) (beh s') ->
        InCs (cs_comp id__c id__e gm ipm opm) (beh s).
  Admitted.
  
End GenerateTransCompInst.

(** ** Facts about SITPN-to-H-VHDL Transformation Function *)

Section Sitpn2HVhdl.
  
  Lemma gen_comp_insts_p_comp :
    forall {sitpn s v s'},
      generate_comp_insts sitpn s = OK v s' ->
      Sig_in_List (lofPs s) ->
      forall p, exists id__p gm ipm opm,
          InA Pkeq (p, id__p) (p2pcomp (γ s')) /\
          InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until s'; intros e; monadInv e; intros Hsil p.
    specialize (gen_p_comp_insts_p_comp EQ Hsil p)
      as (id__p, (gm, (ipm, (opm, (Hin_γs0, Hin_behs0))))).
    exists id__p, gm, ipm, opm.
    eapply gen_tcomp_insts_inv_p_comp; eauto.
  Qed.
  
  Lemma sitpn2hvhdl_p_comp :
    forall {sitpn decpr id__ent id__arch mm d γ},
      (* [sitpn] translates into [(d, γ)]. *)
      sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
      IsWellDefined sitpn ->
      forall p, exists id__p gm ipm opm,
          (* [γ(p) = id__p] *)
          InA Pkeq (p, id__p) (p2pcomp γ)
          /\ InCs (cs_comp id__p Petri.place_entid gm ipm opm) (behavior d).
  Proof.
    intros. 
    functional induction (sitpn_to_hvhdl sitpn decpr id__ent id__arch mm) using sitpn_to_hvhdl_ind.
    
    (* Error *)
    lazymatch goal with
    | [ H: inr _ = inl _ |- _ ] => inversion H
    end.

    (* OK *)
    monadInv e.
    minv EQ4; inversion H; clear H; subst; simpl.
    eapply gen_comp_insts_p_comp; eauto.
    rewrite <- (gen_ports_inv_lofPs EQ0),
    <- (gen_arch_inv_lofPs EQ1).
    lazymatch goal with
    | [ Hwd: IsWellDefined _ |- _ ] =>
      apply (gen_sitpn_infos_sil_lofPs EQ (nodup_pls (wi_fsets Hwd)))
    end.
  Qed.

  Lemma gen_comp_insts_nodup_p2pcomp :
    forall {sitpn : Sitpn} {s : Sitpn2HVhdlState sitpn} {v : unit} {s' : Sitpn2HVhdlState sitpn},
      generate_comp_insts sitpn s = OK v s' ->
      Sig_in_List (lofPs s) ->
      (forall p, ~InA Peq p (fs (p2pcomp (γ s)))) ->
      NoDupA Peq (fs (p2pcomp (γ s))) ->
      NoDupA Peq (fs (p2pcomp (γ s'))).
  Proof.
    intros until s'; intros e; monadInv e; intros.
    minv EQ0; rewrite <- (iter_gen_tcomp_inst_inv_p2pcomp EQ2).
    minv EQ; eapply iter_gen_pcomp_inst_nodup_p2pcomp; eauto.
    apply (proj2 H).
  Qed.

  Lemma sitpn2hvhdl_nodup_p2pcomp :
    forall {sitpn decpr id__ent id__arch mm d γ},    
      (* [sitpn] translates into [(d, γ)]. *)
      sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
      IsWellDefined sitpn ->
      NoDupA Peq (fs (p2pcomp γ)).
  Proof.
    intros until mm;  
      functional induction (sitpn_to_hvhdl sitpn decpr id__ent id__arch mm) using sitpn_to_hvhdl_ind.
    
    (* Error *)
    inversion 1.

    (* OK *)
    intros; monadInv e.
    minv EQ4; inversion H; clear H; subst; simpl.
    eapply gen_comp_insts_nodup_p2pcomp; eauto.
    2, 3: rewrite <- (gen_ports_inv_p2pcomp EQ0);
      rewrite <- (gen_arch_inv_γ EQ1);
      rewrite <- (gen_sitpn_infos_inv_γ EQ);
      simpl; (inversion 1 || apply NoDupA_nil).
    rewrite <- (gen_ports_inv_lofPs EQ0),
    <- (gen_arch_inv_lofPs EQ1).
    lazymatch goal with
    | [ Hwd: IsWellDefined _ |- _ ] =>
      apply (gen_sitpn_infos_sil_lofPs EQ (nodup_pls (wi_fsets Hwd)))
    end.
  Qed.
  
  Lemma gen_comp_insts_bind_init_marking :
    forall {sitpn s v s'},
      generate_comp_insts sitpn s = OK v s' ->
      IsWellDefined sitpn ->
      Sig_in_List (lofPs s) ->
      NoDupA Peq (fs (plmap (arch s))) ->
      NoDupA Peq (fs (p2pcomp (γ s))) ->
      (forall p, InA Peq p (lofPs s) -> ~ InA Peq p (fs (p2pcomp (γ s)))) ->
      ~(exists p id__p, InA Pkeq (p, id__p) (p2pcomp (γ s)) /\ id__p >= nextid s) ->
      ~(exists id__c id__e gm ipm opm,
           InCs (cs_comp id__c id__e gm ipm opm) (beh s) /\ id__c >= nextid s) ->
      forall p id__p gm ipm opm g i o,
        InA Pkeq (p, id__p) (p2pcomp (γ s')) ->
        InA Pkeq (p, (g, i, o)) (plmap (arch s)) ->
        List.In (initial_marking, inl (e_nat (M0 p))) i ->
        InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s') ->
        List.In (associp_ ($initial_marking) (@M0 sitpn p)) ipm.
  Proof.
    intros *; intros e; monadInv e; intros.
    eapply gen_pcomp_insts_bind_init_marking; eauto.    
    erewrite gen_tcomp_insts_inv_p2pcomp; eauto.
    eapply gen_tcomp_insts_gen_only_tcomp; eauto.
    discriminate.
  Qed.

  Lemma sitpn2hvhdl_bind_init_marking :
    forall {sitpn decpr id__ent id__arch mm d γ},
      (* [sitpn] translates into [(d, γ)]. *)
      sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
      IsWellDefined sitpn ->
      forall p id__p gm ipm opm,
        InA Pkeq (p, id__p) (p2pcomp γ) ->
        InCs (cs_comp id__p Petri.place_entid gm ipm opm) (behavior d) ->
        List.In (associp_ ($initial_marking) (@M0 sitpn p)) ipm.
  Proof.
    intros until mm;  
      functional induction (sitpn_to_hvhdl sitpn decpr id__ent id__arch mm) using sitpn_to_hvhdl_ind.
    
    (* Error *)
    inversion 1.

    (* OK *)
    do 3 intro; intros IWD_sitpn; intros; monadInv e.
    minv EQ4; inversion H; clear H; subst; simpl.

    (* Builds [InA Peq (p, (g, i, o)) (plmap (arch s0))] *)
    edestruct @gen_arch_pcomp with (p := p) as (g, (i, (o, InA_plmap))); eauto.
    eapply gen_sitpn_infos_sil_lofPs; eauto.
    exact (nodup_pls (wi_fsets IWD_sitpn)).
    
    (* Apply gen_comp_insts_bind_init_marking, solve the generated
       subgoals. *)
    eapply gen_comp_insts_bind_init_marking; eauto.

    (* SUBGOAL Sig_in_List (lofPs s1) *)
    erewrite <- gen_ports_inv_lofPs; eauto.
    erewrite <- gen_arch_inv_lofPs; eauto.
    eapply gen_sitpn_infos_sil_lofPs; eauto.
    exact (nodup_pls (wi_fsets IWD_sitpn)).

    (* SUBGOAL [NoDupA Peq (fs (plmap (arch s1)))] *)
    erewrite <- gen_ports_inv_arch; eauto.
    eapply gen_arch_nodup_plmap; eauto.
    eapply gen_sitpn_infos_sil_lofPs; eauto.
    exact (nodup_pls (wi_fsets IWD_sitpn)).
    erewrite <- gen_sitpn_infos_inv_arch; eauto; cbn; inversion 1.
    erewrite <- gen_sitpn_infos_inv_arch; eauto; cbn; auto.

    (* SUBGOAL [NoDupA Peq (fs (p2pcomp (γ s1)))] *)
    1, 2: erewrite <- gen_ports_inv_p2pcomp; eauto;
      erewrite <- gen_arch_inv_γ; eauto;
        erewrite <- gen_sitpn_infos_inv_γ; eauto;
           (cbn; eapply NoDupA_nil || inversion 2).

    (* SUBGOAL [∄ (p, id__p) ∈ (p2pcomp (γ s)) s.t. id__p > nextid s1] *)
    erewrite <- gen_ports_inv_p2pcomp; eauto.
    erewrite <- gen_arch_inv_γ; eauto.
    erewrite <- gen_sitpn_infos_inv_γ; eauto.
    simpl; destruct 1 as (p1, (id__p1, (InA_, _))); inversion InA_.
    
    (* SUBGOAL [∄ comp(id__c, id__e, gm, ipm, opm) ∈ (beh s1) /\ id__c >= nextid s1] *)
    destruct 1 as (id__c, (id__e, (gm0, (ipm0, (opm0, (InCs_beh, GE_id__c)))))).
    eapply gen_ports_inv_no_comps_in_beh; eauto.
    erewrite <- gen_arch_inv_beh; eauto.
    erewrite <- gen_sitpn_infos_inv_beh; eauto; cbn.
    destruct 1 as (id__c1, (id__e1, (gm1, (ipm1, (opm1, e))))); inversion e.
    exists id__c, id__e, gm0, ipm0, opm0; auto.
    
    (* SUBGOAL [(p, (g, i, o)) ∈ (plmap (arch s1))] *)
    erewrite <- gen_ports_inv_arch; eauto.

    (* SUBGOAL [(initial_marking, inl (M0 p)) ∈ i] *)
    eapply gen_arch_bind_init_marking; eauto.
  Qed.
  
End Sitpn2HVhdl.
