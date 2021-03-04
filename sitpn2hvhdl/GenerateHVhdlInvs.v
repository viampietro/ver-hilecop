(** * H-VHDL Generation Functions and State Invariants *)

Require Import String.
Require Import common.Coqlib.
Require Import common.GlobalFacts.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListLib.

Require Import sitpn.dp.SitpnLib.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Place.

Require Import sitpn2hvhdl.Sitpn2HVhdl.
Require Import sitpn2hvhdl.GenerateInfosFacts.
Require Import sitpn2hvhdl.GenerateArchitectureFacts.
Require Import sitpn2hvhdl.GeneratePortsFacts.

(** ** [InputMap_to_AST] Function and State Invariants *)

Section InputMap2ASTInvs.

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
  
End InputMap2ASTInvs.

(** ** [OutputMap_to_AST] Function and State Invariants *)

Section OutputMap2ASTInvs.

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
  
End OutputMap2ASTInvs.

(** ** [HComponent_to_comp_inst] Function and State Invariants *)

Section HComp2CompInstInvs.

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
  
End HComp2CompInstInvs.

(** ** Generation of P Component Instances and State Invariants *)

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
    do 1 intro; apply NoDupA_setv_cons; auto.
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
        rewrite <- e2, <- e1; clear e1 e2; simpl;
          eapply InA_notin_fs_setv_inv; eauto.
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
      intros s v s' e; monadInv e; auto; intros *; intros nInA_p2pcomp nInA_pls.
    eapply gen_p_comp_inst_inv_p2pcomp; eauto.
    intros Peq_; apply nInA_pls; symmetry in Peq_; auto.
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
        (eapply iter_gen_pcomp_inst_inv_nodup_p2pcomp; eauto; inversion Hnd; assumption)
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
    
End GeneratePlaceCompInst.

(** ** Generation of T Component Instances and State Invariants *)

Section GenerateTransCompInstInvs.

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

  Lemma gen_tcomp_inst_gen_only_tcomp :
    forall {sitpn t s v s'},
      generate_trans_comp_inst sitpn t s = OK v s' ->
      forall {id__c id__e gm ipm opm},
        id__e <> Petri.transition_entid ->
        InCs (cs_comp id__c id__e gm ipm opm) (beh s') ->
        InCs (cs_comp id__c id__e gm ipm opm) (beh s).
  Proof.
    intros *; intros e; minv e; shelf_state EQ4.
    inversion_clear 2 as [eq_comp | InCs_beh5 ];
      [ inject_left eq_comp; contradiction | ].
    change (beh s0) with (beh s).
    rewrite (getv_inv_state EQ4),
    (InputMap_to_AST_inv_state EQ2),
    (OutputMap_to_AST_inv_state EQ0); auto.
  Qed.
  
  Lemma gen_tcomp_insts_gen_only_tcomp :
    forall {sitpn s v s'},
      generate_trans_comp_insts sitpn s = OK v s' ->
      forall {id__c id__e gm ipm opm},
        id__e <> Petri.transition_entid ->
        InCs (cs_comp id__c id__e gm ipm opm) (beh s') ->
        InCs (cs_comp id__c id__e gm ipm opm) (beh s).
  Proof.
    intros *; intros e; minv e.
    pattern s0, s'; solve_listm EQ0.
    intros *; eapply gen_tcomp_inst_gen_only_tcomp; eauto.
  Qed.
  
End GenerateTransCompInstInvs.

(** ** P and T Component Instances Generation Function and State Invariants *)

Section GenCompInstsInvs.
    
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
    
End GenCompInstsInvs.
