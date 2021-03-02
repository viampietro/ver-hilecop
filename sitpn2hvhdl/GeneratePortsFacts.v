(** * Facts about Port Generation and Connection *)

Require Import String.
Require Import common.Coqlib.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListMonadFacts.
Require Import common.ListMonadTactics.
Require Import common.ListPlus.
Require Import common.SetoidListFacts.

Require Import sitpn.dp.SitpnLib.

Require Import hvhdl.AbstractSyntax.

Require Import sitpn2hvhdl.Sitpn2HVhdl.
Require Import sitpn2hvhdl.GenerateArchitectureFacts.

(** ** Facts about Action Port Generation *)

Section GenActionPorts.
  
  Lemma gen_aports_inv_p2pcomp :
    forall {sitpn s v s'},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      p2pcomp (γ s) = p2pcomp (γ s').
  Proof.
    intros *; intros e; minv e; auto; simpl.
    transitivity (p2pcomp (γ s1)).
    solve_listm EQ2; intros *; intros e.
    minv e; solve_listm EQ3.
    unfold connect_marked_ports in EQ2; solve_listm EQ2.
    intros *; intros e1; minv e1; solve_listm EQ2.
    solve_listm EQ0; intros *; intros e; minv e.
    shelf_state EQ5; change (p2pcomp (γ s)) with (p2pcomp (γ s2)); solve_listm EQ5.
  Qed.

  Lemma gen_aports_inv_lofPs :
    forall {sitpn s v s'},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros *; intros e; minv e; auto; simpl.
    transitivity (lofPs s1).
    solve_listm EQ2; intros *; intros e.
    minv e; solve_listm EQ3.
    unfold connect_marked_ports in EQ2; solve_listm EQ2.
    intros *; intros e1; minv e1; solve_listm EQ2.
    solve_listm EQ0; intros *; intros e; minv e.
    shelf_state EQ5; change (lofPs s) with (lofPs s2); solve_listm EQ5.
  Qed.

  Lemma foldl_gen_aport_and_ss_inv_plmap :
    forall {sitpn acts ss_pair s v s'},
      ListMonad.fold_left (generate_action_port_and_ss sitpn) acts ss_pair s = OK v s' ->
      plmap (arch s) = plmap (arch s').
  Proof.
    intros *; intros e; solve_listm e.
    intros *; intros e; minv e.
    shelf_state EQ4; change (arch s1) with (arch s0); solve_listm EQ4.
  Qed.
  
  Lemma connect_marked_port_sil_plmap :
    forall {sitpn lofexprs p s v s'},
      connect_marked_port sitpn lofexprs p s = OK v s' ->
      Sig_in_List (fs (plmap (arch s))) ->
      Sig_in_List (fs (plmap (arch s'))).
  Proof.
    intros *; intros e; minv e.
    solve_listm EQ1; auto.
    solve_listm EQ1; eauto with setoidl.
    destruct 1 as (InA_plmap2, NoDupA_plmap2); split.
    intros.
    eapply InA_fs_InA_fs_setv; eauto.
    eapply NoDupA_setv_cons; eauto.
  Qed.
  
  Lemma connect_marked_port_inv_plmap :
    forall {sitpn lofexprs p1 s v s'},
      connect_marked_port sitpn lofexprs p1 s = OK v s' ->
      Sig_in_List (fs (plmap (arch s))) ->
      forall {p2 g i o},
        InA Pkeq (p2, (g , i, o)) (plmap (arch s)) ->
        exists o', InA Pkeq (p2, (g, i, o')) (plmap (arch s')).
  Proof.
    intros *; intros e SIL; minv e.
    solve_listm EQ1; intros; exists o0; assumption.
    rewrite <- (getv_inv_state EQ1); intros.
    destruct (Peqdec p1 p2) as [ Peq_ | nPeq ].
    (* CASE [Peq p1 p2] *)
    assert (InA Pkeq (p1, (g, i, o)) (plmap (arch s0)))
      by (eapply getv_correct; eauto).
    assert (InA Pkeq (p1, (g0, i0, o0)) (plmap (arch s0)))
      by (symmetry in Peq_; eapply InA_eqk; eauto).
    assert (e : (g, i, o) = (g0, i0, o0)).
    eapply @NoDupA_fs_eqk_eq with (eqk := Peq); eauto with typeclass_instances.
    apply SIL.
    inject_left e.
    exists (setv Nat.eq_dec Place.marked (inl (Some (n_id (nextid s0)))) o0).
    eapply InA_setv_eqk; eauto; symmetry; assumption.
    (* CASE [~Peq p1 p2] *)
    exists o0; eapply InA_setv_inv_1; eauto.
    intros Peq_; symmetry in Peq_; contradiction.
  Qed.
  
  Lemma iter_add_amap_entry_inv_plmap :
    forall {sitpn acts s v s'},
      ListMonad.iter (add_action_map_entry sitpn) acts s = OK v s' ->
      forall {p g i o},
        Sig_in_List (fs (plmap (arch s))) ->
        InA Pkeq (p, (g , i, o)) (plmap (arch s)) ->
        Sig_in_List (fs (plmap (arch s'))) /\ exists o', InA Pkeq (p, (g, i, o')) (plmap (arch s')).
  Proof.
    intros *; intros e; solve_listm e.
    unfold Transitive; intros.
    edestruct H as (SIL, (o1, InA_plmapy)); eauto.
    intros *; intros e; minv e; solve_listm EQ2.
    unfold connect_marked_ports in EQ1; solve_listm EQ1.
    unfold Transitive; intros.
    edestruct H as (SIL, (o1, InA_plmapy)); eauto.
    split.
    eapply connect_marked_port_sil_plmap; eauto.
    eapply connect_marked_port_inv_plmap; eauto.
  Qed.
  
  Lemma gen_aports_inv_plmap :
    forall {sitpn s v s'},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      Sig_in_List (fs (plmap (arch s))) ->
      forall {p g i o},
        InA Pkeq (p, (g , i, o)) (plmap (arch s)) ->
        exists o', InA Pkeq (p, (g, i, o')) (plmap (arch s')).
  Proof.
    intros *; intros e SIL; minv e; eauto.
    intros *; intros InA_plmap0.
    rewrite <- (foldl_gen_aport_and_ss_inv_plmap EQ0).
    edestruct @iter_add_amap_entry_inv_plmap with (sitpn := sitpn) as (o1, InA_plmap1); eauto.    
  Qed.
  
End GenActionPorts.

(** ** Facts about Function Port Generation *)

Section GenFunPorts.

  Lemma gen_fports_inv_p2pcomp :
    forall {sitpn s v s'},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      p2pcomp (γ s) = p2pcomp (γ s').
  Proof.
    intros *; intros e; minv e; auto.
    transitivity (p2pcomp (γ s1)).
    solve_listm EQ2; intros *; intros e; minv e; solve_listm EQ3.
    unfold connect_fired_ports in EQ2; solve_listm EQ2.
    intros *; intros e1; minv e1; solve_listm EQ2.
    solve_listm EQ0; intros *; intros e; minv e.
    shelf_state EQ5; change (p2pcomp (γ s)) with (p2pcomp (γ s2)); solve_listm EQ5.
  Qed.

  Lemma gen_fports_inv_lofPs :
    forall {sitpn s v s'},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros *; intros e; minv e; auto.
    transitivity (lofPs s1).
    solve_listm EQ2; intros *; intros e; minv e; solve_listm EQ3.
    unfold connect_fired_ports in EQ2; solve_listm EQ2.
    intros *; intros e1; minv e1; solve_listm EQ2.
    solve_listm EQ0; intros *; intros e; minv e.
    shelf_state EQ5; change (lofPs s) with (lofPs s2); solve_listm EQ5.
  Qed.
  
  Lemma gen_fports_inv_plmap :
    forall {sitpn s v s'},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      plmap (arch s) = plmap (arch s').
  Proof.
    intros *; intros e; minv e; auto.
    transitivity (plmap (arch s1)).
    solve_listm EQ2; intros *; intros e; minv e; solve_listm EQ3.
    unfold connect_fired_ports in EQ2; solve_listm EQ2.
    intros *; intros e1; minv e1; solve_listm EQ2.
    solve_listm EQ0; intros *; intros e; minv e.
    shelf_state EQ5; change (plmap (arch s)) with (plmap (arch s2)); solve_listm EQ5.
  Qed.
  
End GenFunPorts.

(** ** Facts about Condition Port Generation *)

Section GenCondPorts.

  Lemma gen_cports_inv_p2pcomp :
    forall {sitpn s v s'},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      p2pcomp (γ s) = p2pcomp (γ s').
  Proof.
    intros *; intros e; minv e.
    solve_listm EQ0.
    intros *; intros e; minv e.
    shelf_state EQ5; change (p2pcomp (γ s)) with (p2pcomp (γ s1)).
    solve_listm EQ5.
    unfold connect_in_cond_ports in EQ4; solve_listm EQ4.
    intros *; intros e; minv e; solve_listm EQ1.
  Qed.

  Lemma gen_cports_inv_lofPs :
    forall {sitpn s v s'},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros *; intros e; minv e.
    solve_listm EQ0.
    intros *; intros e; minv e.
    shelf_state EQ5; change (lofPs s) with (lofPs s1).
    solve_listm EQ5.
    unfold connect_in_cond_ports in EQ4; solve_listm EQ4.
    intros *; intros e; minv e; solve_listm EQ1.
  Qed.

  Lemma gen_cports_inv_plmap :
    forall {sitpn s v s'},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      plmap (arch s) = plmap (arch s').
  Proof.
    intros *; intros e; minv e; solve_listm EQ0.
    intros *; intros e; minv e.
    shelf_state EQ5; change (plmap (arch s)) with (plmap (arch s1)).
    solve_listm EQ5.
    unfold connect_in_cond_ports in EQ4; solve_listm EQ4.
    intros *; intros e; minv e; solve_listm EQ1.
  Qed.
  
End GenCondPorts.

(** ** Facts about Port Generation Function *)

Lemma gen_ports_inv_p2pcomp :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    p2pcomp (γ s) = p2pcomp (γ s').
Proof.
  intros *; intros e; monadInv e.
  rewrite <- (gen_cports_inv_p2pcomp EQ2),
  <- (gen_fports_inv_p2pcomp EQ1),
  <- (gen_aports_inv_p2pcomp EQ);
    reflexivity.
Qed.

Lemma gen_ports_inv_lofPs :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    lofPs s = lofPs s'.
Proof.
  intros *; intros e; monadInv e.
  rewrite <- (gen_cports_inv_lofPs EQ2),
  <- (gen_fports_inv_lofPs EQ1),
  <- (gen_aports_inv_lofPs EQ);
    reflexivity.
Qed.

Lemma gen_ports_inv_plmap :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    Sig_in_List (fs (plmap (arch s))) ->
    forall {p g i o},
      InA Pkeq (p, (g , i, o)) (plmap (arch s)) ->
      exists o', InA Pkeq (p, (g, i, o')) (plmap (arch s')).
Proof.
  intros *; intros e SIL; monadInv e.
  rewrite <- (gen_cports_inv_plmap EQ2).
  intros *; intros InA_plmap.
  edestruct @gen_aports_inv_plmap with (sitpn := sitpn); eauto.
  rewrite <- (gen_fports_inv_plmap EQ1); eauto.
Qed.

Lemma gen_ports_sil_plmap :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    Sig_in_List (fs (plmap (arch s))) ->
    Sig_in_List (fs (plmap (arch s'))).
Proof.
Admitted.

Lemma gen_ports_inv_no_comps_in_beh :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    ~(exists id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) (beh s)) ->
    ~(exists id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) (beh s')).
Admitted.
