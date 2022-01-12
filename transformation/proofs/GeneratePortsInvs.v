(** * Port Generation/Connection and State Invariants *)

Require Import String.
Require Import common.CoqLib.
Require Import common.GlobalFacts.
Require Import common.StateAndErrorMonad.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import common.ListLib.

Require Import sitpn.SitpnLib.

Require Import hvhdl.AbstractSyntax.

Require Import transformation.Sitpn2HVhdl.

(** ** Action Port Generation and State Invariants *)

Section GenActionPortsInvs.

  (* Lemma foldl_gen_aport_and_ss_inv_plmap : *)
  (*   forall {sitpn acts ss_pair s v s'}, *)
  (*     ListMonad.fold_left (generate_action_port_and_ss sitpn) acts ss_pair s = OK v s' -> *)
  (*     plmap (arch s) = plmap (arch s'). *)
  (* Proof. *)
  (*   intros *; intros e; solve_listm e. *)
  (*   intros *; intros e; minv e. *)
  (*   shelf_state EQ4; change (arch s1) with (arch s0); solve_listm EQ4. *)
  (* Qed. *)
  
  (* Lemma connect_marked_port_sil_plmap : *)
  (*   forall {sitpn lofexprs p s v s'}, *)
  (*     connect_marked_port sitpn lofexprs p s = OK v s' -> *)
  (*     Sig_in_List (fs (plmap (arch s))) -> *)
  (*     Sig_in_List (fs (plmap (arch s'))). *)
  (* Proof. *)
  (*   intros *; intros e; minv e. *)
  (*   solve_listm EQ1; auto. *)
  (*   solve_listm EQ1; eauto with setoidl. *)
  (*   destruct 1 as (InA_plmap2, NoDupA_plmap2); split. *)
  (*   intros. *)
  (*   eapply InA_fs_InA_fs_setv; eauto. *)
  (*   eapply NoDupA_setv_cons; eauto. *)
  (* Qed. *)
  
  (* Lemma connect_marked_port_inv_plmap : *)
  (*   forall {sitpn lofexprs p1 s v s'}, *)
  (*     connect_marked_port sitpn lofexprs p1 s = OK v s' -> *)
  (*     Sig_in_List (fs (plmap (arch s))) -> *)
  (*     forall {p2 g i o}, *)
  (*       InA Pkeq (p2, (g , i, o)) (plmap (arch s)) -> *)
  (*       exists o', InA Pkeq (p2, (g, i, o')) (plmap (arch s')). *)
  (* Proof. *)
  (*   intros *; intros e SIL; minv e. *)
  (*   solve_listm EQ1; intros; exists o0; assumption. *)
  (*   rewrite <- (getv_inv_state EQ1); intros. *)
  (*   destruct (Peqdec p1 p2) as [ Peq_ | nPeq ]. *)
  (*   (* CASE [Peq p1 p2] *) *)
  (*   assert (InA Pkeq (p1, (g, i, o)) (plmap (arch s0))) *)
  (*     by (eapply getv_correct; eauto). *)
  (*   assert (InA Pkeq (p1, (g0, i0, o0)) (plmap (arch s0))) *)
  (*     by (symmetry in Peq_; eapply InA_eqk; eauto). *)
  (*   assert (e : (g, i, o) = (g0, i0, o0)). *)
  (*   eapply @NoDupA_fs_eqk_eq with (eqk := Peq); eauto with typeclass_instances. *)
  (*   apply SIL. *)
  (*   inject_left e. *)
  (*   exists (setv Nat.eq_dec Place.marked (inl (Some (n_id (nextid s0)))) o0). *)
  (*   eapply InA_setv_eqk; eauto; symmetry; assumption. *)
  (*   (* CASE [~Peq p1 p2] *) *)
  (*   exists o0; eapply InA_setv_inv_1; eauto.     *)
  (* Qed. *)
  
  (* Lemma iter_add_amap_entry_inv_plmap : *)
  (*   forall {sitpn acts s v s'}, *)
  (*     ListMonad.iter (add_action_map_entry sitpn) acts s = OK v s' -> *)
  (*     forall {p g i o}, *)
  (*       Sig_in_List (fs (plmap (arch s))) -> *)
  (*       InA Pkeq (p, (g , i, o)) (plmap (arch s)) -> *)
  (*       Sig_in_List (fs (plmap (arch s'))) /\ exists o', InA Pkeq (p, (g, i, o')) (plmap (arch s')). *)
  (* Proof. *)
  (*   intros *; intros e; solve_listm e. *)
  (*   unfold Transitive; intros. *)
  (*   edestruct H as (SIL, (o1, InA_plmapy)); eauto. *)
  (*   intros *; intros e; minv e; solve_listm EQ2. *)
  (*   unfold connect_marked_ports in EQ1; solve_listm EQ1. *)
  (*   unfold Transitive; intros. *)
  (*   edestruct H as (SIL, (o1, InA_plmapy)); eauto. *)
  (*   split. *)
  (*   eapply connect_marked_port_sil_plmap; eauto. *)
  (*   eapply connect_marked_port_inv_plmap; eauto. *)
  (* Qed. *)
  
  Lemma gen_aports_inv_p2pcomp :
    forall {sitpn s v s'},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      p2pcomp (γ s) = p2pcomp (γ s').
  Proof.
  (*   intros *; intros e; minv e; auto; simpl. *)
  (*   transitivity (p2pcomp (γ s1)). *)
  (*   solve_listm EQ2; intros *; intros e. *)
  (*   minv e; solve_listm EQ3. *)
  (*   unfold connect_marked_ports in EQ2; solve_listm EQ2. *)
  (*   intros *; intros e1; minv e1; solve_listm EQ2. *)
  (*   solve_listm EQ0; intros *; intros e; minv e. *)
  (*   shelf_state EQ5; change (p2pcomp (γ s)) with (p2pcomp (γ s2)); solve_listm EQ5. *)
  (* Qed. *)
  Admitted.
  
  Lemma gen_aports_inv_t2tcomp :
    forall {sitpn s v s'},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      t2tcomp (γ s) = t2tcomp (γ s').
  Proof.
    (*   intros *; intros e; minv e; auto; simpl. *)
    (*   transitivity (t2tcomp (γ s1)). *)
    (*   solve_listm EQ2; intros *; intros e. *)
    (*   minv e; solve_listm EQ3. *)
    (*   unfold connect_marked_ports in EQ2; solve_listm EQ2. *)
    (*   intros *; intros e1; minv e1; solve_listm EQ2. *)
    (*   solve_listm EQ0; intros *; intros e; minv e. *)
    (*   shelf_state EQ5; change (t2tcomp (γ s)) with (t2tcomp (γ s2)); solve_listm EQ5. *)
    (* Qed. *)
  Admitted.

  Require Import SInvTactics.
  
  Lemma gen_aports_inv_lofPs :
    forall {sitpn s v s'},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros; solve_sinv.
         match goal with
         | [ H: _ ?S3 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
             idtac "OK"
         end.
         match goal with
         | [ H: _ ?S3 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
             tryif (check_is_state_record S3) then
               tryif (change (F S1) with (F S3)) then idtac "OK" else fail
             else fail
         end.
         solve_sinv.
  (*   intros *; intros e; minv e; auto; simpl. *)
  (*   transitivity (lofPs s1). *)
  (*   solve_listm EQ2; intros *; intros e. *)
  (*   minv e; solve_listm EQ3. *)
  (*   unfold connect_marked_ports in EQ2; solve_listm EQ2. *)
  (*   intros *; intros e1; minv e1; solve_listm EQ2. *)
  (*   solve_listm EQ0; intros *; intros e; minv e. *)
  (*   shelf_state EQ5; change (lofPs s) with (lofPs s2); solve_listm EQ5. *)
  (* Qed. *)
  Admitted.
  
  Lemma gen_aports_inv_lofTs :
    forall {sitpn s v s'},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof.
    (* intros *; intros e; minv e; auto; simpl. *)
    (* transitivity (lofTs s1). *)
    (* solve_listm EQ2; intros *; intros e. *)
    (* minv e; solve_listm EQ3. *)
    (* unfold connect_marked_ports in EQ2; solve_listm EQ2. *)
    (* intros *; intros e1; minv e1; solve_listm EQ2. *)
    (* solve_listm EQ0; intros *; intros e; minv e. *)
    (* shelf_state EQ5; change (lofTs s) with (lofTs s2); solve_listm EQ5. *)
    (* Qed. *)
  Admitted.
  
  (* Lemma gen_aports_inv_plmap : *)
  (*   forall {sitpn s v s'}, *)
  (*     generate_action_ports_and_ps sitpn s = OK v s' -> *)
  (*     Sig_in_List (fs (plmap (arch s))) -> *)
  (*     forall {p g i o}, *)
  (*       InA Pkeq (p, (g , i, o)) (plmap (arch s)) -> *)
  (*       exists o', InA Pkeq (p, (g, i, o')) (plmap (arch s')). *)
  (* Proof. *)
  (*   intros *; intros e SIL; minv e; eauto. *)
  (*   intros *; intros InA_plmap0. *)
  (*   rewrite <- (foldl_gen_aport_and_ss_inv_plmap EQ0). *)
  (*   edestruct @iter_add_amap_entry_inv_plmap with (sitpn := sitpn) as (o1, InA_plmap1); eauto.     *)
  (* Qed. *)

  (* Lemma gen_aports_inv_sil_plmap : *)
  (*   forall {sitpn s v s'}, *)
  (*     generate_action_ports_and_ps sitpn s = OK v s' -> *)
  (*     Sig_in_List (fs (plmap (arch s))) -> *)
  (*     Sig_in_List (fs (plmap (arch s'))). *)
  (* Proof. *)
  (*   intros *; intros e; minv e; auto; simpl. *)
  (*   rewrite <- (foldl_gen_aport_and_ss_inv_plmap EQ0). *)
  (*   solveSInv EQ2; intros *; intros e; minv e. *)
  (*   solveSInv EQ4; solveSInv EQ3; intros *; intros e; minv e. *)
  (*   solveSInv EQ5; auto. *)
  (*   solveSInv EQ5; auto; eapply SIL_fs_setv. *)
  (* Qed. *)

  Lemma gen_aports_inv_no_comps_in_beh :
    forall {sitpn s v s'},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      ~(exists id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) (beh s)) ->
      ~(exists id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) (beh s')).      
  Proof.
    (* intros *; intros e; minv e; auto; simpl. *)
    (* assert (e : beh s0 = beh s4). *)
    (* { *)
    (*   transitivity (beh s1). *)
    (*   solve_listm EQ2; intros *; intros e. *)
    (*   minv e; solve_listm EQ3. *)
    (*   unfold connect_marked_ports in EQ2; solve_listm EQ2. *)
    (*   intros *; intros e1; minv e1; solve_listm EQ2. *)
    (*   solve_listm EQ0; intros *; intros e; minv e. *)
    (*   shelf_state EQ5; change (beh s) with (beh s2); solve_listm EQ5. *)
    (* } *)
    (* inject_left e. *)
    (* intros nex_InCs; destruct 1 as (id__c, (id__e, (gm, (ipm, (opm, [eq_ | InCs_]))))); *)
    (*   [ inversion eq_ | apply  nex_InCs; exists id__c, id__e, gm, ipm, opm; assumption ]. *)
    (* Qed. *)
  Admitted.
  
End GenActionPortsInvs.

(** ** Function Port Generation and State Invariants *)

Section GenFunPortsInvs.

  Lemma gen_fports_inv_p2pcomp :
    forall {sitpn s v s'},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      p2pcomp (γ s) = p2pcomp (γ s').
  Proof.
  (*   intros *; intros e; minv e; auto. *)
  (*   transitivity (p2pcomp (γ s1)). *)
  (*   solve_listm EQ2; intros *; intros e; minv e; solve_listm EQ3. *)
  (*   unfold connect_fired_ports in EQ2; solve_listm EQ2. *)
  (*   intros *; intros e1; minv e1; solve_listm EQ2. *)
  (*   solve_listm EQ0; intros *; intros e; minv e. *)
  (*   shelf_state EQ5; change (p2pcomp (γ s)) with (p2pcomp (γ s2)); solve_listm EQ5. *)
    (* Qed. *)
  Admitted.

  Lemma gen_fports_inv_t2tcomp :
    forall {sitpn s v s'},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      t2tcomp (γ s) = t2tcomp (γ s').
  Proof.
  (*   intros *; intros e; minv e; auto. *)
  (*   transitivity (t2tcomp (γ s1)). *)
  (*   solve_listm EQ2; intros *; intros e; minv e; solve_listm EQ3. *)
  (*   unfold connect_fired_ports in EQ2; solve_listm EQ2. *)
  (*   intros *; intros e1; minv e1; solve_listm EQ2. *)
  (*   solve_listm EQ0; intros *; intros e; minv e. *)
  (*   shelf_state EQ5; change (t2tcomp (γ s)) with (t2tcomp (γ s2)); solve_listm EQ5. *)
    (* Qed. *)
  Admitted.

  Lemma gen_fports_inv_lofPs :
    forall {sitpn s v s'},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    (* intros *; intros e; minv e; auto. *)
    (* transitivity (lofPs s1). *)
    (* solve_listm EQ2; intros *; intros e; minv e; solve_listm EQ3. *)
    (* unfold connect_fired_ports in EQ2; solve_listm EQ2. *)
    (* intros *; intros e1; minv e1; solve_listm EQ2. *)
    (* solve_listm EQ0; intros *; intros e; minv e. *)
    (* shelf_state EQ5; change (lofPs s) with (lofPs s2); solve_listm EQ5. *)
    (* Qed. *)
  Admitted.

  Lemma gen_fports_inv_lofTs :
    forall {sitpn s v s'},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof.
  (*   intros *; intros e; minv e; auto. *)
  (*   transitivity (lofTs s1). *)
  (*   solve_listm EQ2; intros *; intros e; minv e; solve_listm EQ3. *)
  (*   unfold connect_fired_ports in EQ2; solve_listm EQ2. *)
  (*   intros *; intros e1; minv e1; solve_listm EQ2. *)
  (*   solve_listm EQ0; intros *; intros e; minv e. *)
  (*   shelf_state EQ5; change (lofTs s) with (lofTs s2); solve_listm EQ5. *)
  (* Qed. *)
  Admitted.
    
  (* Lemma gen_fports_inv_plmap : *)
  (*   forall {sitpn s v s'}, *)
  (*     generate_fun_ports_and_ps sitpn s = OK v s' -> *)
  (*     plmap (arch s) = plmap (arch s'). *)
  (* Proof. *)
  (*   intros *; intros e; minv e; auto. *)
  (*   transitivity (plmap (arch s1)). *)
  (*   solve_listm EQ2; intros *; intros e; minv e; solve_listm EQ3. *)
  (*   unfold connect_fired_ports in EQ2; solve_listm EQ2. *)
  (*   intros *; intros e1; minv e1; solve_listm EQ2. *)
  (*   solve_listm EQ0; intros *; intros e; minv e. *)
  (*   shelf_state EQ5; change (plmap (arch s)) with (plmap (arch s2)); solve_listm EQ5. *)
  (* Qed. *)

  Lemma gen_fports_inv_no_comps_in_beh :
    forall {sitpn s v s'},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      ~(exists id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) (beh s)) ->
      ~(exists id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) (beh s')).
  Proof.
    (* intros *; intros e; minv e; auto. *)
    (* assert (e : beh s0 = beh s5). *)
    (* { transitivity (beh s1). *)
    (*   solve_listm EQ2; intros *; intros e; minv e; solve_listm EQ3. *)
    (*   unfold connect_fired_ports in EQ2; solve_listm EQ2. *)
    (*   intros *; intros e1; minv e1; solve_listm EQ2. *)
    (*   solve_listm EQ0; intros *; intros e; minv e. *)
    (*   shelf_state EQ5; change (beh s) with (beh s2); solve_listm EQ5. *)
    (* } *)
    (* inject_left e. *)
    (* intros nex_InCs; destruct 1 as (id__c, (id__e, (gm, (ipm, (opm, [eq_ | InCs_]))))); *)
    (*   [ inversion eq_ | apply  nex_InCs; exists id__c, id__e, gm, ipm, opm; assumption ]. *)
    (* Qed. *)
  Admitted.
  
End GenFunPortsInvs.

(** ** Condition Port Generation and State Invariants *)

Section GenCondPorts.

  Lemma gen_cports_inv_p2pcomp :
    forall {sitpn s v s'},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      p2pcomp (γ s) = p2pcomp (γ s').
  Proof.
    (* intros *; intros e; minv e; *)
    (*   solve_listm EQ0; intros *; intros e; minv e; shelf_state EQ5; *)
    (*     change (p2pcomp (γ s)) with (p2pcomp (γ s1)); *)
    (*     solve_listm EQ5; *)
    (*     unfold connect_in_cond_ports in EQ4; solve_listm EQ4; *)
    (*       intros *; intros e; minv e; solve_listm EQ1. *)
    (* Qed. *)
  Admitted.

  Lemma gen_cports_inv_t2tcomp :
    forall {sitpn s v s'},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      t2tcomp (γ s) = t2tcomp (γ s').
  Proof.
  (*   intros *; intros e; minv e; *)
  (*     solve_listm EQ0; intros *; intros e; minv e; shelf_state EQ5; *)
  (*       change (t2tcomp (γ s)) with (t2tcomp (γ s1)); *)
  (*       solve_listm EQ5; *)
  (*       unfold connect_in_cond_ports in EQ4; solve_listm EQ4; *)
  (*         intros *; intros e; minv e; solve_listm EQ1. *)
  (* Qed. *)
  Admitted.
  
  Lemma gen_cports_inv_lofPs :
    forall {sitpn s v s'},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    (*   intros *; intros e; minv e. *)
    (*   solve_listm EQ0. *)
    (*   intros *; intros e; minv e. *)
    (*   shelf_state EQ5; change (lofPs s) with (lofPs s1). *)
    (*   solve_listm EQ5. *)
    (*   unfold connect_in_cond_ports in EQ4; solve_listm EQ4. *)
    (*   intros *; intros e; minv e; solve_listm EQ1. *)
    (* Qed. *)
  Admitted.

  Lemma gen_cports_inv_lofTs :
    forall {sitpn s v s'},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof.
    (*   intros *; intros e; minv e. *)
    (*   solve_listm EQ0. *)
    (*   intros *; intros e; minv e. *)
    (*   shelf_state EQ5; change (lofTs s) with (lofTs s1). *)
    (*   solve_listm EQ5. *)
    (*   unfold connect_in_cond_ports in EQ4; solve_listm EQ4. *)
    (*   intros *; intros e; minv e; solve_listm EQ1. *)
    (* Qed. *)
  Admitted.
  
  Lemma gen_cports_inv_beh :
    forall {sitpn s v s'},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      beh s = beh s'.
  Proof.
    (* intros *; intros e; minv e. *)
    (* solve_listm EQ0. *)
    (* intros *; intros e; minv e. *)
    (* shelf_state EQ5; change (beh s) with (beh s1). *)
    (* solve_listm EQ5. *)
    (* unfold connect_in_cond_ports in EQ4; solve_listm EQ4. *)
    (* intros *; intros e; minv e; solve_listm EQ1. *)
    (* Qed. *)
  Admitted.

  (* Lemma gen_cports_inv_plmap : *)
  (*   forall {sitpn s v s'}, *)
  (*     generate_and_connect_cond_ports sitpn s = OK v s' -> *)
  (*     plmap (arch s) = plmap (arch s'). *)
  (* Proof. *)
  (*   intros *; intros e; minv e; solve_listm EQ0. *)
  (*   intros *; intros e; minv e. *)
  (*   shelf_state EQ5; change (plmap (arch s)) with (plmap (arch s1)). *)
  (*   solve_listm EQ5. *)
  (*   unfold connect_in_cond_ports in EQ4; solve_listm EQ4. *)
  (*   intros *; intros e; minv e; solve_listm EQ1. *)
  (* Qed. *)
  
End GenCondPorts.

(** ** Facts about Port Generation Function *)

Lemma gen_ports_inv_p2pcomp :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    p2pcomp (γ s) = p2pcomp (γ s').
Proof.
  (* intros *; intros e; monadInv e. *)
  (* rewrite <- (gen_cports_inv_p2pcomp EQ2), *)
  (* <- (gen_fports_inv_p2pcomp EQ1), *)
  (* <- (gen_aports_inv_p2pcomp EQ); *)
  (*   reflexivity. *)
  (* Qed. *)
Admitted.

Lemma gen_ports_inv_t2tcomp :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    t2tcomp (γ s) = t2tcomp (γ s').
Proof.
  (* intros *; intros e; monadInv e. *)
  (* rewrite <- (gen_cports_inv_t2tcomp EQ2), *)
  (* <- (gen_fports_inv_t2tcomp EQ1), *)
  (* <- (gen_aports_inv_t2tcomp EQ); *)
  (*   reflexivity. *)
  (* Qed. *)
Admitted.

Lemma gen_ports_inv_lofPs :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    lofPs s = lofPs s'.
Proof.
  (* intros *; intros e; monadInv e. *)
  (* rewrite <- (gen_cports_inv_lofPs EQ2), *)
  (* <- (gen_fports_inv_lofPs EQ1), *)
  (* <- (gen_aports_inv_lofPs EQ); *)
  (*   reflexivity. *)
  (* Qed. *)
Admitted.

Lemma gen_ports_inv_lofTs :
  forall {sitpn : Sitpn} {s : Sitpn2HVhdlState sitpn} {v : unit}
         {s' : Sitpn2HVhdlState sitpn},
    generate_ports s = OK v s' -> lofTs s = lofTs s'.
Proof.
  (* intros *; intros e; monadInv e. *)
  (* rewrite <- (gen_cports_inv_lofTs EQ2), *)
  (* <- (gen_fports_inv_lofTs EQ1), *)
  (* <- (gen_aports_inv_lofTs EQ); *)
  (*   reflexivity. *)
  (* Qed. *)
Admitted.

(* Lemma gen_ports_inv_plmap : *)
(*   forall {sitpn s v s'}, *)
(*     @generate_ports sitpn s = OK v s' -> *)
(*     Sig_in_List (fs (plmap (arch s))) -> *)
(*     forall {p g i o}, *)
(*       InA Pkeq (p, (g , i, o)) (plmap (arch s)) -> *)
(*       exists o', InA Pkeq (p, (g, i, o')) (plmap (arch s')). *)
(* Proof. *)
(*   intros *; intros e SIL; monadInv e. *)
(*   rewrite <- (gen_cports_inv_plmap EQ2). *)
(*   intros *; intros InA_plmap. *)
(*   edestruct @gen_aports_inv_plmap with (sitpn := sitpn); eauto. *)
(*   rewrite <- (gen_fports_inv_plmap EQ1); eauto. *)
(* Qed. *)

(* Lemma gen_ports_inv_sil_plmap : *)
(*   forall {sitpn s v s'}, *)
(*     @generate_ports sitpn s = OK v s' -> *)
(*     Sig_in_List (fs (plmap (arch s))) -> *)
(*     Sig_in_List (fs (plmap (arch s'))). *)
(* Proof. *)
(*   intros *; intros e; monadInv e. *)
(*   rewrite <- (gen_cports_inv_plmap EQ2), <- (gen_fports_inv_plmap EQ1). *)
(*   eapply gen_aports_inv_sil_plmap; eauto. *)
(* Qed. *)

Lemma gen_ports_inv_no_comps_in_beh :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    ~(exists id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) (beh s)) ->
    ~(exists id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) (beh s')).
Proof.
  (*   intros *; intros e; monadInv e. *)
  (*   intros nex_InCs_comp. *)
  (*   rewrite <- (gen_cports_inv_beh EQ2); eauto. *)
  (*   eapply gen_fports_inv_no_comps_in_beh; eauto. *)
  (*   eapply gen_aports_inv_no_comps_in_beh; eauto. *)
  (* Qed. *)
Admitted.
