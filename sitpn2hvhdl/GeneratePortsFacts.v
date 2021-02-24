(** * Facts about Port Generation and Connection *)

Require Import String.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListMonadTactics.

Require Import hvhdl.AbstractSyntax.

Require Import sitpn2hvhdl.Sitpn2HVhdl.

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

Lemma gen_ports_inv_arch :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    arch s = arch s'.
Admitted.

Lemma gen_ports_inv_no_comps_in_beh :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    ~(exists id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) (beh s)) ->
    ~(exists id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) (beh s')).
Admitted.
