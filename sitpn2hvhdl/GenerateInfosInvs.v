(** * Sitpn Information Generation Functions and State Invariants *)

Require Import common.Coqlib.
Require Import common.GlobalFacts.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListDep.
Require Import common.ListMonad.
Require Import common.ListMonadFacts.
Require Import common.ListMonadTactics.
Require Import common.ListPlus.

Require Import sitpn.dp.Sitpn.
Require Import sitpn.dp.SitpnFacts.

Require Import sitpn2hvhdl.Sitpn2HVhdl.

(** ** Transition Information Generation and State Invariants *)

Section TInfosInvs.

  Lemma gen_tinfos_inv_γ :
    forall {sitpn s v s'},
      generate_trans_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof.
    intros until s'; intros e; solveSInv e. 
    intros until s2; intros e1; pattern s1, s2; minv e1; simpl; reflexivity.
  Qed.

  Lemma gen_tinfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_trans_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros until s'; intros e; solveSInv e. 
    intros until s2; intros e1; pattern s1, s2; minv e1; simpl; reflexivity.
  Qed.
    
End TInfosInvs.

(** ** Place Information Generation and State Invariants *)

Section PInfosInvs.

  Lemma all_conflicts_solved_by_mutex_inv_state :
    forall {sitpn lofTs s v s'},
      all_conflicts_solved_by_mutex sitpn lofTs s = OK v s' ->
      s = s'.
  Proof.
    induction lofTs; simpl; intros until s'; intros e; minv e; auto; transitivity s0.
    - solve_listm EQ1;
        intros *; intros e; unfold not_exists_mutex in e; minv e;
          repeat (match goal with
                  | [e: _ ?st = OK _ _ |- ?st = _ ] => solve_listm e
                  end).
    - minv EQ0; auto.
    - solve_listm EQ1;
        intros *; intros e; unfold not_exists_mutex in e; minv e;
          repeat (match goal with
                  | [e: _ ?st = OK _ _ |- ?st = _ ] => solve_listm e
                  end).
    - eapply IHlofTs; eauto.
  Qed.

  Lemma sort_by_priority_inv_state :
    forall {sitpn decpr lofTs s v s'},
      sort_by_priority sitpn decpr lofTs s = OK v s' ->
      s = s'.
  Proof.
    intros until s'; intros e; unfold sort_by_priority in e.
    eapply foldl_inv_state; eauto with typeclass_instances.
    intros until s0; cbv beta.
    functional induction (inject_t sitpn decpr a b) using inject_t_ind;
      intros until s0'; intros f; minv f; auto.
    eapply IHc; eauto. 
  Qed.

  Lemma gen_pinfos_inv_γ :
    forall {sitpn decpr s v s'},
      generate_place_infos sitpn decpr s = OK v s' ->
      γ s = γ s'.
  Proof.
    intros until s'; intros e; solveSInv e.
    intros until s2; intros e1; pattern s1, s2; monadInv e1; simpl.
    transitivity (γ s).
    minv EQ; auto.
    minv EQ1; ((rewrite (all_conflicts_solved_by_mutex_inv_state EQ2); simpl; reflexivity)
               || (rewrite (all_conflicts_solved_by_mutex_inv_state EQ2), (sort_by_priority_inv_state EQ1); simpl; reflexivity)).
  Qed.

  Lemma gen_pinfos_inv_lofPs :
    forall {sitpn decpr s v s'},
      generate_place_infos sitpn decpr s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros until s'; intros e; solveSInv e.
    intros until s2; intros e1; pattern s1, s2; monadInv e1; simpl.
    transitivity (lofPs s).
    minv EQ; auto.
    minv EQ1; ((rewrite (all_conflicts_solved_by_mutex_inv_state EQ2); simpl; reflexivity)
               || (rewrite (all_conflicts_solved_by_mutex_inv_state EQ2), (sort_by_priority_inv_state EQ1); simpl; reflexivity)).
  Qed.
  
End PInfosInvs.

(** ** Generation of Interpretation Information and State Invariants *)

Section InterprInfosInvs.

  Lemma gen_cinfos_inv_γ :
    forall {sitpn s v s'},
      generate_cond_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof.
    intros until s'; intros e; pattern s, s'; solveSInv e.
    intros until s2; intros e1; pattern s1, s2; minv e1; simpl; reflexivity.
  Qed.

  Lemma gen_cinfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_cond_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros until s'; intros e; pattern s, s'; solveSInv e.
    intros until s2; intros e1; pattern s1, s2; minv e1; simpl; reflexivity.
  Qed.
  
  Lemma gen_ainfos_inv_γ :
    forall {sitpn s v s'},
      generate_action_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof.
    intros until s'; intros e; pattern s, s'; solveSInv e.
    intros until s2; intros e1; pattern s1, s2; minv e1; simpl; reflexivity.
  Qed.

  Lemma gen_ainfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_action_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros until s'; intros e; pattern s, s'; solveSInv e.
    intros until s2; intros e1; pattern s1, s2; minv e1; simpl; reflexivity.
  Qed.
  
  Lemma gen_finfos_inv_γ :
    forall {sitpn s v s'},
      generate_fun_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof.
    intros until s'; intros e; pattern s, s'; solveSInv e.
    intros until s2; intros e1; pattern s1, s2; minv e1; simpl; reflexivity.
  Qed.

  Lemma gen_finfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_fun_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros until s'; intros e; pattern s, s'; solveSInv e.
    intros until s2; intros e1; pattern s1, s2; minv e1; simpl; reflexivity.
  Qed.

End InterprInfosInvs.

(** ** Checking of Sitpn Well-definition and State Invariants *)

Section CheckWDSitpnInvs.

  Lemma check_wd_sitpn_inv_eq_state :
    forall {sitpn decpr s v s'},
      check_wd_sitpn sitpn decpr s = OK v s' ->
      s = s'.
  Proof.  
    intros until s'; intros e; solveSInv e; auto.
    intros until s3; intros e1; minv e1; auto.
    intros until s3; intros e1; solveSInv e1; auto.
    intros until s5; intros e2; solveSInv e2; auto.
    intros until s7; intros e3; solveSInv e3; auto.
  Qed.
  
End CheckWDSitpnInvs.

(** ** Sitpn Information Generation Function and State Invariants *)

Lemma gen_sitpn_infos_inv_γ :
  forall {sitpn decpr s v s'},
    generate_sitpn_infos sitpn decpr s = OK v s' ->
    γ s = γ s'.
Proof.
  intros until s'; intros e; monadInv e.
  do 10 (match goal with
        | [ H: ?F _ ?st0 = OK _ ?st1 |- γ ?st0 = γ ?st2 ] =>
          transitivity (γ st1); [
            (let e := fresh "e" in solveSInv H; intros *; intros e; minv e; auto)
            || (minv H; simpl; auto) |];
          clear H
        end).
  rewrite (check_wd_sitpn_inv_eq_state EQ9), (gen_tinfos_inv_γ EQ10), (gen_pinfos_inv_γ EQ11),
  (gen_cinfos_inv_γ EQ12), (gen_ainfos_inv_γ EQ13).
  apply (gen_finfos_inv_γ EQ15).
Qed.

Lemma gen_sitpn_infos_inv_arch :
  forall {sitpn decpr s v s'},
    generate_sitpn_infos sitpn decpr s = OK v s' ->
    arch s = arch s'.
Admitted.

Lemma gen_sitpn_infos_inv_beh :
  forall {sitpn decpr s v s'},
    generate_sitpn_infos sitpn decpr s = OK v s' ->
    beh s = beh s'.
Admitted.

