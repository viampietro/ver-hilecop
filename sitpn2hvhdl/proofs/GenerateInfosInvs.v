(** * Sitpn Information Generation Functions and State Invariants *)

Require Import common.CoqLib.
Require Import common.GlobalFacts.
Require Import common.StateAndErrorMonad.

Require Import common.ListDep.
Require Import common.ListMonad.
Require Import common.ListPlus.
Require Import common.proofs.ListMonadFacts.
Require Import common.proofs.ListMonadTactics.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import String.

Require Import sitpn.Sitpn.
Require Import sitpn.SitpnFacts.

Require Import sitpn2hvhdl.Sitpn2HVhdl.
Require Import sitpn2hvhdl.proofs.SInvTactics.

(** Tactic to solve state invariant lemmas. *)

(** ** Transition Information Generation and State Invariants *)

Section TInfosInvs.

  Lemma gen_tinfos_inv_γ :
    forall {sitpn s v s'},
      generate_trans_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_tinfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_trans_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_tinfos_inv_lofTs :
    forall {sitpn s v s'},
      generate_trans_infos sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_tinfos_inv_beh :
    forall {sitpn s v s'},
      generate_trans_infos sitpn s = OK v s' ->
      beh s = beh s'.
  Proof. intros; solve_sinv. Qed.
  
End TInfosInvs.

(** ** Place Information Generation and State Invariants *)

Section PInfosInvs.
      
  Lemma gen_pinfos_inv_γ :
    forall {sitpn decpr s v s'},
      generate_place_infos sitpn decpr s = OK v s' ->
      γ s = γ s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_pinfos_inv_lofPs :
    forall {sitpn decpr s v s'},
      generate_place_infos sitpn decpr s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_pinfos_inv_lofTs :
    forall {sitpn decpr s v s'},
      generate_place_infos sitpn decpr s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_pinfos_inv_beh :
    forall {sitpn decpr s v s'},
      generate_place_infos sitpn decpr s = OK v s' ->
      beh s = beh s'.
  Proof. intros; solve_sinv. Qed.
  
End PInfosInvs.

(** ** Generation of Interpretation Information and State Invariants *)

Section InterprInfosInvs.
  
  Lemma gen_cinfos_inv_γ :
    forall {sitpn s v s'},
      generate_cond_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_cinfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_cond_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_cinfos_inv_lofTs :
    forall {sitpn s v s'},
      generate_cond_infos sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_cinfos_inv_beh :
    forall {sitpn s v s'},
      generate_cond_infos sitpn s = OK v s' ->
      beh s = beh s'.
  Proof. intros; solve_sinv. Qed.
  
  Lemma gen_ainfos_inv_γ :
    forall {sitpn s v s'},
      generate_action_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_ainfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_action_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_ainfos_inv_lofTs :
    forall {sitpn s v s'},
      generate_action_infos sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_ainfos_inv_beh :
    forall {sitpn s v s'},
      generate_action_infos sitpn s = OK v s' ->
      beh s = beh s'.
  Proof. intros; solve_sinv. Qed.
  
  Lemma gen_finfos_inv_γ :
    forall {sitpn s v s'},
      generate_fun_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_finfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_fun_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_finfos_inv_lofTs :
    forall {sitpn s v s'},
      generate_fun_infos sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros; solve_sinv. Qed.

  Lemma gen_finfos_inv_beh :
    forall {sitpn s v s'},
      generate_fun_infos sitpn s = OK v s' ->
      beh s = beh s'.
  Proof. intros; solve_sinv. Qed.

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

Lemma gen_sitpn_infos_inv_beh :
  forall {sitpn decpr s v s'},
    generate_sitpn_infos sitpn decpr s = OK v s' ->
    beh s = beh s'.
Proof.
  intros *; intros e; monadInv e.
  do 10 (match goal with
         | [ H: ?F _ ?st0 = OK _ ?st1 |- beh ?st0 = beh ?st2 ] =>
           transitivity (beh st1); [
             (let e := fresh "e" in solveSInv H; intros *; intros e; minv e; auto)
             || (minv H; simpl; auto) |];
           clear H
         end).
  rewrite (check_wd_sitpn_inv_eq_state EQ9),
  (gen_tinfos_inv_beh EQ10), (gen_pinfos_inv_beh EQ11),
  (gen_cinfos_inv_beh EQ12), (gen_ainfos_inv_beh EQ13).
  apply (gen_finfos_inv_beh EQ15).
Qed.

