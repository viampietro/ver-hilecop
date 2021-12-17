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

Require Import transformation.Sitpn2HVhdl.
Require Import transformation.proofs.SInvTactics.

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
  Proof. intros; solve_sinv. Defined.
  
End CheckWDSitpnInvs.

(** ** Sitpn Information Generation Function and State Invariants *)

Lemma gen_sitpn_infos_inv_γ :
  forall {sitpn decpr s v s'},
    generate_sitpn_infos sitpn decpr s = OK v s' ->
    γ s = γ s'.
Proof. intros; solve_sinv. Qed.

Lemma gen_sitpn_infos_inv_beh :
  forall {sitpn decpr s v s'},
    generate_sitpn_infos sitpn decpr s = OK v s' ->
    beh s = beh s'.
Proof. intros; solve_sinv. Qed.

