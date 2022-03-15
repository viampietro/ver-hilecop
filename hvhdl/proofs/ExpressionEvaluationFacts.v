(** * Facts about Expression Evaluation *)

Require Import common.CoqLib.
Require Import common.NatMap.

Require Import hvhdl.Environment.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.HVhdlTypes.

Require Import hvhdl.proofs.EnvironmentFacts.

Lemma vexpr_eq_iff_eq_sigs :
  forall {Δ1 σ1 Δ2 σ2 flag e v},
    EqGens Δ1 Δ2 /\ EqSigs Δ1 Δ2 ->
    EqSStore σ1 σ2 ->
    VExpr Δ1 σ1 EmptyLEnv flag e v <->
    VExpr Δ2 σ2 EmptyLEnv flag e v.
Proof.
  intros *; intros (EqGens_, EqSigs_) EqSStore_.
  split; intro.
  (* CASE A -> B *)
  apply (VExpr_ind_mut
           Δ1 σ1 EmptyLEnv
           (fun b e v H => VExpr Δ2 σ2 EmptyLEnv b e v)
           (fun b a arrofv H => VAgOfExprs Δ2 σ2 EmptyLEnv b a arrofv));
    intros; eauto with hvhdl.
  (* CASE VExprSig *)
  econstructor; eauto.
  inversion o; [ left; rewrite <- EqSigs_; eauto | right; rewrite <- EqSigs_; eauto].
  pattern σ2; rewrite <- EqSStore_; auto.
  (* CASE VExprOut *)
  eapply VExprOut with (t := t0); eauto.
  rewrite <- EqSigs_; auto.
  pattern σ2; rewrite <- EqSStore_; auto.
  (* CASE VExprVar *)
  rewrite empty_mapsto_iff in m; contradiction.
  (* CASE VExprGen *)
  eapply VExprGen with (t := t0); eauto.
  rewrite <- EqGens_; auto.
  (* CASE VExprIdxOut *)
  eapply VExprIdxOut with (t := t0); eauto.
  rewrite <- EqSigs_; auto.
  pattern σ2; rewrite <- EqSStore_; auto.
  (* CASE VExprIdxSig *)
  eapply VExprIdxSig with (t := t0); eauto.
  inversion o; [ left; rewrite <- EqSigs_; auto | right; rewrite <- EqSigs_; auto].
  pattern σ2; rewrite <- EqSStore_; auto.
  (* CASE VExprVar *)
  rewrite empty_mapsto_iff in m; contradiction.
  (* CASE B -> A *)
  apply (VExpr_ind_mut
           Δ2 σ2 EmptyLEnv
           (fun b e v H => VExpr Δ1 σ1 EmptyLEnv b e v)
           (fun b a arrofv H => VAgOfExprs Δ1 σ1 EmptyLEnv b a arrofv));
    intros; eauto with hvhdl.
  (* CASE VExprSig *)
  econstructor; eauto.
  inversion o; [ left; rewrite EqSigs_; eauto | right; rewrite EqSigs_; eauto].
  pattern σ1; rewrite EqSStore_; auto.
  (* CASE VExprOut *)
  eapply VExprOut with (t := t0); eauto.
  rewrite EqSigs_; auto.
  pattern σ1; rewrite EqSStore_; auto.
  (* CASE VExprVar *)
  rewrite empty_mapsto_iff in m; contradiction.
  (* CASE VExprGen *)
  eapply VExprGen with (t := t0); eauto.
  rewrite EqGens_; auto.
  (* CASE VExprIdxOut *)
  eapply VExprIdxOut with (t := t0); eauto.
  rewrite EqSigs_; auto.
  pattern σ1; rewrite EqSStore_; auto.
  (* CASE VExprIdxSig *)
  eapply VExprIdxSig with (t := t0); eauto.
  inversion o; [ left; rewrite EqSigs_; auto | right; rewrite EqSigs_; auto].
  pattern σ1; rewrite EqSStore_; auto.
  (* CASE VExprVar *)
  rewrite empty_mapsto_iff in m; contradiction.
Qed.
