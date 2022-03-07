(** * Facts about Sitpn Information Generation Functions *)

Require Import common.CoqLib.
Require Import common.GlobalFacts.
Require Import common.StateAndErrorMonad.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import common.ListDep.
Require Import common.ListMonad.
Require Import common.proofs.ListMonadFacts.
Require Import common.proofs.ListMonadTactics.
Require Import common.proofs.SetoidListFacts.
Require Import common.ListPlus.

Require Import sitpn.Sitpn.
Require Import sitpn.SitpnFacts.

Require Import transformation.Sitpn2HVhdl.
Require Import transformation.proofs.SInvTactics.

(** ** Facts about Transition Information Generation *)

Section TInfos.

  Lemma gen_tinfos_inv_γ :
    forall {sitpn s v s'},
      generate_trans_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_tinfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_trans_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_tinfos_inv_lofTs :
    forall {sitpn s v s'},
      generate_trans_infos sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_tinfos_inv_beh :
    forall {sitpn s v s'},
      generate_trans_infos sitpn s = OK v s' ->
      beh s = beh s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.
  
End TInfos.

(** ** Facts about Place Information Generation *)

Section PInfos.

  Lemma gen_pinfos_inv_γ :
    forall {sitpn s v s'},
      generate_place_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_pinfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_place_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_pinfos_inv_lofTs :
    forall {sitpn s v s'},
      generate_place_infos sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_pinfos_inv_beh :
    forall {sitpn s v s'},
      generate_place_infos sitpn s = OK v s' ->
      beh s = beh s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

End PInfos.

(** ** Facts about Generation of Interpretation Information *)

Section InterprInfos.

  Lemma gen_cinfos_inv_γ :
    forall {sitpn s v s'},
      generate_cond_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_cinfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_cond_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_cinfos_inv_lofTs :
    forall {sitpn s v s'},
      generate_cond_infos sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_cinfos_inv_beh :
    forall {sitpn s v s'},
      generate_cond_infos sitpn s = OK v s' ->
      beh s = beh s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.
  
  Lemma gen_ainfos_inv_γ :
    forall {sitpn s v s'},
      generate_action_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_ainfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_action_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_ainfos_inv_lofTs :
    forall {sitpn s v s'},
      generate_action_infos sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_ainfos_inv_beh :
    forall {sitpn s v s'},
      generate_action_infos sitpn s = OK v s' ->
      beh s = beh s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.
  
  Lemma gen_finfos_inv_γ :
    forall {sitpn s v s'},
      generate_fun_infos sitpn s = OK v s' ->
      γ s = γ s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_finfos_inv_lofPs :
    forall {sitpn s v s'},
      generate_fun_infos sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_finfos_inv_lofTs :
    forall {sitpn s v s'},
      generate_fun_infos sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_finfos_inv_beh :
    forall {sitpn s v s'},
      generate_fun_infos sitpn s = OK v s' ->
      beh s = beh s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.
  
End InterprInfos.

(** ** Facts about Checking of Sitpn Well-definition *)

Section CheckWDSitpn.

  Lemma check_wd_sitpn_inv_eq_state :
    forall {sitpn s v s'},
      check_wd_sitpn sitpn s = OK v s' ->
      s = s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Defined.
  
End CheckWDSitpn.

(** ** Facts about Dependently-typed Lists Generation *)

Lemma tmap_aux_sil :
  forall {A state : Type} {Q : A -> Prop}
         {lofAs : list A}
         {lofSigs1 : list { a | Q a}}
         {InlofAs2Sigs : forall a : A, List.In a lofAs -> {x | Q x}}
         {s : state} {lofSigs2 s'},
    tmap_aux (fun p s => Ret p s) lofAs lofSigs1 InlofAs2Sigs s = OK lofSigs2 s' ->
    (forall x, List.In (proj1_sig x) lofAs \/ InA P1SigEq x lofSigs1) ->
    (forall a (InlofAs : List.In a lofAs), a = proj1_sig (InlofAs2Sigs a InlofAs)) ->
    (forall a (InlofAs : List.In a lofAs), ~InA P1SigEq (InlofAs2Sigs a InlofAs) lofSigs1) ->
    List.NoDup lofAs ->
    NoDupA P1SigEq lofSigs1 ->
    Sig_in_List lofSigs2.
Proof.
  induction lofAs; intros *; intros e; minv e.

  - split; [ firstorder | auto ].
  - intros or_InlofAs_InlofSigs eq_proj1 nInA_lofSigs NoDup_lofAs NoDupA_lofSigs;
      eapply IHlofAs; eauto with setoidl.
    (* CASE [In (proj1_sig x) lofAs] or [InA x (lofSigs1 ++ (InlofAs2Sigs a))] *)
    + intros x; specialize (or_InlofAs_InlofSigs x);
        inversion_clear or_InlofAs_InlofSigs as [In_lofAs | InA_lofSigs].
      (* SUBCASE [a = proj1_sig x \/ In (proj1_sig x) lofAs] *)
      -- inversion_clear In_lofAs as [eq_a_proj1 | In_proj1_lofAs].
         ++ right; erewrite (InA_app_iff P1SigEq lofSigs1); right.
            eapply InA_cons_hd; specialize (eq_proj1 a (in_eq a lofAs)).
            transitivity a; auto.
         ++ auto.
      -- right; erewrite (InA_app_iff P1SigEq lofSigs1); left; auto.
    (* CASE [x ∈ lofAs ⇒ x ∉ (lofSigs ++ (InlofAs2Sigs a))] *)
    + intros *; erewrite InA_app_iff.
      inversion_clear 1 as [InA_lofSigs | InA_singl].
      -- unfold in_T_in_sublist_T in InA_lofSigs.
         eapply nInA_lofSigs; eauto.
      -- inversion_clear InA_singl as [e1 e2 P1SigEq_ | e1 e2 InAnil]; [ | inversion InAnil].
         unfold in_T_in_sublist_T in P1SigEq_.
         assert (e : a = a0) by (transitivity (proj1_sig (InlofAs2Sigs a (in_eq a lofAs)));
                                 [ eapply eq_proj1 | rewrite <- P1SigEq_; symmetry; eapply eq_proj1 ]).
         clear P1SigEq_; rewrite <- e in InlofAs; inversion NoDup_lofAs; contradiction.
    (* NoDup lofAs *)
    + inversion NoDup_lofAs; assumption.
    (* NoDupA (lofSigs1 ++ [InlofAs2Sigs a]) *)
    + eapply NoDupA_app; eauto.
      apply NoDupA_singleton.
      intros x InA_lofSigs; inversion_clear 1 as [e1 e2 P1SigEq_ | e1 e2 InAnil]; [ | inversion InAnil].
      apply (nInA_lofSigs a (in_eq a lofAs)).
      eapply InA_eqA; eauto with typeclass_instances.
Qed.

(** ** Facts about Sitpn Information Generation Function *)

Lemma gen_sitpn_infos_inv_γ :
  forall {sitpn s v s'},
    generate_sitpn_infos sitpn s = OK v s' ->
    γ s = γ s'.
Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_sitpn_infos_inv_beh :
  forall {sitpn s v s'},
    generate_sitpn_infos sitpn s = OK v s' ->
    beh s = beh s'.
Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_sitpn_infos_sil_lofPs :
  forall {sitpn s v s'},
    generate_sitpn_infos sitpn s = OK v s' ->
    Sig_in_List (lofPs s').
Proof.
  intros until s'; intros e; monadInv e; intros.
  assert (eq_lofPs : x = lofPs s') by
  (transitivity (lofPs s5);
   [ match goal with
     | [ H: set_lofPs _ _ = OK _ _ |- _ ] => minv H; reflexivity
     end
   | pattern s5, s'; mend_sinv ]).
  rewrite <- eq_lofPs.
  eapply tmap_aux_sil; eauto;
    [intros p; left; exact (proj2_sig p) | inversion 1 | exact (nodup_pls sitpn)].
Qed.

Lemma gen_sitpn_infos_sil_lofTs :
  forall {sitpn s v s'},
    generate_sitpn_infos sitpn s = OK v s' ->
    Sig_in_List (lofTs s').
Proof.
  intros until s'; intros e; monadInv e; intros.
  match goal with
  | [ H: set_lofTs ?X ?S1 = OK _ ?S2 |- Sig_in_List (lofTs ?S3) ] =>
      cut (X = lofTs S3); [
        intros eq_lofTs |
        (transitivity (lofTs S2); [ (minv H; reflexivity) | (pattern S2, S3; mend_sinv) ])
      ]
  end.
  rewrite <- eq_lofTs.
  eapply tmap_aux_sil; eauto;
    [intros p; left; exact (proj2_sig p) | inversion 1 | exact (nodup_trs sitpn)].
Qed.
