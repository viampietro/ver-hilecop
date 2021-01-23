(** * Facts about Sitpn Information Generation Functions *)

Require Import common.Coqlib.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListDep.
Require Import common.ListMonad.
Require Import common.ListMonadFacts.
Require Import common.ListMonadTactics.
Require Import common.ListPlus.
Require Import common.GlobalFacts.


Require Import sitpn.dp.Sitpn.
Require Import sitpn.dp.SitpnFacts.

Require Import sitpn2hvhdl.Sitpn2HVhdl.

(** ** Facts about Transition Information Generation *)

Section TInfos.

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
    
End TInfos.

(** ** Facts about Place Information Generation *)

Section PInfos.

  Lemma all_conflicts_solved_by_mutex_inv_state :
    forall {sitpn lofTs s v s'},
      all_conflicts_solved_by_mutex sitpn lofTs s = OK v s' ->
      s = s'.
  Proof.
    induction lofTs; simpl; intros until s'; intros e; minv e; auto.
    transitivity s0.
    - eapply find_inv_state; eauto with typeclass_instances.
      intros until s2; intros e1; pattern s1, s2; minv e1;
        (transitivity s6; [ eauto with listmonad | ];
         transitivity s4; [ eauto with listmonad | ];
         transitivity s5; [ eauto with listmonad | ];
         eauto with listmonad).
    - eapply IHlofTs; eauto.
    - eapply find_inv_state; eauto with typeclass_instances.
      intros until s2; intros e1; pattern s1, s2; minv e1;
        (transitivity s5; [ eauto with listmonad | ];
         transitivity s3; [ eauto with listmonad | ];
         transitivity s4; [ eauto with listmonad | ];
         eauto with listmonad).
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
  
End PInfos.

(** ** Facts about Generation of Interpretation Information *)

Section InterprInfos.

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

End InterprInfos.

(** ** Facts about Checking of Sitpn Well-definition *)

Section CheckWDSitpn.

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
  
End CheckWDSitpn.

(** ** Facts about Dependently-typed Lists Generation *)

Lemma tmap_aux_sil_lofPs :
  forall {sitpn Nats Pls} {InNats2P : forall n : nat, List.In n Nats -> P sitpn}
         {s : Sitpn2HVhdlState sitpn} {lofPs s'},
    tmap_aux (fun p s => Ret p s) Nats Pls InNats2P s = OK lofPs s' ->
    (forall p, List.In (proj1_sig p) Nats \/ InA Peq p Pls) ->
    (forall x (InxNats : List.In x Nats), x = proj1_sig (InNats2P x InxNats)) ->
    (forall x (InxNats : List.In x Nats), ~InA Peq (InNats2P x InxNats) Pls) ->
    List.NoDup Nats ->
    NoDupA Peq Pls ->
    Sig_in_List lofPs.
Proof.
  induction Nats; intros until s'; intros e; minv e; intros.

  - split; [ firstorder | auto ].
  - eapply IHNats; eauto.
    + intros p; specialize (H p); inversion_clear H as [In_aNats | InA_Pls].
      -- inversion_clear In_aNats as [e_proj1p_a | In_Nats].
         ++ right; eapply (InA_app_iff seq Pls _ _); right.
            eapply InA_cons_hd; specialize (H0 a (in_eq a Nats)).
            transitivity a; [auto | auto].
         ++ auto.
      -- right; eapply (InA_app_iff seq Pls _ _); left; auto.
    + intros *; intros InA_Pls_app. erewrite InA_app_iff in InA_Pls_app.
      inversion_clear InA_Pls_app as [InA_Pls | InA_singleton].
      -- unfold in_T_in_sublist_T in InA_Pls.
         specialize (H1 x (in_cons a x Nats InxNats)); contradiction.
      -- inversion_clear InA_singleton as [e1 e2 Peq_InNats2P | e1 e2 InAnil]; [ | inversion InAnil].
         unfold in_T_in_sublist_T in Peq_InNats2P.
         assert (e_ax : a = x) by
             (transitivity (proj1_sig (InNats2P a (in_eq a Nats)));
              [eapply H0 | rewrite <- Peq_InNats2P; symmetry; eapply H0]).
         rewrite e_ax in H2; inversion H2; contradiction.
    + inversion H2; assumption.
    + eapply NoDupA_app; eauto.
      apply NoDupA_singleton.
      intros; inversion_clear H5 as [e1 e2 Peq_x_InNats2P | e1 e2 InAnil]; [ | inversion InAnil].
      apply (H1 a (in_eq a Nats)); eapply InA_eqA; eauto with typeclass_instances.
Qed. 

(** ** Facts about Sitpn Information Generation Function *)

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

Lemma gen_sitpn_infos_sil_lofPs :
  forall {sitpn decpr s v s'},
    generate_sitpn_infos sitpn decpr s = OK v s' ->
    List.NoDup (places sitpn) ->
    Sig_in_List (lofPs s').
Proof.
  intros until s'; intros e; monadInv e; intros.
  rewrite <- (gen_finfos_inv_lofPs EQ15); clear EQ15.
  rewrite <- (gen_ainfos_inv_lofPs EQ13); clear EQ13.
  rewrite <- (gen_cinfos_inv_lofPs EQ12); clear EQ12.
  rewrite <- (gen_pinfos_inv_lofPs EQ11); clear EQ11.
  rewrite <- (gen_tinfos_inv_lofPs EQ10); clear EQ10.
  rewrite <- (check_wd_sitpn_inv_eq_state EQ9); clear EQ9.
  do 5 (match goal with
        | [ H: ?F _ _ = OK _ ?st1 |- Sig_in_List (lofPs ?st1) ] =>
          minv H; simpl; auto; clear H
        end).
  eapply tmap_aux_sil_lofPs; eauto;
    [intros; left; exact (proj2_sig p) | inversion 1].
Qed.
