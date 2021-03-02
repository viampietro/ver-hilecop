(** * Facts about Sitpn Information Generation Functions *)

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
Require Import sitpn2hvhdl.GenerateInfosInvs.

(** ** Facts about Transition Information Generation *)

Section TInfos.
  
End TInfos.

(** ** Facts about Place Information Generation *)

Section PInfos.
  
End PInfos.

(** ** Facts about Generation of Interpretation Information *)

Section InterprInfos.

End InterprInfos.

(** ** Facts about Checking of Sitpn Well-definition *)

Section CheckWDSitpn.

  
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

