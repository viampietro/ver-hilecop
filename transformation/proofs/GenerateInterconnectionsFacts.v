Require Import common.CoqLib.
Require Import common.StateAndErrorMonad.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import common.proofs.ListMonadFacts.

Require Import sitpn.SitpnLib.

Require Import hvhdl.HVhdlCoreLib.

Require Import transformation.Sitpn2HVhdl.
Require Import transformation.Sitpn2HVhdlUtils.
Require Import transformation.proofs.SInvTactics.
Require Import transformation.proofs.Sitpn2HVhdlUtilsFacts.

(** *** Facts about the [connect_to_input_tcis] *)

Section ConnToInputTcisFacts.

  Lemma conn_to_input_tcis_inv_beh :
    forall {sitpn : Sitpn} {pinfo i} {s : Sitpn2HVhdlState sitpn} {v s'},
      connect_to_input_tcis pinfo i s = OK v s' ->
      beh s = beh s'.
  Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma conn_to_input_tcis_inv_γ :
    forall {sitpn : Sitpn} {pinfo i} {s : Sitpn2HVhdlState sitpn} {v s'},
      connect_to_input_tcis pinfo i s = OK v s' ->
      γ s = γ s'.
  Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

End ConnToInputTcisFacts.

(** *** Facts about the [connect_to_output_tcis] *)

Section ConnToOutputTcisFacts.

  Lemma conn_to_output_tcis_inv_γ :
    forall {sitpn : Sitpn} {pinfo i o} {s : Sitpn2HVhdlState sitpn} {v s'},
      connect_to_output_tcis pinfo i o s = OK v s' ->
      γ s = γ s'.
  Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

  
  Lemma conn_to_output_tcis_p_comp_ex_inv :
    forall {sitpn : Sitpn} {pinfo i o}
           {s : Sitpn2HVhdlState sitpn} {v s' p},
      connect_to_output_tcis pinfo i o s = OK v s' ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s'))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
  Proof. intros *; intros H; pattern s,s'; solve_sinv_pattern.
         - cbn.
           inversion EQ15; clear EQ15; subst_right_no_fail; cbn.
           rewrite <- (put_comp_aux_inv_state EQ12).
  Admitted.
  
  Lemma conn_to_output_tcis_nodup_comp_ids :
    forall {sitpn : Sitpn} {pinfo i o} {s : Sitpn2HVhdlState sitpn}
           {v s'},
      connect_to_output_tcis pinfo i o s = OK v s' ->
      NoDup (get_comp_ids (beh s)) ->
      NoDup (get_comp_ids (beh s')).
  Admitted.
  
  Lemma conn_to_output_tcis_comp_ex :
    forall {sitpn : Sitpn} {pinfo i o} {s : Sitpn2HVhdlState sitpn}
           {v s'} {id__c id__e},
      connect_to_output_tcis pinfo i o s = OK v s' ->
      (exists g' i' o', InCs (cs_comp id__c id__e g' i' o') (beh s)) ->
      (exists g' i' o', InCs (cs_comp id__c id__e g' i' o') (beh s')).
  Admitted.
  
End ConnToOutputTcisFacts.

(** *** Facts about the [generate_interconnections] *)

Section GenInterFacts.

  Lemma gen_inter_p_comp_ex :
    forall (sitpn : Sitpn) (s : Sitpn2HVhdlState sitpn) v s' p,
      generate_interconnections s = OK v s' ->
      NoDup (get_comp_ids (beh s)) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s'))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
  Proof.  
    intros *; intros H; pattern s, s'.
    monadFullInv H.
    intros NoDup_comp_ids pci_ex.
    apply proj2 with (A := NoDup (get_comp_ids (beh s'))).
    generalize NoDup_comp_ids, pci_ex.
    pattern s0, s'; eapply (iter_inv_state EQ0); eauto.
    (*  *)
    - unfold Transitive.
      intros *; intros tr_xy tr_yz NoDup_comp_ids_x pci_ex_x.
      apply tr_yz; eapply tr_xy; eauto.
      
    (*  *)
    - intros *; intros e; monadFullInv e.
      match goal with
      | [ E1: ListMonad.getv _ _ _ ?S1 = OK _ ?S2,
            E2: ListMonad.getv _ _ _ ?S2 = OK _ ?S3,
              E3: get_comp_aux _ _ _ ?S3 = OK _ ?S4 |- _ ] =>
          erewrite (getv_inv_state E1); eauto;
          erewrite (getv_inv_state E2); eauto;
          erewrite (get_comp_aux_inv_state E3); eauto
      end.
      match goal with
      | [ E: (match ?X with _ => _ end) _ = OK _ _ |- _ ] =>
          destruct X; monadInv E
      end.
      match goal with
      | [ E: (let (_, _) := ?X in _) _ = OK _ _  |- _ ] =>
          destruct X as [ [ [ id__e g ] i ] o ]; monadInv E
      end.
      match goal with
      | [ E: connect_to_input_tcis _ _ _ = OK _ _ |- _ ] =>
          erewrite (conn_to_input_tcis_inv_beh E); eauto;
          erewrite (conn_to_input_tcis_inv_γ E); eauto
      end.
      match goal with
      | [ E: (let (_, _) := ?X in _) _ = OK _ _ |- _ ] =>
          destruct X
      end.
      intros NoDup_comp_ids1 pci_ex1; split.
      + eapply put_comp_nodup_comp_ids; eauto;
          eapply conn_to_output_tcis_nodup_comp_ids; eauto.
      + eapply (put_comp_p_comp_ex EQ6); [
            eapply conn_to_output_tcis_nodup_comp_ids; eauto
          | eapply conn_to_output_tcis_comp_ex; eauto;
            erewrite <- conn_to_input_tcis_inv_beh; eauto;
            erewrite <- get_comp_aux_inv_state; eauto;
            exists g, i, o; eapply get_comp_aux_InCs; eauto
          | eapply conn_to_output_tcis_p_comp_ex_inv; eauto
          ].      
  Qed.
  
End GenInterFacts.

