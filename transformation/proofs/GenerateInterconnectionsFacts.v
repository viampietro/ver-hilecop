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
  
  Lemma conn_to_output_tcis_nodup_cids :
    forall {sitpn : Sitpn} {pinfo i o} {s : Sitpn2HVhdlState sitpn}
           {v s'},
      connect_to_output_tcis pinfo i o s = OK v s' ->
      NoDup (get_cids (beh s)) ->
      NoDup (get_cids (beh s')).
  Proof.
    intros *; intros e; pattern s,s'; solve_sinv_pattern.
    monadInv1 EQ15; simpl.    
    erewrite <- put_comp_aux_inv_state; eauto with put_comp.
    monadInv1 EQ23; simpl.    
    erewrite <- put_comp_aux_inv_state; eauto with put_comp.
  Qed.
  
  Lemma conn_to_output_tcis_comp_ex :
    forall {sitpn : Sitpn} {pinfo i o} {s : Sitpn2HVhdlState sitpn}
           {v s'} {id__c id__e},
      connect_to_output_tcis pinfo i o s = OK v s' ->
      (exists g' i' o', InCs (cs_comp id__c id__e g' i' o') (beh s)) ->
      (exists g' i' o', InCs (cs_comp id__c id__e g' i' o') (beh s')).
  Proof.
    intros *; intros e; pattern s,s'; solve_sinv_pattern.
    - monadInv1 EQ15; simpl.    
      erewrite <- put_comp_aux_inv_state; eauto.
      (* 2 CASES [id__c = x1] or [id__c <> x1] *)
      destruct (Nat.eq_dec id__c x1) as [ eq_ | neq_ ].
      + (* CASE [id__c = x1] *)
        subst; intros InCs_ex.
        cut (id__e = i2); [ intros eq_id__e; subst; eapply put_comp_aux_comp_ex; eauto | ].
        destruct InCs_ex as [ g' [ i' [ o' InCs6_bis ] ] ].
        assert (eq_beh : beh s2 = beh s6). {
          transitivity (beh s3); [ pattern s2, s3; solve_sinv_pattern | ].
          transitivity (beh s4); [ pattern s3, s4; solve_sinv_pattern | ].
          transitivity (beh s5); [ pattern s4, s5; solve_sinv_pattern | ].
          transitivity (beh s6); [ pattern s5, s6; solve_sinv_pattern | reflexivity ].
        }
        assert (InCs6 : InCs (cs_comp x1 i2 g i1 o1) (beh s6))
          by (rewrite <- eq_beh; eapply get_comp_InCs; eauto).
        assert (eq_comp : cs_comp x1 id__e g' i' o' = cs_comp x1 i2 g i1 o1)
          by (rewrite <- eq_beh in InCs6_bis, InCs6; eapply get_comp_uniq_comp;  eauto).
        injection eq_comp; auto.
      + (* CASE [id__c <> x1] *)
        destruct 1 as [ g' [ i' [ o' InCs6 ] ] ];
          do 3 eexists; eauto with put_comp.
    - monadInv1 EQ23; simpl.
      erewrite <- put_comp_aux_inv_state; eauto.
      (* 2 CASES [id__c = x1] or [id__c <> x1] *)
      destruct (Nat.eq_dec id__c x1) as [ eq_ | neq_ ].
      + (* CASE [id__c = x1] *)
        subst; intros InCs_ex.
        cut (id__e = i3); [ intros eq_id__e; subst; eapply put_comp_aux_comp_ex; eauto | ].
        destruct InCs_ex as [ g' [ i' [ o' InCs10_bis ] ] ].
        assert (eq_beh : beh s3 = beh s10). {
          transitivity (beh s4); [ pattern s3, s4; solve_sinv_pattern | ].
          transitivity (beh s5); [ pattern s4, s5; solve_sinv_pattern | ].
          transitivity (beh s6); [ pattern s5, s6; solve_sinv_pattern | ].
          transitivity (beh s7); [ pattern s6, s7; solve_sinv_pattern | ].
          transitivity (beh s8); [ pattern s7, s8; solve_sinv_pattern | ].
          transitivity (beh s9); [ pattern s8, s9; solve_sinv_pattern | ].
          transitivity (beh s10); [ pattern s9, s10; solve_sinv_pattern | reflexivity ].
        }
        assert (InCs10 : InCs (cs_comp x1 i3 g i2 o2) (beh s10)) by (rewrite <- eq_beh; eapply get_comp_InCs; eauto).
        assert (eq_comp : cs_comp x1 id__e g' i' o' = cs_comp x1 i3 g i2 o2)
          by (rewrite <- eq_beh in InCs10_bis, InCs10; eapply get_comp_uniq_comp; eauto).
        injection eq_comp; auto.
      + (* CASE [id__c <> x1] *)
        destruct 1 as [ g' [ i' [ o' InCs10 ] ] ];
          do 3 eexists; eauto with put_comp.
  Qed.

  Lemma conn_to_output_tcis_pci_ex_inv :
    forall {sitpn : Sitpn} {pinfo i o}
           {s : Sitpn2HVhdlState sitpn} {v s' p},
      connect_to_output_tcis pinfo i o s = OK v s' ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s'))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
  Proof.
    destruct 2 as [ id__p [ g__p [ i__p [ o__p [ InA_p2pcomp InCss ] ] ] ] ].
    exists id__p.
    cut (exists g__p i__p o__p, InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
    intros InCs_ex; destruct InCs_ex as [ g__p' [ i__p' [ o__p' InCss' ] ] ].
    do 3 eexists; split; eauto; erewrite <- conn_to_output_tcis_inv_γ; eauto.
    eapply conn_to_output_tcis_comp_ex; eauto.
  Qed.

  
End ConnToOutputTcisFacts.

(** *** Facts about the [generate_interconnections] *)

Section GenInterFacts.

  Lemma gen_inter_pci_ex :
    forall (sitpn : Sitpn) (s : Sitpn2HVhdlState sitpn) v s' p,
      generate_interconnections s = OK v s' ->
      NoDup (get_cids (beh s)) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s'))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
  Proof.  
    intros *; intros H; pattern s, s'.
    monadFullInv H.
    intros NoDup_cids pci_ex.
    apply proj2 with (A := NoDup (get_cids (beh s'))).
    generalize NoDup_cids, pci_ex.
    pattern s0, s'; eapply (iter_inv_state EQ0); eauto.
    (*  *)
    - unfold Transitive.
      intros *; intros tr_xy tr_yz NoDup_cids_x pci_ex_x.
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
      intros NoDup_cids1 pci_ex1; split.
      + eapply put_comp_nodup_cids; eauto;
          eapply conn_to_output_tcis_nodup_cids; eauto.
      + eapply (put_comp_pci_ex EQ6); [
            eapply conn_to_output_tcis_nodup_cids; eauto
          | eapply conn_to_output_tcis_comp_ex; eauto;
            erewrite <- conn_to_input_tcis_inv_beh; eauto;
            erewrite <- get_comp_aux_inv_state; eauto;
            exists g, i, o; eapply get_comp_aux_InCs; eauto
          | eapply conn_to_output_tcis_pci_ex_inv; eauto
          ].      
  Qed.
  
End GenInterFacts.

