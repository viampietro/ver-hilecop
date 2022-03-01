(** * Facts about Port Generation and Connection *)

Require Import String.
Require Import common.CoqLib.
Require Import common.StateAndErrorMonad.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import common.proofs.ListMonadFacts.
Require Import common.proofs.ListMonadTactics.
Require Import common.ListPlus.
Require Import common.proofs.SetoidListFacts.

Require Import sitpn.SitpnLib.

Require Import hvhdl.AbstractSyntax.

Require Import transformation.Sitpn2HVhdl.
Require Import transformation.Sitpn2HVhdlUtils.
Require Import transformation.proofs.SInvTactics.
Require Import transformation.proofs.Sitpn2HVhdlUtilsFacts.

(** ** Facts about Action Port Generation *)

Section GenActionPorts.

  Lemma gen_aports_inv_p2pci :
    forall {sitpn s v s'},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      p2pci (γ s) = p2pci (γ s').
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_aports_inv_t2tci :
    forall {sitpn s v s'},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      t2tci (γ s) = t2tci (γ s').
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_aports_inv_lofPs :
    forall {sitpn s v s'},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_aports_inv_lofTs :
    forall {sitpn s v s'},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_aports_pci_ex :
    forall {sitpn s v s' p},
      generate_action_ports_and_ps sitpn s = OK v s' ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pci (γ s))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) -> 
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pci (γ s'))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern.
         minv EQ3; cbn.
         intros [ id__p [ g__p [ i__p [ o__p [ InA_p2pci InCs_ ] ] ] ] ];
           do 4 eexists; split; [ | right ]; eauto.
  Qed.
  
End GenActionPorts.

(** ** Facts about Function Port Generation *)

Section GenFunPorts.
  
  Lemma gen_fports_inv_p2pci :
    forall {sitpn s v s'},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      p2pci (γ s) = p2pci (γ s').
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_fports_inv_t2tci :
    forall {sitpn s v s'},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      t2tci (γ s) = t2tci (γ s').
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_fports_inv_lofPs :
    forall {sitpn s v s'},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_fports_inv_lofTs :
    forall {sitpn s v s'},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.   

  Lemma gen_fports_pci_ex :
    forall {sitpn s v s' p},
      generate_fun_ports_and_ps sitpn s = OK v s' ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pci (γ s))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) -> 
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pci (γ s'))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern.
         minv EQ3; cbn.
         intros [ id__p [ g__p [ i__p [ o__p [ InA_p2pci InCs_ ] ] ] ] ];
           do 4 eexists; split; [ | right ]; eauto.
  Qed.
  
End GenFunPorts.

(** ** Facts about Condition Port Generation *)

Section GenCondPorts.

  Lemma gen_cports_inv_p2pci :
    forall {sitpn s v s'},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      p2pci (γ s) = p2pci (γ s').
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_cports_inv_t2tci :
    forall {sitpn s v s'},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      t2tci (γ s) = t2tci (γ s').
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.
  
  Lemma gen_cports_inv_lofPs :
    forall {sitpn s v s'},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_cports_inv_lofTs :
    forall {sitpn s v s'},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.
  
  Lemma gen_cports_pci_ex :
    forall {sitpn s v s' p},
      generate_and_connect_cond_ports sitpn s = OK v s' ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pci (γ s))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) -> 
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pci (γ s'))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
  Proof. intros * EQ; pattern s, s'; solve_sinv_pattern.
         minv EQ13.
         intros [ id__p [ g__p [ i__p [ o__p [ InA_p2pci InCss7 ] ] ] ] ].
         exists id__p.
         (* 2 CASES [id__p = x2] or [id__p <> x2] *)
         destruct (Nat.eq_dec id__p x2) as [ eq_ | neq_ ].
         + (* CASE [id__p = x2] *)
           subst.
           exists g, x4, o; split; [ assumption | ].
           cut (Petri.place_entid = i0); [ intros eq_id__e; subst; eapply put_comp_aux_InCs; eauto | ].
           assert (eq_beh : beh s3 = beh s6) by (pattern s3, s6; mend_sinv).
           assert (InCss6 : InCs (cs_comp x2 i0 g i o) (beh s6))
             by (rewrite <- eq_beh; eapply get_comp_InCs; eauto).
           erewrite <- put_comp_aux_inv_state in InCss7; eauto.
           assert (eq_comp : cs_comp x2 Petri.place_entid g__p i__p o__p = cs_comp x2 i0 g i o)
             by (rewrite <- eq_beh in InCss7, InCss6; eapply get_comp_uniq_comp; eauto).
           injection eq_comp; auto.
         + (* CASE [id__p <> x2] *)
           erewrite <- put_comp_aux_inv_state in InCss7; eauto.
           do 3 eexists; eauto with put_comp.
  Qed.
  
End GenCondPorts.

(** ** Facts about Port Generation Function *)

Lemma gen_ports_inv_p2pci :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    p2pci (γ s) = p2pci (γ s').
Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_ports_inv_t2tci :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    t2tci (γ s) = t2tci (γ s').
Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_ports_inv_lofPs :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    lofPs s = lofPs s'.
Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_ports_inv_lofTs :
  forall {sitpn : Sitpn} {s : Sitpn2HVhdlState sitpn} {v : unit}
         {s' : Sitpn2HVhdlState sitpn},
    generate_ports s = OK v s' -> lofTs s = lofTs s'.
Proof. intros * EQ; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_ports_pci_ex :
  forall (sitpn : Sitpn) (s : Sitpn2HVhdlState sitpn) v s' p,
    generate_ports s = OK v s' ->
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pci (γ s))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) -> 
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pci (γ s'))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
Proof. intros * EQ pci_ex; monadInv EQ.
       eapply gen_cports_pci_ex; eauto;
         eapply gen_fports_pci_ex; eauto;
         eapply gen_aports_pci_ex; eauto.
Qed.


