(** * Facts about HILECOP's transformation utilitary functions *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.ListPlus.
Require Import common.ListDep.
Require Import common.StateAndErrorMonad.

Require Import String.
Require Import common.proofs.StateAndErrorMonadTactics.

Require Import sitpn.Sitpn.
Require Import sitpn.SitpnFacts.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.proofs.AbstractSyntaxFacts.

Require Import transformation.Sitpn2HVhdlTypes.
Require Import transformation.Sitpn2HVhdlUtils.
Require Import transformation.proofs.SInvTactics.

(** ** Facts about [put_comp] *)

Section PutCompFacts.

  Lemma put_comp_aux_InCs_inv :
    forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o}
           {s : Sitpn2HVhdlState sitpn} {v s'},
      put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
      forall id__c' id__e' g' i' o',
        id__c' <> id__c ->
        InCs (cs_comp id__c' id__e' g' i' o') cstmt ->
        InCs (cs_comp id__c' id__e' g' i' o') v.
  Proof. induction cstmt; intros *; simpl; try (solve [inversion 3]).
         - case_eq (id__c0 =? id__c); intros e EQ; monadInv EQ.
           + inversion 2; subst. 
             rewrite Nat.eqb_eq in e; congruence.
           + inversion_clear 2; do 2 constructor.
         - intros EQ; monadInv EQ.
  Admitted.
  
  Lemma put_comp_aux_InCs :
    forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o}
           {s : Sitpn2HVhdlState sitpn} {v s'},
      put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
      InCs (cs_comp id__c id__e g i o) v.
  Admitted.

  Lemma put_comp_aux_comp_ex :
    forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o}
           {s : Sitpn2HVhdlState sitpn} {v s'},
      put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
      (exists g0 i0 o0, InCs (cs_comp id__c id__e g0 i0 o0) cstmt) ->
      (exists g1 i1 o1, InCs (cs_comp id__c id__e g1 i1 o1) v).
  Admitted.
  
  Lemma put_comp_aux_pci_ex :
    forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o}
           {s : Sitpn2HVhdlState sitpn} {v s' p},
      put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
      NoDup (get_cids cstmt) ->
      (exists g' i' o', InCs (cs_comp id__c id__e g' i' o') cstmt) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) cstmt) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s'))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) v).
  Proof.
    intros *; intros EQ NoDup_compids InCs_idc_ex.  
    destruct 1 as [ id__p [ g__p [ i__p [ o__p [ InA_ InCS_cstmt ] ] ] ] ].
    
    (* 2 CASES : [id__p = id__c] or [id__p <> id__c]. *)
    destruct (Nat.eq_dec id__p id__c) as [ eq_idp_idc | diff_idp_idc ].

    (* CASE [id__p = id__c] *)
    - rewrite <- (put_comp_aux_inv_state EQ).
      exists id__p, g, i, o; split; [ assumption | ].
      destruct InCs_idc_ex as [ g' [ i' [ o' InCs_idc ] ] ].
      rewrite eq_idp_idc.
      assert (eq_ide_plid : id__e = Petri.place_entid).
      {
        rewrite eq_idp_idc in InCS_cstmt.
        specialize (InCs_NoDup_comp_eq InCS_cstmt InCs_idc NoDup_compids)
          as eq_comp.
        inversion eq_comp; subst; reflexivity.      
      }
      rewrite <- eq_ide_plid; eapply put_comp_aux_InCs; eauto.    
      
    (* CASE [id__p <> id__c] *)
    - erewrite <- (put_comp_aux_inv_state EQ).
      exists id__p, g__p, i__p, o__p; split;
        [ assumption | (eapply (put_comp_aux_InCs_inv EQ); eauto) ].
  Qed.

  Lemma put_comp_pci_ex :
    forall {sitpn : Sitpn} {id__c id__e} {g i o}
           {s : Sitpn2HVhdlState sitpn} {v s' p},
      put_comp id__c id__e g i o s = OK v s' ->
      NoDup (get_cids (beh s)) ->
      (exists g' i' o', InCs (cs_comp id__c id__e g' i' o') (beh s)) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s'))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
  Proof. intros *; intros e; monadFullInv e; cbn.
         eapply put_comp_aux_pci_ex; eauto.  
  Qed.
  
  Lemma put_comp_nodup_cids :
    forall {sitpn : Sitpn} {id__c id__e} {g i o}
           {s : Sitpn2HVhdlState sitpn} {v s'},
      put_comp id__c id__e g i o s = OK v s' ->
      NoDup (get_cids (beh s)) ->
      NoDup (get_cids (beh s')).
  Admitted.

  
End PutCompFacts.

(** ** Facts about [get_comp] *)

Section GetCompFacts.

  (* Can not use [solve_sinv_pattern] to decide [get_comp_inv_state]
     because it is used in [solve_sinv_pattern].  *)
  
  Lemma get_comp_aux_InCs :
    forall {cstmt} {sitpn : Sitpn} {id__c : ident}
           {s : Sitpn2HVhdlState sitpn} {s'}
           {id__e g i o},
      get_comp_aux sitpn id__c cstmt s = OK (Some (id__e, g, i, o)) s' ->
      InCs (cs_comp id__c id__e g i o) cstmt.
  Admitted.
  
End GetCompFacts.
