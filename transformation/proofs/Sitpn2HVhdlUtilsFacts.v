(** * Facts about HILECOP's transformation utilitary functions *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.ListPlus.
Require Import common.ListDep.
Require Import common.StateAndErrorMonad.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import common.InAndNoDup.

Require Import sitpn.Sitpn.
Require Import sitpn.SitpnFacts.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.proofs.AbstractSyntaxFacts.

Require Import transformation.Sitpn2HVhdlTypes.
Require Import transformation.Sitpn2HVhdlUtils.
Require Import transformation.proofs.SInvTactics.

(** ** Facts about [get_comp] *)

Section GetCompFacts.
  
  Lemma get_comp_aux_InCs :
    forall {cstmt} {sitpn : Sitpn} {id__c : ident}
           {s : Sitpn2HVhdlState sitpn} {s'}
           {id__e g i o},
      get_comp_aux sitpn id__c cstmt s = OK (Some (id__e, g, i, o)) s' ->
      InCs (cs_comp id__c id__e g i o) cstmt.
  Proof.
    induction cstmt; try (intros *; intros e; monadInv e).
    (* comp *)
    intros *; cbn; destruct (id__c0 =? id__c)%nat eqn: eq_idc; intros e; monadInv e.
    f_equal; apply beq_nat_true; auto.
    (* par *)
    destruct x; destruct x0; monadInv EQ2;
      [ left; eapply IHcstmt1 | right; eapply IHcstmt2 ]; eauto.
  Qed.

  Lemma get_comp_InCs :
    forall {sitpn : Sitpn} {id__c : ident}
           {s : Sitpn2HVhdlState sitpn} {s'}
           {id__e g i o},
      get_comp id__c s = OK (id__e, g, i, o) s' ->
      InCs (cs_comp id__c id__e g i o) (beh s).
  Proof. intros *; intros e; minv e.
         eapply get_comp_aux_InCs; eauto.
  Qed.
  
  Lemma get_comp_aux_not_InCs:
    forall (cstmt : cs) (sitpn : Sitpn) (s s' : Sitpn2HVhdlState sitpn) (id__c : ident),
      get_comp_aux sitpn id__c cstmt s = OK None s' ->
      (exists id__e g i o, InCs (cs_comp id__c id__e g i o) cstmt) -> False.
  Proof.
    induction cstmt.
    1, 4: (destruct 2 as [ id__e [ g [ i [ o InCs_ ] ] ] ]; inversion InCs_).
    (* comp *)
    - intros *; cbn; destruct (id__c0 =? id__c)%nat eqn: eq_idc; intros e; monadInv e.
      destruct 1 as [ id__e0 [ g0 [ i0 [ o0 eq_comp ] ] ] ]; injection eq_comp; intros.
      eapply beq_nat_false; eauto.
    (* par *)
    - intros *; intros e; monadInv e; destruct x; destruct x0; monadInv EQ2.
      destruct 1 as [ id__e [ g [ i [ o [ InCs1 | InCs2 ] ] ] ] ];
        [ eapply IHcstmt1 | eapply IHcstmt2 ]; eauto.
  Qed.
  
  Lemma get_comp_aux_not_In_cids:
    forall (cstmt : cs) (sitpn : Sitpn) (s s' : Sitpn2HVhdlState sitpn) (id__c : ident),
      get_comp_aux sitpn id__c cstmt s = OK None s' -> In id__c (get_cids cstmt) -> False.
  Proof. (intros; eapply get_comp_aux_not_InCs; eauto; eapply get_cids_In_ex; eauto). Qed.

  Lemma get_comp_aux_uniq_comp:
    forall {sitpn : Sitpn} {id__c} {cstmt} {s s' : Sitpn2HVhdlState sitpn} {v},
      get_comp_aux sitpn id__c cstmt s = OK (Some v) s' ->
      forall (id__e : ident) (g : genmap) (i : inputmap) (o : outputmap)
             (id__e' : ident) (g' : genmap) (i' : inputmap) (o' : outputmap),
        InCs (cs_comp id__c id__e g i o) cstmt ->
        InCs (cs_comp id__c id__e' g' i' o') cstmt ->
        cs_comp id__c id__e g i o = cs_comp id__c id__e' g' i' o'.
  Proof.
    induction cstmt.
    1, 4: inversion 2.
    inversion_clear 2; inversion_clear 1; reflexivity.
    intros *; intros e.
    destruct 1 as [ InCs1 | InCs2]; destruct 1 as [ InCs1' | InCs2' ].
    1, 4 : (minv e; (eauto || (elimtype False; eapply get_comp_aux_not_InCs; eauto))).
    1,2 : (minv e; elimtype False; eapply get_comp_aux_not_InCs; eauto).
  Qed.
  
  Lemma get_comp_uniq_comp:
    forall (sitpn : Sitpn) (id__c : ident) (s s' : Sitpn2HVhdlState sitpn) v,
      get_comp id__c s = OK v s' ->
      forall (id__e : ident) (g : genmap) (i : inputmap) (o : outputmap)
             (id__e' : ident) (g' : genmap) (i' : inputmap) (o' : outputmap),
        InCs (cs_comp id__c id__e g i o) (beh s) ->
        InCs (cs_comp id__c id__e' g' i' o') (beh s) ->
        cs_comp id__c id__e g i o = cs_comp id__c id__e' g' i' o'.
  Proof.
    intros *; intros e; minv e.
    eapply get_comp_aux_uniq_comp; eauto.
  Qed.
  
End GetCompFacts.

#[export] Hint Resolve get_comp_aux_InCs get_comp_aux_not_InCs : get_comp.
#[export] Hint Resolve get_comp_aux_not_In_cids : get_comp.
#[export] Hint Resolve get_comp_uniq_comp : get_comp.

(** ** Facts about [put_comp] *)

Section PutCompFacts.

  Lemma put_comp_aux_InCs :
    forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o}
           {s : Sitpn2HVhdlState sitpn} {v s'},
      put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
      InCs (cs_comp id__c id__e g i o) v.
  Proof.
    induction cstmt.
    intros *; cbn; intros e; monadInv e; simpl; right; reflexivity.
    intros *; cbn; intros e; destruct (id__c0 =? id__c)%nat; monadInv e;
      [ constructor | simpl; right; reflexivity ].
    intros *; cbn; intros e; monadInv e;
      destruct x; monadInv EQ0; simpl; [ left | right ]; eauto.
    intros *; cbn; intros e; monadInv e; simpl; right; reflexivity.
  Qed.


    
  Lemma put_comp_aux_InCs_inv :
    forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o}
           {s : Sitpn2HVhdlState sitpn} {v s'},
      put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
      forall id__c' id__e' g' i' o',
        id__c' <> id__c ->
        InCs (cs_comp id__c' id__e' g' i' o') cstmt ->
        InCs (cs_comp id__c' id__e' g' i' o') v.
  Proof. induction cstmt; intros *; simpl; try (solve [inversion 3]).
         - case_eq (id__c0 =? id__c)%nat; intros e EQ; monadInv EQ.
           + inversion 2; subst; rewrite Nat.eqb_eq in e; congruence.
           + inversion_clear 2; do 2 constructor.
         - intros EQ; monadInv EQ.
           destruct x;
             monadInv EQ1; intros *; intros neq_idc; destruct 1; simpl;
             [ left | right | left | right ]; eauto.
  Qed.
  
  Lemma put_comp_aux_comp_ex :
    forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o}
           {s : Sitpn2HVhdlState sitpn} {v s'},
      put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
      (exists g0 i0 o0, InCs (cs_comp id__c id__e g0 i0 o0) cstmt) ->
      (exists g1 i1 o1, InCs (cs_comp id__c id__e g1 i1 o1) v).
  Proof.
    induction cstmt; intros *; cbn; intros e.
    1,4: (monadInv e; simpl; destruct 1 as [ g0 [ i0 [ o0 eq_comp ] ] ]; inversion eq_comp).
    destruct (id__c0 =? id__c)%nat; destruct 1 as [ g1 [ i1 [ o1 eq_comp ] ] ]; inversion eq_comp; subst;
      monadInv e; do 3 eexists; [econstructor | cbn; left; econstructor].
    monadInv e.
    destruct x;
      monadInv EQ0; intros *; destruct 1 as [ g0 [ i0 [ o0 [ InCs1 | InCs2 ] ] ] ].
    edestruct IHcstmt1 as [ g1 [ i1 [ o1 InCsx ] ] ]; eauto; simpl; do 3 eexists; eauto.
    simpl; do 3 eexists; eauto.
    simpl; do 3 eexists; eauto.
    edestruct IHcstmt2 as [ g1 [ i1 [ o1 InCsx ] ] ]; eauto; simpl; do 3 eexists; eauto.
  Qed.
  
  Lemma put_comp_aux_pci_ex :
    forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o}
           {s : Sitpn2HVhdlState sitpn} {v s' p},
      put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
      NoDup (get_cids cstmt) ->
      (exists g' i' o', InCs (cs_comp id__c id__e g' i' o') cstmt) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pci (γ s))
          /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) cstmt) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pci (γ s'))
          /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) v).
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
      assert (eq_ide_plid : id__e = Petri.place_id).
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
          InA Pkeq (p, id__p) (p2pci (γ s))
          /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) (beh s)) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pci (γ s'))
          /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) (beh s')).
  Proof. intros *; intros e; monadFullInv e; cbn.
         eapply put_comp_aux_pci_ex; eauto.  
  Qed.

  Lemma put_comp_aux_cid_In_cstmt:
    forall (cstmt : cs) (sitpn : Sitpn) (id__c id__e : ident)
           (g : genmap) (i : inputmap)
           (o : outputmap) (s' s : Sitpn2HVhdlState sitpn) (x : cs),
      put_comp_aux sitpn id__c id__e g i o cstmt s = OK x s' ->
      forall id__c' : ident, In id__c' (get_cids x) -> id__c <> id__c' -> In id__c' (get_cids cstmt).
  Proof.
    induction cstmt.
    1, 4: (intros *; intros e; monadInv e; cbn; intros id__c' [ eq_ | ] neq_; congruence).
    (* comp *)
    intros *; intros e; cbn in e; destruct (id__c0 =? id__c)%nat eqn: eq_idc.
    monadInv e; cbn; intros id__c' [ eq_idc0 | ] neq_; auto.
    monadInv e; cbn; intros id__c' [ eq_cc' | [ eq_c0c' | ] ] neq_; auto.
    (* par *)
    intros *; intros e; monadInv e.
    destruct x0; monadInv EQ0; do 2 (rewrite get_cids_app);
      intros; edestruct in_app_or; eauto.
  Qed.
  
  Lemma put_comp_aux_nodup_cids :
    forall (cstmt : cs) (sitpn : Sitpn) (id__c id__e : ident) (g : genmap) (i : inputmap) (o : outputmap)
           (s : Sitpn2HVhdlState sitpn) (v : cs) (s' : Sitpn2HVhdlState sitpn),
      put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
      NoDup (get_cids cstmt) -> NoDup (get_cids v).
  Proof.
    induction cstmt; intros *; intros e; cbn in e.
    (* process and null *) 
    1, 4: (monadInv e; cbn; eauto ).
    - (* comp *)
      case_eq (id__c0 =? id__c)%nat; intros eqb; rewrite eqb in e; monadInv e.
      erewrite Nat.eqb_eq in eqb; eauto.
      rewrite eqb; cbn; eauto.
      cbn; constructor; eauto; edestruct 1; eauto.
      intros; eapply beq_nat_false; eauto.
    - (* par *)
      monadInv e; destruct x;
        monadInv EQ0; do 2 rewrite get_cids_app;
        intro; eapply NoDup_app_cons; eauto with nodup;
        intros id__c'; [ intros Inx In2 | intros In1 Inx ];
        destruct (Nat.eq_dec id__c id__c'); [ subst | | subst | ].
      (* CASE [id__c <> id__c'] *)
      2, 4: (eapply nodup_app_not_in; eauto with nodup;
             eapply put_comp_aux_cid_In_cstmt; eauto).
      + (* CASE [id__c = id__c'] *)
        eapply nodup_app_not_in; eauto with nodup.
        destruct p as (((id__e1, g1), i1), o1).
        eapply get_cids_InCs; eapply get_comp_aux_InCs; eauto.
      + (* CASE [id__c = id__c'] *)
        eapply get_comp_aux_not_In_cids; eauto.
  Qed.
  
  Lemma put_comp_nodup_cids :
    forall {sitpn : Sitpn} {id__c id__e} {g i o}
           {s : Sitpn2HVhdlState sitpn} {v s'},
      put_comp id__c id__e g i o s = OK v s' ->
      NoDup (get_cids (beh s)) ->
      NoDup (get_cids (beh s')).
  Proof. intros *; intros e; monadFullInv e; simpl.
         eapply put_comp_aux_nodup_cids; eauto.
  Qed.
  
End PutCompFacts.

#[export]
Hint Resolve put_comp_aux_comp_ex put_comp_aux_pci_ex
 put_comp_pci_ex : put_comp.

#[export]
Hint Resolve put_comp_aux_InCs put_comp_aux_InCs_inv : put_comp.

#[export]
Hint Resolve put_comp_aux_nodup_cids put_comp_nodup_cids
 : put_comp.
