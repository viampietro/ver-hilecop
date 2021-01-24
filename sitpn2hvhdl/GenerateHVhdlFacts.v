(** * Facts about the H-VHDL Generating Functions *)

Require Import common.Coqlib.
Require Import common.GlobalFacts.
Require Import common.FstSplit.
Require Import common.InAndNoDup.
Require Import common.ListDep.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListMonad.
Require Import common.ListMonadFacts.
Require Import common.ListMonadTactics.
Require Import common.SetoidListFacts.
Require Import common.ListPlus.

Require Import sitpn.dp.Sitpn.
Require Import sitpn.dp.SitpnFacts.
Require Import sitpn.dp.SitpnWellDefined.
Require Import sitpn.dp.SitpnWellDefinedTactics.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.

Require Import sitpn2hvhdl.Sitpn2HVhdl.
Require Import sitpn2hvhdl.GenerateInfosFacts.

(** ** Facts about [InputMap_to_AST] Function *)

Section InputMap2AST.

  Lemma imap_entry_to_associp_inv_state :
    forall {sitpn im ime s v s'},
      imap_entry_to_associp sitpn im ime s = OK v s' ->
      s = s'.
  Proof.
    unfold imap_entry_to_associp.
    destruct ime; destruct s; intros s v s' e1; monadFullInv e1;
      [ auto | destruct l; monadFullInv EQ; auto ].
  Qed.
  
End InputMap2AST.

(** ** Facts about [OutputMap_to_AST] Function *)

Section OutputMap2AST.

  Lemma omap_entry_to_assocop_inv_state :
    forall {sitpn om ome s v s'},
      omap_entry_to_assocop sitpn om ome s = OK v s' ->
      s = s'.
  Proof.
    unfold omap_entry_to_assocop.
    destruct ome; destruct s; intros s v s' e1; monadFullInv e1;
      [ auto | destruct l; monadFullInv EQ; auto ].
  Qed.

End OutputMap2AST.

(** ** Facts about [HComponent_to_comp_inst] Function *)

Section HComp2CompInst.

  Lemma HComp_to_comp_inst_inv_state :
    forall {sitpn id__c id__e hcomp s v s'},
      HComponent_to_comp_inst sitpn id__c id__e hcomp s = OK v s' ->
      s = s'.
  Proof.
    intros until s'; intros e; destruct hcomp as ((gm, ipm), opm).
    monadFullInv e.
    unfold InputMap_to_AST in EQ; unfold OutputMap_to_AST in EQ1.
    transitivity s0.
    eapply foldl_inv_state; eauto with typeclass_instances; intros; eapply imap_entry_to_associp_inv_state; eauto.
    eapply foldl_inv_state; eauto with typeclass_instances; intros; eapply omap_entry_to_assocop_inv_state; eauto.
  Qed.

  Lemma HComp_to_comp_inst_p_comp :
    forall {sitpn id__c id__e hcomp s v s'},
      HComponent_to_comp_inst sitpn id__c id__e hcomp s = OK v s' ->
      exists gm ipm opm,
        v = cs_comp id__c id__e gm ipm opm.
  Proof.
    intros until s'; intros e; destruct hcomp as ((gm, ipm), opm).
    monadFullInv e.
    exists gm, x, x0; reflexivity.
  Qed.

  
End HComp2CompInst.

(** ** Facts about Generation of P Component Instances *)

Section GeneratePlaceCompInst.

  (** *** P Component Generation *)
  
  Lemma gen_p_comp_inst_inv_p_comp :
    forall {sitpn x y s v s' id__p gm ipm opm},
      generate_place_comp_inst sitpn y s = OK v s' ->
      ~Peq x y ->
      InA Pkeq (x, id__p) (p2pcomp (γ s)) ->
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s) ->
      InA Pkeq (x, id__p) (p2pcomp (γ s')) /\
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until opm; intros e; intros; split;
      monadFullInv e; simpl; simpl in EQ4;
        specialize (getv_inv_state EQ4) as e1;
        specialize (HComp_to_comp_inst_inv_state EQ2) as e2;
        rewrite <- e2, <- e1; clear e1 e2; simpl;
          [ apply InA_setv_inv; auto | right; assumption ].
  Qed.

  Lemma gen_p_comp_inst_p_comp :
    forall {sitpn p s v s'},
      generate_place_comp_inst sitpn p s = OK v s' ->
      exists (id__p : ident) (gm : genmap) (ipm : inputmap) (opm : outputmap),
        InA Pkeq (p, id__p) (p2pcomp (γ s')) /\ InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until s'; intros e; monadFullInv e.
    simpl; simpl in EQ4.
    specialize (HComp_to_comp_inst_p_comp EQ2) as (gm, (ipm, (opm, e1))); rewrite e1.
    exists (nextid s0), gm, ipm, opm; simpl.
    specialize (getv_inv_state EQ4) as e2; subst s2.
    specialize (HComp_to_comp_inst_inv_state EQ2) as e2; subst s4.
    split; [ apply InA_setv; auto | auto].
  Qed.
  
  Lemma iter_gen_p_comp_inst_p_comp :
    forall {sitpn pls} {s v s'},
      iter (generate_place_comp_inst sitpn) pls s = OK v s' ->
      NoDupA Peq pls ->
      forall p, InA Peq p pls ->
        exists id__p gm ipm opm,
          InA Pkeq (p, id__p) (p2pcomp (γ s')) /\
          InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until pls; functional induction (iter (generate_place_comp_inst sitpn) pls) using iter_ind.

    (* BASE CASE *)
    - inversion 3.

    (* IND. CASE *)
    - intros;
        lazymatch goal with
        | [ Hm : (do _ <- _; _) _ = _, Hin: InA _ _ (_ :: _) |- _ ] =>
          inversion_clear Hin as [ e1 e2 Peq_pb | e1 e2 HIn_ntl ]; monadInv Hm
        end.

      (* CASE a = n *)
      + specialize (gen_p_comp_inst_p_comp EQ0) as (id__p, (gm, (ipm, (opm, (Hin_γs', Hin_behs'))))).
        exists id__p, gm, ipm, opm; split; [ | auto].
        eapply InA_eqk; eauto; symmetry; assumption.        

      (* CASE n ∈ tl *)
      + lazymatch goal with
        | [ H: NoDupA _ _ |- _ ] => inversion_clear H as [ | e1 e2 Hnotin_a_tl Hnodup_tl ]
        end.
        specialize (IHm s x s0 EQ Hnodup_tl p HIn_ntl) as (id__p, (gm, (ipm, (opm, (Hγ, Hincs_comp))))).

        (* Apply gen_p_comp_inst_inv_p_comp *)
        assert (nPeq : ~Peq p b) by (eapply InA_neqA; eauto).
        specialize (gen_p_comp_inst_inv_p_comp EQ0 nPeq Hγ Hincs_comp) as (Hγ', Hincs_comp').
        exists id__p, gm, ipm, opm; auto.
  Qed.
  
  Lemma gen_p_comp_insts_p_comp :
    forall {sitpn s v s'},
      generate_place_comp_insts sitpn s = OK v s' ->
      Sig_in_List (lofPs s) ->
      forall p, exists id__p gm ipm opm,
          InA Pkeq (p, id__p) (p2pcomp (γ s')) /\
          InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until s'; intros e; minv e; intros SIL p.
    eapply iter_gen_p_comp_inst_p_comp; eauto;
      [ apply (proj2 SIL) | apply ((proj1 SIL) p)].
  Qed.

  (** *** NoDup in p2pcomp *)
  
  Lemma gen_p_comp_inst_nodup_p2pcomp :
    forall {sitpn p s v s'},
      generate_place_comp_inst sitpn p s = OK v s' ->
      ~InA Peq p (fs (p2pcomp (γ s))) ->
      NoDupA Peq (fs (p2pcomp (γ s))) ->
      NoDupA Peq (fs (p2pcomp (γ s'))).
  Proof.
    intros until s'; intros e; monadFullInv e;
      simpl; simpl in EQ4;
        specialize (getv_inv_state EQ4) as e1;
        specialize (HComp_to_comp_inst_inv_state EQ2) as e2;
        rewrite <- e2, <- e1; clear e1 e2; simpl.
    apply NoDupA_setv_cons; auto.
  Qed.

  Lemma gen_p_comp_inst_inv_p2pcomp :
    forall {sitpn x y s v s'},
      generate_place_comp_inst sitpn y s = OK v s' ->
      ~Peq y x ->
      ~InA Peq x (fs (p2pcomp (γ s))) ->
      ~InA Peq x (fs (p2pcomp (γ s'))).
  Proof.
    intros until s'; intros e; intros;
      monadFullInv e; simpl; simpl in EQ4;
        specialize (getv_inv_state EQ4) as e1;
        specialize (HComp_to_comp_inst_inv_state EQ2) as e2;
        rewrite <- e2, <- e1; clear e1 e2; simpl; auto with setoidl.
  Qed.

  Lemma iter_gen_pcomp_inst_inv_nodup_p2pcomp :
    forall {sitpn pls} {s v s'},
      iter (generate_place_comp_inst sitpn) pls s = OK v s' ->
      forall p,
        ~InA Peq p (fs (p2pcomp (γ s))) ->
        ~InA Peq p pls ->
        ~InA Peq p (fs (p2pcomp (γ s'))).
  Proof.
    intros until pls;
      functional induction (iter (generate_place_comp_inst sitpn) pls) using iter_ind;
      intros s v s' e; monadInv e; auto; intros.
    eapply gen_p_comp_inst_inv_p2pcomp; eauto with setoidl.
    intro; apply H0; symmetry in H1; auto.
  Qed.

  Lemma iter_gen_pcomp_inst_nodup_p2pcomp :
    forall {sitpn pls s v s'},
      iter (generate_place_comp_inst sitpn) pls s = OK v s' ->
      NoDupA Peq pls ->
      (forall p, InA Peq p pls -> ~InA Peq p (fs (p2pcomp (γ s)))) ->
      NoDupA Peq (fs (p2pcomp (γ s))) ->
      NoDupA Peq (fs (p2pcomp (γ s'))).
  Proof.
    intros until pls;
      functional induction (iter (generate_place_comp_inst sitpn) pls) using iter_ind;
      intros s v s' e; monadInv e; auto; intros.
    
    eapply gen_p_comp_inst_nodup_p2pcomp; eauto;
      lazymatch goal with
      | [ Hnd: NoDupA _ (?a :: ?tl), Hnin: forall _, _ -> ~_ |- _ ] =>
        (eapply iter_gen_pcomp_inst_inv_nodup_p2pcomp; eauto; [
           apply Hnin; apply InA_cons_hd; reflexivity
         | inversion Hnd; assumption])
        || (eapply IHm; eauto; inversion Hnd; assumption)
      end.
  Qed.
    
End GeneratePlaceCompInst.

(** ** Facts about Generation of T Component Instances *)

Section GenerateTransCompInst.

  Lemma gen_t_comp_inst_inv_p2pcomp :
    forall {sitpn t s v s'},
      generate_trans_comp_inst sitpn t s = OK v s' ->
      p2pcomp (γ s) = p2pcomp (γ s').
  Proof.
    intros until s'; intros e; monadFullInv e; simpl; simpl in EQ3.
    specialize (getv_inv_state EQ3) as e1;
      specialize (HComp_to_comp_inst_inv_state EQ0) as e2;
      rewrite <- e2, <- e1; clear e1 e2; simpl; reflexivity.
  Qed.
  
  Lemma iter_gen_tcomp_inst_inv_p2pcomp :
    forall {sitpn trs s v s'},
      iter (generate_trans_comp_inst sitpn) trs s = OK v s' ->
      p2pcomp (γ s) = p2pcomp (γ s').
  Proof.
    intros until s'; intros e; solveSInv e.
    intros; eapply gen_t_comp_inst_inv_p2pcomp; eauto.
  Qed.
  
  Lemma gen_t_comp_inst_inv_in_beh :
    forall {sitpn t s v s'},
      generate_trans_comp_inst sitpn t s = OK v s' ->
      forall cstmt,
        InCs cstmt (beh s) -> InCs cstmt (beh s').
  Proof.
    intros until s'; intros e; monadFullInv e; simpl; simpl in EQ3.
    specialize (getv_inv_state EQ3) as e1;
      specialize (HComp_to_comp_inst_inv_state EQ0) as e2;
      rewrite <- e2, <- e1; clear e1 e2; simpl.
    intros; right; assumption.
  Qed.

  Lemma iter_gen_tcomp_inst_inv_in_beh :
    forall {sitpn trs s v s'},
      iter (generate_trans_comp_inst sitpn) trs s = OK v s' ->
      forall cstmt, InCs cstmt (beh s) -> InCs cstmt (beh s').
  Proof.
    intros until s'; intros e; solveSInv e.
    intros; eapply gen_t_comp_inst_inv_in_beh; eauto.
  Qed.
  
  Lemma gen_t_comp_insts_inv_p_comp :
    forall {sitpn s v s' p id__p gm ipm opm},
      generate_trans_comp_insts sitpn s = OK v s' ->
      InA Pkeq (p, id__p) (p2pcomp (γ s)) ->
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s) ->
      InA Pkeq (p, id__p) (p2pcomp (γ s')) /\
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until opm; intros e; monadFullInv e.
    split;
      [rewrite <- (iter_gen_tcomp_inst_inv_p2pcomp EQ0); assumption |
       eapply iter_gen_tcomp_inst_inv_in_beh; eauto].
  Qed.

End GenerateTransCompInst.

(** ** Facts about SITPN-to-H-VHDL Transformation Function *)

Section Sitpn2HVhdl.
  
  Lemma gen_comp_insts_p_comp :
    forall {sitpn s v s'},
      generate_comp_insts sitpn s = OK v s' ->
      Sig_in_List (lofPs s) ->
      forall p, exists id__p gm ipm opm,
          InA Pkeq (p, id__p) (p2pcomp (γ s')) /\
          InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until s'; intros e; monadInv e; intros Hsil p.
    specialize (gen_p_comp_insts_p_comp EQ Hsil p)
      as (id__p, (gm, (ipm, (opm, (Hin_γs0, Hin_behs0))))).
    exists id__p, gm, ipm, opm.
    eapply gen_t_comp_insts_inv_p_comp; eauto.
  Qed.

  Lemma gen_arch_inv_lofPs :
    forall {sitpn mm} {s : Sitpn2HVhdlState sitpn} {v s'},
      generate_architecture mm s = OK v s' ->
      Sig_in_List (lofPs s) ->
      Sig_in_List (lofPs s').
  Proof.
    
  Admitted.

  Lemma gen_ports_inv_lofPs :
    forall {sitpn} {s : Sitpn2HVhdlState sitpn} {v s'},
      generate_ports s = OK v s' ->
      Sig_in_List (lofPs s) ->
      Sig_in_List (lofPs s').
  Admitted.
  
  Lemma sitpn2hvhdl_p_comp :
    forall {sitpn decpr id__ent id__arch mm d γ},
      (* [sitpn] translates into [(d, γ)]. *)
      sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
      IsWellDefined sitpn ->
      forall p, exists id__p gm ipm opm,
          InA Pkeq (p, id__p) (p2pcomp γ) /\
          InCs (cs_comp id__p Petri.place_entid gm ipm opm) (behavior d).
  Proof.
    intros. 
    functional induction (sitpn_to_hvhdl sitpn decpr id__ent id__arch mm) using sitpn_to_hvhdl_ind.
    
    (* Error *)
    lazymatch goal with
    | [ H: inr _ = inl _ |- _ ] => inversion H
    end.

    (* OK *)
    monadInv e.
    lazymatch goal with
    | [ H: inl _ = inl _, Hwd: IsWellDefined _ |- _ ] =>
      let NoDupPlaces := (get_nodup_places Hwd) in
      let sil_lofPs_s := constr:(gen_sitpn_infos_sil_lofPs EQ NoDupPlaces) in
      let sil_lofPs_s0 := constr:(gen_arch_inv_lofPs EQ1 sil_lofPs_s) in
      let sil_lofPs_s1 := constr:(gen_ports_inv_lofPs EQ0 sil_lofPs_s0) in
      specialize (gen_comp_insts_p_comp EQ2 sil_lofPs_s1 p)
        as (id__p, (gm, (ipm, (opm, (Hin_γs2, Hin_behs2)))));
        exists id__p, gm, ipm, opm;
        monadFullInv EQ4; inversion H; subst; simpl; auto
    end.
  Qed.

  Lemma gen_comp_insts_nodup_p2pcomp :
    forall {sitpn : Sitpn} {s : Sitpn2HVhdlState sitpn} {v : unit} {s' : Sitpn2HVhdlState sitpn},
      generate_comp_insts sitpn s = OK v s' ->
      List.NoDup (places sitpn) ->
      (forall p, ~InA Peq p (fs (p2pcomp (γ s)))) ->
      NoDupA Peq (fs (p2pcomp (γ s))) ->
      NoDupA Peq (fs (p2pcomp (γ s'))).
  Proof.
    intros until s'; intros e; monadInv e; intros.
    minv EQ0; rewrite <- (iter_gen_tcomp_inst_inv_p2pcomp EQ2).
    eapply @iter_gen_pcomp_inst_nodup_p2pcomp with (v := x); eauto.
  Qed.

  
End Sitpn2HVhdl.
