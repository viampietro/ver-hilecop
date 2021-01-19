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
Require Import common.SetoidListFacts.

Require Import sitpn.dp.Sitpn.
Require Import sitpn.dp.SitpnFacts.
Require Import sitpn.dp.SitpnWellDefined.
Require Import sitpn.dp.SitpnWellDefinedTactics.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.

Require Import sitpn2hvhdl.Sitpn2HVhdl.

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
      proj1_sig y <> proj1_sig x ->
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

  Lemma titer_gen_p_comp_inst_p_comp :
    forall {sitpn pls} {Inpls2P : forall n : nat, List.In n pls -> P sitpn} {s v s'},
      titer (generate_place_comp_inst sitpn) pls Inpls2P s = OK v s' ->
      List.NoDup pls ->
      (forall x y pfx pfy, x = y <-> proj1_sig (Inpls2P x pfx) = proj1_sig (Inpls2P y pfy)) ->
      forall n (Innpls : List.In n pls),
      exists id__p gm ipm opm,
        InA Pkeq ((Inpls2P n Innpls), id__p) (p2pcomp (γ s')) /\
        InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').      
  Proof.
    intros until Inpls2P; functional induction (titer (generate_place_comp_inst sitpn) pls Inpls2P) using titer_ind.

    (* BASE CASE *)
    - contradiction.

    (* IND. CASE *)
    - intros;
        lazymatch goal with
        | [ Hm : (do _ <- _; _) _ = _ |- _ ] =>
          inversion_clear Innpls as [ e_an | HIn_ntl ]; monadInv Hm
        end.

      (* CASE a = n *)
      + specialize (gen_p_comp_inst_p_comp EQ0) as (id__p, (gm, (ipm, (opm, (Hin_γs', Hin_behs'))))).
        exists id__p, gm, ipm, opm; split; [ | auto].
        eapply InA_eqk; eauto.
        unfold Peq; unfold seq; rewrite ((proj1 (H1 a n (in_eq a tl) Innpls)) e_an).
        reflexivity.

      (* CASE n ∈ tl *)
      + assert (e_pf : forall x y pfx pfy,
                   x = y <->
                   proj1_sig (in_T_in_sublist_T a tl pf x pfx) = proj1_sig (in_T_in_sublist_T a tl pf y pfy))
          by (intros; apply H1; assumption).
        lazymatch goal with
        | [ H: List.NoDup _ |- _ ] => inversion_clear H as [ | e1 e2 Hnotin_a_tl Hnodup_tl ]
        end.
        specialize (IHm s x s0 EQ Hnodup_tl e_pf n HIn_ntl) as (id__p, (gm, (ipm, (opm, (Hγ, Hincs_comp))))).
        unfold in_T_in_sublist_T in Hγ.

        (* Apply gen_p_comp_inst_inv_p_comp *)
        assert (ne_an : a <> n) by (apply (not_in_in_diff (conj Hnotin_a_tl HIn_ntl))).
        assert (ne_proj1 : proj1_sig (pf a (in_eq a tl)) <> proj1_sig (pf n (in_cons a n tl HIn_ntl)))
          by (intros e_proj1; rewrite <- ((proj2 (H1 a n (in_eq a tl) (in_cons a n tl HIn_ntl))) e_proj1) in ne_an;
              contradiction).
        specialize (gen_p_comp_inst_inv_p_comp EQ0 ne_proj1 Hγ Hincs_comp) as (Hγ', Hincs_comp').
        exists id__p, gm, ipm, opm; split; [ | auto].
        specialize ((proj1 (H1 n n (in_cons a n tl HIn_ntl) Innpls)) eq_refl) as e_proj1.
        eapply InA_eqk; eauto.
  Qed.

  Lemma gen_p_comp_insts_p_comp :
    forall {sitpn s v s'},
      generate_place_comp_insts sitpn s = OK v s' ->
      List.NoDup (places sitpn) ->
      forall p, exists id__p gm ipm opm,
          InA Pkeq (p, id__p) (p2pcomp (γ s')) /\
          InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until s'; intros e; unfold generate_place_comp_insts in e; intros Hnodup p.
    assert (nat_to_P_determ :
              forall x y (pfx : In_P sitpn x) (pfy : In_P sitpn y),
                x = y <-> proj1_sig (nat_to_P x pfx) = proj1_sig (nat_to_P y pfy))
      by (intros; simpl; reflexivity).
    rewrite <- (eq_sig (nat_to_P (proj1_sig p) (proj2_sig p)) p eq_refl eq_refl).
    apply (titer_gen_p_comp_inst_p_comp e Hnodup nat_to_P_determ (proj1_sig p) (proj2_sig p)).  
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

  Lemma titer_gen_p_comp_inst_inv_nodup_p2pcomp :
    forall {sitpn pls} {Inpls2P : forall n : nat, List.In n pls -> P sitpn} {s v s'},
      titer (generate_place_comp_inst sitpn) pls Inpls2P s = OK v s' ->
      (forall x pfx, x = proj1_sig (Inpls2P x pfx)) ->
      forall p,
        ~InA Peq p (fs (p2pcomp (γ s))) ->
        ~List.In (proj1_sig p) pls ->
        ~InA Peq p (fs (p2pcomp (γ s'))).
  Proof.
    intros until Inpls2P;
      functional induction (titer (generate_place_comp_inst sitpn) pls Inpls2P) using titer_ind;
      intros s v s' e; monadInv e; auto; intros.
    eapply gen_p_comp_inst_inv_p2pcomp; eauto.
    unfold Peq; unfold seq.
    lazymatch goal with
    | [ e1: forall _ _, _ = proj1_sig _, H: ~List.In _ (_ :: _) |- _ ] =>
      rewrite <- (e1 a (in_eq a tl));
        rewrite not_in_cons in H1; apply proj1 in H1; auto
    end.
  Qed.

  Lemma titer_gen_p_comp_inst_nodup_p2pcomp :
    forall {sitpn pls} {Inpls2P : forall n : nat, List.In n pls -> P sitpn} {s v s'},
      titer (generate_place_comp_inst sitpn) pls Inpls2P s = OK v s' ->
      List.NoDup pls ->
      (forall n (Innpls : List.In n pls), ~InA Peq (Inpls2P n Innpls) (fs (p2pcomp (γ s)))) ->
      (forall x pfx, x = proj1_sig (Inpls2P x pfx)) ->
      NoDupA Peq (fs (p2pcomp (γ s))) ->
      NoDupA Peq (fs (p2pcomp (γ s'))).
  Proof.
    intros until Inpls2P;
      functional induction (titer (generate_place_comp_inst sitpn) pls Inpls2P) using titer_ind;
      intros s v s' e; monadInv e; auto; intros.
    
    eapply gen_p_comp_inst_nodup_p2pcomp; eauto;
      lazymatch goal with
      | [ H: forall _ _, _ = proj1_sig _, Hnd: List.NoDup (_ :: _) |- _ ] =>
        (eapply titer_gen_p_comp_inst_inv_nodup_p2pcomp; eauto;
         rewrite <- (H a (in_eq a tl));
         apply (proj1 (proj1 (NoDup_cons_iff a tl) Hnd)))
        || (eapply IHm; eauto; apply (proj2 (proj1 (NoDup_cons_iff a tl) Hnd)))
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

  Lemma titer_gen_t_comp_inst_inv_p2pcomp :
    forall {sitpn trs} {Intrs2T : forall n : nat, List.In n trs -> T sitpn} {s v s'},
      titer (generate_trans_comp_inst sitpn) trs Intrs2T s = OK v s' ->
      p2pcomp (γ s) = p2pcomp (γ s').
  Proof.
    intros until Intrs2T;
      functional induction (titer (generate_trans_comp_inst sitpn) trs Intrs2T) using titer_ind;
      intros s v s' e; monadInv e;
        [ auto |
          transitivity (p2pcomp (γ s0));
          [eapply IHm; eauto | eapply gen_t_comp_inst_inv_p2pcomp; eauto] ].
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

  Lemma titer_gen_t_comp_inst_inv_in_beh :
    forall {sitpn trs} {Intrs2T : forall n : nat, List.In n trs -> T sitpn} {s v s'},
      titer (generate_trans_comp_inst sitpn) trs Intrs2T s = OK v s' ->
      forall cstmt, InCs cstmt (beh s) -> InCs cstmt (beh s').
  Proof.
    intros until Intrs2T;
      functional induction (titer (generate_trans_comp_inst sitpn) trs Intrs2T) using titer_ind;
      intros s v s' e; monadInv e;
        [auto
        | intros cstmt Hincs;
          specialize (IHm s x s0 EQ cstmt Hincs);
          eapply gen_t_comp_inst_inv_in_beh; eauto].
  Qed.

  Lemma gen_t_comp_insts_inv_p_comp :
    forall {sitpn s v s' p id__p gm ipm opm},
      generate_trans_comp_insts sitpn s = OK v s' ->
      InA Pkeq (p, id__p) (p2pcomp (γ s)) ->
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s) ->
      InA Pkeq (p, id__p) (p2pcomp (γ s')) /\
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until opm; intros e; unfold generate_trans_comp_insts in e.
    split;
      [rewrite <- (titer_gen_t_comp_inst_inv_p2pcomp e); assumption |
       eapply titer_gen_t_comp_inst_inv_in_beh; eauto].
  Qed.

End GenerateTransCompInst.

(** ** Facts about SITPN-to-H-VHDL Transformation Function *)

Section Sitpn2HVhdl.
  
  Lemma gen_comp_insts_p_comp :
    forall {sitpn s v s'},
      generate_comp_insts sitpn s = OK v s' ->
      List.NoDup (places sitpn) ->
      forall p, exists id__p gm ipm opm,
          InA Pkeq (p, id__p) (p2pcomp (γ s')) /\
          InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
  Proof.
    intros until s'; intros e; monadInv e; intros Hnodup p.
    specialize (gen_p_comp_insts_p_comp EQ Hnodup p)
      as (id__p, (gm, (ipm, (opm, (Hin_γs0, Hin_behs0))))).
    exists id__p, gm, ipm, opm.
    eapply gen_t_comp_insts_inv_p_comp; eauto.
  Qed.

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
      specialize (gen_comp_insts_p_comp EQ2 NoDupPlaces p)
        as (id__p, (gm, (ipm, (opm, (Hin_γs2, Hin_behs2)))));
        exists id__p, gm, ipm, opm;
        monadFullInv EQ4; inversion H; subst; simpl; auto
    end.
  Qed.

  Lemma gen_comp_insts_nodup_p2pcomp :
    forall {sitpn : Sitpn} {s : Sitpn2HVhdlState sitpn} {v : unit} {s' : Sitpn2HVhdlState sitpn},
      generate_comp_insts sitpn s = OK v s' ->
      List.NoDup (places sitpn) ->
      (forall n (n2P : In_P sitpn n), ~InA Peq (exist _ n n2P) (fs (p2pcomp (γ s)))) ->
      NoDupA Peq (fs (p2pcomp (γ s))) ->
      NoDupA Peq (fs (p2pcomp (γ s'))).
  Proof.
    intros until s'; intros e; monadInv e; intros.
    rewrite <- (titer_gen_t_comp_inst_inv_p2pcomp EQ0).
    eapply titer_gen_p_comp_inst_nodup_p2pcomp; eauto.
  Qed.

  
End Sitpn2HVhdl.
