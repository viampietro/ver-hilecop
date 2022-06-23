(** * Facts about Architecture Generation *)

Require Import common.CoqLib.
Require Import common.GlobalFacts.
Require Import common.StateAndErrorMonad.
Require Import common.ListLib.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import common.proofs.ListMonadFacts.
Require Import common.proofs.SetoidListFacts.
Require Import common.proofs.ListPlusFacts.

Require Import sitpn.SitpnLib.
Require Import sitpn.SitpnFacts.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.proofs.AbstractSyntaxFacts.

Require Import transformation.Sitpn2HVhdl.
Require Import transformation.Sitpn2HVhdlUtils.
Require Import transformation.proofs.SInvTactics.

(** ** Facts about the generation of PDIs *)

Section GenPDIsFacts.

  (** *** Facts about the [build_pdi] function *)
  
  Lemma build_pdi_inv_beh :
    forall {sitpn} {p : P sitpn} {pinfo n s v s'},
      build_pdi p pinfo n s = OK v s' ->
      beh s = beh s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma build_pdi_inv_γ :
    forall {sitpn} {p : P sitpn} {pinfo n s v s'},
      build_pdi p pinfo n s = OK v s' ->
      γ s = γ s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma build_pdi_inv_inc_nextid :
    forall {sitpn} {p : P sitpn} {pinfo n s v s'},
      build_pdi p pinfo n s = OK v s' ->
      nextid s <= nextid s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern.
         all: try (unfold Transitive; intros; lia).
         cbn; minv EQ5; auto.
  Qed.
  
  (** *** Facts about the [generate_pdi] function *)

  Lemma pdi_ex_Peq_equiv :
    forall sitpn (x y : P sitpn) s,
      Peq x y ->
      ((exists id__p g__p i__p o__p,
           InA Pkeq (x, id__p) (p2pdi (γ s))
           /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) (beh s))
       <-> (exists id__p g__p i__p o__p,
               InA Pkeq (y, id__p) (p2pdi (γ s))
               /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) (beh s))).
  Proof.
    intros; split;
      (edestruct 1 as (id__p, (g__p, (i__p, (o__p, (InA_a, InCs_)))));
       exists id__p, g__p, i__p, o__p; split; [ eauto with setoidl | assumption ]).
  Qed.
  
  Lemma gen_pdi_pdi_ex :
    forall sitpn (n : nat) (a : P sitpn) (s1 : Sitpn2HVhdlState sitpn)
           (x : unit) (s2 : Sitpn2HVhdlState sitpn),
      generate_pdi a n s1 = OK x s2 ->
      exists id__p g__p i__p o__p,
        InA Pkeq (a, id__p) (p2pdi (γ s2)) /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) (beh s2).
  Proof.
    intros *; intros e; minv e.
    all: do 4 eexists; split; [ eauto with setoidl | left; eauto ].
  Qed.  

  Lemma gen_pdi_pdi_ex_inv :
    forall sitpn (n : nat) (a : P sitpn) (s1 : Sitpn2HVhdlState sitpn) (x : unit) (s2 : Sitpn2HVhdlState sitpn),
      generate_pdi a n s1 = OK x s2 ->
      forall b,
        (exists id__p g__p i__p o__p,
            InA Pkeq (b, id__p) (p2pdi (γ s1)) /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) (beh s1)) ->
        exists id__p g__p i__p o__p,
          InA Pkeq (b, id__p) (p2pdi (γ s2)) /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) (beh s2).
  Proof.
    intros *; intros e b; destruct (Peqdec a b) as [Peq_ab | nPeq_ab]. 

    (* CASE [Peq a b], implies [Q a s' <-> Q b s']. *)
    - rewrite <- (pdi_ex_Peq_equiv sitpn a b s1 Peq_ab).
      rewrite <- (pdi_ex_Peq_equiv sitpn a b s2 Peq_ab).
      intro; eapply gen_pdi_pdi_ex; eauto.
      
    (* CASE [~Peq a b], then nevermind the new entry [(a, id__p)] and new
     PDI in [(beh s2)]. *)
    - monadInv e; monadInv EQ; monadInv EQ2; monadInv EQ.
      rewrite (getv_inv_state EQ4); minv EQ1.
      match goal with
      | [ H: build_pdi _ _ _ ?s = _ |- _ ] => set (s1' := s) in H
      end.
      change (γ s1) with (γ s1'); change (beh s1) with (beh s1').
      rewrite (build_pdi_inv_beh EQ0); rewrite (build_pdi_inv_γ EQ0); minv EQ3.
      edestruct 1 as (id__p, (g__p, (i__p, (o__p, (InA_a, InCs_))))).
      exists id__p, g__p, i__p, o__p; split; [ eauto 1 with setoidl | right; assumption ].
  Qed.

  (** *** Facts about the [generate_pdis] function *)
  
  Lemma gen_pdis_pdi_ex :
    forall (sitpn : Sitpn) (b : P sitpn -> nat) (s : Sitpn2HVhdlState sitpn) v s' p,
      generate_pdis b s = OK v s' ->
      Sig_in_List (lofPs s) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pdi (γ s'))
          /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) (beh s')).
  Proof.
    intros *; intros e; minv e. intros SIL_lofPs.
    pattern p, s'.
    eapply iter_prop_A_state with (eqA := Peq); eauto.

    (* Proves that [Peq a b] implies [Q a s' <-> Q b s']. *)
    - eapply pdi_ex_Peq_equiv.
      
    (* Proves that [∀ a, f a s = OK v s' -> Q a s'] where [f] 
     is [generate_pdi] here. *)
    - cbn; intros x; eapply gen_pdi_pdi_ex.
      
    (* Proves that property [Q] is invariant. *)
    - simpl; intros x; eapply gen_pdi_pdi_ex_inv with (n := b x).

    (* Proves that *)
    - eapply SIL_forall_A; eauto.
  Qed.
  
End GenPDIsFacts.

(** ** Facts about the generation of TDIs *)

Section GenTDIsFacts.

  (** *** Facts about the [build_tdi] function *)
  
  Lemma build_tdi_inv_beh :
    forall {sitpn} {t : T sitpn} {tinfo s v s'},
      build_tdi t tinfo s = OK v s' ->
      beh s = beh s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma build_tdi_inv_inc_nextid :
    forall {sitpn} {t : T sitpn} {tinfo s v s'},
      build_tdi t tinfo s = OK v s' ->
      nextid s <= nextid s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern.
         match goal with
         | EQ: _ _ = OK _ _ |- _ =>
             cbn; minv EQ; auto
         end.
  Qed.
  
  (** *** Facts about the [generate_tdis] function *)

  Lemma gen_tdis_pdi_ex :
    forall (sitpn : Sitpn) (s : Sitpn2HVhdlState sitpn) v s' p,
      generate_tdis s = OK v s' ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pdi (γ s))
          /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) (beh s)) -> 
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pdi (γ s'))
          /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) (beh s')).
  Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern.
         match goal with
         | [ EQ: OK _ _ = OK _ _ |- _ ] =>
             inversion EQ; subst; cbn
         end;
         destruct 1 as [id__p [g__p [i__p [o__p [InA_ InCs_] ] ] ] ].
         exists id__p, g__p, i__p, o__p; split; [ assumption | (right; assumption) ].
  Qed.
  
End GenTDIsFacts.

(** ** Facts about the [generate_architecture] function *)

Section GenArchiFacts.

  Lemma gen_arch_inv_lofPs :
    forall {sitpn mm s v s'},
      @generate_architecture sitpn mm s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_arch_inv_lofTs :
    forall {sitpn mm s v s'},
      @generate_architecture sitpn mm s = OK v s' ->
      lofTs s = lofTs s'.
  Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma gen_arch_inv_sil_lofTs :
    forall {sitpn mm s v s'},
      @generate_architecture sitpn mm s = OK v s' ->
      Sig_in_List (lofTs s) -> Sig_in_List (lofTs s').
  Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.
  
  Lemma gen_archi_pdi_ex :
    forall (sitpn : Sitpn) (b : P sitpn -> nat) (s : Sitpn2HVhdlState sitpn) v s' p,
      generate_architecture b s = OK v s' ->
      Sig_in_List (lofPs s) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pdi (γ s'))
          /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) (beh s')).
  Proof.
    intros *; intros e; monadInv e; intros SIL_lofPs.
    eapply gen_tdis_pdi_ex; eauto.
    eapply gen_pdis_pdi_ex; eauto.
  Qed.

  Lemma gen_archi_nodup_cids2 :
    forall (sitpn : Sitpn) (b : P sitpn -> nat)
           (s : Sitpn2HVhdlState sitpn) v s',
      generate_architecture b s = OK v s' ->
      (forall id__c, In id__c (get_cids (beh s)) -> id__c < nextid s) /\ NoDup (get_cids (beh s)) ->
      (forall id__c, In id__c (get_cids (beh s')) -> id__c < nextid s') /\ NoDup (get_cids (beh s')).
  Proof.
    intros *; intros H Pstart; generalize Pstart; pattern s, s'; solve_sinv_pattern.
    (* Solves nextid subgoals. *)
    all: try (match goal with
              | [ EQ: _ = OK _ ?s  |- (_) _ ?s ] =>
                  cbn; minv EQ; destruct 1;
                  (split; [ intros; eapply Nat.lt_lt_succ_r; eauto | assumption ])
              end).
    (* new tdi in beh *)
    - cbn; match_and_minv constr:(@get_nextid sitpn); match_and_minv constr:(@OK).
      destruct 1 as [ Inlt4 NoDup4 ]; split; rewrite get_cids_app; cbn.
      destruct 1 as [ eq_idc | ]; [ rewrite <- eq_idc | eauto ].
      match goal with
      | H: build_tdi _ _ _ = _ |- _ => shelf_state H; unfold lt
      end.
      match goal with
      | [ s := _ : Sitpn2HVhdlState _ |- S (nextid ?s') <= _ ] =>
          change (S (nextid s')) with (nextid s)
      end.
      eapply build_tdi_inv_inc_nextid; eauto.
      constructor; eauto.
      let build_tdi_eq := (get_meq build_tdi) in
      rewrite <- (build_tdi_inv_beh build_tdi_eq); simpl.
      match goal with
      |  |- ~In ?ns _ => intros In6; apply (Nat.lt_irrefl ns)
      end;
      eapply (proj1 (P1 P0)); eauto.
      
    (* new pdi in beh *)
    - let EQ_get_nextid := get_meq (@get_nextid sitpn) in
      let EQ_OK := get_meq (@OK (Sitpn2HVhdlState sitpn)) in
      cbn; minv EQ_get_nextid; minv EQ_OK.
      destruct 1 as [ Inlt4 NoDup4 ]; split; rewrite get_cids_app; cbn.
      destruct 1 as [ eq_idc | ]; [ rewrite <- eq_idc | eauto ].
      match goal with
      | H: build_pdi _ _ _ _ = _ |- _ => shelf_state H; unfold lt
      end.
      match goal with
      | [ s := _ : Sitpn2HVhdlState _ |- S (nextid ?s') <= _ ] =>
          change (S (nextid s')) with (nextid s)
      end.
      eapply build_pdi_inv_inc_nextid; eauto.
      constructor; eauto.
      let EQ_build_pdi := get_meq build_pdi in
      rewrite <- (build_pdi_inv_beh EQ_build_pdi); simpl.
      match goal with
      |  |- ~In ?ns _ =>
           intros In6; apply (Nat.lt_irrefl ns)
      end; eapply (proj1 (P0 P)); eauto.
  Qed.
  
  Lemma gen_archi_nodup_cids :
    forall (sitpn : Sitpn) (b : P sitpn -> nat)
           (s : Sitpn2HVhdlState sitpn) v s',
      generate_architecture b s = OK v s' ->
      (forall id__c, In id__c (get_cids (beh s)) -> id__c < nextid s) ->
      NoDup (get_cids (beh s)) ->
      NoDup (get_cids (beh s')).
  Proof. intros; eapply gen_archi_nodup_cids2; eauto. Qed.
  
End GenArchiFacts.

