(** * Facts about Architecture Generation *)

Require Import String.
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

Require Import hvhdl.Place.
Require Import hvhdl.AbstractSyntax.

Require Import transformation.Sitpn2HVhdl.
Require Import transformation.proofs.GenerateArchitectureInvs.
Require Import transformation.proofs.SInvTactics.

(** ** Facts about the generation of PCIs *)

Section GenPCIsFacts.

  (** *** Facts about the [build_pci] function *)
  
  Lemma build_pci_inv_beh :
    forall {sitpn} {p : P sitpn} {pinfo n s v s'},
      build_pci p pinfo n s = OK v s' ->
      beh s = beh s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

  Lemma build_pci_inv_γ :
    forall {sitpn} {p : P sitpn} {pinfo n s v s'},
      build_pci p pinfo n s = OK v s' ->
      γ s = γ s'.
  Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.
  
  (** *** Facts about the [generate_pci] function *)

  Lemma p_comp_ex_Peq_equiv :
    forall sitpn (x y : P sitpn) s,
      Peq x y ->
      ((exists id__p g__p i__p o__p,
           InA Pkeq (x, id__p) (p2pcomp (γ s)) /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s))
       <-> (exists id__p g__p i__p o__p,
               InA Pkeq (y, id__p) (p2pcomp (γ s)) /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s))).
  Proof.
    intros; split;
      (edestruct 1 as (id__p, (g__p, (i__p, (o__p, (InA_a, InCs_)))));
       exists id__p, g__p, i__p, o__p; split; [ eauto with setoidl | assumption ]).
  Qed.
  
  Lemma gen_pci_p_comp_ex :
    forall sitpn (n : nat) (a : P sitpn) (s1 : Sitpn2HVhdlState sitpn) (x : unit) (s2 : Sitpn2HVhdlState sitpn),
      generate_pci a n s1 = OK x s2 ->
      exists id__p g__p i__p o__p,
        InA Pkeq (a, id__p) (p2pcomp (γ s2)) /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s2).
  Proof.
    intros *; intros e; minv e.
    all: do 4 eexists; split; [ eauto with setoidl | left; eauto ].
  Qed.  

  Lemma gen_pci_p_comp_ex_inv :
    forall sitpn (n : nat) (a : P sitpn) (s1 : Sitpn2HVhdlState sitpn) (x : unit) (s2 : Sitpn2HVhdlState sitpn),
      generate_pci a n s1 = OK x s2 ->
      forall b,
        (exists id__p g__p i__p o__p,
            InA Pkeq (b, id__p) (p2pcomp (γ s1)) /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s1)) ->
        exists id__p g__p i__p o__p,
          InA Pkeq (b, id__p) (p2pcomp (γ s2)) /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s2).
  Proof.
    intros *; intros e b; destruct (Peqdec a b) as [Peq_ab | nPeq_ab]. 

    (* CASE [Peq a b], implies [Q a s' <-> Q b s']. *)
    - rewrite <- (p_comp_ex_Peq_equiv sitpn a b s1 Peq_ab).
      rewrite <- (p_comp_ex_Peq_equiv sitpn a b s2 Peq_ab).
      intro; eapply gen_pci_p_comp_ex; eauto.
      
    (* CASE [~Peq a b], then nevermind the new entry [(a, id__p)] and new
     PCI in [(beh s2)]. *)
    - monadInv e; monadInv EQ; monadInv EQ2; monadInv EQ.
      rewrite (getv_inv_state EQ4); minv EQ1.
      match goal with
      | [ H: build_pci _ _ _ ?s = _ |- _ ] => set (s1' := s) in H
      end.
      change (γ s1) with (γ s1'); change (beh s1) with (beh s1').
      rewrite (build_pci_inv_beh EQ0); rewrite (build_pci_inv_γ EQ0); minv EQ3.
      edestruct 1 as (id__p, (g__p, (i__p, (o__p, (InA_a, InCs_))))).
      exists id__p, g__p, i__p, o__p; split; [ eauto 1 with setoidl | right; assumption ].
  Qed.

  (** *** Facts about the [generate_pcis] function *)
  
  Lemma gen_pcis_p_comp_ex :
    forall (sitpn : Sitpn) (b : P sitpn -> nat) (s : Sitpn2HVhdlState sitpn) v s' p,
      generate_pcis b s = OK v s' ->
      Sig_in_List (lofPs s) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s'))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
  Proof.
    intros *; intros e; minv e. intros SIL_lofPs.
    pattern p, s'.
    eapply iter_prop_A_state with (eqA := Peq); eauto.

    (* Proves that [Peq a b] implies [Q a s' <-> Q b s']. *)
    - eapply p_comp_ex_Peq_equiv.
      
    (* Proves that [∀ a, f a s = OK v s' -> Q a s'] where [f] 
     is [generate_pci] here. *)
    - cbn; intros x; eapply gen_pci_p_comp_ex.
      
    (* Proves that property [Q] is invariant. *)
    - simpl; intros x; eapply gen_pci_p_comp_ex_inv with (n := b x).

    (* Proves that *)
    - eapply SIL_forall_A; eauto.
  Qed.
  
End GenPCIsFacts.

(** ** Facts about the generation of TCIs *)

Section GenTCIsFacts.

  (** *** Facts about the [generate_tcis] function *)
  
End GenTCIsFacts.

(** ** Facts about the [generate_architecture] function *)

Section GenArchiFacts.

  Lemma gen_archi_p_comp_ex :
    forall (sitpn : Sitpn) (b : P sitpn -> nat) (s : Sitpn2HVhdlState sitpn) v s' p,
      generate_architecture b s = OK v s' ->
      Sig_in_List (lofPs s) ->
      (exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pcomp (γ s'))
          /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
  Proof.
    intros *; intros e; monadInv e; intros SIL_lofPs.
    eapply gen_tcis_p_comp_ex; eauto.
    eapply gen_pcis_p_comp_ex; eauto.
  Qed.
  
End GenArchiFacts.

