(** * Facts about Architecture Generation *)

Require Import String.
Require Import common.Coqlib.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListPlus.
Require Import common.ListMonad.
Require Import common.ListMonadFacts.
Require Import common.ListMonadTactics.
Require Import common.SetoidListFacts.

Require Import dp.Sitpn.
Require Import dp.SitpnFacts.

Require Import hvhdl.Place.
Require Import hvhdl.AbstractSyntax.

Require Import sitpn2hvhdl.Sitpn2HVhdl.
Require Import sitpn2hvhdl.GenerateArchitectureInvs.

(** ** Facts about Place Map Generation *)

Section GenPMap.

  
End GenPMap.

(** ** Facts about Transition Map Generation *)

Section GenTMap.
  
End GenTMap.

(** ** Facts about Interconnection Generation *)

Section GenInterconn.
  
  Lemma interconnect_p_pcomp :
    forall {sitpn p s v s'},
      @interconnect_p sitpn p s = OK v s' ->
      exists g i o, InA Pkeq (p, (g, i, o)) (plmap (arch s')).
  Proof.
    intros until s'; intros e; minv e.
    destruct x2 as ((g1, i1), o1).
    exists g1, i1, o1; eauto with setoidl.
  Qed.
  
  Lemma iter_interconnect_p_pcomp :
    forall {sitpn pls s v s'},
      iter (@interconnect_p sitpn) pls s = OK v s' ->
      NoDupA Peq pls ->
      forall p,
        InA Peq p pls ->
        exists g i o, InA Pkeq (p, (g, i, o)) (plmap (arch s')).
  Proof.
    intros until pls; functional induction (iter (@interconnect_p sitpn) pls) using iter_ind.

    (* BASE CASE *)
    - inversion 3.

    (* IND. CASE *)
    - intros *; intros e NoDupA_pls p InA_pls;
        inversion_clear InA_pls as [ e1 e2 Peq_pb | e1 e2 InA_ntl ];
        monadInv e.

      (* CASE a = n *)
      + edestruct (interconnect_p_pcomp EQ0) as (g, (i, (o, InA_plmap))).
        exists g, i, o; symmetry in Peq_pb; auto with setoidl.

      (* CASE n ∈ tl *)
      + eapply interconnect_p_inv_pcomp; eauto.
        eapply IHm; eauto.
        lazymatch goal with
        | [ H: NoDupA _ _ |- _ ] => inversion_clear H; auto
        end.
  Qed.
  
  Lemma gen_interconnections_pcomp : 
    forall {sitpn s v s'},
      @generate_interconnections sitpn s = OK v s' ->
      Sig_in_List (lofPs s) ->
      forall p, exists g i o,
          InA Pkeq (p, (g, i, o)) (plmap (arch s')).
  Proof.
    intros until s'; intros e; minv e.
    inversion 1; intros; eapply iter_interconnect_p_pcomp; eauto.    
  Qed.
  
End GenInterconn.

(** ** Facts about Architecture Generation Function *)

Lemma gen_arch_pcomp : 
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    Sig_in_List (lofPs s) ->
    forall p, exists g i o,
        InA Pkeq (p, (g, i, o)) (plmap (arch s')).
Proof.
  intros until s'; intros e; monadInv e.
  erewrite gen_pmap_inv_lofPs; eauto.
  erewrite gen_tmap_inv_lofPs; eauto.
  eapply gen_interconnections_pcomp; eauto.
Qed.

Lemma gen_arch_sil_plmap : 
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    Sig_in_List (lofPs s) ->
    (forall p, ~InA Peq p (fs (plmap (arch s)))) ->
    NoDupA Peq (fs (plmap (arch s))) ->
    Sig_in_List (fs (plmap (arch s'))).
Admitted.

Lemma gen_arch_bind_init_marking : 
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    forall p g i o,
      InA Pkeq (p, (g, i, o)) (plmap (arch s')) ->
      List.In (initial_marking, inl (e_nat (M0 p))) i.
Admitted.
