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

(** ** Facts about Place Map Generation *)

Section GenPMap.

  Ltac solve_gen_pmap_entry_sinv :=
    intros *; intros e; minv e;
    match goal with
    | [ H: _ ?st1 = OK _ _ |- ?f ?st1 = ?f ?st2 ] =>
      solve_listm H;
      match goal with
      | [ H: _ ?st1 = OK _ ?st2,  H': _ = OK _ ?st3 |- _ ?st1 = _ ?st3 ] =>
        transitivity (f st2);
        [ solveSInv H; intros *; intros e; minv e; auto
        | solveSInv H'; intros *; intros e; minv e; auto]
      end
    end.
  
  Lemma gen_pmap_entry_inv_γ :
    forall {sitpn} {p : P sitpn} {mm s v s'},
      generate_place_map_entry p mm s = OK v s' ->
      γ s = γ s'.
  Proof. try solve_gen_pmap_entry_sinv. Qed.

  Lemma gen_pmap_inv_γ :
    forall {sitpn mm s v s'},
      @generate_place_map sitpn mm s = OK v s' ->
      γ s = γ s'.
  Proof.
    intros until s'; intros e; minv e.
    pattern s0, s3.
    eapply map_inv_state; eauto with typeclass_instances; cbn.
    intros; eapply gen_pmap_entry_inv_γ; eauto.
  Qed.
  
  Lemma gen_pmap_entry_inv_lofPs :
    forall {sitpn} {p : P sitpn} {mm s v s'},
      generate_place_map_entry p mm s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. try solve_gen_pmap_entry_sinv. Qed.

  Lemma gen_pmap_inv_lofPs :
    forall {sitpn mm s v s'},
      @generate_place_map sitpn mm s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros until s'; intros e; minv e.
    pattern s0, s3.
    eapply map_inv_state; eauto with typeclass_instances; cbn.
    intros; eapply gen_pmap_entry_inv_lofPs; eauto.
  Qed.
  
End GenPMap.

(** ** Facts about Transition Map Generation *)

Section GenTMap.

  Lemma gen_tmap_entry_inv_γ :
    forall {sitpn} {t : T sitpn} {s v s'},
      generate_trans_map_entry t s = OK v s' ->
      γ s = γ s'.
  Proof. intros until s'; intros e; minv e; solve_listm EQ1. Qed.

  Lemma gen_tmap_inv_γ :
    forall {sitpn s v s'},
      @generate_trans_map sitpn s = OK v s' ->
      γ s = γ s'.
  Proof.
    intros until s'; intros e; minv e.
    pattern s0, s3.
    eapply map_inv_state; eauto with typeclass_instances; cbn.
    intros; eapply gen_tmap_entry_inv_γ; eauto.
  Qed.
  
  Lemma gen_tmap_entry_inv_lofPs :
    forall {sitpn} {t : T sitpn} {s v s'},
      generate_trans_map_entry t s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros until s'; intros e; minv e; solve_listm EQ1. Qed.

  Lemma gen_tmap_inv_lofPs :
    forall {sitpn s v s'},
      @generate_trans_map sitpn s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros until s'; intros e; minv e.
    pattern s0, s3.
    eapply map_inv_state; eauto with typeclass_instances; cbn.
    intros; eapply gen_tmap_entry_inv_lofPs; eauto.
  Qed.
  
End GenTMap.

(** ** Facts about Interconnection Generation *)

Section GenInterconn.

  Lemma connect_fired_port_inv_γ :
    forall {sitpn} {e} {t : T sitpn} {s v s'},
      connect_fired_port e t s = OK v s' ->
      γ s = γ s'.
  Proof.
    intros *; intros e1; monadFullInv e1;
      solve_listm EQ3; unfold get_actual_of_out_port in EQ1; destrm EQ1;
        monadInv EQ1; destrm EQ2; inversion EQ2; auto.    
  Qed.

  Lemma connect_fired_port_inv_lofPs :
    forall {sitpn} {e} {t : T sitpn} {s v s'},
      connect_fired_port e t s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros *; intros e1; monadFullInv e1. 
    solve_listm EQ3; unfold get_actual_of_out_port in EQ1; destrm EQ1.
    monadInv EQ1; destrm EQ2; inversion EQ2; auto.
  Qed.

  Lemma connect_fired_port_inv_plmap :
    forall {sitpn} {e} {t : T sitpn} {s v s'},
      connect_fired_port e t s = OK v s' ->
      plmap (arch s) = plmap (arch s').
  Proof.
    intros *; intros e1; monadFullInv e1. 
    solve_listm EQ3; unfold get_actual_of_out_port in EQ1; destrm EQ1.
    monadInv EQ1; destrm EQ2; inversion EQ2; auto.
  Qed.
  
  Lemma connect_fired_ports_inv_γ :
    forall {sitpn} {lofTs : list (T sitpn)} {s v s'},
      connect_fired_ports lofTs s = OK v s' ->
      γ s = γ s'.            
  Proof.
    intros *; intros e; unfold connect_fired_ports in e; solve_listm e.
    intros; eapply connect_fired_port_inv_γ; eauto.
  Qed.

  Lemma connect_fired_ports_inv_lofPs :
    forall {sitpn} {lofTs : list (T sitpn)} {s v s'},
      connect_fired_ports lofTs s = OK v s' ->
      lofPs s = lofPs s'.            
  Proof.
    intros *; intros e; unfold connect_fired_ports in e; solve_listm e.
    intros; eapply connect_fired_port_inv_lofPs; eauto.
  Qed.

  Lemma connect_fired_ports_inv_plmap :
    forall {sitpn} {lofTs : list (T sitpn)} {s v s'},
      connect_fired_ports lofTs s = OK v s' ->
      plmap (arch s) = plmap (arch s').            
  Proof.
    intros *; intros e; unfold connect_fired_ports in e; solve_listm e.
    intros; eapply connect_fired_port_inv_plmap; eauto.
  Qed.
  
  Lemma connect_inv_γ :
    forall {sitpn xcomp ycomp id__x id__y} {s : Sitpn2HVhdlState sitpn} {v s'},
      connect xcomp ycomp id__x id__y s  = OK v s' ->
      γ s = γ s'.
  Proof. intros until s'; intros e; minv e; simpl; reflexivity. Qed.

  Lemma connect_inv_lofPs :
    forall {sitpn xcomp ycomp id__x id__y} {s : Sitpn2HVhdlState sitpn} {v s'},
      connect xcomp ycomp id__x id__y s  = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros until s'; intros e; minv e; simpl; reflexivity. Qed.

  Lemma connect_inv_plmap :
    forall {sitpn xcomp ycomp id__x id__y} {s : Sitpn2HVhdlState sitpn} {v s'},
      connect xcomp ycomp id__x id__y s  = OK v s' ->
      plmap (arch s) = plmap (arch s').
  Proof. intros until s'; intros e; minv e; simpl; reflexivity. Qed.
  
  Lemma connect_poutputs_inv_γ :
    forall {sitpn} {pinfo : PlaceInfo sitpn} {hcomp s v s'},
      connect_place_outputs pinfo hcomp s = OK v s' ->
      γ s = γ s'.
  Proof.
    intros *; intros e; unfold connect_place_outputs in e; solve_listm e.
    intros *; intros e; monadInv e; minv EQ; solve_listm EQ3. 
    rewrite (connect_inv_γ EQ1); clear EQ1.
    destrm EQ2; monadInv EQ2; rewrite (connect_inv_γ EQ); clear EQ.
    destrm EQ0; monadInv EQ0; rewrite (connect_inv_γ EQ); clear EQ.
    minv EQ1; auto.
  Qed.

  Lemma connect_poutputs_inv_lofPs :
    forall {sitpn} {pinfo : PlaceInfo sitpn} {hcomp s v s'},
      connect_place_outputs pinfo hcomp s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros *; intros e; unfold connect_place_outputs in e; solve_listm e.
    intros *; intros e; monadInv e; minv EQ; solve_listm EQ3. 
    rewrite (connect_inv_lofPs EQ1); clear EQ1.
    destrm EQ2; monadInv EQ2; rewrite (connect_inv_lofPs EQ); clear EQ.
    destrm EQ0; monadInv EQ0; rewrite (connect_inv_lofPs EQ); clear EQ.
    minv EQ1; auto.
  Qed.

  Lemma connect_poutputs_inv_plmap :
    forall {sitpn} {pinfo : PlaceInfo sitpn} {hcomp s v s'},
      connect_place_outputs pinfo hcomp s = OK v s' ->
      plmap (arch s) = plmap (arch s').
  Proof.
    intros *; intros e; unfold connect_place_outputs in e; solve_listm e.
    intros *; intros e; monadInv e; minv EQ; solve_listm EQ3. 
    rewrite (connect_inv_plmap EQ1); clear EQ1.
    destrm EQ2; monadInv EQ2; rewrite (connect_inv_plmap EQ); clear EQ.
    destrm EQ0; monadInv EQ0; rewrite (connect_inv_plmap EQ); clear EQ.
    minv EQ1; auto.
  Qed.
  
  Lemma interconnect_p_inv_γ :
    forall {sitpn} {p : P sitpn} {s v s'},
      interconnect_p p s = OK v s' ->
      γ s = γ s'.
  Proof.
    intros until s'; intros e; minv e; simpl.
    solve_listm EQ4; solve_listm EQ5.
    transitivity (γ s3).
    erewrite connect_fired_ports_inv_γ; eauto.
    transitivity (γ s2).
    erewrite connect_fired_ports_inv_γ; eauto.
    erewrite connect_poutputs_inv_γ; eauto.  
  Qed.

  Lemma interconnect_p_inv_lofPs :
    forall {sitpn} {p : P sitpn} {s v s'},
      interconnect_p p s = OK v s' ->
      lofPs s = lofPs s'.
  Proof.
    intros until s'; intros e; minv e; simpl.
    solve_listm EQ4; solve_listm EQ5.
    transitivity (lofPs s3).
    erewrite connect_fired_ports_inv_lofPs; eauto.
    transitivity (lofPs s2).
    erewrite connect_fired_ports_inv_lofPs; eauto.
    erewrite connect_poutputs_inv_lofPs; eauto.  
  Qed.
  
  Lemma interconnect_p_pcomp :
    forall {sitpn p s v s'},
      @interconnect_p sitpn p s = OK v s' ->
      exists g i o, InA Pkeq (p, (g, i, o)) (plmap (arch s')).
  Proof.
    intros until s'; intros e; minv e.
    destruct x2 as ((g1, i1), o1).
    exists g1, i1, o1; eauto with setoidl.
  Qed.

  Lemma interconnect_p_inv_pcomp :
    forall {sitpn p1 s v s'},
      @interconnect_p sitpn p1 s = OK v s' ->
      forall p2,
      (exists g i o, InA Pkeq (p2, (g, i, o)) (plmap (arch s))) ->
      (exists g i o, InA Pkeq (p2, (g, i, o)) (plmap (arch s'))).
  Proof.
    intros until s'; intros e p2; minv e.
    destruct (Peqdec p1 p2) as [Peq_ | nPeq].
    (* CASE [Peq p1 p2] *)
    destruct x2 as ((g1, i1), o1).
    exists g1, i1, o1; eauto with setoidl.
    (* CASE [~Peq p1 p2] *)
    destruct 1 as (g1, (i1, (o1, InA_plmap))).
    exists g1, i1, o1.
    eapply InA_setv_inv_1; eauto.
    assert (e : plmap (arch s0) = plmap (arch s5)).
    { rewrite (getv_inv_state EQ4).
      rewrite (getv_inv_state EQ5).
      rewrite (connect_fired_ports_inv_plmap EQ3).
      rewrite (connect_fired_ports_inv_plmap EQ0).
      rewrite (connect_poutputs_inv_plmap EQ2).
      reflexivity.
    }
    rewrite <- e; auto.
    intros Peq_; symmetry in Peq_; contradiction.
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

Lemma gen_arch_inv_γ :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    γ s = γ s'.
Proof.
  intros until s'; intros e; minv e.
  shelf_state EQ1; shelf_state EQ3.
  transitivity (γ s4).
  solve_listm EQ; intros; eapply gen_pmap_entry_inv_γ; eauto.
  change (γ s4) with (γ s); transitivity (γ s5).
  solve_listm EQ1; intros; eapply gen_tmap_entry_inv_γ; eauto.
  change (γ s5) with (γ s1).
  solve_listm EQ3; intros; eapply interconnect_p_inv_γ; eauto.
Qed.

Lemma gen_arch_inv_lofPs :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    lofPs s = lofPs s'.
Proof.
  intros until s'; intros e; monadFullInv e.
  shelf_state EQ1; shelf_state EQ3.
  transitivity (lofPs s4).
  solve_listm EQ; intros; eapply gen_pmap_entry_inv_lofPs; eauto.
  change (lofPs s4) with (lofPs s); transitivity (lofPs s5).
  solve_listm EQ1; intros; eapply gen_tmap_entry_inv_lofPs; eauto.
  change (lofPs s5) with (lofPs s1).
  solve_listm EQ3; intros; eapply interconnect_p_inv_lofPs; eauto.
Qed.

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

Lemma gen_arch_nodup_plmap : 
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    Sig_in_List (lofPs s) ->
    (forall p, ~InA Peq p (fs (plmap (arch s)))) ->
    NoDupA Peq (fs (plmap (arch s))) ->
    NoDupA Peq (fs (plmap (arch s'))).
Admitted.

Lemma gen_arch_inv_beh : 
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    beh s = beh s'.
Admitted.

Lemma gen_arch_bind_init_marking : 
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    forall p g i o,
      InA Pkeq (p, (g, i, o)) (plmap (arch s')) ->
      List.In (initial_marking, inl (e_nat (M0 p))) i.
Admitted.
