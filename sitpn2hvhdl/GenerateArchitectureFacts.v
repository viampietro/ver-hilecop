(** * Facts about Architecture Generation *)

Require Import String.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListMonad.
Require Import common.ListMonadFacts.
Require Import common.ListMonadTactics.

Require Import dp.Sitpn.

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

  Lemma gen_pmap_entry_inv_lofPs :
    forall {sitpn} {p : P sitpn} {mm s v s'},
      generate_place_map_entry p mm s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. try solve_gen_pmap_entry_sinv. Qed.

End GenPMap.

(** ** Facts about Transition Map Generation *)

Section GenTMap.

  Lemma gen_tmap_entry_inv_γ :
    forall {sitpn} {t : T sitpn} {s v s'},
      generate_trans_map_entry t s = OK v s' ->
      γ s = γ s'.
  Proof. intros until s'; intros e; minv e; solve_listm EQ1. Qed.

  Lemma gen_tmap_entry_inv_lofPs :
    forall {sitpn} {t : T sitpn} {s v s'},
      generate_trans_map_entry t s = OK v s' ->
      lofPs s = lofPs s'.
  Proof. intros until s'; intros e; minv e; solve_listm EQ1. Qed.
  
End GenTMap.

(** ** Facts about Interconnection Generation *)

Section GenInterconn.

  Lemma connect_fired_port_inv_γ :
    forall {sitpn} {e} {t : T sitpn} {s v s'},
      connect_fired_port e t s = OK v s' ->
      γ s = γ s'.
  Proof.
    intros *; intros e1; monadInv e1; solveSInv EQ; minv EQ1;
      destruct (ListPlus.getv PeanoNat.Nat.eq_dec Transition.fired o); inversion EQ2; auto;
        destruct s; inversion EQ2; auto;
          destruct o0; inversion EQ2; auto.
  Qed.
  
  Lemma connect_fired_ports_inv_γ :
    forall {sitpn} {lofTs : list (T sitpn)} {s v s'},
      connect_fired_ports lofTs s = OK v s' ->
      γ s = γ s'.            
  Proof.
    intros *; intros e; solveSInv e.
    intros; eapply connect_fired_port_inv_γ; eauto.
  Qed.

  Lemma connect_inv_γ :
    forall {sitpn xcomp ycomp id__x id__y} {s : Sitpn2HVhdlState sitpn} {v s'},
      connect xcomp ycomp id__x id__y s  = OK v s' ->
      γ s = γ s'.
  Proof. intros until s'; intros e; minv e; simpl; reflexivity. Qed.

  Lemma connect_poutputs_inv_γ :
    forall {sitpn} {pinfo : PlaceInfo sitpn} {hcomp s v s'},
      connect_place_outputs pinfo hcomp s = OK v s' ->
      γ s = γ s'.
  Proof.
    intros; pattern s, s'; eapply foldl_inv_state; eauto with typeclass_instances.
    intros until s0'; intros e.
    simpl in e.
    unfold connect_popmap_to_tipmap in e.
    monadInv e; minv EQ.
    rewrite (getv_inv_state EQ3); rewrite (connect_inv_γ EQ1); clear EQ3 EQ1.
    destruct x0 as (pcomp1, tcomp1).
    monadInv EQ2.
    rewrite (connect_inv_γ EQ); clear EQ.
    destruct x0 as (pcomp2, tcomp2).
    monadInv EQ0; rewrite (connect_inv_γ EQ); clear EQ.
    destruct x0 as (pcomp3, tcomp3); minv EQ1; auto.
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

End GenInterconn.

(** ** Facts about Architecture Generation Function *)

Lemma gen_arch_inv_γ :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    γ s = γ s'.
Proof.
  intros until s'; intros e; monadFullInv e.
  match goal with
  | [ H1: ListMonad.map (generate_trans_map_entry (sitpn:=sitpn)) _ ?st1 = OK _ _,
          H2: ListMonad.iter _ _ ?st2 = OK _ _
      |- _ ] =>
    simpl in H1; simpl in H2;
    let s1 := fresh "s" in
    let s2 := fresh "s" in
    set (s1 := st1) in *; set (s2 := st2) in *; move s2 after s1
  end.
  transitivity (γ s4).
  solveSInv EQ; intros until s3; intros e; eapply gen_pmap_entry_inv_γ; eauto.
  change (γ s4) with (γ s); transitivity (γ s5).
  solveSInv EQ1; intros until s3; intros e; eapply gen_tmap_entry_inv_γ; eauto.
  change (γ s5) with (γ s1); solveSInv EQ3.
  intros until s3; intros e; eapply interconnect_p_inv_γ; eauto.
Qed.

Lemma gen_arch_inv_lofPs :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    lofPs s = lofPs s'.
Proof.
  intros until s'; intros e; monadFullInv e.
  match goal with
  | [ H1: ListMonad.map (generate_trans_map_entry (sitpn:=sitpn)) _ ?st1 = OK _ _,
          H2: ListMonad.iter _ _ ?st2 = OK _ _
      |- _ ] =>
    simpl in H1; simpl in H2;
    let s1 := fresh "s" in
    let s2 := fresh "s" in
    set (s1 := st1) in *; set (s2 := st2) in *; move s2 after s1
  end.
  transitivity (lofPs s4).
  solveSInv EQ; intros until s3; intros e; eapply gen_pmap_entry_inv_lofPs; eauto.
  change (lofPs s4) with (lofPs s); transitivity (lofPs s5).
  solveSInv EQ1; intros until s3; intros e; eapply gen_tmap_entry_inv_lofPs; eauto.
  change (lofPs s5) with (lofPs s1); solveSInv EQ3.
  intros until s3; intros e; eapply interconnect_p_inv_lofPs; eauto.
Qed.
