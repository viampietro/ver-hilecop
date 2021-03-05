(** * Architecture Generation and State Invariants *)

Require Import String.
Require Import common.Coqlib.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListLib.

Require Import dp.Sitpn.
Require Import dp.SitpnFacts.

Require Import hvhdl.Place.
Require Import hvhdl.AbstractSyntax.

Require Import sitpn2hvhdl.Sitpn2HVhdl.

(** ** Place Map Generation and State Invariants *)

Section GenPMapInvs.

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

  Lemma gen_pmap_entry_inv_beh :
    forall {sitpn} {p : P sitpn} {mm s v s'},
      generate_place_map_entry p mm s = OK v s' ->
      beh s = beh s'.
  Proof. try solve_gen_pmap_entry_sinv. Qed.

  Lemma gen_pmap_inv_beh :
    forall {sitpn mm s v s'},
      @generate_place_map sitpn mm s = OK v s' ->
      beh s = beh s'.
  Proof.
    intros until s'; intros e; minv e.
    pattern s0, s3.
    eapply map_inv_state; eauto with typeclass_instances; cbn.
    intros; eapply gen_pmap_entry_inv_beh; eauto.
  Qed.
  
End GenPMapInvs.

(** ** Transition Map Generation and State Invariants *)

Section GenTMapInvs.

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

  Lemma gen_tmap_entry_inv_plmap :
    forall {sitpn} {t : T sitpn} {s v s'},
      generate_trans_map_entry t s = OK v s' ->
      plmap (arch s) = plmap (arch s').
  Proof. intros until s'; intros e; minv e; solve_listm EQ1. Qed.

  Lemma gen_tmap_inv_plmap :
    forall {sitpn s v s'},
      @generate_trans_map sitpn s = OK v s' ->
      plmap (arch s) = plmap (arch s').
  Proof.
    intros until s'; intros e; minv e.
    pattern s0, s3.
    eapply map_inv_state; eauto with typeclass_instances; cbn.
    intros; eapply gen_tmap_entry_inv_plmap; eauto.
  Qed.

  Lemma gen_tmap_entry_inv_beh :
    forall {sitpn} {t : T sitpn} {s v s'},
      generate_trans_map_entry t s = OK v s' ->
      beh s = beh s'.
  Proof. intros until s'; intros e; minv e; solve_listm EQ1. Qed.

  Lemma gen_tmap_inv_beh :
    forall {sitpn s v s'},
      @generate_trans_map sitpn s = OK v s' ->
      beh s = beh s'.
  Proof.
    intros until s'; intros e; minv e.
    pattern s0, s3.
    eapply map_inv_state; eauto with typeclass_instances; cbn.
    intros; eapply gen_tmap_entry_inv_beh; eauto.
  Qed.
  
End GenTMapInvs.

(** ** Interconnection Generation and State Invariants *)

Section GenInterconnInvs.

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
  Proof. intros *; intros e1; minv e1; solve_listm EQ1. Qed.

  Lemma connect_fired_port_inv_plmap :
    forall {sitpn} {e} {t : T sitpn} {s v s'},
      connect_fired_port e t s = OK v s' ->
      plmap (arch s) = plmap (arch s').
  Proof. intros *; intros e1; minv e1; solve_listm EQ1. Qed.

  Lemma connect_fired_port_inv_beh :
    forall {sitpn} {e} {t : T sitpn} {s v s'},
      connect_fired_port e t s = OK v s' ->
      beh s = beh s'.
  Proof. intros *; intros e1; minv e1; solve_listm EQ1. Qed.
      
  Lemma connect_fired_ports_inv_γ :
    forall {sitpn} {lofTs : list (T sitpn)} {s v s'},
      connect_fired_ports lofTs s = OK v s' ->
      γ s = γ s'.            
  Proof. intros *; intros e; unfold connect_fired_ports in e; solve_listm e.
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

  Lemma connect_fired_ports_inv_beh :
    forall {sitpn} {lofTs : list (T sitpn)} {s v s'},
      connect_fired_ports lofTs s = OK v s' ->
      beh s = beh s'.            
  Proof.
    intros *; intros e; unfold connect_fired_ports in e; solve_listm e.
    intros; eapply connect_fired_port_inv_beh; eauto.
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

  Lemma connect_inv_beh :
    forall {sitpn xcomp ycomp id__x id__y} {s : Sitpn2HVhdlState sitpn} {v s'},
      connect xcomp ycomp id__x id__y s  = OK v s' ->
      beh s = beh s'.
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
  
  Lemma connect_poutputs_inv_beh :
    forall {sitpn} {pinfo : PlaceInfo sitpn} {hcomp s v s'},
      connect_place_outputs pinfo hcomp s = OK v s' ->
      beh s = beh s'.
  Proof.
    intros *; intros e; unfold connect_place_outputs in e; solve_listm e.
    intros *; intros e; monadInv e; minv EQ; solve_listm EQ3. 
    rewrite (connect_inv_beh EQ1); clear EQ1.
    destrm EQ2; monadInv EQ2; rewrite (connect_inv_beh EQ); clear EQ.
    destrm EQ0; monadInv EQ0; rewrite (connect_inv_beh EQ); clear EQ.
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

  Ltac rw_plmap_interconnect_p :=
    match goal with
    | [ E0: ListMonad.getv _ _ _ ?s0 = OK _ ?s1,
            E1: ListMonad.getv _ _ _ ?s1 = OK _ ?s2,
                E2: connect_fired_ports _ ?s2 = OK _ ?s3,
                    E3: connect_fired_ports _ ?s3 = OK _ ?s4,
                        E4: connect_place_outputs _ _ ?s4 = OK _ ?s5
        |- _ ] =>
      rewrite (getv_inv_state E0),
      (getv_inv_state E1),
      (connect_fired_ports_inv_plmap E2),
      (connect_fired_ports_inv_plmap E3),
      (connect_poutputs_inv_plmap E4)
    end.
  
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
    assert (e : plmap (arch s0) = plmap (arch s5))
      by (rw_plmap_interconnect_p; reflexivity).
    rewrite <- e; auto.
  Qed.
  
  Lemma interconnect_p_inv_sil_plmap :
    forall {sitpn p s v s'},
      @interconnect_p sitpn p s = OK v s' ->
      Sig_in_List (fs (plmap (arch s))) ->
      Sig_in_List (fs (plmap (arch s'))).
  Proof.
    intros *; intros e; minv e.
    rw_plmap_interconnect_p.
    auto with listplus.
  Qed.

  Lemma interconnect_p_inv_beh :
    forall {sitpn p s v s'},
      @interconnect_p sitpn p s = OK v s' ->
      beh s = beh s'.
  Proof.
    intros until s'; intros e; minv e; simpl.
    solve_listm EQ4; solve_listm EQ5.
    transitivity (beh s3).
    erewrite connect_fired_ports_inv_beh; eauto.
    transitivity (beh s2).
    erewrite connect_fired_ports_inv_beh; eauto.
    erewrite connect_poutputs_inv_beh; eauto.
  Qed.
  
  Lemma gen_interconnections_inv_sil_plmap :
    forall {sitpn s v s'},
      @generate_interconnections sitpn s = OK v s' ->
      Sig_in_List (fs (plmap (arch s))) ->
      Sig_in_List (fs (plmap (arch s'))).
  Proof.
    intros *; intros e; solveSInv e.
    intros; eapply interconnect_p_inv_sil_plmap; eauto.
  Qed.

  Lemma gen_interconnections_inv_beh :
    forall {sitpn s v s'},
      @generate_interconnections sitpn s = OK v s' ->
      beh s = beh s'.
  Proof.
    intros *; intros e; solveSInv e.
    intros; eapply interconnect_p_inv_beh; eauto.
  Qed.  
  
  Lemma interconnect_p_inv_InA_plmap_1 :
    forall {sitpn x y pcomp s v s'},
      @interconnect_p sitpn y s = OK v s' ->
      ~Peq x y ->
      InA Pkeq (x, pcomp) (plmap (arch s')) ->
      InA Pkeq (x, pcomp) (plmap (arch s)).
  Proof.
    intros *; intros e; minv e.
    rw_plmap_interconnect_p; eauto with setoidl.
  Qed.

  Lemma interconnect_p_inv_InA_plmap_2 :
    forall {sitpn x y pcomp s v s'},
      @interconnect_p sitpn y s = OK v s' ->
      ~Peq x y ->
      InA Pkeq (x, pcomp) (plmap (arch s)) ->
      InA Pkeq (x, pcomp) (plmap (arch s')).
  Proof.
    intros *; intros e; minv e.
    rw_plmap_interconnect_p; eauto with setoidl.
  Qed.

  Lemma connect_inv_comp_maps :
    forall {sitpn gx ix ox gy iy oy id__x id__y} {s : Sitpn2HVhdlState sitpn} {v s'},
      connect (gx, ix, ox) (gy, iy, oy) id__x id__y s = OK v s' ->
      exists ox' iy', v = ((gx, ix, ox'), (gy, iy', oy)).
  Proof. intros *; intros e; minv e; eauto. Qed.
  
  Lemma foldl_connect_ptot_inv_gmap_imap :
    forall {sitpn} {trs : list (T sitpn)} {hcomp1 s hcomp2 s'},
      fold_left (fun pcomp t => connect_popmap_to_tipmap pcomp t) trs hcomp1 s = OK hcomp2 s' ->
      forall g i o, hcomp1 = (g, i, o) -> exists o', hcomp2 = (g, i, o').
  Proof.
    intros *; intros e.
    pattern hcomp1, hcomp2.
    eapply foldl_inv_val; eauto with typeclass_instances.
    unfold Transitive; intros; edestruct H; eauto.
    intros *; intros e1; cbn in e1. monadInv e1.
    destruct b3 as ((g3, i3), o3).
    destruct x as ((gx, ix), ox).
    edestruct (@connect_inv_comp_maps sitpn) as (o3', (ix', eq_x0)); eauto.
    clear EQ1.
    rewrite eq_x0 in EQ2; clear eq_x0; monadInv EQ2.
    edestruct (@connect_inv_comp_maps sitpn) as (o3'', (ix'', eq_x)); eauto.
    clear EQ0.
    rewrite eq_x in EQ1; clear eq_x; monadInv EQ1.
    edestruct (@connect_inv_comp_maps sitpn) as (o3''', (ix''', eq_x1)); eauto.
    clear EQ0.
    rewrite eq_x1 in EQ2; clear eq_x1; minv EQ2.
    intros *; intros eq_comp; inject_left eq_comp.
    exists o3'''; reflexivity.
  Qed.
  
  Lemma connect_poutputs_inv_gmap_imap :
    forall {sitpn} {pinfo : PlaceInfo sitpn} {g i o s v s'},
      connect_place_outputs pinfo (g, i, o) s = OK v s' ->
      exists o', (g, i, o') = v.
  Proof.
    intros *; intros e; unfold connect_place_outputs in e.
    edestruct (@foldl_connect_ptot_inv_gmap_imap sitpn) as (o', eq_v); eauto.
  Qed.    
  
  Lemma interconnect_p_inv_pcomp_imap :
    forall {sitpn p s v s'},
      @interconnect_p sitpn p s = OK v s' ->
      Sig_in_List (fs (plmap (arch s))) ->
      forall g1 i1 o1 g2 i2 o2,
        InA Pkeq (p, (g1, i1, o1)) (plmap (arch s)) ->
        InA Pkeq (p, (g2, i2, o2)) (plmap (arch s')) ->
        forall id es,
          id <> input_transitions_fired ->
          id <> output_transitions_fired ->
          List.In (id, es) i1 ->
          List.In (id, es) i2.
  Proof.
    intros *; intros e; minv e.

    (* SUBGOAL [(g1, i1, o1) = (g, i0, o)] *)
    rewrite (getv_inv_state EQ4); intros SIL; intros *; intros InA_plmap4.
    assert (InA_plmap4' : InA Pkeq (p, (g, i0, o)) (plmap (arch s4)))
      by (eapply getv_correct; eauto).
    assert (e : (g1, i1, o1) = (g, i0, o)).
    { eapply NoDupA_fs_eqk_eq with (eqk := Peq); eauto.
      exact (proj2 SIL). }

    (* SUBGOAL [(g2, i2, o2) = (g, (setv ... (setv ... i0)), o')] *)
    intros InA_setv_plmap.
    edestruct (@connect_poutputs_inv_gmap_imap sitpn) as (o', e1);
      eauto.
    assert (e2 : (g2, i2, o2) = x2).
    { eapply @eqv_if_InA_NoDupA_setv with (eqk := Peq); eauto.
      assert (e2 : plmap (arch s4) = plmap (arch s5))
        by (rewrite <- (getv_inv_state EQ4);
            rw_plmap_interconnect_p;
            reflexivity).
      inject_left e2; exact (proj2 SIL).      
    }

    (* Rewrite [i1 = i0] and [i2 = (setv ... (setv ... i0)) *)
    inject_left e; rewrite <- e1 in e2; inject_left e2.
    intros *; intros neq_itf neq_otf In_i0.
    eapply InA_eq_pair_In;
      eapply @In_InA with (eqA := fun x y => (fst x) = (fst y) /\ (snd x) = (snd y)) in In_i0;
      eauto with typeclass_instances.
    eapply InA_setv_inv_1; eauto.
    eapply InA_setv_inv_1; eauto.
  Qed.

  Lemma iter_interconnect_p_inv_InA_plmap :
    forall {sitpn pls} {s v s'},
      iter (@interconnect_p sitpn) pls s = OK v s' ->
      forall p pcomp,
        ~InA Peq p pls ->
        InA Pkeq (p, pcomp) (plmap (arch s)) ->
        InA Pkeq (p, pcomp) (plmap (arch s')).
  Proof.
    intros until pls;
      functional induction (iter (@interconnect_p sitpn) pls) using iter_ind;
      intros s v s' e; monadInv e; auto; intros *; intros nInA_pls InA_plmap.
    eapply @interconnect_p_inv_InA_plmap_2 with (s := s0); eauto.
  Qed.
  
  Lemma iter_interconnect_p_inv_pcomp_imap :
    forall {sitpn pls s v s'},
      iter (@interconnect_p sitpn) pls s = OK v s' ->
      Sig_in_List (fs (plmap (arch s))) ->
      NoDupA Peq pls ->
      forall p g1 i1 o1 g2 i2 o2,
        InA Peq p pls ->
        InA Pkeq (p, (g1, i1, o1)) (plmap (arch s)) ->
        InA Pkeq (p, (g2, i2, o2)) (plmap (arch s')) ->
        forall id es,
          id <> input_transitions_fired ->
          id <> output_transitions_fired ->
          List.In (id, es) i1 ->
          List.In (id, es) i2.
  Proof.
    intros until pls; functional induction (iter (@interconnect_p sitpn) pls) using iter_ind.

    (* CASE pls = [] *)
    - inversion 4.

    (* CASE [a :: pls] *)
    - intros *; intros e; monadInv e; intros SIL_plmap NoDupA_pls.
      inversion_clear 1 as [ y l Peq_pb | y l InA_tl].

      (* SUBCASE [Peq p b] *)
      assert (SIL_plmap0 : Sig_in_List (fs (plmap (arch s0))))
        by (generalize SIL_plmap; solve_listm EQ; intros *;
            eapply interconnect_p_inv_sil_plmap).
      intros; eapply interconnect_p_inv_pcomp_imap; eauto 2 with setoidl.      
      eapply iter_interconnect_p_inv_InA_plmap; eauto with setoidl.
      inversion NoDupA_pls; auto.

      (* SUBCASE [p ∈ tl] *)
      do 2 intro; eapply IHm with (s' := s0); eauto with setoidl.
      eapply interconnect_p_inv_InA_plmap_1; eauto.
      inversion NoDupA_pls; eauto with setoidl.
  Qed.
  
  Lemma gen_interconnections_inv_pcomp_imap : 
    forall {sitpn s v s'},
      @generate_interconnections sitpn s = OK v s' ->
      Sig_in_List (lofPs s) ->
      Sig_in_List (fs (plmap (arch s))) ->
      forall p g1 i1 o1 g2 i2 o2,
        InA Pkeq (p, (g1, i1, o1)) (plmap (arch s)) ->
        InA Pkeq (p, (g2, i2, o2)) (plmap (arch s')) ->
        forall id es,
          id <> input_transitions_fired ->
          id <> output_transitions_fired ->
          List.In (id, es) i1 ->
          List.In (id, es) i2.
  Proof.
    intros *; intros e; minv e; intros SIL_lofps SIL_plmap; intros.
    eapply iter_interconnect_p_inv_pcomp_imap; eauto.
    exact (proj2 SIL_lofps).
    exact ((proj1 SIL_lofps) p).
  Qed.
  
End GenInterconnInvs.

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

Lemma gen_arch_inv_beh :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    beh s = beh s'.
Proof.
  intros until s'; intros e; monadInv e.
  rewrite (gen_pmap_inv_beh EQ),
  (gen_tmap_inv_beh EQ1),
  (gen_interconnections_inv_beh EQ2);
    reflexivity.
Qed.
