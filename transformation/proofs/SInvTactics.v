(** * Tactics for state invariants *)

Require Import common.CoqLib.
Require Import common.StateAndErrorMonad.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import common.proofs.ListMonadFacts.
Require Import common.proofs.ListMonadTactics.

Require Import sitpn.SitpnLib.
Require Import sitpn.SitpnFacts.

Require Import hvhdl.AbstractSyntax.

Require Import transformation.Sitpn2HVhdl.
Require Import transformation.Sitpn2HVhdlTypes.
Require Import transformation.Sitpn2HVhdlUtils.
Require Import transformation.proofs.Sitpn2HVhdlUtilsInvs.

Require Import String.
Require Import FunInd.

Ltac check_is_state_record S :=
  match S with
  | MkS2HState _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.

Lemma inject_t_inv_state :
  forall {sitpn decpr t lofTs s v s'},
    inject_t sitpn decpr t lofTs s = OK v s' ->
    s = s'.
Proof.
  intros until s;
  functional induction (inject_t sitpn decpr t lofTs) using inject_t_ind;
    intros until s'; intros f; minv f; auto.
  eapply IHc; eauto. 
Qed.

Lemma put_comp_aux_inv_state :
  forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o} {s : Sitpn2HVhdlState sitpn} {v s'},
    put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
    s = s'.
Proof.
  induction cstmt; intros *; simpl;
    intros e; try (monadInv e; reflexivity).
  destruct (id__c0 =? id__c) in e; monadInv e; reflexivity.
  monadInv e.
  rewrite (get_comp_aux_inv_state EQ).
  destruct x in EQ0; monadInv EQ0; eauto.
Qed.

Ltac intros_inv_state1 :=
  let a := fresh "a" in
  let x := fresh "x" in
  let S := fresh "s" in
  let S' := fresh "s'" in
  let EQ := fresh "EQ" in
  intros a S x S' EQ;
  pattern S, S'.

Ltac intros_inv_state2 :=
  let b := fresh "b" in
  let a := fresh "a" in
  let x := fresh "x" in
  let S := fresh "s" in
  let S' := fresh "s'" in
  let EQ := fresh "EQ" in
  intros b a S x S' EQ;
  pattern S, S'.

Ltac solve_sinv_pattern :=
  lazymatch goal with

  (* Solves the simplest forms of goals in the tactic *)
  | [ |- ?P ?S1 ?S1 ] => auto
    
  (* CASE the monadic function is one of [OK], [Ret], [Get] or [Put],
     then substitutes [S1] by [S2] before solving the goal with [auto] *)
  | [ H: OK _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      inversion H; clear H; subst; auto
  | [ H: Ret _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      inversion H; clear H; subst; auto
  | [ H: Get ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      inversion H; clear H; subst; auto
  | [ H: Put ?S1 _ = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      inversion H; clear H; subst; auto
                                     
  (* If one hypothesis is of the form [Err = OK] or [Error = OK], then
     solves the goal with the [discriminate] tactic. *)
  | [ H: Err _ _ = OK _ _ |- _ ] => discriminate
  | [ H: Error _ = OK _ _ |- _ ] => discriminate
                                      
  (* CASE the monadic function is [Bind] *)
  | [ H: Bind ?F ?G ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      let x := fresh "x" in
      let s := fresh "s" in
      let EQ1 := fresh "EQ" in
      let EQ2 := fresh "EQ" in
      destruct (Bind_inversion _ _ _ F G X S1 S2 H) as [x [s [EQ1 EQ2] ] ];
      (* Hoping that [P] is a transitive property *)
      cut (RelationClasses.Transitive P); [
          let trans := fresh "trans" in
          intros trans; apply (trans S1 s S2); clear trans;
          [ pattern S1, s; try solve_sinv_pattern
          | pattern s, S2; try solve_sinv_pattern ]
        | try (eauto with typeclass_instances) ]                                            
               
  (* CASE the monadic function is a let-binder.

     Let binders with more than two binders in the list are not
     allowed in pattern matching anymore, for instance:

     | [ H: (let (_, _, _) := _ in _) _ = _ |- _ ] => 
     
     not allowed!! *)
                                            
  | [ H: (let (_, _) := ?G in _) ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      destruct G; pattern S1, S2; try solve_sinv_pattern
  | [ H: (let _ := ?G in _) ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      destruct G; pattern S1, S2; try solve_sinv_pattern
  | [ H: (let (_, _) := ?G in _) _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      destruct G; pattern S1, S2; try solve_sinv_pattern
  | [ H: (let _ := ?G in _) _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      destruct G; pattern S1, S2; try solve_sinv_pattern
                                            
  (* CASE the monadic function is of the form [(if C then _ else _) S1
     = OK X S2], then calls [solve_sinv_pattern] in the two
     branches. *)                        
  | [ H: (if ?C then _ else _) ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>                                 
      case C in H; pattern S1, S2; try solve_sinv_pattern
        
  (* CASE the monadic function is of the form [(match G with | Error _
     => _ OK _ _ => _ end) = OK X S2], then solve the case where
     [Error = OK] with [discriminate], and tries to solve the
     remaining case (i.e. where [G = OK]) with
     [solve_sinv_pattern]. *)
  | [ H: (match ?G with | Error _ => _ | OK _ _ => _ end = OK _ ?S2) |- ?P ?S1 ?S2 ]  =>
      case_eq G; [
        let msg := fresh "msg" in
        let EQ := fresh "EQ" in
        intros msg EQ; rewrite EQ in H;
        discriminate
      |
        let x := fresh "x" in
        let S := fresh "s" in
        let EQ := fresh "EQ" in
        intros x S EQ; rewrite EQ in H; inversion H; clear H; subst
      ]; pattern S1, S2; try solve_sinv_pattern
                             
  | [ H: (match ?O with _ => _ end) ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      case O in H; pattern S1, S2; try solve_sinv_pattern
                                       
  (* ********************************************** *)
  (* ** Particular cases of identified functions ** *)
                                       
  (* CASE [iter] function *)
  | [ H: ListMonad.iter _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      eapply (iter_inv_state H);
      [ eauto with typeclass_instances
      | eauto with typeclass_instances
      | intros_inv_state1 ]; try solve_sinv_pattern

  (* CASE [find] function *)
  | [ H: ListMonad.find _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      eapply (find_inv_state H);
      [ eauto with typeclass_instances
      | eauto with typeclass_instances
      | intros_inv_state1 ]; try solve_sinv_pattern
                                      
  (* CASE [tmap] function *)
  | [ H: ListMonad.tmap _ _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      eapply (tmap_inv_state H);
      [ eauto with typeclass_instances
      | eauto with typeclass_instances
      | intros_inv_state1 ]; try solve_sinv_pattern
                                                  
  (* CASE [map] function *)
  | [ H: ListMonad.map _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      eapply (map_inv_state H);
      [ eauto with typeclass_instances
      | eauto with typeclass_instances
      | intros_inv_state1 ]; try solve_sinv_pattern
                                               
  (* CASE [fold_left] function *)
  | [ H: ListMonad.fold_left _ _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      eapply (foldl_inv_state H);
      [ eauto with typeclass_instances
      | eauto with typeclass_instances
      | intros_inv_state2 ]; try solve_sinv_pattern
      
  (* CASE [foreach] function *)
  | [ H: ListMonad.foreach _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      eapply (foreach_inv_state H);
      [ eauto with typeclass_instances
      | eauto with typeclass_instances
      | intros_inv_state2 ]; try solve_sinv_pattern
                                 
  (* Monadic functions [getv], [inject_t], [get_comp] and
     [put_comp_aux] do not modify the compile-time state.  Then,
     rewrite the starting state with the new state in the current
     goal.  *)
                                 
  (* CASE [getv] function *)
  | [ H: ListMonad.getv _ _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      rewrite (getv_inv_state H); clear H; auto
                                             
  (* CASE [inject_t] function *)
  | [ H: inject_t _ _ _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      erewrite (inject_t_inv_state H); eauto

  (* CASE [get_comp] function *)
  | [ H: get_comp _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      erewrite (get_comp_inv_state H); eauto

  (* CASE [put_comp_aux] function *)
  | [ H: put_comp_aux _ _ _ _ _ _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      erewrite (put_comp_aux_inv_state H); eauto

  (* CASE [set_beh] function *)
  (* | [ H: set_beh _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] => eauto *)
                                             
  (* If [H] is of the form [G A1 ... A__n S1 = OK X S2] where [G] is a
     function identifier not covered by the preceding match entries,
     then calls the [cbn] tactic on [H] or tries to unfold [G]. *)
  | [ H: ?G _ _ _ _ _ _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern
  | [ H: ?G _ _ _ _ _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern  
  | [ H: ?G _ _ _ _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern
  | [ H: ?G _ _ _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern
  | [ H: ?G _ _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern
  | [ H: ?G _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern
  | [ H: ?G ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern
                                                    
  (* If [S3] is an instance of a [Sitpn2HVhdlState] record type,
     i.e. of the form (MkS2HState _), and the goal is of the form [P
     S1 S2], then tries to convert [P S1 S2] with [P S3 S2]. 
     Must be tried as a last solution. *)
  | [ H: _ ?S3 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      tryif (check_is_state_record S3) then
        tryif (change (P S1 S2)  with (P S3 S2)) then solve_sinv_pattern
        else (fail 0 P S1 S2 "and" P S3 S2 "are not convertible")
      else
        tryif (change S1 with S3) then solve_sinv_pattern
        else (fail 0 S1 "and" S3 "are not convertible")
  end.

(* Unit tests on [solve_sinv]. *)

Require Import common.ListPlus.
Require Import RelationClasses.

Lemma gen_tinfos_inv_γ :
  forall {sitpn s v s'},
    generate_trans_infos sitpn s = OK v s' ->
    γ s = γ s'.
Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_tinfos_inv_sil_lofps :
  forall {sitpn s v s'},
    generate_trans_infos sitpn s = OK v s' ->
    Sig_in_List (lofPs s) ->
    Sig_in_List (lofPs s').
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_pinfos_inv_γ :
  forall {sitpn decpr s v s'},
    generate_place_infos sitpn decpr s = OK v s' ->
    γ s = γ s'.
Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_pinfos_inv_sil_lofps :
  forall {sitpn decpr s v s'},
    generate_place_infos sitpn decpr s = OK v s' ->
    Sig_in_List (lofPs s) ->
    Sig_in_List (lofPs s').
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_cinfos_inv_γ :
  forall {sitpn s v s'},
    generate_cond_infos sitpn s = OK v s' ->
    γ s = γ s'.
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_sitpn_infos_inv_γ :
  forall {sitpn decpr s v s'},
    generate_sitpn_infos sitpn decpr s = OK v s' ->
    γ s = γ s'.
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

Lemma conn_to_input_tcis_inv_beh :
  forall {sitpn : Sitpn} {pinfo i} {s : Sitpn2HVhdlState sitpn} {v s'},
    connect_to_input_tcis pinfo i s = OK v s' ->
    beh s = beh s'.
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

Lemma conn_to_input_tcis_inv_γ :
  forall {sitpn : Sitpn} {pinfo i} {s : Sitpn2HVhdlState sitpn} {v s'},
    connect_to_input_tcis pinfo i s = OK v s' ->
    γ s = γ s'.
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

Lemma conn_to_output_tcis_inv_γ :
  forall {sitpn : Sitpn} {pinfo i o} {s : Sitpn2HVhdlState sitpn} {v s'},
    connect_to_output_tcis pinfo i o s = OK v s' ->
    γ s = γ s'.
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

Require Import Lia.

Lemma put_comp_aux_InCs_inv :
  forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o} {s : Sitpn2HVhdlState sitpn} {v s'},
    put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
    forall id__c' id__e' g' i' o',
      id__c' <> id__c ->
      InCs (cs_comp id__c' id__e' g' i' o') cstmt ->
      InCs (cs_comp id__c' id__e' g' i' o') v.
Proof. induction cstmt; intros *; simpl; try (solve [inversion 3]).
       - case_eq (id__c0 =? id__c); intros e EQ; monadInv EQ.
         + inversion 2; subst. 
           rewrite Nat.eqb_eq in e; lia.
         + inversion_clear 2; do 2 constructor.
       - intros EQ; monadInv EQ.
Admitted.

Lemma put_comp_aux_comp_ex :
  forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o} {s : Sitpn2HVhdlState sitpn} {v s'},
    put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
    (exists g0 i0 o0, InCs (cs_comp id__c id__e g0 i0 o0) cstmt) ->
    (exists g1 i1 o1, InCs (cs_comp id__c id__e g1 i1 o1) v).
Admitted.

Require Import hvhdl.HVhdlCoreLib.

Lemma InCs_NoDup_comp_eq :
  forall {cstmt id__c id__e0 g0 i0 o0 id__e1 g1 i1 o1},
    InCs (cs_comp id__c id__e0 g0 i0 o0) cstmt ->
    InCs (cs_comp id__c id__e1 g1 i1 o1) cstmt ->
    NoDup (get_comp_ids cstmt) ->
    cs_comp id__c id__e0 g0 i0 o0 = cs_comp id__c id__e1 g1 i1 o1.
Admitted.

Lemma put_comp_aux_InCs :
  forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o} {s : Sitpn2HVhdlState sitpn} {v s'},
    put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
    InCs (cs_comp id__c id__e g i o) v.
Admitted.

Lemma put_comp_aux_p_comp_ex :
  forall {cstmt} {sitpn : Sitpn} {id__c id__e} {g i o} {s : Sitpn2HVhdlState sitpn} {v s' p},
    put_comp_aux sitpn id__c id__e g i o cstmt s = OK v s' ->
    NoDup (get_comp_ids cstmt) ->
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
      specialize (InCs_NoDup_comp_eq InCS_cstmt InCs_idc NoDup_compids) as eq_comp.
      inversion eq_comp; subst; reflexivity.      
    }
    rewrite <- eq_ide_plid; eapply put_comp_aux_InCs; eauto.    
           
  (* CASE [id__p <> id__c] *)
  - erewrite <- (put_comp_aux_inv_state EQ).
    exists id__p, g__p, i__p, o__p; split;
      [ assumption | (eapply (put_comp_aux_InCs_inv EQ); eauto) ].
Qed.

Lemma put_comp_p_comp_ex :
  forall {sitpn : Sitpn} {id__c id__e} {g i o} {s : Sitpn2HVhdlState sitpn} {v s' p},
    put_comp id__c id__e g i o s = OK v s' ->
    NoDup (get_comp_ids (beh s)) ->
    (exists g' i' o', InCs (cs_comp id__c id__e g' i' o') (beh s)) ->
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) ->
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s'))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
Proof. intros *; intros e; monadFullInv e; cbn.
       eapply put_comp_aux_p_comp_ex; eauto.  
Qed.

Lemma conn_to_output_tcis_p_comp_ex_inv :
  forall {sitpn : Sitpn} {pinfo i o} {s : Sitpn2HVhdlState sitpn} {v s' p},
    connect_to_output_tcis pinfo i o s = OK v s' ->
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) ->
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s'))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
Proof. intros *; intros H; pattern s,s'; solve_sinv_pattern.
       - cbn.
         inversion EQ15; clear EQ15; subst_right_no_fail; cbn.
         rewrite <- (put_comp_aux_inv_state EQ12).
Admitted.
         
Lemma gen_inter_p_comp_ex :
  forall (sitpn : Sitpn) (s : Sitpn2HVhdlState sitpn) v s' p,
    generate_interconnections s = OK v s' ->
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) ->
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s'))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
Proof.  
  intros *; intros H; pattern s, s'.
  monadFullInv H.
  pattern s0, s'; eapply (iter_inv_state EQ0); eauto.
  intros *; intros e; monadFullInv e.
  erewrite (getv_inv_state EQ3); eauto; clear EQ3.
  erewrite (getv_inv_state EQ5); eauto; clear EQ5.
  erewrite (get_comp_aux_inv_state EQ1); eauto; clear EQ1.
  destruct x4 in EQ6; monadInv EQ6.
  destruct x2 in EQ4; destruct p0 in EQ4; destruct p0 in EQ4.
  monadInv EQ4.
  erewrite (conn_to_input_tcis_inv_beh EQ); eauto.
  erewrite (conn_to_input_tcis_inv_γ EQ); eauto.
  clear EQ.
  case_eq x3; intros *; intros e; subst.
  intro; eapply (put_comp_p_comp_ex EQ3); eauto.
  eapply (conn_to_output_tcis_p_comp_ex_inv EQ2); eauto.
Qed.
