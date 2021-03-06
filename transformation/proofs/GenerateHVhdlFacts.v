(** * Facts about the H-VHDL Generating Functions *)

Require Import String.
Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.GlobalFacts.
Require Import common.StateAndErrorMonad.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import common.ListLib.

Require Import sitpn.SitpnLib.
Require Import sitpn.SitpnUtils.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Place.

Require Import transformation.Sitpn2HVhdl.
Require Import transformation.proofs.Sitpn2HVhdlInvs.
Require Import transformation.proofs.GenerateInfosFacts.
Require Import transformation.proofs.GenerateArchitectureFacts.
Require Import transformation.proofs.GenerateInterconnectionsFacts.
Require Import transformation.proofs.GeneratePortsFacts.

(** ** Facts about Generation of P Component Instances *)

(* Section GeneratePlaceCompInst. *)

  (* Lemma gen_p_comp_inst_p_comp : *)
  (*   forall {sitpn p s v s'}, *)
  (*     generate_place_comp_inst sitpn p s = OK v s' -> *)
  (*     exists (id__p : ident) (gm : genmap) (ipm : inputmap) (opm : outputmap), *)
  (*       InA Pkeq (p, id__p) (p2pdi (γ s')) /\ InCs (cs_comp id__p Petri.place_id gm ipm opm) (beh s'). *)
  (* Proof. *)
  (*   intros until s'; intros e; monadFullInv e. *)
  (*   simpl; simpl in EQ4. *)
  (*   specialize (HComp_to_comp_inst_p_comp EQ2) as (gm, (ipm, (opm, e1))); rewrite e1. *)
  (*   exists (nextid s0), gm, ipm, opm; simpl. *)
  (*   specialize (getv_inv_state EQ4) as e2; subst s2. *)
  (*   specialize (HComp_to_comp_inst_inv_state EQ2) as e2; subst s4. *)
  (*   split; [ apply InA_setv; auto | auto]. *)
  (* Qed. *)

(*   Lemma gen_pcomp_inst_bind_init_marking : *)
(*     forall {sitpn p s v s' g i o}, *)
(*       generate_place_comp_inst sitpn p s = OK v s' -> *)
(*       forall (id__p : ident) (gm : genmap) (ipm : inputmap) (opm : outputmap), *)
(*         InCs (cs_comp id__p Petri.place_id gm ipm opm) (beh s') -> *)
(*         InA Pkeq (p, id__p) (p2pdi (γ s')) -> *)
(*         ~(exists id__e gm ipm opm, InCs (cs_comp (nextid s) id__e gm ipm opm) (beh s)) -> *)
(*         InA Pkeq (p, (g, i, o)) (plmap (arch s)) -> *)
(*         List.In (initial_marking, inl (e_nat (M0 p))) i -> *)
(*         NoDupA Peq (fs (plmap (arch s))) -> *)
(*         NoDupA Peq (fs (p2pdi (γ s))) -> *)
(*         List.In (associp_ initial_marking (M0 p)) ipm. *)
(*   Proof. *)
(*     intros until o; intros e; minv e; shelf_state EQ5. *)
(*     inversion_clear 1 as [eq_comp | InCs_beh]. *)
(*     (* CASE comp are equal *) *)
(*     inject_left eq_comp. *)
(*     do 3 intro; intros InA_plmap; intros. *)
(*     eapply InputMap_to_AST_In_inl; eauto. *)
(*     assert (s = s2) by (eapply getv_inv_state; eauto); subst. *)
(*     change (plmap (arch s0)) with (plmap (arch s)) in InA_plmap. *)
(*     erewrite getv_compl in EQ5; eauto. *)
(*     inject_left EQ5; auto. *)
(*     (* CASE [comp(id__p, "place", gm, ipm, opm) ∈ (beh s)],  *)
(*        contradiction. *) *)
(*     assert (s = s2) by (eapply getv_inv_state; eauto); subst. *)
(*     assert (s = s3) by (eapply InputMap_to_AST_inv_state; eauto); subst. *)
(*     assert (s = s4) by (eapply OutputMap_to_AST_inv_state; eauto); subst. *)
(*     change (p2pdi (γ s)) with (setv Peqdec p (nextid s0) (p2pdi (γ s0))). *)
(*     intros InA_setv nex_InCs; intros; *)
(*       erewrite @eqv_if_InA_NoDupA_setv with (y := id__p) (eqk := Peq) in InCs_beh; *)
(*       eauto with typeclass_instances. *)
(*     exfalso; apply nex_InCs; exists Petri.place_id, gm, ipm, opm; auto. *)
(*   Qed. *)
  
  (* Lemma iter_gen_p_comp_inst_p_comp : *)
  (*   forall {sitpn pls} {s v s'}, *)
  (*     iter (generate_place_comp_inst sitpn) pls s = OK v s' -> *)
  (*     NoDupA Peq pls -> *)
  (*     forall p, InA Peq p pls -> *)
  (*       exists id__p gm ipm opm, *)
  (*         InA Pkeq (p, id__p) (p2pdi (γ s')) /\ *)
  (*         InCs (cs_comp id__p Petri.place_id gm ipm opm) (beh s'). *)
  (* Proof. *)
  (*   intros until pls; functional induction (iter (generate_place_comp_inst sitpn) pls) using iter_ind. *)

  (*   (* BASE CASE *) *)
  (*   - inversion 3. *)

  (*   (* IND. CASE *) *)
  (*   - intros; *)
  (*       lazymatch goal with *)
  (*       | [ Hm : (do _ <- _; _) _ = _, Hin: InA _ _ (_ :: _) |- _ ] => *)
  (*         inversion_clear Hin as [ e1 e2 Peq_pb | e1 e2 HIn_ntl ]; monadInv Hm *)
  (*       end. *)

  (*     (* CASE a = n *) *)
  (*     + specialize (gen_p_comp_inst_p_comp EQ0) as (id__p, (gm, (ipm, (opm, (Hin_γs', Hin_behs'))))). *)
  (*       exists id__p, gm, ipm, opm; split; [ eauto with setoidl | auto]. *)

  (*     (* CASE n ∈ tl *) *)
  (*     + lazymatch goal with *)
  (*       | [ H: NoDupA _ _ |- _ ] => inversion_clear H as [ | e1 e2 Hnotin_a_tl Hnodup_tl ] *)
  (*       end. *)
  (*       specialize (IHm s x s0 EQ Hnodup_tl p HIn_ntl) as (id__p, (gm, (ipm, (opm, (Hγ, Hincs_comp))))). *)

  (*       (* Apply gen_pcomp_inst_inv_p_comp_1 *) *)
  (*       assert (nPeq : ~Peq p b) by (eapply InA_neqA; eauto). *)
  (*       specialize (gen_pcomp_inst_inv_p_comp_1 EQ0 nPeq Hγ Hincs_comp) as (Hγ', Hincs_comp'). *)
  (*       exists id__p, gm, ipm, opm; auto. *)
  (* Qed. *)
  
(*   Lemma iter_gen_pcomp_inst_bind_init_marking : *)
(*     forall {sitpn pls} {s v s'}, *)
(*       iter (generate_place_comp_inst sitpn) pls s = OK v s' -> *)
(*       forall p id__p gm ipm opm g i o, *)
(*         IsWellDefined sitpn -> *)
(*         NoDupA Peq pls -> *)
(*         InA Peq p pls -> *)
(*         InA Pkeq (p, id__p) (p2pdi (γ s')) -> *)
(*         InCs (cs_comp id__p Petri.place_id gm ipm opm) (beh s') -> *)
(*         NoDupA Peq (fs (plmap (arch s))) -> *)
(*         ~(exists p1 id__p1, InA Pkeq (p1, id__p1) (p2pdi (γ s)) /\ id__p1 >= nextid s) -> *)
(*         ~(exists id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) (beh s) /\ id__c >= nextid s) -> *)
(*         InA Pkeq (p, (g, i, o)) (plmap (arch s)) -> *)
(*         List.In (initial_marking, inl (e_nat (M0 p))) i -> *)
(*         NoDupA Peq (fs (p2pdi (γ s))) -> *)
(*         (forall p, InA Peq p pls -> ~InA Peq p (fs (p2pdi (γ s)))) -> *)
(*         List.In (associp_ ($initial_marking) (@M0 sitpn p)) ipm. *)
(*   Proof. *)
(*     intros until pls; *)
(*       functional induction (iter (generate_place_comp_inst sitpn) pls) using iter_ind; *)
(*       try (solve [inversion 4]). *)
(*     intros s v s' e; monadInv e; intros *; intros IWD_sitpn NoDupA_pls. *)
(*     inversion_clear 1. *)

(*     (* CASE [Peq p b] *) *)
(*     erewrite (wi_M0 (wi_funs IWD_sitpn)); eauto. *)
(*     intros; eapply @gen_pcomp_inst_bind_init_marking *)
(*               with (p := b) (g := g) (o := o); *)
(*       eauto with setoidl. *)
(*     (* SUBCASE [∄ comp((nextid s0),...) ∈ (beh s0)] *) *)
(*     destruct 1 as (id__e, (g0, (i0, (o0, InCs_behs0)))). *)
(*     eapply iter_gen_pcomp_inst_inv_nextid_1; eauto. *)
(*     exists (nextid s0), id__e, g0, i0, o0; auto. *)
(*     (* SUBCASE [(b, (g, i, o)) ∈ (plmap (arch s0))] *) *)
(*     erewrite <- iter_gen_pcomp_inst_inv_arch; eauto with setoidl. *)
(*     (* SUBCASE [NoDupA Peq (fs (plmap (arch s0)))] *) *)
(*     erewrite <- iter_gen_pcomp_inst_inv_arch; eauto with setoidl. *)
(*     (* SUBCASE [NoDupA Peq (fs (p2pdi (γ s0)))] *) *)
(*     eapply iter_gen_pcomp_inst_nodup_p2pdi; eauto with setoidl. *)
    
(*     (* CASE [p ∈ tl] *) *)
(*     intros; eapply IHm with (s' := s0) (id__p := id__p) (gm := gm) (opm := opm); *)
(*       eauto with setoidl; inversion NoDupA_pls; subst. *)
(*     all : eapply gen_pcomp_inst_inv_p_comp_2; eauto with setoidl; *)
(*       eapply iter_gen_pcomp_inst_inv_nextid_2; eauto. *)
(*   Qed. *)

(*   Lemma gen_p_comp_insts_p_comp : *)
(*     forall {sitpn s v s'}, *)
(*       generate_place_comp_insts sitpn s = OK v s' -> *)
(*       Sig_in_List (lofPs s) -> *)
(*       forall p, exists id__p gm ipm opm, *)
(*           InA Pkeq (p, id__p) (p2pdi (γ s')) /\ *)
(*           InCs (cs_comp id__p Petri.place_id gm ipm opm) (beh s'). *)
(*   Proof. *)
(*     intros until s'; intros e; minv e; intros SIL p. *)
(*     eapply iter_gen_p_comp_inst_p_comp; eauto; *)
(*       [ apply (proj2 SIL) | apply ((proj1 SIL) p)]. *)
(*   Qed. *)
  
(*   Lemma gen_pcomp_insts_bind_init_marking : *)
(*     forall {sitpn s v s'}, *)
(*       generate_place_comp_insts sitpn s = OK v s' -> *)
(*       IsWellDefined sitpn -> *)
(*       Sig_in_List (lofPs s) -> *)
(*       NoDupA Peq (fs (plmap (arch s))) -> *)
(*       NoDupA Peq (fs (p2pdi (γ s))) -> *)
(*       (forall p, InA Peq p (lofPs s) -> ~ InA Peq p (fs (p2pdi (γ s)))) -> *)
(*       ~(exists p id__p, InA Pkeq (p, id__p) (p2pdi (γ s)) /\ id__p >= nextid s) -> *)
(*       ~(exists id__c id__e gm ipm opm, *)
(*            InCs (cs_comp id__c id__e gm ipm opm) (beh s) /\ id__c >= nextid s) -> *)
(*       forall p id__p gm ipm opm g i o, *)
(*         InA Pkeq (p, id__p) (p2pdi (γ s')) -> *)
(*         InA Pkeq (p, (g, i, o)) (plmap (arch s)) -> *)
(*         List.In (initial_marking, inl (e_nat (M0 p))) i -> *)
(*         InCs (cs_comp id__p Petri.place_id gm ipm opm) (beh s') -> *)
(*         List.In (associp_ ($initial_marking) (@M0 sitpn p)) ipm. *)
(*   Proof. *)
(*     intros until s'; intros e; minv e. *)
(*     intros IWD_sitpn SIL_lofPs; intros. *)
(*     eapply iter_gen_pcomp_inst_bind_init_marking; eauto; *)
(*       destruct SIL_lofPs; auto. *)
(*   Qed. *)
  
(* End GeneratePlaceCompInst. *)

(** ** Facts about Generation of T Component Instances *)

(* Section GenerateTransCompInst. *)

(*   Lemma gen_tcomp_inst_t_comp : *)
(*     forall {sitpn} {t : T sitpn} {s v s'}, *)
(*       generate_trans_comp_inst sitpn t s = OK v s' -> *)
(*       exists id__t gm ipm opm, *)
(*         InA Tkeq (t, id__t) (t2tdi (γ s')) *)
(*         /\ InCs (cs_comp id__t Petri.trans_id gm ipm opm) (beh s'). *)
(*   Proof. *)
(*     intros until s'; intros e; minv e. *)
(*     exists (nextid s0), g, x0, x2; split; eauto with setoidl. *)
(*   Qed. *)

(*   Lemma iter_gen_tcomp_inst_t_comp : *)
(*     forall {sitpn trs} {s v s'}, *)
(*       iter (generate_trans_comp_inst sitpn) trs s = OK v s' -> *)
(*       NoDupA Teq trs -> *)
(*       forall t, InA Teq t trs -> *)
(*                 exists id__t gm ipm opm, *)
(*                   InA Tkeq (t, id__t) (t2tdi (γ s')) /\ *)
(*                   InCs (cs_comp id__t Petri.trans_id gm ipm opm) (beh s'). *)
(*   Proof. *)
(*     intros until trs; *)
(*       functional induction (iter (generate_trans_comp_inst sitpn) trs) using iter_ind. *)

(*     (* BASE CASE *) *)
(*     - inversion 3. *)

(*     (* IND. CASE *) *)
(*     - intros *; intros e NoDupA_trs t; *)
(*         inversion_clear 1 as [ e1 e2 Teq_tb | e1 e2 InA_tl ]; monadInv e. *)

(*       (* CASE [Teq t b] *) *)
(*       + edestruct (@gen_tcomp_inst_t_comp sitpn) as (id__t, (gm, (ipm, (opm, (InA_t2tdi, InCs_))))); *)
(*           eauto. *)
(*         exists id__t, gm, ipm, opm; split; eauto with setoidl. *)

(*       (* CASE [t ∈ tl] *) *)
(*       + edestruct (IHm s x s0) as (id__t, (gm, (ipm, (opm, (InA_t2tdi, InCs_))))); *)
(*           eauto with setoidl. *)
(*         exists id__t, gm, ipm, opm; eapply gen_tcomp_inst_inv_t_comp_1; eauto. *)
(*         inversion NoDupA_trs; eauto with setoidl. *)
(*   Qed. *)

(*   Lemma gen_tcomp_insts_t_comp : *)
(*     forall {sitpn : Sitpn} {s : Sitpn2HVhdlState sitpn} {v : unit} {s' : Sitpn2HVhdlState sitpn}, *)
(*       generate_trans_comp_insts sitpn s = OK v s' -> *)
(*       Sig_in_List (lofTs s) -> *)
(*       forall t, *)
(*       exists id__t gm ipm opm, *)
(*         InA Tkeq (t, id__t) (t2tdi (γ s')) /\ InCs (cs_comp id__t Petri.trans_id gm ipm opm) (beh s'). *)
(*   Proof. *)
(*     intros *; intros e; minv e; intros SIL t. *)
(*     eapply iter_gen_tcomp_inst_t_comp; eauto; *)
(*       [ apply (proj2 SIL) | apply ((proj1 SIL) t)]. *)
(*   Qed. *)
  
(* End GenerateTransCompInst. *)

(** ** Facts about SITPN-to-H-VHDL transformation function *)

Section Sitpn2HVhdl.
    
  (* Lemma gen_comp_insts_t_comp : *)
  (*   forall {sitpn s v s'}, *)
  (*     generate_comp_insts sitpn s = OK v s' -> *)
  (*     Sig_in_List (lofTs s) -> *)
  (*     forall t, exists id__t gm ipm opm, *)
  (*         InA Tkeq (t, id__t) (t2tdi (γ s')) /\ *)
  (*         InCs (cs_comp id__t Petri.trans_id gm ipm opm) (beh s'). *)
  (* Proof. *)
  (*   intros *; intros e; monadInv e; intros SIL t. *)
  (*   eapply gen_tcomp_insts_t_comp; eauto. *)
  (*   erewrite <- gen_pcomp_insts_inv_lofTs; eauto. *)
  (* Qed. *)

  (* Lemma gen_comp_insts_p_comp : *)
  (*   forall {sitpn s v s'}, *)
  (*     generate_comp_insts sitpn s = OK v s' -> *)
  (*     Sig_in_List (lofPs s) -> *)
  (*     forall p, exists id__p gm ipm opm, *)
  (*         InA Pkeq (p, id__p) (p2pdi (γ s')) /\ *)
  (*         InCs (cs_comp id__p Petri.place_id gm ipm opm) (beh s'). *)
  (* Proof. *)
  (*   intros until s'; intros e; monadInv e; intros Hsil p. *)
  (*   specialize (gen_p_comp_insts_p_comp EQ Hsil p) *)
  (*     as (id__p, (gm, (ipm, (opm, (Hin_γs0, Hin_behs0))))). *)
  (*   exists id__p, gm, ipm, opm. *)
  (*   eapply gen_tcomp_insts_inv_p_comp; eauto. *)
  (* Qed. *)
  
  (* Lemma gen_comp_insts_bind_init_marking : *)
  (*   forall {sitpn s v s'}, *)
  (*     generate_comp_insts sitpn s = OK v s' -> *)
  (*     IsWellDefined sitpn -> *)
  (*     Sig_in_List (lofPs s) -> *)
  (*     NoDupA Peq (fs (plmap (arch s))) -> *)
  (*     NoDupA Peq (fs (p2pdi (γ s))) -> *)
  (*     (forall p, InA Peq p (lofPs s) -> ~ InA Peq p (fs (p2pdi (γ s)))) -> *)
  (*     ~(exists p id__p, InA Pkeq (p, id__p) (p2pdi (γ s)) /\ id__p >= nextid s) -> *)
  (*     ~(exists id__c id__e gm ipm opm, *)
  (*          InCs (cs_comp id__c id__e gm ipm opm) (beh s) /\ id__c >= nextid s) -> *)
  (*     forall p id__p gm ipm opm g i o, *)
  (*       InA Pkeq (p, id__p) (p2pdi (γ s')) -> *)
  (*       InA Pkeq (p, (g, i, o)) (plmap (arch s)) -> *)
  (*       List.In (initial_marking, inl (e_nat (M0 p))) i -> *)
  (*       InCs (cs_comp id__p Petri.place_id gm ipm opm) (beh s') -> *)
  (*       List.In (associp_ ($initial_marking) (@M0 sitpn p)) ipm. *)
  (* Proof. *)
  (*   intros *; intros e; monadInv e; intros. *)
  (*   eapply gen_pcomp_insts_bind_init_marking; eauto.     *)
  (*   erewrite gen_tcomp_insts_inv_p2pdi; eauto. *)
  (*   eapply gen_tcomp_insts_gen_only_tcomp; eauto. *)
  (*   discriminate. *)
  (* Qed. *)

  (* Lemma sitpn2hvhdl_nodup_t2tdi : *)
  (*   forall {sitpn b d γ},     *)
  (*     sitpn2hvhdl sitpn b = (inl (d, γ)) -> *)
  (*     IsWellDefined sitpn -> *)
  (*     NoDupA Teq (fs (t2tdi γ)). *)
  (* Proof. *)
  (*   intros until mm;   *)
  (*     functional induction (sitpn2hvhdl sitpn b) *)
  (*                using sitpn2hvhdl_ind; (try (solve [inversion 1])). *)
  (*   intros *; intros e1 IWD; monadInv e. *)
  (*   minv EQ4; inversion_clear e1.     *)
  (*   eapply gen_comp_insts_nodup_t2tdi; eauto. *)
  (*   2, 3: rewrite <- (gen_ports_inv_t2tdi EQ0), *)
  (*         <- (gen_arch_inv_γ EQ1), *)
  (*         <- (gen_sitpn_infos_inv_γ EQ); *)
  (*     simpl; (inversion 1 || apply NoDupA_nil). *)
  (*   rewrite <- (gen_ports_inv_lofTs EQ0), *)
  (*   <- (gen_arch_inv_lofTs EQ1). *)
  (*   apply (gen_sitpn_infos_sil_lofTs EQ (nodup_trs (wi_fsets IWD))).           *)
  (* Qed. *)
  
  (* Lemma sitpn2hvhdl_nodup_p2pdi : *)
  (*   forall {sitpn b d γ},     *)
  (*     (* [sitpn] translates into [(d, γ)]. *) *)
  (*     sitpn2hvhdl sitpn b = (inl (d, γ)) -> *)
  (*     IsWellDefined sitpn -> *)
  (*     NoDupA Peq (fs (p2pdi γ)). *)
  (* Proof. *)
  (*   intros until mm;   *)
  (*     functional induction (sitpn2hvhdl sitpn b) *)
  (*                using sitpn2hvhdl_ind.   *)
  (*   (* Error *) *)
  (*   inversion 1. *)
  (*   (* OK *) *)
  (*   intros; monadInv e. *)
  (*   minv EQ4; inversion H; clear H; subst; simpl. *)
  (*   eapply gen_comp_insts_nodup_p2pdi; eauto. *)
  (*   2, 3: rewrite <- (gen_ports_inv_p2pdi EQ0), *)
  (*         <- (gen_arch_inv_γ EQ1), *)
  (*         <- (gen_sitpn_infos_inv_γ EQ); *)
  (*     simpl; (inversion 1 || apply NoDupA_nil). *)
  (*   rewrite <- (gen_ports_inv_lofPs EQ0), *)
  (*   <- (gen_arch_inv_lofPs EQ1). *)
  (*   lazymatch goal with *)
  (*   | [ Hwd: IsWellDefined _ |- _ ] => *)
  (*     apply (gen_sitpn_infos_sil_lofPs EQ (nodup_pls (wi_fsets Hwd))) *)
  (*   end. *)
  (* Qed. *)
  
  Lemma sitpn2hvhdl_pdi_ex :
    forall sitpn b d γ,
      sitpn2hvhdl sitpn b = (inl (d, γ)) ->
      IsWellDefined sitpn ->
      forall p, exists id__p g__p i__p o__p,
          InA Pkeq (p, id__p) (p2pdi γ)
          /\ InCs (cs_comp id__p Petri.place_id g__p i__p o__p) (AbstractSyntax.beh d).
  Proof.
    intros. 
    functional induction (sitpn2hvhdl sitpn b) using sitpn2hvhdl_ind.
    
    (* Error *)
    lazymatch goal with
    | [ H: inr _ = inl _ |- _ ] => inversion H
    end.

    (* OK *)
    monadInv e.
    match goal with
    | [ H: generate_design_and_binder _ _ = OK _ _ |- _ ] =>
        minv H
    end.

    lazymatch goal with
    | [ H: inl _ = inl _ |- _ ] =>
        inversion H; clear H; subst; simpl
    end.
    
    eapply gen_ports_pdi_ex; eauto.
    eapply gen_inter_pdi_ex; eauto; [
        (* [NoDup cids] and [all id__c < nextid]  *)
        eapply gen_archi_nodup_cids; eauto;
        erewrite <- (gen_sitpn_infos_inv_beh EQ); eauto; cbn;
        [ destruct 1 | constructor ]
      | ].

    eapply gen_archi_pdi_ex; eauto.
    lazymatch goal with
    | [ Hwd: IsWellDefined _ |- _ ] =>
        apply (gen_sitpn_infos_sil_lofPs EQ)
    end.
  Qed.

  Lemma sitpn2hvhdl_t_comp :
    forall sitpn b d γ,
      sitpn2hvhdl sitpn b = (inl (d, γ)) ->
      IsWellDefined sitpn ->
      forall t, exists id__t gm ipm opm,
          InA Tkeq (t, id__t) (t2tdi γ)
          /\ InCs (cs_comp id__t Petri.trans_id gm ipm opm) (AbstractSyntax.beh d).
  Proof.
    (*   intros *.  *)
    (*   functional induction (sitpn2hvhdl sitpn b) using sitpn2hvhdl_ind. *)

    (*   (* ERROR CASE *) *)
    (*   inversion 1. *)

    (*   (* OK CASE *) *)
    (*   monadInv e. *)
    (*   minv EQ4; intros e IWD; inject_left e; cbn. *)
    (*   eapply gen_comp_insts_t_comp; eauto. *)

    (*   (* Prove [Sig_in_List (lofTs s1)] *) *)
    (*   rewrite <- (gen_ports_inv_lofTs EQ0), *)
    (*   <- (gen_arch_inv_lofTs EQ1). *)
    (*   apply (gen_sitpn_infos_sil_lofTs EQ (nodup_trs (wi_fsets IWD))). *)
    (* Qed. *)
  Admitted.    
  
  Lemma sitpn2hvhdl_bind_init_marking :
    forall sitpn b d γ,
      (* [sitpn] translates into [(d, γ)]. *)
      sitpn2hvhdl sitpn b = (inl (d, γ)) ->
      IsWellDefined sitpn ->
      forall p id__p gm ipm opm,
        InA Pkeq (p, id__p) (p2pdi γ) ->
        InCs (cs_comp id__p Petri.place_id gm ipm opm) (AbstractSyntax.beh d) ->
        List.In (ipa_ ($initial_marking) (@M0 sitpn p)) ipm.
  Proof.
    (*   intros until mm;   *)
    (*     functional induction (sitpn2hvhdl sitpn b) *)
    (*                using sitpn2hvhdl_ind. *)
    
    (*   (* Error *) *)
    (*   inversion 1. *)

    (*   (* OK *) *)
    (*   do 3 intro; intros IWD_sitpn; intros; monadInv e. *)
    (*   minv EQ4; inversion H; clear H; subst; simpl. *)

  (*   (* Builds [InA Peq (p, (g, i, o)) (plmap (arch s0))], *)
   (*      and [InA Peq (p, (g, i, o')) (plmap (arch s1))] *) *)
    (*   edestruct @gen_arch_pcomp with (p := p) as (g, (i, (o, InA_plmap0))); eauto. *)
    (*   eapply gen_sitpn_infos_sil_lofPs; eauto. *)
    (*   exact (nodup_pls (wi_fsets IWD_sitpn)). *)
    (*   edestruct @gen_ports_inv_plmap with (p := p) as (o', InA_plmap1); eauto. *)
    (*   eapply gen_arch_sil_plmap; eauto. *)
    (*   eapply gen_sitpn_infos_sil_lofPs; eauto. *)
    (*   exact (nodup_pls (wi_fsets IWD_sitpn)). *)
    (*   erewrite <- gen_sitpn_infos_inv_arch; eauto; cbn; inversion 1. *)
    (*   erewrite <- gen_sitpn_infos_inv_arch; eauto; cbn; auto. *)
    
  (*   (* Apply gen_comp_insts_bind_init_marking, solve the generated *)
   (*      subgoals. *) *)
    (*   eapply gen_comp_insts_bind_init_marking; eauto. *)

    (*   (* SUBGOAL Sig_in_List (lofPs s1) *) *)
    (*   erewrite <- gen_ports_inv_lofPs; eauto. *)
    (*   erewrite <- gen_arch_inv_lofPs; eauto. *)
    (*   eapply gen_sitpn_infos_sil_lofPs; eauto. *)
    (*   exact (nodup_pls (wi_fsets IWD_sitpn)). *)

    (*   (* SUBGOAL [NoDupA Peq (fs (plmap (arch s1)))] *) *)
    (*   eapply gen_ports_inv_sil_plmap; eauto. *)
    (*   eapply gen_arch_sil_plmap; eauto. *)
    (*   eapply gen_sitpn_infos_sil_lofPs; eauto. *)
    (*   exact (nodup_pls (wi_fsets IWD_sitpn)). *)
    (*   erewrite <- gen_sitpn_infos_inv_arch; eauto; cbn; inversion 1. *)
    (*   erewrite <- gen_sitpn_infos_inv_arch; eauto; cbn; auto. *)

    (*   (* SUBGOAL [NoDupA Peq (fs (p2pdi (γ s1)))] *) *)
    (*   1, 2: erewrite <- gen_ports_inv_p2pdi; eauto; *)
    (*     erewrite <- gen_arch_inv_γ; eauto; *)
    (*       erewrite <- gen_sitpn_infos_inv_γ; eauto; *)
    (*          (cbn; eapply NoDupA_nil || inversion 2). *)

    (*   (* SUBGOAL [∄ (p, id__p) ∈ (p2pdi (γ s)) s.t. id__p >= nextid s1] *) *)
    (*   erewrite <- gen_ports_inv_p2pdi; eauto. *)
    (*   erewrite <- gen_arch_inv_γ; eauto. *)
    (*   erewrite <- gen_sitpn_infos_inv_γ; eauto. *)
    (*   simpl; destruct 1 as (p1, (id__p1, (InA_, _))); inversion InA_. *)
    
    (*   (* SUBGOAL [∄ comp(id__c, id__e, gm, ipm, opm) ∈ (beh s1) /\ id__c >= nextid s1] *) *)
    (*   destruct 1 as (id__c, (id__e, (gm0, (ipm0, (opm0, (InCs_beh, GE_id__c)))))). *)
    (*   eapply gen_ports_inv_no_comps_in_beh; eauto. *)
    (*   erewrite <- gen_arch_inv_beh; eauto. *)
    (*   erewrite <- gen_sitpn_infos_inv_beh; eauto; cbn. *)
    (*   destruct 1 as (id__c1, (id__e1, (gm1, (ipm1, (opm1, e))))); inversion e. *)
    (*   exists id__c, id__e, gm0, ipm0, opm0; auto. *)
    
    (*   (* SUBGOAL [(initial_marking, inl (M0 p)) ∈ i] *) *)
    (*   eapply gen_arch_bind_init_marking; eauto. *)
    (*   eapply gen_sitpn_infos_sil_lofPs; eauto. *)
    (*   exact (nodup_pls (wi_fsets IWD_sitpn)). *)
    (*   erewrite <- gen_sitpn_infos_inv_arch; eauto; cbn; auto. *)
    (*   inversion 1. *)
    (* Qed. *)
  Admitted.
  
  Lemma sitpn2hvhdl_emp_pinputs_rt :
    forall {sitpn b d γ},
      sitpn2hvhdl sitpn b = (inl (d, γ)) ->
      IsWellDefined sitpn ->
      forall t id__t gm ipm opm,
        InA Tkeq (t, id__t) (t2tdi γ) ->
        InCs (cs_comp id__t Petri.trans_id gm ipm opm) (AbstractSyntax.beh d) ->
        PInputsOf t [] ->
        List.In (ipa_ (Transition.reinit_time $[[0]]) false) ipm.
  Admitted.

  Lemma sitpn2hvhdl_emp_pinputs_in_arcs_nb :
    forall {sitpn b d γ},
      sitpn2hvhdl sitpn b = (inl (d, γ)) ->
      IsWellDefined sitpn ->
      forall t id__t gm ipm opm,
        InA Tkeq (t, id__t) (t2tdi γ) ->
        InCs (cs_comp id__t Petri.trans_id gm ipm opm) (AbstractSyntax.beh d) ->
        PInputsOf t [] ->
        List.In (ga_ Transition.input_arcs_number 1) gm.
  Admitted.

  Lemma sitpn2hvhdl_connect_rtt_rt :
    forall {sitpn b d γ},
      sitpn2hvhdl sitpn b = (inl (d, γ)) ->
      IsWellDefined sitpn ->
      forall t id__t gm__t ipm__t opm__t p id__p gm__p ipm__p opm__p pinputs_of_t toutputs_of_p,
        @pre sitpn p t <> None ->
        PInputsOf t pinputs_of_t ->
        TOutputsOf p toutputs_of_p ->
        InA Tkeq (t, id__t) (t2tdi γ) ->
        InCs (cs_comp id__t Petri.trans_id gm__t ipm__t opm__t) (AbstractSyntax.beh d) ->
        InA Pkeq (p, id__p) (p2pdi γ) ->
        InCs (cs_comp id__p Petri.place_id gm__p ipm__p opm__p) (AbstractSyntax.beh d) ->
        exists i j id__ji,
          0 <= i < length pinputs_of_t
          /\ 0 <= j < length toutputs_of_p
          /\ List.In (opa_idx Place.reinit_transitions_time (e_nat j) ($id__ji)) opm__p
          /\ List.In (ipa_ (Transition.reinit_time $[[(e_nat i)]]) (#id__ji)) ipm__t.    
  Admitted.

  Lemma sitpn2hvhdl_nemp_pinputs_in_arcs_nb :
    forall {sitpn b d γ},
      sitpn2hvhdl sitpn b = (inl (d, γ)) ->
      IsWellDefined sitpn ->
      forall t id__t gm ipm opm pinputs_of_t,
        InA Tkeq (t, id__t) (t2tdi γ) ->
        InCs (cs_comp id__t Petri.trans_id gm ipm opm) (AbstractSyntax.beh d) ->
        PInputsOf t pinputs_of_t ->
        length pinputs_of_t <> 0 ->
        List.In (ga_ Transition.input_arcs_number (length pinputs_of_t)) gm.
  Admitted.

  Lemma sitpn2hvhdl_nemp_toutputs_out_arcs_nb :
    forall {sitpn b d γ},
      sitpn2hvhdl sitpn b = (inl (d, γ)) ->
      IsWellDefined sitpn ->
      forall p id__p gm ipm opm toutputs_of_p,
        InA Pkeq (p, id__p) (p2pdi γ) ->
        InCs (cs_comp id__p Petri.place_id gm ipm opm) (AbstractSyntax.beh d) ->
        TOutputsOf p toutputs_of_p ->
        length toutputs_of_p <> 0 ->
        List.In (ga_ Place.output_arcs_number (length toutputs_of_p)) gm.
  Admitted.
  
End Sitpn2HVhdl.
