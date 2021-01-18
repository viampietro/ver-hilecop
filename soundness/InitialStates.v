(** * Similar Initial States *)

Require Import String.
Require Import common.Coqlib.
Require Import common.InAndNoDup.
Require Import common.NatMap.
Require Import common.FstSplit.
Require Import common.GlobalFacts.
Require Import common.SetoidListFacts.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import ListPlus.
Require Import common.ListMonad.
Require Import common.ListMonadFacts.
Require Import common.ListDep.

Require Import sitpn.dp.Sitpn.
Require Import sitpn.dp.SitpnTypes.
Require Import sitpn.dp.SitpnSemanticsDefs.
Require Import sitpn.dp.SitpnSemantics.
Require Import sitpn.dp.SitpnFacts.
Require Import sitpn.dp.SitpnWellDefined.
Require Import sitpn.dp.SitpnWellDefinedTactics.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.AbstractSyntaxTactics.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.Initialization.
Require Import hvhdl.Environment.
Require Import hvhdl.Place.
Require Import hvhdl.ExpressionEvaluation.

Require Import sitpn2hvhdl.Sitpn2HVhdl.
Require Import sitpn2hvhdl.GenerateHVhdlFacts.

Require Import soundness.SoundnessDefs.

(** ** Initial States Equal Marking Lemma *)    

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

Lemma titer_gen_p_comp_inst_inv_nodup_p2pcomp :
  forall {sitpn pls} {Inpls2P : forall n : nat, List.In n pls -> P sitpn} {s v s'},
    titer (generate_place_comp_inst sitpn) pls Inpls2P s = OK v s' ->
    (forall x pfx, x = proj1_sig (Inpls2P x pfx)) ->
    forall p,
      ~InA Peq p (fs (p2pcomp (γ s))) ->
      ~List.In (proj1_sig p) pls ->
      ~InA Peq p (fs (p2pcomp (γ s'))).
Admitted.

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

Lemma gen_sitpn_infos_inv_p2pcomp :
  forall {sitpn decpr s v s'},
    generate_sitpn_infos sitpn decpr s = OK v s' ->
    p2pcomp (γ s) = p2pcomp (γ s').
Admitted.

Lemma gen_arch_inv_p2pcomp :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    p2pcomp (γ s) = p2pcomp (γ s').
Admitted.

Lemma gen_ports_inv_p2pcomp :
  forall {sitpn s v s'},
    @generate_ports sitpn s = OK v s' ->
    p2pcomp (γ s) = p2pcomp (γ s').
Admitted.

Lemma sitpn2hvhdl_nodup_p2pcomp :
  forall {sitpn decpr id__ent id__arch mm d γ},    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    IsWellDefined sitpn ->
    NoDupA Peq (fs (p2pcomp γ)).
Proof.
  intros until mm;  
    functional induction (sitpn_to_hvhdl sitpn decpr id__ent id__arch mm) using sitpn_to_hvhdl_ind.
  
  (* Error *)
  inversion 1.

  (* OK *)
  intros; monadInv e.
  lazymatch goal with
  | [ H: inl _ = inl _, Hwd: IsWellDefined _ |- _ ] =>
    let NoDupPlaces := (get_nodup_places Hwd) in
    monadFullInv EQ4; inversion H; subst; simpl;
      eapply (gen_comp_insts_nodup_p_binder EQ2 NoDupPlaces);
      rewrite <- (gen_ports_inv_p2pcomp EQ0);
      rewrite <- (gen_arch_inv_p2pcomp EQ1);
      rewrite <- (gen_sitpn_infos_inv_p2pcomp EQ);
      simpl; apply NoDupA_nil
  end.
Qed.

(* Lemma sitpn2hvhdl_bind_init_marking : *)
(*   forall {sitpn decpr id__ent id__arch mm d γ}, *)
(*     (* [sitpn] translates into [(d, γ)]. *) *)
(*     sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) -> *)
(*     forall p id__p gm ipm opm, *)
(*       InA Pkeq (p, id__p) (p2pcomp γ) -> *)
(*       InCs (cs_comp id__p Petri.place_entid gm ipm opm) (behavior d) -> *)
(*       List.In (associp_ ($initial_marking) (@M0 sitpn p)) ipm. *)
(* Admitted. *)

(* Lemma sitpn2hvhdl_γp : *)
(*   forall {sitpn decpr id__ent id__arch mm d γ}, *)
(*     (* [sitpn] translates into [(d, γ)]. *) *)
(*     sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) -> *)
(*     IsWellDefined sitpn -> *)
(*     forall p, exists id__p, InA Pkeq (p, id__p) (p2pcomp γ). *)
(* Proof. *)
(*   intros *; intros Hs2h Hwd p; *)
(*     specialize (sitpn2hvhdl_p_comp Hs2h Hwd p) as Hex. *)
(*   inversion_clear Hex as (id__p, (gm, (ipm, (opm, (HinA, H))))). *)
(*   exists id__p; assumption. *)
(* Qed. *)

Lemma init_s_marking_eq_init_marking :
  forall Δ σ behavior σ0,
    init hdstore Δ σ behavior σ0 ->
    forall id__p gm ipm opm σ__p0 v,
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) behavior ->
      NatMap.MapsTo id__p σ__p0 (compstore σ0) ->
      NatMap.MapsTo Place.initial_marking v (sigstore σ__p0) ->
      NatMap.MapsTo Place.s_marking v (sigstore σ__p0).
Admitted.

Lemma init_init_marking_eq_M0 :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ σ0,
    init hdstore Δ σ (behavior d) σ0 ->
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
  
    forall p id__p gm ipm opm σ__p0,
      InA Pkeq (p, id__p) (p2pcomp γ) ->
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (behavior d) ->
      NatMap.MapsTo id__p σ__p0 (compstore σ0) ->
      NatMap.MapsTo Place.initial_marking (Vnat (M0 p)) (sigstore σ__p0).
Admitted.

Ltac rw_γp p id__p id__p' :=
  lazymatch type of p with
  | P _ =>
    let tpp := (type of p) in
    lazymatch goal with
    | [ H: sitpn_to_hvhdl ?sitpn _ _ _ _ = inl (_, ?γ), Hwd: IsWellDefined ?sitpn |- _ ] =>
      specialize (sitpn2hvhdl_nodup_p2pcomp H Hwd); intros Hnodup_p2pcomp;
      lazymatch goal with
      | [ H: InA _ (p, id__p) (p2pcomp γ), H': InA _ (p, id__p') (p2pcomp γ) |- _ ] =>
        rewrite <- (NoDupA_fs_eqk_eq (P sitpn) (Equivalence_Peq sitpn) Hnodup_p2pcomp H H');
        clear Hnodup_p2pcomp
      end
    | _ => fail "Found no term of type (sitpn_to_hvhdl ?sitpn ?decpr ?id__ent ?id__arch ?mm = inl (?d, ?γ))"
    end
  | _ =>
    let tpp := (type of p) in
    fail "Term" p "is of type" tpp
         "while it is expected to be of type P ?sitpn" 
  end.

Lemma init_states_eq_marking :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (empty value) d Δ σ__e ->

    (* initialization d's state. *)
    init hdstore Δ σ__e (behavior d) σ0 ->

    forall p id__p σ__p0,
      (* [id__p] is the identifier of the place component associated with
         place [p] by the [γ] binder. *)
      InA Pkeq (p, id__p) (p2pcomp γ) ->

      (* [σ__p] is the current state of component [id__p] is the global
         design state [σ]. *)
      MapsTo id__p σ__p0 (compstore σ0) ->

      (* Marking of place [p] at state [s] equals value of signal
         [s_marking] at state [σ__p]. *)
      MapsTo Place.s_marking (Vnat (M (s0 sitpn) p)) (sigstore σ__p0).
Proof.
  intros.
  
  (* Builds [comp(id__p', "place", gm, ipm, opm) ∈ (behavior d)] *)
  lazymatch goal with
  | [ Hs2h: sitpn_to_hvhdl _ _ _ _ _ = _, Hwd: IsWellDefined _ |- _ ] =>
    specialize (sitpn2hvhdl_p_comp Hs2h Hwd p) as Hex;
      inversion_clear Hex as (id__p', (gm, (ipm, (opm, (Hγ, Hincs_comp)))));
      rename H into Hsitpn2hvhdl
  end.

  (* To prove [σ__p0("s_marking") = M0(p)], then prove
     [σ__p0("initial_marking") = M0(p)] *)
  eapply init_s_marking_eq_init_marking; eauto.  
  rw_γp p id__p id__p'; assumption.

  (* To prove [σ__p0("initial_marking") = M0(p)], then prove *)
  eapply init_init_marking_eq_M0; eauto.
  rw_γp p id__p id__p'; assumption.    
Qed.

(** ** Similar Initial States Lemma *)

Lemma sim_init_states :
  forall sitpn decpr id__ent id__arch mm d γ Δ σ__e σ0,

    (* [sitpn] is well-defined. *)
    IsWellDefined sitpn ->
    
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (empty value) d Δ σ__e ->

    (* initialization d's state. *)
    init hdstore Δ σ__e (behavior d) σ0 ->

    (* init states are similar *)
    γ ⊢ (s0 sitpn) ∼ σ0.
Proof.
  intros; unfold SimState. split.
  eapply init_states_eq_marking; eauto.
Admitted.

Hint Resolve sim_init_states : core.
