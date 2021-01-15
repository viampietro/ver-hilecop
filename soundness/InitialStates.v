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

Require Import soundness.SoundnessDefs.

(** ** Initial States Equal Marking Lemma *)

Functional Scheme getv_ind := Induction for getv Sort Prop.

Lemma getv_idle :
  forall {state A B : Type} {eqk}
         {eqk_dec : forall x y, {eqk x y} + {~eqk x y}}
         {x : A} {l : list (A * B)} {s : state} {v s'},
    getv eqk_dec x l s = OK v s' ->
    s = s'.
Proof.
  intros until s.
  functional induction (@getv state A B eqk eqk_dec x l) using getv_ind;
    intros v s' e; (try monadInv e; auto || eapply IHm; eauto).
Qed.

Hint Resolve getv_idle : listmonad.

Lemma foldl_idle :
  forall {state A B : Type} {f : B -> A -> Mon B} {l b0} {s : state} {v s'},
    fold_left f l b0 s = OK v s' ->
    (forall b a s0 v0 s0', f b a s0 = OK v0 s0' -> s0 = s0') ->
    s = s'.
Proof.
  induction l; simpl; intros b0 s v s' e; monadInv e; intros f_idle.
  auto.
  apply IHl with (b0 := x) (v := v); auto.
  rewrite <- (f_idle b0 a s x s0 EQ) in EQ0; assumption.
Qed.

Lemma imap_entry_to_associp_idle :
  forall {sitpn im ime s v s'},
    imap_entry_to_associp sitpn im ime s = OK v s' ->
    s = s'.
Proof.
  unfold imap_entry_to_associp.
  destruct ime; destruct s; intros s v s' e1; monadFullInv e1;
  [ auto | destruct l; monadFullInv EQ; auto ].
Qed.

Lemma omap_entry_to_assocop_idle :
  forall {sitpn om ome s v s'},
    omap_entry_to_assocop sitpn om ome s = OK v s' ->
    s = s'.
Proof.
  unfold omap_entry_to_assocop.
  destruct ome; destruct s; intros s v s' e1; monadFullInv e1;
    [ auto | destruct l; monadFullInv EQ; auto ].
Qed.

Lemma HComp_to_comp_inst_idle :
  forall {sitpn id__c id__e hcomp s v s'},
    HComponent_to_comp_inst sitpn id__c id__e hcomp s = OK v s' ->
    s = s'.
Proof.
  intros until s'; intros e; destruct hcomp as ((gm, ipm), opm).
  monadFullInv e.
  unfold InputMap_to_AST in EQ; unfold OutputMap_to_AST in EQ1.
  transitivity s0.
  eapply foldl_idle; eauto; intros; eapply imap_entry_to_associp_idle; eauto.
  eapply foldl_idle; eauto; intros; eapply omap_entry_to_assocop_idle; eauto.
Qed.

Lemma gen_p_comp_inst_idle_p_comp :
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
      specialize (getv_idle EQ4) as e1;
      specialize (HComp_to_comp_inst_idle EQ2) as e2;
      rewrite <- e2, <- e1; clear e1 e2; simpl;
        [ apply InA_setv; auto | right; assumption ].
Qed.

Lemma gen_p_comp_inst_p_comp :
  forall {sitpn p s v s'},
    generate_place_comp_inst sitpn p s = OK v s' ->
    exists (id__p : ident) (gm : genmap) (ipm : inputmap) (opm : outputmap),
      InA Pkeq (p, id__p) (p2pcomp (γ s')) /\ InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
Proof.
  intros until s'; intros e; monadFullInv e.
  simpl; simpl in EQ4.
Admitted.

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

      (* Apply gen_p_comp_inst_idle_p_comp *)
      assert (ne_an : a <> n) by (apply (not_in_in_diff (conj Hnotin_a_tl HIn_ntl))).
      assert (ne_proj1 : proj1_sig (pf a (in_eq a tl)) <> proj1_sig (pf n (in_cons a n tl HIn_ntl)))
        by (intros e_proj1; rewrite <- ((proj2 (H1 a n (in_eq a tl) (in_cons a n tl HIn_ntl))) e_proj1) in ne_an;
            contradiction).
      specialize (gen_p_comp_inst_idle_p_comp EQ0 ne_proj1 Hγ Hincs_comp) as (Hγ', Hincs_comp').
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

Lemma gen_t_comp_insts_p_comp :
  forall {sitpn s v s' p id__p gm ipm opm},
    generate_trans_comp_insts sitpn s = OK v s' ->
    InA Pkeq (p, id__p) (p2pcomp (γ s)) ->
    InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s) ->
    InA Pkeq (p, id__p) (p2pcomp (γ s')) /\
    InCs (cs_comp id__p Petri.place_entid gm ipm opm) (beh s').
Admitted.

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
  eapply gen_t_comp_insts_p_comp; eauto.
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

Lemma sitpn2hvhdl_bind_init_marking :
  forall {sitpn decpr id__ent id__arch mm d γ},
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    forall p id__p gm ipm opm,
      InA Pkeq (p, id__p) (p2pcomp γ) ->
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) (behavior d) ->
      List.In (associp_ ($initial_marking) (@M0 sitpn p)) ipm.
Admitted.

Lemma sitpn2hvhdl_γp :
  forall {sitpn decpr id__ent id__arch mm d γ},
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    IsWellDefined sitpn ->
    forall p, exists id__p, InA Pkeq (p, id__p) (p2pcomp γ).
Proof.
  intros *; intros Hs2h Hwd p;
    specialize (sitpn2hvhdl_p_comp Hs2h Hwd p) as Hex.
  inversion_clear Hex as (id__p, (gm, (ipm, (opm, (HinA, H))))).
  exists id__p; assumption.
Qed.

Lemma sitpn2hvhdl_nodup_p_binder :
  forall {sitpn decpr id__ent id__arch mm d γ},
    (* [sitpn] translates into [(d, γ)]. *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->
    NoDupA Peq (fs (p2pcomp γ)).
Admitted.

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
    | [ H: sitpn_to_hvhdl ?sitpn _ _ _ _ = inl (_, ?γ) |- _ ] =>
      specialize (sitpn2hvhdl_nodup_p_binder H); intros Hnodup_p2pcomp;
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
