(** * Facts about Port Elaboration Relations *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.proofs.DefaultValueFacts.
Require Import hvhdl.proofs.EnvironmentFacts.

Lemma EPort_inv_gens :
  forall {Δ σ pd Δ' σ'},
    EPort Δ σ pd Δ' σ' ->
    EqGens Δ Δ'.
Proof.
  inversion_clear 1; unfold EqGens; intros.

  (* 2 CASES, [id = id0 or id <> id0]. *)
  all : specialize (Nat.eq_dec id id0) as Hsum; inversion_clear Hsum as [Heq_id | Hneq_id].
  2, 4:
    split; intros Hmap;
    [ let apply_add_2 sobj := ltac: (apply (NatMap.add_2 sobj Hneq_id Hmap)) in
      (apply_add_2 (Input t0) || apply_add_2 (Output t0))
    | apply (NatMap.add_3 Hneq_id Hmap)
    ].
  1, 2 :
    split; intros Hmap; rewrite Heq_id in *;
    [ 
      elimtype False;
      lazymatch goal with
      | [ H: ~NatMap.In _ _ |- _ ] => 
        apply H; exists (Generic t1 v0); assumption
      end
    | 
    let tac sobj :=
        ltac:(rewrite (add_mapsto_iff Δ id0 id0 sobj (Generic t1 v0)) in Hmap;
              firstorder;
              lazymatch goal with
              | [ Heq_semobj: _ = Generic _ _ |- _ ] =>
                inversion Heq_semobj
              end)
    in tac (Input t0) || tac (Output t0)
    ].
Qed.

#[export] Hint Resolve EPort_inv_gens : hvhdl.

Lemma EPorts_inv_gens :
  forall {Δ σ ports Δ' σ'},
    EPorts Δ σ ports Δ' σ' ->
    EqGens Δ Δ'.
Proof.
  induction 1; [reflexivity | transitivity Δ'; eauto with hvhdl].
Qed.

#[export] Hint Resolve EPorts_inv_gens : hvhdl.

Lemma EPort_inv_sstore :
  forall Δ σ pd Δ' σ' id v,
    EPort Δ σ pd Δ' σ' ->
    MapsTo id v (sstore σ) ->
    MapsTo id v (sstore σ').
Proof.
  inversion_clear 1;
  intros; simpl; apply add_2; auto;
    match goal with
    | [ H: ~InSStore _ _ |- _ ] =>
      intro; subst; apply H; exists v; auto
    end.
Qed.

#[export] Hint Resolve EPort_inv_sstore : hvhdl.

Lemma EPorts_inv_sstore :
  forall Δ σ ports Δ' σ' id v,
    EPorts Δ σ ports Δ' σ' ->
    MapsTo id v (sstore σ) ->
    MapsTo id v (sstore σ').
Proof.
  induction 1; auto; intros.
  apply IHEPorts; eauto with hvhdl.
Qed.

Lemma EPort_inv_Δ :
  forall Δ σ pd Δ' σ' id sobj,
    EPort Δ σ pd Δ' σ' ->
    MapsTo id sobj Δ ->
    MapsTo id sobj Δ'.
Proof.
  inversion_clear 1;
    intros; simpl; apply add_2; auto;
      match goal with
      | [ H: ~NatMap.In _ _ |- _ ] =>
        intro; subst; apply H; exists sobj; auto
      end.
Qed.

#[export] Hint Resolve EPort_inv_Δ : hvhdl.

Lemma EPorts_inv_Δ :
  forall Δ σ ports Δ' σ' id sobj,
    EPorts Δ σ ports Δ' σ' ->
    MapsTo id sobj Δ ->
    MapsTo id sobj Δ'.
Proof.
  induction 1; auto; intros.
  apply IHEPorts; eauto with hvhdl.
Qed.

Lemma EPort_input :
  forall {Δ σ Δ' σ' id τ},
    EPort Δ σ (pdecl_in id τ) Δ' σ' ->
    InputOf Δ' id.
Proof. inversion 1; exists t0; cbn; auto with mapsto. Qed.

Lemma EPorts_input :
  forall {Δ σ ports Δ' σ' id τ},
    EPorts Δ σ ports Δ' σ' ->
    List.In (pdecl_in id τ) ports ->
    InputOf Δ' id.
Proof.
  induction 1; try (solve [inversion 1]).
  inversion 1.
  subst; edestruct @EPort_input; eauto;
    exists x; eapply EPorts_inv_Δ; eauto.
  eapply IHEPorts; eauto.
Qed.

Lemma EPort_Varr_in_sstore :
  forall {Δ σ Δ' σ' id t e e'},
    EPort Δ σ (pdecl_in id (tind_array t e e')) Δ' σ' ->
    exists aofv, MapsTo id (Varr aofv) (sstore σ').
Proof.
  inversion_clear 1.
  inversion_clear H0 in H1.
  inversion_clear H1; unfold sstore_add.
  cbn [sstore].
  exists (create_arr (S size) v0 (Nat.lt_0_succ size)).
  eauto with mapsto.
Qed.

Lemma EPort_inv_well_typed_values_in_sstore : 
  forall {Δ σ pd Δ' σ'},
    EPort Δ σ pd Δ' σ' ->
    (forall {id t v},
        (MapsTo id (Internal t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
        MapsTo id v (sstore σ) ->
        IsOfType v t) ->
    forall {id t v},
      (MapsTo id (Internal t) Δ' \/ MapsTo id (Input t) Δ' \/ MapsTo id (Output t) Δ') ->
      MapsTo id v (sstore σ') ->
      IsOfType v t.
Proof.
  inversion_clear 1; intros WT; intros *;
    
    (* 2 CASES: [id0 = id] or [id0 ≠ id] *)
    destruct (Nat.eq_dec id0 id) as [ eq_ | neq_ ]. 

  (* CASE [id0 ≠ id] *)
  2, 4:
    cbn; intros MapsTo_or MapsTo_sstore;
    eapply WT with (id := id0); eauto with mapsto;
      inversion_clear MapsTo_or as [MapsTo_decl | MapsTo_or1];
      [ left; eauto with mapsto
      | inversion_clear MapsTo_or1;
        [ right; left; eauto with mapsto
        | right; right; eauto with mapsto ] ].
  
  (* CASE [id0 = id] *)
  1,2 : cbn; inversion_clear 1 as [MapsTo_decl | MapsTo_or]; intros MapsTo_sstore;
    rewrite eq_ in *; 
    (* CASE Internal *)
    [ mapsto_discriminate
    | 
    (* CASE Input or Output *)
    inversion_clear MapsTo_or;
    ((match goal with
      | [ H: MapsTo ?k1 (?SObj _) (add _ (?SObj _) _) |- _ ] =>
        assert (eq_type : SObj t1 = SObj t0) by (eauto with mapsto);
        inject_left eq_type;
        erewrite @MapsTo_add_eqv with (e := v0); eauto;
        eapply DefaultV_is_well_typed; eauto
      end)
     || mapsto_discriminate) ].
Qed.

Lemma EPorts_inv_well_typed_values_in_sstore :
  forall {Δ σ ports Δ' σ'},
    EPorts Δ σ ports Δ' σ' ->
    (forall {id t v},
        (MapsTo id (Internal t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
        MapsTo id v (sstore σ) ->
        IsOfType v t) ->
    forall {id t v},
      (MapsTo id (Internal t) Δ' \/ MapsTo id (Input t) Δ' \/ MapsTo id (Output t) Δ') ->
      MapsTo id v (sstore σ') ->
      IsOfType v t.
Proof.
  induction 1; try (solve [auto]).
  intros WT; intros; eapply IHEPorts; eauto.
  eapply EPort_inv_well_typed_values_in_sstore; eauto.
Qed.

Lemma EPort_inv_Δ_if_not_port :
  forall {Δ σ pd Δ' σ'},
    EPort Δ σ pd Δ' σ' ->
    forall {id sobj},
      (~exists t, sobj = Input t \/ sobj = Output t) ->
      MapsTo id sobj Δ' <-> MapsTo id sobj Δ.
Proof.
  split; [ | eapply EPort_inv_Δ; eauto].
  induction H; cbn.
  all :
    destruct (Nat.eq_dec id0 id) as [eq_ | neq_];
    [ rewrite eq_; intros; exfalso;
      match goal with
      | [ H1: ~(_), H2: MapsTo ?k _ (add ?k (Input ?t) _)  |- _ ] =>
        apply H1; exists t; left; eauto with mapsto
      | [ H1: ~(_), H2: MapsTo ?k _ (add ?k (Output ?t) _)  |- _ ] =>
        apply H1; exists t; right; eauto with mapsto
      end
    | eauto with mapsto ].
Qed.

Lemma EPorts_inv_Δ_if_not_port :
  forall {Δ σ ports Δ' σ'},
    EPorts Δ σ ports Δ' σ' ->
    forall {id sobj},
      (~exists t, sobj = Input t \/ sobj = Output t) ->
      MapsTo id sobj Δ' <-> MapsTo id sobj Δ.
Proof.
  induction 1; try (solve [reflexivity]).
  intros; erewrite <- @EPort_inv_Δ_if_not_port with (Δ := Δ); eauto.
Qed.
