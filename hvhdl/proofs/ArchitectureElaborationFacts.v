(** * Facts about Architecture Elaboration Relation *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.proofs.DefaultValueFacts.
Require Import hvhdl.proofs.EnvironmentFacts.

Lemma EDecls_elab_idle_sigma :
  forall Δ σ sigs Δ' σ',
    EDecls Δ σ sigs Δ' σ' ->
    forall id v,
    (~exists τ, List.In (sdecl_ id τ) sigs) ->
    MapsTo id v (sstore σ) ->
    MapsTo id v (sstore σ').
Proof.
  induction 1; auto.
  intros; apply IHEDecls.
  firstorder.
  lazymatch goal with
  | [ HEDecl: EDecl _ _ _ _ _ |- _ ] =>
    destruct ad; inversion_clear HEDecl
  end.
  specialize (Nat.eq_dec id sigid) as Hsum_id.
  inversion_clear Hsum_id as [Heq_id | Hneq_id].
  - assert (Hex_id : exists τ0, List.In (sdecl_ id τ0) (sdecl_ sigid τ :: lofsigs))
      by (exists τ; rewrite Heq_id; apply in_eq).
    elimtype False; apply H1; assumption.
  - simpl; apply add_2; auto.          
Qed.

Lemma EDecl_idle_gens :
  forall {Δ σ sd Δ' σ'},
    EDecl Δ σ sd Δ' σ' ->
    EqGens Δ Δ'.
Proof.
  inversion_clear 1; unfold EqGens; intros.

  (* 2 CASES, [id = id0 or id <> id0]. *)
  all : specialize (Nat.eq_dec id id0) as Hsum; inversion_clear Hsum as [Heq_id | Hneq_id].
  - split; intros Hmap; rewrite Heq_id in *;
      [ 
        elimtype False;
        lazymatch goal with
        | [ H: ~NatMap.In _ _ |- _ ] => 
          apply H; exists (Generic t1 v0); assumption
        end
      | rewrite (add_mapsto_iff Δ id0 id0 (Declared t0) (Generic t1 v0)) in Hmap;
        firstorder;
        lazymatch goal with
        | [ Heq_semobj: _ = Generic _ _ |- _ ] =>
          inversion Heq_semobj
        end ].
  - split; intros Hmap; [ apply (add_2 (Declared t0) Hneq_id Hmap) | apply (add_3 Hneq_id Hmap) ].
Qed.

#[export] Hint Resolve EDecl_idle_gens : hvhdl.

Lemma EDecls_inv_gens :
  forall {Δ σ sigs Δ' σ'},
    EDecls Δ σ sigs Δ' σ' ->
    EqGens Δ Δ'.
Proof. induction 1; [reflexivity | transitivity Δ'; eauto with hvhdl]. Qed.

#[export] Hint Resolve EDecls_inv_gens : hvhdl.

Lemma EDecl_inv_Δ : 
  forall {Δ σ Δ' ad σ' id sobj},
    EDecl Δ σ ad Δ' σ' ->
    MapsTo id sobj Δ ->
    MapsTo id sobj Δ'.
Proof.
  inversion_clear 1; intros; auto.
  destruct (Nat.eq_dec id id0) as [e | ne]; try subst.
  elimtype False;
    match goal with | [ H: ~NatMap.In (elt:=_) _ _ |- _] => apply H end;
    exists sobj; auto.
  apply add_2; auto.
Qed.

Lemma EDecls_inv_Δ : 
  forall {Δ σ sigs Δ' σ' id sobj},
    EDecls Δ σ sigs Δ' σ' ->
    MapsTo id sobj Δ ->
    MapsTo id sobj Δ'.
Proof.
  induction 1; intros; auto.
  apply IHEDecls; eapply EDecl_inv_Δ; eauto.
Qed.

Lemma EDecl_inv_sstore : 
  forall {Δ σ Δ' ad σ' id v},
    EDecl Δ σ ad Δ' σ' ->
    MapsTo id v (sstore σ) ->
    MapsTo id v (sstore σ').
Proof.
  inversion_clear 1; intros; auto.
  destruct (Nat.eq_dec id id0) as [e | ne]; try subst.
  unfold InSStore in H3; mapsto_not_in_contrad.
  apply add_2; auto.
Qed.

Lemma EDecls_inv_sstore :
  forall Δ σ sigs Δ' σ',
    EDecls Δ σ sigs Δ' σ' ->
    forall id v,
      MapsTo id v (sstore σ) ->
      MapsTo id v (sstore σ').
Proof.
  induction 1; intros; auto.
  apply IHEDecls; eapply EDecl_inv_sstore; eauto.
Qed.

Lemma EDecl_inv_events :
  forall {Δ σ ad Δ' σ'},
    EDecl Δ σ ad Δ' σ' ->
    NatSet.Equal (events σ) (events σ').
Proof. induction 1; auto with set. Qed.

Lemma EDecls_inv_events : 
  forall {Δ σ sigs Δ' σ'},
    EDecls Δ σ sigs Δ' σ' ->
    NatSet.Equal (events σ) (events σ').
Proof.
  induction 1; auto with set.
  transitivity (events σ'); [
    eapply EDecl_inv_events; eauto | auto].
Qed.

Lemma EDecl_decl :
  forall {Δ σ Δ' σ' id τ},
    EDecl Δ σ (sdecl_ id τ) Δ' σ' ->
    DeclaredOf Δ' id.
Proof. inversion 1; exists t0; auto with mapsto. Qed.

Lemma EDecls_decl :
  forall {Δ σ sigs Δ' σ' id τ},
    EDecls Δ σ sigs Δ' σ' ->
    List.In (sdecl_ id τ) sigs ->
    DeclaredOf Δ' id.
Proof.
  induction 1; try (solve [inversion 1]).
  inversion 1.
  subst; edestruct @EDecl_decl; eauto;
    exists x; eapply EDecls_inv_Δ; eauto.
  eapply IHEDecls; eauto.
Qed.

Lemma EDecl_inv_well_typed_values_in_sstore : 
  forall {Δ σ ad Δ' σ'},
    EDecl Δ σ ad Δ' σ' ->
    (forall {id t v},
        (MapsTo id (Declared t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
        MapsTo id v (sstore σ) ->
        IsOfType v t) ->
    forall {id t v},
      (MapsTo id (Declared t) Δ' \/ MapsTo id (Input t) Δ' \/ MapsTo id (Output t) Δ') ->
      MapsTo id v (sstore σ') ->
      IsOfType v t.
Proof.
  inversion_clear 1.
  intros WT; intros *.
  (* 2 CASES: [id0 = id] or [id0 ≠ id] *)
  destruct (Nat.eq_dec id0 id) as [ eq_ | neq_ ]. 

  (* CASE [id0 = id] *)
  - cbn; inversion_clear 1 as [MapsTo_decl | MapsTo_or];
    intros MapsTo_sstore.
    (* CASE Declared *)
    + assert (eq_type : Declared t1 = Declared t0) by
          (eauto with mapsto).
      inject_left eq_type.
      assert (eq_val : v0 = v) by (eauto with mapsto).
      inject_left eq_val.
      eapply DefaultV_is_well_typed; eauto.
    (* CASE Input or Output *)
    + inject_left eq_; mapsto_discriminate.

  (* CASE [id0 ≠ id] *)
  - cbn; intros MapsTo_or MapsTo_sstore.
    eapply WT with (id := id0); eauto with mapsto.
    inversion_clear MapsTo_or as [MapsTo_decl | MapsTo_or1];
      [ left; eauto with mapsto
      | inversion_clear MapsTo_or1;
        [ right; left; eauto with mapsto
        | right; right; eauto with mapsto ] ].
Qed.

Lemma EDecls_inv_well_typed_values_in_sstore : 
  forall {Δ σ sigs Δ' σ'},
    EDecls Δ σ sigs Δ' σ' ->
    (forall {id t v},
        (MapsTo id (Declared t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
        MapsTo id v (sstore σ) ->
        IsOfType v t) ->
    forall {id t v},
      (MapsTo id (Declared t) Δ' \/ MapsTo id (Input t) Δ' \/ MapsTo id (Output t) Δ') ->
      MapsTo id v (sstore σ') ->
      IsOfType v t.
Proof.
  induction 1; try (solve [auto]).
  intros WT; intros; eapply IHEDecls; eauto.
  eapply EDecl_inv_well_typed_values_in_sstore; eauto.
Qed.

Lemma EDecl_inv_Δ_if_not_decl : 
  forall {Δ σ ad Δ' σ'},
    EDecl Δ σ ad Δ' σ' ->
    forall {id sobj},
      (~exists t, sobj = Declared t) ->
      MapsTo id sobj Δ' <-> MapsTo id sobj Δ.
Proof.
  split; [ | eapply EDecl_inv_Δ; eauto].
  induction H.
  destruct (Nat.eq_dec id0 id) as [eq_ | neq_];
    [ rewrite eq_; intros; exfalso;
      match goal with
      | [ H1: ~(_), H2: MapsTo ?k _ (add ?k (Declared ?t) _)  |- _ ] =>
        apply H1; exists t; eauto with mapsto
      end
    | eauto with mapsto ].
Qed.

Lemma EDecls_inv_Δ_if_not_decl : 
  forall {Δ σ sigs Δ' σ'},
    EDecls Δ σ sigs Δ' σ' ->
    forall {id sobj},
      (~exists t, sobj = Declared t) ->
      MapsTo id sobj Δ' <-> MapsTo id sobj Δ.
Proof.
  induction 1; try (solve [reflexivity]).
  intros; erewrite <- @EDecl_inv_Δ_if_not_decl with (Δ := Δ); eauto.
Qed.
