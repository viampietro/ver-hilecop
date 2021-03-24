(** * Facts about Architecture Elaboration Relation *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.NatMapTactics.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.DefaultValueFacts.

Lemma edecls_elab_idle_sigma :
  forall Δ σ sigs Δ' σ',
    edecls Δ σ sigs Δ' σ' ->
    forall id v,
    (~exists τ, List.In (sdecl_ id τ) sigs) ->
    MapsTo id v (sigstore σ) ->
    MapsTo id v (sigstore σ').
Proof.
  induction 1; auto.
  intros; apply IHedecls.
  firstorder.
  lazymatch goal with
  | [ Hedecl: edecl _ _ _ _ _ |- _ ] =>
    destruct ad; inversion_clear Hedecl
  end.
  specialize (Nat.eq_dec id sigid) as Hsum_id.
  inversion_clear Hsum_id as [Heq_id | Hneq_id].
  - assert (Hex_id : exists τ0, List.In (sdecl_ id τ0) (sdecl_ sigid τ :: lofsigs))
      by (exists τ; rewrite Heq_id; apply in_eq).
    elimtype False; apply H1; assumption.
  - simpl; apply add_2; auto.          
Qed.

Lemma edecl_idle_gens :
  forall {Δ σ sd Δ' σ'},
    edecl Δ σ sd Δ' σ' ->
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

Hint Resolve edecl_idle_gens : hvhdl.

Lemma edecls_inv_gens :
  forall {Δ σ sigs Δ' σ'},
    edecls Δ σ sigs Δ' σ' ->
    EqGens Δ Δ'.
Proof. induction 1; [reflexivity | transitivity Δ'; eauto with hvhdl]. Qed.

Hint Resolve edecls_inv_gens : hvhdl.

Lemma edecl_inv_Δ : 
  forall {Δ σ Δ' ad σ' id sobj},
    edecl Δ σ ad Δ' σ' ->
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

Lemma edecls_inv_Δ : 
  forall {Δ σ sigs Δ' σ' id sobj},
    edecls Δ σ sigs Δ' σ' ->
    MapsTo id sobj Δ ->
    MapsTo id sobj Δ'.
Proof.
  induction 1; intros; auto.
  apply IHedecls; eapply edecl_inv_Δ; eauto.
Qed.

Lemma edecl_inv_sigstore : 
  forall {Δ σ Δ' ad σ' id v},
    edecl Δ σ ad Δ' σ' ->
    MapsTo id v (sigstore σ) ->
    MapsTo id v (sigstore σ').
Proof.
  inversion_clear 1; intros; auto.
  destruct (Nat.eq_dec id id0) as [e | ne]; try subst.
  unfold InSStore in H3; mapsto_not_in_contrad.
  apply add_2; auto.
Qed.

Lemma edecls_inv_sigstore :
  forall Δ σ sigs Δ' σ',
    edecls Δ σ sigs Δ' σ' ->
    forall id v,
      MapsTo id v (sigstore σ) ->
      MapsTo id v (sigstore σ').
Proof.
  induction 1; intros; auto.
  apply IHedecls; eapply edecl_inv_sigstore; eauto.
Qed.

Lemma edecl_inv_events :
  forall {Δ σ ad Δ' σ'},
    edecl Δ σ ad Δ' σ' ->
    NatSet.Equal (events σ) (events σ').
Proof. induction 1; auto with set. Qed.

Lemma edecls_inv_events : 
  forall {Δ σ sigs Δ' σ'},
    edecls Δ σ sigs Δ' σ' ->
    NatSet.Equal (events σ) (events σ').
Proof.
  induction 1; auto with set.
  transitivity (events σ'); [
    eapply edecl_inv_events; eauto | auto].
Qed.

Lemma edecl_decl :
  forall {Δ σ Δ' σ' id τ},
    edecl Δ σ (sdecl_ id τ) Δ' σ' ->
    DeclaredOf Δ' id.
Proof. inversion 1; exists t0; auto with mapsto. Qed.

Lemma edecls_decl :
  forall {Δ σ sigs Δ' σ' id τ},
    edecls Δ σ sigs Δ' σ' ->
    List.In (sdecl_ id τ) sigs ->
    DeclaredOf Δ' id.
Proof.
  induction 1; try (solve [inversion 1]).
  inversion 1.
  subst; edestruct @edecl_decl; eauto;
    exists x; eapply edecls_inv_Δ; eauto.
  eapply IHedecls; eauto.
Qed.

Lemma edecl_inv_sstore_well_typed_values :
  forall {Δ σ ad Δ' σ'},
    edecl Δ σ ad Δ' σ' ->
    (forall id v, MapsTo id v (sigstore σ) ->
                  exists t, is_of_type v t) ->
    forall {id v},
      MapsTo id v (sigstore σ') ->
      exists t, is_of_type v t.
Proof.
  induction 1.
  intros oftype; cbn; intros id0 v0 MapsTo_.
  rewrite add_mapsto_iff in MapsTo_.
  destruct MapsTo_ as [ (eq_id, eq_val) | (neq_id, MapsTo_)].
  rewrite <- eq_val; exists t0; eapply defaultv_is_well_typed; eauto.
  eapply oftype; eauto.
Qed.

Lemma edecls_inv_sstore_well_typed_values :
  forall {Δ σ sigs Δ' σ'},
    edecls Δ σ sigs Δ' σ' ->
    (forall id v, MapsTo id v (sigstore σ) ->
                  exists t, is_of_type v t) ->
    forall {id v},
      MapsTo id v (sigstore σ') ->
      exists t, is_of_type v t.
Proof.
  induction 1; auto.
  intro; eapply IHedecls.
  eapply edecl_inv_sstore_well_typed_values; eauto.
Qed.
