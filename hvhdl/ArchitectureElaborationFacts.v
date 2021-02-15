(** * Facts about Architecture Elaboration Relation *)

Require Import common.Coqlib.
Require Import common.NatMap.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.Elaboration.

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

Lemma edecls_idle_gens :
  forall {Δ σ sigs Δ' σ'},
    edecls Δ σ sigs Δ' σ' ->
    EqGens Δ Δ'.
Proof. induction 1; [reflexivity | transitivity Δ'; eauto with hvhdl]. Qed.

Hint Resolve edecls_idle_gens : hvhdl.

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
