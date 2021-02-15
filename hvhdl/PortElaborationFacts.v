(** * Facts about Port Elaboration Relations *)

Require Import common.Coqlib.
Require Import common.NatMap.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.Elaboration.

Lemma eport_inv_gens :
  forall {Δ σ pd Δ' σ'},
    eport Δ σ pd Δ' σ' ->
    EqGens Δ Δ'.
Proof.
  inversion_clear 1; unfold EqGens; intros.

  (* 2 CASES, [id = id0 or id <> id0]. *)
  all : specialize (Nat.eq_dec id id0) as Hsum; inversion_clear Hsum as [Heq_id | Hneq_id].
  2, 4:
    split; intros Hmap;
    [ let apply_add_2 sobj := ltac: (apply (add_2 sobj Hneq_id Hmap)) in
      (apply_add_2 (Input t0) || apply_add_2 (Output t0))
    | apply (add_3 Hneq_id Hmap)
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

Hint Resolve eport_inv_gens : hvhdl.

Lemma eports_inv_gens :
  forall {Δ σ ports Δ' σ'},
    eports Δ σ ports Δ' σ' ->
    EqGens Δ Δ'.
Proof.
  induction 1; [reflexivity | transitivity Δ'; eauto with hvhdl].
Qed.

Hint Resolve eports_inv_gens : hvhdl.

Lemma eport_inv_sigma :
  forall Δ σ pd Δ' σ' id v,
    eport Δ σ pd Δ' σ' ->
    MapsTo id v (sigstore σ) ->
    MapsTo id v (sigstore σ').
Proof.
  inversion_clear 1;
  intros; simpl; apply add_2; auto;
    match goal with
    | [ H: ~InSStore _ _ |- _ ] =>
      intro; subst; apply H; exists v; auto
    end.
Qed.

Hint Resolve eport_inv_sigma : hvhdl.

Lemma eports_inv_sigma :
  forall Δ σ ports Δ' σ' id v,
    eports Δ σ ports Δ' σ' ->
    MapsTo id v (sigstore σ) ->
    MapsTo id v (sigstore σ').
Proof.
  induction 1; auto; intros.
  apply IHeports; eauto with hvhdl.
Qed.

Lemma eport_inv_events :
  forall {Δ σ pd Δ' σ'},
    eport Δ σ pd Δ' σ' ->
    NatSet.Equal (events σ) (events σ').
Proof. induction 1; auto with set. Qed.

Lemma eports_inv_events :
  forall Δ σ ports Δ' σ',
    eports Δ σ ports Δ' σ' ->
    NatSet.Equal (events σ) (events σ').
Proof.
  induction 1; auto with set.
  transitivity (events σ'); [
    eapply eport_inv_events; eauto
  | auto].
Qed.

Lemma eport_inv_Δ :
  forall Δ σ pd Δ' σ' id sobj,
    eport Δ σ pd Δ' σ' ->
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

Hint Resolve eport_inv_Δ : hvhdl.

Lemma eports_inv_Δ :
  forall Δ σ ports Δ' σ' id sobj,
    eports Δ σ ports Δ' σ' ->
    MapsTo id sobj Δ ->
    MapsTo id sobj Δ'.
Proof.
  induction 1; auto; intros.
  apply IHeports; eauto with hvhdl.
Qed.

Lemma eport_input :
  forall {Δ σ Δ' σ' id τ},
    eport Δ σ (pdecl_in id τ) Δ' σ' ->
    InputOf Δ' id.
Proof. inversion 1; exists t0; auto with mapsto. Qed.

Lemma eports_input :
  forall {Δ σ ports Δ' σ' id τ},
    eports Δ σ ports Δ' σ' ->
    List.In (pdecl_in id τ) ports ->
    InputOf Δ' id.
Proof.
  induction 1; try (solve [inversion 1]).
  inversion 1.
  subst; edestruct @eport_input; eauto;
    exists x; eapply eports_inv_Δ; eauto.
  eapply IHeports; eauto.
Qed.
