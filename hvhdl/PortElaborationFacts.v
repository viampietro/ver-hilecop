(** * Facts about Port Elaboration Relations *)

Require Import common.Coqlib.
Require Import common.NatMap.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.Elaboration.

Lemma eport_idle_gens :
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

Hint Resolve eport_idle_gens : hvhdl.

Lemma eports_idle_gens :
  forall {Δ σ ports Δ' σ'},
    eports Δ σ ports Δ' σ' ->
    EqGens Δ Δ'.
Proof.
  induction 1; [reflexivity | transitivity Δ'; eauto with hvhdl].
Qed.

Hint Resolve eports_idle_gens : hvhdl.

Lemma eport_elab_idle_sigma :
  forall Δ σ id' τ Δ' σ' id v,
    (eport Δ σ (pdecl_out id' τ) Δ' σ' \/ eport Δ σ (pdecl_in id' τ) Δ' σ') ->
    id' <> id ->
    MapsTo id v (sigstore σ) ->
    MapsTo id v (sigstore σ').
Proof.
  inversion_clear 1;
    lazymatch goal with
    | [ H: eport _ _ _ _ _ |- _ ] =>
      inversion_clear H; simpl; apply add_2
    end.
Qed.

Hint Resolve eport_elab_idle_sigma : hvhdl.

Lemma eports_elab_idle_sigma :
  forall Δ σ ports Δ' σ' id v,
    eports Δ σ ports Δ' σ' ->
    ~(exists τ, List.In (pdecl_in id τ) ports \/ List.In (pdecl_out id τ) ports) ->
    MapsTo id v (sigstore σ) ->
    MapsTo id v (sigstore σ').
Proof.
  induction 1; auto.
  intros Hnex Hmapsto.
  apply IHeports. firstorder.
  destruct pd;
    (destruct (Nat.eq_dec portid id);
     [ elimtype False; apply Hnex; exists τ; rewrite e; firstorder |
       eauto with hvhdl ]).
Qed.
