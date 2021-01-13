(** * Facts about H-VHDL Elaboration Relations *)

Require Import common.Coqlib.
Require Import common.NatMap.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.Elaboration.

(** ** Facts about Architecture Declaration Elaboration *)

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

(** ** Facts about Behavior Elaboration *)

Lemma ebeh_elab_idle_sigma :
  forall D__s Δ σ beh Δ' σ' id v,
    ebeh D__s Δ σ beh Δ' σ' ->
    MapsTo id v (sigstore σ) ->
    MapsTo id v (sigstore σ').
Proof. induction 1; intros; auto. Defined.

Lemma ebeh_idle_gens :
  forall {D__s Δ σ behavior Δ' σ'},
    ebeh D__s Δ σ behavior Δ' σ' ->
    EqGens Δ Δ'.
Proof.
  induction 1; (reflexivity || auto).
  3 : { transitivity Δ'; eauto with hvhdl. }
  all : unfold EqGens; intros id0 t0;
    let tac id := (specialize (Nat.eq_dec id id0) as Hsum; inversion_clear Hsum as [Heq_id | Hneq_id]) in
    (tac id__p || tac id__c).
  2, 4:
    split; intros Hmap;
    [ let apply_add_2 sobj := ltac: (apply (add_2 sobj Hneq_id Hmap)) in
      (apply_add_2 (Process Λ) || apply_add_2 (Component Δ__c))
    | apply (add_3 Hneq_id Hmap)
    ].
  1, 2:
    split; intros Hmap; rewrite Heq_id in *;
    [ elimtype False;
      lazymatch goal with
      | [ H: ~NatMap.In _ _, _: MapsTo _ (Generic ?t1 ?v0) _ |- _ ] => 
        apply H; exists (Generic t1 v0); assumption
      end
    |
    let tac sobj :=
        (lazymatch goal with
         | [ _: MapsTo _ (Generic ?t1 ?v0) _ |- _ ] =>
           rewrite (add_mapsto_iff Δ id0 id0 sobj (Generic t1 v0)) in Hmap
         end;
         firstorder;
         lazymatch goal with
         | [ Heq_semobj: _ = Generic _ _ |- _ ] =>
           inversion Heq_semobj
         end
        )
    in (tac (Process Λ) || tac (Component Δ__c))
    ].
Qed.

Hint Resolve ebeh_idle_gens : hvhdl.

(** ** Facts about Port Elaboration *)

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
