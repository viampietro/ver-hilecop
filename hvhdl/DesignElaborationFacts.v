(** * Facts about Design Elaboration Relations *)

Require Import common.Coqlib.
Require Import common.NatMap.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.Elaboration.

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
      | [ H: ~NatMap.In (elt:=SemanticalObject) _ _, _: MapsTo _ (Generic ?t1 ?v0) _ |- _ ] => 
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

Lemma ebeh_inv_Δ :
  forall {D__s Δ σ behavior Δ' σ' id sobj},
    ebeh D__s Δ σ behavior Δ' σ' ->
    MapsTo id sobj Δ ->
    MapsTo id sobj Δ'.
Proof.
  induction 1; intros; auto;
  match goal with
   | [ H: ~NatMap.In (elt:=_) ?id2 _ |- MapsTo ?id1 _ (add ?id2 _ _) ] =>
       destruct (Nat.eq_dec id2 id1) as [e | ne];
       [elimtype False; apply H; exists sobj; rewrite e; assumption
       | eapply add_2; eauto]
  end.
Qed.

Lemma ebeh_inv_compstore :
  forall {D__s Δ σ behavior Δ' σ' id σ__c},
    ebeh D__s Δ σ behavior Δ' σ' ->
    MapsTo id σ__c (compstore σ) ->
    MapsTo id σ__c (compstore σ').
Proof.
  induction 1; intros; auto; simpl.
  match goal with
  | [ H: ~NatMap.In (elt:=DState) ?id2 _ |- MapsTo ?id1 _ (add ?id2 _ _) ] =>
    destruct (Nat.eq_dec id2 id1) as [e | ne];
      [elimtype False; apply H; exists σ__c; rewrite e; assumption
      | eapply add_2; eauto]
  end.
Qed.

Lemma ebeh_compid_in_comps :
  forall {D__s Δ σ behavior Δ' σ' id__c id__e gm ipm opm},
    ebeh D__s Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__c id__e gm ipm opm) behavior ->
    exists Δ__c, MapsTo id__c (Component Δ__c) Δ'.
Proof.
  induction 1; inversion 1.
  exists Δ__c; apply add_1; auto.
  - edestruct IHebeh1 as (Δ__c, MapsTo_Δ'); eauto; exists Δ__c.
    eapply ebeh_inv_Δ; eauto.
  - eapply IHebeh2; eauto.
Qed.

Lemma ebeh_compid_in_compstore :
  forall {D__s Δ σ behavior Δ' σ' id__c id__e gm ipm opm},
    ebeh D__s Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__c id__e gm ipm opm) behavior ->
    exists σ__c, MapsTo id__c σ__c (compstore σ').
Proof.
  induction 1; inversion 1.
  exists σ__c; apply add_1; auto.
  - edestruct IHebeh1 as (σ__c, MapsTo_σ'); eauto; exists σ__c.
    eapply ebeh_inv_compstore; eauto.
  - eapply IHebeh2; eauto.
Qed.

(** ** Facts about the [edesign] relation *)

Lemma elab_compid_in_comps :
  forall {D__s M__g d Δ σ__e id__c id__e gm ipm opm},
    edesign D__s M__g d Δ σ__e ->
    InCs (cs_comp id__c id__e gm ipm opm) (behavior d) ->
    exists Δ__c, MapsTo id__c (Component Δ__c) Δ.
Proof.
  inversion 1.
  eapply ebeh_compid_in_comps; eauto.
Qed.

Lemma elab_compid_in_compstore :
  forall {D__s M__g d Δ σ__e id__c id__e gm ipm opm},
    edesign D__s M__g d Δ σ__e ->
    InCs (cs_comp id__c id__e gm ipm opm) (behavior d) ->
    exists σ__c, MapsTo id__c σ__c (compstore σ__e).
Proof.
  inversion 1.
  eapply ebeh_compid_in_compstore; eauto.
Qed.

Lemma elab_nodup_compids :
  forall {D__s M__g d Δ σ__e compids},
    edesign D__s M__g d Δ σ__e ->
    AreCsCompIds (behavior d) compids ->
    List.NoDup compids.
Admitted.
