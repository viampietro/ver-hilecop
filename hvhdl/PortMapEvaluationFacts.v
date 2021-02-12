(** * Facts about Port Map Evaluation *)

Require Import common.NatMap.
Require Import common.Coqlib.
Require Import common.NatSet.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.ExpressionEvaluation.

(** ** Facts about Input Port Map Evaluation *)

Section IPMap.

  Lemma vassocip_inv_sigstore :
    forall {Δ Δ__c σ σ__c asip σ__c' id v},
      vassocip Δ Δ__c σ σ__c asip σ__c' -> 
      ~InputOf Δ__c id ->
      MapsTo id v (sigstore σ__c) ->
      MapsTo id v (sigstore σ__c').
  Proof.
    inversion 1; subst; simpl; auto; intros.
    all :
      destruct (Nat.eq_dec id id0) as [e1 | ne1]; try subst;
      [ elimtype False;
        match goal with
        | [ H: ~InputOf _ _, H': MapsTo _ (Input ?t) _ |- _ ] =>
          apply H; exists t; assumption
        end
      | eapply NatMap.add_2; eauto ].
  Qed.
  
  Lemma mapip_inv_sigstore :
    forall {Δ Δ__c σ σ__c ipm σ__c' id v},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      ~InputOf Δ__c id ->
      MapsTo id v (sigstore σ__c) ->
      MapsTo id v (sigstore σ__c').
  Proof.
    induction 1; intros; auto.
    apply IHmapip; auto.
    eapply vassocip_inv_sigstore; eauto.
  Qed.

  Lemma mapip_eval_simpl_associp :
    forall {Δ Δ__c σ σ__c ipm σ__c'} {id__i : ident} {e},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      List.In (associp_ id__i e) ipm ->
      exists v, vexpr Δ σ EmptyLEnv false e v /\
                MapsTo id__i v (sigstore σ__c').
  Admitted.

  Lemma mapip_eq_state_if_no_events :
    forall {Δ Δ__c σ σ__c ipm σ__c'},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      Equal (events σ__c') {[]} ->
      σ__c = σ__c'.
  Admitted.
  
End IPMap.

(** ** Facts about Output Port Map Evaluation *)

Section OPMap.

  Lemma mapop_inv_compstore :
    forall {Δ Δ__c σ σ__c1 ipmap σ' id__c σ__c2},
      mapop Δ Δ__c σ σ__c1 ipmap σ' ->
      MapsTo id__c σ__c2 (compstore σ) ->
      MapsTo id__c σ__c2 (compstore σ').
  Proof.
    induction 1; try subst; auto.
    induction H; try subst; auto.
  Qed.

  Lemma mapop_not_in_events_if_not_assigned :
    forall {Δ Δ__c σ σ__c opmap σ' id},
      mapop Δ Δ__c σ σ__c opmap σ' ->
      ~NatSet.In id (events σ) ->
      ~AssignedInOPM id opmap ->
      ~NatSet.In id (events σ').
  Proof.
    induction 1; subst; auto.
    inversion H; subst; simpl; auto.
    all : simpl in IHmapop; intros; apply IHmapop;
      auto; rewrite add_spec; firstorder.
  Qed.

  Lemma mapop_not_in_events_if_not_sig :
    forall {Δ Δ__c σ σ__c opmap σ' id},
      mapop Δ Δ__c σ σ__c opmap σ' ->
      ~NatSet.In id (events σ) ->
      ~OutputOf Δ id ->
      ~NatSet.In id (events σ').
  Admitted.
  
End OPMap.
