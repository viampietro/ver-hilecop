(** * Falling Edge Lemma *)

Require Import common.NatMap.
Require Import common.CoqLib.

Require Import sitpn.dp.SitpnLib.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Stabilize.
Require Import hvhdl.SynchronousEvaluation.
Require Import hvhdl.Environment.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.HilecopDesignStore.

Require Import sitpn2hvhdl.Sitpn2HVhdl.

Require Import soundness.SoundnessDefs.

Lemma fe_equal_fired_aux :
  forall sitpn decpr id__ent id__arch mm d γ E__c E__p Δ σ__e s σ τ s' σ__i σ__f σ',

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post rising edge). *)
    SimStateAfterRE sitpn γ s σ ->

    (* From s to s' after ↓. *)
    SitpnStateTransition E__c τ s s' fe ->

    (* From σ to σ' after ↓. *)
    IsInjectedDState σ (E__p τ fe) σ__i ->
    vfalling hdstore Δ σ__i (behavior d) σ__f ->
    stabilize hdstore Δ σ__f (behavior d) σ' ->

    forall ftrs lofT__s flist,
      IsFiredListAux s' ftrs lofT__s flist ->
      (* Extra. Hypothesis. *)
      (forall t' id__t' σ'__t',
          InA Tkeq (t', id__t') (t2tcomp γ) ->
          MapsTo id__t' σ'__t' (compstore σ') ->
          (InA Teq t' ftrs -> MapsTo Transition.fired (Vbool true) (sigstore σ'__t'))
          /\ (MapsTo Transition.fired (Vbool true) (sigstore σ'__t') -> InA Teq t' ftrs \/ InA Teq t' lofT__s)) ->
      forall t id__t σ'__t,
        InA Tkeq (t, id__t) (t2tcomp γ) ->
        MapsTo id__t σ'__t (compstore σ') ->
        InA Teq t flist <-> MapsTo Transition.fired (Vbool true) (sigstore σ'__t).
Proof.
  intros until ftrs; induction 1.

  (* BASE CASE *)
  - intros EH; intros.
    edestruct EH as (Fired_true, True_fired); eauto.
    split; try assumption.
    intros; edestruct True_fired; eauto.
    inversion H10.

  (* INDUCTION CASE *)
  - intros EH. apply IHIsFiredListAux.
    admit.
Admitted.

Lemma fe_equal_fired :
  forall sitpn decpr id__ent id__arch mm d γ E__c E__p Δ σ__e s σ τ s' σ__i σ__f σ',

    (* sitpn translates into (d, γ). *)
    sitpn_to_hvhdl sitpn decpr id__ent id__arch mm = (inl (d, γ)) ->

    (* Environments are similar. *)
    SimEnv sitpn γ E__c E__p ->
    
    (* [Δ, σ__e] are the results of the elaboration of [d]. *)
    edesign hdstore (empty value) d Δ σ__e ->

    (* States s and σ are similar (post rising edge). *)
    SimStateAfterRE sitpn γ s σ ->

    (* From s to s' after ↓. *)
    SitpnStateTransition E__c τ s s' fe ->

    (* From σ to σ' after ↓. *)
    IsInjectedDState σ (E__p τ fe) σ__i ->
    vfalling hdstore Δ σ__i (behavior d) σ__f ->
    stabilize hdstore Δ σ__f (behavior d) σ' ->

    forall t id__t σ'__t,
      InA Tkeq (t, id__t) (t2tcomp γ) ->
      MapsTo id__t σ'__t (compstore σ') ->
      forall flist,
        IsFiredList s' flist ->
        InA Teq t flist <-> MapsTo Transition.fired (Vbool true) (sigstore σ'__t).
Proof.
  intros until flist; inversion 1.
  eapply fe_equal_fired_aux; eauto.

  intros; split.

  - inversion 1.
  - right. destruct H10 as (InA_Tlist, NoDup_Tlist).
    rewrite <- (InA_Tlist t'); exact Logic.I.
Qed.



