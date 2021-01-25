(** * Facts about Initialization *)

Require Import common.Coqlib.
Require Import common.NatMap.

Require Import hvhdl.Environment.
Require Import hvhdl.Initialization.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Place.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.StabilizeFacts.

(** ** Facts about [vruninit] *)

Section VRunInit.

  Lemma vseq_inv_compstore_id :
        forall {Δ σ Λ flag stmt σ' Λ' id__c σ__c},
          SSEvaluation.vseq Δ σ Λ flag stmt σ' Λ' ->
          MapsTo id__c σ__c (compstore σ) ->
          MapsTo id__c σ__c (compstore σ').
  Admitted.

  Lemma mapop_inv_compstore_id :
    forall {Δ Δ__c σ σ__c1 ipmap σ' id__c σ__c2},
      PortMapEvaluation.mapop Δ Δ__c σ σ__c1 ipmap σ' ->
      MapsTo id__c σ__c2 (compstore σ) ->
      MapsTo id__c σ__c2 (compstore σ').
  Admitted.
             
  Lemma vruninit_inv_compstore_id :
    forall {D__s Δ σ behavior σ' id__c σ__c},
      vruninit D__s Δ σ behavior σ' ->
      MapsTo id__c σ__c (compstore σ) ->
      exists σ__c', MapsTo id__c σ__c' (compstore σ').
  Proof.
    induction 1.
    
    (* CASE process evaluation *)
    - exists σ__c; eapply vseq_inv_compstore_id; eauto.
      
    (* CASE comp evaluation with events.
       2 subcases, [id__c = compid] or [id__c ≠ compid] *)
    - simpl; destruct (Nat.eq_dec compid id__c).
      + exists σ__c''; rewrite e; apply add_1; auto.
      + exists σ__c; apply add_2; auto.
        eapply mapop_inv_compstore_id; eauto.

    (* CASE comp evaluation with no events. *)
    - exists σ__c; eapply mapop_inv_compstore_id; eauto.

    (* CASE null *)
    - exists σ__c; assumption.

    (* CASE par *)
    - unfold IsMergedDState in H2; apply proj2, proj1 in H2.
      unfold EqualDom in H2; rewrite <- (H2 id__c); exists σ__c; assumption.
  Qed.

  Lemma vruninit_s_marking_eq_nat :
    forall Δ σ behavior σ',
      vruninit hdstore Δ σ behavior σ' ->
      MapsTo Petri.rst (Vbool false) (sigstore σ) ->
      forall id__p gm ipm opm σ__p' n,
        InCs (cs_comp id__p Petri.place_entid gm ipm opm) behavior ->
        List.In (associp_ ($initial_marking) (e_nat n)) ipm ->
        NatMap.MapsTo id__p σ__p' (compstore σ') ->
        NatMap.MapsTo Place.s_marking (Vnat n) (sigstore σ__p').
  Admitted.
  
End VRunInit.

(** ** Facts about [init] *)

Section Init.

  Lemma init_s_marking_eq_nat :
    forall Δ σ behavior σ0,
      init hdstore Δ σ behavior σ0 ->
      forall id__p gm ipm opm σ__p0 n,
        InCs (cs_comp id__p Petri.place_entid gm ipm opm) behavior ->
        List.In (associp_ ($initial_marking) (e_nat n)) ipm ->
        (exists σ__p, MapsTo id__p σ__p (compstore σ)) ->
        NatMap.MapsTo id__p σ__p0 (compstore σ0) ->
        NatMap.MapsTo Place.s_marking (Vnat n) (sigstore σ__p0).
  Proof.
    inversion 1.
    intros.

    (* [∃ σ__p s.t. σ(id__p)(rst ← ⊥) = σ__p] *)
    match goal with
    | [ ex_MapsTo: exists _, _ , Hvr: vruninit _ _ _ _ _ |- _ ] =>
      inversion ex_MapsTo as (σ__p, MapsTo_σ__p);
        specialize (vruninit_inv_compstore_id Hvr MapsTo_σ__p) as ex_MapsTo_σp';
        inversion ex_MapsTo_σp' as (σ__p', MapsTo_σ__p'); clear ex_MapsTo_σp'
    end.
    assert (MapsTo_rst_σ__p' : MapsTo id__p σ__p' (compstore (sstore_add Petri.rst (Vbool true) σ')))
      by assumption.

    (* [s_marking] value stays the same during stabilization. *)
    eapply stab_inv_s_marking; eauto.

    (* [s_marking] takes [n] during [vruninit], if [<initial_marking => n>] *)
    eapply vruninit_s_marking_eq_nat; eauto.
    simpl; apply add_1; reflexivity.
  Qed.
  
End Init.
