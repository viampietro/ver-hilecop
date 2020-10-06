(** * Facts about the H-VHDL Transition Component *)

Require Import common.NatMap.
Require Import common.Coqlib.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import Environment.
Require Import hvhdl.Petri.
Require Import hvhdl.Transition.
Require Import hvhdl.SynchronousEvaluation.
Require Import hvhdl.Stabilize.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Initialization.

Require Import soundness.SoundnessDefs.

(** ** Facts about the Transition Component Behavior on Falling Edge *)

(** ** Facts about the Transition Component Behavior on Stabilization *)

Lemma s_fired_assign_on_init :
  forall id__t tg tip top Δ σ σ',
    vruninit Δ σ (cs_comp id__t transition_entid tg tip top) σ' ->
    
    forall b σ'__t b' Δ__t,
      MapsTo id__t (Component Δ__t transition_behavior) Δ ->
      MapsTo id__t σ'__t (compstore σ') ->
      MapsTo s_firable (Vbool b) (sigstore σ'__t) ->
      MapsTo s_priority_combination (Vbool b') (sigstore σ'__t) ->
      MapsTo s_fired (Vbool (andb b b')) (sigstore σ'__t).
Proof.
  intros *;
    intros Hruninit;
    dependent induction Hruninit;
    intros *;
    intros H__Δ Hσ'__t Hs_firable Hs_prio_comb. 

  - inversion_clear Hpast as [Hrising | Hfalling].
    
    + induction Hrising using PastSimRising_ind.
      
Admitted.
