(** * Facts about the H-VHDL Transition Component *)

Require Import common.NMap.
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

(** ** Facts about the Transition Component on Initialization *)

(* ∀ transition component instance [idt], the output port "fired" a
   [idt] equals "s_firable.s_priority_combination" after the
   initialization phase.  *)

Lemma fired_assign_on_init :
  forall id__t tg tip top Δ σ σ',
    vruninit Δ σ (cs_comp id__t transition_entid tg tip top) σ' ->
    
    forall b σ'__t b' Δ__t,
      MapsTo id__t (Component Δ__t transition_behavior) Δ ->
      MapsTo id__t σ'__t (compstore σ') ->
      MapsTo s_firable (Vbool b) (sigstore σ'__t) ->
      MapsTo s_priority_combination (Vbool b') (sigstore σ'__t) ->
      MapsTo fired (Vbool (andb b b')) (sigstore σ'__t).
Proof.
Admitted.

(** ** Facts about the Transition Component Behavior on Falling Edge *)


(** ** Facts about the Transition Component Behavior on Stabilization *)

(* ∀ transition component instance [idt], the output port "fired" of
   [idt] equals "s_firable.s_priority_combination" after a
   stabilization phase.  *)

Lemma fired_assign_on_stabilize :
  forall id__t tg tip top Δ σ θ σ',
    stabilize Δ σ (cs_comp id__t transition_entid tg tip top) θ σ' ->
    
    forall b σ'__t b' Δ__t,
      MapsTo id__t (Component Δ__t transition_behavior) Δ ->
      MapsTo id__t σ'__t (compstore σ') ->
      MapsTo s_firable (Vbool b) (sigstore σ'__t) ->
      MapsTo s_priority_combination (Vbool b') (sigstore σ'__t) ->
      MapsTo fired (Vbool (andb b b')) (sigstore σ'__t).
Proof.
Admitted.

