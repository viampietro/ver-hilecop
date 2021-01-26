(** * Facts about Stabilization *)

Require Import common.Coqlib.
Require Import common.NatMap.
Require Import common.NatSet.
Require Import common.ListPlus.

Require Import hvhdl.Environment.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Stabilize.
Require Import hvhdl.Place.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.CombinationalEvaluationFacts.

Lemma is_last_of_trace :
  forall D__s Δ σ behavior θ σ',
    stabilize D__s Δ σ behavior θ σ' ->
    (Last θ σ' \/ σ = σ').
Proof.
  induction 1.

  (* BASE CASE. *)
  - right; reflexivity. 

  (* IND. CASE. *)
  - destruct θ.
    + lazymatch goal with
      | [ H: stabilize _ _ _ _ [] _ |- _ ] =>
        inversion H; left; apply Last_singleton
      end.
    + inversion_clear IHstabilize as [Hlast | Heq].
      -- left; apply Last_cons; assumption.
      -- rewrite Heq in H0; inversion H0; contradiction.
Qed.

Lemma last_no_event :
  forall D__s Δ σ behavior θ σ',
    stabilize D__s Δ σ behavior θ σ' ->
    Last θ σ' ->
    events σ' = {[]}.
Proof.
  induction 1.
  - inversion 1.
  - intros Hlast.
    destruct θ.
    assumption.
    assert (Hconsl : d :: θ <> nil) by inversion 1.
    apply (IHstabilize (last_cons_inv Hconsl Hlast)).
Qed.

(** Value of signal [s_marking] in a given P component [id__p] is
    invariant during stabilization. *)

Lemma stab_inv_s_marking :
  forall Δ σ behavior θ σ',
    stabilize hdstore Δ σ behavior θ σ' ->
    forall id__p gm ipm opm σ__p σ__p' v,
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) behavior ->
      MapsTo id__p σ__p (compstore σ) ->
      MapsTo s_marking v (sigstore σ__p) ->
      MapsTo id__p σ__p' (compstore σ') ->
      MapsTo s_marking v (sigstore σ__p').
Proof.
  induction 1; intros.

  (* CASE No events, [σ = σ'] *)
  - erewrite <- MapsTo_fun with (e := σ__p) (e' := σ__p'); eauto.

  (* CASE Events *)
  - edestruct @vcomb_maps_compstore_id with (Δ := Δ) as (σ__pi, MapsTo_σ__pi); eauto.
    eapply IHstabilize; eauto.
    eapply vcomb_inv_s_marking; eauto.  
Qed.
