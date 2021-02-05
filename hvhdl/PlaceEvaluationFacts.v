(** Facts about Evaluation of the Place Design Behavior *)

Require Import common.NatSet.
Require Import common.NatMap.

Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Place.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.HilecopDesignStore.

Lemma vcomb_par_comm :
  forall {D__s Δ σ cstmt cstmt' σ'},
    vcomb D__s Δ σ (cstmt // cstmt') σ' <->
    vcomb D__s Δ σ (cstmt' // cstmt) σ'.
Admitted.

Lemma vcomb_par_assoc :
  forall {D__s Δ σ cstmt cstmt' cstmt'' σ'},
    vcomb D__s Δ σ (cstmt // cstmt' // cstmt'') σ' <->
    vcomb D__s Δ σ ((cstmt // cstmt') // cstmt'')  σ'.
Admitted.

Lemma vcomb_marking_ps_inv_sigstore :
  forall {D__s Δ σ σ' id v},
    vcomb D__s Δ σ marking_ps σ' ->
    MapsTo id v (sigstore σ) ->
    MapsTo id v (sigstore σ').
Admitted.

Lemma vcomb_sigid_not_in_events_1 :
  forall {D__s Δ σ σ' cstmt id v},
    vcomb D__s Δ σ cstmt σ' ->
    MapsTo id v (sigstore σ) ->
    MapsTo id v (sigstore σ') ->
    ~CompOf Δ id ->
    ~NatSet.In id (events σ').
Admitted.

Lemma vcomb_place_inv_s_marking :
  forall {Δ σ σ' v m},
    vcomb hdstore Δ σ place_behavior σ' ->
    MapsTo s_marking (Declared (Tnat 0 m)) Δ ->
    MapsTo s_marking v (sigstore σ) ->
    MapsTo s_marking v (sigstore σ').
Proof.
  intros *; unfold place_behavior.
  do 2 (rewrite vcomb_par_comm; rewrite <- vcomb_par_assoc);
    rewrite <- vcomb_par_assoc.
  inversion_clear 1; intros.

  (* Use merge state definition *)
  match goal with
  | [ H: IsMergedDState _ _ _ _ |- _ ] =>
    do 4 (apply proj2 in H); apply proj1 in H; apply H; clear H; auto
  end.
  apply nIn_nIn_Union.

  (* CASE [id ∉ (events σ'0)] *)
  - eapply vcomb_sigid_not_in_events_1; eauto.
    eapply vcomb_marking_ps_inv_sigstore; eauto.    
    destruct 1.
    match goal with
    | [ H: MapsTo _ _ Δ, H': MapsTo _ _ Δ |- _ ] =>
      specialize (MapsTo_fun H H'); intros e; inversion e
    end.
Admitted.

